import LeanEditor.Keys

/-!
# The same keys, a second meaning

Our direct editor already works. To make it modal, we need one more coordinate
in its state. The buffer stays exactly as it was: a cursor is a gap between
characters in either mode. In particular, Escape will not secretly move it.
-/
namespace LeanEditor

inductive Mode where
  | insert | command
  deriving DecidableEq, Repr

structure Editor where
  buffer : Buffer
  mode : Mode := .command

namespace Editor

def change (f : Buffer → Buffer) (e : Editor) : Editor := { e with buffer := f e.buffer }
def enter (mode : Mode) (e : Editor) : Editor := { e with mode }

/-- Reuse a buffer action in the larger state, preserving the mode. -/
def lift : Action Buffer → Action Editor
  | .edit f => .edit (change f)
  | .save => .save
  | .quit => .quit

/-!
Lifting does not distort composition: changing the buffer twice is the same as
changing it by the composed function. This is why the first editor's bindings
can survive the introduction of modes without being rewritten.
-/
theorem change_comp (f g : Buffer → Buffer) (e : Editor) :
    change g (change f e) = change (g ∘ f) e := rfl

theorem enter_buffer (m : Mode) (e : Editor) : (enter m e).buffer = e.buffer := rfl

/-- Applying a lifted action is exactly applying the old action to the buffer. -/
theorem apply_lift (a : Action Buffer) (b : Buffer) (m : Mode) :
    (lift a).apply ⟨b, m⟩ = ⟨a.apply b, m⟩ := by
  cases a <;> rfl

/-!
Command mode gives a few letters new meanings. `i` changes only the mode; `a`
first moves right and then enters insert mode. Navigation and deletion still use
the old buffer functions. Unbound characters, Enter, Tab and Backspace do nothing
in command mode. Saving and quitting remain explicit requests.
-/
def command : Key → Action Editor
  | .character 'i' => .edit (enter .insert)
  | .character 'a' => .edit (enter .insert ∘ change Buffer.right)
  | .character 'h' => lift (.edit Buffer.left)
  | .character 'j' => lift (.edit Buffer.down)
  | .character 'k' => lift (.edit Buffer.up)
  | .character 'l' => lift (.edit Buffer.right)
  | .character '0' => lift (.edit Buffer.home)
  | .character '$' => lift (.edit Buffer.lineEnd)
  | .character 'x' => lift (.edit Buffer.delete)
  | .character 'w' => .save
  | .character 'q' => .quit
  | .character _ | .paste _ | .enter | .tab | .backspace => .edit id
  | key => lift key.action

def action (e : Editor) (key : Key) : Action Editor :=
  match key with
  | .escape => .edit (enter .command)
  | _ => match e.mode with
    | .insert => lift key.action
    | .command => command key

/-- One pure transition. The terminal separately carries out save/quit requests. -/
def step (e : Editor) (key : Key) : Editor := (e.action key).apply e

/-- Replay the state changes of a list of keys, without performing any I/O. -/
def replay (e : Editor) (keys : List Key) : Editor := keys.foldl step e

/-!
We can now state properties of interactions, not just individual edits. Escape
always returns to command mode with the exact same buffer. Repeating it has no
further effect. Replaying two key sequences agrees with their concatenation.
-/
@[simp] theorem step_escape (e : Editor) : e.step .escape = enter .command e := rfl

theorem escape_escape (e : Editor) : (e.step .escape).step .escape = e.step .escape := rfl

@[simp] theorem step_insert_character (b : Buffer) (c : Char) :
    step ⟨b, .insert⟩ (.character c) = ⟨b.insert [c], .insert⟩ := rfl

@[simp] theorem step_command_i (b : Buffer) :
    step ⟨b, .command⟩ (.character 'i') = ⟨b, .insert⟩ := rfl

/-- Before Escape, insert mode preserves the direct editor's interpretation. -/
theorem step_insert (b : Buffer) (key : Key) (h : key ≠ .escape) :
    step ⟨b, .insert⟩ key = ⟨key.action.apply b, .insert⟩ := by
  cases key <;> simp_all [step, action, apply_lift]

/-- A paste is literal text in insert mode, including command letters and controls. -/
theorem paste_insert (b : Buffer) (cs : List Char) :
    step ⟨b, .insert⟩ (.paste cs) = ⟨b.insert cs, .insert⟩ := rfl

/-- Pasted text cannot become a sequence of commands. -/
theorem paste_command (b : Buffer) (cs : List Char) :
    step ⟨b, .command⟩ (.paste cs) = ⟨b, .command⟩ := rfl

@[simp] theorem replay_nil (e : Editor) : e.replay [] = e := rfl

theorem replay_cons (e : Editor) (key : Key) (keys : List Key) :
    e.replay (key :: keys) = (e.step key).replay keys := rfl

theorem replay_append (e : Editor) (xs ys : List Key) :
    e.replay (xs ++ ys) = (e.replay xs).replay ys := by
  simp [replay, List.foldl_append]

/-- The pure states of the two editors agree throughout an Escape-free input.
Save and quit are projected to state identities here; this is not an I/O trace. -/
theorem replay_insert (b : Buffer) (keys : List Key) (h : .escape ∉ keys) :
    replay ⟨b, .insert⟩ keys =
      ⟨keys.foldl (fun b key => key.action.apply b) b, .insert⟩ := by
  induction keys generalizing b with
  | nil => rfl
  | cons key keys ih =>
    have hk : key ≠ .escape := by
      intro he
      exact h (by simp [he])
    have hs : .escape ∉ keys := fun hm => h (List.mem_cons_of_mem key hm)
    rw [replay_cons, step_insert b key hk, ih _ hs]
    rfl

/-- In insert mode, typing any text is exactly one bulk insertion. -/
theorem type_text (b : Buffer) (cs : List Char) :
    replay ⟨b, .insert⟩ (cs.map Key.character) = ⟨b.insert cs, .insert⟩ := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, replay_cons, step_insert_character, ih]
    simp [Buffer.insert_append]

/-!
Here is the destination of the walk. Starting in command mode, press `i`, type
any text, and press Escape. The resulting buffer is exactly the original buffer
with that text inserted, and the mode is command again. There is no bound on the
document, cursor offset or typed text in this statement.

`Key.character` means a decoded text character; physical Enter and Tab have their
own keys. The theorem is about the pure interaction, not terminal byte decoding.
-/
theorem insert_session (b : Buffer) (cs : List Char) :
    replay ⟨b, .command⟩ (.character 'i' :: (cs.map Key.character ++ [.escape])) =
      ⟨b.insert cs, .command⟩ := by
  rw [replay_cons, step_command_i, replay_append, type_text, replay_cons, step_escape]
  rfl

/-- Adjacent insert sessions fuse after interpretation, although their key lists differ. -/
theorem insert_sessions (b : Buffer) (xs ys : List Char) :
    replay ⟨b, .command⟩
      ((.character 'i' :: (xs.map Key.character ++ [.escape])) ++
        (.character 'i' :: (ys.map Key.character ++ [.escape]))) =
    replay ⟨b, .command⟩
      (.character 'i' :: ((xs ++ ys).map Key.character ++ [.escape])) := by
  rw [replay_append, insert_session, insert_session, insert_session,
    Buffer.insert_append]

end Editor
end LeanEditor
