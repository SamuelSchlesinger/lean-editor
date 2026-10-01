import Std

/-!
# A place to put the next character

`Walk/Empty.lean` gave us a running program and nothing to edit. A string would
give us text, but an editor also needs a place *inside* the text. Split a list of
characters at that place, and store the left half backwards:

    hel|lo       before = ['l', 'e', 'h']       after = ['l', 'o']

The next character in either direction is now at the head of a list. This is the
list form of the zipper, the focused-data-structure idea presented in Gérard
Huet's *The Zipper* (1997), https://doi.org/10.1017/S0956796897002864. Here the focus
is a gap. We will derive our editor and its laws from that gap.
-/
namespace LeanEditor

/-- The text before the cursor is stored backwards; the text after it is forwards.
Every pair of lists is a valid buffer, including an empty one. -/
structure Buffer where
  before : List Char := []
  after : List Char := []

namespace Buffer

def text (b : Buffer) : List Char := b.before.reverse ++ b.after
def position (b : Buffer) : Nat := b.before.length
def ofText (cs : List Char) : Buffer := ⟨[], cs⟩

/-!
Moving left transfers one head to the other list. Moving right does the reverse.
At an edge there is no head to transfer, so the operation does nothing. Insertion
puts a reversed block on the left; deletion drops one head. These definitions are
total: the empty document needs no special error state.

Single-character motion and deletion are constant-time list operations. Asking
for the whole text or the numerical position traverses lists. This distinction
will matter when we reach the deliberately simple, whole-screen renderer.
-/
def left : Buffer → Buffer
  | ⟨[], cs⟩ => ⟨[], cs⟩
  | ⟨c :: cs, rest⟩ => ⟨cs, c :: rest⟩

def right : Buffer → Buffer
  | ⟨cs, []⟩ => ⟨cs, []⟩
  | ⟨cs, c :: rest⟩ => ⟨c :: cs, rest⟩

/-- Insert text and leave the cursor immediately after it. -/
def insert (b : Buffer) (cs : List Char) : Buffer :=
  ⟨cs.reverse ++ b.before, b.after⟩

def backspace (b : Buffer) : Buffer := ⟨b.before.tail, b.after⟩
def delete (b : Buffer) : Buffer := ⟨b.before, b.after.tail⟩

/-!
## What does this representation mean?

The observations are `text` and `position`. The cursor bound is automatic because
the position counts a part of the document. Taking and dropping at that position
recover the two halves. Consequently, those observations determine the entire
buffer: to prove two buffers equal, it suffices to compare text and position.
-/
@[simp] theorem text_ofText (cs : List Char) : (ofText cs).text = cs := by
  simp [ofText, text]

@[simp] theorem position_ofText (cs : List Char) : (ofText cs).position = 0 := rfl

theorem position_le_length (b : Buffer) : b.position ≤ b.text.length := by
  simp [position, text]

theorem take_position (b : Buffer) : b.text.take b.position = b.before.reverse := by
  simp [text, position]

theorem drop_position (b : Buffer) : b.text.drop b.position = b.after := by
  simp [text, position]

/-- Text and cursor position determine the entire buffer: there is no hidden state. -/
theorem ext {a b : Buffer} (ht : a.text = b.text) (hp : a.position = b.position) :
    a = b := by
  have hl : a.before.reverse = b.before.reverse := by
    rw [← take_position a, ← take_position b, ht, hp]
  have hr : a.after = b.after := by
    rw [← drop_position a, ← drop_position b, ht, hp]
  have := List.reverse_inj.mp hl
  cases a
  cases b
  simp_all

/-!
## Motion changes the place, not the text

Text preservation and the exact cursor formulas come first. The inverse laws
then expose a useful boundary condition: left followed by right is an identity
only if left could actually move. At the beginning, left does nothing and right
advances. The hypothesis in `right_left` records precisely that distinction.
-/
@[simp] theorem text_left (b : Buffer) : b.left.text = b.text := by
  cases b with | mk cs rest => cases cs <;> simp [left, text, List.append_assoc]

@[simp] theorem text_right (b : Buffer) : b.right.text = b.text := by
  cases b with | mk cs rest => cases rest <;> simp [right, text, List.append_assoc]

theorem position_left (b : Buffer) : b.left.position = b.position - 1 := by
  cases b with | mk cs rest => cases cs <;> simp [left, position]

theorem position_right (b : Buffer) :
    b.right.position = min (b.position + 1) b.text.length := by
  cases b with
  | mk cs rest => cases rest <;> simp [right, position, text] <;> omega

/-- Moving left then right is an exact inverse away from the start. -/
theorem right_left (b : Buffer) (h : 0 < b.position) : b.left.right = b := by
  cases b with
  | mk cs rest => cases cs <;> simp_all [position, left, right]

theorem left_right (b : Buffer) (h : b.position < b.text.length) : b.right.left = b := by
  cases b with
  | mk cs rest => cases rest <;> simp_all [position, text, left, right]

/-!
## Editing agrees with cutting and joining

The implementation uses reversed lists; its specification need not. Insertion
cuts the observed text at the cursor and places the new text between the pieces.
Backspace and delete remove the appropriate character using `take` and `drop`.
These equations include both boundaries; natural-number subtraction saturates
at zero, and taking or dropping beyond the end is well defined.
-/
theorem text_insert (b : Buffer) (cs : List Char) :
    (b.insert cs).text = b.text.take b.position ++ cs ++ b.text.drop b.position := by
  rw [take_position, drop_position]
  simp [insert, text, List.append_assoc]

theorem position_insert (b : Buffer) (cs : List Char) :
    (b.insert cs).position = b.position + cs.length := by
  simp [insert, position, Nat.add_comm]

theorem text_backspace (b : Buffer) :
    b.backspace.text = b.text.take (b.position - 1) ++ b.text.drop b.position := by
  rw [drop_position]
  cases b with
  | mk cs rest =>
    cases cs <;> simp [backspace, text, position, List.append_assoc]

theorem position_backspace (b : Buffer) : b.backspace.position = b.position - 1 := by
  simp [backspace, position]

theorem text_delete (b : Buffer) :
    b.delete.text = b.text.take b.position ++ b.text.drop (b.position + 1) := by
  rw [take_position]
  simp [delete, text, position, List.drop_append]

theorem position_delete (b : Buffer) : b.delete.position = b.position := rfl

/-!
## An algebra for typing

A one-character insertion has an exact left inverse: backspace restores the
entire buffer, including the cursor. More generally, insertion respects the
empty list and concatenation. Typing a block at once is equivalent to typing its
pieces in order. Later, `Editor.type_text` will turn this equation into a theorem
about an arbitrary sequence of keystrokes.
-/
theorem backspace_insert (b : Buffer) (c : Char) : (b.insert [c]).backspace = b := by
  cases b
  simp [insert, backspace]

@[simp] theorem insert_nil (b : Buffer) : b.insert [] = b := by
  cases b
  simp [insert]

/-- Together with `insert_nil`, insertion is a right action of lists under concatenation. -/
theorem insert_append (b : Buffer) (xs ys : List Char) :
    (b.insert xs).insert ys = b.insert (xs ++ ys) := by
  simp [insert, List.reverse_append, List.append_assoc]

end Buffer
end LeanEditor
