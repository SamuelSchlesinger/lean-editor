import LeanEditor.Navigation

/-!
# From characters to actions

A buffer can be edited, but cannot yet be used. The next step is to give keystrokes
a meaning. We keep physical input separate from that meaning: `enter` is a key,
whereas inserting a newline is a choice made by the bindings below.

Most actions are pure functions. Saving and quitting are requests to the outside
world. The type parameter will matter in the next chapter: today we edit a
`Buffer`; later we will edit a buffer together with a mode.
-/
namespace LeanEditor

inductive Key where
  | character (c : Char)
  | paste (cs : List Char)
  | left | right | up | down | home | lineEnd | delete
  | enter | tab | backspace | escape | save | quit | redraw

inductive Action (State : Type) where
  | edit (change : State → State)
  | save | quit

/-- The pure part of an action. Requests leave the state alone. -/
def Action.apply (action : Action State) (s : State) : State :=
  match action with
  | .edit change => change s
  | .save | .quit => s

/-!
For our first editor, typing always inserts. There is no parser for commands, and
no mode to remember. Notice how the arrow bindings reuse precisely the functions
whose laws we proved. Escape and redraw use the identity function.
-/
def Key.action : Key → Action Buffer
  | .character c => .edit (·.insert [c])
  | .paste cs => .edit (·.insert cs)
  | .left => .edit Buffer.left
  | .right => .edit Buffer.right
  | .up => .edit Buffer.up
  | .down => .edit Buffer.down
  | .home => .edit Buffer.home
  | .lineEnd => .edit Buffer.lineEnd
  | .delete => .edit Buffer.delete
  | .backspace => .edit Buffer.backspace
  | .enter => .edit (·.insert ['\n'])
  | .tab => .edit (·.insert ['\t'])
  | .save => .save
  | .quit => .quit
  | .escape | .redraw => .edit id

end LeanEditor
