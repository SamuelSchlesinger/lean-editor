import LeanEditor

/-!
# Stop 2: a modal editor

Run `lake exe lean-editor notes.txt`. The initial mode is command: `i` enters
insert mode, and Escape returns. The proof `Editor.insert_session` describes the
whole round trip. Arrow keys and Ctrl-S/Ctrl-Q work in either mode.

Only the bindings change between this entry point and `Walk/Editor.lean`.
The buffer, its proofs and the terminal loop are shared.
-/

def main : List String → IO UInt32 := LeanEditor.runMain (modal := true)
