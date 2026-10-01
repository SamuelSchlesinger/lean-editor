import LeanEditor

/-!
# Stop 1: an editor

Run `lake exe walk-editor notes.txt`. Type directly, navigate with the arrows,
save with Ctrl-S, and quit with Ctrl-Q. This is a complete non-modal editor using
`Key.action`: typing a character always inserts it.

The common terminal loop is in `LeanEditor/Run.lean`. Its `modal` parameter picks
the bindings, not a different buffer or a second implementation of the terminal.
We keep this executable so that the middle stop of the walk stays usable.
-/

def main : List String → IO UInt32 := LeanEditor.runMain (modal := false)
