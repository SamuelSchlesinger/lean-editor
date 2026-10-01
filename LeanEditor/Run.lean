import LeanEditor.Terminal

/-!
# Closing the loop

The direct editor and the modal editor share one terminal loop. Their difference
is the interpretation of a key: lift the original buffer action, or ask the mode
to choose its meaning. In either case there are only three kinds of action.

The saved text is a value, not a manually maintained dirty flag. Moving the cursor
or changing modes therefore cannot make a clean document dirty. The quit latch
and status message are presentation state; a successful save updates the saved
value only after the write returns.
-/
namespace LeanEditor

private def run (file : String) (modal : Bool) : IO Unit := do
  let path : System.FilePath := file
  let contents ← if ← path.pathExists then IO.FS.readFile path else pure ""
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  Terminal.withRaw stdin stdout do
    let mut e : Editor := ⟨Buffer.ofText contents.toList, if modal then .command else .insert⟩
    let mut saved := e.buffer.text
    let mut reader : Terminal.Reader := {}
    let mut top := 0
    let mut left := 0
    let mut message := ""
    let mut quitArmed := false
    while true do
      let viewport ← Terminal.draw stdout e modal file message (e.buffer.text != saved) top left
      (top, left) := viewport
      let (next, key) ← reader.read stdin
      reader := next
      let some key := key | break
      let action := if modal then e.action key else Editor.lift key.action
      -- Apply the same pure transition that appears in the interaction proofs.
      e := action.apply e
      match action with
      | .edit _ =>
        quitArmed := false
        message := ""
      | .save =>
        quitArmed := false
        try
          IO.FS.writeFile path (String.ofList e.buffer.text)
          saved := e.buffer.text
          message := "Saved."
        catch err => message := s!"Save failed: {err}"
      | .quit =>
        if e.buffer.text == saved || quitArmed then break
        message := "Unsaved changes. Quit again to discard."
        quitArmed := true

def runMain (modal : Bool) (args : List String) : IO UInt32 := do
  let [file] := args | do
    IO.eprintln s!"usage: {if modal then "lean-editor" else "walk-editor"} FILE"
    return 1
  try
    run file modal
    return 0
  catch err =>
    IO.eprintln s!"lean-editor: {err}"
    return 1

end LeanEditor
