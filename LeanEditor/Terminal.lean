import LeanEditor.Editor

/-!
# Letting the outside world in

The functional story is complete before this module. Here we translate bytes
into keys, and buffers into terminal cells. These are ordinary I/O adapters, not
an end-to-end verification of a terminal or filesystem.

We borrow the terminal's settings with `stty -g` and return them in `finally`.
Raw input gives us individual bytes. A short read timeout resolves a small but
essential ambiguity: Escape is both a key and the first byte of an arrow key.
-/

namespace LeanEditor.Terminal

-- stty must inherit stdin: IO.Process.output would replace it with /dev/null.
private def stty (args : Array String) : IO String := do
  let child ← IO.Process.spawn { cmd := "stty", args, stdout := .piped, stderr := .piped }
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  if (← child.wait) != 0 then throw <| IO.userError s!"stty: {err.trimAscii}"
  return out.trimAscii.toString

def withRaw (stdin stdout : IO.FS.Stream) (action : IO Unit) : IO Unit := do
  unless (← stdin.isTty) && (← stdout.isTty) do
    throw <| IO.userError "run this editor in a terminal"
  let saved ← stty #["-g"]
  try
    discard <| stty #["raw", "-echo", "min", "0", "time", "1"]
    stdout.putStr "\x1b[?1049h\x1b[?7l\x1b[?2004h"
    stdout.flush
    action
  finally
    try
      stdout.putStr "\x1b[0m\x1b[0 q\x1b[?2004l\x1b[?25h\x1b[?7h\x1b[?1049l"
      stdout.flush
    finally
      discard <| stty #[saved]

private def size : IO (Nat × Nat) := do
  let fields := ((← stty #["size"]).splitOn " ").filter (· != "")
  match fields with
  | [rows, cols] => return ((rows.toNat?.getD 24).max 3, (cols.toNat?.getD 80).max 1)
  | _ => return (24, 80)

private inductive Decoder where
  | normal
  | utf8 (bytes : ByteArray) (remaining : Nat)
  | escape
  | sequence (params : String)
  | paste (bytes : ByteArray)

private def plain (byte : UInt8) : Decoder × List Key :=
  let n := byte.toNat
  if n == 27 then (.escape, [])
  else if n < 128 then (.normal, match n with
    | 3 | 17 => [.quit]
    | 19 => [.save]
    | 8 | 127 => [.backspace]
    | 10 | 13 => [.enter]
    | 9 => [.tab]
    | 12 => [.redraw]
    | _ => if n < 32 then [] else [.character (Char.ofNat n)])
  else if 194 ≤ n && n ≤ 244 then
    (.utf8 (ByteArray.empty.push byte) (if n < 224 then 1 else if n < 240 then 2 else 3), [])
  else (.normal, [])

private def decode (state : Decoder) (byte : UInt8) : Decoder × List Key :=
  let c := Char.ofNat byte.toNat
  match state with
  | .normal => plain byte
  | .utf8 bytes remaining =>
    if byte.toNat < 128 || 192 ≤ byte.toNat then plain byte else
      let bytes := bytes.push byte
      if remaining > 1 then (.utf8 bytes (remaining - 1), []) else
        (.normal, ((String.fromUTF8? bytes).bind fun s => s.toList.head?.map Key.character).toList)
  | .escape =>
    if c == '[' || c == 'O' then (.sequence "", []) else
      let (next, keys) := plain byte
      (next, .escape :: keys)
  | .paste bytes =>
    let bytes := bytes.push byte
    if bytes.size ≥ 6 && bytes.extract (bytes.size - 6) bytes.size == "\x1b[201~".toUTF8 then
      let text := String.fromUTF8? (bytes.extract 0 (bytes.size - 6))
      (.normal, text.toList.map fun s =>
        .paste (((s.replace "\r\n" "\n").replace "\r" "\n").toList))
    else (.paste bytes, [])
  | .sequence params =>
    if c == '\x1b' then (.escape, [])
    else if byte.toNat < 32 || byte.toNat > 126 || params.length > 16 then (.normal, [])
    else if byte.toNat < 64 then (.sequence (params.push c), [])
    else if c == '~' && params == "200" then (.paste ByteArray.empty, [])
    else (.normal, match c with
      | 'A' => [.up] | 'B' => [.down] | 'C' => [.right] | 'D' => [.left]
      | 'H' => [.home] | 'F' => [.lineEnd]
      | '~' => match params with
        | "1" | "7" => [.home] | "4" | "8" => [.lineEnd]
        | "3" => [.delete] | _ => []
      | _ => [])

/-!
An Escape followed quickly by `i` is two keys, not an Alt-I binding. Decoding can
therefore produce two keys at once. A small queue preserves their order across
calls. An isolated Escape becomes a key after the terminal's 100 ms timeout.
An arrow sequence received before that timeout remains one key and does not
change the editor's mode.

Bracketed paste is one payload, not a stream of commands. The bindings can then
insert it in insert mode and ignore it in command mode. The xterm control-sequence
reference documents the wire format: https://invisible-island.net/xterm/ctlseqs/ctlseqs.html.
Terminals can send pasted line endings as CR; we normalize CRLF and CR to LF here.
-/
structure Reader where
  private decoder : Decoder := .normal
  private pending : List Key := []

def Reader.read (r : Reader) (stdin : IO.FS.Stream) : IO (Reader × Option Key) := do
  let mut reader := r
  while true do
    if let key :: keys := reader.pending then
      return ({ reader with pending := keys }, some key)
    let bytes ← stdin.read 1
    if bytes.isEmpty then
      unless (← stdin.isTty) do return (reader, none)
      match reader.decoder with
      | .escape => reader := ⟨.normal, [.escape]⟩
      | _ => pure ()
    else
      let (next, keys) := decode reader.decoder bytes[0]!
      reader := ⟨next, keys⟩
  return (reader, none)

/-!
The screen needs only one geometric idea: keep an integer cursor inside an
interval. We use the same calculation for rows and columns. Its two inequalities
are proved for every positive extent, independently of terminal escape codes.
-/
def scroll (cursor start extent : Nat) : Nat :=
  if cursor < start then cursor
  else if start + extent ≤ cursor then cursor + 1 - extent
  else start

theorem scroll_le_cursor (cursor start extent : Nat) (h : 0 < extent) :
    scroll cursor start extent ≤ cursor := by
  unfold scroll
  split <;> (try split) <;> omega

theorem cursor_lt_scroll_add (cursor start extent : Nat) (h : 0 < extent) :
    cursor < scroll cursor start extent + extent := by
  unfold scroll
  split <;> (try split) <;> omega

-- Tabs use four cells. Escape/control bytes from files never reach the terminal.
-- Other Unicode characters are assumed to occupy one cell.
private def display (s : String) : String :=
  String.join <| s.toList.map fun c =>
    if c == '\t' then "    "
    else if c.toNat < 32 || (127 ≤ c.toNat && c.toNat < 160) then "?"
    else String.singleton c

def draw (stdout : IO.FS.Stream) (e : Editor) (modal : Bool)
    (file message : String) (dirty : Bool)
    (top left : Nat) : IO (Nat × Nat) := do
  let b := e.buffer
  let (rows, cols) ← size
  let height := rows - 2
  let row := b.before.count '\n'
  let column := (display (String.ofList (b.before.takeWhile (· != '\n')).reverse)).length
  let top := scroll row top height
  let left := scroll column left cols
  let lines := ((String.ofList b.text).splitOn "\n").toArray
  let mut frame := "\x1b[?25l"
  for i in [:height] do
    let line := ((display (lines[top + i]?.getD "")).drop left).take cols
    frame := frame ++ s!"\x1b[{i + 1};1H\x1b[2K{line}"
  let name := (System.FilePath.mk file).fileName.getD file
  let label := if !modal then "DIRECT" else if e.mode == .insert then "INSERT" else "COMMAND"
  let status := s!"{label}  {row + 1}:{b.column + 1}{if dirty then " *" else ""}  {name}"
  let help := if !message.isEmpty then message else if !modal then "^S save  ^Q quit  arrows move"
    else if e.mode == .insert then "Esc command  ^S save  ^Q quit"
    else "i insert  hjkl move  x delete  w save  q quit"
  frame := frame ++ s!"\x1b[{rows - 1};1H\x1b[2K\x1b[7m{(display status).take cols}\x1b[0m"
  frame := frame ++ s!"\x1b[{rows};1H\x1b[2K{(display help).take cols}"
  let shape := if !modal || e.mode == .insert then 6 else 2
  frame := frame ++ s!"\x1b[{shape} q\x1b[{row - top + 1};{column - left + 1}H\x1b[?25h"
  stdout.putStr frame
  stdout.flush
  return (top, left)

end LeanEditor.Terminal
