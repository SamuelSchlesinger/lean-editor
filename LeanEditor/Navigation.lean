import LeanEditor.Basic

/-!
# From a gap to lines

An editor needs to move farther than one character. Rather than introduce another
representation, we first define `seek`: cut the observed text at an offset and
rebuild the zipper. List `take` and `drop` do the clamping for us.

This costs a traversal. It also gives a small, trustworthy basis for line motion:
the text is unchanged, the position is exactly the requested offset clamped to
the document length, and the final destination wins when two seeks are composed.
-/
namespace LeanEditor.Buffer

/-- Move to a character offset, clamping at the end of the document. -/
def seek (b : Buffer) (n : Nat) : Buffer :=
  ⟨(b.text.take n).reverse, b.text.drop n⟩

@[simp] theorem text_seek (b : Buffer) (n : Nat) : (b.seek n).text = b.text := by
  simp [seek, text]

theorem position_seek (b : Buffer) (n : Nat) :
    (b.seek n).position = min n b.text.length := by
  simp [seek, position]

theorem seek_position (b : Buffer) : b.seek b.position = b := by
  apply ext (text_seek _ _)
  simp [position_seek, Nat.min_eq_left (position_le_length b)]

theorem seek_seek (b : Buffer) (n m : Nat) : (b.seek n).seek m = b.seek m := by
  apply ext <;> simp [position_seek]

/-!
The current column is the number of characters before the nearest newline to
the left. Home and End seek to the ends of that line. Up and Down find the
adjacent line and keep this column as far as its length allows. At the first or
last line they stay put. No preferred column is remembered across short lines.

The proofs below establish text preservation for these derived motions. Their
row-and-column targeting formulas are not independently specified by a theorem;
we distinguish that remaining obligation from the proved contract of `seek`.
-/
def column (b : Buffer) : Nat := (b.before.takeWhile (· != '\n')).length
def home (b : Buffer) : Buffer := b.seek (b.position - b.column)
def lineEnd (b : Buffer) : Buffer :=
  b.seek (b.position + (b.after.takeWhile (· != '\n')).length)

def up (b : Buffer) : Buffer :=
  match b.before.drop b.column with
  | [] => b
  | _ :: rest =>
    let width := (rest.takeWhile (· != '\n')).length
    b.seek (b.position - b.column - 1 - width + min b.column width)

def down (b : Buffer) : Buffer :=
  let rest := b.after.dropWhile (· != '\n')
  if rest.isEmpty then b else
    let width := (rest.tail.takeWhile (· != '\n')).length
    b.seek (b.position + b.after.length - rest.length + 1 + min b.column width)

@[simp] theorem text_home (b : Buffer) : b.home.text = b.text := by
  simp [home]

@[simp] theorem text_lineEnd (b : Buffer) : b.lineEnd.text = b.text := by
  simp [lineEnd]

@[simp] theorem text_up (b : Buffer) : b.up.text = b.text := by
  unfold up
  split <;> simp

@[simp] theorem text_down (b : Buffer) : b.down.text = b.text := by
  dsimp only [down]
  split <;> simp

end LeanEditor.Buffer
