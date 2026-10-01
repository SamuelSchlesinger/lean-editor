# From nothing to modes

A small functional pearl in Lean 4: start with a program that does nothing,
give it text and a cursor, make it a terminal editor, then give its keys a second
meaning. The last step is a working editor with insert and command modes.

The walk lives in the source. Explanatory passages sit between the definitions
and proofs they motivate. Every stop is runnable, and the later stops share the
same buffer and terminal loop.

Read the standalone functional pearl, *From nothing to a modal editor*, as
[TeX source](PEARL.tex) or a [PDF](output/pdf/PEARL.pdf). Its central calculation
shows how the law for inserting lists survives adding keys and modes, and why
two completed insert sessions have the same final effect as one. This README
covers the runnable stages and their controls.

Build the paper with `make pearl` (Python 3, Lean, `latexmk`, and a TeX Live
installation are required). The command checks every Lean listing against the
implementation, checks the proofs, and writes `output/pdf/PEARL.pdf`. The
manuscript uses a single-column article layout and includes its bibliography in
the TeX source. It is self-contained as a document; the code listings are
excerpts in their surrounding module namespaces.

```sh
lake build --wfail
lake exe walk-empty
lake exe walk-editor notes.txt
lake exe lean-editor notes.txt
```

The two editors require a UTF-8 terminal on macOS or Linux, `stty`, and at least
three screen rows. Lean is pinned in `lean-toolchain`; there are no external Lean
libraries, C shims, or curses bindings.

## 0. A program that returns

[Walk/Empty.lean](Walk/Empty.lean) contains our starting point: `main` has type
`IO Unit`, and its body is `pure ()`. It returns without reading, writing, or
remembering anything. `lake exe walk-empty` does exactly that.

The first useful demand is to remember some text. The second is to remember
*where* the next character belongs. Putting these demands together suggests the
representation in [Basic.lean](LeanEditor/Basic.lean): split a list of characters
at the cursor, and reverse the part before it.

```text
hel|lo

before = ['l', 'e', 'h']
after  = ['l', 'o']
```

The character immediately to either side is at the head of a list. Moving left
or right transfers one head; backspace or delete removes one. Insertion places
a reversed block on the left. Each operation returns a new value, sharing list
structure with its predecessor.

This is the list form of the zipper, following the focused-data-structure idea
in Gérard Huet's [The Zipper](https://doi.org/10.1017/S0956796897002864), itself a
functional pearl. Our focus is a gap between characters.

## A specification small enough to see

Observe a buffer in two ways: its text is `reverse before ++ after`, and its
cursor position is `length before`. The cursor is automatically in bounds.
Taking and dropping the text at that position recover the two halves. The
`Buffer.ext` theorem then says that text and position determine the entire buffer.

Editing can be specified using those observations, without mentioning reversed
lists. Inserting `cs` at position `p` must produce:

```text
take p text ++ cs ++ drop p text
```

`text_insert` proves that equation. Similar equations specify backspace and
forward delete, and separate theorems give the resulting cursor positions. They
include the empty document and both ends of every document.

Motion teaches a small lesson about hypotheses. Left followed by right is an
identity if the first move is possible. At the beginning of the text, left does
nothing and right advances. The inverse theorem records that necessary condition.

Insertion also has an algebra. Inserting nothing is an identity; inserting `xs`
and then `ys` is insertion of `xs ++ ys`. Inserting one character and then
backspacing restores the exact original buffer. These are laws for every buffer
and every inserted text, rather than a collection of examples.

[Navigation.lean](LeanEditor/Navigation.lean) builds longer movements from
`seek`: cut the text at an offset and reconstruct the zipper. Its position is
exactly the requested offset clamped to the document length. Seeking twice keeps
only the final destination. Home, End, Up and Down reuse this operation; all
preserve the text.

## 1. Give the keyboard a meaning

Run `lake exe walk-editor notes.txt`. This is the first editor: typing inserts,
arrows move, Ctrl-S saves, and Ctrl-Q quits. It has a full-screen display and
scrolling, but no modes. An existing file opens at its beginning; a missing file
starts empty and is created when saved.

[Keys.lean](LeanEditor/Keys.lean) makes the connection between keystrokes and
buffer functions. An action is either a pure transformation `State → State`, a
save request, or a quit request. For this first editor, `State` is `Buffer`.

The left arrow denotes `Buffer.left`. A character denotes insertion of that
character. Redraw denotes `id`. The keyboard chooses a function; the loop applies
it. Saving and quitting stay explicit requests handled at the I/O boundary.

We parameterized `Action` by the state it transforms. The next step will use
exactly that small amount of flexibility.

## 2. Give the same keyboard two meanings

Run `lake exe lean-editor notes.txt`. It starts in **command mode**. Press `i`
and the status changes to **INSERT**; now ordinary typing inserts. Press Escape
and the status changes back to **COMMAND**. The cursor also changes between a bar
and a block on terminals that support cursor styles.

[Editor.lean](LeanEditor/Editor.lean) adds one coordinate to the state: a `Mode`
alongside the existing `Buffer`. A lifted buffer function changes only the
buffer. Entering a mode changes only the mode. Lifting respects function
composition, so we reuse the direct editor's actions in insert mode.

Command mode gives selected characters other meanings. `h` means move left,
`x` means delete, and `i` means enter insert mode. The action for `a` composes a
rightward move with entering insert mode. Unbound characters do nothing. The
buffer operations and their proofs are unchanged by this new interpretation.

The cursor remains a **gap** in both modes. Escape changes the mode without an
implicit leftward move. This keeps the transition honest and makes repeated
Escape an identity after the first press.

Now we can prove a whole interaction. `Editor.type_text` lifts the concatenation
law for insertion to a list of character keys. `Editor.insert_session` uses that
result to prove, for every buffer `b` and text `cs`:

```text
command b
  -- press i -->       insert b
  -- type cs -->       insert (b.insert cs)
  -- press Escape -->  command (b.insert cs)
```

The actual loop applies the same pure action used by these proofs. The theorem
concerns decoded character keys; it does not assume that arbitrary raw terminal
bytes are already valid input.

`Editor.replay_insert` proves a broader reuse property: before Escape, insert
mode has the same pure buffer states as the direct editor. `Editor.insert_sessions`
then shows that two completed insert sessions have the same final editor state
as one session inserting the concatenated text. These are state equations;
`replay` projects save and quit requests to identities and performs no I/O.

## Try the last step

On a new file, press `i`, type `hello`, and press Escape. Then press `0`, `x`,
`i`, `H`, Escape, `w`, `q`. The saved file contains `Hello`.

| Key | Command mode | Insert mode |
| --- | --- | --- |
| `i` | Enter insert mode at the cursor | Insert `i` |
| `a` | Move right, then enter insert mode | Insert `a` |
| `h`, `j`, `k`, `l` | Left, down, up, right | Insert the character |
| `0`, `$` | Start, end of line | Insert the character |
| `x` | Delete after the cursor | Insert `x` |
| `w`, `q` | Save, quit | Insert the character |
| Escape | Remain in command mode | Enter command mode |
| Enter, Tab, Backspace | No change | Newline, tab, delete before cursor |
| Arrow keys, Home, End, Delete | Navigate or delete | Navigate or delete |
| Ctrl-S, Ctrl-Q | Save, quit | Save, quit |
| Ctrl-L | Redraw | Redraw |
| Bracketed paste | Ignore the payload | Insert the payload literally |

Ctrl-C also requests quit. If the document differs from the last saved text,
quit asks for a second quit to discard it. Another edit or save cancels that
confirmation. A failed save keeps the buffer open and displays the error.

## The part that touches the world

[Run.lean](LeanEditor/Run.lean) contains one loop for both editors. The saved
snapshot is text, so moving the cursor or changing modes cannot make a clean
file dirty. The loop updates that snapshot only after a successful write.

[Terminal.lean](LeanEditor/Terminal.lean) handles raw input, display, and the
terminal's alternate screen. Its reader follows the
[xterm control-sequence conventions](https://invisible-island.net/xterm/ctlseqs/ctlseqs.html).
Escape is also the beginning of an arrow sequence, so an isolated Escape waits
about 100 ms. Escape followed quickly by an ordinary key yields both keys in
order. Alt combinations are interpreted the same way; there are no Alt bindings.

A bracketed paste arrives as one payload. Command letters and control characters
inside it never become individual key actions. The reader normalizes pasted CRLF
and CR line endings to LF. The pure mode-specific paste rules are proved too.
Without bracketed-paste support, pasted bytes are ordinary
keystrokes, so enter insert mode before pasting.

The display uses one scrolling function for both axes. Its two theorems put the
cursor inside every positive-sized viewport. Raw terminal settings are restored
on normal exit and caught I/O errors. Ctrl-L, or the next key, refreshes a resized
terminal.

## What is checked, and where the story stops

`lake build --wfail` builds all three stops and checks their imported proofs.
CI runs the same command. There are no test suites, `sorry`s, or added axioms;
the proofs use Lean's standard-library list lemmas and arithmetic tactics.

The proved contracts cover the buffer representation, exact edit semantics,
left/right movement, seeking, text preservation under line navigation, pure
modal interactions, and the scrolling calculation. The exact row/column targets
of Up and Down are not separately proved. Byte decoding, actual glyph placement,
filesystem writes and the operating system are outside these proofs.

The editor is deliberately small: it redraws on each key and traverses the
whole document, so it suits small files. Positions count Unicode scalar values;
layout assumes one screen cell per character, with tabs displayed as four spaces.
Wide glyphs and combining sequences are not handled, and other control characters
are shown as `?`. Use LF-delimited UTF-8 files. Saving overwrites the target
directly. There is no undo, selection, search, or syntax highlighting.

The walk's destination is the separation we can now see in the types: a buffer
says *where*, a mode says *what a key means*, and a small I/O loop carries out the
requests that remain.
