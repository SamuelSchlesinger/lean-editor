/-!
# Stop 0: do nothing

Begin with a program whose only promise is to return. `IO Unit` describes an
effectful computation with no useful result; `pure ()` performs no effects.

Run it with `lake exe walk-empty`. It has no buffer, keyboard handler or screen.
The next demand is to remember text and a place at which to edit it. Continue in
`LeanEditor/Basic.lean`, where that place becomes a split between two lists.
-/

def main : IO Unit := pure ()
