import Mathlib

/-- The inverse bifunction obtained by swapping the two arguments and negating the value. -/
def bifunctionInverse {U X : Type*} (F : U → X → EReal) : X → U → EReal :=
  fun x u => -F u x
