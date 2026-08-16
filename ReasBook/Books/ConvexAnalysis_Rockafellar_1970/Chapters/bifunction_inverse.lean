import Mathlib

section RockafellarShared

/-- The canonical inverse `F_*` of a bifunction `F`, obtained by swapping the arguments and
negating the value:

`(F_* x)(u) = -(F u)(x)`.

This is shared across the Chapter 7/8 developments so the repository has a single top-level API
for the inverse bifunction construction. -/
noncomputable def bifunctionInverse
    {U X : Type*} (F : U → X → EReal) : X → U → EReal :=
  fun x u => -F u x

end RockafellarShared
