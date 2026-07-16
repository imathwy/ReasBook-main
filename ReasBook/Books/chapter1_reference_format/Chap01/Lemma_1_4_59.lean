import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 1.4.59: the unit circle `S^1`, viewed in the multiplicative group `ℂˣ` via the
canonical homomorphism `Circle.toUnits`, is the subgroup `Circle.toUnits.range`. -/
recall Circle.toUnits : Circle →* ℂˣ
#check (Circle.toUnits.range : Subgroup ℂˣ)
