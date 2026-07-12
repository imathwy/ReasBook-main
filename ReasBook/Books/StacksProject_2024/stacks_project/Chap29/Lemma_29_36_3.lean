import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owner `AlgebraicGeometry.IsEtale` together
  with the general ring-level stability theorem `RingHom.Etale.stableUnderComposition`;
- direct Lean elaboration verified that typeclass inference already provides
  `Etale (f ≫ g)` from `Etale f` and `Etale g`;
- local Chapter 29 precedent records the source-facing consequences of `Etale` as theorem shells,
  so this item is stated as the corresponding composition theorem rather than a wrapper definition.
-/

section

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Lemma 29.36.3: the composition of two morphisms which are étale is étale. -/
@[stacks 02GN]
theorem etale_comp (hf : Etale f) (hg : Etale g) :
    Etale (f ≫ g) := by
  letI := hf
  letI := hg
  infer_instance

end

end AlgebraicGeometry
