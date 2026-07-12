import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import StacksProject_2024.Chap29.Definition_29_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

-- Semantic recall:
-- - the core ring-level owner is the canonical `Algebra.QuasiFiniteAt` residue-field finite
--   instance at a prime;
-- - `Chap29/Definition_29_10_1` already owns the canonical induced algebra on scheme residue
--   fields, so this file should reuse that owner instead of duplicating it locally.

/-- Lemma 29.20.5: if a morphism of schemes `f : X ⟶ S` is quasi-finite at a point `x : X`, then
the residue field extension `κ(x) / κ(f(x))` is finite. -/
@[stacks 01TG]
theorem moduleFinite_residueField_of_quasiFiniteAt
    (hfx : f.QuasiFiniteAt x) :
    Module.Finite (S.residueField (f x)) (X.residueField x) := by
  let R := S.presheaf.stalk (f x)
  let T := X.presheaf.stalk x
  letI : Algebra R T := (f.stalkMap x).hom.toAlgebra
  letI : (f.stalkMap x).hom.QuasiFinite := hfx
  letI : Algebra.QuasiFinite R T := RingHom.QuasiFinite.toAlgebra hfx
  change Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)
  infer_instance

end

end AlgebraicGeometry
