import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` returned `AlgebraicGeometry.IsProper`,
-- `Scheme.IdealSheafData.vanishingIdeal`, and `Scheme.IdealSheafData.vanishingIdeal_iSup`.
-- Nearby Chapter 30 precedent represents a closed subset proper over a base by the properness
-- of its reduced closed subscheme `vanishingIdeal Z`.

/-- Lemma 30.26.6: if `f : X ⟶ S` is locally of finite type and `Z i ⊆ X`,
`i = 1, ..., n`, are closed subsets proper over `S`, then their finite union is proper
over `S`, using the reduced closed-subscheme structure attached by `vanishingIdeal`. -/
@[stacks 0CYR]
theorem closedSubset_iSup_isProper_over_base
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (n : ℕ) (hn : 0 < n) (Z : Fin n → TopologicalSpace.Closeds X)
    (hproper : ∀ i, IsProper ((vanishingIdeal (Z i)).subschemeι ≫ f)) :
    IsProper ((vanishingIdeal (iSup Z)).subschemeι ≫ f) := sorry

end AlgebraicGeometry
