import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import StacksProject_2024.Chap29.Definition_29_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

open AlgebraicGeometry
open Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` returned `AlgebraicGeometry.IsProper`,
-- `Scheme.IdealSheafData.vanishingIdeal_antimono`, and `Scheme.IdealSheafData.inclusion` as the
-- relevant canonical owners/API. This item is source-facing: it keeps the textbook closed-subset
-- statement, removes the redundant ambient finite-type assumption on `f`, and uses the canonical
-- subscheme inclusion induced by `vanishingIdeal_antimono hYZ` as the bridge to the properness
-- owner on morphisms.

/-- Lemma 30.26.3: if `Y ⊆ Z ⊆ X` are closed subsets and `Z` is proper over `S`, then `Y` is
proper over `S`, formalized via the canonical closed subschemes attached by `vanishingIdeal`. -/
@[stacks 0CYN]
theorem closedSubset_isProper_over_base
    {X S : Scheme.{u}} (f : X ⟶ S)
    (Y Z : TopologicalSpace.Closeds X) (hYZ : Y ≤ Z)
    [IsProper ((vanishingIdeal Z).subschemeι ≫ f)] :
    IsProper ((vanishingIdeal Y).subschemeι ≫ f) := by
  let i : (vanishingIdeal Y).subscheme ⟶ (vanishingIdeal Z).subscheme :=
    inclusion (vanishingIdeal_antimono hYZ)
  haveI : IsProper i := inferInstance
  simpa [i] using
    (show IsProper (i ≫ (vanishingIdeal Z).subschemeι ≫ f) by infer_instance)

end AlgebraicGeometry
