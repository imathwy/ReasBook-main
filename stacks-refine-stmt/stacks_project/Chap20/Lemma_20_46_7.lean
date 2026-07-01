import Mathlib
import stacks_project.Chap20.Definition_20_46_1
import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

-- Proof sketch: pass from `f` to its mapping cone. The hypotheses on the homology maps imply that
-- `C(f)` has zero homology in degrees `≥ a`, so the composite `E ⟶ F ⟶ C(f)` is locally
-- homotopic to zero by Lemma `20.46.6`. Over such an open neighborhood, the distinguished
-- triangle `G ⟶ F ⟶ C(f) ⟶ G⟦1⟧` yields a lift of the restricted map `α` to `G` up to homotopy.
/-- Lemma 20.46.7: if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` and
`f : \mathcal G^\bullet \to \mathcal F^\bullet` are morphisms of complexes of
`\mathcal O_X`-modules, `\mathcal E^\bullet` is strictly perfect, `\mathcal E^j = 0` for
`j < a`, and `H^j(f)` is an isomorphism for `j > a` and surjective for `j = a`, then locally on
`X` the map `\alpha` lifts through `f` up to homotopy. -/
theorem exists_open_neighborhood_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi
    [CategoryWithHomology (RingedSpace.Modules X)]
    (E F G : CochainComplex (RingedSpace.Modules X) ℤ) (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      ∃ β : (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E) ⟶
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G),
        Nonempty
          (Homotopy
            (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map α)
            (β ≫
              (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f))) := sorry

end AlgebraicGeometry.RingedSpace
