import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap21.Example_21_39_2_Computing_homology
import stacks_project.Chap21.Lemma_21_38_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.Fiber

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable {D : RingedSite.{u, v}} (S : inherited_ringed_topos_situation D)

/-- The target object `U` viewed in the fiber category over its image in the base site. -/
abbrev comparisonIndexTargetFiberObj (U : S.C.S) :
    Functor.Fiber S.C.p ((S.C.p).obj U) :=
  mk rfl

/-- The comparison functor on the fibers over `p(U)`, obtained by restricting the morphism of
fibred categories `u : \mathcal C' \to \mathcal C`. -/
abbrev comparisonFiberUnderlyingFunctor (U : S.C.S) :
    Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C.S :=
  (fiberInclusion : Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C'.S) ⋙ S.u.G

/-- The restricted comparison functor lands in the fiber over `p(U)`, so its composite with the
projection to the base is the constant functor at `p(U)`. -/
private theorem comparisonFiberUnderlyingFunctor_comp_eq_const (U : S.C.S) :
    comparisonFiberUnderlyingFunctor S U ⋙ S.C.p =
      (Functor.const (Functor.Fiber S.C'.p ((S.C.p).obj U))).obj ((S.C.p).obj U) := by
  calc
    comparisonFiberUnderlyingFunctor S U ⋙ S.C.p =
        (fiberInclusion : Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C'.S) ⋙ S.C'.p := by
          simpa [comparisonFiberUnderlyingFunctor] using congrArg
            (fun F ↦
              (fiberInclusion : Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C'.S) ⋙ F)
            S.u.w
    _ = (Functor.const (Functor.Fiber S.C'.p ((S.C.p).obj U))).obj ((S.C.p).obj U) :=
      fiberInclusion_comp_eq_const

/-- The comparison functor on the fibers over `p(U)`, obtained by restricting the morphism of
fibred categories `u : \mathcal C' \to \mathcal C`. -/
noncomputable abbrev comparisonFiberFunctor (U : S.C.S) :
    Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ Functor.Fiber S.C.p ((S.C.p).obj U) :=
  Functor.Fiber.inducedFunctor (comparisonFiberUnderlyingFunctor_comp_eq_const S U)

/-- The indexing category `\mathcal I_U` of pairs `(U', \varphi)` with
`\varphi : U \to u(U')` in the fiber over `p(U)`. -/
abbrev comparisonIndexCategory (U : S.C.S) :=
  StructuredArrow (comparisonIndexTargetFiberObj S U) (comparisonFiberFunctor S U)

/-- The presheaf `\mathcal F'_U` on `\mathcal I_U`, obtained by restricting `\mathcal F'` to the
source fiber and then projecting from `\mathcal I_U`. -/
noncomputable abbrev comparisonIndexRestrictionPresheaf
    (ℱ' : sourceAbelianSheafCat S) (U : S.C.S) :
    (comparisonIndexCategory S U)ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (StructuredArrow.proj (comparisonIndexTargetFiberObj S U) (comparisonFiberFunctor S U)).op ⋙
    ((fiberInclusion : Functor.Fiber S.C'.p ((S.C.p).obj U) ⥤ S.C'.S).op) ⋙ ℱ'.1

variable [∀ U : S.C.S,
  HasProjectiveResolutions ((comparisonIndexCategory S U)ᵒᵖ ⥤ AddCommGrpCat.{max u v})]

/-- The objectwise homology group `H_n(\mathcal I_U, \mathcal F'_U)` attached to `U`. -/
def comparisonIndexHomologyObject
    (ℱ' : sourceAbelianSheafCat S) (n : ℕ) (U : S.C.S) :
    AddCommGrpCat.{max u v} :=
  categoryHomology (comparisonIndexRestrictionPresheaf S ℱ' U) n

variable [HasWeakSheafify (targetTopology S) AddCommGrpCat.{max u v}]
variable [(abelianInverseImage S).IsRightAdjoint]
variable [(abelianLowerShriek S).Additive]
variable [HasProjectiveResolutions (sourceAbelianSheafCat S)]

-- Proof sketch: factor the comparison functor `u` through the fibred category `\mathcal C''`
-- of Categories, Lemma `4.33.14`, where the first stage has exact lower shriek and the second
-- stage is covered by Lemma `21.40.2`. The construction of `\mathcal C''` identifies each fiber
-- `\mathcal C''_U` with `\mathcal I_U`, and the restricted sheaf with `\mathcal F'_U`. The
-- proof also supplies the restriction maps on the objectwise rule `U ↦ H_n(\mathcal I_U,
-- \mathcal F'_U)`, producing the presheaf whose sheafification computes `L_n g_!(\mathcal F')`.
/-- Lemma 21.40.3: in Situation `21.38.3`, for an abelian sheaf `\mathcal F'` on `\mathcal C'`
and `n \ge 0`, the `n`-th left derived lower shriek `L_n g_!(\mathcal F')` is canonically
isomorphic to the sheaf associated to the presheaf sending an object `U` of `\mathcal C` to the
homology group `H_n(\mathcal I_U, \mathcal F'_U)`, where `\mathcal I_U` is the fiberwise
comparison indexing category defined above and `\mathcal F'_U` is the induced presheaf on
`\mathcal I_U`. -/
theorem abelian_lower_shriek_left_derived_isomorphic_comparison_index_homology_sheaf
    (ℱ' : sourceAbelianSheafCat S) (n : ℕ) :
    ∃ P : S.C.Sᵒᵖ ⥤ AddCommGrpCat.{max u v},
      (∀ U : S.C.S, P.obj (op U) = comparisonIndexHomologyObject S ℱ' n U) ∧
        IsIsomorphic
          (((abelianLowerShriek S).leftDerived n).obj ℱ')
          ((presheafToSheaf (targetTopology S) AddCommGrpCat.{max u v}).obj P) := sorry

end

end FibredCategoryOver
end CategoryTheory
