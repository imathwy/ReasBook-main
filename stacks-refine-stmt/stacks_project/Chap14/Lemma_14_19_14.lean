import Mathlib
import stacks_project.Chap14.Remark_14_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Over

variable {X : C}

/- Domain-style sampling for Lemma 14.19.14:
- primary domain: simplicial `k`-coskeleta as right Kan extensions, and their compatibility with
  slice forgetful functors;
- sampled owner declarations:
  `Truncated.cosk`,
  `Functor.ranCompIsoOfPreserves`,
  `Over.preservesLimitsOfShape_forget_of_isConnected`,
  `simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits`;
- best owner abstraction: the canonical comparison isomorphism
  `(Over.forget X).ranCompIsoOfPreserves ((SimplexCategory.Truncated.inclusion k).op)`, with the
  source-facing finite-connected-limit and `0 < k` hypotheses supplying its Kan-extension and
  preservation instances;
- primitive data: the slice object `X`, the truncation level `k`, the positivity hypothesis
  `0 < k`, and finite connected limits in `C`;
- derived API: the pointwise right-Kan-extension comparison for `forget X`, and from it the
  owner-level preservation instance and induced natural isomorphism showing that `Over.forget X`
  commutes with `Truncated.cosk k`.

Source/core/bridge triage:
- `source-facing`: the finite-connected-limits slice-category specialization saying that forgetting
  a `k`-coskeleton over `X` agrees with taking the `k`-coskeleton after forgetting to `C`;
- `core/canonical`: `Functor.ranCompIsoOfPreserves`;
- `bridge/view`: the positive-`k` Kan-extension existence bridge from
  `Remark_14_19_11`, the induced finite-connected-limits bridge for `Over X`, and the connected
  limit preservation of `Over.forget X`. -/

section Positive

variable (X) (k : ℕ) (hk : 0 < k) [HasFiniteConnectedLimits C]

local instance : HasFiniteConnectedLimits (Over X) where
  out J := by infer_instance

private noncomputable instance hasRightKanExtensionOver
    : ∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ Over X,
        (SimplexCategory.Truncated.inclusion k).op.HasRightKanExtension F :=
  fun F ↦ by
    letI : (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F :=
      simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits k hk F
    exact Functor.HasRightKanExtension.mk _ <|
      Functor.pointwiseRightKanExtensionCounit _ F

private noncomputable instance hasRightKanExtensionBase :
    ∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion k).op.HasRightKanExtension F :=
  fun F ↦ by
    letI : (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F :=
      simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits k hk F
    exact Functor.HasRightKanExtension.mk _ <|
      Functor.pointwiseRightKanExtensionCounit _ F

private noncomputable instance forgetPreservesRightKanExtensions :
    (forget X).PreservesRightKanExtensions ((SimplexCategory.Truncated.inclusion k).op) :=
  fun F ↦ by
    letI : (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F :=
      simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits k hk F
    letI :
        (forget X).PreservesPointwiseRightKanExtension F
          ((SimplexCategory.Truncated.inclusion k).op) := by
      intro Y
      cases Y with
      | op Y =>
          letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
          letI : FinCategory (matchingIndex k Y.len) := inferInstance
          letI : IsConnected (matchingIndex k Y.len) := inferInstance
          letI :
              PreservesLimit
                (StructuredArrow.proj (op Y) (SimplexCategory.Truncated.inclusion k).op ⋙ F)
                (forget X) :=
            inferInstance
          infer_instance
    infer_instance

/- Lemma 14.19.14: if `C` has finite connected limits and `0 < k`, then for every `k`-truncated
simplicial object over `X`, forgetting its canonical `k`-coskeleton agrees with taking the
canonical `k`-coskeleton after forgetting to `C`. This is the componentwise source-facing bridge
obtained by applying the owner isomorphism
`(forget X).ranCompIsoOfPreserves ((SimplexCategory.Truncated.inclusion k).op)` to `U` and
rewriting `ran` as `Truncated.cosk k`. -/
#check
  (letI := hasRightKanExtensionOver X k hk
   letI := hasRightKanExtensionBase k hk
   letI := forgetPreservesRightKanExtensions X k hk
   let f :
       ∀ U : SimplicialObject.Truncated (Over X) k,
         ((Truncated.cosk k).obj U) ⋙ forget X ≅
           (Truncated.cosk k).obj (U ⋙ forget X) :=
     ((forget X).ranCompIsoOfPreserves ((SimplexCategory.Truncated.inclusion k).op)).app
   f)

end Positive

end Over

end CategoryTheory
