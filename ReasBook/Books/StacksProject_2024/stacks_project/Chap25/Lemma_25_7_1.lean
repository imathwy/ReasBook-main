import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` only surfaced mathlib's generic `OneHypercover` and
-- adjunction-unit naturality API. The source item is about the local Chapter 25 owner
-- the local `Hypercovering` owner with ambient topology parameter `J`, so the statement stays on
-- that owner and exposes the source's
-- degreewise `γ_n` maps explicitly.

/-- The naturality square defining the source's degree-`n + 1` map `γ` into the pullback of
matching objects. -/
theorem pullbackGamma_condition
    {X : C}
    {L M : SimplicialObject (SR(C, X))}
    (b : M ⟶ L) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    b.app (op <| SimplexCategory.mk (n + 1)) ≫ matchingMap L n =
      matchingMap M n ≫
        ((SimplicialObject.cosk n).map b).app (op <| SimplexCategory.mk (n + 1)) := sorry

/-- The degree-`n + 1` map `γ_n : M_{n + 1} ⟶ L_{n + 1} ×_{(\operatorname{cosk}_n L)_{n + 1}}
(\operatorname{cosk}_n M)_{n + 1}` appearing in the pullback hypercovering criterion. -/
noncomputable abbrev pullbackGamma
    {X : C}
    {L M : SimplicialObject (SR(C, X))}
    (b : M ⟶ L) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    M.obj (op <| SimplexCategory.mk (n + 1)) ⟶
      pullback (matchingMap L n)
        (((SimplicialObject.cosk n).map b).app (op <| SimplexCategory.mk (n + 1))) :=
  pullback.lift
    (b.app (op <| SimplexCategory.mk (n + 1)))
    (matchingMap M n)
    (pullbackGamma_condition b n)

/-- Unfolding `pullbackGamma` gives the canonical lift into the pullback of matching objects. -/
theorem pullbackGamma_def
    {X : C}
    {L M : SimplicialObject (SR(C, X))}
    (b : M ⟶ L) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    pullbackGamma b n =
      pullback.lift
        (b.app (op <| SimplexCategory.mk (n + 1)))
        (matchingMap M n)
        (pullbackGamma_condition b n) := sorry

/-- The degree-`0` term of the simplicial pullback is covering under the hypotheses of
`pullbackHypercovering`. -/
private theorem pullbackHypercovering_zero_isCovering
    {X : C}
    (K : @Hypercovering C _ J X)
    {L M : SimplicialObject (SR(C, X))}
    (a : K.toSimplicialObject ⟶ L) (b : M ⟶ L)
    (hb0 : Hom.IsCovering J (b.app (op <| SimplexCategory.mk 0))) :
    ((pullback a b).obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X := sorry

/-- Each higher matching map of the simplicial pullback is covering under the hypotheses of
`pullbackHypercovering`. -/
private theorem pullbackHypercovering_succ_isCovering
    {X : C}
    (K : @Hypercovering C _ J X)
    {L M : SimplicialObject (SR(C, X))}
    (a : K.toSimplicialObject ⟶ L) (b : M ⟶ L)
    (hγ : ∀ (n : ℕ)
      [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
      Hom.IsCovering J (pullbackGamma b n))
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Hom.IsCovering J (matchingMap (pullback a b) n) := sorry

/-- Lemma 25.7.1: let `K ⟶ L ← M` be morphisms of simplicial objects in `SR(C, X)`. If `K` is a
hypercovering of `X`, the degree-`0` map `M₀ ⟶ L₀` is covering, and for every `n ≥ 0` the
canonical map `γ_n : M_{n + 1} ⟶ L_{n + 1} ×_{(\operatorname{cosk}_n L)_{n + 1}}
(\operatorname{cosk}_n M)_{n + 1}` is covering, then the simplicial pullback `K ×[L] M` is a
hypercovering of `X`. -/
noncomputable def pullbackHypercovering
    {X : C}
    (K : @Hypercovering C _ J X)
    (L M : SimplicialObject (SR(C, X)))
    (a : K.toSimplicialObject ⟶ L) (b : M ⟶ L)
    (hb0 : Hom.IsCovering J (b.app (op <| SimplexCategory.mk 0)))
    (hγ : ∀ (n : ℕ)
      [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
      Hom.IsCovering J (pullbackGamma b n)) :
    @Hypercovering C _ J X where
  toSimplicialObject := pullback a b
  zero_isCovering := pullbackHypercovering_zero_isCovering K a b hb0
  succ_isCovering := pullbackHypercovering_succ_isCovering K a b hγ

/-- The hypercovering `pullbackHypercovering K L M a b hb0 hγ` has underlying simplicial object
`K.toSimplicialObject ×[L] M`. -/
theorem pullbackHypercovering_toSimplicialObject
    {X : C}
    (K : @Hypercovering C _ J X)
    (L M : SimplicialObject (SR(C, X)))
    (a : K.toSimplicialObject ⟶ L) (b : M ⟶ L)
    (hb0 : Hom.IsCovering J (b.app (op <| SimplexCategory.mk 0)))
    (hγ : ∀ (n : ℕ)
      [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
      Hom.IsCovering J (pullbackGamma b n)) :
    (pullbackHypercovering K L M a b hb0 hγ).toSimplicialObject = pullback a b := sorry

end CategoryTheory
