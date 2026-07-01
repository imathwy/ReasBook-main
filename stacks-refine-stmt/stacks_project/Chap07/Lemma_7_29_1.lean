import Mathlib
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- A functor is source-locally faithful for a topology on the source if equal arrows become equal
after restricting along a covering sieve in the source site. -/
class IsSourceLocallyFaithful (u : C ⥤ D) (J : GrothendieckTopology C) : Prop where
  equalizer_mem {U' U : C} (a b : U' ⟶ U) (h : u.map a = u.map b) :
    Sieve.equalizer a b ∈ J U'

/-- A functor is source-locally full for a topology on the source if every arrow between objects in
the image locally comes from an arrow in the source site. -/
class IsSourceLocallyFull (u : C ⥤ D) (J : GrothendieckTopology C) : Prop where
  imageSieve_mem {U' U : C} (c : u.obj U' ⟶ u.obj U) : u.imageSieve c ∈ J U'

private theorem isLocallyFull_of_isSourceLocallyFull
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [u.IsCocontinuous J K] [IsSourceLocallyFull u J] :
    u.IsLocallyFull K where
  functorPushforward_imageSieve_mem c := by
    have hmem : u.imageSieve c ∈ J _ := IsSourceLocallyFull.imageSieve_mem c
    sorry

private theorem isLocallyFaithful_of_isSourceLocallyFaithful
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [u.IsCocontinuous J K] [IsSourceLocallyFaithful u J] :
    u.IsLocallyFaithful K where
  functorPushforward_equalizer_mem a b h := by
    have hmem : Sieve.equalizer a b ∈ J _ := IsSourceLocallyFaithful.equalizer_mem a b h
    sorry

end CategoryTheory.Functor

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

private theorem functorPushforward_mem_iff_of_source_local
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [Functor.IsSourceLocallyFaithful u J] [Functor.IsSourceLocallyFull u J] [u.IsCoverDense K]
    {X : C} {S : Sieve X} :
    S.functorPushforward u ∈ K (u.obj X) ↔ S ∈ J X := by
  sorry

/-- The comparison-lemma hypotheses refine to mathlib's canonical dense-subsite owner. -/
theorem sourceLocal_isDenseSubsite
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [Functor.IsSourceLocallyFaithful u J] [Functor.IsSourceLocallyFull u J] [u.IsCoverDense K] :
    u.IsDenseSubsite J K where
  isLocallyFull' := Functor.isLocallyFull_of_isSourceLocallyFull J K u
  isLocallyFaithful' := Functor.isLocallyFaithful_of_isSourceLocallyFaithful J K u
  functorPushforward_mem_iff := functorPushforward_mem_iff_of_source_local u

/-- The comparison-lemma hypotheses refine to mathlib's canonical dense-subsite owner. -/
instance isDenseSubsite_of_source_local
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [Functor.IsSourceLocallyFaithful u J] [Functor.IsSourceLocallyFull u J] [u.IsCoverDense K] :
    u.IsDenseSubsite J K :=
  sourceLocal_isDenseSubsite u

attribute [instance 100] isDenseSubsite_of_source_local

private theorem sheafPushforwardContinuous_isEquivalence_of_source_local
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [Functor.IsSourceLocallyFaithful u J] [Functor.IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P] :
    (u.sheafPushforwardContinuous (Type w) J K).IsEquivalence := by
  letI : u.IsDenseSubsite J K := isDenseSubsite_of_source_local u
  sorry

-- Proof sketch: the source-local hypotheses upgrade to mathlib's canonical dense-subsite owner,
-- whose comparison-lemma API gives the continuous pushforward equivalence after the required
-- right-Kan-extension bridge is supplied. Applying the adjunction between continuous inverse image
-- and cocontinuous direct image then shows that the right adjoint is also an equivalence.
/-- Lemma 7.29.1: if `u : C ⥤ D` is continuous, cocontinuous, source-locally faithful,
source-locally full, and cover-dense, then the direct-image functor on sheaves of sets attached to
`u` is an equivalence of categories; equivalently, the morphism of topoi associated to `u` is an
equivalence. -/
lemma comparison_directImage_isEquivalence
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [Functor.IsSourceLocallyFaithful u J] [Functor.IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P] :
    (u.sheafPushforwardCocontinuous (Type w) J K).IsEquivalence := by
  letI : (u.sheafPushforwardContinuous (Type w) J K).IsEquivalence :=
    sheafPushforwardContinuous_isEquivalence_of_source_local u
  exact (u.sheafAdjunctionCocontinuous (Type w) J K).isEquivalence_right_of_isEquivalence_left

end

end CategoryTheory
