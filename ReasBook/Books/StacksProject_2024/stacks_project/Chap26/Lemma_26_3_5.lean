import Mathlib.Geometry.RingedSpace.OpenImmersion
import StacksProject_2024.Chap06.Definition_6_25_1

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

-- Semantic recall: `lean_leansearch` surfaced the restriction and open-immersion API around
-- `LocallyRingedSpace.restrict`, `LocallyRingedSpace.ofRestrict`, and
-- `LocallyRingedSpace.IsOpenImmersion.lift`, together with the canonical open-preimage owner
-- `Opens.map`, which is used by the restriction construction below.

section

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
variable (U : Opens X) (V : Opens Y)

local notation "XU" => X.restrict U.isOpenEmbedding
local notation "YV" => Y.restrict V.isOpenEmbedding
local notation "jU" => X.ofRestrict U.isOpenEmbedding
local notation "jV" => Y.ofRestrict V.isOpenEmbedding

/-- The composite `jU ≫ f` lands in the open subspace `Y|_V` when `f(U) ⊆ V`. -/
private theorem restrictToOpen_lift_condition
    (hUV : U ≤ preimageOpen f.toShHom V) :
    Set.range ((jU ≫ f).base) ⊆ Set.range (Y.ofRestrict V.isOpenEmbedding).base := by
  intro y
  rintro ⟨x, rfl⟩
  exact ⟨⟨f.base x.1, hUV x.2⟩, rfl⟩

/-- The restricted morphism induced by a morphism `f : X ⟶ Y` that maps the open subset `U ⊆ X`
into the open subset `V ⊆ Y`. -/
def restrictToOpen (hUV : U ≤ preimageOpen f.toShHom V) :
    XU ⟶ YV :=
  LocallyRingedSpace.IsOpenImmersion.lift jV (jU ≫ f)
    (restrictToOpen_lift_condition f U V hUV)

@[reassoc]
theorem restrictToOpen_fac (hUV : U ≤ preimageOpen f.toShHom V) :
    restrictToOpen f U V hUV ≫ jV = jU ≫ f := by
  simpa [restrictToOpen] using
    LocallyRingedSpace.IsOpenImmersion.lift_fac jV (jU ≫ f)
      (restrictToOpen_lift_condition f U V hUV)

/-- The restricted morphism makes the evident square with the ambient inclusions commute. -/
theorem restrictToOpen_commSq (hUV : U ≤ preimageOpen f.toShHom V) :
    CommSq jU (restrictToOpen f U V hUV) f jV := by
  refine CommSq.mk ?_
  simpa using (restrictToOpen_fac f U V hUV).symm

theorem restrictToOpen_uniq
    (hUV : U ≤ preimageOpen f.toShHom V)
    (f' : XU ⟶ YV)
    (hcomm : CommSq jU f' f jV) :
    f' = restrictToOpen f U V hUV := by
  exact LocallyRingedSpace.IsOpenImmersion.lift_uniq jV (jU ≫ f)
    (restrictToOpen_lift_condition f U V hUV) f' <| by
      simpa using hcomm.w.symm

/-- The universal property of `restrictToOpen`: a morphism into `Y|_V` is the canonical
restriction precisely when it makes the evident square with the ambient inclusions commute. -/
theorem restrictToOpen_eq_iff
    (hUV : U ≤ preimageOpen f.toShHom V)
    (f' : XU ⟶ YV) :
    f' = restrictToOpen f U V hUV ↔ CommSq jU f' f jV := by
  constructor
  · rintro rfl
    exact restrictToOpen_commSq f U V hUV
  · exact fun hcomm ↦ restrictToOpen_uniq f U V hUV f' hcomm

/-- The canonical restricted morphism `f⁻¹(V) ⟶ V` induced by `f`. -/
abbrev pullbackToPreimageOpenMorphism :
    X.restrict (preimageOpen f.toShHom V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  restrictToOpen f (preimageOpen f.toShHom V) V le_rfl

@[reassoc]
theorem pullbackToPreimageOpenMorphism_fac :
    pullbackToPreimageOpenMorphism f V ≫ jV =
      X.ofRestrict (preimageOpen f.toShHom V).isOpenEmbedding ≫ f := by
  simpa [pullbackToPreimageOpenMorphism] using
    restrictToOpen_fac f (preimageOpen f.toShHom V) V le_rfl

/-- The canonical restricted morphism `f^{-1}(V) ⟶ V` makes the expected square with the ambient
inclusions commute. -/
theorem pullbackToPreimageOpenMorphism_commSq :
    CommSq
      (X.ofRestrict (preimageOpen f.toShHom V).isOpenEmbedding)
      (pullbackToPreimageOpenMorphism f V) f jV := by
  simpa [pullbackToPreimageOpenMorphism] using
    restrictToOpen_commSq f (preimageOpen f.toShHom V) V le_rfl

theorem pullbackToPreimageOpenMorphism_uniq
    (f' :
      X.restrict (preimageOpen f.toShHom V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding)
    (hcomm :
      CommSq
        (X.ofRestrict (preimageOpen f.toShHom V).isOpenEmbedding)
        f' f jV) :
    f' = pullbackToPreimageOpenMorphism f V := by
  simpa [pullbackToPreimageOpenMorphism] using
    restrictToOpen_uniq f (preimageOpen f.toShHom V) V le_rfl f' hcomm

/-- The universal property of the canonical preimage-open morphism `f^{-1}(V) ⟶ V`. -/
theorem pullbackToPreimageOpenMorphism_eq_iff
    (f' :
      X.restrict (preimageOpen f.toShHom V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding) :
    f' = pullbackToPreimageOpenMorphism f V ↔
      CommSq
        (X.ofRestrict (preimageOpen f.toShHom V).isOpenEmbedding)
        f' f jV := by
  simpa [pullbackToPreimageOpenMorphism] using
    (restrictToOpen_eq_iff f (preimageOpen f.toShHom V) V le_rfl f')

/-- Lemma 26.3.5: if `f : X ⟶ Y` maps the open subset `U ⊆ X` into the open subset `V ⊆ Y`,
then the canonical restricted morphism `restrictToOpen` is the unique morphism `U ⟶ V` of locally
ringed spaces making the evident square with the ambient inclusions commute. -/
@[stacks 01HI]
theorem existsUnique_restrictToOpen
    (hUV : U ≤ preimageOpen f.toShHom V) :
    ∃! f' : XU ⟶ YV,
      CommSq jU f' f jV := by
  refine ⟨restrictToOpen f U V hUV, restrictToOpen_commSq f U V hUV, ?_⟩
  intro f' hcomm
  exact restrictToOpen_uniq f U V hUV f' hcomm

end

end AlgebraicGeometry.LocallyRingedSpace
