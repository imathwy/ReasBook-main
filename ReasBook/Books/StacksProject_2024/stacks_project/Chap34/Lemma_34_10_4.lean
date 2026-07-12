import Mathlib
import StacksProject_2024.Chap26.Lemma_26_17_2
import StacksProject_2024.Chap34.Definition_34_10_1

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace AffineFamilyOver

noncomputable section

section

variable {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']

-- Semantic recall: local Chapter 34 precedent already packages standard `V` coverings of affine
-- schemes as finite affine families `AffineFamilyOver T` with the owner
-- `AffineFamilyOver.IsStandardVCover`. This item is therefore the base-change bridge on that
-- existing owner, not a second public covering predicate.

/-- The base change of a finite affine family along a morphism of affine schemes. -/
def pullback (𝒰 : AffineFamilyOver T) (g : T' ⟶ T) : AffineFamilyOver T' where
  n := 𝒰.n
  U := fun j ↦ Limits.pullback g (𝒰.map j)
  map := fun j ↦ Limits.pullback.fst g (𝒰.map j)
  isAffine := fun j ↦ by
    letI : IsAffine (𝒰.U j) := 𝒰.isAffine j
    infer_instance

/-- The `j`-th structure morphism of the pullback family is the canonical first projection from
the categorical pullback. -/
@[simp] theorem pullback_map (𝒰 : AffineFamilyOver T) (g : T' ⟶ T) (j : Fin 𝒰.n) :
    (pullback 𝒰 g).map j = Limits.pullback.fst g (𝒰.map j) :=
  rfl

/-- The pullback family is the canonical base change of `𝒰` along `g` in the repository's
`AffineFamilyOver.IsBaseChangeOf` sense. -/
def pullback_isBaseChangeOf (𝒰 : AffineFamilyOver T) (g : T' ⟶ T) :
    AffineFamilyOver.IsBaseChangeOf g 𝒰 (pullback 𝒰 g) where
  indexEquiv := Equiv.refl _
  componentIso := fun j ↦ Iso.refl _
  map_eq := fun j ↦ by
    change 𝟙 (Limits.pullback g (𝒰.map j)) ≫ Limits.pullback.fst g (𝒰.map j) =
        Limits.pullback.fst g (𝒰.map j)
    exact Category.id_comp (Limits.pullback.fst g (𝒰.map j))

/-- The pullback-family base-change witness is identity on indices. -/
@[simp] theorem pullback_isBaseChangeOf_indexEquiv
    (𝒰 : AffineFamilyOver T) (g : T' ⟶ T) (j : Fin 𝒰.n) :
    (pullback_isBaseChangeOf 𝒰 g).indexEquiv j = j :=
  rfl

/-- The pullback-family base-change witness uses the identity isomorphism on each pullback
component. -/
@[simp] theorem pullback_isBaseChangeOf_componentIso_hom
    (𝒰 : AffineFamilyOver T) (g : T' ⟶ T) (j : Fin 𝒰.n) :
    ((pullback_isBaseChangeOf 𝒰 g).componentIso j).hom = 𝟙 _ :=
  rfl

/-- The pullback-family base-change witness is compatible with the structure maps to the new
base. -/
theorem pullback_isBaseChangeOf_map_eq
    (𝒰 : AffineFamilyOver T) (g : T' ⟶ T) (j : Fin 𝒰.n) :
    ((pullback_isBaseChangeOf 𝒰 g).componentIso j).hom ≫
        (pullback 𝒰 g).map ((pullback_isBaseChangeOf 𝒰 g).indexEquiv j) =
      Limits.pullback.fst g (𝒰.map j) :=
  (pullback_isBaseChangeOf 𝒰 g).map_eq j

/-- Lemma 34.10.4: the base change of a standard `V` covering along a morphism of affine schemes
is again a standard `V` covering. -/
theorem IsStandardVCover.pullback {𝒰 : AffineFamilyOver T} (h𝒰 : IsStandardVCover 𝒰)
    (g : T' ⟶ T) :
    IsStandardVCover (pullback 𝒰 g) := sorry

/-- A standard `V` covering remains a standard `V` covering after base change along a morphism of
affine schemes. -/
instance instIsStandardVCoverPullback (𝒰 : AffineFamilyOver T) [IsStandardVCover 𝒰]
    (g : T' ⟶ T) : IsStandardVCover (pullback 𝒰 g) :=
  IsStandardVCover.pullback ‹IsStandardVCover 𝒰› g

end

end

end AffineFamilyOver

end AlgebraicGeometry
