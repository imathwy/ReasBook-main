import StacksProject_2024.stacks_project.Chap34.Definition_34_10_1

open CategoryTheory

universe u

namespace AlgebraicGeometry

noncomputable section

namespace AffineFamilyOver

section

variable {T : Scheme.{u}}

/- Reindex a finite family over an arbitrary finite type by `Fin (Fintype.card I)`. -/
private def ofFiniteFamily (I : Type*) [Fintype I] (U : I → Scheme.{u}) (map : (i : I) → U i ⟶ T)
    (isAffine : ∀ i, IsAffine (U i)) : AffineFamilyOver T where
  n := Fintype.card I
  U := fun j ↦ U ((Fintype.equivFin I).symm j)
  map := fun j ↦ map ((Fintype.equivFin I).symm j)
  isAffine := fun j ↦ isAffine ((Fintype.equivFin I).symm j)

/-- The sigma-indexed composite of a finite affine family over `T` with finite affine families over
its members. -/
def comp (𝒰 : AffineFamilyOver T) (𝒱 : (i : Fin 𝒰.n) → AffineFamilyOver (𝒰.U i)) :
    AffineFamilyOver T :=
  ofFiniteFamily
    (Sigma fun i : Fin 𝒰.n ↦ Fin (𝒱 i).n)
    (fun p ↦ (𝒱 p.1).U p.2)
    (fun p ↦ (𝒱 p.1).map p.2 ≫ 𝒰.map p.1)
    (fun p ↦ (𝒱 p.1).isAffine p.2)

/-- The `k`-th structure morphism in the composite family is the corresponding member of `𝒱`
composed with the ambient member of `𝒰`. -/
@[simp] theorem comp_map (𝒰 : AffineFamilyOver T)
    (𝒱 : (i : Fin 𝒰.n) → AffineFamilyOver (𝒰.U i))
    (k : Fin (𝒰.comp 𝒱).n) :
    (𝒰.comp 𝒱).map k =
      let p := (Fintype.equivFin (Sigma fun i : Fin 𝒰.n ↦ Fin (𝒱 i).n)).symm k
      (𝒱 p.1).map p.2 ≫ 𝒰.map p.1 :=
  rfl

variable [IsAffine T]

/-- Lemma 34.10.5: if `𝒰` is a standard `V` covering of an affine scheme and each member admits a
standard `V` covering `𝒱 i`, then the sigma-indexed composite family is a standard `V`
covering. -/
@[stacks 0ETE]
theorem IsStandardVCover.comp {𝒰 : AffineFamilyOver T} (h𝒰 : IsStandardVCover 𝒰)
    (𝒱 : (i : Fin 𝒰.n) → AffineFamilyOver (𝒰.U i)) (h𝒱 : ∀ i, IsStandardVCover (𝒱 i)) :
    IsStandardVCover (𝒰.comp 𝒱) := sorry

/-- A composite of standard `V` coverings is again a standard `V` covering. -/
instance instIsStandardVCoverComp (𝒰 : AffineFamilyOver T) [IsStandardVCover 𝒰]
    (𝒱 : (i : Fin 𝒰.n) → AffineFamilyOver (𝒰.U i)) [∀ i, IsStandardVCover (𝒱 i)] :
    IsStandardVCover (𝒰.comp 𝒱) :=
  IsStandardVCover.comp ‹IsStandardVCover 𝒰› 𝒱 fun i ↦ inferInstance

end

end AffineFamilyOver

end

end AlgebraicGeometry
