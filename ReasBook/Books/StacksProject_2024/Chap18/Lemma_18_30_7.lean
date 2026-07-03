import Mathlib
import StacksProject_2024.Chap18.Lemma_18_30_4
import StacksProject_2024.Chap18.Lemma_18_30_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type u)]
variable [HasFiniteCoproducts (Sheaf J (Type u))]
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

/-- A sheaf of sets has a finite basis coequalizer presentation if it is isomorphic to the
coequalizer of two maps between finite coproducts of sheafified representables `h_U^#` built from
objects of `B`. -/
abbrev HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation
    (ℱ : Sheaf J (Type u)) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    let _ : HasColimitsOfShape (Discrete (Fin m)) (Sheaf J (Type u)) :=
      Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin m)
    let _ : HasColimitsOfShape (Discrete (Fin n)) (Sheaf J (Type u)) :=
      Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin n)
    let _ : HasColimitsOfShape WalkingParallelPair (Sheaf J (Type u)) :=
      (Sheaf.instHasColimitsOfShape :
        HasColimitsOfShape WalkingParallelPair (Sheaf J (Type u)))
    ∃ (left right :
      (∐ fun j : Fin m ↦ h[V j]^#[J]) ⟶
        (∐ fun i : Fin n ↦ h[U i]^#[J]))
      (_ : ℱ ≅ coequalizer left right),
        (∀ i, U i ∈ B) ∧
          ∀ j, V j ∈ B

-- Proof sketch: first use Lemma `18.30.6` in Situation `18.30.5` to write `ℱ` as the
-- coequalizer of a pair of maps between possibly infinite coproducts of basis sheafified
-- representables. Then use quasi-compactness of basis objects together with the finite-subcoproduct
-- argument from Lemma `7.17.7` to express that coequalizer as a filtered colimit over finite
-- subdiagrams.
/-- Lemma 18.30.7 (1): in Situation `18.30.5`, every sheaf of sets is a filtered colimit of
sheaves admitting finite coequalizer presentations by sheafified representables `h_U^#` with
`U ∈ B`. -/
theorem exists_filteredColimitPresentation_by_finite_basis_sheafifiedRepresentable_coequalizers
    (ℱ : Sheaf J (Type u)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (pres : ColimitPresentation I ℱ),
        ∀ i, HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B (pres.diag.obj i) :=
  sorry

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u}) (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

/-- An `\mathcal O`-module has a finite basis cokernel presentation if it is isomorphic to the
cokernel of a map between finite coproducts of the extensions by zero `j_{U!}\mathcal O_U` built
from objects of `B`. -/
abbrev HasFiniteBasisConstructibleModuleCokernelPresentation
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    ∃ (f :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
      (_ : ℱ ≅ cokernel f),
        (∀ i, U i ∈ B) ∧
          ∀ j, V j ∈ B

-- Proof sketch: start from the epimorphism of Lemma `18.30.6 (2)` available in Situation
-- `18.30.5` from a possibly infinite direct sum of modules `j_{U!}\mathcal O_U` with `U ∈ B`.
-- Apply Lemma `18.30.4` to the quasi-compact basis objects to show that morphisms out of the
-- finite source pieces factor through finite subcoproducts, so the resulting cokernels over
-- finite subdiagrams form a filtered colimit presentation of `ℱ`.
/-- Lemma 18.30.7 (2): in Situation `18.30.5`, every `\mathcal O`-module is a filtered colimit
of modules admitting finite cokernel presentations by sums of the extensions by zero
`j_{U!}\mathcal O_U` with `U ∈ B`. -/
theorem exists_filteredColimitPresentation_by_finite_basis_constructibleModule_cokernels
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (pres : ColimitPresentation I ℱ),
        ∀ i, HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (pres.diag.obj i) :=
  sorry

end SheafOfModules.RingedSite
