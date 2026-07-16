import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import StacksProject_2024.stacks_project.Chap13.Definition_13_19_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_27_1
import StacksProject_2024.stacks_project.Chap13.«13_3_5_1»
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_8
import StacksProject_2024.stacks_project.Chap13.Lemma_13_27_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape DerivedCategory HomotopyCategory HomologicalComplex
open CochainComplex.HomComplex.CohomologyClass
open Pretriangulated
open scoped DerivedExt

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

private noncomputable abbrev derivedExtFunctor
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat R)) (n : ℤ) :
    ModuleCat R ⥤ ModuleCat (End K)ᵐᵒᵖ :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ) ⋙ shiftFunctor _ n ⋙ preadditiveCoyonedaObj K

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "singleCpx₀" => CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (up ℤ)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

/-- Helper for Lemma 15.66.1: the functor `M ↦ Ext^n_R(K, M)` on `R`-modules, with `K` fixed in
`D(R)`, obtained from the canonical `ModuleCat (End K)ᵐᵒᵖ`-valued owner by forgetting to abelian
groups. -/
noncomputable abbrev derivedExtToModuleFunctor
    (K : DMod) (n : ℤ) :
    ModuleCat R ⥤ AddCommGrpCat :=
  derivedExtFunctor K n ⋙ forget₂ _ AddCommGrpCat

/-- Helper for Lemma 15.66.1: an isomorphism on source and target objects induces an additive
equivalence on the corresponding Hom groups. -/
private theorem iso_hom_congr_add_equiv_map_add
    {X Y X₁ Y₁ : DMod} (α : X ≅ X₁) (β : Y ≅ Y₁) (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 15.66.1: an isomorphism on source and target objects induces an additive
equivalence on the corresponding Hom groups. -/
private noncomputable def iso_hom_congr_add_equiv
    {X Y X₁ Y₁ : DMod} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := α.homCongr β
    map_add' := iso_hom_congr_add_equiv_map_add α β }

/-- Helper for Lemma 15.66.1: for a bounded-above projective complex, shifted homotopy morphisms
into a complex identify additively with shifted derived morphisms. -/
private noncomputable def homotopy_shifted_hom_add_equiv
    (P : CochainComplex.ProjectiveMinus (ModuleCat R)) (L : Cpx) (n : ℤ) :
    ((KQ).obj P ⟶ (KQ).obj (L⟦n⟧)) ≃+ CategoryTheory.ShiftedHom (Q.obj P) (Q.obj L) n :=
  let e₁ :
      ((KQ).obj P ⟶ (KQ).obj (L⟦n⟧)) ≃+
        ((Q.obj P) ⟶ (Q.obj (L⟦n⟧))) :=
    AddEquiv.ofBijective
      (Qh.mapAddHom :
        ((KQ).obj P ⟶ (KQ).obj (L⟦n⟧)) →+ ((Q.obj P) ⟶ (Q.obj (L⟦n⟧))))
      (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective P (L⟦n⟧))
  let e₂ :
      ((Q.obj P) ⟶ (Q.obj (L⟦n⟧))) ≃+
        CategoryTheory.ShiftedHom (Q.obj P) (Q.obj L) n :=
    iso_hom_congr_add_equiv (Iso.refl _) ((Q.commShiftIso n).app L)
  e₁.trans e₂

/-- Helper for Lemma 15.66.1: the Hom complex from a bounded-above projective complex to a
degree-zero module computes derived `Ext` against that module. -/
noncomputable def projective_minus_homology_add_equiv_shiftedHom_single0
    (P : CochainComplex.ProjectiveMinus (ModuleCat R)) (M : ModuleCat R) (n : ℤ) :
    (CochainComplex.HomComplex P ((singleCpx₀).obj M)).homology n ≃+ Ext^n(Q.obj P, (single₀).obj M) :=
  let e₁ :
      (CochainComplex.HomComplex P ((singleCpx₀).obj M)).homology n ≃+
        ((KQ).obj P ⟶ (KQ).obj (((singleCpx₀).obj M)⟦n⟧)) :=
    (CochainComplex.HomComplex.homologyAddEquiv P ((singleCpx₀).obj M) n).trans homAddEquiv
  let e₂ :
      ((KQ).obj P ⟶ (KQ).obj (((singleCpx₀).obj M)⟦n⟧)) ≃+
        Ext^n(Q.obj P, (single₀).obj M) :=
    homotopy_shifted_hom_add_equiv P ((singleCpx₀).obj M) n
  e₁.trans e₂

/-- Helper for Lemma 15.66.1: an `m`-pseudo-coherent object admits a bounded-above projective
approximation by a termwise finite free complex with the expected cohomology control. -/
theorem exists_projectiveMinus_approximation_of_isMPseudoCoherent
    (K : DMod) (m : ℤ) (hK : K.IsMPseudoCoherent m) :
    ∃ P : CochainComplex.ProjectiveMinus (ModuleCat R),
      (∃ a : ℤ, (P : Cpx).IsStrictlyGE a) ∧
      (∀ i : ℤ, Module.Finite R ((P : Cpx).X i)) ∧
      ∃ α : Q.obj (P : Cpx) ⟶ K,
        (∀ i : ℤ, m < i → IsIso ((H i).map α)) ∧
          Epi ((H m).map α) := by
  rcases hK with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαiso, hαepi⟩
  let P : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hEb⟩⟩,
      fun i ↦ by
        letI : CochainComplex.IsTermwiseFiniteFree E := hEfree
        exact inferInstance⟩
  refine ⟨P, ⟨a, hEa⟩, ?_, α, hαiso, hαepi⟩
  intro i
  simpa [P] using (show Module.Finite R (E.X i) by infer_instance)

/-- Helper for Lemma 15.66.1: the pseudo-coherent approximation can be packaged as a
`ProjectiveMinus` complex while retaining the termwise finite free information degreewise. -/
theorem exists_projectiveMinus_finiteFree_approximation_of_isMPseudoCoherent
    (K : DMod) (m : ℤ) (hK : K.IsMPseudoCoherent m) :
    ∃ P : CochainComplex.ProjectiveMinus (ModuleCat R),
      (∃ a : ℤ, (P : Cpx).IsStrictlyGE a) ∧
      (∀ i : ℤ, Module.Free R ((P : Cpx).X i)) ∧
      (∀ i : ℤ, Module.Finite R ((P : Cpx).X i)) ∧
      ∃ α : Q.obj (P : Cpx) ⟶ K,
        (∀ i : ℤ, m < i → IsIso ((H i).map α)) ∧
          Epi ((H m).map α) := by
  rcases hK with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαiso, hαepi⟩
  let P : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hEb⟩⟩,
      fun i ↦ by
        letI : CochainComplex.IsTermwiseFiniteFree E := hEfree
        exact inferInstance⟩
  refine ⟨P, ⟨a, hEa⟩, ?_, ?_, α, hαiso, hαepi⟩
  · intro i
    simpa [P] using (show Module.Free R (E.X i) by
      letI : CochainComplex.IsTermwiseFiniteFree E := hEfree
      infer_instance)
  · intro i
    simpa [P] using (show Module.Finite R (E.X i) by
      letI : CochainComplex.IsTermwiseFiniteFree E := hEfree
      infer_instance)

/-- Lemma 15.66.1 (1): if `M = colim_i M_i` is a filtered colimit of `R`-modules and `K` is
`m`-pseudo-coherent in `D(R)`, then the canonical map
`\mathop{\mathrm{colim}}_i \operatorname{Ext}^n_R(K, M_i) \to \operatorname{Ext}^n_R(K, M)` is an
isomorphism for `n < -m`. -/
theorem derivedExtFilteredColimitComparison_isIso_of_isMPseudoCoherent
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (K : DMod) (m n : ℤ) (hK : K.IsMPseudoCoherent m)
    (F : J ⥤ ModuleCat R) (hn : n < -m) :
    IsIso (colimit.post F (derivedExtToModuleFunctor K n)) := by
  let _ := hK
  let _ := F
  let _ := hn
  sorry

/-- Lemma 15.66.1 (2): if `M = colim_i M_i` is a filtered colimit of `R`-modules and `K` is
`m`-pseudo-coherent in `D(R)`, then the canonical map
`\mathop{\mathrm{colim}}_i \operatorname{Ext}^{-m}_R(K, M_i) \to
\operatorname{Ext}^{-m}_R(K, M)` is injective. -/
theorem derivedExtFilteredColimitComparison_mono_at_neg_of_isMPseudoCoherent
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (K : DMod) (m : ℤ) (hK : K.IsMPseudoCoherent m)
    (F : J ⥤ ModuleCat R) :
    Mono (colimit.post F (derivedExtToModuleFunctor K (-m))) := by
  let _ := hK
  let _ := F
  sorry

end

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- Helper for Lemma 15.66.1: the `A`-linear Ext functor `M ↦ Ext^i_A(K, M)` on `A`-modules. -/
noncomputable abbrev derivedExtModuleFunctor
    (K : DMod) (i : ℤ) :
    ModuleCat A ⥤ ModuleCat A :=
  DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ) ⋙
    shiftFunctor _ i ⋙
    preadditiveCoyonedaObj K ⋙
    ModuleCat.restrictScalars (algebraMap A (End K)ᵐᵒᵖ)

end

end CategoryTheory
