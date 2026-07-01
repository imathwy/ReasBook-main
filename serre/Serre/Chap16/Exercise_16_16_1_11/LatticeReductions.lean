import Serre.Chap16.Exercise_16_16_1_11.RationalSignCharacters

noncomputable section

open CategoryTheory
open Representation
open scoped Representation SubgroupInduction

namespace Exercise_16_16_1_11

section

variable {G : Type} [Group G]

variable {A : Type} [CommRing A] [IsLocalRing A] [Algebra A ℚ] [IsFractionRing A ℚ]

local notation "k" => IsLocalRing.ResidueField A

variable [CharP (IsLocalRing.ResidueField A) 5]
variable [Finite G] [IsCyclic G] (hG : Nat.card G = 4)

local instance latticeReductionsFintype : Fintype G := Fintype.ofFinite G
local instance latticeReductionsCommGroup : CommGroup G := IsCyclic.commGroup
local instance latticeReductionsIsDomain : IsDomain A := (IsFractionRing.injective A ℚ).isDomain
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Helper for Exercise 16-16.1-11: the explicit stable lattice in a rational unit-character line
is the image of `A` inside `ℚ`. -/
noncomputable def unit_character_line_lattice
    (β : G →* Aˣ) :
    StableLattice A
      (FDRep.of
        (unitCharacterToRepresentation
          (((Units.map (algebraMap A ℚ).toMonoidHom).comp β) : G →* ℚˣ))).ρ where
  toSubmodule := Submodule.map (Algebra.linearMap A ℚ) ⊤
  apply_mem_toSubmodule g := by
    intro x hx
    rcases Submodule.mem_map.1 hx with ⟨a, -, rfl⟩
    refine Submodule.mem_map.2 ?_
    refine ⟨(β g : A) * a, by simp, ?_⟩
    change (algebraMap A ℚ) ((β g : A) * a) =
      ((FDRep.of
        (unitCharacterToRepresentation
          (((Units.map (algebraMap A ℚ).toMonoidHom).comp β) : G →* ℚˣ))).ρ g)
        ((algebraMap A ℚ) a)
    simp [unitCharacterToRepresentation, LinearMap.lsmul_apply, map_mul]
  isLattice := by
    refine ⟨?_, ?_⟩
    · simpa [Submodule.map_top] using
        (Submodule.fg_span (Set.toFinite ({(1 : ℚ)} : Set ℚ)))
    · refine le_antisymm le_top ?_
      intro x _
      have hone :
          (1 : ℚ) ∈
            (Submodule.map (Algebra.linearMap A ℚ) (⊤ : Submodule A A) : Submodule A ℚ) := by
        refine Submodule.mem_map.2 ?_
        exact ⟨1, by simp, by simp⟩
      simpa using
        Submodule.smul_mem
          (Submodule.span ℚ
            ((Submodule.map (Algebra.linearMap A ℚ) (⊤ : Submodule A A) :
              Submodule A ℚ) : Set ℚ))
          x
          (Submodule.subset_span hone)

/-- Helper for Exercise 16-16.1-11: reducing the explicit image lattice in a rational
unit-character line is already `A / 𝔪_A` at the `A`-linear level. -/
noncomputable def unit_character_line_reduction_equiv_over_A
    (β : G →* Aˣ) :
    k ≃ₗ[A] (unit_character_line_lattice (A := A) (G := G) β).reduction := by
  let eMap :
      (⊤ : Submodule A A) ≃ₗ[A]
        (unit_character_line_lattice (A := A) (G := G) β).toSubmodule :=
    Submodule.equivMapOfInjective
      (Algebra.linearMap A ℚ)
      (IsFractionRing.injective A ℚ)
      ⊤
  let eTopQuot :
      ((⊤ : Submodule A A) ⧸
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (⊤ : Submodule A A)))) ≃ₗ[A]
          (unit_character_line_lattice (A := A) (G := G) β).reduction := by
    refine Submodule.Quotient.equiv _ _ eMap ?_
    change
      ((IsLocalRing.maximalIdeal A • (⊤ : Submodule A (⊤ : Submodule A A))).map
          eMap.toLinearMap) =
        IsLocalRing.maximalIdeal A •
          (⊤ :
            Submodule A
              (unit_character_line_lattice (A := A) (G := G) β).toSubmodule)
    simp [eMap]
  let eAQuotTop :
      ((⊤ : Submodule A A) ⧸
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (⊤ : Submodule A A)))) ≃ₗ[A]
          (A ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A A))) :=
    Submodule.Quotient.equiv _ _ (Submodule.topEquiv : (⊤ : Submodule A A) ≃ₗ[A] A) (by simp)
  let eAQuot :
      (A ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A A))) ≃ₗ[A] k :=
    Submodule.quotEquivOfEq _ _ (by simp)
  exact eAQuot.symm.trans (eAQuotTop.symm.trans eTopQuot)

/-- Helper for Exercise 16-16.1-11: an `A`-linear equivalence between residue-field modules is
already `k`-linear because every scalar in `k` lifts from `A`. -/
noncomputable def residue_field_linear_equiv_of_linear_equiv
    {V W : Type*}
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower A k V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower A k W]
    (e : V ≃ₗ[A] W) : V ≃ₗ[k] W where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' c x := by
    obtain ⟨a, rfl⟩ :
        ∃ a : A, (algebraMap A k a : k) = c := by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using
        (IsLocalRing.residue_surjective (R := A) c)
    show e ((algebraMap A k a) • x) = ((algebraMap A k a : k) • e x)
    simpa only [IsScalarTower.algebraMap_smul] using e.map_smul a x

/-- Helper for Exercise 16-16.1-11: the explicit quotient-coordinate equivalence on the reduced
unit-character line is available over the residue field itself. -/
noncomputable def unit_character_line_reduction_equiv
    (β : G →* Aˣ) :
    k ≃ₗ[k] (unit_character_line_lattice (A := A) (G := G) β).reduction := by
  letI :
      IsScalarTower A k
        (unit_character_line_lattice (A := A) (G := G) β).reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact
    residue_field_linear_equiv_of_linear_equiv
      (unit_character_line_reduction_equiv_over_A (A := A) (G := G) β)

/-- Helper for Exercise 16-16.1-11: for finitely supported functions, the coordinatewise ideal
submodule is exactly the ideal multiple of the full module. -/
theorem finsupp_submodule_eq_smul_top
    (X : Type) (I : Ideal A) :
    Finsupp.submodule (α := X) (R := A) (fun _ => (I : Submodule A A)) =
      I • (⊤ : Submodule A (X →₀ A)) := by
  refine le_antisymm ?_ ?_
  · intro f hf
    classical
    rw [← f.sum_single]
    refine Submodule.sum_mem _ ?_
    intro x hx
    have hcoeff : f x ∈ I := hf x
    simpa [Finsupp.smul_single_one] using
      Submodule.smul_mem_smul hcoeff
        (show Finsupp.single x (1 : A) ∈ (⊤ : Submodule A (X →₀ A)) by simp)
  · intro f hf
    refine Submodule.smul_induction_on hf ?_ ?_
    · intro a ha g hg
      exact fun x => by
        simpa [Finsupp.smul_apply] using I.mul_mem_right (g x) ha
    · intro f g hf hg
      exact fun x => I.add_mem (hf x) (hg x)

/-- Helper for Exercise 16-16.1-11: the rational permutation representation on a finite `G`-set
contains the obvious coefficientwise `A`-lattice. -/
noncomputable def permutation_lattice
    (X : Type) [MulAction G X] [Finite X] :
    StableLattice A (FDRep.of (ofMulAction ℚ G X)).ρ where
  toSubmodule :=
    Submodule.map (Finsupp.mapRange.linearMap (α := X) (Algebra.linearMap A ℚ)) ⊤
  apply_mem_toSubmodule g := by
    intro x hx
    rcases Submodule.mem_map.1 hx with ⟨f, -, rfl⟩
    refine Submodule.mem_map.2 ?_
    refine ⟨(ofMulAction A G X) g f, by simp, ?_⟩
    simpa using
      (show
        Finsupp.mapRange.linearMap (α := X) (Algebra.linearMap A ℚ) ((ofMulAction A G X) g f) =
          (ofMulAction ℚ G X) g
            (Finsupp.mapRange.linearMap (α := X) (Algebra.linearMap A ℚ) f) by
          ext y
          simp [Representation.ofMulAction_apply, Finsupp.mapRange.linearMap_apply])
  isLattice := by
    refine ⟨?_, ?_⟩
    · simpa using
        Submodule.FG.map
          (f := Finsupp.mapRange.linearMap (α := X) (Algebra.linearMap A ℚ))
          Module.Finite.fg_top
    · refine le_antisymm le_top ?_
      have hsubset :
          Set.range (Finsupp.basisSingleOne (R := ℚ) (ι := X)) ⊆
            ((Submodule.map
              (Finsupp.mapRange.linearMap (α := X) (Algebra.linearMap A ℚ))
              (⊤ : Submodule A (X →₀ A)) : Submodule A (X →₀ ℚ)) : Set (X →₀ ℚ)) := by
        intro v hv
        rcases hv with ⟨x, rfl⟩
        refine Submodule.mem_map.2 ?_
        refine ⟨Finsupp.single x 1, by simp, ?_⟩
        simp [Finsupp.mapRange.linearMap_apply, Algebra.linearMap_apply]
      calc
        ⊤ = Submodule.span ℚ (Set.range (Finsupp.basisSingleOne (R := ℚ) (ι := X))) := by
          symm
          simpa using (Finsupp.basisSingleOne (R := ℚ) (ι := X)).span_eq
        _ ≤ Submodule.span ℚ
              (((Submodule.map
                (Finsupp.mapRange.linearMap (α := X) (Algebra.linearMap A ℚ))
                (⊤ : Submodule A (X →₀ A)) : Submodule A (X →₀ ℚ)) : Set (X →₀ ℚ))) := by
                exact Submodule.span_le.mpr fun v hv => Submodule.subset_span (hsubset hv)

/-- Helper for Exercise 16-16.1-11: after quotienting the explicit permutation lattice by the
maximal ideal, one recovers the residue-field permutation module at the `A`-linear level. -/
noncomputable def permutation_lattice_reduction_equiv_over_A
    (X : Type) [MulAction G X] [Finite X] :
    (X →₀ k) ≃ₗ[A] (permutation_lattice (A := A) (G := G) X).reduction := by
  let f : (X →₀ A) →ₗ[A] (X →₀ ℚ) :=
    Finsupp.mapRange.linearMap (α := X) (Algebra.linearMap A ℚ)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    ext g
    simp [f, Finsupp.ker_mapRange, Finsupp.ext_iff]
  let eMap :
      (⊤ : Submodule A (X →₀ A)) ≃ₗ[A]
        (permutation_lattice (A := A) (G := G) X).toSubmodule :=
    Submodule.equivMapOfInjective f hf ⊤
  let eTopQuot :
      ((⊤ : Submodule A (X →₀ A)) ⧸
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (⊤ : Submodule A (X →₀ A))))) ≃ₗ[A]
          (permutation_lattice (A := A) (G := G) X).reduction := by
    refine Submodule.Quotient.equiv _ _ eMap ?_
    simp [eMap]
  let eTop :
      ((⊤ : Submodule A (X →₀ A)) ⧸
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (⊤ : Submodule A (X →₀ A))))) ≃ₗ[A]
          ((X →₀ A) ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (X →₀ A)))) :=
    Submodule.Quotient.equiv _ _
      (Submodule.topEquiv : (⊤ : Submodule A (X →₀ A)) ≃ₗ[A] (X →₀ A))
      (by simp)
  let q : (X →₀ A) →ₗ[A] (X →₀ k) :=
    Finsupp.mapRange.linearMap (α := X) (Algebra.linearMap A k)
  have hkerA : (Algebra.linearMap A k).ker = IsLocalRing.maximalIdeal A := by
    ext a
    simp
  have hker : LinearMap.ker q = IsLocalRing.maximalIdeal A • (⊤ : Submodule A (X →₀ A)) := by
    rw [Finsupp.ker_mapRange, hkerA,
      finsupp_submodule_eq_smul_top (A := A) X (IsLocalRing.maximalIdeal A)]
  have hsurj : Function.Surjective q := by
    simpa [q, Finsupp.mapRange.linearMap_apply, IsLocalRing.ResidueField.algebraMap_eq] using
      (Finsupp.mapRange_surjective (α := X) (e := algebraMap A k)
        (he₀ := map_zero _) (he := IsLocalRing.residue_surjective (R := A)))
  let eQuot :
      ((X →₀ A) ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (X →₀ A)))) ≃ₗ[A] (X →₀ k) :=
    (Submodule.quotEquivOfEq _ _ hker).symm.trans
      (LinearMap.quotKerEquivOfSurjective q hsurj)
  exact eQuot.symm.trans (eTop.symm.trans eTopQuot)

/-- Helper for Exercise 16-16.1-11: the explicit permutation-lattice reduction equivalence is
also available over the residue field itself. -/
noncomputable def permutation_lattice_reduction_equiv
    (X : Type) [MulAction G X] [Finite X] :
    (X →₀ k) ≃ₗ[k] (permutation_lattice (A := A) (G := G) X).reduction := by
  letI :
      IsScalarTower A k
        (permutation_lattice (A := A) (G := G) X).reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact
    residue_field_linear_equiv_of_linear_equiv
      (permutation_lattice_reduction_equiv_over_A (A := A) (G := G) X)

end

end Exercise_16_16_1_11
