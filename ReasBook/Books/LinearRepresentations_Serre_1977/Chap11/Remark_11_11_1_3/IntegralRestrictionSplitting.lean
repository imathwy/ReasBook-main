import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_1
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1

-- Stable integral restriction-family splitting infrastructure extracted from Remark 11-11.1-3.

noncomputable section

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation TensorProduct

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- Helper for Remark 11-11.1-3: every integral character is already a bundled class function. -/
private theorem mem_classFunctionSubmodule_of_mem_characterRing {χ : G → ℂ}
    (hχ : χ ∈ R(G)) : χ ∈ classFunctionSubmodule ℂ G := by
  rw [mem_classFunctionSubmodule_iff]
  exact isClassFunction_of_mem_characterRingOverField χ hχ

/-- Helper for Remark 11-11.1-3: if `z = n * w` with `n ≠ 0`, then dividing by `n` recovers
`w`. -/
private theorem div_eq_of_eq_intCast_mul {n : ℤ} (hn : n ≠ 0) {z w : ℂ}
    (h : z = (n : ℂ) * w) : z / (n : ℂ) = w := by
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  exact (div_eq_iff hnC).2 (by simpa [mul_comm] using h)

/-- Helper for Remark 11-11.1-3: the range of the restriction-family map is saturated. -/
private theorem restriction_range_saturated
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G))
    {f : Π H : X, R(H.1)} {n : ℤ} (hn : n ≠ 0)
    (h : n • f ∈ LinearMap.range (Representation.characterRingRestriction X).toLinearMap) :
    f ∈ LinearMap.range (Representation.characterRingRestriction X).toLinearMap := by
  rcases h with ⟨χ, hχ⟩
  have hχ_class : ((χ : G → ℂ) ∈ classFunctionSubmodule ℂ G) :=
    mem_classFunctionSubmodule_of_mem_characterRing χ.property
  have hscaled_class :
      (fun g : G ↦ (χ : G → ℂ) g / (n : ℂ)) ∈ classFunctionSubmodule ℂ G := by
    rw [show (fun g : G ↦ (χ : G → ℂ) g / (n : ℂ)) =
        ((n : ℂ)⁻¹ • (χ : G → ℂ)) by
          ext g
          simp [div_eq_mul_inv, mul_comm]]
    exact (classFunctionSubmodule ℂ G).smul_mem ((n : ℂ)⁻¹) hχ_class
  let φ : classFunctionSubmodule ℂ G :=
    ⟨fun g : G ↦ (χ : G → ℂ) g / (n : ℂ), hscaled_class⟩
  have hcoord :
      ∀ H : X, ((H.1.classFunctionRestriction φ : H.1 → ℂ) : H.1 → ℂ) = (f H : H.1 → ℂ) := by
    intro H
    ext hH
    have hvalue :
        (χ : G → ℂ) hH = (n : ℂ) * ((f H : R(H.1)) : H.1 → ℂ) hH := by
      have hcoordEval := congrArg
        (fun z : Π H : X, R(H.1) ↦ (((z H : R(H.1)) : H.1 → ℂ) hH)) hχ
      simpa [zsmul_eq_mul] using hcoordEval
    simpa [φ, Subgroup.classFunctionRestriction_apply] using
      div_eq_of_eq_intCast_mul hn hvalue
  have hφ_res :
      ∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1) := by
    intro H
    rw [hcoord H]
    exact (f H).property
  have hφ_mem : (φ : G → ℂ) ∈ R(G) := hdetect φ hφ_res
  refine ⟨⟨(φ : G → ℂ), hφ_mem⟩, ?_⟩
  ext H hH
  exact congrFun (hcoord H) hH

/-- Helper for Remark 11-11.1-3: every kernel element of the restriction-family map is divisible
by every nonzero integer. -/
private theorem restriction_kernel_divisible
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G))
    {χ : R(G)} {n : ℤ} (hn : n ≠ 0)
    (hχ : Representation.characterRingRestriction X χ = 0) :
    ∃ ψ : R(G), n • ψ = χ := by
  have hχ_class : (((χ : R(G)) : G → ℂ) ∈ classFunctionSubmodule ℂ G) :=
    mem_classFunctionSubmodule_of_mem_characterRing χ.property
  have hscaled_class :
      (fun g : G ↦ (χ : G → ℂ) g / (n : ℂ)) ∈ classFunctionSubmodule ℂ G := by
    rw [show (fun g : G ↦ (χ : G → ℂ) g / (n : ℂ)) =
        ((n : ℂ)⁻¹ • (χ : G → ℂ)) by
          ext g
          simp [div_eq_mul_inv, mul_comm]]
    exact (classFunctionSubmodule ℂ G).smul_mem ((n : ℂ)⁻¹) hχ_class
  let φ : classFunctionSubmodule ℂ G :=
    ⟨fun g : G ↦ (χ : G → ℂ) g / (n : ℂ), hscaled_class⟩
  have hφ_res :
      ∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1) := by
    intro H
    have hzero :
        ((H.1.classFunctionRestriction φ : H.1 → ℂ) : H.1 → ℂ) = 0 := by
      ext hH
      have hvalue : (χ : G → ℂ) hH = 0 := by
        have hcoordEval := congrArg
          (fun z : Π H : X, R(H.1) ↦ (((z H : R(H.1)) : H.1 → ℂ) hH)) hχ
        simpa using hcoordEval
      simp [φ, Subgroup.classFunctionRestriction_apply, hvalue]
    rw [hzero]
    exact (zero_mem (R(H.1)) : (0 : H.1 → ℂ) ∈ R(H.1))
  have hφ_mem : (φ : G → ℂ) ∈ R(G) := hdetect φ hφ_res
  refine ⟨⟨(φ : G → ℂ), hφ_mem⟩, ?_⟩
  apply Subtype.ext
  ext g
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  simpa [φ, zsmul_eq_mul] using mul_div_cancel₀ ((χ : G → ℂ) g) hnC

/-- Helper for Remark 11-11.1-3: a quotient by a saturated range is torsion-free. -/
theorem quotient_torsion_free_of_saturated_range
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N)
    (hrange :
      ∀ {y : N} {n : ℤ}, n ≠ 0 → n • y ∈ LinearMap.range f → y ∈ LinearMap.range f) :
    Module.IsTorsionFree ℤ (N ⧸ LinearMap.range f) := by
  refine Module.IsTorsionFree.of_smul_eq_zero ?_
  intro n q hq
  by_cases hn : n = 0
  · exact Or.inl hn
  · rcases Submodule.mkQ_surjective (LinearMap.range f) q with ⟨y, rfl⟩
    right
    have hy : n • y ∈ LinearMap.range f := by
      change Submodule.Quotient.mk (n • y) = 0 at hq
      rw [Submodule.Quotient.mk_eq_zero] at hq
      exact hq
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).2 (hrange hn hy)

/-- Helper for Remark 11-11.1-3: a split linear map remains injective after base change. -/
theorem baseChange_injective_of_leftInverse
    {A : Type*} [CommRing A]
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (i : M →ₗ[ℤ] N) (r : N →ₗ[ℤ] M)
    (hr : Function.LeftInverse r i) :
    Function.Injective (i.baseChange A) := by
  have hr_comp : r.comp i = LinearMap.id := by
    exact LinearMap.ext hr
  have hrA : (r.baseChange A).comp (i.baseChange A) = LinearMap.id := by
    simpa [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange A) hr_comp
  intro x y hxy
  calc
    x = ((r.baseChange A).comp (i.baseChange A)) x := by
          simp [hrA]
    _ = ((r.baseChange A).comp (i.baseChange A)) y := by
          simpa [LinearMap.comp_apply] using congrArg (fun z ↦ (r.baseChange A) z) hxy
    _ = y := by
          simp [hrA]

/-- Helper for Remark 11-11.1-3: a finitely generated torsion-free `ℤ`-module has no nonzero
element divisible by every nonzero integer. -/
private theorem eq_zero_of_divisible_by_all_nonzero_int
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]
    {x : M} (hdiv : ∀ {n : ℤ}, n ≠ 0 → ∃ y : M, n • y = x) : x = 0 := by
  obtain ⟨d, b⟩ : Σ d, Module.Basis (Fin d) ℤ M := Module.basisOfFiniteTypeTorsionFree'
  have hcoeff_zero : ∀ i : Fin d, b.repr x i = 0 := by
    intro i
    let B : ℕ := ∑ j : Fin d, Int.natAbs (b.repr x j)
    obtain ⟨p, hpB, hpprime⟩ := Nat.exists_infinite_primes (B + 1)
    have hpz : (p : ℤ) ≠ 0 := by
      exact_mod_cast hpprime.ne_zero
    obtain ⟨y, hy⟩ := hdiv hpz
    have hdivides : (p : ℤ) ∣ b.repr x i := by
      refine ⟨b.repr y i, ?_⟩
      have hrepr := congrArg (fun z : M ↦ b.repr z i) hy
      simpa [zsmul_eq_mul, mul_comm] using hrepr.symm
    have hle_sum : Int.natAbs (b.repr x i) ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum
        (fun j _ ↦ Nat.zero_le (Int.natAbs (b.repr x j)))
        (by simp : i ∈ (Finset.univ : Finset (Fin d)))
    have hlt : Int.natAbs (b.repr x i) < Int.natAbs (p : ℤ) := by
      have hpgt : B < p := lt_of_lt_of_le (Nat.lt_succ_self B) hpB
      simpa using lt_of_le_of_lt hle_sum hpgt
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdivides hlt
  apply b.repr.injective
  ext i
  simpa using hcoeff_zero i

omit [Finite G] in
/-- Helper for Remark 11-11.1-3: LinearRepresentations_Serre_1977's character ring is torsion-free as a `ℤ`-module. -/
private theorem characterRing_isTorsionFree :
    Module.IsTorsionFree ℤ (R(G)) := by
  refine Module.IsTorsionFree.of_smul_eq_zero ?_
  intro n χ hχ
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    apply Subtype.ext
    ext g
    have hvalue := congrArg (fun z : R(G) ↦ ((z : G → ℂ) g)) hχ
    simpa [smul_eq_mul, hn] using hvalue

/-- Helper for Remark 11-11.1-3: the cokernel of the restriction-family map is torsion-free once
the local detection theorem is available. -/
private theorem characterRingRestriction_quotient_torsion_free_of_detection
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G)) :
    Module.IsTorsionFree ℤ
      ((Π H : X, R(H.1)) ⧸ LinearMap.range (Representation.characterRingRestriction X).toLinearMap) := by
  exact quotient_torsion_free_of_saturated_range
    (Representation.characterRingRestriction X).toLinearMap (restriction_range_saturated X hdetect)

/-- Helper for Remark 11-11.1-3: finite generation plus infinite divisibility force the kernel of
the restriction-family map to vanish. -/
private theorem characterRingRestriction_ker_eq_bot_of_detection
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G))
    [Module.Finite ℤ (R(G))] :
    LinearMap.ker (Representation.characterRingRestriction X).toLinearMap = ⊥ := by
  letI : Module.IsTorsionFree ℤ (R(G)) := characterRing_isTorsionFree
  rw [LinearMap.ker_eq_bot]
  intro χ ψ hχψ
  have hsub : Representation.characterRingRestriction X (χ - ψ) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr hχψ
  have hdiv : ∀ {n : ℤ}, n ≠ 0 → ∃ η : R(G), n • η = χ - ψ := fun hn ↦
    restriction_kernel_divisible X hdetect hn hsub
  have hzero : χ - ψ = 0 := eq_zero_of_divisible_by_all_nonzero_int hdiv
  exact sub_eq_zero.mp hzero

omit [Finite G] in
/-- Helper for Remark 11-11.1-3: a finite group admits a complete pairwise nonisomorphic family
of irreducible complex finite-dimensional representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep ℂ G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso
        ((CategoryTheory.forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : CategoryTheory.Simple (π q) := by
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (π q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπ_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank ℂ (π q) := by
    have hmult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } =
          Module.finrank ℂ (π q) := by
      letI : Representation.IsIrreducible (π q).ρ := by
        exact FDRep.isIrreducible_of_simple (π q)
      simpa using
        leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (π q).ρ
          inferInstance
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } = (S q).card := by
      rw [show S q = Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (q : ι) : Finset.sum (S q) dimσ = Module.finrank ℂ (π q) ^ 2 := by
    calc
      Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank ℂ (π q)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S q).card * Module.finrank ℂ (π q) := by
            simp
      _ = Module.finrank ℂ (π q) ^ 2 := by
            rw [hS_card, pow_two]
  have hcover : Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hj_mem : j ∈ S (⟦j⟧ : ι) := by
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · rcases Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)) with ⟨e⟩
          exact ⟨e.symm⟩
      exact Finset.mem_biUnion.mpr ⟨(⟦j⟧ : ι), Finset.mem_univ _, hj_mem⟩
  have htotal_eq_card : Finset.sum (Finset.univ : Finset κ) dimσ = Nat.card G := by
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free ℂ (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing ℂ (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank ℂ (G →₀ ℂ) := by
        symm
        calc
          Module.finrank ℂ (G →₀ ℂ) = Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
            exact e.finrank_eq.symm
          _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
                rw [show dimσ = fun j ↦ Module.finrank ℂ ↥(σ j).toSubmodule from rfl]
                exact Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule)
      _ = Nat.card G := by
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
  have hπ_sum : ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = Nat.card G := by
    calc
      ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
            symm
            exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
            rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

omit [Finite G] in
/-- Helper for Remark 11-11.1-3: LinearRepresentations_Serre_1977's character ring is finitely generated over `ℤ`. -/
theorem characterRing_moduleFinite [Finite G] : Module.Finite ℤ (R(G)) := by
  classical
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  exact Module.Finite.of_basis
    (Representation.irreducible_characters_basis_of_complete_family
      ℂ π hπ_pairwise hπ_complete)

/-- Helper for Remark 11-11.1-3: the detection theorem yields a left inverse for the integral
restriction-family map. -/
theorem characterRingRestriction_has_leftInverse_of_detection_by_restrictions
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G)) :
    ∃ s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G),
      Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap := by
  letI : Module.Finite ℤ (R(G)) := characterRing_moduleFinite
  letI : ∀ H : X, Module.Finite ℤ (R(H.1)) := fun H ↦
    show Module.Finite ℤ (R(H.1)) from characterRing_moduleFinite
  letI : Module.Finite ℤ (Π H : X, R(H.1)) := by
    infer_instance
  let f : R(G) →ₗ[ℤ] (Π H : X, R(H.1)) := (Representation.characterRingRestriction X).toLinearMap
  have hker : LinearMap.ker f = ⊥ :=
    characterRingRestriction_ker_eq_bot_of_detection X hdetect
  have hquot :
      Module.IsTorsionFree ℤ ((Π H : X, R(H.1)) ⧸ LinearMap.range f) := by
    simpa [f] using characterRingRestriction_quotient_torsion_free_of_detection X hdetect
  letI : Module.IsTorsionFree ℤ ((Π H : X, R(H.1)) ⧸ LinearMap.range f) := hquot
  letI : Module.Finite ℤ ((Π H : X, R(H.1)) ⧸ LinearMap.range f) :=
    Module.Finite.of_surjective ((LinearMap.range f).mkQ) (Submodule.mkQ_surjective _)
  obtain ⟨d, b⟩ :
      Σ d, Module.Basis (Fin d) ℤ ((Π H : X, R(H.1)) ⧸ LinearMap.range f) :=
    Module.basisOfFiniteTypeTorsionFree'
  letI : Module.Projective ℤ ((Π H : X, R(H.1)) ⧸ LinearMap.range f) :=
    Module.Projective.of_basis b
  obtain ⟨t, ht⟩ :=
    Module.projective_lifting_property ((LinearMap.range f).mkQ) (LinearMap.id : _ →ₗ[ℤ] _)
      (Submodule.mkQ_surjective _)
  let p : (Π H : X, R(H.1)) →ₗ[ℤ] (Π H : X, R(H.1)) :=
    LinearMap.id - t.comp ((LinearMap.range f).mkQ)
  have ht_apply :
      ∀ z : (Π H : X, R(H.1)) ⧸ LinearMap.range f, ((LinearMap.range f).mkQ) (t z) = z := by
    intro z
    have hEval := congrArg
      (fun g : ((Π H : X, R(H.1)) ⧸ LinearMap.range f) →ₗ[ℤ]
          ((Π H : X, R(H.1)) ⧸ LinearMap.range f) ↦ g z) ht
    simpa using hEval
  have hp_range : ∀ y : Π H : X, R(H.1), p y ∈ LinearMap.range f := by
    intro y
    rw [← Submodule.ker_mkQ (LinearMap.range f), LinearMap.mem_ker]
    change ((LinearMap.range f).mkQ) y -
        ((LinearMap.range f).mkQ) (t (((LinearMap.range f).mkQ) y)) = 0
    rw [ht_apply (((LinearMap.range f).mkQ) y), sub_self]
  letI : Module ℤ ↥(LinearMap.range f) := (LinearMap.range f).module
  let pRange := LinearMap.codRestrict (LinearMap.range f) p hp_range
  let e := LinearEquiv.ofInjective f ((LinearMap.ker_eq_bot).1 hker)
  refine ⟨e.symm.toLinearMap ∘ₗ pRange, ?_⟩
  intro x
  have hqx : ((LinearMap.range f).mkQ) (f x) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).2 ⟨x, rfl⟩
  have hpfx : p (f x) = f x := by
    change f x - t (((LinearMap.range f).mkQ) (f x)) = f x
    rw [hqx]
    simp
  have hpRange_fx : pRange (f x) = e x := by
    apply Subtype.ext
    exact hpfx
  simpa using congrArg e.symm hpRange_fx

end CharacterizationOfCharacters

end Representation
