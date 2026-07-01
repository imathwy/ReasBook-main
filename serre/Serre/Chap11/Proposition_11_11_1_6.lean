import Mathlib
import Serre.Chap12.Proposition_12_12_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Representation
open scoped Representation

section CharacterRing

variable {G : Type} [Group G]

end CharacterRing

namespace Representation

section CharacterizationOfCharacters

variable {G : Type} [Group G]

/-- The restriction algebra hom from `R(G)` to the finite direct sum of the `R(H)`, realized in
Lean as the product over the finite index type `X`. -/
def characterRingRestriction (X : Finset (Subgroup G)) : R(G) →ₐ[ℤ] (Π H : X, R(H.1)) :=
  Pi.algHom ℤ (fun H : X ↦ R(H.1)) fun H ↦ H.1 ↾R[ℂ]

-- Proof sketch: unfold `characterRingRestriction`; its `H`-component is the canonical subgroup
-- restriction map `H.1 ↾R[ℂ]`.
/-- Evaluating the restriction family at `H` gives the ordinary restriction of `χ` to `H`. -/
@[simp] theorem characterRingRestriction_apply
    (X : Finset (Subgroup G)) (χ : R(G)) (H : X) (h : H.1) :
    ((characterRingRestriction X χ H : R(H.1)) : H.1 → ℂ) h = (χ : G → ℂ) h := by
  simp [characterRingRestriction]

/-- Helper for Proposition 11-11.1-6: every element of `R(G)` defines a bundled class function on
`G`. -/
private theorem mem_classFunctionSubmodule_of_mem_characterRing {χ : G → ℂ}
    (hχ : χ ∈ R(G)) : χ ∈ classFunctionSubmodule ℂ G := by
  rw [mem_classFunctionSubmodule_iff]
  exact isClassFunction_of_mem_characterRingOverField χ hχ

/-- Helper for Proposition 11-11.1-6: if `z = n * w` with `n ≠ 0`, then dividing by `n`
recovers `w`. -/
private theorem div_eq_of_eq_intCast_mul {n : ℤ} (hn : n ≠ 0) {z w : ℂ}
    (h : z = (n : ℂ) * w) : z / (n : ℂ) = w := by
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  -- Move the nonzero denominator to the right and simplify.
  exact (div_eq_iff hnC).2 (by simpa [mul_comm] using h)

/-- Helper for Proposition 11-11.1-6: the range of the restriction map is saturated. -/
private theorem restriction_range_saturated
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G))
    {f : Π H : X, R(H.1)} {n : ℤ} (hn : n ≠ 0)
    (h : n • f ∈ LinearMap.range (characterRingRestriction X).toLinearMap) :
    f ∈ LinearMap.range (characterRingRestriction X).toLinearMap := by
  rcases h with ⟨χ, hχ⟩
  have hχ_class : ((χ : G → ℂ) ∈ classFunctionSubmodule ℂ G) :=
    mem_classFunctionSubmodule_of_mem_characterRing χ.property
  have hscaled_class :
      (fun g : G ↦ (χ : G → ℂ) g / (n : ℂ)) ∈ classFunctionSubmodule ℂ G := by
    -- Scaling a bundled class function preserves the class-function subspace.
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
      have := congrArg
        (fun z : Π H : X, R(H.1) ↦ (((z H : R(H.1)) : H.1 → ℂ) hH)) hχ
      simpa [zsmul_eq_mul] using this
    -- Compare the scaled global character with the given local coordinate.
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
  -- The restriction of the recovered global character agrees with the prescribed coordinate.
  exact congrFun (hcoord H) hH

/-- Helper for Proposition 11-11.1-6: every kernel element is divisible by every nonzero integer.
-/
private theorem restriction_kernel_divisible
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G))
    {χ : R(G)} {n : ℤ} (hn : n ≠ 0)
    (hχ : characterRingRestriction X χ = 0) :
    ∃ ψ : R(G), n • ψ = χ := by
  have hχ_class : (((χ : R(G)) : G → ℂ) ∈ classFunctionSubmodule ℂ G) :=
    mem_classFunctionSubmodule_of_mem_characterRing χ.property
  have hscaled_class :
      (fun g : G ↦ (χ : G → ℂ) g / (n : ℂ)) ∈ classFunctionSubmodule ℂ G := by
    -- The same scaling trick used for the cokernel keeps us inside the class-function space.
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
        have := congrArg
          (fun z : Π H : X, R(H.1) ↦ (((z H : R(H.1)) : H.1 → ℂ) hH)) hχ
        simpa using this
      -- Each restricted scaled value vanishes because the original restriction is zero.
      simp [φ, Subgroup.classFunctionRestriction_apply, hvalue]
    rw [hzero]
    exact (zero_mem (R(H.1)) : (0 : H.1 → ℂ) ∈ R(H.1))
  have hφ_mem : (φ : G → ℂ) ∈ R(G) := hdetect φ hφ_res
  refine ⟨⟨(φ : G → ℂ), hφ_mem⟩, ?_⟩
  apply Subtype.ext
  ext g
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  -- Multiplying the scaled character by `n` recovers the original one pointwise.
  simpa [φ, zsmul_eq_mul] using mul_div_cancel₀ ((χ : G → ℂ) g) hnC

/-- Helper for Proposition 11-11.1-6: the quotient by a saturated range is torsion-free. -/
private theorem quotient_torsion_free_of_saturated_range
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N)
    (hrange :
      ∀ {y : N} {n : ℤ}, n ≠ 0 → n • y ∈ LinearMap.range f → y ∈ LinearMap.range f) :
    Module.IsTorsionFree ℤ (N ⧸ LinearMap.range f) := by
  -- Route correction: the cokernel step should be formulated as torsion-freeness of the quotient,
  -- not as an ad hoc element-chasing argument each time it is used.
  refine Module.IsTorsionFree.of_smul_eq_zero ?_
  intro n q hq
  by_cases hn : n = 0
  · exact Or.inl hn
  · rcases Submodule.mkQ_surjective (LinearMap.range f) q with ⟨y, rfl⟩
    right
    -- A quotient class annihilated by a nonzero integer comes from an element whose multiple lies
    -- in the range, so saturation forces the element itself into the range.
    have hy : n • y ∈ LinearMap.range f := by
      change Submodule.Quotient.mk (n • y) = 0 at hq
      rw [Submodule.Quotient.mk_eq_zero] at hq
      exact hq
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).2 (hrange hn hy)

/-- Helper for Proposition 11-11.1-6: a finitely generated torsion-free `ℤ`-module has no nonzero
element divisible by every nonzero integer. -/
private theorem eq_zero_of_divisible_by_all_nonzero_int
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]
    {x : M} (hdiv : ∀ {n : ℤ}, n ≠ 0 → ∃ y : M, n • y = x) : x = 0 := by
  -- Choose a finite basis and bound the absolute values of the coordinates of `x`.
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
    -- A prime larger than every coordinate bound cannot divide a nonzero coordinate.
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

/-- Helper for Proposition 11-11.1-6: Serre's character ring is torsion-free as a `ℤ`-module. -/
private theorem characterRing_isTorsionFree :
    Module.IsTorsionFree ℤ (R(G)) := by
  refine Module.IsTorsionFree.of_smul_eq_zero ?_
  intro n χ hχ
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    apply Subtype.ext
    ext g
    -- Evaluate the torsion equation pointwise in `ℂ`, where nonzero integers act injectively.
    have hvalue := congrArg (fun z : R(G) ↦ ((z : G → ℂ) g)) hχ
    simpa [smul_eq_mul, hn] using hvalue

/-- Helper for Proposition 11-11.1-6: the cokernel of the restriction map is torsion-free. -/
private theorem characterRingRestriction_quotient_torsion_free_of_detection
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G)) :
    Module.IsTorsionFree ℤ
      ((Π H : X, R(H.1)) ⧸ LinearMap.range (characterRingRestriction X).toLinearMap) := by
  -- The saturated-image lemma is exactly the torsion-free-cokernel statement from the source.
  exact quotient_torsion_free_of_saturated_range
    (characterRingRestriction X).toLinearMap (restriction_range_saturated X hdetect)

/-- Helper for Proposition 11-11.1-6: under finite generation of `R(G)`, the divisible-kernel
argument forces the kernel of the restriction map to vanish. -/
private theorem characterRingRestriction_ker_eq_bot_of_detection
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G))
    [Module.Finite ℤ (R(G))] :
    LinearMap.ker (characterRingRestriction X).toLinearMap = ⊥ := by
  letI : Module.IsTorsionFree ℤ (R(G)) := characterRing_isTorsionFree
  rw [LinearMap.ker_eq_bot]
  intro χ ψ hχψ
  have hsub : characterRingRestriction X (χ - ψ) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr hχψ
  -- Once `R(G)` is known to be a finite free abelian group, infinite divisibility forces the
  -- difference of two elements with the same restriction family to vanish.
  have hdiv : ∀ {n : ℤ}, n ≠ 0 → ∃ η : R(G), n • η = χ - ψ := fun hn ↦
    restriction_kernel_divisible X hdetect hn hsub
  have hzero : χ - ψ = 0 := eq_zero_of_divisible_by_all_nonzero_int hdiv
  exact sub_eq_zero.mp hzero

/-- Helper for Proposition 11-11.1-6: a finite group admits a complete pairwise nonisomorphic
family of irreducible complex finite-dimensional representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
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
                simpa [dimσ] using
                  (Module.finrank_directSum fun j ↦ (σ j).toSubmodule)
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

/-- Helper for Proposition 11-11.1-6: in the finite-group character-ring setting,
`R(G)` is finitely generated over `ℤ`. -/
private theorem characterRing_moduleFinite [Finite G] : Module.Finite ℤ (R(G)) := by
  classical
  have hfamily :
      ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
        CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π :=
    exists_complete_pairwise_nonisomorphic_irreducible_family
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ := hfamily
  exact Module.Finite.of_basis
    (irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete)

/-- Helper for Proposition 11-11.1-6: in the finite-group character-ring setting, the detection
hypothesis yields a split injection. -/
private theorem split_injective_of_detection_by_restrictions_of_finite
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G))
    [Finite G] :
    ∃ s : (Π H : X, R(H.1)) →ₗ[ℤ] R(G),
      Function.LeftInverse s (characterRingRestriction X).toLinearMap := by
  letI : Module.Finite ℤ (R(G)) := characterRing_moduleFinite
  letI : ∀ H : X, Module.Finite ℤ (R(H.1)) := fun H ↦
    show Module.Finite ℤ (R(H.1)) from characterRing_moduleFinite
  letI : Module.Finite ℤ (Π H : X, R(H.1)) := by
    infer_instance
  let f : R(G) →ₗ[ℤ] (Π H : X, R(H.1)) := (characterRingRestriction X).toLinearMap
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
    have := congrArg
      (fun g : ((Π H : X, R(H.1)) ⧸ LinearMap.range f) →ₗ[ℤ]
          ((Π H : X, R(H.1)) ⧸ LinearMap.range f) ↦ g z) ht
    simpa using this
  have hp_range : ∀ y : Π H : X, R(H.1), p y ∈ LinearMap.range f := by
    intro y
    rw [← Submodule.ker_mkQ (LinearMap.range f), LinearMap.mem_ker]
    -- The projector onto the chosen complement kills the quotient coordinate.
    change ((LinearMap.range f).mkQ) y -
        ((LinearMap.range f).mkQ) (t (((LinearMap.range f).mkQ) y)) = 0
    rw [ht_apply (((LinearMap.range f).mkQ) y), sub_self]
  letI : Module ℤ ↥(LinearMap.range f) := (LinearMap.range f).module
  let pRange :=
    LinearMap.codRestrict (LinearMap.range f) p hp_range
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
  -- Apply the inverse range equivalence to recover the original source element.
  simpa using congrArg e.symm hpRange_fx

-- Proof sketch: show first that the cokernel of `characterRingRestriction X` is torsion-free. If
-- `n • f` comes from a global character `χ`, then the detection hypothesis applies to the
-- canonical class-function view of `χ / n`, whose restrictions are exactly the local characters
-- encoded by `f`, so `f` already lies in the image. Serre's proof then invokes the fact that,
-- for finite groups, the character rings under consideration are finitely generated free
-- `ℤ`-modules; here that finite-generation input is derived internally from the canonical
-- irreducible-character basis owner, keeping the public theorem in the finite-group chapter
-- context rather than exposing proof-route module hypotheses.
/-- Proposition 11-11.1-6: if restriction to a finite family `X` of subgroups detects membership
in Serre's character ring `R(G)` for bundled complex class functions
`φ : classFunctionSubmodule ℂ G` via the canonical restriction maps `H.classFunctionRestriction φ`,
then for a finite group `G` the restriction homomorphism `R(G) → ⨁_{H ∈ X} R(H)` is a split
injection; in Lean the finite direct sum is realized as the product over the finite index type
`X`. -/
theorem characterRingRestriction_split_injective_of_detection_by_restrictions
    (X : Finset (Subgroup G))
    (hdetect :
      ∀ φ : classFunctionSubmodule ℂ G,
        (∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) →
          (φ : G → ℂ) ∈ R(G))
    [Finite G] :
    ∃ s : (Π H : X, R(H.1)) →ₗ[ℤ] R(G),
      Function.LeftInverse s (characterRingRestriction X).toLinearMap := by
  -- Route correction: the previous route tried to reject the statement outright.
  -- The source-faithful route instead proves that the image is saturated and that kernel
  -- elements are divisible by every nonzero integer; the remaining blocker is converting
  -- those structural facts into an actual splitting inside the current hypothesis/import
  -- boundary.
  have hrange_saturated :
      ∀ {f : Π H : X, R(H.1)} {n : ℤ}, n ≠ 0 →
        n • f ∈ LinearMap.range (characterRingRestriction X).toLinearMap →
          f ∈ LinearMap.range (characterRingRestriction X).toLinearMap :=
    restriction_range_saturated X hdetect
  have hkernel_divisible :
      ∀ {χ : R(G)} {n : ℤ}, n ≠ 0 → characterRingRestriction X χ = 0 →
        ∃ ψ : R(G), n • ψ = χ :=
    restriction_kernel_divisible X hdetect
  have hquot_torsion_free :
      Module.IsTorsionFree ℤ
        ((Π H : X, R(H.1)) ⧸ LinearMap.range (characterRingRestriction X).toLinearMap) :=
    characterRingRestriction_quotient_torsion_free_of_detection X hdetect
  exact split_injective_of_detection_by_restrictions_of_finite X hdetect

end CharacterizationOfCharacters

end Representation
