import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Remark_2_2_1_2
import LinearRepresentations_Serre_1977.Serre.Chap02.Corollary_2_2_4_2
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_2_1
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_3_2
import LinearRepresentations_Serre_1977.Serre.Chap06.Exercise_6_6_5_6
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap13.Proposition_13_13_2_3
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra Representation TensorProduct ComplexStarModule
open Representation
open CategoryTheory

noncomputable section

universe u v

section

variable {G : Type} [Group G] [Finite G]
local instance instFintypeG_Exercise_13_13_2_7 : Fintype G := Fintype.ofFinite G
local instance anonInst_Exercise_13_13_2_7_1 : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)

/-- Helper for Exercise `13-13.2-7`: if a pairwise nonisomorphic irreducible complex family
already accounts for the full degree-squared sum, then it is complete. -/
private lemma isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card_local
    [NeZero (Nat.card G : ℂ)] {ι : Type} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_sum : ∑ i : ι, Module.finrank ℂ (π i) ^ 2 = Nat.card G) :
    IsCompleteIrreducibleFamily π := by
  classical
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation (leftRegular ℂ G)),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i, (σ i).toRepresentation.IsIrreducible := by
    exact exists_isInternal_irreducible_subrepresentations (leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    -- Distinct irreducible classes cannot share the same regular summand.
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    exact hπ_pairwise hii <| ⟨(e.symm.trans e').toFDRepIso⟩
  have hmult (i : ι) :
      Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } =
        Module.finrank ℂ (π i) := by
    have hπ_irreducible : Representation.IsIrreducible (π i).ρ := by
      letI : Simple (π i) := hπ_simple i
      exact FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible (π i).ρ := hπ_irreducible
    simpa using
      leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (π i).ρ
        inferInstance
  have hS_card (i : ι) : (S i).card = Module.finrank ℂ (π i) := by
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } = (S i).card := by
      rw [show S i =
            Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) by rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult i
  have hS_sum (i : ι) : Finset.sum (S i) dimσ = Module.finrank ℂ (π i) ^ 2 := by
    calc
      Finset.sum (S i) dimσ = Finset.sum (S i) (fun _j ↦ Module.finrank ℂ (π i)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S i).card * Module.finrank ℂ (π i) := by
            simp
      _ = Module.finrank ℂ (π i) ^ 2 := by
            rw [hS_card, pow_two]
  have hcovered_raw : Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  have hcovered_sum : Finset.sum covered dimσ = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := by
    calc
      Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := hcovered_raw
      _ = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
  have hcovered_eq_card : Finset.sum covered dimσ = Nat.card G := by
    calc
      Finset.sum covered dimσ = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := hcovered_sum
      _ = Nat.card G := hπ_sum
  have htotal_eq_card : ∑ j : κ, dimσ j = Nat.card G := by
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      ∑ j : κ, dimσ j = Module.finrank ℂ (G →₀ ℂ) := by
        symm
        calc
          Module.finrank ℂ (G →₀ ℂ) =
              Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
                exact e.finrank_eq.symm
          _ = ∑ j : κ, dimσ j := by
                simp [dimσ, Module.finrank_directSum]
      _ = Nat.card G := by
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
  refine
    { isSimple := hπ_simple
      exists_iso := ?_ }
  intro τ _
  letI : Nontrivial τ := by
    by_contra hτ
    letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ
    have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero τ hzero
  let τρ := τ.ρ
  have hτρ_irreducible : Representation.IsIrreducible τρ := by
    exact FDRep.isIrreducible_of_simple τ
  letI : Representation.IsIrreducible τρ := hτρ_irreducible
  have hτ_pos : 0 < Module.finrank ℂ τ := Module.finrank_pos
  have hτ_mult :
      Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } = Module.finrank ℂ τ := by
    simpa [τρ] using
      leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr τρ inferInstance
  have hτ_count_pos : 0 < Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } := by
    rw [hτ_mult]
    exact hτ_pos
  obtain ⟨⟨j, hjτ⟩⟩ := (Nat.card_pos_iff.mp hτ_count_pos).1
  have hj_mem : j ∈ covered := by
    by_contra hj_not_mem
    have hτ_term : dimσ j = Module.finrank ℂ τ := by
      rcases hjτ with ⟨e⟩
      exact e.toLinearEquiv.finrank_eq
    have hcomp_pos : 0 < Finset.sum (Finset.univ \ covered) dimσ := by
      have hj_mem_compl : j ∈ Finset.univ \ covered := by
        simp [hj_not_mem]
      have hsingle : dimσ j ≤ Finset.sum (Finset.univ \ covered) dimσ := by
        simpa using
          (Finset.single_le_sum (fun x hx ↦ Nat.zero_le (dimσ x)) hj_mem_compl :
            dimσ j ≤ Finset.sum (Finset.univ \ covered) dimσ)
      exact lt_of_lt_of_le (by simpa [hτ_term] using hτ_pos) hsingle
    have hlt : Finset.sum covered dimσ < ∑ j : κ, dimσ j := by
      rw [← Finset.sum_add_sum_compl covered dimσ]
      exact Nat.lt_add_of_pos_right hcomp_pos
    have hcontra : Nat.card G < Nat.card G := by
      calc
        Nat.card G = Finset.sum covered dimσ := hcovered_eq_card.symm
        _ < ∑ j : κ, dimσ j := hlt
        _ = Nat.card G := htotal_eq_card
    exact Nat.lt_irrefl _ hcontra
  rcases Finset.mem_biUnion.mp hj_mem with ⟨i, _, hij⟩
  rcases (Finset.mem_filter.mp hij).2 with ⟨e⟩
  rcases hjτ with ⟨eτ⟩
  exact ⟨i, ⟨(eτ.symm.trans e).toFDRepIso⟩⟩

/-- Helper for Exercise `13-13.2-7`: choose a complete pairwise nonisomorphic irreducible complex
family without importing the colliding Chapter `6.6.5-10` file. -/
private lemma exists_complete_pairwise_nonisomorphic_irreducible_family
    [NeZero (Nat.card G : ℂ)] :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
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
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : Simple (π q) := by
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (π q)
  have hπ_sum : ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = Nat.card G := by
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
      letI : ∀ j : κ, Module.Free ℂ (σ j).toSubmodule :=
        fun j ↦ Module.Free.of_divisionRing ℂ (σ j).toSubmodule
      let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
      calc
        Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank ℂ (G →₀ ℂ) := by
          symm
          calc
            Module.finrank ℂ (G →₀ ℂ) =
                Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
                  exact e.finrank_eq.symm
            _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
                  dsimp [dimσ]
                  exact Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule)
        _ = Nat.card G := by
              rw [Nat.card_eq_fintype_card]
              exact Module.finrank_finsupp_self ℂ
    calc
      ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
            symm
            exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
            rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπ_complete :
      IsCompleteIrreducibleFamily π := by
    exact
      isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card_local
        (G := G) π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

-- Source/core/bridge triage:
-- * source-facing: Exercise `13-13.2-7` asks for an `ℝ`-algebra isomorphism
--   `Z(ℝ[G]) ≃ ℝ ⊗R(G)`.
-- * core/canonical: the Chapter `11` owner `ℝ ⊗R(G)`.
-- * bridge/view: the realized subalgebra `characterRingScalarExtensionSubalgebra ℝ G`.
--
-- Primitive data: the two `ℝ`-algebras `Subalgebra.center ℝ (ℝ[G])` and `ℝ ⊗R(G)`.
-- Derived API: any realization of `ℝ ⊗R(G)` inside `G → ℂ`.

/-- Helper for Exercise `13-13.2-7`: each conjugacy-class indicator already lies in the complex
tensor character ring. -/
lemma conjClassIndicator_mem_characterRingScalarExtension_complex
    (c : ConjClasses G) :
    (ConjClasses.indicator c : G → ℂ) ∈ Representation.characterRingScalarExtension ℂ G := by
  rcases Representation.weighted_adamsOperator_conjClassIndicator_lifts_to_tensorCharacterRing
      ℂ 1 c (by
        intro z hz
        exact ⟨(z : ℂ), by simp⟩) with ⟨χ, hχ⟩
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  -- Theorem `11-11.2-2` (global form) gives the indicator weighted by `|G| / (|G|, 1) = |G|`.
  have hweighted :
      (fun x : G ↦ (Nat.card G : ℂ) * ConjClasses.indicator (ConjClasses.mk g) x) ∈
        Representation.characterRingScalarExtension ℂ G := by
    have hmemχ :
        (↑χ : G → ℂ) ∈ Representation.characterRingScalarExtension ℂ G :=
      Representation.tensorCharacterRing_mem_characterRingScalarExtension χ
    simpa [hχ, Representation.adamsOperator] using hmemχ
  have hsmul :
      (Nat.card G : ℂ)⁻¹ •
          (fun x : G ↦ (Nat.card G : ℂ) * ConjClasses.indicator (ConjClasses.mk g) x) ∈
        Representation.characterRingScalarExtension ℂ G := by
    -- Rescale by the inverse group order to recover the raw indicator function.
    exact (Representation.characterRingScalarExtension ℂ G).smul_mem _ hweighted
  have hfun :
      (Nat.card G : ℂ)⁻¹ •
          (fun x : G ↦ (Nat.card G : ℂ) * ConjClasses.indicator (ConjClasses.mk g) x) =
        ConjClasses.indicator (ConjClasses.mk g) := by
    funext x
    by_cases hx : ConjClasses.mk x = ConjClasses.mk g
    · simp [Pi.smul_apply, ConjClasses.indicator, hcard_ne]
    · have hxnot : x ∉ (ConjClasses.mk g).carrier := by
        intro hxmem
        exact hx ((ConjClasses.mem_carrier_iff_mk_eq).mp hxmem)
      simp [Pi.smul_apply, ConjClasses.indicator, hxnot]
  rw [hfun] at hsmul
  exact hsmul

/-- Helper for Exercise `13-13.2-7`: every complex class function belongs to the complex tensor
character ring. -/
lemma classFunction_mem_characterRingScalarExtension_complex
    (f : G → ℂ) (hf : _root_.IsClassFunction f) :
    f ∈ Representation.characterRingScalarExtension ℂ G := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let F : ConjClasses G → ℂ := hf.lift
  have hsum : (fun x : G ↦ ∑ c : ConjClasses G, F c * ConjClasses.indicator c x) = f := by
    -- Expand `f` in the conjugacy-class indicator basis.
    funext x
    calc
      ∑ c : ConjClasses G, F c * ConjClasses.indicator c x
          = F (ConjClasses.mk x) := by
              classical
              rw [Finset.sum_eq_single (ConjClasses.mk x)]
              · simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq]
              · intro c hc hcx
                have hxnot : x ∉ c.carrier := by
                  intro hxmem
                  exact hcx ((ConjClasses.mem_carrier_iff_mk_eq).mp hxmem).symm
                simp [ConjClasses.indicator, hxnot]
              · intro hmem
                simp at hmem
      _ = f x := by
            simp [F]
  rw [← hsum]
  -- Each basis vector already lies in the tensor character ring, so the finite sum does as well.
  classical
  have hsum_mem :
      (∑ c : ConjClasses G, F c • ConjClasses.indicator c) ∈
        Representation.characterRingScalarExtension ℂ G := by
    simpa using
    (Submodule.sum_mem (Representation.characterRingScalarExtension ℂ G)
      (fun c hc ↦
        (Representation.characterRingScalarExtension ℂ G).smul_mem _
          (conjClassIndicator_mem_characterRingScalarExtension_complex c)))
  have hsum_eq :
      (∑ c : ConjClasses G, F c • ConjClasses.indicator c : G → ℂ) =
        fun x : G ↦ ∑ c : ConjClasses G, F c * ConjClasses.indicator c x := by
    funext x
    simp [Pi.smul_apply]
  exact hsum_eq ▸ hsum_mem

/-- Helper for Exercise `13-13.2-7`: evaluating a realized complex tensor character on
conjugacy classes packages it as a function on `ConjClasses G`. -/
noncomputable def classFunctionSubalgebraEvalConjClasses :
    Representation.characterRingScalarExtensionSubalgebra ℂ G →ₐ[ℂ] (ConjClasses G → ℂ) where
  toFun f :=
    (Representation.isClassFunction_of_mem_characterRingScalarExtension
      (show (f : G → ℂ) ∈ Representation.characterRingScalarExtension ℂ G from f.2)).lift
  map_one' := by
    -- Evaluate the constant class function `1` on a representative.
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_mul' f g := by
    -- The lift preserves pointwise multiplication because both inputs are class functions.
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_zero' := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_add' f g := by
    -- The lift is pointwise additive on class functions.
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    simp
  commutes' z := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp

/-- Helper for Exercise `13-13.2-7`: evaluating realized tensor characters on conjugacy classes is
bijective. -/
lemma bijective_classFunctionSubalgebraEvalConjClasses :
    Function.Bijective (classFunctionSubalgebraEvalConjClasses (G := G)) := by
  constructor
  · intro f g hfg
    -- Equality on every conjugacy class forces equality of the underlying class functions.
    ext x
    have h := congrFun hfg (ConjClasses.mk x)
    simpa [classFunctionSubalgebraEvalConjClasses] using h
  · intro F
    refine ⟨⟨fun g ↦ F (ConjClasses.mk g), ?_⟩, ?_⟩
    · -- The function pulled back from `ConjClasses G` is a class function, hence belongs to the
      -- complex tensor character ring by the previous helper.
      exact classFunction_mem_characterRingScalarExtension_complex
        (fun g ↦ F (ConjClasses.mk g))
        ⟨by
          intro x y hxy
          exact congrArg F hxy⟩
    · -- Evaluating the pulled-back function on conjugacy classes recovers `F`.
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      simp [classFunctionSubalgebraEvalConjClasses]

/-- Helper for Exercise `13-13.2-7`: the complex tensor character ring already surjects onto the
product algebra of functions on the conjugacy classes. -/
lemma surjective_tensorCharacterRing_complex_to_conjClasses :
    Function.Surjective
      ((classFunctionSubalgebraEvalConjClasses (G := G)).comp
        (Representation.tensorCharacterRingToSubalgebra ℂ G)) := by
  intro F
  let f : Representation.characterRingScalarExtensionSubalgebra ℂ G :=
    ⟨fun g ↦ F (ConjClasses.mk g),
      classFunction_mem_characterRingScalarExtension_complex
        (fun g ↦ F (ConjClasses.mk g))
        ⟨by
          intro x y hxy
          exact congrArg F hxy⟩⟩
  obtain ⟨χ, hχ⟩ :=
    ((R(G)).toSubmodule.surjective_tensorToSpan ℂ) (f : Representation.characterRingScalarExtension ℂ G)
  change ℂ ⊗R(G) at χ
  change (R(G)).toSubmodule.tensorToSpan ℂ χ = (f : Representation.characterRingScalarExtension ℂ G)
    at hχ
  refine ⟨χ, ?_⟩
  ext c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  have hχfun : (χ : G → ℂ) g = (f : G → ℂ) g := by
    have hχ' :=
      congrArg (fun z : Representation.characterRingScalarExtension ℂ G ↦ (z : G → ℂ)) hχ
    simpa using congrFun hχ' g
  simpa [f, classFunctionSubalgebraEvalConjClasses] using hχfun

/-- Helper for Exercise `13-13.2-7`: equal irreducible characters force an equivalence of the
corresponding finite-dimensional complex representations. -/
private lemma Representation.nonempty_equiv_of_character_eq_of_isIrreducible
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (hχ : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  -- Evaluate the shared character at `1` to identify the two underlying dimensions.
  have hdim' : (Module.finrank ℂ V : ℂ) = Module.finrank ℂ W := by
    simpa [Representation.char_one] using congrFun hχ 1
  have hdim : Module.finrank ℂ V = Module.finrank ℂ W := by
    exact Nat.cast_injective (R := ℂ) hdim'
  -- Orthogonality upgrades character equality to a one-dimensional intertwining space.
  have hfinrank : Module.finrank ℂ (ρ.IntertwiningMap σ) = 1 := by
    exact_mod_cast
      calc
        (Module.finrank ℂ (ρ.IntertwiningMap σ) : ℂ) = ⟪ρ.character, σ.character⟫ := by
          symm
          exact
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ ρ σ
        _ = ⟪ρ.character, ρ.character⟫ := by simp [hχ]
        _ = Module.finrank ℂ (ρ.IntertwiningMap ρ) := by
          exact
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ ρ ρ
        _ = 1 := by
          simp [Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := ρ)]
  letI : Nontrivial (ρ.IntertwiningMap σ) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [hfinrank])
  obtain ⟨f, hf_ne⟩ := exists_ne (0 : ρ.IntertwiningMap σ)
  -- A nonzero intertwiner between irreducibles is injective; equal dimensions make it surjective.
  have hf_inj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero (ρ := ρ) (σ := σ) f).resolve_right hf_ne
  have hf_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf_inj
  exact
    Representation.nonempty_equiv_of_bijective_intertwiningMap
      (ρ1 := ρ) (ρ2 := σ) f ⟨hf_inj, hf_surj⟩

omit [Finite G] in
/-- Helper for Exercise `13-13.2-7`: an irreducible finite-dimensional complex representation has
irreducible dual. -/
private lemma Representation.isIrreducible_dual_of_isIrreducible
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ρ.dual.IsIrreducible := by
  -- Turn source irreducibility into nontriviality of the carrier so the dual also has a
  -- nontrivial lattice of subrepresentations.
  have hV_nontrivial : Nontrivial V := by
    letI : Nontrivial (Subrepresentation ρ) := inferInstance
    by_contra hV
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      simp [Subsingleton.elim x 0]
    exact (show (⊥ : Subrepresentation ρ) ≠ ⊤ from bot_ne_top) hbot_top
  letI : Nontrivial V := hV_nontrivial
  letI : Nontrivial (Module.Dual ℂ V) := (Module.nontrivial_dual_iff ℂ).2 inferInstance
  letI : Nontrivial (Subrepresentation ρ.dual) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot_top
    obtain ⟨f, hf⟩ := exists_ne (0 : Module.Dual ℂ V)
    have htopmem : f ∈ (⊤ : Subrepresentation ρ.dual) := by
      exact show f ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule from Submodule.mem_top
    have hfmem : f ∈ (⊥ : Subrepresentation ρ.dual) := by
      simpa [hbot_top] using htopmem
    exact hf (by simpa using hfmem)
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule := by
        -- Stability of the annihilator is exactly the contragredient action identity.
        intro g x hx
        rw [Submodule.mem_dualCoannihilator] at hx ⊢
        intro φ hφ
        have hgphi : ρ.dual g⁻¹ φ ∈ W.toSubmodule := by
          exact W.apply_mem_toSubmodule g⁻¹ hφ
        have hx' := hx (ρ.dual g⁻¹ φ) hgphi
        simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hx' }
  have hW' : W' = ⊥ ∨ W' = ⊤ := by
    exact eq_bot_or_eq_top W'
  rcases hW' with hW' | hW'
  · -- If the annihilator in `V` is zero, finite-dimensional duality forces `W = ⊤`.
    apply Subrepresentation.toSubmodule_injective
    calc
      W.toSubmodule = W.toSubmodule.dualCoannihilator.dualAnnihilator := by
        symm
        exact Subspace.dualCoannihilator_dualAnnihilator_eq (W := W.toSubmodule)
      _ = ⊤ := by
        have hco : W.toSubmodule.dualCoannihilator = ⊥ := by
          simpa using congrArg Subrepresentation.toSubmodule hW'
        simp [hco]
  · -- If the annihilator in `V` is all of `V`, then `W = ⊥`, contradicting `hW`.
    exfalso
    apply hW
    apply Subrepresentation.toSubmodule_injective
    calc
      W.toSubmodule = W.toSubmodule.dualCoannihilator.dualAnnihilator := by
        symm
        exact Subspace.dualCoannihilator_dualAnnihilator_eq (W := W.toSubmodule)
      _ = ⊥ := by
        have hco : W.toSubmodule.dualCoannihilator = ⊤ := by
          simpa using congrArg Subrepresentation.toSubmodule hW'
        simp [hco]

omit [Finite G] in
/-- Helper for Exercise `13-13.2-7`: completeness supplies an index for the dual of any member of
a complete irreducible complex family. -/
private lemma exists_iso_conjugateIndex
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    ∃ j, Nonempty (FDRep.of ((π i).ρ.dual) ≅ FDRep.of (π j).ρ) := by
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  letI : ((π i).ρ.dual).IsIrreducible :=
    Representation.isIrreducible_dual_of_isIrreducible (ρ := (π i).ρ)
  -- Feed the dual representation back into the complete-family owner.
  exact
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := fun j ↦ FDRep.of (π j).ρ) hπ_complete ((π i).ρ.dual) inferInstance

/-- Helper for Exercise `13-13.2-7`: the dual partner of `i` in a complete irreducible family. -/
noncomputable def conjugateIndex_e2137
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) : ι :=
  Classical.choose (exists_iso_conjugateIndex π hπ_complete i)

/-- Helper for Exercise `13-13.2-7`: the character at the dual index is the pointwise complex
conjugate of the original character. -/
private lemma conjugateIndex_character
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    (π (conjugateIndex_e2137 π hπ_complete i)).ρ.character =
      fun g ↦ star ((π i).ρ.character g) := by
  -- Recover the chosen owner-level dual isomorphism.
  rcases Classical.choose_spec (exists_iso_conjugateIndex π hπ_complete i) with ⟨e⟩
  have hchar_iso :
      ((π i).ρ.dual).character =
        (π (conjugateIndex_e2137 π hπ_complete i)).ρ.character := by
    simpa [conjugateIndex_e2137] using
      Representation.char_iso
        (Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e))
  -- The dual character is pointwise complex conjugation of the original character.
  ext g
  rw [← hchar_iso, Representation.char_dual_eq_star]

/-- Helper for Exercise `13-13.2-7`: the dual-index operation on a complete pairwise
nonisomorphic irreducible family is an involution. -/
private lemma conjugateIndex_involution
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_pairwise : PairwiseNonisomorphic π)
    (i : ι) :
    conjugateIndex_e2137 π hπ_complete (conjugateIndex_e2137 π hπ_complete i) = i := by
  let j := conjugateIndex_e2137 π hπ_complete (conjugateIndex_e2137 π hπ_complete i)
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  letI : (π j).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete j
  -- Applying the conjugate-character formula twice recovers the original character.
  have hchar : (π j).ρ.character = (π i).ρ.character := by
    ext g
    calc
      (π j).ρ.character g =
          star ((π (conjugateIndex_e2137 π hπ_complete i)).ρ.character g) := by
            exact
              congrFun
                (conjugateIndex_character π hπ_complete
                  (conjugateIndex_e2137 π hπ_complete i)) g
      _ = star (star ((π i).ρ.character g)) := by
            rw [congrFun (conjugateIndex_character π hπ_complete i) g]
      _ = (π i).ρ.character g := by simp
  rcases
      Representation.nonempty_equiv_of_character_eq_of_isIrreducible
        (G := G) (ρ := (π j).ρ) (σ := (π i).ρ) hchar with
    ⟨e⟩
  by_contra hji
  have hπ_pairwise_fdrep :
      PairwiseNonisomorphic (fun i ↦ FDRep.of (π i).ρ) :=
    Representation.pairwiseNonisomorphic_fdrep_of_rep (π := π) hπ_pairwise
  exact hπ_pairwise_fdrep hji ⟨e.toFDRepIso⟩

/-- Helper for Exercise `13-13.2-7`: an index is fixed by the dual-index involution exactly when
its irreducible character is real-valued. -/
lemma conjugateIndex_fixed_iff_isValuedInBaseField
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    conjugateIndex_e2137 π hπ_complete i = i ↔ IsValuedInBaseField ℝ ((π i).ρ.character) := by
  constructor
  · intro hfix
    letI : (π i).ρ.IsIrreducible :=
      IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
    -- A fixed index turns the chosen dual partner into a genuine self-duality.
    have hspec :
        Nonempty (FDRep.of ((π i).ρ.dual) ≅ FDRep.of (π (conjugateIndex_e2137 π hπ_complete i)).ρ) := by
      simpa [conjugateIndex_e2137] using
        (Classical.choose_spec (exists_iso_conjugateIndex π hπ_complete i))
    rw [hfix] at hspec
    have hselfdual : Nonempty ((π i).ρ.Equiv (π i).ρ.dual) := by
      rcases hspec with ⟨e⟩
      exact
        ⟨(Representation.equivOfIso
            ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)).symm⟩
    exact
      (Representation.hasRealValuedCharacter_iff_nonempty_equiv_dual (ρ := (π i).ρ)).2
        hselfdual
  · intro hreal
    let j := conjugateIndex_e2137 π hπ_complete i
    letI : (π i).ρ.IsIrreducible :=
      IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
    letI : (π j).ρ.IsIrreducible :=
      IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete j
    obtain ⟨e⟩ :
        Nonempty ((π i).ρ.Equiv (π i).ρ.dual) :=
      (Representation.hasRealValuedCharacter_iff_nonempty_equiv_dual (ρ := (π i).ρ)).1
        hreal
    -- Real-valuedness identifies the character with its dual, hence with the chosen partner.
    have hchar : (π j).ρ.character = (π i).ρ.character := by
      ext g
      calc
        (π j).ρ.character g = star ((π i).ρ.character g) := by
          exact congrFun (conjugateIndex_character π hπ_complete i) g
        _ = ((π i).ρ.dual).character g := by
          symm
          exact Representation.char_dual_eq_star (ρ := (π i).ρ) g
        _ = (π i).ρ.character g := by
          exact (congrFun (Representation.char_iso e) g).symm
    rcases
        Representation.nonempty_equiv_of_character_eq_of_isIrreducible
          (G := G) (ρ := (π j).ρ) (σ := (π i).ρ) hchar with
      ⟨eji⟩
    by_contra hji
    have hπ_pairwise_fdrep :
        PairwiseNonisomorphic (fun k ↦ FDRep.of (π k).ρ) :=
      Representation.pairwiseNonisomorphic_fdrep_of_rep (π := π) hπ_pairwise
    exact hπ_pairwise_fdrep hji ⟨eji.toFDRepIso⟩

/-- Helper for Exercise `13-13.2-7`: the fixed points of the dual-index involution are in
bijection with the real-valued irreducible characters. -/
lemma card_fixed_conjugateIndex_eq_card_realValuedCharacters
    {ι : Type v} (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Nat.card { i // conjugateIndex_e2137 (fun j ↦ Rep.of (π j).ρ)
        (by simpa using hπ_complete) i = i } =
      Nat.card { i // IsValuedInBaseField ℝ (π i).character } := by
  let πRep : ι → Rep ℂ G := fun i ↦ Rep.of (π i).ρ
  have hπRep_pairwise : PairwiseNonisomorphic πRep := by
    intro i j hij hij_iso
    apply hπ_pairwise hij
    rcases hij_iso with ⟨e⟩
    simpa [πRep] using ⟨(Representation.equivOfIso e).toFDRepIso⟩
  have hπRep_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (πRep i).ρ) := by
    simpa [πRep] using hπ_complete
  let e :
      { i // conjugateIndex_e2137 πRep hπRep_complete i = i } ≃
        { i // IsValuedInBaseField ℝ (π i).character } :=
    { toFun := fun i ↦
        ⟨i.1,
          (conjugateIndex_fixed_iff_isValuedInBaseField
            (π := πRep) hπRep_pairwise hπRep_complete i.1).1 i.2⟩
      invFun := fun i ↦
        ⟨i.1,
          (conjugateIndex_fixed_iff_isValuedInBaseField
            (π := πRep) hπRep_pairwise hπRep_complete i.1).2 i.2⟩
      left_inv := by
        intro i
        cases i
        rfl
      right_inv := by
        intro i
        cases i
        rfl }
  -- Translate the fixed-point count to the earlier real-valued-character count.
  exact Nat.card_congr e

/-- Helper for Exercise `13-13.2-7`: the fixed points of the dual-index involution are as numerous
as the even conjugacy classes. -/
lemma card_fixed_conjugateIndex_eq_card_even_conjClasses
    {ι : Type v} (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Nat.card { i // conjugateIndex_e2137 (fun j ↦ Rep.of (π j).ρ)
        (by simpa using hπ_complete) i = i } =
      Nat.card { c : ConjClasses G // c.IsEven } := by
  -- First rewrite fixed dual indices as real-valued irreducible characters.
  calc
    Nat.card { i // conjugateIndex_e2137 (fun j ↦ Rep.of (π j).ρ)
        (by simpa using hπ_complete) i = i }
        = Nat.card { i // IsValuedInBaseField ℝ (π i).character } := by
            exact
              card_fixed_conjugateIndex_eq_card_realValuedCharacters
                (G := G) π hπ_pairwise hπ_complete
    -- Then import Exercise `13-13.2-6` to convert that count to even conjugacy classes.
    _ = Nat.card { c : ConjClasses G // c.IsEven } := by
          exact
            card_realValued_irreducible_characters_eq_card_even_conjClasses
              (G := G) π hπ_pairwise hπ_complete

/-- Helper for Exercise `13-13.2-7`: the complex tensor character ring is already the full product
algebra of complex-valued functions on `ConjClasses G`. -/
lemma tensorCharacterRing_complex_algEquiv_conjClasses :
    Nonempty (ℂ ⊗R(G) ≃ₐ[ℂ] (ConjClasses G → ℂ)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  letI : DecidableEq ι := Classical.decEq ι
  let b := Representation.irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  letI : Module.Free ℤ (R(G)) := Module.Free.of_basis b
  letI : Module.Finite ℤ (R(G)) := Module.Finite.of_basis b
  let bt := Algebra.TensorProduct.basis ℂ b
  letI : Module.Free ℂ (ℂ ⊗R(G)) := Module.Free.of_basis bt
  letI : Module.Finite ℂ (ℂ ⊗R(G)) := Module.Finite.of_basis bt
  let v : ι → _root_.classFunctionSubspace G := fun i ↦
    ⟨(π i).character, by
      have hclass : _root_.IsClassFunction (π i).character := by
        refine ⟨?_⟩
        intro x y hxy
        rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp hxy) with ⟨a, ha⟩
        rw [← ha]
        exact ((π i).char_conj x a).symm
      simpa [_root_.mem_classFunctionSubspace_iff] using
        hclass⟩
  let f :
      ℂ ⊗R(G) →ₐ[ℂ] (ConjClasses G → ℂ) :=
    (classFunctionSubalgebraEvalConjClasses (G := G)).comp
      (Representation.tensorCharacterRingToSubalgebra ℂ G)
  have hsurj : Function.Surjective f :=
    surjective_tensorCharacterRing_complex_to_conjClasses (G := G)
  have hpair_sum :
      ∀ s : Finset ι, ∀ a : ι → ℂ, ∀ ψ : G → ℂ,
        ⟪∑ j ∈ s, a j • (π j).character, ψ⟫ =
          ∑ j ∈ s, a j * ⟪(π j).character, ψ⟫ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro a ψ
      simp [Representation.groupFunctionPairingOverField]
    · intro i s hi ih a ψ
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]
  have horth :
      Pairwise fun i j ↦
        ⟪(π i).character, (π j).character⟫ = (0 : ℂ) :=
    Representation.irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      ℂ π hπ_complete.isSimple hπ_pairwise
  have hdiag : ∀ i : ι, ⟪(π i).character, (π i).character⟫ = (1 : ℂ) := by
    intro i
    letI : Simple (π i) := hπ_complete.isSimple i
    have hself : Nonempty (π i ≅ π i) := ⟨Iso.refl _⟩
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
      (FDRep.char_orthonormal (π i) (π i))
  have hlin_char : LinearIndependent ℂ fun i ↦ (π i).character := by
    -- Orthogonality isolates every coefficient in a finite linear relation.
    rw [linearIndependent_iff']
    intro s a hsum i hi
    have hpair_zero :
        ⟪∑ j ∈ s, a j • (π j).character, (π i).character⟫ = 0 := by
      have hpair_eq :
          Representation.groupFunctionPairingOverField ℂ
              (∑ j ∈ s, a j • (π j).character) (π i).character =
            Representation.groupFunctionPairingOverField ℂ 0 (π i).character := by
        exact
          congrArg
            (fun ψ : G → ℂ ↦ Representation.groupFunctionPairingOverField ℂ ψ (π i).character) hsum
      have hzero_pair :
          Representation.groupFunctionPairingOverField ℂ 0 (π i).character = 0 := by
        simp [Representation.groupFunctionPairingOverField]
      exact hpair_eq.trans hzero_pair
    rw [hpair_sum s a ((π i).character), Finset.sum_eq_single i] at hpair_zero
    · simpa [hdiag i] using hpair_zero
    · intro j hj hji
      rw [horth hji, mul_zero]
    · intro hnot
      exact (hnot hi).elim
  have hlin_sub : LinearIndependent ℂ v := by
    -- The same orthogonal family remains independent inside the class-function subspace.
    rw [linearIndependent_iff']
    intro s a hsum i hi
    exact
      (linearIndependent_iff'.mp hlin_char) s a
        (by
          have hsum' := congrArg (fun z : _root_.classFunctionSubspace G ↦ (z : G → ℂ)) hsum
          simpa [v] using hsum')
        i hi
  have hlin_conj :
      LinearIndependent ℂ
        fun i ↦ _root_.classFunctionSubmodule.equivFun ℂ G (v i) := by
    exact
      hlin_sub.map'
        (_root_.classFunctionSubmodule.equivFun ℂ G).toLinearMap
        (LinearMap.ker_eq_bot.2 (_root_.classFunctionSubmodule.equivFun ℂ G).injective)
  have hdomain :
      Module.finrank ℂ (ℂ ⊗R(G)) = Fintype.card ι := by
    calc
      Module.finrank ℂ (ℂ ⊗R(G))
          = Module.finrank ℂ ℂ * Module.finrank ℤ (R(G)) := by
              rw [Module.finrank_tensorProduct]
      _ = Module.finrank ℤ (R(G)) := by simp
      _ = Fintype.card ι := by
            simpa using Module.finrank_eq_card_basis b
  have hcodomain_ge :
      Fintype.card ι ≤ Module.finrank ℂ (ConjClasses G → ℂ) :=
    hlin_conj.fintype_card_le_finrank
  have hcodomain_le :
      Module.finrank ℂ (ConjClasses G → ℂ) ≤ Fintype.card ι := by
    rw [← hdomain]
    exact LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hsurj
  have hcodomain :
      Module.finrank ℂ (ConjClasses G → ℂ) = Fintype.card ι :=
    le_antisymm hcodomain_le hcodomain_ge
  have hdim :
      Module.finrank ℂ (ℂ ⊗R(G)) =
        Module.finrank ℂ (ConjClasses G → ℂ) := by
    rw [hdomain, hcodomain]
  have hinj : Function.Injective f := by
    -- Equal dimensions upgrade surjectivity to bijectivity.
    let fL : (ℂ ⊗R(G)) →ₗ[ℂ] (ConjClasses G → ℂ) := f.toLinearMap
    have hsurjL : Function.Surjective fL := hsurj
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := fL) hdim).2 hsurjL
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

/-- Helper for Exercise `13-13.2-7`: the complex center of `ℂ[G]` is algebra-isomorphic to the
product algebra of functions on `ConjClasses G`. -/
lemma center_complex_algEquiv_conjClasses :
    Nonempty (Subalgebra.center ℂ (ℂ[G]) ≃ₐ[ℂ] (ConjClasses G → ℂ)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  obtain ⟨ι, _, πfd, hπfd_pairwise, hπfd_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  let πRep : ι → Rep ℂ G := fun i ↦ Rep.of (πfd i).ρ
  let b :=
    Representation.irreducible_characters_basis_of_complete_family ℂ πfd hπfd_pairwise hπfd_complete
  letI : Module.Free ℤ (R(G)) := Module.Free.of_basis b
  letI : Module.Finite ℤ (R(G)) := Module.Finite.of_basis b
  have hπRep_pairwise : PairwiseNonisomorphic πRep := by
    intro i j hij hij_iso
    apply hπfd_pairwise hij
    rcases hij_iso with ⟨e⟩
    simpa [πRep] using ⟨(Representation.equivOfIso e).toFDRepIso⟩
  have hπRep_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (πRep i).ρ) := by
    simpa [πRep] using hπfd_complete
  have hcard :
      Fintype.card ι = Fintype.card (ConjClasses G) := by
    rcases tensorCharacterRing_complex_algEquiv_conjClasses (G := G) with ⟨eχ⟩
    calc
      Fintype.card ι = Module.finrank ℤ (R(G)) := by
        symm
        simpa using Module.finrank_eq_card_basis b
      _ = Module.finrank ℂ (ℂ ⊗R(G)) := by
        symm
        rw [Module.finrank_tensorProduct]
        simp
      _ = Module.finrank ℂ (ConjClasses G → ℂ) := by
        simpa using eχ.toLinearEquiv.finrank_eq
      _ = Fintype.card (ConjClasses G) := Module.finrank_fintype_fun_eq_card ℂ
  let e : ι ≃ ConjClasses G := Fintype.equivOfCardEq hcard
  let eπ : (ι → ℂ) ≃ₐ[ℂ] (ConjClasses G → ℂ) :=
    AlgEquiv.piCongrLeft' ℂ (fun _ : ι ↦ ℂ) e
  -- Transport the central-character product decomposition across the cardinality equivalence.
  exact
    ⟨(Representation.centralCharacterFamilyAlgEquiv πRep hπRep_pairwise hπRep_complete).trans eπ⟩

/-- Helper for Exercise `13-13.2-7`: the real center of `ℝ[G]` has one basis vector per
conjugacy class. -/
lemma finrank_center_realGroupRing_eq_card_conjClasses :
    Module.finrank ℝ (Subalgebra.center ℝ (ℝ[G])) = Fintype.card (ConjClasses G) := by
  simpa using
    Module.finrank_eq_card_basis
      (conjugacyClassSumBasis (G := G) (k := ℝ))

/-- Helper for Exercise `13-13.2-7`: the real tensor character ring has one basis vector per
irreducible complex character in a complete family. -/
lemma finrank_tensorCharacterRing_real_eq_card_irreducible
    {ι : Type*} [Fintype ι] (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.finrank ℝ (ℝ ⊗R(G)) = Fintype.card ι := by
  let b :=
    Representation.irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  letI : Module.Free ℤ (R(G)) := Module.Free.of_basis b
  letI : Module.Finite ℤ (R(G)) := Module.Finite.of_basis b
  calc
    Module.finrank ℝ (ℝ ⊗R(G))
        = Module.finrank ℝ ℝ * Module.finrank ℤ (R(G)) := by
            rw [Module.finrank_tensorProduct]
    _ = Module.finrank ℤ (R(G)) := by simp
    _ = Fintype.card ι := by
          simpa using Module.finrank_eq_card_basis b

/-- Helper for Exercise `13-13.2-7`: every virtual character satisfies the usual inversion and
complex-conjugation identity. -/
lemma virtual_character_inv_eq_star
    (χ : R(G)) (g : G) :
    (χ : G → ℂ) g⁻¹ = star ((χ : G → ℂ) g) := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  letI : DecidableEq ι := Classical.decEq ι
  let b :=
    Representation.irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let c : ι → ℤ := b.repr χ
  have hχ_expand :
      ∑ i, c i • (π i).character = (χ : G → ℂ) := by
    -- Expand the virtual character in the irreducible-character basis.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr χ)
  have hχ_expand_inv : (χ : G → ℂ) g⁻¹ = ∑ i, c i • (π i).character g⁻¹ := by
    simpa using congrFun hχ_expand.symm g⁻¹
  have hχ_expand_val : (χ : G → ℂ) g = ∑ i, c i • (π i).character g := by
    simpa using congrFun hχ_expand.symm g
  calc
    (χ : G → ℂ) g⁻¹ = ∑ i, c i • (π i).character g⁻¹ := hχ_expand_inv
    _ = ∑ i, c i • star ((π i).character g) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          -- Each honest irreducible character satisfies the standard inversion formula.
          rw [show (π i).character g⁻¹ = star ((π i).character g) by
            simpa using
              (Representation.char_inv_eq_star_of_isOfFinOrder
                (ρ := (π i).ρ) g (isOfFinOrder_of_finite g))]
    _ = star (∑ i, c i • (π i).character g) := by
          -- Integer coefficients are fixed by complex conjugation, so star distributes termwise.
          symm
          simp
    _ = star ((χ : G → ℂ) g) := by
          rw [hχ_expand_val]

/-- Helper for Exercise `13-13.2-7`: postcomposing the coefficient function of a real central
element with `ℝ → ℂ` preserves the class-function condition. -/
lemma centerRealToComplexCenter_mem_classFunctionSubmodule
    (u : Subalgebra.center ℝ (ℝ[G])) :
    (fun g ↦ algebraMap ℝ ℂ ((u : ℝ[G]) g)) ∈ _root_.classFunctionSubmodule ℂ G := by
  -- The real coefficient function is already constant on conjugacy classes, and postcomposition
  -- with `algebraMap ℝ ℂ` keeps that invariance.
  let hclass : _root_.IsClassFunction fun g ↦ (u : ℝ[G]) g :=
    Representation.coeff_isClassFunction_of_mem_center u
  exact (_root_.mem_classFunctionSubmodule_iff ℂ _).2 (hclass.comp (algebraMap ℝ ℂ))

/-- Helper for Exercise `13-13.2-7`: the coefficientwise complexification of a real central
element is still central. -/
lemma centerRealToComplexCenter_mem_center
    (u : Subalgebra.center ℝ (ℝ[G])) :
    MonoidAlgebra.mapAlgHom G (Algebra.ofId ℝ ℂ) (u : ℝ[G]) ∈ Subalgebra.center ℂ (ℂ[G]) := by
  let f : _root_.classFunctionSubmodule ℂ G :=
    ⟨fun g ↦ algebraMap ℝ ℂ ((u : ℝ[G]) g),
      centerRealToComplexCenter_mem_classFunctionSubmodule (G := G) u⟩
  -- Identify the mapped group-algebra element with the finite-support function attached to the
  -- transported class function, then invoke the Chapter 6 center/class-function bridge.
  have hmap :
      MonoidAlgebra.mapAlgHom G (Algebra.ofId ℝ ℂ) (u : ℝ[G]) =
        Finsupp.equivFunOnFinite.symm (f : G → ℂ) := by
    ext g
    simp [f]
  rw [hmap]
  exact mem_center_of_classFunction ℂ f

/-- Helper for Exercise `13-13.2-7`: coefficientwise scalar extension sends the real center into
the complex center. -/
noncomputable def centerRealToComplexCenter :
    Subalgebra.center ℝ (ℝ[G]) →ₐ[ℝ] Subalgebra.center ℂ (ℂ[G]) :=
  AlgHom.codRestrict
    ((MonoidAlgebra.mapAlgHom G (Algebra.ofId ℝ ℂ)).comp
      (Subalgebra.center ℝ (ℝ[G])).val)
    ((Subalgebra.center ℂ (ℂ[G])).restrictScalars ℝ)
    (centerRealToComplexCenter_mem_center (G := G))

/-- Helper for Exercise `13-13.2-7`: coefficientwise scalar extension preserves the coefficients of
the central element. -/
@[simp] lemma centerRealToComplexCenter_apply
    (u : Subalgebra.center ℝ (ℝ[G])) (g : G) :
    (centerRealToComplexCenter (G := G) u : ℂ[G]) g = algebraMap ℝ ℂ ((u : ℝ[G]) g) := by
  -- Unfold the codomain restriction and read off the coefficientwise action of
  -- `MonoidAlgebra.mapAlgHom`.
  change ((MonoidAlgebra.mapAlgHom G (Algebra.ofId ℝ ℂ)) (u : ℝ[G])) g =
    algebraMap ℝ ℂ ((u : ℝ[G]) g)
  simp

/-- Helper for Exercise `13-13.2-7`: the dual-index operation preserves irreducible degree. -/
lemma conjugateIndex_finrank_eq
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    Module.finrank ℂ (π (conjugateIndex_e2137 π hπ_complete i)) = Module.finrank ℂ (π i) := by
  -- Evaluate the conjugate-character identity at `1`.
  have hvalue := congrFun (conjugateIndex_character π hπ_complete i) 1
  simpa [Representation.char_one] using hvalue

/-- Helper for Exercise `13-13.2-7`: a simple finite-dimensional complex representation has
positive degree. -/
private theorem simple_fdRep_finrank_pos_local
    (V : FDRep ℂ G) [Simple V] :
    0 < Module.finrank ℂ V := by
  have hV_nontriv : Nontrivial V := by
    by_contra hV
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hzero : (𝟙 V : V ⟶ V) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero V hzero
  exact Module.finrank_pos

/-- Helper for Exercise `13-13.2-7`: the center-side fixed-owner relation on the irreducible-index
product algebra. -/
def IsFixedDualFun
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (F : ι → ℂ) : Prop :=
  ∀ i, star (F (conjugateIndex_e2137 π hπ_complete i)) = F i

/-- Helper for Exercise `13-13.2-7`: the dual-index fixed relation is stable under zero. -/
lemma isFixedDualFun_zero
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    IsFixedDualFun π hπ_complete (0 : ι → ℂ) := by
  intro i
  simp [IsFixedDualFun]

/-- Helper for Exercise `13-13.2-7`: the dual-index fixed relation is stable under addition. -/
lemma isFixedDualFun_add
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    {F H : ι → ℂ}
    (hF : IsFixedDualFun π hπ_complete F)
    (hH : IsFixedDualFun π hπ_complete H) :
    IsFixedDualFun π hπ_complete (F + H) := by
  intro i
  -- The fixedness relation is coordinatewise and additive.
  simpa [IsFixedDualFun] using congrArg₂ (fun x y ↦ x + y) (hF i) (hH i)

/-- Helper for Exercise `13-13.2-7`: the dual-index fixed relation is stable under
multiplication. -/
lemma isFixedDualFun_mul
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    {F H : ι → ℂ}
    (hF : IsFixedDualFun π hπ_complete F)
    (hH : IsFixedDualFun π hπ_complete H) :
    IsFixedDualFun π hπ_complete (F * H) := by
  intro i
  -- Complex conjugation reverses products, and commutativity of `ℂ` restores the target order.
  simp [Pi.mul_apply, IsFixedDualFun, hF i, hH i, mul_comm]

/-- Helper for Exercise `13-13.2-7`: the dual-index fixed relation is stable under the constant
function `1`. -/
lemma isFixedDualFun_one
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    IsFixedDualFun π hπ_complete (1 : ι → ℂ) := by
  intro i
  simp [IsFixedDualFun]

/-- Helper for Exercise `13-13.2-7`: real scalars act through dual-index fixed constant
functions. -/
lemma isFixedDualFun_algebraMap
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (r : ℝ) :
    IsFixedDualFun π hπ_complete fun _ : ι ↦ (r : ℂ) := by
  intro i
  simp [IsFixedDualFun]

/-- Helper for Exercise `13-13.2-7`: the center-side fixed owner as a concrete `ℝ`-subalgebra of
the irreducible-index product algebra. -/
def fixedDualFunSubalgebra
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Subalgebra ℝ (ι → ℂ) :=
  { carrier := { F | IsFixedDualFun π hπ_complete F }
    zero_mem' := isFixedDualFun_zero π hπ_complete
    add_mem' := fun hF hH ↦ isFixedDualFun_add π hπ_complete hF hH
    one_mem' := isFixedDualFun_one π hπ_complete
    mul_mem' := fun hF hH ↦ isFixedDualFun_mul π hπ_complete hF hH
    algebraMap_mem' := isFixedDualFun_algebraMap π hπ_complete }

/-- Helper for Exercise `13-13.2-7`: shorthand for the center-side fixed owner on irreducible
indices. -/
abbrev FixedDualFun
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :=
  fixedDualFunSubalgebra π hπ_complete

/-- Helper for Exercise `13-13.2-7`: the central-character family of a real central element is
fixed by the dual-index involution. -/
lemma centerRealGroupRingToDualFun_isFixed
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (u : Subalgebra.center ℝ (ℝ[G])) :
    IsFixedDualFun π hπ_complete
      ((Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete)
        (centerRealToComplexCenter (G := G) u)) := by
  intro i
  have hfinrank_ne (j : ι) : (Module.finrank ℂ (π j) : ℂ) ≠ 0 := by
    -- Completeness makes each family member simple, so its degree is strictly positive.
    letI : Simple (FDRep.of (π j).ρ) := hπ_complete.isSimple j
    exact_mod_cast
      (Nat.ne_of_gt (simple_fdRep_finrank_pos_local (FDRep.of (π j).ρ)))
  letI : (π (conjugateIndex_e2137 π hπ_complete i)).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete
      (conjugateIndex_e2137 π hπ_complete i)
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  have hleft :
      ((Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete)
          (centerRealToComplexCenter (G := G) u))
        (conjugateIndex_e2137 π hπ_complete i) =
        (Module.finrank ℂ (π (conjugateIndex_e2137 π hπ_complete i)) : ℂ)⁻¹ *
          ∑ g : G,
            (centerRealToComplexCenter (G := G) u : ℂ[G]) g *
              (π (conjugateIndex_e2137 π hπ_complete i)).ρ.character g := by
    -- Read the chosen coordinate through the central-character family equivalence.
    simpa [Representation.centralCharacterFamilyAlgEquiv_apply,
      Representation.centralCharacterFamilyAlgHom] using
      (Representation.centralCharacter_apply_eq_sum_character
        (ρ := (π (conjugateIndex_e2137 π hπ_complete i)).ρ)
        (u := centerRealToComplexCenter (G := G) u)
        (hfinrank := hfinrank_ne (conjugateIndex_e2137 π hπ_complete i)))
  have hright :
      ((Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete)
          (centerRealToComplexCenter (G := G) u))
        i =
        (Module.finrank ℂ (π i) : ℂ)⁻¹ *
          ∑ g : G,
            (centerRealToComplexCenter (G := G) u : ℂ[G]) g *
              (π i).ρ.character g := by
    -- The same trace formula identifies the `i`-th coordinate.
    simpa [Representation.centralCharacterFamilyAlgEquiv_apply,
      Representation.centralCharacterFamilyAlgHom] using
      (Representation.centralCharacter_apply_eq_sum_character
        (ρ := (π i).ρ)
        (u := centerRealToComplexCenter (G := G) u)
        (hfinrank := hfinrank_ne i))
  -- The conjugate-index character formula turns the left coordinate into the complex conjugate of
  -- the right one, while the coefficients stay fixed because they come from `ℝ`.
  calc
    star
        (((Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete)
            (centerRealToComplexCenter (G := G) u))
          (conjugateIndex_e2137 π hπ_complete i)) =
      star
        ((Module.finrank ℂ (π (conjugateIndex_e2137 π hπ_complete i)) : ℂ)⁻¹ *
          ∑ g : G,
            (centerRealToComplexCenter (G := G) u : ℂ[G]) g *
              (π (conjugateIndex_e2137 π hπ_complete i)).ρ.character g) := by
            rw [hleft]
    _ =
      (Module.finrank ℂ (π i) : ℂ)⁻¹ *
        ∑ g : G,
          (centerRealToComplexCenter (G := G) u : ℂ[G]) g * (π i).ρ.character g := by
            rw [conjugateIndex_finrank_eq π hπ_complete i]
            simp_rw [centerRealToComplexCenter_apply,
              congrFun (conjugateIndex_character π hπ_complete i)]
            simp [map_sum, mul_assoc, mul_left_comm, mul_comm]
    _ =
      ((Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete)
          (centerRealToComplexCenter (G := G) u))
        i := hright.symm

/-- Helper for Exercise `13-13.2-7`: the complex central-character map sends `1` to the constant
function `1` when viewed over `ℝ`. -/
lemma complexCenterToDualFunReal_map_one
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete 1 = 1 := by
  simp

/-- Helper for Exercise `13-13.2-7`: the complex central-character map preserves multiplication
when viewed over `ℝ`. -/
lemma complexCenterToDualFunReal_map_mul
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (u v : Subalgebra.center ℂ (ℂ[G])) :
    Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete (u * v) =
      Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete u *
        Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete v := by
  simp

/-- Helper for Exercise `13-13.2-7`: the complex central-character map sends `0` to `0` when
viewed over `ℝ`. -/
lemma complexCenterToDualFunReal_map_zero
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete 0 = 0 := by
  simp

/-- Helper for Exercise `13-13.2-7`: the complex central-character map preserves addition when
viewed over `ℝ`. -/
lemma complexCenterToDualFunReal_map_add
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (u v : Subalgebra.center ℂ (ℂ[G])) :
    Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete (u + v) =
      Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete u +
        Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete v := by
  simp

/-- Helper for Exercise `13-13.2-7`: real scalars commute with the complex central-character map.
-/
lemma complexCenterToDualFunReal_commutes
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (r : ℝ) :
    Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
        (algebraMap ℝ (Subalgebra.center ℂ (ℂ[G])) r) =
      algebraMap ℝ (ι → ℂ) r := by
  -- Rewrite the real scalar in the complex center as the corresponding complex scalar.
  rw [show algebraMap ℝ (Subalgebra.center ℂ (ℂ[G])) r =
      algebraMap ℂ (Subalgebra.center ℂ (ℂ[G])) (r : ℂ) by rfl]
  -- Then the complex central-character equivalence commutes with scalar maps.
  ext i
  simp

/-- Helper for Exercise `13-13.2-7`: the complex central-character map viewed as an
`ℝ`-algebra hom. -/
noncomputable def complexCenterToDualFunReal
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Subalgebra.center ℂ (ℂ[G]) →ₐ[ℝ] (ι → ℂ) :=
  { toFun := fun u ↦ Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete u
    map_one' := complexCenterToDualFunReal_map_one π hπ_pairwise hπ_complete
    map_mul' := complexCenterToDualFunReal_map_mul π hπ_pairwise hπ_complete
    map_zero' := complexCenterToDualFunReal_map_zero π hπ_pairwise hπ_complete
    map_add' := complexCenterToDualFunReal_map_add π hπ_pairwise hπ_complete
    commutes' := complexCenterToDualFunReal_commutes π hπ_pairwise hπ_complete }

/-- Helper for Exercise `13-13.2-7`: package the real center into the dual-index fixed owner. -/
noncomputable def centerRealGroupRingToFixedDualFun
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Subalgebra.center ℝ (ℝ[G]) →ₐ[ℝ] FixedDualFun π hπ_complete :=
  -- View the complex central-character equivalence over `ℝ`, then cod-restrict to the fixed owner.
  AlgHom.codRestrict
    ((complexCenterToDualFunReal (G := G) π hπ_pairwise hπ_complete).comp
      (centerRealToComplexCenter (G := G)))
    (FixedDualFun π hπ_complete)
    (centerRealGroupRingToDualFun_isFixed (G := G) π hπ_pairwise hπ_complete)

/-- Helper for Exercise `13-13.2-7`: the center-side packaging map into the dual fixed owner is
injective. -/
lemma injective_centerRealGroupRingToFixedDualFun
    {ι : Type v} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Function.Injective (centerRealGroupRingToFixedDualFun (G := G) π hπ_pairwise hπ_complete) := by
  intro u v huv
  -- Forget the codomain restriction and compare in the ambient product algebra.
  have hcomplex : centerRealToComplexCenter (G := G) u = centerRealToComplexCenter (G := G) v := by
    apply (Representation.centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete).injective
    exact congrArg Subtype.val huv
  -- Coefficientwise injectivity of `ℝ → ℂ` recovers equality in the real center.
  ext g
  apply (algebraMap ℝ ℂ).injective
  simpa [centerRealToComplexCenter_apply] using
    congrArg (fun z : Subalgebra.center ℂ (ℂ[G]) ↦ (z : ℂ[G]) g) hcomplex

/-- Helper for Exercise `13-13.2-7`: inversion on conjugacy classes as a permutation. -/
noncomputable def conjClassesInvPerm :
    Equiv.Perm (ConjClasses G) where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv

/-- Helper for Exercise `13-13.2-7`: the dual-index involution is permutation-conjugate to
inversion on conjugacy classes after choosing a suitable indexing equivalence. -/
lemma exists_equiv_conjugateIndex_inv
    {ι : Type v} [Fintype ι] (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    ∃ e : ι ≃ ConjClasses G, ∀ i, e (conjugateIndex_e2137 π hπ_complete i) = (e i)⁻¹ := by
  classical
  let πfd : ι → FDRep ℂ G := fun i ↦ FDRep.of (π i).ρ
  have hπfd_pairwise : PairwiseNonisomorphic πfd :=
    Representation.pairwiseNonisomorphic_fdrep_of_rep (π := π) hπ_pairwise
  have hcard : Fintype.card ι = Fintype.card (ConjClasses G) := by
    let b := Representation.irreducible_characters_basis_of_complete_family ℂ πfd
      hπfd_pairwise hπ_complete
    letI : Module.Free ℤ (R(G)) := Module.Free.of_basis b
    letI : Module.Finite ℤ (R(G)) := Module.Finite.of_basis b
    rcases tensorCharacterRing_complex_algEquiv_conjClasses (G := G) with ⟨eχ⟩
    calc
      Fintype.card ι = Module.finrank ℤ (R(G)) := by
        symm
        simpa using Module.finrank_eq_card_basis b
      _ = Module.finrank ℂ (ℂ ⊗R(G)) := by
        symm
        rw [Module.finrank_tensorProduct]
        simp
      _ = Module.finrank ℂ (ConjClasses G → ℂ) := by
        simpa using eχ.toLinearEquiv.finrank_eq
      _ = Fintype.card (ConjClasses G) := Module.finrank_fintype_fun_eq_card ℂ
  let e₀ : ι ≃ ConjClasses G := Fintype.equivOfCardEq hcard
  let σdual : Equiv.Perm ι :=
    Equiv.ofBijective (conjugateIndex_e2137 π hπ_complete) <| by
      constructor
      · intro i j hij
        calc
          i = conjugateIndex_e2137 π hπ_complete (conjugateIndex_e2137 π hπ_complete i) := by
            symm
            exact conjugateIndex_involution π hπ_complete hπ_pairwise i
          _ = conjugateIndex_e2137 π hπ_complete (conjugateIndex_e2137 π hπ_complete j) := by
            simpa [hij]
          _ = j := conjugateIndex_involution π hπ_complete hπ_pairwise j
      · intro i
        exact ⟨conjugateIndex_e2137 π hπ_complete i,
          conjugateIndex_involution π hπ_complete hπ_pairwise i⟩
  let σconj : Equiv.Perm ι :=
    (e₀.trans (conjClassesInvPerm (G := G))).trans e₀.symm
  have hσdual_sq : σdual ^ 2 = 1 := by
    -- The complete-family dual partner is an honest involution.
    ext i
    exact conjugateIndex_involution π hπ_complete hπ_pairwise i
  have hσconj_sq : σconj ^ 2 = 1 := by
    -- Inversion on conjugacy classes is itself an involution.
    ext i
    simp [σconj, conjClassesInvPerm, pow_two]
  have hfixed_dual :
      Fintype.card (Function.fixedPoints σdual) =
        Nat.card { i // conjugateIndex_e2137 π hπ_complete i = i } := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      { toFun := fun i ↦ ⟨i.1, i.2⟩
        invFun := fun i ↦ ⟨i.1, i.2⟩
        left_inv := by
          intro i
          cases i
          rfl
        right_inv := by
          intro i
          cases i
          rfl }
  have hfixed_conj :
      Fintype.card (Function.fixedPoints σconj) =
        Nat.card { c : ConjClasses G // c.IsEven } := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      { toFun := fun i ↦
          ⟨e₀ i.1, by
            -- A fixed point of the transported involution is exactly an even conjugacy class.
            change (e₀ i.1)⁻¹ = e₀ i.1
            have hi := congrArg e₀ i.2
            simpa [σconj, conjClassesInvPerm, Equiv.trans_apply] using hi⟩
        invFun := fun c ↦
          ⟨e₀.symm c.1, by
            -- The converse direction is the same calculation after applying `e₀.symm`.
            apply e₀.injective
            simpa [ConjClasses.IsEven, σconj, conjClassesInvPerm, Equiv.trans_apply] using c.2⟩
        left_inv := by
          intro i
          cases i with
          | mk i hi =>
              apply Subtype.ext
              simp
        right_inv := by
          intro c
          cases c with
          | mk c hc =>
              apply Subtype.ext
              simp }
  have hfixed_eq :
      Fintype.card (Function.fixedPoints σdual) =
        Fintype.card (Function.fixedPoints σconj) := by
    rw [hfixed_dual, hfixed_conj]
    simpa [πfd] using
      card_fixed_conjugateIndex_eq_card_even_conjClasses
        (G := G) πfd hπfd_pairwise hπ_complete
  have hsum_eq : σdual.cycleType.sum = σconj.cycleType.sum := by
    have hdual_card := Equiv.Perm.card_fixedPoints σdual
    have hconj_card := Equiv.Perm.card_fixedPoints σconj
    have hdual_le : σdual.cycleType.sum ≤ Fintype.card ι :=
      Equiv.Perm.sum_cycleType_le σdual
    have hconj_le : σconj.cycleType.sum ≤ Fintype.card ι :=
      Equiv.Perm.sum_cycleType_le σconj
    have hsub :
        Fintype.card ι - σdual.cycleType.sum =
          Fintype.card ι - σconj.cycleType.sum := by
      simpa [hdual_card, hconj_card] using hfixed_eq
    omega
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hcycle_dual :
      σdual.cycleType = Multiset.replicate σdual.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσdual_sq
  have hcycle_conj :
      σconj.cycleType = Multiset.replicate σconj.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσconj_sq
  have hcard_cycle : σdual.cycleType.card = σconj.cycleType.card := by
    rw [hcycle_dual, hcycle_conj, Multiset.sum_replicate, Multiset.sum_replicate, nsmul_eq_mul,
      nsmul_eq_mul] at hsum_eq
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hsum_eq
  have hcycle : σdual.cycleType = σconj.cycleType := by
    rw [hcycle_dual, hcycle_conj, hcard_cycle]
  rcases (isConj_iff.mp ((Equiv.Perm.isConj_iff_cycleType_eq).2 hcycle)) with ⟨u, hu⟩
  refine ⟨u.trans e₀, ?_⟩
  intro i
  -- Conjugating the dual-index involution by `u` and then transporting by `e₀` gives inversion.
  have hu_apply : u (σdual i) = σconj (u i) := by
    have hu_point := congrArg (fun p : Equiv.Perm ι ↦ p (u i)) hu
    simpa [Equiv.Perm.mul_apply] using hu_point
  have hu_apply' := congrArg e₀ hu_apply
  calc
    (u.trans e₀) (conjugateIndex_e2137 π hπ_complete i) = e₀ (u (σdual i)) := by
      simp [σdual, Equiv.trans_apply]
    _ = e₀ (σconj (u i)) := hu_apply'
    _ = ((u.trans e₀) i)⁻¹ := by
      simp [σconj, conjClassesInvPerm, Equiv.trans_apply]

/-- Helper for Exercise `13-13.2-7`: the fixed tensor-owner relation on conjugacy-class
functions. -/
def IsFixedConjFun (F : ConjClasses G → ℂ) : Prop :=
  ∀ c, star (F c⁻¹) = F c

/-- Helper for Exercise `13-13.2-7`: the fixed conjugacy-class relation is stable under zero. -/
lemma isFixedConjFun_zero :
    IsFixedConjFun (G := G) (0 : ConjClasses G → ℂ) := by
  intro c
  simp

/-- Helper for Exercise `13-13.2-7`: the fixed conjugacy-class relation is stable under addition.
-/
lemma isFixedConjFun_add
    {F H : ConjClasses G → ℂ}
    (hF : IsFixedConjFun (G := G) F)
    (hH : IsFixedConjFun (G := G) H) :
    IsFixedConjFun (G := G) (F + H) := by
  intro c
  -- The fixedness relation is coordinatewise and additive.
  simpa using congrArg₂ (fun x y ↦ x + y) (hF c) (hH c)

/-- Helper for Exercise `13-13.2-7`: the fixed conjugacy-class relation is stable under
multiplication. -/
lemma isFixedConjFun_mul
    {F H : ConjClasses G → ℂ}
    (hF : IsFixedConjFun (G := G) F)
    (hH : IsFixedConjFun (G := G) H) :
    IsFixedConjFun (G := G) (F * H) := by
  intro c
  -- Complex conjugation reverses products, so commutativity of `ℂ` restores the target order.
  simp [Pi.mul_apply, hF c, hH c, mul_comm]

/-- Helper for Exercise `13-13.2-7`: the fixed conjugacy-class relation is stable under the
constant function `1`. -/
lemma isFixedConjFun_one :
    IsFixedConjFun (G := G) (1 : ConjClasses G → ℂ) := by
  intro c
  simp

/-- Helper for Exercise `13-13.2-7`: real scalars act through fixed constant functions. -/
lemma isFixedConjFun_algebraMap
    (r : ℝ) :
    IsFixedConjFun (G := G) fun _ : ConjClasses G ↦ (r : ℂ) := by
  intro c
  simp

/-- Helper for Exercise `13-13.2-7`: the tensor-side fixed owner as a concrete `ℝ`-subalgebra of
complex-valued functions on the conjugacy classes. -/
def fixedConjFunSubalgebra :
    Subalgebra ℝ (ConjClasses G → ℂ) :=
  { carrier := { F | IsFixedConjFun (G := G) F }
    zero_mem' := isFixedConjFun_zero (G := G)
    add_mem' := fun hF hH ↦ isFixedConjFun_add (G := G) hF hH
    one_mem' := isFixedConjFun_one (G := G)
    mul_mem' := fun hF hH ↦ isFixedConjFun_mul (G := G) hF hH
    algebraMap_mem' := isFixedConjFun_algebraMap (G := G) }

/-- Helper for Exercise `13-13.2-7`: shorthand for the tensor-side fixed owner on conjugacy
classes. -/
abbrev FixedConjFun :=
  fixedConjFunSubalgebra (G := G)

/-- Helper for Exercise `13-13.2-7`: reindexing by an involution-compatible equivalence carries
the dual fixed owner to the conjugacy-class fixed owner. -/
lemma exists_fixedDualFun_algEquiv_fixedConjFun
    {ι : Type v} [Fintype ι] (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Nonempty (FixedDualFun π hπ_complete ≃ₐ[ℝ] FixedConjFun (G := G)) := by
  classical
  rcases exists_equiv_conjugateIndex_inv (G := G) π hπ_pairwise hπ_complete with ⟨e, he⟩
  let E : (ι → ℂ) ≃ₐ[ℝ] (ConjClasses G → ℂ) :=
    AlgEquiv.piCongrLeft' ℝ (fun _ : ι ↦ ℂ) e
  have he_symm (c : ConjClasses G) :
      conjugateIndex_e2137 π hπ_complete (e.symm c) = e.symm (c⁻¹) := by
    apply e.injective
    simpa using he (e.symm c)
  refine ⟨
    { toFun := fun F ↦ ⟨E F, ?_⟩
      invFun := fun H ↦ ⟨E.symm H, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_
      commutes' := ?_ }⟩
  · -- Reindex the dual-index fixedness relation along `e`.
    intro c
    simpa [E, he_symm c] using F.2 (e.symm c)
  · -- The inverse reindexing turns inversion-fixed functions back into dual-index fixed ones.
    intro i
    simpa [E, he i] using H.2 (e i)
  · intro F
    apply Subtype.ext
    ext i
    simp [E]
  · intro H
    apply Subtype.ext
    ext c
    simp [E]
  · intro F H
    apply Subtype.ext
    exact E.map_mul F H
  · intro F H
    apply Subtype.ext
    exact E.map_add F H
  · intro r
    apply Subtype.ext
    exact E.commutes r

/-- Helper for Exercise `13-13.2-7`: transport the dual fixed owner to the conjugacy-class fixed
owner through an involution-compatible indexing equivalence. -/
noncomputable def fixedDualFun_algEquiv_fixedConjFun
    {ι : Type v} [Fintype ι] (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    FixedDualFun π hπ_complete ≃ₐ[ℝ] FixedConjFun (G := G) :=
  Classical.choice <|
    exists_fixedDualFun_algEquiv_fixedConjFun (G := G) π hπ_pairwise hπ_complete

/-- Helper for Exercise `13-13.2-7`: evaluate a real tensor character on conjugacy classes. -/
noncomputable def tensorCharacterRingToConjClassesFun
    (χ : ℝ ⊗R(G)) :
    ConjClasses G → ℂ :=
  (Representation.isClassFunction_of_mem_characterRingScalarExtension
    (Representation.tensorCharacterRing_mem_characterRingScalarExtension χ)).lift

/-- Helper for Exercise `13-13.2-7`: evaluating on the conjugacy class of `g` recovers the
underlying realized tensor character at `g`. -/
lemma tensorCharacterRingToConjClassesFun_apply_mk
    (χ : ℝ ⊗R(G)) (g : G) :
    tensorCharacterRingToConjClassesFun (G := G) χ (ConjClasses.mk g) = (χ : G → ℂ) g := by
  rfl

/-- Helper for Exercise `13-13.2-7`: evaluating a realized real tensor character on conjugacy
classes is an `ℝ`-algebra map. -/
noncomputable def classFunctionSubalgebraEvalConjClassesReal :
    Representation.characterRingScalarExtensionSubalgebra ℝ G →ₐ[ℝ] (ConjClasses G → ℂ) where
  toFun f :=
    (Representation.isClassFunction_of_mem_characterRingScalarExtension
      (show (f : G → ℂ) ∈ Representation.characterRingScalarExtension ℝ G from f.2)).lift
  map_one' := by
    -- Evaluating the scalar-extended trivial character gives the constant function `1`.
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_mul' f g := by
    -- The class-function lift preserves pointwise multiplication.
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_zero' := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_add' f g := by
    -- The class-function lift preserves pointwise addition.
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    simp
  commutes' r := by
    -- Real scalars act as constant class functions after evaluation.
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp

/-- Helper for Exercise `13-13.2-7`: evaluation on conjugacy classes is an `ℝ`-algebra map on the
real tensor character ring. -/
noncomputable def tensorCharacterRingToConjClasses :
    ℝ ⊗R(G) →ₐ[ℝ] (ConjClasses G → ℂ) :=
  (classFunctionSubalgebraEvalConjClassesReal (G := G)).comp
    (Representation.tensorCharacterRingToSubalgebra ℝ G)

/-- Helper for Exercise `13-13.2-7`: the composed real evaluation map agrees with the realized
tensor character on each conjugacy class representative. -/
lemma tensorCharacterRingToConjClasses_apply_mk
    (χ : ℝ ⊗R(G)) (g : G) :
    tensorCharacterRingToConjClasses (G := G) χ (ConjClasses.mk g) = (χ : G → ℂ) g := by
  -- Unfold the composed evaluation map and evaluate on a representative.
  rfl

/-- Helper for Exercise `13-13.2-7`: the image of a real tensor character satisfies the involutive
fixed-owner relation on conjugacy classes. -/
lemma tensorCharacterRingToConjClasses_isFixed
    (χ : ℝ ⊗R(G)) :
    IsFixedConjFun (G := G) (tensorCharacterRingToConjClasses (G := G) χ) := by
  intro c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  -- Reduce the fixedness relation to the realized tensor character identity on `g` and `g⁻¹`.
  rw [ConjClasses.inv_mk, tensorCharacterRingToConjClasses_apply_mk,
    tensorCharacterRingToConjClasses_apply_mk]
  induction χ using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul r ψ =>
      -- On pure tensors, the scalar is real and the virtual character handles inversion.
      simp [Representation.coe_tmul, Pi.smul_apply, Algebra.smul_def,
        virtual_character_inv_eq_star]
  | add χ ψ hχ hψ =>
      -- The fixedness identity is additive in the tensor variable.
      simpa using congrArg₂ (fun x y : ℂ ↦ x + y) hχ hψ

/-- Helper for Exercise `13-13.2-7`: the tensor-side owner map lands in the fixed conjugacy-class
subalgebra. -/
noncomputable def tensorCharacterRingToFixedConjFun :
    ℝ ⊗R(G) →ₐ[ℝ] FixedConjFun (G := G) :=
  AlgHom.codRestrict
    (tensorCharacterRingToConjClasses (G := G))
    (FixedConjFun (G := G))
    (tensorCharacterRingToConjClasses_isFixed (G := G))

/-- Helper for Exercise `13-13.2-7`: the tensor-side owner map into the fixed conjugacy-class
owner is injective. -/
lemma tensorCharacterRingToConjClasses_injective :
    Function.Injective (tensorCharacterRingToConjClasses (G := G)) := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  letI : DecidableEq ι := Classical.decEq ι
  let b :=
    Representation.irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let bt := Algebra.TensorProduct.basis ℝ b
  have hpair_sum :
      ∀ s : Finset ι, ∀ a : ι → ℂ, ∀ ψ : G → ℂ,
        ⟪∑ j ∈ s, a j • (π j).character, ψ⟫ =
          ∑ j ∈ s, a j * ⟪(π j).character, ψ⟫ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro a ψ
      simp [Representation.groupFunctionPairingOverField]
    · intro i s hi ih a ψ
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]
  have horth :
      Pairwise fun i j ↦
        ⟪(π i).character, (π j).character⟫ = (0 : ℂ) :=
    Representation.irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      ℂ π hπ_complete.isSimple hπ_pairwise
  have hdiag : ∀ i : ι, ⟪(π i).character, (π i).character⟫ = (1 : ℂ) := by
    intro i
    letI : Simple (π i) := hπ_complete.isSimple i
    have hself : Nonempty (π i ≅ π i) := ⟨Iso.refl _⟩
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
      (FDRep.char_orthonormal (π i) (π i))
  have hlin_char_complex : LinearIndependent ℂ fun i ↦ (π i).character := by
    -- Route correction: use orthogonality of irreducible characters to isolate the real tensor
    -- coefficients after expanding on the canonical tensor-product basis.
    rw [linearIndependent_iff']
    intro s a hsum i hi
    have hpair_zero :
        ⟪∑ j ∈ s, a j • (π j).character, (π i).character⟫ = 0 := by
      have hpair_eq :
          Representation.groupFunctionPairingOverField ℂ
              (∑ j ∈ s, a j • (π j).character) (π i).character =
            Representation.groupFunctionPairingOverField ℂ 0 (π i).character := by
        exact
          congrArg
            (fun ψ : G → ℂ ↦ Representation.groupFunctionPairingOverField ℂ ψ (π i).character) hsum
      have hzero_pair :
          Representation.groupFunctionPairingOverField ℂ 0 (π i).character = 0 := by
        simp [Representation.groupFunctionPairingOverField]
      exact hpair_eq.trans hzero_pair
    rw [hpair_sum s a ((π i).character), Finset.sum_eq_single i] at hpair_zero
    · simpa [hdiag i] using hpair_zero
    · intro j hj hji
      rw [horth hji, mul_zero]
    · intro hnot
      exact (hnot hi).elim
  have hlin_char_real : LinearIndependent ℝ fun i ↦ (π i).character :=
    hlin_char_complex.restrict_scalars' ℝ
  intro χ ψ hχψ
  let δ : ℝ ⊗R(G) := χ - ψ
  have hzero_fun : ((δ : ℝ ⊗R(G)) : G → ℂ) = 0 := by
    -- Equality on conjugacy classes forces equality of the realized class functions on `G`.
    funext g
    have hvalue : tensorCharacterRingToConjClasses (G := G) χ (ConjClasses.mk g) =
        tensorCharacterRingToConjClasses (G := G) ψ (ConjClasses.mk g) := by
      exact congrFun hχψ (ConjClasses.mk g)
    have hvalue' : (χ : G → ℂ) g = (ψ : G → ℂ) g := by
      simpa [tensorCharacterRingToConjClasses_apply_mk] using hvalue
    simpa [δ] using sub_eq_zero.mpr hvalue'
  let c : ι → ℝ := bt.repr δ
  have hbt_apply (i : ι) : ((bt i : ℝ ⊗R(G)) : G → ℂ) = (π i).character := by
    ext g
    simp [bt, b, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply, Representation.coe_tmul]
  have hχ_expand :
      ∑ i, c i • (π i).character = ((δ : ℝ ⊗R(G)) : G → ℂ) := by
    -- Expanding in the tensor basis turns the realized tensor character into a real linear
    -- combination of irreducible characters.
    calc
      ∑ i, c i • (π i).character = ∑ i, c i • ((bt i : ℝ ⊗R(G)) : G → ℂ) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hbt_apply i]
      _ = ((δ : ℝ ⊗R(G)) : G → ℂ) := by
        have hsum : (((∑ i, c i • bt i : ℝ ⊗R(G)) : G → ℂ)) = (δ : G → ℂ) := by
          simpa [c] using congrArg (fun z : ℝ ⊗R(G) ↦ (z : G → ℂ)) (bt.sum_repr δ)
        simpa using hsum
  have hc_zero : c = 0 := by
    ext i
    exact
      (linearIndependent_iff'.mp hlin_char_real)
        Finset.univ c (by simpa [hzero_fun] using hχ_expand) i (Finset.mem_univ i)
  have hrepr : bt.repr δ = 0 := by
    ext i
    simpa [c] using congrFun hc_zero i
  have hsub : δ = 0 := bt.repr.injective hrepr
  have hsub' : χ - ψ = 0 := by simpa [δ] using hsub
  exact sub_eq_zero.mp hsub'

/-- Helper for Exercise `13-13.2-7`: the tensor-side owner map into the fixed conjugacy-class
owner is injective. -/
lemma injective_tensorCharacterRingToFixedConjFun :
    Function.Injective (tensorCharacterRingToFixedConjFun (G := G)) := by
  intro χ ψ hχψ
  -- Forget the codomain restriction and compare in the ambient conjugacy-class owner.
  exact tensorCharacterRingToConjClasses_injective (G := G) (congrArg Subtype.val hχψ)

/-- Helper for Exercise `13-13.2-7`: averaging a conjugacy-class function with the conjugate
inversion involution produces a fixed function. -/
lemma isFixedConjFun_average
    (F : ConjClasses G → ℂ) :
    IsFixedConjFun (G := G) (fun c ↦ (F c + star (F c⁻¹)) / 2) := by
  intro c
  -- Swapping `c` with `c⁻¹` and conjugating leaves the averaged function unchanged.
  simp [IsFixedConjFun, add_comm, add_left_comm, add_assoc]

/-- Helper for Exercise `13-13.2-7`: the complementary skew-average also lands in the fixed
owner. -/
lemma isFixedConjFun_skew
    (F : ConjClasses G → ℂ) :
    IsFixedConjFun (G := G) (fun c ↦ (Complex.I / 2) * (star (F c⁻¹) - F c)) := by
  intro c
  -- Conjugation changes the sign of `I`, which exactly compensates for the skew term.
  simp [IsFixedConjFun, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
    mul_left_comm, mul_assoc]
  ring

/-- Helper for Exercise `13-13.2-7`: the average part of a conjugacy-class function, viewed in
the fixed conjugacy-class owner. -/
abbrev fixedConjFunAverage
    (F : ConjClasses G → ℂ) :
    (FixedConjFun (G := G)).toSubmodule :=
  ⟨fun c ↦ (F c + star (F c⁻¹)) / 2, isFixedConjFun_average (G := G) F⟩

/-- Helper for Exercise `13-13.2-7`: the skew part of a conjugacy-class function, viewed in the
fixed conjugacy-class owner. -/
abbrev fixedConjFunSkew
    (F : ConjClasses G → ℂ) :
    (FixedConjFun (G := G)).toSubmodule :=
  ⟨fun c ↦ (Complex.I / 2) * (star (F c⁻¹) - F c), isFixedConjFun_skew (G := G) F⟩

/-- Helper for Exercise `13-13.2-7`: the explicit average/skew decomposition recovers every
conjugacy-class function. -/
lemma fixedConjFun_average_skew_decomposition
    (F : ConjClasses G → ℂ) :
    (fixedConjFunAverage (G := G) F : ConjClasses G → ℂ) +
        Complex.I • (fixedConjFunSkew (G := G) F : ConjClasses G → ℂ) = F := by
  -- The average and skew formulas were chosen so that the `star`-terms cancel pointwise.
  ext c
  simp [fixedConjFunAverage, fixedConjFunSkew, Pi.smul_apply, div_eq_mul_inv, sub_eq_add_neg]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Helper for Exercise `13-13.2-7`: averaging the scalar multiple of a fixed function keeps only
the real part of the scalar. -/
lemma fixedConjFun_average_smul_eq
    (z : ℂ) (w : (FixedConjFun (G := G)).toSubmodule) :
    fixedConjFunAverage (G := G) (z • (w : ConjClasses G → ℂ)) =
      ((z.re : ℝ) • w : (FixedConjFun (G := G)).toSubmodule) := by
  -- The fixedness relation on `w` rewrites the conjugated inverse value back to `w c`.
  apply Subtype.ext
  ext c
  have hw : star ((w : ConjClasses G → ℂ) c⁻¹) = (w : ConjClasses G → ℂ) c := w.2 c
  have hz : (z + star z) / 2 = (z.re : ℂ) := by
    apply Complex.ext
    · simp [div_eq_mul_inv]
      ring
    · simp [div_eq_mul_inv]
  calc
    (fixedConjFunAverage (G := G) (z • (w : ConjClasses G → ℂ)) : ConjClasses G → ℂ) c
        = (z * (w : ConjClasses G → ℂ) c + (w : ConjClasses G → ℂ) c * star z) / 2 := by
            simp [fixedConjFunAverage, Pi.smul_apply, Algebra.smul_def, hw, mul_comm, mul_left_comm,
              mul_assoc]
    _ = ((z + star z) / 2) * (w : ConjClasses G → ℂ) c := by
          ring
    _ = (z.re : ℂ) * (w : ConjClasses G → ℂ) c := by
          rw [hz]
    _ = (((z.re : ℝ) • w : (FixedConjFun (G := G)).toSubmodule) : ConjClasses G → ℂ) c := by
          simp [Algebra.smul_def, mul_comm]

/-- Helper for Exercise `13-13.2-7`: the skew part of a scalar multiple of a fixed function keeps
only the imaginary part of the scalar. -/
lemma fixedConjFun_skew_smul_eq
    (z : ℂ) (w : (FixedConjFun (G := G)).toSubmodule) :
    fixedConjFunSkew (G := G) (z • (w : ConjClasses G → ℂ)) =
      ((z.im : ℝ) • w : (FixedConjFun (G := G)).toSubmodule) := by
  -- After using the fixedness relation on `w`, the skew operator reduces to `(I / 2) * (conj z - z)`.
  apply Subtype.ext
  ext c
  have hw : star ((w : ConjClasses G → ℂ) c⁻¹) = (w : ConjClasses G → ℂ) c := w.2 c
  have hz : (Complex.I / 2) * (star z - z) = (z.im : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, div_eq_mul_inv]
      ring
    · simp [Complex.mul_im, div_eq_mul_inv]
  calc
    (fixedConjFunSkew (G := G) (z • (w : ConjClasses G → ℂ)) : ConjClasses G → ℂ) c
        = (Complex.I / 2) * ((w : ConjClasses G → ℂ) c * star z - z * (w : ConjClasses G → ℂ) c) := by
            simp [fixedConjFunSkew, Pi.smul_apply, Algebra.smul_def, hw, mul_comm, mul_left_comm,
              mul_assoc]
    _ = ((Complex.I / 2) * (star z - z)) * (w : ConjClasses G → ℂ) c := by
          ring
    _ = (z.im : ℂ) * (w : ConjClasses G → ℂ) c := by
          rw [hz]
    _ = (((z.im : ℝ) • w : (FixedConjFun (G := G)).toSubmodule) : ConjClasses G → ℂ) c := by
          simp [Algebra.smul_def, mul_comm]

/-- Helper for Exercise `13-13.2-7`: the explicit average/skew inverse recovers each pure tensor
in the fixed conjugacy-class owner. -/
lemma fixedConjFun_inverse_on_pure_tensors
    (z : ℂ) (w : (FixedConjFun (G := G)).toSubmodule) :
    (1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) (z • (w : ConjClasses G → ℂ)) :
        (FixedConjFun (G := G)).toSubmodule) +
      Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) (z • (w : ConjClasses G → ℂ)) :
        (FixedConjFun (G := G)).toSubmodule) =
      z ⊗ₜ[ℝ] w := by
  -- The two scalar-rewrite lemmas identify the real and imaginary tensor components explicitly.
  calc
    (1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) (z • (w : ConjClasses G → ℂ)) :
        (FixedConjFun (G := G)).toSubmodule) +
      Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) (z • (w : ConjClasses G → ℂ)) :
        (FixedConjFun (G := G)).toSubmodule) =
        (1 : ℂ) ⊗ₜ[ℝ] (((z.re : ℝ) • w : (FixedConjFun (G := G)).toSubmodule)) +
          Complex.I ⊗ₜ[ℝ] (((z.im : ℝ) • w : (FixedConjFun (G := G)).toSubmodule)) := by
            rw [fixedConjFun_average_smul_eq (G := G) z w, fixedConjFun_skew_smul_eq (G := G) z w]
    _ = (z.re : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] w) + (z.im : ℂ) • (Complex.I ⊗ₜ[ℝ] w) := by
          rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
          rfl
    _ = ((z.re : ℂ) * (1 : ℂ)) ⊗ₜ[ℝ] w + ((z.im : ℂ) * Complex.I) ⊗ₜ[ℝ] w := by
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
          simp
    _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) ⊗ₜ[ℝ] w := by
          rw [← TensorProduct.add_tmul]
          simp
    _ = z ⊗ₜ[ℝ] w := by
          rw [Complex.re_add_im]

/-- Helper for Exercise `13-13.2-7`: the fixed conjugacy-class owner has one real dimension per
conjugacy class. -/
lemma exists_fixedConjFun_complexification_linearEquiv :
    Nonempty
      (ℂ ⊗[ℝ] (FixedConjFun (G := G)).toSubmodule ≃ₗ[ℂ] (ConjClasses G → ℂ)) := by
  let W : Submodule ℝ (ConjClasses G → ℂ) := (FixedConjFun (G := G)).toSubmodule
  let fR : ℂ →ₗ[ℝ] W →ₗ[ℝ] (ConjClasses G → ℂ) :=
    { toFun := fun z =>
        { toFun := fun w => z • (w : ConjClasses G → ℂ)
          map_add' := by
            intro w₁ w₂
            simp [smul_add]
          map_smul' := by
            intro r w
            -- Move the real scalar through the complex scalar and regroup the multiplication.
            calc
              z • (r • (w : ConjClasses G → ℂ)) = (z * (r : ℂ)) • (w : ConjClasses G → ℂ) := by
                simpa [Complex.coe_smul] using
                  (mul_smul z (r : ℂ) (w : ConjClasses G → ℂ)).symm
              _ = ((r : ℂ) * z) • (w : ConjClasses G → ℂ) := by
                rw [mul_comm]
              _ = r • z • (w : ConjClasses G → ℂ) := by
                simpa [Complex.coe_smul] using
                  (mul_smul (r : ℂ) z (w : ConjClasses G → ℂ)) }
      map_add' := by
        intro z₁ z₂
        ext w c
        simp [add_smul]
      map_smul' := by
        intro r z
        ext w c
        simpa [Algebra.smul_def] using (mul_smul (r : ℂ) z ((w : ConjClasses G → ℂ) c)) }
  let eR : ℂ ⊗[ℝ] W →ₗ[ℝ] (ConjClasses G → ℂ) := TensorProduct.lift fR
  let e : ℂ ⊗[ℝ] W →ₗ[ℂ] (ConjClasses G → ℂ) :=
    { toFun := eR
      map_add' := eR.map_add
      map_smul' := by
        intro c x
        -- Check complex linearity on pure tensors and extend by tensor induction.
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [eR]
        · intro z w
          ext d
          change eR ((c * z) ⊗ₜ[ℝ] w) d = (c • eR (z ⊗ₜ[ℝ] w)) d
          simpa [eR, fR, Algebra.smul_def, Pi.smul_apply] using
            congrFun (mul_smul c z (w : ConjClasses G → ℂ)) d
        · intro x y hx hy
          simp [hx, hy] }
  let inv : (ConjClasses G → ℂ) → ℂ ⊗[ℝ] W := fun F ↦
    (1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) F : W) +
      Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) F : W)
  have he_inv : ∀ F : ConjClasses G → ℂ, e (inv F) = F := by
    intro F
    -- The explicit average/skew inverse evaluates back to the original function.
    calc
      e (inv F) =
          e ((1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) F : W)) +
            e (Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) F : W)) := by
              change e
                  ((1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) F : W) +
                    Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) F : W)) =
                e ((1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) F : W)) +
                  e (Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) F : W))
              exact e.map_add _ _
      _ = (1 : ℂ) • (fixedConjFunAverage (G := G) F : ConjClasses G → ℂ) +
            Complex.I • (fixedConjFunSkew (G := G) F : ConjClasses G → ℂ) := by
              simp [e, eR, fR]
      _ = F := by
            simpa using fixedConjFun_average_skew_decomposition (G := G) F
  have hinv_zero : inv (0 : ConjClasses G → ℂ) = 0 := by
    -- Both pieces vanish on the zero function, so the inverse candidate sends `0` to `0`.
    have havg0 : fixedConjFunAverage (G := G) (0 : ConjClasses G → ℂ) = (0 : W) := by
      apply Subtype.ext
      ext c
      simp [fixedConjFunAverage]
    have hskew0 : fixedConjFunSkew (G := G) (0 : ConjClasses G → ℂ) = (0 : W) := by
      apply Subtype.ext
      ext c
      simp [fixedConjFunSkew]
    show
      (1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) (0 : ConjClasses G → ℂ) : W) +
          Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) (0 : ConjClasses G → ℂ) : W) =
        0
    rw [havg0, hskew0]
    simp
  have hinv_add : ∀ F H : ConjClasses G → ℂ, inv (F + H) = inv F + inv H := by
    intro F H
    have havg :
        fixedConjFunAverage (G := G) (F + H) =
          fixedConjFunAverage (G := G) F + fixedConjFunAverage (G := G) H := by
      -- The average operator is additive pointwise.
      apply Subtype.ext
      ext c
      simp [fixedConjFunAverage, add_assoc, add_left_comm, add_comm]
      ring
    have hskew :
        fixedConjFunSkew (G := G) (F + H) =
          fixedConjFunSkew (G := G) F + fixedConjFunSkew (G := G) H := by
      -- The skew operator is additive pointwise as well.
      apply Subtype.ext
      ext c
      simp [fixedConjFunSkew, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      ring
    show
      (1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) (F + H) : W) +
          Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) (F + H) : W) =
        ((1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) F : W) +
            Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) F : W)) +
          ((1 : ℂ) ⊗ₜ[ℝ] (fixedConjFunAverage (G := G) H : W) +
            Complex.I ⊗ₜ[ℝ] (fixedConjFunSkew (G := G) H : W))
    rw [havg, hskew, TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel
  have hinv_e : ∀ x : ℂ ⊗[ℝ] W, inv (e x) = x := by
    intro x
    -- It is enough to verify the inverse formula on pure tensors and extend by tensor induction.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · rw [LinearMap.map_zero]
      exact hinv_zero
    · intro z w
      have he_tmul : e (z ⊗ₜ[ℝ] w) = z • (w : ConjClasses G → ℂ) := by
        rfl
      rw [he_tmul]
      simpa [inv] using fixedConjFun_inverse_on_pure_tensors (G := G) z w
    · intro x y hx hy
      rw [LinearMap.map_add, hinv_add, hx, hy]
  have hbij : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hxy' := congrArg inv hxy
      simpa [hinv_e x, hinv_e y] using hxy'
    · intro F
      exact ⟨inv F, he_inv F⟩
  exact ⟨LinearEquiv.ofBijective e hbij⟩

/-- Helper for Exercise `13-13.2-7`: the fixed conjugacy-class owner has one real dimension per
conjugacy class. -/
lemma finrank_fixedConjFun_eq_card_conjClasses :
    Module.finrank ℝ (FixedConjFun (G := G)).toSubmodule = Fintype.card (ConjClasses G) := by
  let W : Submodule ℝ (ConjClasses G → ℂ) := (FixedConjFun (G := G)).toSubmodule
  letI : IsScalarTower ℝ ℂ ℂ := by
    infer_instance
  letI : FiniteDimensional ℝ (ConjClasses G → ℂ) := by
    infer_instance
  letI : Module.Free ℂ ℂ := Module.Free.of_divisionRing ℂ ℂ
  letI : Module.Free ℝ W := Module.Free.of_divisionRing ℝ W
  letI : FiniteDimensional ℝ W :=
    FiniteDimensional.of_injective (Submodule.subtype W) Subtype.val_injective
  rcases exists_fixedConjFun_complexification_linearEquiv (G := G) with ⟨e⟩
  have htensor : Module.finrank ℂ (ℂ ⊗[ℝ] W) = Module.finrank ℝ W := by
    exact Module.finrank_baseChange (R := ℂ) (S := ℝ) (M' := W)
  -- Compare the complexified fixed owner with all class functions by the explicit linear equivalence.
  calc
    Module.finrank ℝ W = Module.finrank ℂ (ℂ ⊗[ℝ] W) := htensor.symm
    _ = Module.finrank ℂ (ConjClasses G → ℂ) := by
          exact e.finrank_eq
    _ = Fintype.card (ConjClasses G) := Module.finrank_fintype_fun_eq_card ℂ

/-- Exercise 13-13.2-7: the center of the real group algebra `ℝ[G]` is `ℝ`-algebra isomorphic
to Serre's tensor character ring `ℝ ⊗R(G)`. -/
theorem center_realGroupRing_algEquiv_tensorCharacterRing :
    Nonempty (Subalgebra.center ℝ (ℝ[G]) ≃ₐ[ℝ] ℝ ⊗R(G)) := by
  classical
  let W : Submodule ℝ (ConjClasses G → ℂ) := (FixedConjFun (G := G)).toSubmodule
  letI : FiniteDimensional ℝ (ConjClasses G → ℂ) := by
    infer_instance
  letI : Module.Free ℝ W := Module.Free.of_divisionRing ℝ W
  letI : FiniteDimensional ℝ W :=
    FiniteDimensional.of_injective (Submodule.subtype W) Subtype.val_injective
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  obtain ⟨ι, _, πfd, hπfd_pairwise, hπfd_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  let b :=
    Representation.irreducible_characters_basis_of_complete_family ℂ πfd
      hπfd_pairwise hπfd_complete
  letI : Module.Free ℤ (R(G)) := Module.Free.of_basis b
  letI : Module.Finite ℤ (R(G)) := Module.Finite.of_basis b
  let π : ι → Rep ℂ G := fun i ↦ Rep.of (πfd i).ρ
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro i j hij hij_iso
    apply hπfd_pairwise hij
    rcases hij_iso with ⟨e⟩
    simpa [π] using ⟨(Representation.equivOfIso e).toFDRepIso⟩
  have hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ) := by
    simpa [π] using hπfd_complete
  rcases exists_equiv_conjugateIndex_inv (G := G) π hπ_pairwise hπ_complete with ⟨eι, _⟩
  have hcard :
      Fintype.card ι = Fintype.card (ConjClasses G) := Fintype.card_congr eι
  let eFixed := fixedDualFun_algEquiv_fixedConjFun (G := G) π hπ_pairwise hπ_complete
  let fCenter : Subalgebra.center ℝ (ℝ[G]) →ₐ[ℝ] FixedConjFun (G := G) :=
    eFixed.toAlgHom.comp
      (centerRealGroupRingToFixedDualFun (G := G) π hπ_pairwise hπ_complete)
  have hCenter_inj : Function.Injective fCenter := by
    intro u v huv
    exact
      injective_centerRealGroupRingToFixedDualFun (G := G) π hπ_pairwise hπ_complete
        (eFixed.injective huv)
  have hFixedDim :
      Module.finrank ℝ W = Fintype.card (ConjClasses G) := by
    change Module.finrank ℝ ((FixedConjFun (G := G)).toSubmodule) = Fintype.card (ConjClasses G)
    exact finrank_fixedConjFun_eq_card_conjClasses (G := G)
  have hCenterDim :
      Module.finrank ℝ (Subalgebra.center ℝ (ℝ[G])) =
        Module.finrank ℝ W := by
    calc
      Module.finrank ℝ (Subalgebra.center ℝ (ℝ[G])) = Fintype.card (ConjClasses G) := by
        exact finrank_center_realGroupRing_eq_card_conjClasses (G := G)
      _ = Module.finrank ℝ W := hFixedDim.symm
  have hCenter_surj : Function.Surjective fCenter := by
    let fCenterL :
        Subalgebra.center ℝ (ℝ[G]) →ₗ[ℝ] W := fCenter.toLinearMap
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := fCenterL) hCenterDim).mp hCenter_inj
  let eCenter : Subalgebra.center ℝ (ℝ[G]) ≃ₐ[ℝ] FixedConjFun (G := G) :=
    AlgEquiv.ofBijective fCenter ⟨hCenter_inj, hCenter_surj⟩
  let fTensor : ℝ ⊗R(G) →ₐ[ℝ] FixedConjFun (G := G) :=
    tensorCharacterRingToFixedConjFun (G := G)
  have hTensor_inj : Function.Injective fTensor :=
    injective_tensorCharacterRingToFixedConjFun (G := G)
  have hTensorDim :
      Module.finrank ℝ (ℝ ⊗R(G)) =
        Module.finrank ℝ W := by
    calc
      Module.finrank ℝ (ℝ ⊗R(G)) = Fintype.card ι := by
        exact
          finrank_tensorCharacterRing_real_eq_card_irreducible (G := G) πfd
            hπfd_pairwise hπfd_complete
      _ = Fintype.card (ConjClasses G) := hcard
      _ = Module.finrank ℝ W := hFixedDim.symm
  have hTensor_surj : Function.Surjective fTensor := by
    let fTensorL : ℝ ⊗R(G) →ₗ[ℝ] W := fTensor.toLinearMap
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := fTensorL) hTensorDim).mp hTensor_inj
  let eTensor : ℝ ⊗R(G) ≃ₐ[ℝ] FixedConjFun (G := G) :=
    AlgEquiv.ofBijective fTensor ⟨hTensor_inj, hTensor_surj⟩
  -- Both algebras identify with the same fixed-owner model, so compose the resulting equivalences.
  exact ⟨eCenter.trans eTensor.symm⟩

end
