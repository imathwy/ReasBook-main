import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap03.Definition_3_3_3_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Exercise_3_3_3_6
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap08.Definition_8_8_3_2
import LinearRepresentations_Serre_1977.Serre.Chap08.Exercise_8_8_3_9
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap10.MonomialCharacter
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension

import LinearRepresentations_Serre_1977.Serre.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure

noncomputable section

namespace Representation

open CategoryTheory Rep
open scoped Representation SubgroupInduction
open scoped BigOperators Pointwise

section

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: choose a concrete
representative of a conjugacy class of `G`. -/
noncomputable def conjClassRepresentative (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective c)

omit [Finite G] in
/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: the chosen representative
realizes its conjugacy class. -/
theorem conjClassRepresentative_mk (c : ConjClasses G) :
    ConjClasses.mk (conjClassRepresentative c) = c :=
  Classical.choose_spec (ConjClasses.mk_surjective c)

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_brauer_pregular_fintype_of_finite : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_brauer_pregular_subgroup_fintype_of_finite (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: a finite group admits a finite
complete family of pairwise nonisomorphic irreducible complex representations. -/
theorem exists_complete_pairwise_nonisomorphic_irreducible_family_local :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
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
    -- Every quotient class has a chosen representative, so only finitely many classes appear.
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep ℂ G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot have isomorphic representatives.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((CategoryTheory.forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : CategoryTheory.Simple (π q) := by
    -- Each quotient-class representative is irreducible by construction.
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (π q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    -- Distinct quotient classes cannot label isomorphic regular summands.
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπ_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank ℂ (π q) := by
    -- Multiplicity of one irreducible class in the regular representation equals its degree.
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
    -- All regular summands in one quotient class have the same degree.
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
    -- Every irreducible regular summand lies in the class determined by its own label.
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
    -- Summing the dimensions of the internal decomposition recovers the regular dimension.
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
                  (Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule))
      _ = Nat.card G := by
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
  have hπ_sum : ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = Nat.card G := by
    -- The quotient classes partition the regular summands, so the square-degree sum is `|G|`.
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
    -- The square-degree criterion upgrades the quotient family to completeness.
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: restricting an integral
character of `G` to a subgroup still lands in that subgroup's integral character ring. -/
theorem restrict_mem_characterRing_preBrauer (H : Subgroup G) (χ : R(G)) :
    (fun h : H ↦ (χ : G → ℂ) h) ∈ R(H) := by
  let res : (G → ℂ) →ₐ[ℤ] (H → ℂ) :=
    { toFun := fun φ : G → ℂ ↦ fun h : H ↦ φ h
      map_zero' := rfl
      map_one' := rfl
      map_add' := by
        intro φ ψ
        ext h
        rfl
      map_mul' := by
        intro φ ψ
        ext h
        rfl
      commutes' := by
        intro n
        ext h
        rfl }
  -- Restriction is an algebra map, so it suffices to check it on honest-character generators.
  change res χ ∈ R(H)
  have hmap_le : R(G).map res ≤ R(H) := by
    refine (Subalgebra.gc_map_comap res).l_le ?_
    rw [Representation.characterRingOverField]
    refine (Algebra.adjoin_le_iff).2 ?_
    intro ψ hψ
    rcases hψ with ⟨ρ, hfd, hirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hfd
    -- Restricting a representation restricts its character pointwise.
    change res (ρ.ρ.character) ∈ R(H)
    simpa [res] using
      (Representation.rep_character_mem_characterRingOverField (K := ℂ)
        (ρ := Rep.res H.subtype ρ))
  exact hmap_le ⟨χ, χ.property, rfl⟩

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: multiplying an induced class
function by an ambient integral character is the same as inducing the restricted product. -/
theorem induced_mul_eq_induced_mul_restriction_preBrauer
    (H : Subgroup G) (ψ : H → ℂ) (χ : R(G)) :
    Ind[H](ψ) * (χ : G → ℂ) = Ind[H](fun h : H ↦ ψ h * χ h) := by
  classical
  -- Compare the induction formula term-by-term after restricting the ambient character.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * x * s ∈ H
  · have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hχ :
        (χ : G → ℂ) (s⁻¹ * x * s) = (χ : G → ℂ) x := by
      exact (Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ)
        (χ : G → ℂ) χ.property).eq_of_isConj <| isConj_iff.2 ⟨s, by group⟩
    have hχ' : (χ : G → ℂ) (s⁻¹ * (x * s)) = (χ : G → ℂ) x := by
      simpa [mul_assoc] using hχ
    simp [hs', hχ', mul_comm, mul_assoc]
  · simp [hs]

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: Brauer's subgroup `V_p` is
stable under multiplication by an arbitrary integral character of `G`. -/
theorem mul_mem_pElementaryInducedCharacterSpan_local (p : ℕ) {χ ψ : R(G)}
    (hψ : ψ ∈ V[p](G)) :
    χ * ψ ∈ V[p](G) := by
  classical
  let _ : DecidablePred (fun H : Subgroup G ↦ IsPElementary p H) := Classical.decPred _
  -- Check the stability first on subgroup-induced generators, then extend by `iSup` induction.
  rw [Representation.pElementaryInducedCharacterSpan] at hψ
  simp_rw [Representation.artinInducedCharacterSubmodule] at hψ
  refine Submodule.iSup_induction
      (p := fun H :
        {H : Subgroup G // H ∈ Finset.filter (fun H : Subgroup G ↦ IsPElementary p H) Finset.univ} ↦
          LinearMap.range (Subgroup.characterRingInduction H.1))
      (motive := fun ξ : R(G) ↦ χ * ξ ∈ V[p](G))
      hψ ?_ ?_ ?_
  · intro H ξ hξ
    rcases H with ⟨H, hHmem⟩
    rcases hξ with ⟨η, rfl⟩
    have hprod : (fun h : H ↦ ((η : H → ℂ) h) * ((χ : G → ℂ) h)) ∈ R(H) := by
      exact (R(H)).mul_mem η.property (restrict_mem_characterRing_preBrauer H χ)
    let ζ : R(H) := ⟨fun h : H ↦ ((η : H → ℂ) h) * ((χ : G → ℂ) h), hprod⟩
    have hζ :
        χ * Subgroup.characterRingInduction H η =
          Subgroup.characterRingInduction H ζ := by
      -- Rewrite the product on characters, then repack it into the induced character owner.
      apply Subtype.ext
      ext g
      have hind :=
        congrFun (induced_mul_eq_induced_mul_restriction_preBrauer H (η : H → ℂ) χ) g
      simpa [ζ, Subgroup.characterRingInduction_apply, mul_comm] using hind
    exact hζ ▸
      Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hHmem ζ
  · simpa using Submodule.zero_mem (V[p](G))
  · intro ξ η hξ hη
    simpa [mul_add] using Submodule.add_mem (V[p](G)) hξ hη

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: once a scalar multiple of the
trivial character lies in `V_p`, the same scalar multiple of every character also lies in `V_p`. -/
theorem smul_mem_pElementaryInducedCharacterSpan_of_scalar_mem_local
    (p : ℕ) (l : ℕ) (hscalar : l • (1 : R(G)) ∈ V[p](G)) (χ : R(G)) :
    l • χ ∈ V[p](G) := by
  -- Multiply the scalar witness by `χ` inside the character ring.
  have hmul :=
    mul_mem_pElementaryInducedCharacterSpan_local (G := G) (p := p)
      (χ := χ) (ψ := l • (1 : R(G))) hscalar
  simpa [mul_comm] using hmul

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: once a prime-to-`p` scalar
multiple of the trivial character lies in `V_p`, the additive quotient `R(G) / V_p` is finite and
its order is prime to `p`. -/
theorem finiteIndex_and_coprime_of_scalar_mem_pElementaryInducedCharacterSpan_local
    (p : Nat.Primes) (l : ℕ) (hl : Nat.Coprime p l)
    (hscalar : l • (1 : R(G)) ∈ V[p](G)) :
    (V[p](G)).toAddSubgroup.FiniteIndex ∧ Nat.Coprime p (V[p](G)).toAddSubgroup.index := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  -- Build a basis of `R(G)` from a complete irreducible family so the `nsmul`-index formula
  -- applies to the scalar witness.
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family_local (G := G)
  let b :=
    Representation.irreducible_characters_basis_of_complete_family
      ℂ π hπ_pairwise hπ_complete
  letI : Module.Free ℤ (R(G)) := Module.Free.of_basis b
  letI : Module.Finite ℤ (R(G)) := Module.Finite.of_basis b
  have hl_ne_zero : l ≠ 0 := by
    intro hl0
    have hp_one : (p : ℕ) = 1 := by
      simpa [hl0] using hl
    exact p.2.ne_one hp_one
  have hlmul : ∀ χ : R(G), l • χ ∈ V[p](G) := by
    intro χ
    -- The scalar witness propagates from `1` to all of `R(G)` by multiplicative stability.
    exact smul_mem_pElementaryInducedCharacterSpan_of_scalar_mem_local
      (G := G) (p := (p : ℕ)) l hscalar χ
  let L : AddSubgroup (R(G)) := (nsmulAddMonoidHom (α := R(G)) l).range
  have hL_le : L ≤ (V[p](G)).toAddSubgroup := by
    intro χ hχ
    rcases hχ with ⟨x, rfl⟩
    exact hlmul x
  have hL_index : L.index = l ^ Module.finrank ℤ (R(G)) := by
    simpa [L] using AddSubgroup.index_range_nsmul (M := R(G)) l
  have hL_finite : L.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff, hL_index]
    exact pow_ne_zero _ hl_ne_zero
  have hfinite : (V[p](G)).toAddSubgroup.FiniteIndex :=
    AddSubgroup.finiteIndex_of_le hL_le
  constructor
  · exact hfinite
  · have hdiv : (V[p](G)).toAddSubgroup.index ∣ l ^ Module.finrank ℤ (R(G)) := by
      letI : L.FiniteIndex := hL_finite
      exact (AddSubgroup.index_dvd_of_le hL_le).trans (dvd_of_eq hL_index)
    exact Nat.Coprime.of_dvd_right hdiv (hl.pow_right _)

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: once `V_p` has finite index,
the quotient cardinal annihilates every class in `R(G) / V_p`. -/
theorem quotient_card_smul_mem_pElementaryInducedCharacterSpan_of_finiteIndex_local
    (p : Nat.Primes)
    [hfinite : (V[p](G)).toAddSubgroup.FiniteIndex] (χ : R(G)) :
    Nat.card (R(G) ⧸ V[p](G)) • χ ∈ V[p](G) := by
  classical
  letI : Fintype (R(G) ⧸ V[p](G)) := AddSubgroup.fintypeQuotientOfFiniteIndex
  let m : ℕ := Nat.card (R(G) ⧸ V[p](G))
  let m' : ℕ := Fintype.card (R(G) ⧸ V[p](G))
  have hm : m = m' := by
    simp [m, m', Nat.card_eq_fintype_card]
  have hzero :
      m' • (Submodule.mkQ (V[p](G)) χ : R(G) ⧸ V[p](G)) = 0 := by
    -- Finite additive groups are annihilated by their cardinality.
    simpa [m'] using
      (card_nsmul_eq_zero
        (x := (Submodule.mkQ (V[p](G)) χ : R(G) ⧸ V[p](G))))
  have hmk_zero : Submodule.mkQ (V[p](G)) (m' • χ) = 0 := by
    -- Push the scalar action through the quotient map before reading membership upstairs.
    rw [map_nsmul]
    exact hzero
  have hmem' : m' • χ ∈ V[p](G) :=
    (Submodule.Quotient.mk_eq_zero (V[p](G))).1 hmk_zero
  simpa [m, m'] using hmem'

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: the normalized pairing of two
honest characters is the dimension of the intertwining space. -/
theorem groupFunctionPairing_character_eq_finrank_intertwiningMap_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) :
    ⟪σ.character, ρ.character⟫ = (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  -- This is the standard normalized character-pairing identity rewritten in the local notation.
  simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := σ) (σ := ρ))

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: pairing any integral virtual
character with an honest representation character gives an algebraic integer. -/
theorem characterRing_pairing_isIntegral_with_rep_character_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (η : R(G)) (ρ : Representation ℂ G V) :
    IsIntegral ℤ ⟪(η : G → ℂ), ρ.character⟫ := by
  let S : Set (G → ℂ) :=
    { ψ |
        ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
          (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
          ψ = σ.character }
  have hmul_span :
      ∀ {f g : G → ℂ},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hfg : ∀ g : G → ℂ, g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          change ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
            (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
            ψ = σ.character at hψ
          rcases hψ with ⟨W, _instWAdd, _instWMod, _instWfd, σ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              change ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X)
                (_ : FiniteDimensional ℂ X) (τ : Representation ℂ G X),
                ξ = τ.character at hξ
              rcases hξ with ⟨X, _instXAdd, _instXMod, _instXfd, τ, rfl⟩
              let π : Representation ℂ G (TensorProduct ℂ W X) := σ.tprod τ
              -- Tensor products realize pointwise products of honest characters.
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct ℂ W X, inferInstance, inferInstance, inferInstance, π, ?_⟩
              change σ.character * τ.character = (σ.tprod τ).character
              exact (Representation.char_tensor (ρ := σ) (σ := τ)).symm
          | zero =>
              have hzero_mul : σ.character * (0 : G → ℂ) = 0 := by
                ext x
                simp
              rw [hzero_mul]
              exact (Submodule.zero_mem (Submodule.span ℤ S))
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using
                Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              have hmul_zsmul : σ.character * (n • ξ) = n • (σ.character * ξ) := by
                ext x
                simp [zsmul_eq_mul, mul_left_comm]
              rw [hmul_zsmul]
              exact Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          have hzero_mul : (0 : G → ℂ) * g = 0 := by
            ext x
            simp
          rw [hzero_mul]
          exact (Submodule.zero_mem (Submodule.span ℤ S))
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  have hηspan : (η : G → ℂ) ∈ Submodule.span ℤ S := by
    -- The integral character ring is generated by honest characters, and that span is stable
    -- under multiplication by tensor-product closure.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ η.2
    · intro ψ hψ
      rcases hψ with ⟨σ, hσfd, _hσirr, rfl⟩
      exact Submodule.subset_span ⟨σ, inferInstance, inferInstance, hσfd, σ.ρ, rfl⟩
    · intro n
      have htriv :
          (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
        ext x
        simp [Representation.character, Representation.trivial]
      rw [show algebraMap ℤ (G → ℂ) n =
          n • (Representation.trivial ℂ G ℂ).character by
        ext x
        simp [htriv]]
      exact
        Submodule.smul_mem (Submodule.span ℤ S) n <|
          Submodule.subset_span
            ⟨ℂ, inferInstance, inferInstance, inferInstance,
              Representation.trivial ℂ G ℂ, rfl⟩
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  -- Evaluate the pairing on the honest-character spanning set.
  refine
    Submodule.span_induction
      (p := fun ψ _ ↦ IsIntegral ℤ ⟪ψ, ρ.character⟫)
      ?_ ?_ ?_ ?_ hηspan
  · intro ψ hψ
    change ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
      ψ = σ.character at hψ
    rcases hψ with ⟨W, _instWAdd, _instWMod, _instWfd, σ, rfl⟩
    -- For a genuine character, the pairing is the finite dimension of the intertwining space.
    rw [groupFunctionPairing_character_eq_finrank_intertwiningMap_local (G := G) σ ρ]
    exact isIntegral_algebraMap
  · -- The pairing with the zero class function is zero.
    simpa [Representation.groupFunctionPairingOverField] using
      (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  · intro ψ ξ _ _ hψ hξ
    simpa [Representation.groupFunctionPairing_add_left] using hψ.add hξ
  · intro n ψ _ hψ
    rw [show ⟪n • ψ, ρ.character⟫ = (n : ℂ) * ⟪ψ, ρ.character⟫ by
      simpa [zsmul_eq_mul] using
        (Representation.groupFunctionPairing_smul_left
          (a := (n : ℂ)) (φ := ψ) (ψ := ρ.character))]
    exact (isIntegral_algebraMap : IsIntegral ℤ (n : ℂ)).mul hψ

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: when `|G| = p^n l` with
`(p, l) = 1`, an element is `p`-regular exactly when its `l`th power is `1`. -/
theorem isPRegular_iff_pow_primeToPart_eq_one_local
    (p : Nat.Primes) (n l : ℕ) (hcard : Nat.card G = (p : ℕ) ^ n * l)
    (hl : Nat.Coprime p l) {s : G} :
    IsPRegular (p : ℕ) s ↔ s ^ l = 1 := by
  -- Route correction: consume the canonical earlier Chapter 10 arithmetic normalization rather
  -- than duplicating the proof in this bridge file.
  simpa using
    Representation.isPRegular_iff_pow_primeToPart_eq_one
      (G := G) p n l hcard hl (s := s)

-- NOTE (falsification record): the former helpers `pregular_indicator_mem_characterRing_local`
-- and `pregular_indicator_eq_one_local` were deleted: the underlying statement (the indicator of
-- the `p`-regular locus is a virtual character) was PROVEN FALSE in
-- `Representation.Brauer18.pregular_indicator_not_mem_characterRing`
-- (`Serre.Chap10.Theorem_10_10_2_1.PRegularEndgame`). Neither helper had any consumer; the
-- index-coprimality route now goes through Serre's Theorem 18'
-- (`Brauer18.const_primeToPart_mem_ownerSpan`).

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: if `(m : ℂ) / d` is integral
and `d ≠ 0`, then `d` divides `m`. -/
theorem nat_dvd_of_isIntegral_natCast_div_local
    {m d : ℕ} (hd : d ≠ 0) (h : IsIntegral ℤ ((m : ℂ) / d)) :
    d ∣ m := by
  let q : ℚ := m / d
  have hq : IsIntegral ℤ q := by
    have hqC : IsIntegral ℤ (q : ℂ) := by
      simpa [q] using h
    exact IsIntegral.ratCast_iff.mp hqC
  obtain ⟨z, hz : q = z⟩ := hq.exists_int_iff_exists_rat |>.mp ⟨q, rfl⟩
  have hden : q.den = 1 := by
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m d hd).mp <| by
    simpa [q] using hden


/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: the local scalar-extension
owner uses the algebraic integers inside `ℂ`. -/
abbrev pElementaryScalarExtensionRing_local : Type :=
  ↥(integralClosure ℤ ℂ)

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: the ambient inclusion of the
local Brauer owner `V[p](G)` into complex-valued class functions on `G`. -/
abbrev pElementaryInducedCharacterToFunction_local
    (p : ℕ) :
    V[p](G) →ₗ[ℤ] G → ℂ :=
  ((R(G)).toSubmodule.subtype).comp (V[p](G)).subtype

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: any character already in the
local Brauer owner contributes a generator to its scalar extension. -/
theorem mem_pElementaryInducedCharacterScalarExtension_of_mem_pElementary_local
    (p : ℕ) {χ : R(G)} (hχ : χ ∈ V[p](G)) :
    let W : Submodule pElementaryScalarExtensionRing_local (G → ℂ) :=
      Submodule.span pElementaryScalarExtensionRing_local
        { φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) }
    (χ : G → ℂ) ∈ W := by
  let W : Submodule pElementaryScalarExtensionRing_local (G → ℂ) :=
    Submodule.span pElementaryScalarExtensionRing_local
      { φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) }
  -- The scalar extension is the span of the image of `V[p](G)`, so a generator enters directly.
  change (χ : G → ℂ) ∈ W
  exact Submodule.subset_span ⟨⟨χ, hχ⟩, rfl⟩

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: inducing an integral character
from a `p`-elementary subgroup lands in the local Brauer owner `V[p](G)`. -/
theorem characterRingInduction_mem_pElementaryInducedCharacterSpan_local
    (p : ℕ) (H : Subgroup G) (hH : IsPElementary p H) (χ : R(H)) :
    Representation.Subgroup.characterRingInduction H χ ∈ V[p](G) := by
  classical
  -- Rewrite `V[p](G)` to the filtered induction span and insert the subgroup generator directly.
  rw [Representation.pElementaryInducedCharacterSpan]
  let _ : DecidablePred (fun K : Subgroup G ↦ IsPElementary p K) := Classical.decPred _
  have hHmem :
      H ∈ Finset.univ.filter (fun K : Subgroup G ↦ IsPElementary p K) := by
    simp [hH]
  exact
    Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hHmem χ

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: the subgroup induction map
codrestricts to the local Brauer owner when the source subgroup is `p`-elementary. -/
abbrev characterRingInductionToPElementary_local
    (p : ℕ) (H : Subgroup G) (hH : IsPElementary p H) :
    R(H) →ₗ[ℤ] V[p](G) :=
  LinearMap.codRestrict (V[p](G))
    (Representation.Subgroup.characterRingInduction H)
    (fun χ ↦
      characterRingInduction_mem_pElementaryInducedCharacterSpan_local
        (G := G) p H hH χ)

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: tensor induction from a
`p`-elementary subgroup lands in the realized local scalar extension of `V[p](G)`. -/
theorem induced_tensor_character_mem_pElementary_scalarExtension_local
    (p : ℕ) (H : Subgroup G) (hH : IsPElementary p H)
    (ψ : pElementaryScalarExtensionRing_local ⊗R(H)) :
    let W : Submodule pElementaryScalarExtensionRing_local (G → ℂ) :=
      Submodule.span pElementaryScalarExtensionRing_local
        { φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) }
    Ind[H]((ψ : H → ℂ)) ∈ W := by
  classical
  let W : Submodule pElementaryScalarExtensionRing_local (G → ℂ) :=
    Submodule.span pElementaryScalarExtensionRing_local
      { φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) }
  change Ind[H]((ψ : H → ℂ)) ∈ W
  induction ψ using TensorProduct.induction_on with
  | zero =>
      have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext g
        simp [Subgroup.inducedClassFunction]
      -- The scalar extension is a submodule, so it contains the zero function.
      simpa [hzero] using (Submodule.zero_mem W : (0 : G → ℂ) ∈ W)
  | tmul a χ =>
      have hbase :
          Ind[H]((χ : H → ℂ)) ∈ W := by
        -- The honest induced character already lies in `V[p](G)`, hence in its scalar span.
        exact
          mem_pElementaryInducedCharacterScalarExtension_of_mem_pElementary_local p
            (characterRingInduction_mem_pElementaryInducedCharacterSpan_local
              (G := G) p H hH χ)
      have hsmul :
          Ind[H](a • (χ : H → ℂ)) =
            a • Ind[H]((χ : H → ℂ)) := by
        -- Induction is linear in the induced class function.
        ext g
        simp [Subgroup.inducedClassFunction, Finset.sum_mul, Finset.mul_sum,
          Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
      -- On pure tensors, induction commutes with scalar multiplication by algebraic integers.
      simpa [Representation.Subgroup.characterRingInduction_apply, hsmul] using
        W.smul_mem a hbase
  | add ψ₁ ψ₂ hψ₁ hψ₂ =>
      have hadd :
          Ind[H](((ψ₁ : H → ℂ) + (ψ₂ : H → ℂ))) =
            (Ind[H]((ψ₁ : H → ℂ)) : G → ℂ) + Ind[H]((ψ₂ : H → ℂ)) := by
        -- Induction is additive in the induced class function.
        ext g
        exact congrFun
          ((((classFunctionSubmodule ℂ G).subtype.comp H.classFunctionInduction).map_add
              (ψ₁ : H → ℂ) (ψ₂ : H → ℂ))) g
      -- The scalar extension is closed under addition once the induced sum is rewritten.
      rw [map_add, hadd]
      exact W.add_mem hψ₁ hψ₂

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: the algebraic integers in `ℂ`
are faithfully flat over `ℤ`, specialized to the local scalar-extension owner used in this file. -/
lemma integral_closure_faithfullyFlat_over_int_local :
    Module.FaithfullyFlat ℤ pElementaryScalarExtensionRing_local := by
  let A := pElementaryScalarExtensionRing_local
  let f := algebraMap A ℂ
  have hAC : Function.Injective f := IsIntegralClosure.algebraMap_injective A ℤ ℂ
  letI : IsDomain A := Function.Injective.isDomain f hAC
  have hZA : Function.Injective (algebraMap ℤ A) := by
    -- Compose `ℤ → A` with `A → ℂ` to reflect injectivity from the characteristic-zero field.
    intro m n hmn
    have hmn' := congrArg f hmn
    rw [← IsScalarTower.algebraMap_apply ℤ A ℂ m, ← IsScalarTower.algebraMap_apply ℤ A ℂ n] at hmn'
    exact Int.cast_injective hmn'
  letI : Module.IsTorsionFree ℤ A :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 hZA
  haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ ℂ
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap ℤ A)) := by
    -- Integral extensions are surjective on prime spectra, so torsion-free flatness upgrades to
    -- faithful flatness.
    exact Algebra.IsIntegral.comap_surjective ℤ A
  exact Module.FaithfullyFlat.of_comap_surjective hsurj

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: the current local generator
description of the scalar-extension span is exactly the range of the inclusion
`V[p](G) → G → ℂ`. -/
theorem mem_range_pElementaryInducedCharacterToFunction_local_iff
    (p : ℕ) {φ : G → ℂ} :
    φ ∈ (LinearMap.range (pElementaryInducedCharacterToFunction_local (G := G) p) :
        Set (G → ℂ)) ↔
      ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) := by
  constructor
  · rintro ⟨β, rfl⟩
    exact ⟨β, rfl⟩
  · rintro ⟨β, rfl⟩
    exact ⟨β, rfl⟩

/-- Helper for character_mem_iSup_pElementaryInducedCharacterSpan: the local span presentation
can be rewritten using the actual `LinearMap.range` of the inclusion `V[p](G) → G → ℂ`. -/
theorem pElementaryInducedCharacterSpan_generators_eq_range_span_local
    (p : ℕ) :
    Submodule.span pElementaryScalarExtensionRing_local
      { φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) } =
    Submodule.span pElementaryScalarExtensionRing_local
      ((LinearMap.range (pElementaryInducedCharacterToFunction_local (G := G) p)) :
        Set (G → ℂ)) := by
  congr
  ext φ
  constructor
  · exact (mem_range_pElementaryInducedCharacterToFunction_local_iff (G := G) (p := p)).mpr
  · exact (mem_range_pElementaryInducedCharacterToFunction_local_iff (G := G) (p := p)).mp
end

end Representation
