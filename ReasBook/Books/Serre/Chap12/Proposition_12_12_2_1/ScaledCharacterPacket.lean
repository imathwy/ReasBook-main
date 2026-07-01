import Serre.Chap03.Theorem_3_3_2_1
import Serre.Chap12.Proposition_12_12_2_1.ScaledCharacterCore

noncomputable section

open scoped Representation

universe u v

namespace Representation

open CategoryTheory

section

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeScaledCharacterGroupPacket : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 12-12.2-1: the normalized pairing is additive on finite
`AlgebraicClosure K`-linear combinations in its left argument. -/
theorem groupFunctionPairing_sum_field_smul_left
    {ι : Type u} (s : Finset ι) (a : ι → AlgebraicClosure K) (χ : ι → G → AlgebraicClosure K)
    (ψ : G → AlgebraicClosure K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, a j * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Proposition 12-12.2-1: coefficient extension to `AlgebraicClosure K` preserves the
normalized class-function pairing. -/
theorem groupFunctionPairing_compLeft_toAlgClosure
    (φ ψ : G → K) :
    ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) φ,
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ψ⟫ =
      algebraMap K (AlgebraicClosure K) ⟪φ, ψ⟫ := by
  simp [Representation.groupFunctionPairingOverField, map_mul]

/-- Helper for Proposition 12-12.2-1: scalar extension carries the source character to its
coefficientwise image in `AlgebraicClosure K`. -/
theorem scalarExtension_character_eq_map_fdRep_character
    (V : FDRep K G) :
    (Representation.scalarExtension (k := AlgebraicClosure K) V.ρ).character =
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character := by
  ext g
  exact LinearMap.trace_baseChange (V.ρ g) (AlgebraicClosure K)

/-- Helper for Proposition 12-12.2-1: the character of an internal direct sum is the sum of the
constituent characters. -/
theorem character_eq_sum_of_internal_family
    {L : Type u} [Field L]
    {V : Type u} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ρ : Representation L G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i, ((σ i).toRepresentation).character := by
  -- Decompose the trace along the chosen internal direct-sum decomposition.
  ext g
  simpa [Representation.character] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := L) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
      (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))

/-- Helper for Proposition 12-12.2-1: after scalar extension to `AlgebraicClosure K`, a simple
`K`-representation admits a packet decomposition into pairwise nonisomorphic irreducibles with
natural multiplicities. -/
theorem scalar_extension_character_eq_sum_irreducible_family_with_nat_coefficients
    (V : FDRep K G) :
    ∃ (ι : Type u) (_ : Fintype ι) (ψ : ι → Rep.{u} (AlgebraicClosure K) G) (d : ι → ℕ),
      (∀ i, 0 < d i) ∧
      (∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i)) ∧
      PairwiseNonisomorphic ψ ∧
      (∀ i, (ψ i).ρ.IsIrreducible) ∧
      (Representation.scalarExtension (k := AlgebraicClosure K) V.ρ).character =
        ∑ i, (d i : AlgebraicClosure K) • (ψ i).ρ.character := by
  classical
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : AlgebraicClosure K) := ⟨hcard_ne⟩
  let τ : Representation (AlgebraicClosure K) G
      (TensorProduct K (AlgebraicClosure K) V) :=
    Representation.scalarExtension (k := AlgebraicClosure K) V.ρ
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := τ)
  let hinternal : DirectSum.IsInternal (fun i : κ ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty (((σ i).toRepresentation).Equiv ((σ j).toRepresentation))
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j k} hij hjk ↦ by
            rcases hij with ⟨eij⟩
            rcases hjk with ⟨ejk⟩
            exact ⟨eij.trans ejk⟩⟩ }
  let ι : Type u := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : Quotient r)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let ψ : ι → Rep.{u} (AlgebraicClosure K) G :=
    fun q ↦ Rep.of ((σ (Quotient.out q)).toRepresentation)
  have hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i) := by
    intro i
    letI : (ψ i).ρ.IsIrreducible := by
      simpa [ψ] using hσ_irr (Quotient.out i)
    exact Representation.IsIrreducible.finiteDimensional_of_finite (ρ := (ψ i).ρ)
  have hψ_pairwise : PairwiseNonisomorphic ψ := by
    intro q q' hqq' hIso
    have hclasses :
        (⟦Quotient.out q⟧ : ι) = ⟦Quotient.out q'⟧ := by
      apply Quotient.sound
      rcases hIso with ⟨e⟩
      exact ⟨Representation.equivOfIso (by simpa [ψ] using e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = ⟦Quotient.out q'⟧ := hclasses
      _ = q' := Quotient.out_eq q'
  have hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible := by
    intro i
    simpa [ψ] using hσ_irr (Quotient.out i)
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦
      Nonempty (((σ j).toRepresentation).Equiv (ψ i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let d : ι → ℕ := fun i ↦ (S i).card
  have hd_pos : ∀ i, 0 < d i := by
    intro i
    dsimp [d]
    refine Finset.card_pos.mpr ?_
    refine ⟨Quotient.out i, ?_⟩
    exact Finset.mem_filter.mpr ⟨by simp, by simpa [ψ] using
      (show Nonempty (((σ (Quotient.out i)).toRepresentation).Equiv
        ((σ (Quotient.out i)).toRepresentation)) from
        ⟨Representation.Equiv.refl _⟩)⟩
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    have hclasses :
        (⟦Quotient.out i⟧ : ι) = ⟦Quotient.out i'⟧ := by
      apply Quotient.sound
      exact ⟨e.symm.trans e'⟩
    apply hii
    calc
      i = (⟦Quotient.out i⟧ : ι) := (Quotient.out_eq i).symm
      _ = ⟦Quotient.out i'⟧ := hclasses
      _ = i' := Quotient.out_eq i'
  have hcovered_univ : covered = Finset.univ := by
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨(⟦j⟧ : ι), by simp, ?_⟩
      have hclass :
          Nonempty (((σ j).toRepresentation).Equiv
            ((σ (Quotient.out (⟦j⟧ : ι))).toRepresentation)) := by
        exact Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)).symm
      exact Finset.mem_filter.mpr ⟨by simp, by simpa [ψ] using hclass⟩
  have hcovered_raw (g : G) :
      Finset.sum covered (fun j ↦ ((σ j).toRepresentation).character g) =
        ∑ i : ι, Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  refine ⟨ι, inferInstance, ψ, d, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, ?_⟩
  -- Regroup the irreducible summands of the scalar extension by isomorphism class.
  ext g
  have hsum_sigma :
      τ.character g = ∑ j : κ, ((σ j).toRepresentation).character g := by
    simpa [τ] using
      congrArg (fun χ : G → AlgebraicClosure K ↦ χ g)
        (character_eq_sum_of_internal_family (ρ := τ) σ hinternal)
  have hS_sum (i : ι) :
      Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) =
        (d i : AlgebraicClosure K) * (ψ i).ρ.character g := by
    calc
      Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) =
          Finset.sum (S i) (fun _j ↦ (ψ i).ρ.character g) := by
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
            simpa using congrArg (fun χ : G → AlgebraicClosure K ↦ χ g) (Representation.char_iso e)
      _ = (S i).card * (ψ i).ρ.character g := by
            simp
      _ = (d i : AlgebraicClosure K) * (ψ i).ρ.character g := by
            simp [d]
  calc
    τ.character g = ∑ j : κ, ((σ j).toRepresentation).character g := hsum_sigma
    _ = Finset.sum covered (fun j ↦ ((σ j).toRepresentation).character g) := by
          simpa [covered, hcovered_univ]
    _ = ∑ i : ι, Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) :=
          hcovered_raw g
    _ = ∑ i : ι, (d i : AlgebraicClosure K) * (ψ i).ρ.character g := by
          refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
    _ = (∑ i, (d i : AlgebraicClosure K) • (ψ i).ρ.character) g := by
          simp [smul_eq_mul]

/-- Helper for Proposition 12-12.2-1: an irreducible `AlgebraicClosure K`-character has
normalized self-pairing equal to `1`. -/
theorem irreducible_character_self_pairing_eq_one
    {V : Type u} [AddCommGroup V] [Module (AlgebraicClosure K) V]
    (ρ : Representation (AlgebraicClosure K) G V)
    [FiniteDimensional (AlgebraicClosure K) V] [ρ.IsIrreducible] :
    ⟪ρ.character, ρ.character⟫ = (1 : AlgebraicClosure K) := by
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K) := invertibleOfNonzero hcard_ne
  -- Over an algebraically closed field, Schur's lemma makes the endomorphism space
  -- one-dimensional.
  have hfinrank :
      Module.finrank (AlgebraicClosure K) (ρ.IntertwiningMap ρ) = 1 := by
    simpa using
      (finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
        (ρ := ρ) inferInstance (τ := ρ) inferInstance)
  calc
    ⟪ρ.character, ρ.character⟫
        = Module.finrank (AlgebraicClosure K) (ρ.IntertwiningMap ρ) := by
            simpa using
              (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                (K := AlgebraicClosure K) (G := G) ρ ρ)
    _ = 1 := by simpa using hfinrank

/-- Helper for Proposition 12-12.2-1: pairing the scalar-extension packet of an irreducible
`K`-representation against one packet constituent recovers its multiplicity. -/
theorem packet_constituent_pairing_eq_multiplicity
    {ι : Type u} [Fintype ι]
    (V : FDRep K G)
    (ψ : ι → Rep.{u} (AlgebraicClosure K) G)
    (d : ι → ℕ)
    (hψ_fd : ∀ j, FiniteDimensional (AlgebraicClosure K) (ψ j))
    (hψ_pairwise : PairwiseNonisomorphic ψ)
    (hψ_irr : ∀ j, (ψ j).ρ.IsIrreducible)
    (hpacket :
      (Representation.scalarExtension (k := AlgebraicClosure K) V.ρ).character =
        ∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character) :
    ∀ j,
      ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character,
        (ψ j).ρ.character⟫ = (d j : AlgebraicClosure K) := by
  intro j
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K) := invertibleOfNonzero hcard_ne
  letI : FiniteDimensional (AlgebraicClosure K) (ψ j) := hψ_fd j
  letI : (ψ j).ρ.IsIrreducible := hψ_irr j
  -- Pair the packet decomposition with the `j`-th constituent and use packet orthogonality.
  calc
    ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character,
        (ψ j).ρ.character⟫
        =
          ⟪(Representation.scalarExtension (k := AlgebraicClosure K) V.ρ).character,
            (ψ j).ρ.character⟫ := by
              rw [scalarExtension_character_eq_map_fdRep_character]
    _ = ⟪∑ l, (d l : AlgebraicClosure K) • (ψ l).ρ.character, (ψ j).ρ.character⟫ := by
          rw [hpacket]
    _ = ∑ l, (d l : AlgebraicClosure K) * ⟪(ψ l).ρ.character, (ψ j).ρ.character⟫ := by
          simpa using
            groupFunctionPairing_sum_field_smul_left
              (K := K) (G := G) (s := Finset.univ)
              (a := fun l ↦ (d l : AlgebraicClosure K))
              (χ := fun l ↦ (ψ l).ρ.character) ((ψ j).ρ.character)
    _ = (d j : AlgebraicClosure K) * ⟪(ψ j).ρ.character, (ψ j).ρ.character⟫ := by
          refine Finset.sum_eq_single j ?_ ?_
          · intro l _ hlj
            letI : FiniteDimensional (AlgebraicClosure K) (ψ l) := hψ_fd l
            letI : (ψ l).ρ.IsIrreducible := hψ_irr l
            have hnot :
                ¬ Nonempty ((ψ l).ρ.Equiv (ψ j).ρ) := by
              intro hIso
              apply hψ_pairwise hlj
              rcases hIso with ⟨e⟩
              simpa using
                (show Nonempty (ψ l ≅ ψ j) from
                  ⟨(forget₂ (FDRep (AlgebraicClosure K) G) (Rep (AlgebraicClosure K) G)).mapIso
                    (Representation.Equiv.toFDRepIso e)⟩)
            have hpair_zero :
                ⟪(ψ l).ρ.character, (ψ j).ρ.character⟫ = (0 : AlgebraicClosure K) := by
              exact
                Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
                  (K := AlgebraicClosure K) (G := G) (ρ := (ψ l).ρ) (σ := (ψ j).ρ) hnot
            rw [hpair_zero, mul_zero]
          · intro hj
            exact (hj (Finset.mem_univ j)).elim
    _ = d j := by
          rw [irreducible_character_self_pairing_eq_one (K := K) (G := G) (ρ := (ψ j).ρ)]
          simp

/-- Helper for Proposition 12-12.2-1: source-side orthogonality against one irreducible
character forces orthogonality against every constituent of its algebraic-closure packet. -/
theorem packet_constituent_pairing_zero_of_source_pairing_zero
    {ι : Type u} [Fintype ι]
    (V W : FDRep K G)
    (ψ : ι → Rep.{u} (AlgebraicClosure K) G)
    (d : ι → ℕ)
    (hψ_pos : ∀ j, 0 < d j)
    (hψ_fd : ∀ j, FiniteDimensional (AlgebraicClosure K) (ψ j))
    (hpacket :
      (Representation.scalarExtension (k := AlgebraicClosure K) V.ρ).character =
        ∑ j, (d j : AlgebraicClosure K) • (ψ j).ρ.character)
    (hpair_zero : ⟪W.character, V.character⟫ = (0 : K)) :
    ∀ j,
      ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character,
        (ψ j).ρ.character⟫ = (0 : AlgebraicClosure K) := by
  intro j
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K) := invertibleOfNonzero hcard_ne
  have hpair_finrank :
      ∀ l,
        ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character,
          (ψ l).ρ.character⟫ =
            (Module.finrank (AlgebraicClosure K)
              ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
                (ψ l).ρ) : AlgebraicClosure K) := by
    intro l
    letI : FiniteDimensional (AlgebraicClosure K) (ψ l) := hψ_fd l
    rw [← scalarExtension_character_eq_map_fdRep_character (K := K) (G := G) (V := W)]
    simpa using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := AlgebraicClosure K) (G := G)
        (Representation.scalarExtension (k := AlgebraicClosure K) W.ρ) (ψ l).ρ)
  have hsum_zero :
      ∑ l, (d l : AlgebraicClosure K) *
          ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character,
            (ψ l).ρ.character⟫ =
        (0 : AlgebraicClosure K) := by
    -- Pair the whole packet against the mapped source character and use source-side orthogonality.
    calc
      ∑ l, (d l : AlgebraicClosure K) *
          ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character,
            (ψ l).ρ.character⟫
          =
            ⟪∑ l, (d l : AlgebraicClosure K) • (ψ l).ρ.character,
              ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character⟫ := by
                rw [groupFunctionPairing_sum_field_smul_left
                  (K := K) (G := G) (s := Finset.univ)
                  (a := fun l ↦ (d l : AlgebraicClosure K))
                  (χ := fun l ↦ (ψ l).ρ.character)
                  (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                    W.character)]
                refine Finset.sum_congr rfl ?_
                intro l _
                rw [Representation.groupFunctionPairing_comm]
      _ =
          ⟪(Representation.scalarExtension (k := AlgebraicClosure K) V.ρ).character,
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character⟫ := by
              rw [hpacket]
      _ =
          ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character,
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character⟫ := by
              rw [scalarExtension_character_eq_map_fdRep_character]
      _ = algebraMap K (AlgebraicClosure K) ⟪V.character, W.character⟫ := by
            exact groupFunctionPairing_compLeft_toAlgClosure (K := K) (G := G) V.character
              W.character
      _ = 0 := by
            rw [Representation.groupFunctionPairing_comm, hpair_zero]
            simp
  have hsum_nat_zero :
      ∑ l,
        d l *
          Module.finrank (AlgebraicClosure K)
            ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
              (ψ l).ρ) = 0 := by
    letI : CharZero (AlgebraicClosure K) := inferInstance
    have hcast_zero :
        ((∑ l,
            d l *
              Module.finrank (AlgebraicClosure K)
                ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
                  (ψ l).ρ) : ℕ) : AlgebraicClosure K) = 0 := by
      calc
        ((∑ l,
            d l *
              Module.finrank (AlgebraicClosure K)
                ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
                  (ψ l).ρ) : ℕ) : AlgebraicClosure K)
            =
              ∑ l, (d l : AlgebraicClosure K) *
                ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character,
                  (ψ l).ρ.character⟫ := by
                    calc
                      ((∑ l,
                          d l *
                            Module.finrank (AlgebraicClosure K)
                              ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
                                (ψ l).ρ) : ℕ) : AlgebraicClosure K)
                          =
                            ∑ l,
                              ((d l *
                                Module.finrank (AlgebraicClosure K)
                                  ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
                                    (ψ l).ρ) : ℕ) : AlgebraicClosure K) := by
                                      simp
                      _ =
                          ∑ l, (d l : AlgebraicClosure K) *
                            (Module.finrank (AlgebraicClosure K)
                              ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
                                (ψ l).ρ) : AlgebraicClosure K) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro l _
                                  simp
                      _ =
                          ∑ l, (d l : AlgebraicClosure K) *
                            ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                                W.character, (ψ l).ρ.character⟫ := by
                                  refine Finset.sum_congr rfl ?_
                                  intro l _
                                  rw [hpair_finrank l]
        _ = 0 := hsum_zero
    exact Nat.cast_eq_zero.mp hcast_zero
  have hterm_zero :
      d j *
          Module.finrank (AlgebraicClosure K)
            ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
              (ψ j).ρ) = 0 := by
    have hsum_eq_zero_iff :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun l _ ↦ Nat.zero_le
          (d l *
            Module.finrank (AlgebraicClosure K)
              ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
                (ψ l).ρ)))).mp hsum_nat_zero
    exact hsum_eq_zero_iff j (Finset.mem_univ j)
  have hfinrank_zero :
      Module.finrank (AlgebraicClosure K)
        ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
          (ψ j).ρ) = 0 := by
    exact (Nat.mul_eq_zero.mp hterm_zero).resolve_left (Nat.ne_of_gt (hψ_pos j))
  letI : FiniteDimensional (AlgebraicClosure K) (ψ j) := hψ_fd j
  -- The pairing is the intertwining-space dimension, so zero finrank gives the desired vanishing.
  calc
    ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) W.character,
        (ψ j).ρ.character⟫
        =
          (Module.finrank (AlgebraicClosure K)
            ((Representation.scalarExtension (k := AlgebraicClosure K) W.ρ).IntertwiningMap
              (ψ j).ρ) : AlgebraicClosure K) := hpair_finrank j
    _ = 0 := by simp [hfinrank_zero]

end

end Representation
