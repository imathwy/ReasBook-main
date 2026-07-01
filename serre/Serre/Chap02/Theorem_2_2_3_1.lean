import Serre.Chap02.Remark_2_2_2_5
import Serre.Chap02.Corollary_2_2_2_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w u₁ u₂

namespace Representation

noncomputable section

section

open scoped Representation BigOperators MonoidAlgebra

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
variable {ι : Type u₁} [Fintype ι] [DecidableEq ι]
variable {κ : Type u₂} [Fintype κ] [DecidableEq κ]

local instance : Fintype G := Fintype.ofFinite G

local instance : Invertible (Nat.card G : ℂ) := by
  refine invertibleOfNonzero ?_
  exact_mod_cast Nat.card_pos.ne'

omit [Finite G] [FiniteDimensional ℂ V] in
/-- Helper for Theorem 2-2.3-1: a character is the sum of its diagonal matrix coefficients in any
finite basis. -/
lemma character_eq_sum_diagonal_matrix_coefficients
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V) :
    ρ.character = fun g ↦ ∑ i, (ρ g).toMatrix b b i i := by
  -- Rewrite the trace defining the character as the trace of the representing matrix.
  ext g
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp [Matrix.diag]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- Helper for Theorem 2-2.3-1: after expanding each character along a basis, the normalized
pairing becomes a double sum of pairings of diagonal matrix coefficients. -/
lemma pairing_eq_sum_diagonal_matrix_coefficient_pairings
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (bρ : Module.Basis ι ℂ V) (bσ : Module.Basis κ ℂ W) :
    ⟪ρ.character, σ.character⟫ =
      ∑ i, ∑ j,
        ⟪fun t ↦ (σ t).toMatrix bσ bσ j j, fun t ↦ (ρ t).toMatrix bρ bρ i i⟫ := by
  -- Commute the pairing so that the matrix-coefficient orthogonality theorem matches the index
  -- order used below.
  rw [groupFunctionPairing_comm]
  rw [character_eq_sum_diagonal_matrix_coefficients (ρ := σ) bσ]
  rw [character_eq_sum_diagonal_matrix_coefficients (ρ := ρ) bρ]
  simp_rw [groupFunctionPairingOverField]
  -- Expand the product of the two diagonal sums and reorder the three finite sums.
  calc
    (↑(Fintype.card G) : ℂ)⁻¹ *
        ∑ x : G, (∑ j, (σ x⁻¹).toMatrix bσ bσ j j) * ∑ i, (ρ x).toMatrix bρ bρ i i
      = (↑(Fintype.card G) : ℂ)⁻¹ *
          ∑ x : G, ∑ j, (σ x⁻¹).toMatrix bσ bσ j j * ∑ i, (ρ x).toMatrix bρ bρ i i := by
          simp_rw [Finset.sum_mul]
    _ = (↑(Fintype.card G) : ℂ)⁻¹ *
          ∑ x : G, ∑ j, ∑ i, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
          simp_rw [Finset.mul_sum]
    _ = (↑(Fintype.card G) : ℂ)⁻¹ *
          ∑ i, ∑ j, ∑ x : G, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
          congr 1
          have hxy :
              ∑ x : G, ∑ j, ∑ i, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i =
                ∑ j, ∑ x : G, ∑ i, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
            rw [Finset.sum_comm]
          have hyi :
              ∑ j, ∑ x : G, ∑ i, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i =
                ∑ j, ∑ i, ∑ x : G, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
          have hji :
              ∑ j, ∑ i, ∑ x : G, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i =
                ∑ i, ∑ j, ∑ x : G, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
            rw [Finset.sum_comm]
          exact hxy.trans (hyi.trans hji)
    _ = ∑ i, ∑ j,
          ((↑(Fintype.card G) : ℂ)⁻¹ *
            ∑ x : G,
              (fun t ↦ (σ t).toMatrix bσ bσ j j) x⁻¹ *
                (fun t ↦ (ρ t).toMatrix bρ bρ i i) x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ i, ∑ j,
          ⟪fun t ↦ (σ t).toMatrix bσ bσ j j, fun t ↦ (ρ t).toMatrix bρ bρ i i⟫ := by
          simp_rw [groupFunctionPairingOverField]

omit [FiniteDimensional ℂ V] in
/-- Helper for Theorem 2-2.3-1: the diagonal matrix coefficients of an irreducible representation
have pairing `(dim V)⁻¹` on the diagonal and `0` off the diagonal. -/
lemma diagonal_matrixCoefficient_pairing_of_irreducible
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V)
    (i j : Fin (Module.finrank ℂ V)) :
    ⟪fun t ↦ (ρ t).toMatrix b b j j, fun t ↦ (ρ t).toMatrix b b i i⟫ =
      if j = i then (Module.finrank ℂ V : ℂ)⁻¹ else 0 := by
  classical
  -- Specialize the matrix-coefficient orthogonality theorem to diagonal entries.
  by_cases hji : j = i
  · subst j
    convert
      (matrixCoefficient_pairing_of_irreducible
        (ρ := ρ) (b := b) (i1 := i) (j1 := i) (i2 := i) (j2 := i)) using 1
    · congr 1 <;> ext t <;> simp [LinearMap.toMatrix_apply]
    · simp
  · convert
      (matrixCoefficient_pairing_of_irreducible
        (ρ := ρ) (b := b) (i1 := i) (j1 := i) (i2 := j) (j2 := j)) using 1
    · congr 1 <;> ext t <;> simp [LinearMap.toMatrix_apply]
    · simp [hji]

/-- Helper for Theorem 2-2.3-1: in a `Fin n`-indexed sum, exactly one diagonal term contributes
to `∑ j, if j = i then c else 0`. -/
lemma fin_sum_diagonal_const (n : ℕ) (c : ℂ) (i : Fin n) :
    (∑ j : Fin n, (if j = i then c else 0)) = c := by
  -- Collapse the sum to the unique index where `j = i`.
  exact Fintype.sum_ite_eq' i (fun _ : Fin n => c)

/-- Helper for Theorem 2-2.3-1: summing the previous diagonal contribution over all `i : Fin n`
produces `n` copies of `c`. -/
lemma fin_double_sum_diagonal_const (n : ℕ) (c : ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, (if j = i then c else 0)) = (n : ℂ) * c := by
  -- First collapse each inner diagonal sum to a single copy of `c`.
  calc
    (∑ i : Fin n, ∑ j : Fin n, (if j = i then c else 0))
      = ∑ i : Fin n, c := by
          apply Finset.sum_congr rfl
          intro i _
          rw [fin_sum_diagonal_const (n := n) (c := c) (i := i)]
    _ = (n : ℂ) * c := by
          -- Then count how many outer indices remain.
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp

/-- Helper for Theorem 2-2.3-1: summing the diagonal matrix-coefficient pairings of an irreducible
representation leaves exactly one copy of `(dim V)⁻¹` for each diagonal index, so the total is
`1`. -/
lemma sum_diagonal_self_pairings_eq_one
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) :
    ∑ i, ∑ j,
      ⟪fun t ↦ (ρ t).toMatrix b b j j, fun t ↦ (ρ t).toMatrix b b i i⟫ = 1 := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  have hdim_ne_zero : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  -- Rewrite each summand by irreducible matrix-coefficient orthogonality.
  calc
    ∑ i, ∑ j,
        ⟪fun t ↦ (ρ t).toMatrix b b j j, fun t ↦ (ρ t).toMatrix b b i i⟫
      = ∑ i : Fin (Module.finrank ℂ V), ∑ j : Fin (Module.finrank ℂ V),
          if j = i then (Module.finrank ℂ V : ℂ)⁻¹ else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [diagonal_matrixCoefficient_pairing_of_irreducible (ρ := ρ) (b := b) (i := i)
              (j := j)]
    _ = (Module.finrank ℂ V : ℂ) * (Module.finrank ℂ V : ℂ)⁻¹ := by
          rw [fin_double_sum_diagonal_const]
    _ = 1 := by
          exact mul_inv_cancel₀ hdim_ne_zero

-- Route correction: replace the later Chapter 12 shortcut by Serre's Chapter 2 proof skeleton,
-- namely character expansion into diagonal matrix coefficients followed by orthogonality.
/-- Theorem 2-2.3-1 (1): clause (i). The normalized scalar product of the character of an
irreducible complex representation with itself is `1`. -/
theorem self_character_pairing_eq_one_of_irreducible
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ⟪ρ.character, ρ.character⟫ = 1 := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  have hexpand :
      ⟪ρ.character, ρ.character⟫ =
        ∑ i, ∑ j,
          ⟪fun t ↦ (ρ t).toMatrix b b j j, fun t ↦ (ρ t).toMatrix b b i i⟫ :=
    pairing_eq_sum_diagonal_matrix_coefficient_pairings (ρ := ρ) (σ := ρ) b b
  -- Expand the character pairing into diagonal matrix-coefficient pairings.
  calc
    ⟪ρ.character, ρ.character⟫
      = ∑ i, ∑ j,
          ⟪fun t ↦ (ρ t).toMatrix b b j j, fun t ↦ (ρ t).toMatrix b b i i⟫ := hexpand
    _ = 1 := sum_diagonal_self_pairings_eq_one (ρ := ρ) b

/-- Source-facing clause (ii) of Theorem 2-2.3-1: characters of nonisomorphic irreducible complex
representations are orthogonal for Serre's normalized pairing. -/
theorem character_pairing_eq_zero_of_not_isomorphic_irreducible
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] (hρσ : ¬ Nonempty (ρ.Equiv σ)) :
    ⟪ρ.character, σ.character⟫ = 0 := by
  classical
  let _ : DecidableEq (Fin (Module.finrank ℂ V)) := Classical.decEq _
  let _ : DecidableEq (Fin (Module.finrank ℂ W)) := Classical.decEq _
  let bρ : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let bσ : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W := Module.finBasis ℂ W
  have hexpand :
      ⟪ρ.character, σ.character⟫ =
        ∑ i, ∑ j,
          ⟪fun t ↦ (σ t).toMatrix bσ bσ j j, fun t ↦ (ρ t).toMatrix bρ bρ i i⟫ :=
    pairing_eq_sum_diagonal_matrix_coefficient_pairings (ρ := ρ) (σ := σ) bρ bσ
  -- Expand the pairing and annihilate each summand by the nonisomorphic orthogonality theorem.
  calc
    ⟪ρ.character, σ.character⟫
      = ∑ i, ∑ j,
          ⟪fun t ↦ (σ t).toMatrix bσ bσ j j, fun t ↦ (ρ t).toMatrix bρ bρ i i⟫ := hexpand
    _ = ∑ i, ∑ j, (0 : ℂ) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          have hterm :=
            matrix_coefficient_orthogonality_of_not_isomorphic
              (ρ1 := ρ) (ρ2 := σ) hρσ bρ bσ i i j j
          simpa [groupFunctionPairingOverField, Nat.card_eq_fintype_card] using hterm
    _ = 0 := by
          simp

end

end

end Representation
