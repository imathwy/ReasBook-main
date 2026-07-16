import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import ReasLib.NumericalAlgebra.Defs
import Mathlib.Logic.Nontrivial.Basic
import ReasLib.NumericalAlgebra.Direct.SVD
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import ReasLib.NumericalAlgebra.Basics.Norms
import ReasLib.NumericalAlgebra.Basics.Orthogonality
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option linter.unusedSectionVars false

namespace  Matrix

section von_neumann

namespace von_neumann
open FiniteDimensional LinearMap Module

/-
The final goal of this section is to prove the `von Neumann trace inequality`:
    ''let A and B be any two n x n complex matrices,
      and let σᵢ(A) and σᵢ(B) be their singular values,
      arranged in descending order σ₁(A) ≥ σ₂(A) ≥ ... ≥ σ_n(A) and σ₁(B) ≥ σ₂(B) ≥ ... ≥ σ_n(B),
      then we have ‖tr(A * B)‖ ≤ ∑ᵢ σ(A)ᵢ · σ(B)ᵢ''

In the proof process, we supplemented some theories regarding doubly sub-stochastic matrices
and doubly stochastic matrices.

### Definitions
  1. Define the `singular values` of a square matrix
  2. Define a `doubly substochastic` matrix
  3. Let` T A ` denote  the number of rows and columns of A whose sums are less than 1

### Main Theorem
-  Some theorems regarding doubly sub-stochastic matrices and doubly stochastic matrices
    1.the lemma `DoublySubStochastic_eq_T_0 `says " If A is a doubly sub-stochastic matrix ,
      then A is a doubly stochastic matrix if and only if T A = 0
    2.the lemma `DoublySubStochastic_improvement `says " If A is a doubly sub-stochastic matrix
      with T A > 0, then there exists a doubly sub-stochastic matrix C such that A i j ≤ C i j
      for all i, j ; and T C < T A".
    3.the private theorem `exists_doubly_stochastic_above_substochastic` says "For any doubly
      sub-stochastic matrix A, there exists a doubly stochastic matrix B such that A i j ≤ B i j
      for all i, j".
    4.the lemma `convex_doublyStochastic`says the set of doubly stochastic matrices is a convex set
        This result is already available in Mathlib
    5.the lemma `Iscompact_doublyStochastic`says the set of doubly stochastic matrices is
      a compact set
    6.the lemma `extremePoints_doublyStochastic`says "The extreme points of the set of doubly
      stochastic matrices are exactly the permutation matrices"
      This result is already available in Mathlib

- other lemmas used in the proof of von Neumann trace inequality
    1.the lemma `cauchy_schwarz_real ` for real-valued finite sequences
    2.the lemma `trace_unitary_similarity` says " For any square matrix A and any unitary matrix U,
      we have tr(U * A * Uᴴ) = tr(A) "
    3.the lemma `conjTranspose_unitary` says " The conjugate transpose of a unitary matrix is also
      a unitary matrix "
    4.the lemma `mul_unitary` says " The product of two unitary matrices is also a unitary matrix "
    5.the lemma `unitary_col_norm` says " Each column of a unitary matrix has norm 1 "
    6.the lemma `unitary_row_norm` says " Each row of a unitary matrix has norm 1 "
    7.the lemma `singular_values_nonneg` says " All singular values of a matrix are non-negative "
    8.the lemma `trace_mul_comm` says " For any two square matrices A and B of the same size,
      we have tr(A * B) = tr(B * A) "
    9.the lemma `exists_max_at_extreme_point_of_compact_convex_linear` says " For a compact convex
      set S in a finite-dimensional real vector space V, and a linear functional f on V,
      there exists an extreme point x of S such that f(x) = max_{y ∈ S} f(y) "
    10.the lemma `rearrangement_ineq_antitone` says "For antitone sequences a and b and
      any permutation π, the sum ∑ i, a i * b (π i) is maximized when π is the identity".
-/


variable {R} {α : Type*} [RCLike α] [AddCommMonoid R] [CommMonoid R]
variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
variable {V : Type*} {𝕜 : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]-- add a finite-dimensional assumption
         [DecidableEq m] [DecidableEq n] [DecidableEq k]


/-
  Define the `singular values` of a matrix
-/
noncomputable def singularValues {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
  [InnerProductSpace 𝕜 (Fin m → 𝕜)] [InnerProductSpace 𝕜 (Fin n → 𝕜)]
  (A : Matrix (Fin m) (Fin n) 𝕜) (i : Fin n) : ℝ :=
  let r := finrank 𝕜 (range (Matrix.toLin' A))
  if h : i.1 < r then
    (singular_value_decomposition A rfl).some.σ ⟨ i.1, h ⟩
  else
  0

/-
  Define a `doubly substochastic` matrix
-/
def DoublySubStochastic (M : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j ≤ 1) ∧ (∀ j, ∑ i, M i j ≤ 1)

/-
  Let` T A ` denote  the number of rows and columns of A whose sums are less than 1
-/
noncomputable def T (S : Matrix n n ℝ) : ℕ :=
    let row_lt_one := (Finset.univ.filter fun i => ∑ j, S i j < 1).card
    let col_lt_one := (Finset.univ.filter fun j => ∑ i, S i j < 1).card
    row_lt_one + col_lt_one

/-
  The meaning of symbols used below
-/
local notation "σ" => singularValues
local notation "tr" => Matrix.trace
local notation "⟪" x ", " y "⟫" => inner ℝ  x y


/-
  If A and C are diagonal matrices, the matrix product A * B * C * D has elements given by
  (A * B * C * D)ᵢⱼ = Σₖ (Aᵢᵢ * Cₖₖ * Bᵢₖ * Dₖⱼ)

  The proof relies solely on expanding the matrix multiplication definition
-/
lemma matric_elements (n : ℕ) (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin n) 𝕜)
    (C : Matrix (Fin n) (Fin n) 𝕜) (D : Matrix (Fin n) (Fin n) 𝕜)
    (hA : ∀ (i : Fin n) (k : Fin n), A i k ≠ 0 → i.val = k.val)
    (hC : ∀ (j : Fin n) (l : Fin n), C j l ≠ 0 → j.val = l.val) :
    ∀ i j, (A * B * C * D) i j = ∑ k : Fin n, A i i * C k k * (B i k * D k j) := by
    sorry

/-
  let A be `a doubly sub-stochastic matrix`,
  then `A is a doubly stochastic matrix if and only if T A = 0`
-/
lemma DoublySubStochastic_eq_T_0 {A : Matrix n n ℝ}
    (hA : DoublySubStochastic A) : A ∈ doublyStochastic ℝ n ↔ T A = 0 := by
    have h1 :A ∈ doublyStochastic ℝ  n ↔ (∀ (i j : n), 0 ≤ A i j) ∧ (∀ (i : n), ∑ j, A i j = 1)
        ∧ ∀ (j : n), ∑ i, A i j = 1 :=by
     apply mem_doublyStochastic_iff_sum
    have h2 :  DoublySubStochastic A ↔ (∀ (i j : n), 0 ≤ A i j) ∧ (∀ (i : n), ∑ j, A i j ≤ 1)
        ∧ ∀ (j : n), ∑ i, A i j ≤ 1 := by
     simp [DoublySubStochastic]
    obtain ⟨ hA_pos, hA_row_sum, hA_col_sum ⟩ := hA
    have h_doublyStochastic_eq : A ∈ doublyStochastic ℝ  n ↔ T A = 0 := by
     constructor
     · intro h ; rw [h1] at h ; rcases h with ⟨h_nonneg, h_row_eq, h_col_eq⟩
       dsimp [T]
       have h_row_card : (Finset.univ.filter fun i => ∑ j, A i j < 1).card = 0 := by
        apply Finset.card_eq_zero.2; rw [Finset.filter_eq_empty_iff]; intro i hi
        have row_sum_eq : ∑ j, A i j = 1 := h_row_eq i
        linarith [row_sum_eq]
       have h_col_card : (Finset.univ.filter fun j => ∑ i, A i j < 1).card = 0 := by
        apply Finset.card_eq_zero.2; rw [Finset.filter_eq_empty_iff]
        intro j hj
        have col_sum_eq : ∑ i, A i j = 1 := h_col_eq j
        linarith [col_sum_eq]
       simp [h_row_card, h_col_card]
     · intro h
       dsimp [T] at h
       have h_row_card : (Finset.univ.filter fun i => ∑ j, A i j < 1).card = 0 := by
         linarith
       have h_col_card : (Finset.univ.filter fun j => ∑ i, A i j < 1).card = 0 := by
         linarith
       rw [h1]
       have h3 :(∀ (i : n), ∑ j, A i j = 1):=by
        intro i
        have h_row_sum_le : ∑ j, A i j ≤ 1 := hA_row_sum i
        have h_row_sum_not_lt : ¬ (∑ j, A i j < 1) := by
          intro hlt
          have hi_in_filter : i ∈ Finset.univ.filter fun i => ∑ j, A i j < 1 := by
            apply Finset.mem_filter.2; constructor; apply Finset.mem_univ; exact hlt
          have card_pos : (Finset.univ.filter fun i => ∑ j, A i j < 1).card > 0 :=
            Finset.card_pos.2 ⟨i, hi_in_filter⟩
          linarith [h_row_card]
        linarith [h_row_sum_le]
       have h4 : (∀ (j : n), ∑ i, A i j = 1) := by
        intro j
        have h_col_sum_le : ∑ i, A i j ≤ 1 := hA_col_sum j
        have h_col_sum_not_lt : ¬ (∑ i, A i j < 1) := by
          intro hlt
          have hj_in_filter : j ∈ Finset.univ.filter fun j => ∑ i, A i j < 1 := by
            apply Finset.mem_filter.2; constructor; apply Finset.mem_univ; exact hlt
          have card_pos : (Finset.univ.filter fun j => ∑ i, A i j < 1).card > 0 :=
            Finset.card_pos.2 ⟨j, hj_in_filter⟩
          linarith [h_col_card]
        linarith [h_col_sum_le]
       exact ⟨hA_pos, h3, h4⟩
    exact h_doublyStochastic_eq

/-
  If A is a doubly sub-stochastic matrix with `T A > 0`,
  then there exists a `doubly sub-stochastic matrix C `such that `A i j ≤ C i j` for all i, j ;
  and `T C < T A`.
-/
lemma DoublySubStochastic_improvement {A : Matrix n n ℝ} (hA : DoublySubStochastic A)
    (hT_pos : T A > 0) : ∃ (C : Matrix n n ℝ), DoublySubStochastic C ∧ (∀ i j, A i j ≤ C i j)
    ∧ T C < T A := by
  rcases hA with ⟨hA_pos, hA_row_sum, hA_col_sum⟩
  --there must exist at least one row or one column whose sum is less than 1
  have h_exist  : ((∃ i, ∑ j, A i j < 1) ∨ (∃ j, ∑ i, A i j < 1) ) := by
    by_contra! H
    obtain ⟨ H1, H2 ⟩ := H
    have h1: T A = 0 := by
      dsimp [T]
      have h2 : (Finset.univ.filter fun i => ∑ j, A i j < 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro i hi
        have row_sum_ge : ∑ j, A i j ≥ 1 := by
          linarith [H1 i]
        linarith [row_sum_ge]
      have h3 : (Finset.univ.filter fun j => ∑ i, A i j < 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro j hj
        have col_sum_ge : ∑ i, A i j ≥ 1 := by
          linarith [H2 j]
        linarith [col_sum_ge]
      simp [h2, h3]
    linarith [hT_pos, h1]

  rcases h_exist with (⟨i, hi_row⟩ | ⟨j, hj_col⟩)

  · -- case 1 : If there exists a row i such that ∑ j, A i j < 1 ,then we can find a column j
    -- such that ∑ i, A i j < 1
    -- this statement can be proven by contradiction. Specifically, we analyze the sum of all
    -- elements within the matrix
    have : ∃ j, ∑ i, A i j < 1 := by
      by_contra! H
      have total_sum_ge : ∑ i ,∑ j, A i j ≥ Fintype.card n := by
        calc
          ∑ i ,∑ j, A i j = ∑ j, ∑ i, A i j := by rw [Finset.sum_comm]
          _ ≥ ∑ i, 1 := Finset.sum_le_sum fun i _ => H i
          _ = Fintype.card n := by simp
      have total_sum_le : ∑ i ,∑ j, A i j ≤ Fintype.card n := by
        calc
          ∑ i ,∑ j, A i j = ∑ i, ∑ j, A i j := by rw [Finset.sum_comm]
          _ ≤ ∑ i, 1 := Finset.sum_le_sum fun i _ => hA_row_sum i
          _ = Fintype.card n := by simp
      have h_eq : ∑ i ,∑ j, A i j = Fintype.card n := by
        linarith [total_sum_ge, total_sum_le]
      have h_col_eq : ∀ i, ∑ j, A i j = 1 := by
        intro i
        have col_sum_le :  ∑ j, A i j ≤ 1 := hA_row_sum i
        have col_sum_ge :  ∑ j, A i j ≥ 1 := by
          by_contra! hlt
          have h1: ∑ i, ∑  j, A i j < Fintype.card n := by
            calc
              ∑ i, ∑  j, A i j < ∑ i, 1 := Finset.sum_lt_sum (fun i _ => hA_row_sum i)
                ⟨i, Finset.mem_univ i, hlt⟩
              _ = Fintype.card n := by simp
          linarith [h_eq, h1]
        linarith [col_sum_le, col_sum_ge]
      linarith [hi_row , h_col_eq i]

    rcases this with ⟨j, hj_col_lt⟩

    -- Now we have found a row i and a column j such that their sums are less than 1
    -- then we modify the element A i j by adding a small positive number ε to it
    -- until either the i-th row sum or the j-th column sum (or both) reaches 1 ,
    -- ε = min (1 - ∑ j, A i j) (1 - ∑ i, A i j)
    -- let C be the modified matrix ,then C is still a doubly sub-stochastic matrix such that
    -- A i j ≤ C i j for all i, j and T C < T A
    set ε := min (1 - ∑ j, A i j) (1 - ∑ i, A i j) with hε_def
    have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
    let C : Matrix n n ℝ := fun x y => if x = i ∧ y = j then A x y + ε else A x y
    -- prove that C is a doubly sub-stochastic matrix
    have hC_DoublySubStochastic : DoublySubStochastic C := by
      refine ⟨?_, ?_, ?_⟩
      · --Prove that Cᵢⱼ is non-negative
        intro x y
        by_cases h : x = i ∧ y = j
        · rcases h with ⟨rfl, rfl⟩
          simp [C]
          linarith [hA_pos x y, hε_pos]
        · simp [C, h, hA_pos x y]
      · --prove that all row sums of C are less than or equal to 1
        intro x
        dsimp [C]
        by_cases h : x = i
        · have h0 : ∑ j, C x j = ∑ j, A x j + ε := by
            dsimp [C]
            subst h
            simp
            simp [Finset.sum_ite]
            simp [ Finset.filter_eq']
            ring_nf
            have h1 :A x j + ε + ∑ x_1 with ¬x_1 = j, A x x_1 = ε + A x j + ∑ x_1
              with ¬x_1 = j, A x x_1 := by ring_nf
            rw [h1]
            rw [← Finset.add_sum_erase (s := Finset.univ) (A x) (Finset.mem_univ j)]
            ring_nf
            congr 1
            apply Finset.sum_congr
            simp [Finset.ext_iff]
            simp only
            intro _ _
            exact trivial
          have h2: ε ≤ 1 - ∑ j, A x j := by
            subst h
            apply min_le_left
          have h3 : ∑ j, C x j ≤ 1 := by
            linarith [h0, h2]
          exact h3
        · dsimp [C]
          simp [h]
          exact hA_row_sum x
      · -- prove that all column sums of C are less than or equal to 1
        intro y
        dsimp [C]
        by_cases h : y = j
        · have h0 : ∑ i, C i y = ∑ i, A i y + ε := by
            dsimp [C]
            subst h
            simp
            simp [Finset.sum_ite]
            simp [ Finset.filter_eq']
            ring_nf
            have h1 :A i y + ε + ∑ i_1 with ¬i_1 = i, A i_1 y = ε + A i y + ∑ i_1
              with ¬i_1 = i, A i_1 y := by ring_nf
            rw [h1]
            rw [← Finset.add_sum_erase (s := Finset.univ) (fun x => A x y) (Finset.mem_univ i)]
            ring_nf
            congr 1
            apply Finset.sum_congr
            simp [Finset.ext_iff]
            simp only
            intro _ _
            exact trivial
          have h2: ε ≤ 1 - ∑ i, A i y := by
            subst h
            apply min_le_right
          have h3 : ∑ i, C i y ≤ 1 := by
            linarith [h0, h2]
          exact h3
        · dsimp [C]
          simp [h]
          exact hA_col_sum y
    -- prove that A i j ≤ C i j for all i, j
    have hAC_le : ∀ x y, A x y ≤ C x y := by
      intro x y
      by_cases h : x = i ∧ y = j
      · rcases h with ⟨rfl, rfl⟩
        simp [C]
        linarith [hε_pos]
      · simp [C, h]
    -- prove that T C < T A
    -- we consider two cases ：ε = 1 - ∑ j, A i j  or ε = 1 - ∑ i, A i j
    have hT_C_lt_T_A : T C < T A := by
      have hε_eq_or : ε = 1 - ∑ j, A i j ∨ ε = 1 - ∑ i, A i j := by
        rw [hε_def]
        exact min_choice  _ _
      obtain h_H | h_L := hε_eq_or

      · -- case 1 : ε = 1 - ∑ j, A i j
        -- Since the i-th row sum of C becomes to 1 and other row sums remain unchanged
        -- while the column sums remain unchanged except the j-th column sum which increases
        -- by ε but still less or equal to 1
        -- then we can show that T C < T A
        have row_sum_C_eq : ∑ j, C i j = 1 := by
          dsimp [C]
          have h0 : ∑ j, C i j = ∑ j, A i j + ε := by
            dsimp [C]
            simp
            simp [Finset.sum_ite]
            simp [ Finset.filter_eq']
            ring_nf
            have h1 :A i j + ε + ∑ x with ¬ x = j, A  i x = ε + A i j + ∑ x
                with ¬x = j , A i x := by ring_nf
            rw [h1]
            rw [← Finset.add_sum_erase (s := Finset.univ) (fun x => A i x) (Finset.mem_univ j)]
            ring_nf
            congr 1
            apply Finset.sum_congr
            simp [Finset.ext_iff]
            simp only
            intro _ _
            exact trivial
          have h2: ε = 1 - ∑ j, A i j := h_H
          linarith [h0, h2]
        have row_sum_C_eq_1 : ∀ x, x ≠ i → ∑ j, C x j =∑ j, A x j := by
          intro x hx_ne
          dsimp [C]
          simp [hx_ne]

        have h_row_card_lt : (Finset.univ.filter fun i => ∑ j, C i j < 1).card <
                            (Finset.univ.filter fun i => ∑ j, A i j < 1).card := by
          apply Finset.card_lt_card
          refine ⟨?_, ?_⟩
          --we need to prove the subset relation and then prove the strictness
          · intro x hx
            simp_rw [Finset.mem_filter] at hx ⊢
            have h_univ : x ∈ Finset.univ := hx.1
            have h_sum_lt : ∑ j, C x j < 1 := hx.2
            refine ⟨h_univ, ?_⟩
            by_cases h : x = i
            · subst h
              linarith [row_sum_C_eq, h_sum_lt]
            · have h0 : x ≠ i := h
              have h1 : ∑ j, C x j = ∑ j, A x j := row_sum_C_eq_1 x h0
              linarith [h1, h_sum_lt]
          · by_contra h_contra
            have men_right : i ∈ Finset.univ.filter fun i => ∑ j, A i j < 1 := by
              apply Finset.mem_filter.2; constructor; apply Finset.mem_univ; exact hi_row
            have not_mem_left : i ∉ Finset.univ.filter (fun i => ∑ j, C i j < 1) := by
              simp_rw [Finset.mem_filter, not_and]
              intro _
              exact by
                rw [row_sum_C_eq]
                linarith
            have h1 : i ∈ Finset.univ.filter fun i => ∑ j, C i j < 1 := h_contra men_right
            contradiction

        have h_col_card_le : (Finset.univ.filter fun j => ∑ i, C i j < 1).card ≤
                            (Finset.univ.filter fun j => ∑ i, A i j < 1).card := by
          apply Finset.card_le_card
          --we can only prove the subset relation here
          intro y hy
          simp_rw [Finset.mem_filter] at hy ⊢
          have h_univ : y ∈ Finset.univ := hy.1
          have h_sum_lt : ∑ i, C i y < 1 := hy.2
          refine ⟨h_univ, ?_⟩
          by_cases h : y = j
          · have h0 : ∑ i, C i y = ∑ i, A i y + ε := by
              dsimp [C]
              subst h
              simp
              simp [Finset.sum_ite]
              simp [ Finset.filter_eq']
              ring_nf
              have h1 :A i y + ε + ∑ i_1 with ¬i_1 = i, A i_1 y = ε + A i y + ∑ i_1
                with ¬i_1 = i, A i_1 y := by ring_nf
              rw [h1]
              rw [← Finset.add_sum_erase (s := Finset.univ) (fun x => A x y) (Finset.mem_univ i)]
              ring_nf
              congr 1
              apply Finset.sum_congr
              simp [Finset.ext_iff]
              simp only
              intro _ _
              exact trivial
            have h1: ∑ i ,A i y = ∑ i , C i y - ε := by
              linarith [h0]
            have h2 : ∑ i , A i y < 1 := by
              linarith [h1, h_sum_lt, hε_pos]
            exact h2
          · have h0 : ∑ i, C i y = ∑ i, A i y := by
              dsimp [C]
              simp [h]
            rw [← h0]
            exact h_sum_lt

        have hT_C_lt_T_A : T C < T A := by
          dsimp [T]
          linarith [h_row_card_lt, h_col_card_le]
        exact hT_C_lt_T_A

      · -- case 2 : ε = 1 - ∑ i, A i j
        -- Since the j-th column sum of C becomes to 1 and other column sums remain unchanged
        -- while the row sums remain unchanged except the i-th row sum which increases by ε
        -- but still less or equal to 1
        -- we can show that T C < T A
        have col_sum_C_eq : ∑ i, C i j = 1 := by
          dsimp [C]
          have h0 : ∑ i, C i j = ∑ i, A i j + ε := by
            dsimp [C]
            simp
            simp [Finset.sum_ite]
            simp [ Finset.filter_eq']
            ring_nf
            have h1 :A i j + ε + ∑ i_1 with ¬i_1 = i, A i_1 j = ε + A i j + ∑ i_1
              with ¬i_1 = i, A i_1 j := by ring_nf
            rw [h1]
            rw [← Finset.add_sum_erase (s := Finset.univ) (fun x => A x j) (Finset.mem_univ i)]
            ring_nf
            congr 1
            apply Finset.sum_congr
            simp [Finset.ext_iff]
            simp only
            intro _ _
            exact trivial
          have h2: ε = 1 - ∑ i, A i j := h_L
          linarith [h0, h2]
        have col_sum_C_eq_1 : ∀ y, y ≠ j → ∑ i, C i y =∑ i, A i y := by
          intro y hy_ne
          dsimp [C]
          simp [hy_ne]
        have h_col_card_lt : (Finset.univ.filter fun j => ∑ i, C i j < 1).card <
                            (Finset.univ.filter fun j => ∑ i, A i j < 1).card := by
          apply Finset.card_lt_card
          --we need to prove the subset relation and then prove the strictness
          refine ⟨?_, ?_⟩
          · intro y hy
            simp_rw [Finset.mem_filter] at hy ⊢
            have h_univ : y ∈ Finset.univ := hy.1
            have h_sum_lt : ∑ i, C i y < 1 := hy.2
            refine ⟨h_univ, ?_⟩
            by_cases h : y = j
            · subst h
              linarith [col_sum_C_eq, h_sum_lt]
            · have h0 : y ≠ j := h
              have h1 : ∑ i, C i y = ∑ i, A i y := col_sum_C_eq_1 y h0
              linarith [h1, h_sum_lt]
          · by_contra h_contra
            have men_right : j ∈ Finset.univ.filter fun j => ∑ i, A i j < 1 := by
              apply Finset.mem_filter.2; constructor; apply Finset.mem_univ; exact hj_col_lt
            have not_mem_left : j ∉ Finset.univ.filter (fun j => ∑ i, C i j < 1) := by
              simp_rw [Finset.mem_filter, not_and]
              intro _
              exact by
                rw [col_sum_C_eq]
                linarith
            have h1 : j ∈ Finset.univ.filter fun j => ∑ i, C i j < 1 := h_contra men_right
            contradiction

        have h_row_card_le : (Finset.univ.filter fun i => ∑ j, C i j < 1).card ≤
                            (Finset.univ.filter fun i => ∑ j, A i j < 1).card := by
          apply Finset.card_le_card
          --we can only prove the subset relation here
          intro x hx
          simp_rw [Finset.mem_filter] at hx ⊢
          have h_univ : x ∈ Finset.univ := hx.1
          have h_sum_lt : ∑ j, C x j < 1 := hx.2
          refine ⟨h_univ, ?_⟩
          by_cases h : x = i
          · have h0 : ∑ j, C x j = ∑ j, A x j + ε := by
              dsimp [C]
              subst h
              simp
              simp [Finset.sum_ite]
              simp [ Finset.filter_eq']
              ring_nf
              have h1 :A x j + ε + ∑ x_1 with ¬x_1 = j, A x x_1 = ε + A x j + ∑ x_1
                with ¬x_1 = j, A x x_1 := by ring_nf
              rw [h1]
              rw [← Finset.add_sum_erase (s := Finset.univ) (A x) (Finset.mem_univ j)]
              ring_nf
              congr 1
              apply Finset.sum_congr
              simp [Finset.ext_iff]
              simp only
              intro _ _
              exact trivial
            have h1: ∑ j ,A x j = ∑ j , C x j - ε := by
              linarith [h0]
            have h2 : ∑ j , A x j < 1 := by
              linarith [h1, h_sum_lt, hε_pos]
            exact h2
          · have h0 : ∑ j, C x j = ∑ j, A x j := by
              dsimp [C]
              simp [h]
            rw [← h0]
            exact h_sum_lt

        have hT_C_lt_T_A : T C < T A := by
          dsimp [T]
          linarith [h_row_card_le, h_col_card_lt]
        exact hT_C_lt_T_A

    use C

  · -- case 2 : If there exists a column j such that ∑ i, A i j < 1 ,
    -- then we can find a row i such that ∑ j, A i j < 1
    -- this statement can be proven by contradiction. Specifically,
    -- we analyze the sum of all elements within the matrix
    have : ∃ i, ∑ j, A i j < 1 := by
       by_contra! H
       have total_sum_ge : ∑ i ,∑ j, A i j ≥ Fintype.card n := by
          calc
            ∑ i ,∑ j, A i j = ∑ i, ∑ j, A i j := by rw [Finset.sum_comm]
            _ ≥ ∑ j, 1 := Finset.sum_le_sum fun j _ => H j
            _ = Fintype.card n := by simp
       have total_sum_le : ∑ i ,∑ j, A i j ≤ Fintype.card n := by
          calc
            ∑ i ,∑ j, A i j = ∑ i, ∑ j, A i j := by rw [Finset.sum_comm]
            _ ≤ ∑ i, 1 := Finset.sum_le_sum fun i _ => hA_row_sum i
            _ = Fintype.card n := by simp
       have h_eq : ∑ i ,∑ j, A i j = Fintype.card n := by
          linarith [total_sum_ge, total_sum_le]
       have h_row_eq : ∀ j, ∑ i, A i j = 1 := by
          intro j
          have row_sum_le :  ∑ i, A i j ≤ 1 := hA_col_sum j
          have row_sum_ge :  ∑ i, A i j ≥ 1 := by
            by_contra! hlt
            have h1: ∑ i, ∑  j, A i j < Fintype.card n := by
              calc
                ∑ i ,∑ j , A i j = ∑ j ,∑ i , A i j := by rw [Finset.sum_comm]
                _ < ∑ j, 1 := Finset.sum_lt_sum (fun j _ => hA_col_sum j)
                  ⟨j, Finset.mem_univ j, hlt⟩
                _ = Fintype.card n := by simp
            linarith [h_eq, h1]
          linarith [row_sum_le, row_sum_ge]
       linarith [hj_col , h_row_eq j]

    rcases this with ⟨i, hi_row_lt⟩

    -- Now we have found a row i and a column j such that their sums are less than 1
    -- then we modify the element A i j by adding a small positive number ε to it
    -- until either the i-th row sum or the j-th column sum (or both) reaches 1 ,
    -- ε = min (1 - ∑ j, A i j) (1 - ∑ i, A i j)
    -- let C be the modified matrix ,then C is still a doubly sub-stochastic matrix such that
    -- A i j ≤ C i j for all i, j and T C < T A
    set ε := min (1 - ∑ j, A i j) (1 - ∑ i, A i j) with hε_def
    have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
    let C : Matrix n n ℝ := fun x y => if x = i ∧ y = j then A x y + ε else A x y
    have hC_DoublySubStochastic : DoublySubStochastic C := by
      refine ⟨?_, ?_, ?_⟩
      ·--Prove that Cᵢⱼ is non-negative
        intro x y
        by_cases h : x = i ∧ y = j
        · rcases h with ⟨rfl, rfl⟩
          simp [C]
          linarith [hA_pos x y, hε_pos]
        · simp [C, h, hA_pos x y]
      ·--prove that all row sums of C are less than or equal to 1
        intro x
        by_cases h : x = i
        · have h0 : ∑ j, C x j = ∑ j, A x j + ε := by
            dsimp [C]
            subst h
            simp
            simp [Finset.sum_ite]
            simp [ Finset.filter_eq']
            ring_nf
            have h1 :A x j + ε + ∑ x_1 with ¬x_1 = j, A x x_1 = ε + A x j + ∑ x_1
              with ¬x_1 = j, A x x_1 := by ring_nf
            rw [h1]
            rw [← Finset.add_sum_erase (s := Finset.univ) (A x) (Finset.mem_univ j)]
            ring_nf
            congr 1
            apply Finset.sum_congr
            simp [Finset.ext_iff]
            simp only
            intro _ _
            exact trivial
          have h2: ε ≤ 1 - ∑ j, A x j := by
            subst h
            apply min_le_left
          have h3 : ∑ j, C x j ≤ 1 := by
            linarith [h0, h2]
          exact h3
        · dsimp [C]
          simp [h]
          exact hA_row_sum x

      ·-- prove that all column sums of C are less than or equal to 1
        intro y
        dsimp [C]
        by_cases h : y = j
        · have h0 : ∑ i, C i y = ∑ i, A i y + ε := by
            dsimp [C]
            subst h
            simp
            simp [Finset.sum_ite]
            simp [ Finset.filter_eq']
            ring_nf
            have h1 :A i y + ε + ∑ i_1 with ¬i_1 = i, A i_1 y = ε + A i y + ∑ i_1
              with ¬i_1 = i, A i_1 y := by ring_nf
            rw [h1]
            rw [← Finset.add_sum_erase (s := Finset.univ) (fun x => A x y) (Finset.mem_univ i)]
            ring_nf
            congr 1
            apply Finset.sum_congr
            simp [Finset.ext_iff]
            simp only
            intro _ _
            exact trivial
          have h2: ε ≤ 1 - ∑ i, A i y := by
            subst h
            apply min_le_right
          have h3 : ∑ i, C i y ≤ 1 := by
            linarith [h0, h2]
          exact h3
        · dsimp [C]
          simp [h]
          exact hA_col_sum y
    -- prove that A i j ≤ C i j for all i, j
    have hAC_le : ∀ x y, A x y ≤ C x y := by
      intro x y
      by_cases h : x = i ∧ y = j
      · rcases h with ⟨rfl, rfl⟩
        simp [C]
        linarith [hε_pos]
      · simp [C, h]
    -- prove that T C < T A
    -- we consider two cases ：ε = 1 - ∑ j, A i j  or ε = 1 - ∑ i, A i j
    have hT_C_lt_T_A : T C < T A := by
      have hε_eq_or : ε = 1 - ∑ j, A i j ∨ ε = 1 - ∑ i, A i j := by
        rw [hε_def]
        exact min_choice  _ _
      obtain h_H | h_L := hε_eq_or

      · -- case 1 : ε = 1 - ∑ j, A i j
        -- Since the i-th row sum of C becomes to 1 and other row sums remain unchanged
        -- while the column sums remain unchanged except the j-th column sum which increases
        -- by ε but still less or equal to 1
        -- we can show that T C < T A
        have row_sum_C_eq : ∑ j, C i j = 1 := by
          dsimp [C]
          have h0 : ∑ j, C i j = ∑ j, A i j + ε := by
            dsimp [C]
            simp
            simp [Finset.sum_ite]
            simp [ Finset.filter_eq']
            ring_nf
            have h1 :A i j + ε + ∑ x with ¬ x = j, A  i x = ε + A i j + ∑ x
                with ¬x = j , A i x := by ring_nf
            rw [h1]
            rw [← Finset.add_sum_erase (s := Finset.univ) (fun x => A i x) (Finset.mem_univ j)]
            ring_nf
            congr 1
            apply Finset.sum_congr
            simp [Finset.ext_iff]
            simp only
            intro _ _
            exact trivial
          have h2: ε = 1 - ∑ j, A i j := h_H
          linarith [h0, h2]
        have row_sum_C_eq_1 : ∀ x, x ≠ i → ∑ j, C x j =∑ j, A x j := by -- prove other row sums unchanged
          intro x hx_ne
          dsimp [C]
          simp [hx_ne]

        have h_row_card_lt : (Finset.univ.filter fun i => ∑ j, C i j < 1).card <
                            (Finset.univ.filter fun i => ∑ j, A i j < 1).card := by
          apply Finset.card_lt_card
          --we need to prove the subset relation and then prove the strictness
          refine ⟨?_, ?_⟩
          · intro x hx
            simp_rw [Finset.mem_filter] at hx ⊢
            have h_univ : x ∈ Finset.univ := hx.1
            have h_sum_lt : ∑ j, C x j < 1 := hx.2
            refine ⟨h_univ, ?_⟩
            by_cases h : x = i
            · subst h
              linarith [row_sum_C_eq, h_sum_lt]
            · have h0 : x ≠ i := h
              have h1 : ∑ j, C x j = ∑ j, A x j := row_sum_C_eq_1 x h0
              linarith [h1, h_sum_lt]
          · by_contra h_contra
            have men_right : i ∈ Finset.univ.filter fun i => ∑ j, A i j < 1 := by
              apply Finset.mem_filter.2; constructor; apply Finset.mem_univ; exact hi_row_lt
            have not_mem_left : i ∉ Finset.univ.filter (fun i => ∑ j, C i j < 1) := by
              simp_rw [Finset.mem_filter, not_and]
              intro _
              exact by
                rw [row_sum_C_eq]
                linarith
            have h1 : i ∈ Finset.univ.filter fun i => ∑ j, C i j < 1 := h_contra men_right
            contradiction

        have h_col_card_le : (Finset.univ.filter fun j => ∑ i, C i j < 1).card ≤
                            (Finset.univ.filter fun j => ∑ i, A i j < 1).card := by
          apply Finset.card_le_card
          --we can only prove the subset relation here
          intro y hy
          simp_rw [Finset.mem_filter] at hy ⊢
          have h_univ : y ∈ Finset.univ := hy.1
          have h_sum_lt : ∑ i, C i y < 1 := hy.2
          refine ⟨h_univ, ?_⟩
          by_cases h : y = j
          · have h0 : ∑ i, C i y = ∑ i, A i y + ε := by
              dsimp [C]
              subst h
              simp
              simp [Finset.sum_ite]
              simp [ Finset.filter_eq']
              ring_nf
              have h1 :A i y + ε + ∑ i_1 with ¬i_1 = i, A i_1 y = ε + A i y + ∑ i_1
                with ¬i_1 = i, A i_1 y := by ring_nf
              rw [h1]
              rw [← Finset.add_sum_erase (s := Finset.univ) (fun x => A x y) (Finset.mem_univ i)]
              ring_nf
              congr 1
              apply Finset.sum_congr
              simp [Finset.ext_iff]
              simp only
              intro _ _
              exact trivial
            have h1: ∑ i ,A i y = ∑ i , C i y - ε := by
              linarith [h0]
            have h2 : ∑ i , A i y < 1 := by
              linarith [h1, h_sum_lt, hε_pos]
            exact h2
          · have h0 : ∑ i, C i y = ∑ i, A i y := by
              dsimp [C]
              simp [h]
            rw [← h0]
            exact h_sum_lt

        have hT_C_lt_T_A : T C < T A := by
          dsimp [T]
          linarith [h_row_card_lt, h_col_card_le]
        exact hT_C_lt_T_A

      · -- case 2 : ε = 1 - ∑ i, A i j
        -- Since the j-th column sum of C becomes to 1 and other column sums remain unchanged
        -- while the row sums remain unchanged except the i-th row sum which increases
        -- by ε but still less or equal to 1
        -- we can show that T C < T A
        have col_sum_C_eq : ∑ i, C i j = 1 := by
          dsimp [C]
          have h0 : ∑ i, C i j = ∑ i, A i j + ε := by
            dsimp [C]
            simp
            simp [Finset.sum_ite]
            simp [ Finset.filter_eq']
            ring_nf
            have h1 :A i j + ε + ∑ i_1 with ¬i_1 = i, A i_1 j = ε + A i j + ∑ i_1
                with ¬i_1 = i, A i_1 j := by ring_nf
            rw [h1]
            rw [← Finset.add_sum_erase (s := Finset.univ) (fun x => A x j) (Finset.mem_univ i)]
            ring_nf
            congr 1
            apply Finset.sum_congr
            simp [Finset.ext_iff]
            simp only
            intro _ _
            exact trivial
          have h2: ε = 1 - ∑ i, A i j := h_L
          linarith [h0, h2]
        have col_sum_C_eq_1 : ∀ y, y ≠ j → ∑ i, C i y =∑ i, A i y := by
          intro y hy_ne
          dsimp [C]
          simp [hy_ne]

        have h_col_card_lt : (Finset.univ.filter fun j => ∑ i, C i j < 1).card <
                            (Finset.univ.filter fun j => ∑ i, A i j < 1).card := by
          apply Finset.card_lt_card
          --we need to prove the subset relation and then prove the strictness
          refine ⟨?_, ?_⟩
          · intro y hy
            simp_rw [Finset.mem_filter] at hy ⊢
            have h_univ : y ∈ Finset.univ := hy.1
            have h_sum_lt : ∑ i, C i y < 1 := hy.2
            refine ⟨h_univ, ?_⟩
            by_cases h : y = j
            · subst h
              linarith [col_sum_C_eq, h_sum_lt]
            · have h0 : y ≠ j := h
              have h1 : ∑ i, C i y = ∑ i, A i y := col_sum_C_eq_1 y h0
              linarith [h1, h_sum_lt]
          · by_contra h_contra
            have men_right : j ∈ Finset.univ.filter fun j => ∑ i, A i j < 1 := by
              apply Finset.mem_filter.2; constructor; apply Finset.mem_univ; exact hj_col
            have not_mem_left : j ∉ Finset.univ.filter (fun j => ∑ i, C i j < 1) := by
              simp_rw [Finset.mem_filter, not_and]
              intro _
              exact by
                rw [col_sum_C_eq]
                linarith
            have h1 : j ∈ Finset.univ.filter fun j => ∑ i, C i j < 1 := h_contra men_right
            contradiction

        have h_row_card_le : (Finset.univ.filter fun i => ∑ j, C i j < 1).card ≤
                            (Finset.univ.filter fun i => ∑ j, A i j < 1).card := by
          apply Finset.card_le_card
          --we can only prove the subset relation here
          intro x hx
          simp_rw [Finset.mem_filter] at hx ⊢
          have h_univ : x ∈ Finset.univ := hx.1
          have h_sum_lt : ∑ j, C x j < 1 := hx.2
          refine ⟨h_univ, ?_⟩
          by_cases h : x = i
          · have h0 : ∑ j, C x j = ∑ j, A x j + ε := by
              dsimp [C]
              subst h
              simp
              simp [Finset.sum_ite]
              simp [ Finset.filter_eq']
              ring_nf
              have h1 :A x j + ε + ∑ x_1 with ¬x_1 = j, A x x_1 = ε + A x j + ∑ x_1
                  with ¬x_1 = j, A x x_1 := by ring_nf
              rw [h1]
              rw [← Finset.add_sum_erase (s := Finset.univ) (A x) (Finset.mem_univ j)]
              ring_nf
              congr 1
              apply Finset.sum_congr
              simp [Finset.ext_iff]
              simp only
              intro _ _
              exact trivial
            have h1: ∑ j ,A x j = ∑ j , C x j - ε := by
              linarith [h0]
            have h2 : ∑ j , A x j < 1 := by
              linarith [h1, h_sum_lt, hε_pos]
            exact h2
          · have h0 : ∑ j, C x j = ∑ j, A x j := by
              dsimp [C]
              simp [h]
            rw [← h0]
            exact h_sum_lt

        have hT_C_lt_T_A : T C < T A := by
          dsimp [T]
          linarith [h_row_card_le, h_col_card_lt]
        exact hT_C_lt_T_A
    use C


/-
For any `doubly sub-stochastic matrix A`, there `exists a doubly stochastic matrix S`
such that `A i j ≤ S i j `for all i, j

Proof: See Matrix Analysis by Roger A. Horn and Charles R. Johnson, 2nd edition, Theorem 8.7.5,
page 550.
-/
/-
We can proof this theorem by strong induction on T A ,where T A is the number of rows and columns
whose sums are less than 1
If T A = 0 ,by `the lemma DoublySubStochastic_eq_T_0` then A is already a doubly stochastic matrix,
we can take S = A
If T A > 0 ,by `the lemma DoublySubStochastic_improvement`, we can find a doubly sub-stochastic
matrix C such that A i j ≤ C i j for all i, j and T C < T A
By the induction hypothesis ,there exists a doubly stochastic matrix S such that C i j ≤ S i j
for all i, j
Then we have A i j ≤ S i j for all i, j
Finally,  we complete the proof
-/
private theorem exists_doubly_stochastic_above_substochastic {A : Matrix n n ℝ}
    (hA : DoublySubStochastic A) :
    ∃ S : Matrix n n ℝ, S ∈ doublyStochastic ℝ n ∧  ∀ i j, A i j ≤ S i j:= by
    have h_equiv : A ∈ doublyStochastic ℝ  n ↔ T A = 0 := DoublySubStochastic_eq_T_0 hA
    have h_improve : T A > 0 → ∃ (C : Matrix n n ℝ), DoublySubStochastic C ∧
        (∀ i j, A i j ≤ C i j) ∧ T C < T A := by
      exact DoublySubStochastic_improvement hA

    induction' hk: T A using Nat.strong_induction_on with k IH generalizing A
    by_cases h : T A = 0
    · -- T A = 0
      obtain h_A := h_equiv.mpr h
      use A
      exact ⟨h_A, fun i j => le_refl (A i j)⟩
    · -- T A > 0
      have hpos : T A > 0 := Nat.pos_of_ne_zero h
      obtain ⟨C, hC_substochastic, hAC_le, hT_C_lt⟩ := h_improve hpos
      have h1 : T A = k := by
        rw [hk]
      have h2 : T C < k := by
        linarith
      have h_equiv_C : C ∈ doublyStochastic ℝ n ↔ T C = 0 :=
        DoublySubStochastic_eq_T_0 hC_substochastic
      have h_improve_C : T C > 0 → ∃ (D : Matrix n n ℝ), DoublySubStochastic D
          ∧ (∀ i j, C i j ≤ D i j) ∧ T D < T C :=
        DoublySubStochastic_improvement hC_substochastic
      obtain ⟨S, hS_stochastic, hCS_le⟩ := IH (T C) h2 hC_substochastic h_equiv_C h_improve_C rfl
      use S
      exact ⟨hS_stochastic, fun i j => le_trans (hAC_le i j) (hCS_le i j)⟩

/-
 For a` compact convex set S` in a `finite-dimensional` real vector space V,
 and a `linear` functional f on V,
 there exists an `extreme point` x of S such that f(x) = max_{y ∈ S} f(y) "
-/
lemma exists_max_at_extreme_point_of_compact_convex_linear {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (h_compact : IsCompact s) (h_convex : Convex ℝ s) {f : E → ℝ}
    (h_linear : IsLinearMap ℝ f) : ∃ x ∈ Set.extremePoints ℝ s, ∀ y ∈ s, f y ≤ f x := by
   sorry

/-
 The `set of doubly stochastic matrices `is a `convex set`
 This result is already available in Mathlib
-/
#check convex_doublyStochastic

/-
 The `set of doubly stochastic matrices `is a `compact set`
 Indeed, it is compact, as it is both bounded and closed.
-/
lemma isCompact_doublyStochastic :
    IsCompact (doublyStochastic ℝ n : Set (Matrix n n ℝ)) := by
    sorry
/-
 The `extreme points` of` the set of doubly stochastic matrices` are `permutation matrices`
 this result is already available in Mathlib.
-/
#check extremePoints_doublyStochastic

/-
 `Rearrangement inequality` for antitone sequences.
 For antitone sequences `a` and `b` and any permutation `π`,
 the sum `∑ i, a i * b (π i)` is maximized when `π` is the identity.
-/
lemma rearrangement_ineq_antitone {n : Type*} [Fintype n] [LinearOrder n] (a b : n → ℝ)
    (π : Equiv.Perm n) (ha_antitone : ∀ i j, i ≤ j → a j ≤ a i)
    (hb_antitone : ∀ i j, i ≤ j → b j ≤ b i) : ∑ i, a i * b (π i) ≤ ∑ i, a i * b i := by
    sorry

/-
  `Cauchy-Schwarz inequality` for real-valued finite sequences.
-/
lemma cauchy_schwarz_real {n : ℕ} (u v : Fin n → ℝ) :
    ‖ ∑ i : Fin n, u i * v i‖  ≤ √(∑ i : Fin n, ‖ u i‖  ^ 2) * √(∑ i : Fin n, ‖ v i‖ ^ 2) := by
  let u' : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 u
  let v' : PiLp 2 (fun _ : Fin n => ℝ) := WithLp.toLp 2 v
  have h : ‖⟪u', v'⟫‖ ≤ ‖u'‖ * ‖v'‖ := norm_inner_le_norm u' v'
  have inner_eq : ⟪u', v'⟫ = ∑ i, ⟪u' i, v' i⟫ := PiLp.inner_apply u' v'
  have scalar_inner : ∀ i, ⟪u' i, v' i⟫ = (u i) * v i := by
    intro i
    simp [u',v']
    apply mul_comm
  have norm_u_sq : ‖u'‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 :=
    by simpa [u'] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) u'
  have norm_v_sq : ‖v'‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
    by simpa [v'] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) v'
  have norm_u_eq : ‖u'‖ = √(∑ i, ‖u i‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg u'), norm_u_sq]
  have norm_v_eq : ‖v'‖ = √(∑ i, ‖v i‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v'), norm_v_sq]
  rw [inner_eq] at h
  rw [norm_u_eq, norm_v_eq] at h
  simp_rw [scalar_inner] at h
  exact h

/-
  The trace is invariant under unitary similarity transformations
-/
lemma trace_unitary_similarity (U : Matrix n n 𝕜) (A : Matrix n n 𝕜) (hU : U ∈ unitaryGroup n 𝕜) :
    tr (Uᴴ * A * U) = tr A := by
  have hU' : U * Uᴴ = 1 := by
    rw [mem_unitaryGroup_iff] at hU ; exact hU
  calc
    tr (Uᴴ * A * U)= tr (A * U * Uᴴ ) := by rw [Matrix.mul_assoc, trace_mul_comm]
    _ = tr A := by rw [Matrix.mul_assoc, hU', Matrix.mul_one]

/-
  The conjugate transpose of a unitary matrix is also a unitary matrix.
-/
lemma conjTranspose_unitary (U : Matrix n n 𝕜) (hU : U ∈ unitaryGroup n 𝕜) :
    Uᴴ ∈ unitaryGroup n 𝕜 := by
  have h0 : Uᴴ * U = 1 := by
    apply mem_unitaryGroup_iff'.1
    exact hU
  have h1 : Uᴴ *(Uᴴ)ᴴ = 1 := by
    rw [conjTranspose_conjTranspose,h0];
  apply mem_unitaryGroup_iff.2
  exact h1

/-
  The product of two unitary matrices is also a unitary matrix.
-/
lemma mul_unitary (U1 U2 : Matrix n n 𝕜)
    (hU1 : U1 ∈ unitaryGroup n 𝕜) (hU2 : U2 ∈ unitaryGroup n 𝕜) :
    (U1 * U2) ∈ unitaryGroup n 𝕜 := by
  have h1 : U2 * U2ᴴ  = 1 := by
    apply mem_unitaryGroup_iff.1
    exact hU2
  have h2 : U1 * U1ᴴ = 1 := by
    apply mem_unitaryGroup_iff.1
    exact hU1
  have h3 : (U1 * U2) * (U1 * U2)ᴴ = 1 := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U1, h1, Matrix.mul_one,h2]
  apply mem_unitaryGroup_iff.2
  exact h3

/-
  Each column vector of a unitary matrix has norm 1
-/
lemma unitary_col_norm (hU : U ∈ unitaryGroup n 𝕜) (j : n) :
    ∑ i, ‖U i j‖ ^ 2 = 1 := by
  have h_conjTranspose_mul_eq_one : Uᴴ * U = 1 :=by
      apply mem_unitaryGroup_iff'.1
      exact hU
  have h_col_orthonormal : Orthonormal 𝕜 (U.colVec) :=
    colVec_orthonormal_iff_conjTranspose_mul_eq_one.2 h_conjTranspose_mul_eq_one
  have h_col_norm : ∀ j, ‖U.colVec j‖ = 1 :=
    h_col_orthonormal.1
  calc
    ∑ i, ‖U i j‖ ^ 2 = ‖U.colVec j‖ ^ 2 := by
      simp [Matrix.colVec,PiLp.norm_sq_eq_of_L2 ]
    _ = 1 ^ 2 := by rw [h_col_norm j]
    _ = 1 := by norm_num
/-
  Each row vector of a unitary matrix has norm 1.
-/
lemma unitary_row_norm (hU : U ∈ unitaryGroup n 𝕜) (i : n) :
    ∑ j, ‖U i j‖ ^ 2 = 1 := by
  have h_conjT_unitary : Uᴴ ∈ unitaryGroup n 𝕜 :=
    conjTranspose_unitary U hU
  have h_col_norm : ∑ k, ‖(Uᴴ) k i‖ ^ 2 = 1 :=
    unitary_col_norm h_conjT_unitary i
  simp [Matrix.conjTranspose_apply] at h_col_norm ⊢
  exact h_col_norm

/-
  Singular values are non-negative
-/
lemma singular_value_nonneg {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    [InnerProductSpace 𝕜 (Fin m → 𝕜)] [InnerProductSpace 𝕜 (Fin n → 𝕜)]
    (A : Matrix (Fin m) (Fin n) 𝕜) (i : Fin n) :
    0 ≤ σ A i := by
  unfold singularValues
  dsimp only []
  split_ifs with h
  · simp only [NNReal.coe_nonneg]
  · exact le_refl 0

/-
  Trace of the product of two matrices is invariant under the order of multiplication
-/
@[simp]
lemma trace_mul_comm (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) :
    trace (A * B) = trace (B * A) := by rw [← trace_transpose, ← trace_transpose_mul, transpose_mul]



/-**von Neumann trace inequality**

Let A and B be any two n x n complex matrices, and let σᵢ(A) and σᵢ(B) be their singular values,
arranged in descending order σ₁(A) ≥ σ₂(A) ≥ ... ≥ σ_n(A) and σ₁(B) ≥ σ₂(B) ≥ ... ≥ σ_n(B).
Then ‖tr(A * B)‖ ≤ ∑ᵢ σ(A)ᵢ · σ(B)ᵢ.
-/
theorem von_neumann_trace_inequality_general
  {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
  [InnerProductSpace 𝕜 (Fin n → 𝕜)]
  (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin n) 𝕜)
  (hA_antitone : ∀ i j : Fin n, i ≤ j → σ A j ≤ σ A i)
  (hB_antitone : ∀ i j : Fin n, i ≤ j → σ B j ≤ σ B i) :
  ‖tr (A * B)‖ ≤ ∑ i : Fin n, σ A i * σ B i := by

  by_cases hA : A = 0
  · subst hA ; simp;apply Finset.sum_nonneg;intro i _;
    apply mul_nonneg <;> apply singular_value_nonneg
  by_cases hB : B = 0
  · subst hB;simp;apply Finset.sum_nonneg;intro i _;apply mul_nonneg <;> apply singular_value_nonneg
  -- use singular value decomposition to express A and B
  let rA := finrank 𝕜 (range (Matrix.toLin' A))
  let rB := finrank 𝕜 (range (Matrix.toLin' B))
  rcases Matrix.singular_value_decomposition A rfl with
    ⟨σ_A, U_A, V_A, S_A, hσA_pos, hσA_anti, hU_A, hV_A, hS_def, hA_eq⟩
  rcases Matrix.singular_value_decomposition B rfl with
    ⟨σ_B, U_B, V_B, S_B, hσB_pos, hσB_anti, hU_B, hV_B, hS_def_B, hB_eq⟩
  -- prove that S_A and S_B are diagonal matrices
  have hS_A_diag : ∀ (i : Fin n) (k : Fin n), S_A i k ≠ 0 → i.val = k.val := by
    intro i k h ; rw [hS_def] at h ; split_ifs at h with H
    · simp at H ; exact H.1
    · contradiction
  have hS_B_diag : ∀ (j : Fin n) (l : Fin n), S_B j l ≠ 0 → j.val = l.val := by
    intro j l h ; rw [hS_def_B] at h ; split_ifs at h with H
    · simp at H ; exact H.1
    · contradiction
  -- prove that the diagonal entries of S_A and S_B are the singular values
  have hS_A_diag_vals : ∀ i : Fin n, S_A i i = σ A i := by
    sorry
  have hS_B_diag_vals : ∀ j : Fin n, S_B j j = σ B j := by
    sorry
  -- simplify tr (A * B)
  let C := V_Aᴴ * U_B
  let D := V_Bᴴ * U_A
  have hC_unitary : C ∈ unitaryGroup (Fin n) 𝕜 := by
    have hVh : V_Aᴴ ∈ unitaryGroup (Fin n) 𝕜 := conjTranspose_unitary V_A hV_A
    exact mul_unitary _ _ hVh hU_B
  have hD_unitary : D ∈ unitaryGroup (Fin n) 𝕜 := by
    have hVhB : V_Bᴴ ∈ unitaryGroup (Fin n) 𝕜 := conjTranspose_unitary V_B hV_B
    exact mul_unitary _ _ hVhB hU_A

  have h0: tr (A*B)= tr (U_A*S_A * C * S_B * V_Bᴴ ) := by
    unfold C
    rw [hA_eq, hB_eq,← Matrix.mul_assoc,← Matrix.mul_assoc,Matrix.mul_assoc (U_A * S_A)]
  have h1 : U_A * S_A * C * S_B * V_Bᴴ = U_A * (S_A * C * S_B * V_Bᴴ) := by
   simp [Matrix.mul_assoc]
  have h2 : tr (U_A * (S_A * C * S_B * V_Bᴴ)) = tr (S_A * C * S_B * D) := by
    unfold D
    rw[trace_mul_comm,Matrix.mul_assoc]
  have h_trace_simplified : tr (A * B) = tr (S_A * C * S_B * D) := by
    rw [h0, h1, h2]

  have h_U_A_S_A_C_S_B_V_B_H_elements :∀ i j , (S_A * C * S_B * D) i j=
      ∑ k : Fin n, σ A i * σ B k * (C i k * D k j) := by
      have h_elements : ∀ i j, (S_A * C * S_B * D) i j =
          ∑ k : Fin n, S_A i i * S_B k k * (C i k * D k j) := by
        apply matric_elements n S_A C S_B D hS_A_diag hS_B_diag
      intro i j
      rw [h_elements]
      simp_rw [hS_A_diag_vals, hS_B_diag_vals]

  have h_trace : tr (A * B) = ∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k * (C i k * D k i) := by
    rw [h_trace_simplified]
    simp [Matrix.trace]
    simp_rw [h_U_A_S_A_C_S_B_V_B_H_elements]

  have h1 : ‖∑ i, ∑ k, σ A i * σ B k * (C i k * D k i)‖
      ≤ ∑ i, ‖∑ k, σ A i * σ B k * (C i k * D k i)‖ :=
      norm_sum_le Finset.univ (fun i => ∑ k, σ A i * σ B k * (C i k * D k i))
  have h2 : ∀ i, ‖∑ k, σ A i * σ B k * (C i k * D k i)‖ ≤ ∑ k, ‖σ A i * σ B k * (C i k * D k i)‖ :=
        by intro i; apply norm_sum_le Finset.univ (fun k => σ A i * σ B k * (C i k * D k i))
  have h3 : ∑ i, ‖∑ k, σ A i * σ B k * (C i k * D k i)‖
      ≤ ∑ i, ∑ k, ‖σ A i * σ B k * (C i k * D k i)‖ := Finset.sum_le_sum fun i _ => h2 i
  have h_eq_terms : ∑ i, ∑ k, ‖σ A i * σ B k * (C i k * D k i)‖
      = ∑ i, ∑ k, σ A i * σ B k * ‖C i k * D k i‖ := by
        apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by
          calc
            ‖σ A i * σ B k * (C i k * D k i)‖
              = ‖(σ A i : 𝕜) * ((σ B k : 𝕜) * (C i k * D k i))‖ := by ring_nf
            _ = ‖(σ A i : 𝕜)‖ * ‖(σ B k : 𝕜) * (C i k * D k i)‖ := by rw [norm_mul]
            _ = ‖(σ A i : 𝕜)‖ * (‖(σ B k : 𝕜)‖ * ‖C i k * D k i‖) := by rw [norm_mul]
            _ = (‖(σ A i : 𝕜)‖ * ‖(σ B k : 𝕜)‖) * ‖C i k * D k i‖ := by ring
            _ = (|σ A i| * |σ B k|) * ‖C i k * D k i‖ := by simp [Real.norm_eq_abs]
            _ = (σ A i * σ B k) * ‖C i k * D k i‖ := by
              simp [abs_of_nonneg (singular_value_nonneg A i),
                abs_of_nonneg (singular_value_nonneg B k)]
  have h_norm_bound : ‖∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k * (C i k * D k i)‖ ≤
                    ∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k * ‖C i k * D k i‖ := by
      calc
         ‖∑ i, ∑ k, σ A i * σ B k * (C i k * D k i)‖
            ≤ ∑ i, ‖∑ k, σ A i * σ B k * (C i k * D k i)‖ := h1
         _ ≤ ∑ i, ∑ k, ‖σ A i * σ B k * (C i k * D k i)‖ := h3
         _ = ∑ i, ∑ k, σ A i * σ B k * ‖C i k * D k i‖ := h_eq_terms

  have h_row_sum : ∀ i, ∑ k, ‖C i k * D k i‖ ≤ 1 := by
    intro i
    calc
      ∑ k, ‖C i k * D k i‖ ≤ ∑ k, ‖C i k‖ * ‖D k i‖ :=
         Finset.sum_le_sum (fun k _ => norm_mul_le (C i k) (D k i))
      _ ≤ √(∑ k, ‖C i k‖ ^ 2)  * √(∑ k, ‖D k i‖ ^ 2) := by
        have sum_nonneg : 0 ≤ ∑ k, ‖C i k‖ * ‖D k i‖ :=
         Finset.sum_nonneg fun k _ => by positivity
        have h := cauchy_schwarz_real (fun k => ‖C i k‖) (fun k => ‖D k i‖)
        simp at h ⊢
        rw [abs_of_nonneg sum_nonneg] at h
        exact h
      _ = 1 * 1 := by
        rw [unitary_row_norm hC_unitary i, unitary_col_norm hD_unitary i]
        ring
      _ = 1  := by norm_num
  have h_col_sum : ∀ k, ∑ i, ‖C i k * D k i‖ ≤ 1 := by
    intro k
    calc
      ∑ i, ‖C i k * D k i‖ ≤ ∑ i, ‖C i k‖ * ‖D k i‖ :=
         Finset.sum_le_sum (fun i _ => norm_mul_le (C i k) (D k i))
      _ ≤ √(∑ i, ‖C i k‖ ^ 2)  * √(∑ i, ‖D k i‖ ^ 2) := by
        have sum_nonneg : 0 ≤ ∑ i, ‖C i k‖ * ‖D k i‖ :=
         Finset.sum_nonneg fun i _ => by positivity
        have h := cauchy_schwarz_real (fun i => ‖C i k‖) (fun i => ‖D k i‖)
        simp at h ⊢
        rw [abs_of_nonneg sum_nonneg] at h
        exact h
      _ = 1 * 1 := by
        rw [unitary_col_norm hC_unitary k, unitary_row_norm hD_unitary k]
        ring
      _ = 1  := by norm_num

  -- Now we have |tr(A * B)| ≤ ∑ i ∑ k σ(A)ᵢ * σ(B)ₖ * ‖Cᵢₖ * Dₖᵢ‖
  -- let N be the matrix with entries N i k = ‖C i k * D k i‖
  -- then we have  N is doubly sub-stochastic
  -- the private theorem `exists_doubly_stochastic_above_substochastic` guarantees the existence
  -- of a doubly stochastic matrix M such that N i k ≤ M i k for all i, k
  -- thus we have |tr(A * B)| ≤ ∑ i ∑ k σ(A)ᵢ * σ(B)ₖ * Mᵢₖ
  -- let f = ∑ i ∑ k σ(A)ᵢ * σ(B)ₖ * Sᵢₖ where S is a doubly stochastic matrix,f is
  -- a linear function
  -- the lemma `isCompact_doublyStochastic` and `convex_doublyStochastic` show that the set
  -- of doubly stochastic matrices is a compact convex set
  -- the lemma `exists_max_at_extreme_point_of_compact_convex_linear` guarantees the existence
  -- of a maximizer for f over the set of doubly stochastic matrices at an extreme point of the set
  -- the lemma `extremePoints_doublyStochastic` shows that the extreme points of the set
  -- of doubly stochastic matrices are permutation matrices
  -- so we have the maximum value of f over the set of doubly stochastic matrices is
  -- ∑ i σ(A)ᵢ * σ(B)_{π(i)} for some permutation π
  -- then |tr(A * B)| ≤ ∑ i σ(A)ᵢ * σ(B)_{π(i)}
  -- finally, we apply the rearrangement inequality for antitone sequences to conclude that
  -- ∑ i σ(A)ᵢ * σ(B)_{π(i)} ≤ ∑ i σ(A)ᵢ * σ(B)ᵢ
  -- thus we complete the proof

  let N : Matrix (Fin n) (Fin n) ℝ := fun i k => ‖C i k * D k i‖
  have hN_pos : ∀ i k, 0 ≤ N i k := fun i k => by
    simp [N]
    apply mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hN_row_sum : ∀ i, ∑ k, N i k ≤ 1 := h_row_sum
  have hN_col_sum : ∀ k, ∑ i, N i k ≤ 1 := h_col_sum
  have hN_doubly_substochastic : DoublySubStochastic N :=
    ⟨hN_pos, hN_row_sum, hN_col_sum⟩

  obtain ⟨M, hM_doubly_stochastic, hM_bound⟩ :=
    exists_doubly_stochastic_above_substochastic hN_doubly_substochastic
  have h_bounded_1 : ∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k * ‖C i k * D k i‖ ≤
                   ∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k * M i k := by
   refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
   calc
     σ A i * σ B k * ‖C i k * D k i‖ = σ A i * σ B k * N i k := by simp [N]
     _ ≤ σ A i * σ B k * M i k := by
      refine mul_le_mul_of_nonneg_left (hM_bound i k) ?_
      exact mul_nonneg (singular_value_nonneg A i) (singular_value_nonneg B k)

  let f : Matrix (Fin n) (Fin n) ℝ → ℝ := fun S => ∑ i, ∑ k, σ A i * σ B k * S i k
  have h_linear' : IsLinearMap ℝ f := by
    constructor
    · --  f(S + T) = f(S) + f(T)
      simp [f]; intro S T ; ring_nf ; simp [Finset.sum_add_distrib]
    · --  f(c • S) = c • f(S)
      intro c S; simp [f]; ring_nf; simp [Finset.mul_sum]; congr; ext x; congr; ext x_1; ring

  have h_max_at_permutation : ∃ (π : Equiv.Perm (Fin n)),
      ∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k * M i k ≤ ∑ i : Fin n, σ A i * σ B (π i) := by

    have h_compact : IsCompact (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)) :=
      isCompact_doublyStochastic
    have h_convex : Convex ℝ (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)) :=
      convex_doublyStochastic
    rcases exists_max_at_extreme_point_of_compact_convex_linear h_compact h_convex h_linear' with
      ⟨P, hP_extreme, hP_max⟩

    rw [extremePoints_doublyStochastic] at hP_extreme
    rcases hP_extreme with ⟨π, rfl⟩

    have h_f_at_perm : f (π.permMatrix ℝ) = ∑ i : Fin n, σ A i * σ B (π i) := by
      simp [f, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply]
    refine ⟨π, ?_⟩
    calc
      ∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k * M i k = f M := by simp [f]
      _ ≤ f (π.permMatrix ℝ) := hP_max M hM_doubly_stochastic
      _ = ∑ i : Fin n, σ A i * σ B (π i) := h_f_at_perm

  rcases h_max_at_permutation with ⟨π, hπ_max⟩
  have h_bounded_2:∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k *‖C i k * D k i‖
      ≤ ∑ i : Fin n, σ A i * σ B (π i) := by
    apply le_trans h_bounded_1  hπ_max
  have h_final_1 : ∑ i : Fin n, σ A i * σ B (π i) ≤ ∑ i : Fin n, σ A i * σ B i := by
    exact rearrangement_ineq_antitone (σ A) (σ B) π hA_antitone hB_antitone
  have h_final : ‖tr (A * B)‖ ≤ ∑ i : Fin n, σ A i * σ B i := by
    calc
      ‖tr (A * B)‖ ≤ ∑ i : Fin n, ∑ k : Fin n, σ A i * σ B k * ‖C i k * D k i‖ := by
        rw [h_trace]
        exact h_norm_bound
      _ ≤ ∑ i : Fin n, σ A i * σ B (π i) := h_bounded_2
      _ ≤ ∑ i : Fin n, σ A i * σ B i := h_final_1
  exact h_final

end von_neumann
end von_neumann
end Matrix
