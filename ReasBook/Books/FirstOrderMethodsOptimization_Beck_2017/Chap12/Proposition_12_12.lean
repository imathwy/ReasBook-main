import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_19
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)

open EuclideanSpace
open WithLp (toLp ofLp)

/- Proposition 12.12 is `source-facing`: it computes the proximal mapping of the second split
total-variation block `g₂` introduced in Proposition 12.11.

Domain sampling against the existing chapter API identifies:

- `core/canonical`: `prox[...]` from Chapter 6 and
  `one_dimensional_total_variation_odd_edge_penalty` from Proposition 12.11;
- `bridge/view`: Proposition 12.10's pairwise two-coordinate shrinkage formula, used here through
  `pair_difference_prox_correction` on each odd-start pair `(1,2), (3,4), ...`;
- the finite Euclidean product `EuclideanSpace ℝ (Fin n)` as the chapter's canonical realization
  of `ℝ^n`.

Primitive data are therefore only the existing split-block owner and the pairwise correction.
This file removes the duplicated local two-coordinate and odd-start penalty owners, and keeps only
the new explicit proximal point plus the singleton proximal formula for that canonical owner. -/

private def oddEdgeProxSummand (lam : PosReal) (x : En) (i : Fin ((n - 1) / 2)) : En :=
  let e := one_dimensional_total_variation_odd_edge i
  let l := one_dimensional_total_variation_edge_left e
  let r := one_dimensional_total_variation_edge_right e
  pair_difference_prox_correction lam
      (x l)
      (x r) •
    ((single l (1 : ℝ) : En) - single r (1 : ℝ))

/-- The explicit proximal point obtained by applying the two-coordinate shrinkage independently to
all odd-start adjacent pairs `(1,2), (3,4), ...` and leaving the remaining coordinates fixed. -/
def one_dimensional_total_variation_odd_edge_prox_point (lam : PosReal) (x : En) : En :=
  x + ∑ i : Fin ((n - 1) / 2), oddEdgeProxSummand lam x i

-- Proof sketch: unfold `one_dimensional_total_variation_odd_edge_prox_point`; the right-hand side
-- is exactly
-- the sum of the pairwise corrections along the basis differences
-- `e_(2 i + 1) - e_(2 i + 2)`.
/-- Expanding `one_dimensional_total_variation_odd_edge_prox_point` gives the explicit sum of the
odd-start pairwise shrinkage corrections. -/
@[simp] theorem one_dimensional_total_variation_odd_edge_prox_point_eq (lam : PosReal) (x : En) :
    one_dimensional_total_variation_odd_edge_prox_point lam x =
      x +
        ∑ i : Fin ((n - 1) / 2),
          let e := one_dimensional_total_variation_odd_edge i
          let l := one_dimensional_total_variation_edge_left e
          let r := one_dimensional_total_variation_edge_right e
          pair_difference_prox_correction lam
              (x l)
              (x r) •
            ((single l (1 : ℝ) : En) - single r (1 : ℝ)) :=
  rfl

/-- Helper for Proposition 12.12: after dropping the first coordinate of a vector in
`ℝ^(n+1)`, the odd-edge penalty becomes the even-edge penalty on the tail coordinates. -/
theorem one_dimensional_total_variation_odd_edge_penalty_eq_even_edge_penalty_tail
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam x =
      one_dimensional_total_variation_even_edge_penalty (n := n) lam (toLp 2 (Fin.tail x)) := by
  -- Expand both penalties and identify the same adjacent differences after the index shift.
  rw [one_dimensional_total_variation_odd_edge_penalty_apply,
    one_dimensional_total_variation_even_edge_penalty_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [one_dimensional_total_variation_difference_operator_apply_edge,
    one_dimensional_total_variation_difference_operator_apply_edge]
  have hleft :
      one_dimensional_total_variation_edge_left
          (one_dimensional_total_variation_odd_edge (n := n + 1) i) =
        (one_dimensional_total_variation_edge_left
          (one_dimensional_total_variation_even_edge (n := n) i)).succ := by
    apply Fin.ext
    simp [one_dimensional_total_variation_odd_edge, one_dimensional_total_variation_even_edge]
  have hright :
      one_dimensional_total_variation_edge_right
          (one_dimensional_total_variation_odd_edge (n := n + 1) i) =
        (one_dimensional_total_variation_edge_right
          (one_dimensional_total_variation_even_edge (n := n) i)).succ := by
    apply Fin.ext
    simp [one_dimensional_total_variation_odd_edge, one_dimensional_total_variation_even_edge]
  rw [hleft, hright]
  simp [Fin.tail]

/-- Helper for Proposition 12.12: on `ℝ^(n+1)`, the odd-edge proximal point keeps the first
coordinate and applies the even-edge proximal point to the tail coordinates. -/
theorem one_dimensional_total_variation_odd_edge_prox_point_eq_cons_even_edge_prox_point
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    one_dimensional_total_variation_odd_edge_prox_point (n := n + 1) lam x =
      toLp 2
        (Fin.cons (x 0)
          (one_dimensional_total_variation_even_edge_prox_point (n := n) lam
            (toLp 2 (Fin.tail x)))) := by
  -- Compare coordinates: the odd-edge correction never touches index `0`, and on the tail it is
  -- exactly the even-edge correction from Proposition 12.11 after shifting the indices.
  ext j
  refine Fin.cases ?_ ?_ j
  · rw [one_dimensional_total_variation_odd_edge_prox_point_eq]
    simp only [Fin.cons_zero]
    have hsum :
        ∑ i : Fin ((n + 1 - 1) / 2),
            (let e := one_dimensional_total_variation_odd_edge i
             let l := one_dimensional_total_variation_edge_left e
             let r := one_dimensional_total_variation_edge_right e
             pair_difference_prox_correction lam (x l) (x r) •
               ((single l (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 1))) - single r (1 : ℝ))) 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hleft_ne :
          one_dimensional_total_variation_edge_left
              (one_dimensional_total_variation_odd_edge (n := n + 1) i) ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [one_dimensional_total_variation_odd_edge] at hval
      have hright_ne :
          one_dimensional_total_variation_edge_right
              (one_dimensional_total_variation_odd_edge (n := n + 1) i) ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [one_dimensional_total_variation_odd_edge] at hval
      simp [hleft_ne, hright_ne]
    simpa using hsum
  · intro j
    rw [one_dimensional_total_variation_odd_edge_prox_point_eq,
      one_dimensional_total_variation_even_edge_prox_point_eq]
    simp [Fin.cons, Fin.tail]
    congr 2
    funext i
    have hleft :
        one_dimensional_total_variation_edge_left
            (one_dimensional_total_variation_odd_edge (n := n + 1) i) =
          (one_dimensional_total_variation_edge_left
            (one_dimensional_total_variation_even_edge (n := n) i)).succ := by
      apply Fin.ext
      simp [one_dimensional_total_variation_odd_edge, one_dimensional_total_variation_even_edge]
    have hright :
        one_dimensional_total_variation_edge_right
            (one_dimensional_total_variation_odd_edge (n := n + 1) i) =
          (one_dimensional_total_variation_edge_right
            (one_dimensional_total_variation_even_edge (n := n) i)).succ := by
      apply Fin.ext
      simp [one_dimensional_total_variation_odd_edge, one_dimensional_total_variation_even_edge]
    rw [hleft, hright]
    congr 1
    simp [Pi.single_apply]

/-- Helper for Proposition 12.12: the odd-edge proximal point fixes the head coordinate. -/
@[simp] theorem one_dimensional_total_variation_odd_edge_prox_point_zero
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    one_dimensional_total_variation_odd_edge_prox_point (n := n + 1) lam x 0 = x 0 := by
  -- Read the head coordinate from the explicit `Fin.cons` decomposition.
  rw [one_dimensional_total_variation_odd_edge_prox_point_eq_cons_even_edge_prox_point
    (n := n) lam x]
  simp

/-- Helper for Proposition 12.12: the tail of the odd-edge proximal point is exactly the
even-edge proximal point of the tail data. -/
@[simp] theorem one_dimensional_total_variation_tail_odd_edge_prox_point
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    toLp 2 (Fin.tail (one_dimensional_total_variation_odd_edge_prox_point (n := n + 1) lam x)) =
      one_dimensional_total_variation_even_edge_prox_point (n := n) lam (toLp 2 (Fin.tail x)) := by
  -- Apply `Fin.tail` to the `Fin.cons` decomposition to remove the untouched head coordinate.
  simpa using congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) ↦ toLp 2 (Fin.tail y))
    (one_dimensional_total_variation_odd_edge_prox_point_eq_cons_even_edge_prox_point
      (n := n) lam x)

/-- Helper for Proposition 12.12: in `ℝ^(n+1)`, the squared Euclidean distance splits into the
head-coordinate contribution and the squared norm of the tail difference. -/
theorem one_dimensional_total_variation_tail_norm_sq_split
    (x u : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖u - x‖ ^ (2 : ℕ) =
      (u 0 - x 0) ^ (2 : ℕ) +
        ‖(toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))‖ ^ (2 : ℕ) := by
  -- Expand the squared norm as the sum of squared coordinates and separate the head term.
  have hfull := EuclideanSpace.real_norm_sq_eq (u - x)
  have htail := EuclideanSpace.real_norm_sq_eq ((toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x)))
  rw [Fin.sum_univ_succ] at hfull
  calc
    ‖u - x‖ ^ (2 : ℕ) = (u - x) 0 ^ (2 : ℕ) + ∑ i : Fin n, (u - x) i.succ ^ (2 : ℕ) := by
      simpa using hfull
    _ = (u 0 - x 0) ^ (2 : ℕ) +
          ∑ i : Fin n, ((toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))) i ^ (2 : ℕ) := by
      simp [Fin.tail, sub_eq_add_neg, pow_two, add_comm]
    _ = (u 0 - x 0) ^ (2 : ℕ) +
          ‖(toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))‖ ^ (2 : ℕ) := by
      rw [← htail]

/-- Helper for Proposition 12.12: in `ℝ^(n+1)`, the proximal objective of the odd-edge penalty
splits into the even-edge proximal objective on the tail plus the scalar quadratic term for the
first coordinate. -/
theorem one_dimensional_total_variation_odd_edge_proximal_objective_split
    (lam : PosReal) (x u : EuclideanSpace ℝ (Fin (n + 1))) :
    proximal_objective (one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam) x u =
      proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
          (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) +
        ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Rewrite the odd penalty through the tail and split the quadratic term coordinatewise.
  rw [proximal_objective_apply, proximal_objective_apply,
    one_dimensional_total_variation_odd_edge_penalty_eq_even_edge_penalty_tail]
  have hnorm :
      ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        ((((1 / 2 : ℝ) * ‖(toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))‖ ^ (2 : ℕ)) : ℝ) :
          EReal) +
          ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
    exact_mod_cast (show
      (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ‖(toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ) by
      nlinarith [one_dimensional_total_variation_tail_norm_sq_split x u])
  rw [hnorm]
  simp [add_assoc]

/-- Helper for Proposition 12.12: specializing the odd-edge objective split to an explicit
`Fin.cons` vector records the source-proof decomposition into a free head coordinate and the even
tail problem. -/
theorem one_dimensional_total_variation_odd_edge_proximal_objective_cons
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) (a : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    proximal_objective (one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam) x
        (toLp 2 (Fin.cons a z)) =
      proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
          (toLp 2 (Fin.tail x)) z +
        ((((1 / 2 : ℝ) * (a - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Specialize the tail-splitting identity to the explicit `head :: tail` reconstruction.
  simpa using
    (one_dimensional_total_variation_odd_edge_proximal_objective_split
      (n := n) lam x (toLp 2 (Fin.cons a z)))

/-- Helper for Proposition 12.12: resetting the head coordinate to `x 0` removes the scalar
quadratic term from the odd-edge objective split. -/
@[simp] theorem one_dimensional_total_variation_odd_edge_proximal_objective_cons_head
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) (z : EuclideanSpace ℝ (Fin n)) :
    proximal_objective (one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam) x
        (toLp 2 (Fin.cons (x 0) z)) =
      proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
          (toLp 2 (Fin.tail x)) z := by
  -- The added scalar correction vanishes because the reconstructed vector keeps the original head.
  rw [one_dimensional_total_variation_odd_edge_proximal_objective_cons]
  simp

/-- Helper for Proposition 12.12: odd-edge proximal membership factorizes into the untouched head
coordinate and the even-edge proximal problem on the tail block. -/
theorem mem_prox_one_dimensional_total_variation_odd_edge_penalty_iff_head_eq_tail_mem
    (lam : PosReal) (x u : EuclideanSpace ℝ (Fin (n + 1))) :
    u ∈ prox[one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam] x ↔
      u 0 = x 0 ∧
        toLp 2 (Fin.tail u) ∈
          prox[one_dimensional_total_variation_even_edge_penalty (n := n) lam]
            (toLp 2 (Fin.tail x)) := by
  constructor
  · intro hu
    have htail_min :
        toLp 2 (Fin.tail u) ∈
          prox[one_dimensional_total_variation_even_edge_penalty (n := n) lam]
            (toLp 2 (Fin.tail x)) := by
      -- Freeze the head coordinate at `x 0` and compare only the tail competitors.
      rw [mem_proximal_mapping_iff] at hu ⊢
      rw [isMinOn_univ_iff] at hu ⊢
      intro z
      let v : EuclideanSpace ℝ (Fin (n + 1)) := toLp 2 (Fin.cons (x 0) z)
      have huv := hu v
      have hu_split :=
        one_dimensional_total_variation_odd_edge_proximal_objective_split
          (n := n) lam x u
      have hv_split :
          proximal_objective
              (one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam) x v =
            proximal_objective
                (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
                (toLp 2 (Fin.tail x)) z := by
        simpa [v] using
          (one_dimensional_total_variation_odd_edge_proximal_objective_cons_head
            (n := n) lam x z)
      have hhead_nonneg :
          (0 : EReal) ≤ ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
        positivity
      rw [hu_split, hv_split] at huv
      have hdrop :
          proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
              (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) ≤
            proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
              (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) +
                ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
        simpa using le_add_of_nonneg_right hhead_nonneg
      exact le_trans hdrop huv
    have hhead : u 0 = x 0 := by
      -- Reset only the head coordinate; minimality forces the extra scalar term to vanish.
      let v : EuclideanSpace ℝ (Fin (n + 1)) := toLp 2 (Fin.cons (x 0) (Fin.tail u))
      have huv :
          proximal_objective
              (one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam) x u ≤
            proximal_objective
              (one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam) x v := by
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
        exact hu v
      have hu_split :=
        one_dimensional_total_variation_odd_edge_proximal_objective_split
          (n := n) lam x u
      have hv_split :
          proximal_objective
              (one_dimensional_total_variation_odd_edge_penalty (n := n + 1) lam) x v =
            proximal_objective
                (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
                (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) := by
        simpa [v] using
          (one_dimensional_total_variation_odd_edge_proximal_objective_cons_head
            (n := n) lam x (toLp 2 (Fin.tail u)))
      rw [hu_split, hv_split] at huv
      have hnonneg :
          (0 : EReal) ≤ ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
        positivity
      obtain ⟨r, hr⟩ :=
        one_dimensional_total_variation_even_edge_proximal_objective_eq_coe
          (n := n) lam (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u))
      have hsum_le : r + (1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ) ≤ r := by
        rw [hr] at huv
        exact_mod_cast huv
      have hle_zero :
          ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) ≤ 0 := by
        have hle_zero_real : (1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ) ≤ 0 := by
          linarith
        exact_mod_cast hle_zero_real
      have hzero :
          ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) = 0 :=
        le_antisymm hle_zero hnonneg
      have hzero_real : (1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ) = 0 := by
        exact_mod_cast hzero
      have hsq : (u 0 - x 0) ^ (2 : ℕ) = 0 := by
        linarith
      have hsub : u 0 - x 0 = 0 := by
        exact eq_zero_of_pow_eq_zero hsq
      linarith
    exact ⟨hhead, htail_min⟩
  · rintro ⟨hhead, htail_min⟩
    rw [mem_proximal_mapping_iff]
    rw [isMinOn_univ_iff]
    intro v
    -- Compare the split odd objective against the minimized tail objective and the nonnegative
    -- scalar head correction.
    have hsplit_u :=
      one_dimensional_total_variation_odd_edge_proximal_objective_split
        (n := n) lam x u
    have hsplit_v :=
      one_dimensional_total_variation_odd_edge_proximal_objective_split
        (n := n) lam x v
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at htail_min
    rw [hsplit_u, hsplit_v]
    have htail_le := htail_min (toLp 2 (Fin.tail v))
    have hhead_zero :
        ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) = 0 := by
      simp [hhead]
    have hhead_nonneg :
        (0 : EReal) ≤ ((((1 / 2 : ℝ) * (v 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
      positivity
    have htail_le' :
        proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
            (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) +
            ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) ≤
          proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
            (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail v)) := by
      rw [hhead_zero]
      simpa using htail_le
    calc
      proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
          (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) +
          ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal)
          ≤
        proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
          (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail v)) := htail_le'
      _ ≤
        proximal_objective (one_dimensional_total_variation_even_edge_penalty (n := n) lam)
          (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail v)) +
          ((((1 / 2 : ℝ) * (v 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) :=
            le_add_of_nonneg_right hhead_nonneg

-- Route correction: keep the textbook tail-reduction route through the even-edge problem on
-- `Fin.tail x`, and package the `Fin.cons` specialization explicitly instead of adding a new
-- block-separable transport layer in this file.
-- Proof sketch: use the separability of `one_dimensional_total_variation_odd_edge_penalty lam`
-- across the
-- disjoint odd-start adjacent pairs, apply
-- `prox_pair_difference_penalty_eq_singleton` on each two-coordinate block, and observe that all
-- untouched coordinates remain fixed.
/-- Proposition 12.12: for the split total-variation block
`g₂(x) = λ ∑ |x_(2 i + 1) - x_(2 i + 2)|`, realized on `Fin n` as the odd-start adjacent pairs
`(1,2), (3,4), ...`, the proximal mapping is the singleton containing the point obtained by the
explicit pairwise shrinkage formula on each such pair, for the chapter's positive parameter
`lam : PosReal`. -/
theorem prox_one_dimensional_total_variation_odd_edge_penalty_eq_singleton
    (lam : PosReal) (x : En) :
    prox[one_dimensional_total_variation_odd_edge_penalty lam] x =
      {one_dimensional_total_variation_odd_edge_prox_point lam x} := by
  cases n with
  | zero =>
      -- With no coordinates, the odd-edge penalty is identically zero and the proximal map fixes
      -- the unique point.
      have hpen0 :
          one_dimensional_total_variation_odd_edge_penalty (n := 0) lam =
            (0 : EuclideanSpace ℝ (Fin 0) → EReal) := by
        funext u
        simp [one_dimensional_total_variation_odd_edge_penalty_apply]
      calc
        prox[one_dimensional_total_variation_odd_edge_penalty (n := 0) lam] x = {x} := by
          rw [hpen0]
          simpa using prox_zero_eq_singleton x
        _ = {one_dimensional_total_variation_odd_edge_prox_point (n := 0) lam x} := by
          congr 1
          simp [one_dimensional_total_variation_odd_edge_prox_point_eq]
  | succ n =>
      -- Reduce the odd-edge problem on `ℝ^(n+1)` to the even-edge problem on the tail.
      ext u
      constructor
      · intro hu
        rw [Set.mem_singleton_iff]
        have hu_factor :
            u 0 = x 0 ∧
            toLp 2 (Fin.tail u) ∈
              prox[one_dimensional_total_variation_even_edge_penalty (n := n) lam]
                (toLp 2 (Fin.tail x)) := by
          exact
            (mem_prox_one_dimensional_total_variation_odd_edge_penalty_iff_head_eq_tail_mem
              (n := n) lam x u).1 hu
        rcases hu_factor with ⟨hhead, htail_min⟩
        have htail_eq :
            toLp 2 (Fin.tail u) =
              one_dimensional_total_variation_even_edge_prox_point (n := n) lam
                (toLp 2 (Fin.tail x)) := by
          rw [prox_one_dimensional_total_variation_even_edge_penalty_eq_singleton
            (n := n) lam (toLp 2 (Fin.tail x))] at htail_min
          simpa using htail_min
        calc
          u =
              toLp 2
                (Fin.cons (x 0)
                  (one_dimensional_total_variation_even_edge_prox_point (n := n) lam
                    (toLp 2 (Fin.tail x)))) := by
            ext j
            refine Fin.cases ?_ ?_ j
            · simpa using hhead
            · intro j
              simpa [hhead] using congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) htail_eq
          _ = one_dimensional_total_variation_odd_edge_prox_point (n := n + 1) lam x := by
            symm
            exact one_dimensional_total_variation_odd_edge_prox_point_eq_cons_even_edge_prox_point
              (n := n) lam x
      · intro hu
        rw [Set.mem_singleton_iff] at hu
        subst hu
        apply
          (mem_prox_one_dimensional_total_variation_odd_edge_penalty_iff_head_eq_tail_mem
            (n := n) lam x
            (one_dimensional_total_variation_odd_edge_prox_point (n := n + 1) lam x)).2
        have htail_min :
            toLp 2
                (Fin.tail
                  (one_dimensional_total_variation_odd_edge_prox_point (n := n + 1) lam x)) ∈
              prox[one_dimensional_total_variation_even_edge_penalty (n := n) lam]
                (toLp 2 (Fin.tail x)) := by
          rw [one_dimensional_total_variation_tail_odd_edge_prox_point (n := n) lam x]
          rw [prox_one_dimensional_total_variation_even_edge_penalty_eq_singleton
            (n := n) lam (toLp 2 (Fin.tail x))]
          simp
        have hhead :
            one_dimensional_total_variation_odd_edge_prox_point (n := n + 1) lam x 0 = x 0 := by
          -- The decomposition theorem already records that the head coordinate is unchanged.
          simpa using one_dimensional_total_variation_odd_edge_prox_point_zero (n := n) lam x
        exact ⟨hhead, htail_min⟩

end
