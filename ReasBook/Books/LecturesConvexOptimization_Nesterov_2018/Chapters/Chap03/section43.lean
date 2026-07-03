import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_43 (from Chap03) -/
universe u v w

variable {Q : Type u} {ι : Type v} {α : Type w}

/-
Definition 3.43 lies in the family sublevel-set / inequality-feasibility domain.

Sampled owner-style declarations:
- `𝓛[f](a)`, `mem_levelSet_iff`, and `levelSet_eq_setOf` in `Chap01/Definition_1_4_8`, the
  project owner for a single sublevel set;
- mathlib `Set.Iic` and `Set.preimage`, the canonical lower-interval and preimage presentation of
  a pointwise inequality `f x ≤ a`;
- `inequalityConstrainedFeasibleSet` and `mem_inequalityConstrainedFeasibleSet_iff` in
  `Chap03/Theorem_3_1_26`, the specialized finite real `≤ 0` owner used elsewhere in Chapter 3;
- `constraintInequalities_eq_aggregateConstraintSublevelSet` in `Chap03/Definition_3_42`, the
  finite real bridge from coordinatewise inequalities to a single aggregate constraint.

Best owner abstraction:
- the source-facing owner `extendedFeasibleSet`, stated directly at the comparison level
  `constraints j x ≤ ε`;
- the Chapter 3 finite real `≤ 0` feasible-set owner only as a specialized bridge.

Primitive data:
- the constraint family `ι → Q → α`;
- the threshold `ε : α`;
- the preorder structure on the comparison codomain.

Derived API:
- the source-facing extended feasible-set notation `𝓕[constraints](ε) = {x | ∀ j, fⱼ(x) ≤ ε}`;
- the membership equivalence `x ∈ 𝓕[constraints](ε) ↔ ∀ j, constraints j x ≤ ε`.

Source/core/bridge triage:
- source-facing: `extendedFeasibleSet`;
- core/canonical: the family of lower sublevel predicates `constraints j x ≤ ε`;
- bridge/view: `mem_extendedFeasibleSet_iff` and the finite real specialization
  `extendedFeasibleSet_eq_inequalityConstrainedFeasibleSet`.

The source notion is purely about feasibility, not optimization data. The refined file therefore
keeps `extendedFeasibleSet` as the source-facing owner and states it directly at the natural
comparison level `fⱼ(x) ≤ ε` for an arbitrary index type and preorder codomain. The earlier
finite real `≤ 0` Chapter 3 owner remains available only as a bridge theorem rather than as the
defining primitive body.
-/

section

variable [Preorder α]
variable (constraints : ι → Q → α) (ε : α)

/-- Definition 3.43: for a domain `Q`, a family of constraint functions `fⱼ : Q → α`, and a
threshold `ε : α`, the extended feasible set consists of the points `x : Q` such that every
constraint value satisfies `fⱼ(x) ≤ ε`. Its Lean surface notation is `𝓕[constraints](ε)`. -/
def extendedFeasibleSet : Set Q :=
  {x | ∀ j : ι, constraints j x ≤ ε}

end

namespace ExtendedFeasibleSetNotation

/- Source-facing Lean notation for the extended feasible set, with the constraint family kept
explicit in the surface syntax. -/
scoped notation:max "𝓕[" constraints:arg "](" ε:arg ")" =>
  extendedFeasibleSet constraints ε

end ExtendedFeasibleSetNotation

open scoped ExtendedFeasibleSetNotation

section

variable [Preorder α]
variable (constraints : ι → Q → α) (ε : α)

/-- Membership in the extended feasible set at tolerance `ε` is exactly the coordinatewise
inequality family `fⱼ(x) ≤ ε`. -/
@[simp] theorem mem_extendedFeasibleSet_iff {x : Q} :
    x ∈ 𝓕[constraints](ε) ↔ ∀ j : ι, constraints j x ≤ ε :=
  Iff.rfl

end

section

variable {m : ℕ}
variable (constraints : Fin m → Q → ℝ) (ε : ℝ)

/-- For finite real-valued constraints, the source-facing extended feasible set is exactly the
Chapter 3 feasible-set owner applied to the shifted family `x ↦ fⱼ(x) - ε` on `Set.univ`. -/
theorem extendedFeasibleSet_eq_inequalityConstrainedFeasibleSet :
    𝓕[constraints](ε) =
      inequalityConstrainedFeasibleSet Set.univ (fun j x ↦ constraints j x - ε) := by
  ext x
  simp [extendedFeasibleSet, inequalityConstrainedFeasibleSet]

end

/-! ### Proposition_3_43 (from Chap03) -/
open MeasureTheory

/- Proposition 3.43 lies in the chapter's midpoint-bisection box geometry domain.

Sampled owner-style declarations before refinement:
* mathlib `midpoint ℝ` and `pi_midpoint_apply`, the canonical affine midpoint owner for coordinate
  updates;
* mathlib `Real.volume_Icc_pi_toReal`, the owner formula for the volume of a coordinate box;
* project `FeasibilityResistingOracleState.currentLower` / `currentUpper` in `Algorithm_3_5`,
  whose recursive box transcript already uses the canonical midpoint owner.

Best owner abstraction:
* source-facing: midpoint bisection of one coordinate interval of a box and the resulting
  box-volume / side-length consequences;
* core/canonical: `midpoint ℝ` for the bisected endpoint and `Real.volume_Icc_pi_toReal` for box
  volume;
* bridge/view: the finite-block coverage predicate used only for the `n`-step consequence.

Primitive data:
* one box `Set.Icc a b`
* one chosen coordinate `i`
* one midpoint coordinate bisection step from `(a, b)` to `(a', b')`

Derived API:
* the exact side-length update at the bisected coordinate
* the resulting one-step volume-halving consequence
* the `n`-step side-length consequence under the block-coverage schedule hypothesis

This refinement keeps Proposition 3.43 source-facing, but removes the local arithmetic duplicate
of the midpoint construction and states the one-step volume theorem directly on the primitive
single-step box data instead of a packaged whole-sequence wrapper. -/

/-- A midpoint coordinate bisection step keeps one half of the `i`-th coordinate interval of the
box `Set.Icc a b` and leaves all other coordinates unchanged. The updated endpoint is expressed
through the canonical affine midpoint owner `midpoint ℝ`. -/
def IsMidpointCoordinateBisectionStep
    {n : ℕ} (a b a' b' : Fin n → ℝ) (i : Fin n) : Prop :=
  let midpointBox := midpoint ℝ a b
  (a' = a ∧ b' = Function.update b i (midpointBox i)) ∨
    (a' = Function.update a i (midpointBox i) ∧ b' = b)

/-- In a midpoint coordinate bisection step, the length of the bisected coordinate interval is
exactly halved. -/
-- Proof sketch: split into the two cases in `IsMidpointCoordinateBisectionStep`; in each case,
-- evaluate the updated endpoint at `i` and simplify the resulting difference.
theorem midpointCoordinateBisectionStep_halvedCoordinateLength
    {n : ℕ} {a b a' b' : Fin n → ℝ} {i : Fin n}
    (h : IsMidpointCoordinateBisectionStep a b a' b' i) :
    b' i - a' i = (b i - a i) / 2 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [pi_midpoint_apply, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, div_eq_mul_inv,
      mul_add]
    ring_nf
  · simp [pi_midpoint_apply, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, div_eq_mul_inv,
      mul_add]
    ring_nf

/-- In a midpoint coordinate bisection step, the side-length vector is unchanged away from the
bisected coordinate and is updated at that coordinate by the halved length. -/
theorem midpointCoordinateBisectionStep_sideLengths_eq_update
    {n : ℕ} {a b a' b' : Fin n → ℝ} {i : Fin n}
    (h : IsMidpointCoordinateBisectionStep a b a' b' i) :
    b' - a' = Function.update (b - a) i ((b i - a i) / 2) := by
  ext j
  by_cases hj : j = i
  · subst hj
    simpa [Function.update_self] using midpointCoordinateBisectionStep_halvedCoordinateLength h
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hj]

/-- Every coordinate direction is selected at least once in each block of `n` consecutive
midpoint bisection steps. -/
def BisectionBlockCoversAllCoordinates
    (n : ℕ) (bisectedCoordinate : ℕ → Fin n) : Prop :=
  ∀ k (i : Fin n), ∃ t ∈ Finset.Icc k (k + n - 1), bisectedCoordinate t = i

/-- In any block of `n` consecutive midpoint bisection steps satisfying the block-coverage
hypothesis, the coordinate-selection map is a permutation of `Fin n`. -/
theorem bisectionBlockCoordinates_bijective
    {n : ℕ} (bisectedCoordinate : ℕ → Fin n)
    (hcover : BisectionBlockCoversAllCoordinates n bisectedCoordinate)
    (k : ℕ) :
    Function.Bijective (fun t : Fin n ↦ bisectedCoordinate (k + t)) := by
  cases n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n =>
      have hsurj :
          Function.Surjective (fun t : Fin (n + 1) ↦ bisectedCoordinate (k + t)) := by
        intro i
        rcases hcover k i with ⟨t, ht, hti⟩
        have htk : k ≤ t := (Finset.mem_Icc.mp ht).1
        have htn : t < k + (n + 1) := by
          have htn' : t ≤ k + (n + 1) - 1 := (Finset.mem_Icc.mp ht).2
          omega
        refine ⟨⟨t - k, by omega⟩, ?_⟩
        simpa [Nat.add_sub_of_le htk] using hti
      exact (Finite.surjective_iff_bijective).1 hsurj

/-- Proposition 3.43 (1): each midpoint bisection step divides the volume of the resulting
axis-aligned box by two. -/
-- Proof sketch: use `volume_Icc_pi_toReal` to express the volume of each box as the product of its
-- side lengths, then apply the fact that exactly one coordinate length is halved at step `k` while
-- the others are unchanged.
theorem generated_box_volume_eq_half_of_midpoint_bisection
    {n : ℕ} {a b a' b' : Fin n → ℝ} {i : Fin n}
    (hbox : a ≤ b)
    (hstep : IsMidpointCoordinateBisectionStep a b a' b' i) :
    (volume (Set.Icc a' b')).toReal = (1 / 2 : ℝ) * (volume (Set.Icc a b)).toReal := by
  have hsideEq := midpointCoordinateBisectionStep_sideLengths_eq_update hstep
  have hside :
      (fun j ↦ b' j - a' j) = Function.update (fun j ↦ b j - a j) i ((b i - a i) / 2) := by
    funext j
    exact congrFun hsideEq j
  have hbox' : a' ≤ b' := by
    intro j
    have hnonneg : 0 ≤ Function.update (fun j ↦ b j - a j) i ((b i - a i) / 2) j := by
      by_cases hj : j = i
      · subst j
        have hwidth : 0 ≤ b i - a i := sub_nonneg.mpr (hbox i)
        simpa [Function.update_self] using div_nonneg hwidth (show (0 : ℝ) ≤ 2 by norm_num)
      · simp [hj, sub_nonneg.mpr (hbox j)]
    have hjwidth :
        b' j - a' j = Function.update (fun j ↦ b j - a j) i ((b i - a i) / 2) j := by
      simpa [Pi.sub_apply] using congrFun hsideEq j
    have : 0 ≤ b' j - a' j := by
      rw [hjwidth]
      exact hnonneg
    exact sub_nonneg.mp this
  rw [Real.volume_Icc_pi_toReal hbox', Real.volume_Icc_pi_toReal hbox, hside]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i)]
  ring

/-- Proposition 3.43 (2): if every coordinate direction is bisected at least once in each block
of `n` consecutive steps, then after `n` steps every endpoint difference, and hence every side
length for ordered boxes, is halved. -/
-- Proof sketch: track the endpoint-difference vector `b k - a k`. Each step halves exactly the
-- coordinate indexed by `bisectedCoordinate k`. The block-covering hypothesis forces every
-- coordinate to be selected at least once in the next `n` steps, hence exactly once, so the whole
-- endpoint-difference vector is multiplied by `1 / 2`.
theorem generated_box_side_lengths_eq_half_after_n_steps
    {n : ℕ} (a b : ℕ → Fin n → ℝ) (bisectedCoordinate : ℕ → Fin n)
    (hstep : ∀ k,
      IsMidpointCoordinateBisectionStep
        (a k) (b k) (a (k + 1)) (b (k + 1)) (bisectedCoordinate k))
    (hcover : BisectionBlockCoversAllCoordinates n bisectedCoordinate)
    (k : ℕ) :
    b (k + n) - a (k + n) = (1 / 2 : ℝ) • (b k - a k) := by
  classical
  cases n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n =>
      let side : ℕ → Fin (n + 1) → ℝ := fun m ↦ b m - a m
      let c : ℕ → Fin (n + 1) := fun t ↦ bisectedCoordinate (k + t)
      let updatedCoords : ℕ → Finset (Fin (n + 1)) := fun t ↦ (Finset.range t).image c
      let half : Fin (n + 1) → ℝ := fun j ↦ side k j / 2
      have hbij : Function.Bijective (fun t : Fin (n + 1) ↦ c t) := by
        simpa [c] using bisectionBlockCoordinates_bijective bisectedCoordinate hcover k
      have hnotmem : ∀ {t : ℕ}, t < n + 1 → c t ∉ updatedCoords t := by
        intro t ht hmem
        rcases Finset.mem_image.mp hmem with ⟨u, hu, hcu⟩
        have hu' : u < n + 1 := lt_of_lt_of_le (Finset.mem_range.mp hu) (Nat.le_of_lt ht)
        have hEq : (⟨u, hu'⟩ : Fin (n + 1)) = ⟨t, ht⟩ := hbij.1 hcu
        have : u = t := by simpa using congrArg Fin.val hEq
        have hu_lt : u < t := Finset.mem_range.mp hu
        exact (Nat.ne_of_lt hu_lt) this
      have hupdated_succ :
          ∀ {t : ℕ}, t < n + 1 → updatedCoords (t + 1) = insert (c t) (updatedCoords t) := by
        intro t ht
        simp [updatedCoords, Finset.range_add_one]
      have hside_succ :
          ∀ m,
            side (m + 1) =
              Function.update (side m) (bisectedCoordinate m)
                ((side m (bisectedCoordinate m)) / 2) := by
        intro m
        simpa [side] using midpointCoordinateBisectionStep_sideLengths_eq_update (hstep m)
      have hprefix :
          ∀ t, t ≤ n + 1 →
            side (k + t) = (updatedCoords t).piecewise half (side k) := by
        intro t ht
        induction t with
        | zero =>
            simp [updatedCoords, side]
        | succ t ih =>
            have ht' : t < n + 1 := Nat.lt_of_succ_le ht
            have hstep_t :
                side (k + (t + 1)) =
                  Function.update (side (k + t)) (c t) ((side (k + t) (c t)) / 2) := by
              simpa [c, Nat.add_assoc] using hside_succ (k + t)
            calc
              side (k + (t + 1))
                  = Function.update (side (k + t)) (c t) ((side (k + t) (c t)) / 2) := hstep_t
              _ =
                  Function.update ((updatedCoords t).piecewise half (side k)) (c t)
                    (half (c t)) := by
                    rw [ih (Nat.le_of_lt ht')]
                    congr 1
                    rw [Finset.piecewise_eq_of_notMem _ _ _ (hnotmem ht')]
              _ = (insert (c t) (updatedCoords t)).piecewise half (side k) := by
                    symm
                    rw [Finset.piecewise_insert]
              _ = (updatedCoords (t + 1)).piecewise half (side k) := by
                    rw [hupdated_succ ht']
      have huniv : updatedCoords (n + 1) = Finset.univ := by
        ext j
        constructor
        · intro _
          simp
        · intro _
          rcases hbij.2 j with ⟨u, hu⟩
          exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr u.2, hu⟩
      calc
        b (k + (n + 1)) - a (k + (n + 1))
            = (updatedCoords (n + 1)).piecewise half (side k) := by
                simpa [side] using hprefix (n + 1) le_rfl
        _ = half := by
              rw [huniv]
              simp [half]
        _ = (1 / 2 : ℝ) • (b k - a k) := by
              ext j
              simp [half, side, Pi.smul_apply, div_eq_mul_inv, mul_comm]

/-! ### Theorem_3_43 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ}

open ApproximateLagrangeMultiplierSwitchingMethod

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/- Theorem 3.43 lies in the chapter's approximate-Lagrange-multiplier switching-method domain.

Sampled owner-style declarations:
- `positive_inactiveConstraintCount_of_large_iteration_count`
- `maxTypeObjective` and `maxTypeObjective_le_iff`
- `constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices`
- `delta_le_sampleMaxSubgradientNorm_mul_h_of_large_iteration_count`

Best owner abstraction:
- the owner run `ApproximateLagrangeMultiplierSwitchingMethod problem`
- the chapter finite-family maximum owner `maxTypeObjective`

Primitive data:
- the switching-method run `method`
- the time index `t`, the objective-step iterate `k ∈ A₀(t)`, and the stepsize positivity `0 < h`

Derived API:
- the source-facing residual maximum `maxTypeObjective problem.constraints (method k)`
- the componentwise owner theorem
  `constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices`
- the gap bound `δ_t ≤ M h`

Source/core/bridge triage:
- source-facing: Theorem 3.43's positivity statement, residual-maximum bound, and gap estimate
- core/canonical: the run owner theorems in `Theorem_3_2_4` and the finite-max owner
  `maxTypeObjective`
- bridge/view: the finite-max reformulation of the componentwise residual bound

The first and third clauses are exact owner recalls. The middle clause in the source is the
finite residual maximum `max_{1 ≤ j ≤ m} f_j(x_k) ≤ M h`, and this theorem surface now lives
directly in `Theorem_3_2_4`, so this file recalls it rather than reproving a parallel copy. -/

recall positive_inactiveConstraintCount_of_large_iteration_count

omit [CompleteSpace E] in
/-- Theorem 3.43 (middle clause): on every objective-step iterate `x_k` with `k ∈ A₀(t)`, the
maximum constraint residual is bounded by `M h`, where
`M = M[method](t)`. -/
recall maxConstraintValueAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices

recall delta_le_sampleMaxSubgradientNorm_mul_h_of_large_iteration_count

end ApproximateLagrangeMultiplierSwitchingMethod

end
