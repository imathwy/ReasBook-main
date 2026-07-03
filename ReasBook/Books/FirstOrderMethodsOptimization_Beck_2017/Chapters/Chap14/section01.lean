import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_1 (from Chap14) -/
noncomputable section

universe u

open scoped Gradient

section

variable {p : ℕ} {E : Fin p → Type u}

local notation "BlockSpace" => PiLp (2 : ENNReal) E

/- Definition 14.1 is `source-facing`: the source item names the mixed inner states `x^{k,i}`
attached to an explicit outer iterate sequence `x^k`.

Domain sampling shows the following owner split.
- `core/canonical`: `alternating_minimization_partial_state` from Algorithm 14.1 is the chapter
  owner for one Gauss-Seidel block replacement on the coordinate family;
- `bridge/view`: Chapter 11's `𝒰[i]` and its coordinate lemmas are the canonical additive
  singleton presentation of a one-block update in `PiLp 2 E`;
- `source-facing`: this file keeps the textbook family `x^{k,i}` itself, obtained by adjoining the
  initial state `x^k` to the successive canonical one-block replacements.

Accordingly, the primitive data here are only the iterate family `x`. The successor auxiliary
states are derived from the owner `alternating_minimization_partial_state`, while the additive
update formula is stated through the existing Chapter 11 block embedding API. -/

/-- Definition 14.1: for an outer iterate sequence `x^k` in the block product `PiLp 2 E`, the
auxiliary state `x^{k,i}` uses the new iterate `x^(k+1)` in blocks with index `< i` and the old
iterate `x^k` in the remaining blocks. -/
def alternating_minimization_auxiliary_iterate
    (x : ℕ → BlockSpace) (k : ℕ) (i : Fin (p + 1)) : BlockSpace :=
  WithLp.toLp 2 (fun j ↦ if j.castSucc < i then x (k + 1) j else x k j)

/-- The successor auxiliary state is the canonical Algorithm 14.1 mixed block state with the
active block set to the next iterate value. -/
@[simp] theorem alternating_minimization_auxiliary_iterate_succ
    (x : ℕ → BlockSpace) (k : ℕ) (i : Fin p) :
    alternating_minimization_auxiliary_iterate x k i.succ =
      WithLp.toLp 2
        (alternating_minimization_partial_state
          (fun j ↦ x k j)
          (fun j ↦ x (k + 1) j)
          i
          (x (k + 1) i)) := by
  ext j
  by_cases hji : j < i
  · have hcut : j.castSucc < i.succ := Fin.castSucc_lt_succ_iff.mpr (le_of_lt hji)
    change (if j.castSucc < i.succ then (x (k + 1)).ofLp j else (x k).ofLp j) =
      if j < i then (x (k + 1)).ofLp j else
        Function.update (fun j ↦ (x k).ofLp j) i ((x (k + 1)).ofLp i) j
    rw [if_pos hcut, if_pos hji]
  · by_cases h : j = i
    · subst j
      change (if i.castSucc < i.succ then (x (k + 1)).ofLp i else (x k).ofLp i) =
        if i < i then (x (k + 1)).ofLp i else
          Function.update (fun j ↦ (x k).ofLp j) i ((x (k + 1)).ofLp i) i
      simp
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm h)
      have hcut : ¬ j.castSucc < i.succ := by
        intro h'
        exact not_lt_of_ge (Fin.castSucc_lt_succ_iff.mp h') hij
      change (if j.castSucc < i.succ then (x (k + 1)).ofLp j else (x k).ofLp j) =
        if j < i then (x (k + 1)).ofLp j else
          Function.update (fun j ↦ (x k).ofLp j) i ((x (k + 1)).ofLp i) j
      rw [if_neg hcut, if_neg hji]
      simp [Function.update, h]

/-- The coordinates of `x^{k,i}` agree with the textbook mixed-state rule. -/
@[simp] theorem alternating_minimization_auxiliary_iterate_apply
    (x : ℕ → BlockSpace) (k : ℕ) (i : Fin (p + 1)) (j : Fin p) :
    alternating_minimization_auxiliary_iterate x k i j =
      if j.castSucc < i then x (k + 1) j else x k j :=
  rfl

/-- The initial auxiliary state is the current outer iterate `x^k`. -/
@[simp] theorem alternating_minimization_auxiliary_iterate_zero
    (x : ℕ → BlockSpace) (k : ℕ) :
    alternating_minimization_auxiliary_iterate x k 0 = x k := by
  ext j
  rw [alternating_minimization_auxiliary_iterate_apply]
  simp

/-- The terminal auxiliary state is the next outer iterate `x^(k+1)`. -/
@[simp] theorem alternating_minimization_auxiliary_iterate_last
    (x : ℕ → BlockSpace) (k : ℕ) :
    alternating_minimization_auxiliary_iterate x k (Fin.last p) = x (k + 1) := by
  ext j
  rw [alternating_minimization_auxiliary_iterate_apply]
  simp [Fin.castSucc_lt_last]

section

variable [∀ i, NormedAddCommGroup (E i)]

recall PiLp.single

/-- Passing from `x^{k,i-1}` to `x^{k,i}` updates exactly block `i` by the Chapter 11 block
embedding `𝒰[i]`. This is the Chapter 14 block-update surface
`x^{k,i} = x^{k,i-1} + 𝒰[i] (x_i^(k+1) - x_i^k)`. -/
theorem alternating_minimization_auxiliary_iterate_succ_eq_add_single
    (x : ℕ → BlockSpace) (k : ℕ) (i : Fin p) :
    alternating_minimization_auxiliary_iterate x k i.succ =
      alternating_minimization_auxiliary_iterate x k i.castSucc +
        𝒰[i] (x (k + 1) i - x k i) := by
  ext j
  by_cases h : j = i
  · subst j
    change (if i.castSucc < i.succ then (x (k + 1)).ofLp i else (x k).ofLp i) =
      (if i.castSucc < i.castSucc then (x (k + 1)).ofLp i else (x k).ofLp i) +
        (𝒰[i] ((x (k + 1)).ofLp i - (x k).ofLp i)) i
    simp [block_coordinate_embedding_apply_same]
  · by_cases hji : j < i
    · have hsucc : j.castSucc < i.succ := Fin.castSucc_lt_succ_iff.mpr (le_of_lt hji)
      have hpred : j.castSucc < i.castSucc := by simpa using hji
      change (if j.castSucc < i.succ then (x (k + 1)).ofLp j else (x k).ofLp j) =
        (if j.castSucc < i.castSucc then (x (k + 1)).ofLp j else (x k).ofLp j) +
          (𝒰[i] ((x (k + 1)).ofLp i - (x k).ofLp i)) j
      rw [if_pos hsucc, if_pos hpred]
      simp [h]
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm h)
      have hsucc : ¬ j.castSucc < i.succ := by
        intro h'
        exact not_lt_of_ge (Fin.castSucc_lt_succ_iff.mp h') hij
      have hpred : ¬ j.castSucc < i.castSucc := by
        intro h'
        exact hji (by simpa using h')
      change (if j.castSucc < i.succ then (x (k + 1)).ofLp j else (x k).ofLp j) =
        (if j.castSucc < i.castSucc then (x (k + 1)).ofLp j else (x k).ofLp j) +
          (𝒰[i] ((x (k + 1)).ofLp i - (x k).ofLp i)) j
      rw [if_neg hsucc, if_neg hpred]
      simp [h]

end

end

/-! ### Lemma_14_1 (from Chap14) -/
universe v

section

variable {p : ℕ} {Ei : Fin p → Type v}

/- Lemma 14.1 is `source-facing`: its Chapter 14 content is the fixed-base one-block argmin
existence statement, and its generic minimization prerequisite is already owned upstream in
Chapter 2.

Domain sampling in the surrounding project identifies the relevant owner split:
- `core/canonical`: Chapter 2's `effective_domain` and
  `exists_isMinOn_on_compact` for lower-semicontinuous minimization on compact sets meeting the
  effective domain;
- `core/canonical`: Chapter 8's `unconstrained_problem_solutions` for global argmin sets;
- `core/canonical`: Chapter 14's `alternating_minimization_block_objective` for one-block
  objective slices;
- `bridge/view`: Mathlib's `continuous_update` and `LowerSemicontinuous.comp`, which transfer
  lower semicontinuity along the fixed-base block section `y ↦ Function.update xBar i y`;
- `bridge/view`: the source-facing fixed-base block argmin set at `xBar`, obtained by applying the
  Chapter 8 solution-set owner to `alternating_minimization_block_objective F xBar xBar i`.

The primitive data for the Chapter 14 statement are therefore the block objective together with
the source-facing fixed-base argmin set. The proof reduces the source-facing statement to the
compact-sublevel-set owner theorem from Chapter 2; there is no primitive properness field for the
block slice beyond the single witness supplied by `xBar ∈ effective_domain F`. -/

/-- The argmin set of the one-block alternating-minimization subproblem at `xBar` and block `i`.
This is the canonical Chapter 14 block objective specialized to the fixed-base case
`xNext = xBar`. -/
abbrev alternating_minimization_argmin
    (F : ((i : Fin p) → Ei i) → EReal) (xBar : (i : Fin p) → Ei i) (i : Fin p) :
    Set (Ei i) :=
  unconstrained_problem_solutions (alternating_minimization_block_objective F xBar xBar i)

/-- Definitionally, the Chapter 14 fixed-base argmin set is the Chapter 8 unconstrained solution
set of the specialized one-block objective. -/
theorem alternating_minimization_argmin_def
    (F : ((i : Fin p) → Ei i) → EReal) (xBar : (i : Fin p) → Ei i) (i : Fin p) :
    alternating_minimization_argmin F xBar i =
      unconstrained_problem_solutions (alternating_minimization_block_objective F xBar xBar i) :=
  rfl

-- Proof sketch: unfold the Chapter 8 solution-set owner used by
-- `alternating_minimization_argmin`.
/-- A point `y` belongs to the one-block alternating-minimization argmin set exactly when it
globally minimizes the specialized Chapter 14 one-block objective. -/
@[simp] theorem mem_alternating_minimization_argmin_iff
    {F : ((i : Fin p) → Ei i) → EReal} {xBar : (i : Fin p) → Ei i} {i : Fin p} {y : Ei i} :
    y ∈ alternating_minimization_argmin F xBar i ↔
      IsMinOn (alternating_minimization_block_objective F xBar xBar i) Set.univ y :=
  mem_unconstrained_problem_solutions_iff

-- Proof sketch: combine `mem_alternating_minimization_argmin_iff` with the fixed-base objective
-- identity `alternating_minimization_block_objective_base_apply`.
/-- A point `y` belongs to the one-block alternating-minimization argmin set exactly when it
globally minimizes the fixed-base objective `yi ↦ F (Function.update xBar i yi)`. -/
@[simp] theorem mem_alternating_minimization_argmin_update_iff
    {F : ((i : Fin p) → Ei i) → EReal} {xBar : (i : Fin p) → Ei i} {i : Fin p} {y : Ei i} :
    y ∈ alternating_minimization_argmin F xBar i ↔
      IsMinOn (fun yi ↦ F (Function.update xBar i yi)) Set.univ y := by
  have hfun :
      alternating_minimization_block_objective F xBar xBar i =
        fun yi ↦ F (Function.update xBar i yi) := by
    funext yi
    exact alternating_minimization_block_objective_base_apply F xBar i yi
  rw [mem_alternating_minimization_argmin_iff, hfun]

section

variable [∀ i, PseudoMetricSpace (Ei i)]

/- Lemma 14.1 uses Chapter 2's compact minimization owner
`exists_isMinOn_on_compact` on a bounded real sublevel set of the fixed-block objective. -/
recall exists_isMinOn_on_compact

-- Proof sketch: the fixed-base slice `yi ↦ F (Function.update xBar i yi)` is the composition of
-- `F` with the continuous block-update section `yi ↦ Function.update xBar i yi`.
/-- Helper for Lemma 14.1: composing a lower-semicontinuous objective with the fixed-base block
update section preserves lower semicontinuity. -/
lemma alternating_minimization_block_update_lowerSemicontinuous
    (F : ((i : Fin p) → Ei i) → EReal) (hF_closed : LowerSemicontinuous F)
    (xBar : (i : Fin p) → Ei i) (i : Fin p) :
    LowerSemicontinuous (fun yi ↦ F (Function.update xBar i yi)) := by
  -- Transfer lower semicontinuity along the continuous coordinate-update section.
  simpa [Function.comp] using hF_closed.comp (continuous_const.update i continuous_id)

-- Proof sketch: each slice sublevel set is contained in the image under the `i`-th coordinate
-- projection of the corresponding ambient sublevel set, so boundedness descends from `F`.
/-- Helper for Lemma 14.1: bounded real sublevel sets of `F` induce bounded real sublevel sets of
the fixed-base one-block slice. -/
lemma alternating_minimization_block_real_sublevel_bounded
    (F : ((i : Fin p) → Ei i) → EReal)
    (hlevel : ∀ α : ℝ, Bornology.IsBounded {x | F x ≤ (α : EReal)})
    (xBar : (i : Fin p) → Ei i) (i : Fin p) :
    ∀ α : ℝ, Bornology.IsBounded {yi | F (Function.update xBar i yi) ≤ (α : EReal)} := by
  intro α
  let S : Set ((j : Fin p) → Ei j) := {x | F x ≤ (α : EReal)}
  have hsubset : {yi | F (Function.update xBar i yi) ≤ (α : EReal)} ⊆ (fun x ↦ x i) '' S := by
    intro yi hyi
    refine ⟨Function.update xBar i yi, ?_, ?_⟩
    · simpa [S] using hyi
    · simp
  -- The coordinate projection of a bounded ambient sublevel set is bounded.
  have himage : Bornology.IsBounded ((fun x ↦ x i) '' S) := by
    simpa using (hlevel α).image_eval i
  exact himage.subset hsubset

-- Proof sketch: points outside the real sublevel set have value strictly larger than the cut
-- level, while the minimizing point lies at or below that level.
/-- Helper for Lemma 14.1: a minimizer on a real sublevel set is already a global minimizer once
the minimizing point lies in that sublevel set. -/
lemma isMinOn_univ_of_isMinOn_real_sublevel
    {E : Type*} {G : E → EReal} {a : EReal} {y : E}
    (hy : y ∈ {u | G u ≤ a}) (hmin : IsMinOn G {u | G u ≤ a} y) :
    IsMinOn G Set.univ y := by
  -- Compare with competitors inside the sublevel set by minimality, and with points outside by
  -- the strict sublevel inequality.
  rw [isMinOn_univ_iff]
  intro z
  by_cases hz : z ∈ {u | G u ≤ a}
  · exact hmin hz
  · have hlt : a < G z := lt_of_not_ge hz
    exact le_trans hy hlt.le

end

-- Proof sketch: if `F xBar = ⊥`, then the fixed-base slice attains the bottom value at `xBar i`,
-- so no competitor can be smaller.
/-- Helper for Lemma 14.1: if the base point has objective value `⊥`, then the current block
value already globally minimizes the fixed-base one-block slice. -/
lemma alternating_minimization_block_bottom_base_isMinOn
    (F : ((i : Fin p) → Ei i) → EReal)
    (xBar : (i : Fin p) → Ei i) (i : Fin p) (hbot : F xBar = ⊥) :
    IsMinOn (fun yi ↦ F (Function.update xBar i yi)) Set.univ (xBar i) := by
  -- The witness `xBar i` gives the bottom objective value on the slice.
  rw [isMinOn_univ_iff]
  intro yi
  calc
    F (Function.update xBar i (xBar i)) = ⊥ := by simp [hbot]
    _ ≤ F (Function.update xBar i yi) := by exact bot_le

section

variable [∀ i, PseudoMetricSpace (Ei i)]

-- Proof sketch: if `F xBar = ⊥`, then the witness `y = xBar i` already minimizes the fixed-block
-- objective globally. Otherwise `F xBar` is finite because `hxBar` rules out `⊤`, so the real
-- sublevel set `{y | G y ≤ F xBar}` of the fixed-block objective `G` is compact by lower
-- semicontinuity and boundedness. The witness `xBar i` lies in that compact set and in
-- `effective_domain G`, so `exists_isMinOn_on_compact` yields a minimizer on the sublevel set,
-- and points outside the set have strictly larger value.
/-- Lemma 14.1: for any base point `xBar` in the effective domain and any block index `i`, the
one-block alternating-minimization subproblem obtained by varying only block `i` has a minimizer.
-/
theorem alternating_minimization_argmin_nonempty_of_mem_effective_domain
    (F : ((i : Fin p) → Ei i) → EReal) (hF_closed : LowerSemicontinuous F)
    (hlevel : ∀ α : ℝ, Bornology.IsBounded {x | F x ≤ (α : EReal)})
    (xBar : (i : Fin p) → Ei i) (hxBar : xBar ∈ effective_domain F) (i : Fin p)
    [ProperSpace (Ei i)] :
    (alternating_minimization_argmin F xBar i).Nonempty := by
  let G : Ei i → EReal := fun yi ↦ F (Function.update xBar i yi)
  by_cases hbot : F xBar = ⊥
  · refine ⟨xBar i, ?_⟩
    -- In the bottom branch, the current block value already minimizes the slice globally.
    rw [mem_alternating_minimization_argmin_update_iff]
    exact alternating_minimization_block_bottom_base_isMinOn F xBar i hbot
  · have hG_closed : LowerSemicontinuous G :=
      alternating_minimization_block_update_lowerSemicontinuous F hF_closed xBar i
    have hxBar_top : F xBar ≠ ⊤ := (mem_effective_domain.mp hxBar).ne
    have hxBar_toReal : ((((F xBar).toReal : ℝ) : EReal)) = F xBar :=
      EReal.coe_toReal hxBar_top hbot
    let C : Set (Ei i) := {yi | G yi ≤ (((F xBar).toReal : ℝ) : EReal)}
    have hC_closed : IsClosed C := by
      -- Lower semicontinuity makes the real sublevel set of the slice closed.
      simpa [C] using hG_closed.isClosed_preimage ((((F xBar).toReal : ℝ) : EReal))
    have hC_bounded : Bornology.IsBounded C := by
      -- Boundedness is inherited from the ambient real sublevel set of `F`.
      simpa [C, G] using
        alternating_minimization_block_real_sublevel_bounded F hlevel xBar i ((F xBar).toReal)
    have hC_compact : IsCompact C := Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded
    have hxBarC : xBar i ∈ C := by
      -- The base block lies in the chosen real sublevel set because updating it leaves `xBar`
      -- unchanged.
      simp [C, G, hxBar_toReal]
    have hxBarG : xBar i ∈ effective_domain G := by
      -- The slice is finite at `xBar i` because `G (xBar i) = F xBar < ⊤`.
      simpa [G] using hxBar
    obtain ⟨y, hyCdom, hyminC⟩ :=
      exists_isMinOn_on_compact
        G
        C
        (hG_closed.lowerSemicontinuousOn C)
        hC_compact
        ⟨xBar i, ⟨hxBarC, hxBarG⟩⟩
    have hymin_univ : IsMinOn G Set.univ y :=
      -- A minimizer on the compact sublevel set is already global.
      isMinOn_univ_of_isMinOn_real_sublevel hyCdom.1 hyminC
    refine ⟨y, ?_⟩
    -- Return to the source-facing Chapter 14 argmin set.
    rw [mem_alternating_minimization_argmin_update_iff]
    simpa [G] using hymin_univ

end

end

/-! ### Proposition_14_1 (from Chap14) -/
noncomputable section

/- Proposition 14.1 is `source-facing`: it studies the distinguished line of coordinatewise minima
for the Chapter 14 counterexample objective. Domain sampling against the existing Chapter 14 API
identifies the following owner split.
- `source-facing`: Definition 14.4's real-valued owner
  `alternating_minimization_failure_ii_objective`;
- `core/canonical`: `is_coordinatewise_minimum` from Definition 14.2;
- `source-facing` companion owners: the pair section owners
  `two_block_alternating_minimization_x1_objective` and
  `two_block_alternating_minimization_x2_objective` from Algorithm 14.8;
- `bridge/view`: the canonical coercion `Function.toEReal` from Definition 9.2; and
- `bridge/view`: `two_block_alternating_minimization_objective_blocks` and
  `two_block_alternating_minimization_state` from Algorithm 14.8.

Accordingly, the objective itself is not redefined here: the file reuses Definition 14.4's owner
through its canonical `EReal` view. The primitive data kept here are only the distinguished line
of counterexample points and the resulting minimizer statements on that fixed objective. The main
coordinatewise-minimality statement therefore uses the Chapter 14 owner
`is_coordinatewise_minimum` on the canonical two-block block-vector view, while the textbook pair
sections are kept only as a thin source-facing companion theorem. -/

local notation "F" => alternating_minimization_failure_ii_objective.toEReal
local notation "g₀" => (0 : ℝ → EReal)
local notation "F₂" =>
  two_block_alternating_minimization_objective_blocks
    F
    g₀
    g₀

-- Proof sketch: the objective is nonnegative as a sum of absolute values, and it vanishes exactly
-- when the linear system `3 x₁ + 4 x₂ = 0` and `x₁ - 2 x₂ = 0` holds, whose unique solution is
-- `(0, 0)`.
/-- Proposition 14.1 (1): the counterexample objective has the origin as its unique global
minimizer. -/
theorem alternating_minimization_counterexample_unique_minimizer
    (x : ℝ × ℝ) :
    IsMinOn F Set.univ x ↔ x = 0 := sorry

/-- Proposition 14.1 (2): every point `(-4 * α, 3 * α)` on the distinguished line is a
coordinate-wise minimum of the counterexample objective in the Chapter 14 two-block owner sense. -/
theorem alternating_minimization_counterexample_is_coordinatewise_minimum
    (α : ℝ) :
    is_coordinatewise_minimum F₂ (two_block_alternating_minimization_state (-4 * α) (3 * α)) :=
  sorry

-- Proof sketch: unpack the owner statement above at the two blocks `0` and `1`, then simplify
-- the canonical block objectives with the two-block bridge lemmas from Algorithm 14.8.
/-- Source-facing companion to Proposition 14.1 (2): every point `(-4 * α, 3 * α)` on the
distinguished line lies in the effective domain and minimizes both textbook one-variable sections
of the counterexample objective. -/
theorem alternating_minimization_counterexample_coordinatewise_minimum
    (α : ℝ) :
    (-4 * α, 3 * α) ∈ effective_domain F ∧
      IsMinOn
        (two_block_alternating_minimization_x1_objective
          F
          g₀
          g₀
          (3 * α))
        Set.univ
        (-4 * α) ∧
      IsMinOn
        (two_block_alternating_minimization_x2_objective
          F
          g₀
          g₀
          (-4 * α))
        Set.univ
        (3 * α) := by
  let hcoord := alternating_minimization_counterexample_is_coordinatewise_minimum α
  refine ⟨?_, ?_, ?_⟩
  · simp [effective_domain, Function.toEReal]
  · simpa using hcoord.isMinOn 0
  · simpa using hcoord.isMinOn 1
