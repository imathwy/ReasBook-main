import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_2 (from Chap14) -/
universe v

open scoped Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}

/- Definition 14.2 is `source-facing`: it introduces coordinate-wise minimality for a finite block
product.

Domain sampling against the local block-coordinate API identifies the owner split:
- `core/canonical`: Mathlib's `IsMinOn` owner for one-block slice minimizers;
- `core/canonical`: Chapter 14's `alternating_minimization_block_objective`, specialized to the
  fixed-base case `xNext = xStar`, for the one-block slice itself; and
- `bridge/view`: one-block replacement through `Function.update`, and, in `PiLp 2 Ei`, the
  additive singleton presentation `x + 𝒰[i] d` of the same replacement.

The primitive data are therefore only effective-domain membership and the per-block `IsMinOn`
conditions for the canonical Chapter 14 block objective. Pointwise comparison inequalities and the
additive singleton formula are derived API, not primitive public data. -/
/-- Definition 14.2: a point `xStar` is a coordinate-wise minimum of `F` on the finite block
product if `xStar ∈ dom(F)` and, for every block `i`, the current coordinate `xStar i`
globally minimizes the fixed-base Chapter 14 one-block objective obtained by varying only block
`i`. The additive perturbation formula `xStar + 𝒰[i] d` is the equivalent bridge view in
`PiLp 2 Ei`. -/
@[mk_iff is_coordinatewise_minimum_iff]
class is_coordinatewise_minimum
    (F : ((i : Fin p) → Ei i) → EReal) (xStar : (i : Fin p) → Ei i) : Prop where
  /-- A coordinate-wise minimum lies in the effective domain of the objective. -/
  mem_effective_domain : xStar ∈ effective_domain F
  /-- At a coordinate-wise minimum, each coordinate globally minimizes the fixed-base one-block
  slice. -/
  isMinOn (i : Fin p) :
    IsMinOn (alternating_minimization_block_objective F xStar xStar i) Set.univ (xStar i)

attribute [simp] is_coordinatewise_minimum.mem_effective_domain
attribute [simp] is_coordinatewise_minimum_iff

@[simp] theorem alternating_minimization_block_objective_base_self
    (F : ((i : Fin p) → Ei i) → EReal) (x : (i : Fin p) → Ei i) (i : Fin p) :
    alternating_minimization_block_objective F x x i (x i) = F x := by
  simp

/-- The coordinate-wise minimum owner exposes effective-domain membership to typeclass search. -/
instance instEffectiveDomainOfIsCoordinatewiseMinimum
    {F : ((i : Fin p) → Ei i) → EReal} {xStar : (i : Fin p) → Ei i}
    [h : is_coordinatewise_minimum F xStar] :
    xStar ∈ effective_domain F :=
  h.mem_effective_domain

/-- At a coordinate-wise minimum, every one-coordinate replacement has objective value at least
`F xStar`. -/
theorem is_coordinatewise_minimum.le_update
    {F : ((i : Fin p) → Ei i) → EReal} {xStar : (i : Fin p) → Ei i}
    (h : is_coordinatewise_minimum F xStar) (i : Fin p) (y : Ei i) :
    F xStar ≤ F (Function.update xStar i y) := by
  simpa [alternating_minimization_block_objective_base_apply] using
    (isMinOn_iff.mp (h.isMinOn i)) y (by simp)

end

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)]

local notation "BlockSpace" => PiLp (2 : ENNReal) Ei

@[simp] theorem add_single_zero
    (x : BlockSpace) (i : Fin p) :
    x + 𝒰[i] (0 : Ei i) = x := by
  ext j
  by_cases h : j = i
  · subst h
    simp [PiLp.single_eq_same]
  · simp [h, PiLp.single_eq_of_ne]

/-- In `PiLp 2 Ei`, the fixed-base Chapter 14 one-block objective on the coordinate view agrees
with the additive singleton-update formula. -/
@[simp] theorem alternating_minimization_block_objective_toLp_eq_add_single
    (F : BlockSpace → EReal) (x : (i : Fin p) → Ei i) (i : Fin p) (y : Ei i) :
    alternating_minimization_block_objective (fun z ↦ F (WithLp.toLp 2 z)) x x i y =
      F (WithLp.toLp 2 x + 𝒰[i] (y - x i)) := by
  rw [alternating_minimization_block_objective_base_apply]
  congr 1
  ext j
  by_cases h : j = i
  · subst h
    simp [PiLp.single_eq_same]
  · simp [Function.update, h, PiLp.single_eq_of_ne]

/-- Bridge view: a coordinate-wise minimum of the coordinate pullback induces a one-block
`IsMinOn` statement for additive singleton perturbations in `PiLp 2 Ei`. -/
theorem is_coordinatewise_minimum.isMinOn_add_single
    {F : BlockSpace → EReal} {xStar : (i : Fin p) → Ei i}
    (h : is_coordinatewise_minimum (fun z ↦ F (WithLp.toLp 2 z)) xStar) (i : Fin p) :
    IsMinOn (fun y : Ei i ↦ F (WithLp.toLp 2 xStar + 𝒰[i] y)) Set.univ 0 := by
  rw [isMinOn_iff]
  intro y hy
  have hi := (isMinOn_iff.mp (h.isMinOn i)) (xStar i + y) (by simp)
  have hi' :
      F (WithLp.toLp 2 xStar) ≤
        F (WithLp.toLp 2 (Function.update xStar i (xStar i + y))) := by
    simpa [alternating_minimization_block_objective_base_apply] using hi
  have hupdate :
      WithLp.toLp 2 (Function.update xStar i (xStar i + y)) =
        WithLp.toLp 2 xStar + 𝒰[i] y := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [PiLp.single_eq_same]
    · simp [Function.update, hji, PiLp.single_eq_of_ne]
  simpa [hupdate] using hi'

/-- Bridge view: if the pullback of a `PiLp` objective along `WithLp.toLp 2` is coordinate-wise
minimal at `xStar`, then every one-block perturbation of `WithLp.toLp 2 xStar` has objective
value at least `F (WithLp.toLp 2 xStar)`. -/
theorem is_coordinatewise_minimum.le_add_single
    {F : BlockSpace → EReal} {xStar : (i : Fin p) → Ei i}
    (h : is_coordinatewise_minimum (fun z ↦ F (WithLp.toLp 2 z)) xStar)
    (i : Fin p) (y : Ei i) :
    F (WithLp.toLp 2 xStar) ≤ F (WithLp.toLp 2 xStar + 𝒰[i] y) := by
  have hy := (isMinOn_iff.mp (h.isMinOn_add_single i)) y (by simp)
  simpa using hy

end

/-! ### Lemma_14_2 (from Chap14) -/
noncomputable section

universe u v

section

/- `Lemma 14.2` is a `bridge/view` item. The source-facing coordinatewise minimum owner is
`is_coordinatewise_minimum`, the canonical Chapter 14 regularity owner is
`IsAlternatingMinimizationCompositeModel`, and the downstream Chapter 3 owner is
`is_stationary_point`. The theorem should therefore expose the model assumptions through the
existing owner class instead of restating its fields as a second public hypothesis bundle. -/

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
variable [FiniteDimensional ℝ ((i : Fin p) → Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}

/-- The Chapter 3 stationary-point owner uses the product-space module induced by the chosen
inner product on `Π i, E_i`. -/
local instance : Module ℝ ((i : Fin p) → Ei i) :=
  (inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule

local notation "F" => composite_model_objective f (separableSum g)

-- Proof sketch: fix a block `i`. The coordinate-wise minimum inequalities for `F` imply that
-- `xStar i` globally minimizes the one-block slice `y ↦ f (Function.update xStar i y) + g i y`.
-- The standing Assumption 14.6 owner `IsAlternatingMinimizationCompositeModel f g` supplies the
-- regularity hypotheses needed for the one-block first-order optimality theorem, giving
-- `-∇ᵢ f(xStar) ∈ ∂ g_i(xStar_i)` for every block. The block-separable regularizer then
-- identifies these coordinatewise subgradient conditions with the Chapter 3 stationary-point
-- predicate for `f + separableSum g`.
/-- Lemma 14.2: under the standing composite-model assumptions from Assumption 14.6, every
coordinate-wise minimum of the composite objective `F(x) = f(x) + ∑ i, g_i(x_i)` is a stationary
point of the composite problem `(14.9)`. The coordinate-wise minimum hypothesis uses the
source-facing owner predicate from Definition 14.2 directly on the block product, while the
regularity assumptions are supplied canonically by
`IsAlternatingMinimizationCompositeModel f g`. -/
theorem is_stationary_point_of_coordinatewise_minimum
    (hmodel : IsAlternatingMinimizationCompositeModel f g)
    {xStar : (i : Fin p) → Ei i}
    (hcoord : is_coordinatewise_minimum F xStar) :
    is_stationary_point f (separableSum g) xStar := sorry

end

/-! ### Proposition_14_2 (from Chap14) -/
noncomputable section

universe v

open scoped BigOperators

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable (f : ((i : Fin p) → Ei i) → EReal)
variable (g : (i : Fin p) → Ei i → EReal)
variable (xk xNext : (i : Fin p) → Ei i) (i : Fin p)

/- Proposition 14.2 is `bridge/view`: the source-facing content is the equivalence between the
full composite block step and the displayed one-block objective. The Chapter 14 owner of the
displayed subproblem is already `alternating_minimization_composite_block_objective`, built from
the core owners `alternating_minimization_block_objective`, `composite_model_objective`, and
`separableSum`. -/

-- Proof sketch: unfold the full block slice of `composite_model_objective f (separableSum g)`,
-- split the finite sum `separableSum g` into the active term `g_i(xi)` and the erased inactive
-- sum, and simplify the mixed state away from the active block.
/-- The full block slice of the composite objective decomposes into the displayed one-block owner
from Algorithm 14.3 plus the frozen sum of the inactive penalties. -/
theorem alternating_minimization_block_objective_composite_model_eq_add_inactive_penalty :
    alternating_minimization_block_objective
        (composite_model_objective f (separableSum g))
        xk
        xNext
        i =
      fun xi ↦
        alternating_minimization_composite_block_objective f g xk xNext i xi +
          (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)) := by
  funext xi
  rw [alternating_minimization_block_objective_apply,
    composite_model_objective_apply, separableSum_apply,
    alternating_minimization_composite_block_objective_apply]
  calc
    f (alternating_minimization_partial_state xk xNext i xi) +
        ∑ j, g j (alternating_minimization_partial_state xk xNext i xi j) =
      f (alternating_minimization_partial_state xk xNext i xi) +
        (g i (alternating_minimization_partial_state xk xNext i xi i) +
          ∑ j ∈ Finset.univ.erase i,
            g j (alternating_minimization_partial_state xk xNext i xi j)) := by
          rw [show
            (∑ j, g j (alternating_minimization_partial_state xk xNext i xi j)) =
              g i (alternating_minimization_partial_state xk xNext i xi i) +
                ∑ j ∈ Finset.univ.erase i,
                  g j (alternating_minimization_partial_state xk xNext i xi j) by
                symm
                exact Finset.add_sum_erase Finset.univ
                  (fun j ↦ g j (alternating_minimization_partial_state xk xNext i xi j))
                  (Finset.mem_univ i)]
    _ =
      f (alternating_minimization_partial_state xk xNext i xi) + g i xi +
        ∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j) := by
          have hsum :
              ∑ j ∈ Finset.univ.erase i,
                g j (alternating_minimization_partial_state xk xNext i xi j) =
                ∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
                  simp [alternating_minimization_partial_state, Function.update, hji]
          rw [hsum]
          simp [alternating_minimization_partial_state, add_assoc]

-- Proof sketch: if the displayed active term at the old block and the frozen inactive penalty sum
-- are both non-`⊥`, while the mixed old state lies in the effective domain of the full composite
-- objective, then the decomposition theorem above gives a sum `< ⊤`. The inactive penalty term
-- therefore cannot be `⊤`, so it is a genuine real constant and agrees with its `toReal`
-- coercion.
/-- If the frozen inactive penalty sum is not `⊥`, the displayed active term at the old block is
not `⊥`, and the mixed old state lies in the effective domain of the full composite objective,
then the frozen inactive penalty sum is finite. -/
theorem inactive_penalty_eq_coe_toReal_of_ne_bot_of_mem_effective_domain
    (hinactive_ne_bot :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)) ≠ ⊥)
    (hactive_ne_bot :
      alternating_minimization_composite_block_objective f g xk xNext i (xk i) ≠ ⊥)
    (hstate :
      alternating_minimization_partial_state xk xNext i (xk i) ∈
        effective_domain (composite_model_objective f (separableSum g))) :
    (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)) =
      (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)).toReal : ℝ) :
        EReal) := by
  let inactivePenalty : EReal :=
    ∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)
  have hinactive_ne_bot : inactivePenalty ≠ ⊥ := by
    simpa [inactivePenalty] using hinactive_ne_bot
  let stateOld : (j : Fin p) → Ei j := alternating_minimization_partial_state xk xNext i (xk i)
  have hdisplay_ne_bot :
      alternating_minimization_composite_block_objective f g xk xNext i (xk i) ≠ ⊥ :=
    hactive_ne_bot
  have hsum_top :
      alternating_minimization_composite_block_objective f g xk xNext i (xk i) + inactivePenalty <
        ⊤ := by
    have hstate_top :
        composite_model_objective f (separableSum g) stateOld < ⊤ :=
      mem_effective_domain.mp hstate
    calc
      alternating_minimization_composite_block_objective f g xk xNext i (xk i) + inactivePenalty =
          alternating_minimization_block_objective
            (composite_model_objective f (separableSum g))
            xk
            xNext
            i
            (xk i) := by
              simpa [inactivePenalty] using
                (congrFun
                  (alternating_minimization_block_objective_composite_model_eq_add_inactive_penalty
                    f g xk xNext i)
                  (xk i)).symm
      _ = composite_model_objective f (separableSum g) stateOld := by
        simp [alternating_minimization_block_objective_apply, stateOld]
      _ < ⊤ := hstate_top
  have hinactive_top : inactivePenalty < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro hinactive_eq_top
    exact (lt_top_iff_ne_top.mp hsum_top) <|
      by rw [hinactive_eq_top, EReal.add_top_of_ne_bot hdisplay_ne_bot]
  exact (EReal.coe_toReal (lt_top_iff_ne_top.mp hinactive_top) hinactive_ne_bot).symm

-- Proof sketch: apply the exact decomposition theorem above and replace the frozen inactive
-- penalty sum by its canonical `toReal` coercion using the explicit finiteness hypothesis. Both
-- objectives then differ by pointwise addition of the same finite constant, which
-- `EReal.addLECancellable_coe` cancels in the `IsMinOn` inequalities.
/-- Proposition 14.2: if the frozen inactive penalty sum is finite, then the full block subproblem
and the displayed one-block objective have the same minimizers. -/
theorem isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective
    (hinactive :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)) =
        (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)).toReal : ℝ) :
          EReal))
    (xi : Ei i) :
    IsMinOn
      (alternating_minimization_block_objective
        (composite_model_objective f (separableSum g))
        xk
        xNext
        i)
        Set.univ
        xi ↔
    IsMinOn
      (alternating_minimization_composite_block_objective f g xk xNext i)
      Set.univ
      xi := by
  let inactivePenalty : EReal :=
    ∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then xNext j else xk j)
  have hinactive :
      inactivePenalty = (((inactivePenalty.toReal : ℝ) : EReal)) := by
    simpa [inactivePenalty] using hinactive
  have hinactive_coe :
      (((inactivePenalty.toReal : ℝ) : EReal)) = inactivePenalty :=
    hinactive.symm
  have hfull_eval (yi : Ei i) :
      alternating_minimization_block_objective
          (composite_model_objective f (separableSum g))
          xk
          xNext
          i
          yi =
        alternating_minimization_composite_block_objective f g xk xNext i yi +
          (((inactivePenalty.toReal : ℝ) : EReal)) := by
    calc
      alternating_minimization_block_objective
          (composite_model_objective f (separableSum g))
          xk
          xNext
          i
          yi =
        alternating_minimization_composite_block_objective f g xk xNext i yi +
          inactivePenalty := by
            simpa using congrFun
              (alternating_minimization_block_objective_composite_model_eq_add_inactive_penalty
                f g xk xNext i) yi
      _ = alternating_minimization_composite_block_objective f g xk xNext i yi +
            (((inactivePenalty.toReal : ℝ) : EReal)) := by
        rw [hinactive_coe]
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h yi hy
    have hy' := h yi hy
    rw [hfull_eval xi, hfull_eval yi] at hy'
    exact ((EReal.addLECancellable_coe inactivePenalty.toReal).add_le_add_iff_right).mp hy'
  · intro h yi hy
    have hy' :
        alternating_minimization_composite_block_objective f g xk xNext i xi +
            (((inactivePenalty.toReal : ℝ) : EReal)) ≤
          alternating_minimization_composite_block_objective f g xk xNext i yi +
            (((inactivePenalty.toReal : ℝ) : EReal)) := by
      exact ((EReal.addLECancellable_coe inactivePenalty.toReal).add_le_add_iff_right).mpr
        (h yi hy)
    rw [← hfull_eval xi, ← hfull_eval yi] at hy'
    exact hy'

end

end
