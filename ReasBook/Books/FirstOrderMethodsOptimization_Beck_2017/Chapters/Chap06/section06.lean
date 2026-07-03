import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_6 (from Chap06) -/
open WithLp
open scoped BigOperators

noncomputable section

section

variable {ι : Type*}

local notation "coord" => WithLp.equiv (2 : ENNReal) (ι → ℝ)
local notation "E" => EuclideanSpace ℝ ι

/-
Definition 6.6 is `source-facing` in the separable finite-product penalty domain. Sampling the
nearby chapter owners `Box[ℓ,u]` from Chapter 1, `extendedIndicator` from Chapter 2,
`softThreshold` from Definition 6.3, and `twoSidedSoftThreshold` from Definition 6.5 shows that
the primitive data are:

- a finite index family of nonnegative weights `ω : ι → NNReal`,
- a finite index family of extended nonnegative box half-widths `α : ι → ENNReal`.

The source-facing owners therefore remain the weighted box-constrained set and its penalty on the
canonical finite Euclidean product `EuclideanSpace ℝ ι`, while the supporting box data should be
reused from the Chapter 1 owner `Box[ℓ,u]` through the canonical coordinate equivalence
`WithLp.equiv`.
-/

private theorem mem_symmetricInterval_iff
    (a : ENNReal) (t : ℝ) :
    (-((a : EReal)) ≤ (t : EReal) ∧ (t : EReal) ≤ (a : EReal)) ↔ ENNReal.ofReal |t| ≤ a := by
  by_cases ha : a = ⊤
  · simp [ha]
  · lift a to NNReal using ha with a
    have hleft : (-((a : NNReal) : EReal) ≤ (t : EReal)) ↔ (-(a : ℝ) ≤ t) := by
      change (((-(a : ℝ)) : EReal) ≤ (t : EReal)) ↔ (-(a : ℝ) ≤ t)
      exact EReal.coe_le_coe_iff
    have hright : ((t : EReal) ≤ ((a : NNReal) : EReal)) ↔ t ≤ (a : ℝ) := by
      change ((t : EReal) ≤ ((a : ℝ) : EReal)) ↔ t ≤ (a : ℝ)
      exact EReal.coe_le_coe_iff
    simp [hleft, hright, abs_le]

private theorem mem_symmetricBox_iff (α : ι → ENNReal) (x : E) :
    x ∈
        (coord ⁻¹'
          Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E) ↔
      ∀ i, ENNReal.ofReal |x i| ≤ α i := by
  change
    (∀ i, -((α i : EReal)) ≤ (x i : EReal) ∧ (x i : EReal) ≤ (α i : EReal)) ↔
      ∀ i, ENNReal.ofReal |x i| ≤ α i
  constructor
  · intro hx i
    exact (mem_symmetricInterval_iff (α i) (x i)).1 (hx i)
  · intro hx i
    exact (mem_symmetricInterval_iff (α i) (x i)).2 (hx i)

/-- Helper for Definition 6.6: the scalar box `ENNReal.ofReal |t| ≤ a` is closed. -/
private theorem isClosed_scalar_abs_le_ennreal
    (a : ENNReal) :
    IsClosed {t : ℝ | ENNReal.ofReal |t| ≤ a} := by
  -- The scalar box is the preimage of the closed lower interval `(-∞, a]`.
  simpa using
    (isClosed_Iic.preimage
      (ENNReal.continuous_ofReal.comp
        (continuous_norm : Continuous fun t : ℝ => ‖t‖)))

/-- Helper for Definition 6.6: the scalar box `ENNReal.ofReal |t| ≤ a` is convex. -/
private theorem convex_scalar_abs_le_ennreal
    (a : ENNReal) :
    Convex ℝ {t : ℝ | ENNReal.ofReal |t| ≤ a} := by
  by_cases ha : a = ⊤
  · -- At `a = ∞`, the scalar constraint is vacuous.
    simpa [ha] using (convex_univ : Convex ℝ (Set.univ : Set ℝ))
  · -- For finite `a`, the scalar box is the interval `[-a, a]`.
    lift a to NNReal using ha with a
    simpa [abs_le] using
      (convex_Icc (-(a : ℝ)) (a : ℝ) :
        Convex ℝ (Set.Icc (-(a : ℝ)) (a : ℝ)))

/-- Helper for Definition 6.6: the coordinatewise symmetric box is closed. -/
private theorem isClosed_symmetric_abs_box
    (α : ι → ENNReal) :
    IsClosed {x : E | ∀ i, ENNReal.ofReal |x i| ≤ α i} := by
  -- Each coordinate slice is closed by continuity of the evaluation map.
  have hcoord : ∀ i, IsClosed {x : E | ENNReal.ofReal |x i| ≤ α i} := by
    intro i
    simpa using
      (isClosed_scalar_abs_le_ennreal (α i)).preimage
        (PiLp.continuous_apply (2 : ENNReal) (fun _ ↦ ℝ) i)
  -- The full box is the intersection of the coordinate slices.
  simpa [Set.setOf_forall] using (isClosed_iInter hcoord)

/-- Helper for Definition 6.6: the coordinatewise symmetric box is convex. -/
private theorem convex_symmetric_abs_box
    (α : ι → ENNReal) :
    Convex ℝ {x : E | ∀ i, ENNReal.ofReal |x i| ≤ α i} := by
  -- Convexity is checked coordinatewise using the scalar box lemma.
  intro x hx y hy a b ha hb hab i
  exact (convex_scalar_abs_le_ennreal (α i)) (hx i) (hy i) ha hb hab

variable [Fintype ι]

/-- Helper for Definition 6.6: the weighted `ℓ¹` sublevel set is closed. -/
private theorem isClosed_weighted_l1_sublevel
    (ω : ι → NNReal) (β : ℝ) :
    IsClosed {x : E | (∑ i, (ω i : ℝ) * |x i|) ≤ β} := by
  let f : E → ℝ := fun x ↦ ∑ i, (ω i : ℝ) * |x i|
  -- The weighted absolute-value sum is continuous term by term.
  have hf : Continuous f := by
    unfold f
    refine continuous_finset_sum Finset.univ ?_
    intro i hi
    simpa [Real.norm_eq_abs] using
      ((PiLp.continuous_apply (2 : ENNReal) (fun _ ↦ ℝ) i).norm.const_mul
        (ω i : ℝ))
  -- Closedness follows from taking a closed sublevel set of a continuous map.
  simpa [f] using (isClosed_Iic.preimage hf)

/-- Helper for Definition 6.6: the weighted `ℓ¹` sublevel set is convex. -/
private theorem convex_weighted_l1_sublevel
    (ω : ι → NNReal) (β : ℝ) :
    Convex ℝ {x : E | (∑ i, (ω i : ℝ) * |x i|) ≤ β} := by
  intro x hx y hy a b ha hb hab
  change (∑ i, (ω i : ℝ) * |(a • x + b • y) i|) ≤ β
  have hxβ : (∑ i, (ω i : ℝ) * |x i|) ≤ β := by
    simpa using hx
  have hyβ : (∑ i, (ω i : ℝ) * |y i|) ≤ β := by
    simpa using hy
  -- Bound each coordinate of the convex combination by the triangle inequality.
  have hterm :
      ∀ i,
        (ω i : ℝ) * |(a • x + b • y) i| ≤
          (ω i : ℝ) * (a * |x i| + b * |y i|) := by
    intro i
    have habs :
        |(a • x + b • y) i| ≤ a * |x i| + b * |y i| := by
      calc
        |(a • x + b • y) i| = |a * x i + b * y i| := by
          simp [smul_eq_mul]
        _ ≤ |a * x i| + |b * y i| := by
          simpa [Real.norm_eq_abs] using norm_add_le (a * x i) (b * y i)
        _ = a * |x i| + b * |y i| := by
          rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb]
    have hω : 0 ≤ (ω i : ℝ) := by
      exact_mod_cast (ω i).2
    exact mul_le_mul_of_nonneg_left habs hω
  have hsum :
      (∑ i, (ω i : ℝ) * |(a • x + b • y) i|) ≤
        ∑ i, (ω i : ℝ) * (a * |x i| + b * |y i|) := by
    exact Finset.sum_le_sum fun i hi ↦ hterm i
  -- Rearrange the bound into the convex combination of the endpoint sums.
  calc
    (∑ i, (ω i : ℝ) * |(a • x + b • y) i|) ≤
        ∑ i, (ω i : ℝ) * (a * |x i| + b * |y i|) := hsum
    _ = a * ∑ i, (ω i : ℝ) * |x i| + b * ∑ i, (ω i : ℝ) * |y i| := by
      calc
        (∑ i, (ω i : ℝ) * (a * |x i| + b * |y i|)) =
            ∑ i, (a * ((ω i : ℝ) * |x i|) + b * ((ω i : ℝ) * |y i|)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = a * ∑ i, (ω i : ℝ) * |x i| + b * ∑ i, (ω i : ℝ) * |y i| := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_add_distrib]
    _ ≤ a * β + b * β := by
      gcongr
    _ = (a + b) * β := by
      ring
    _ = β := by
      rw [hab, one_mul]

/-- Definition 6.6: the weighted `ℓ¹` box-constrained level set consists of the families
`x : EuclideanSpace ℝ ι` such that `∑ i, ω_i |x_i| ≤ β` and `|x_i| ≤ α_i` coordinatewise,
equivalently `-α ≤ x ≤ α`; specializing to `ι = Fin n` recovers the textbook subset of `ℝ^n`. -/
def weighted_l1_box_constraint_set
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) : Set E :=
  {x |
    (∑ i, (ω i : ℝ) * |x i|) ≤ β ∧
      x ∈
        (coord ⁻¹' Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E)}

/-- A point lies in the weighted `ℓ¹` box-constrained set exactly when its weighted `ℓ¹` value is
at most `β` and every coordinate satisfies `|x i| ≤ α i`, with `α i = ∞` allowed. -/
theorem mem_weighted_l1_box_constraint_set_iff
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) (x : E) :
    x ∈ weighted_l1_box_constraint_set ω α β ↔
      (∑ i, (ω i : ℝ) * |x i|) ≤ β ∧ ∀ i, ENNReal.ofReal |x i| ≤ α i := by
  constructor
  · rintro ⟨hβ, hx⟩
    exact ⟨hβ, (mem_symmetricBox_iff α x).1 hx⟩
  · rintro ⟨hβ, hx⟩
    exact ⟨hβ, (mem_symmetricBox_iff α x).2 hx⟩

-- Proof sketch: the zero vector has weighted `ℓ¹` value `0`, so `0 ≤ β` implies the sublevel
-- inequality, and the coordinate box constraints hold trivially because `|0| = 0`.
/-- The weighted `ℓ¹` box-constrained set is nonempty whenever `β ≥ 0`. -/
theorem weighted_l1_box_constraint_set_nonempty_of_nonneg
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) (hβ : 0 ≤ β) :
    (weighted_l1_box_constraint_set ω α β).Nonempty := by
  -- Use the zero vector, whose weighted `ℓ¹` value is zero and which satisfies the box bounds.
  refine ⟨0, ?_⟩
  rw [mem_weighted_l1_box_constraint_set_iff]
  constructor
  · simpa using hβ
  · intro i
    simp

-- Proof sketch: the weighted `ℓ¹` inequality is a closed sublevel condition for a continuous
-- finite sum of absolute values, and the coordinate box constraints are closed; their
-- intersection is therefore closed.
/-- The weighted `ℓ¹` box-constrained set is closed. -/
theorem weighted_l1_box_constraint_set_isClosed
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) :
    IsClosed (weighted_l1_box_constraint_set ω α β) := by
  have hset :
      weighted_l1_box_constraint_set ω α β =
        {x : E | (∑ i, (ω i : ℝ) * |x i|) ≤ β} ∩
          {x : E | ∀ i, ENNReal.ofReal |x i| ≤ α i} := by
    -- Rewrite the set as the intersection of the weighted sublevel and the box.
    ext x
    simp [mem_weighted_l1_box_constraint_set_iff]
  -- Closedness follows from the two closed factors.
  rw [hset]
  exact
    (isClosed_weighted_l1_sublevel ω β).inter
      (isClosed_symmetric_abs_box α)

-- Proof sketch: the weighted `ℓ¹` sublevel set is convex, the symmetric coordinate box is convex,
-- and `weighted_l1_box_constraint_set ω α β` is their intersection.
/-- The weighted `ℓ¹` box-constrained set is convex. -/
theorem weighted_l1_box_constraint_set_convex
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) :
    Convex ℝ (weighted_l1_box_constraint_set ω α β) := by
  have hset :
      weighted_l1_box_constraint_set ω α β =
        {x : E | (∑ i, (ω i : ℝ) * |x i|) ≤ β} ∩
          {x : E | ∀ i, ENNReal.ofReal |x i| ≤ α i} := by
    -- Rewrite the set as the intersection of the weighted sublevel and the box.
    ext x
    simp [mem_weighted_l1_box_constraint_set_iff]
  -- Convexity follows from the two convex factors.
  rw [hset]
  exact
    (convex_weighted_l1_sublevel ω β).inter
      (convex_symmetric_abs_box α)

/-- The extended-real-valued penalty
`x ↦ ωᵀ|x| + δ_{Box(-α, α)}(x)` attached to the weighted box constraint. -/
def weighted_l1_box_penalty
    (ω : ι → NNReal) (α : ι → ENNReal) : E → EReal :=
  fun x ↦
    ((∑ i, (ω i : ℝ) * |x i| : ℝ) : EReal) +
      extendedIndicator
        ((coord ⁻¹' Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E)) x

-- Proof sketch: unfold `weighted_l1_box_penalty`; the value is by definition the finite weighted
-- absolute-value sum, viewed in `EReal`, plus the indicator of the symmetric box.
/-- Evaluating `weighted_l1_box_penalty` gives the weighted absolute-value sum plus the indicator
of the symmetric box. -/
theorem weighted_l1_box_penalty_apply
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) :
    weighted_l1_box_penalty ω α x =
      ((∑ i, (ω i : ℝ) * |x i| : ℝ) : EReal) +
        extendedIndicator {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} x := by
  have hbox :
      (coord ⁻¹' Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E) =
        {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} := by
    ext y
    exact mem_symmetricBox_iff α y
  simp [weighted_l1_box_penalty, hbox]

-- Proof sketch: extensionality on `x`; unfold `weighted_l1_box_constraint_set`,
-- `weighted_l1_box_penalty`, `symmetricBox`, and `extendedIndicator`. On the box, the indicator
-- term is `0`, so the sublevel condition reduces to `∑ i, ω_i |x_i| ≤ β`; outside the box, the
-- indicator term is `⊤`, so the sublevel condition fails.
/-- The weighted box-constrained set is the `β`-sublevel set of the penalty
`x ↦ ωᵀ|x| + δ_{Box(-α, α)}(x)`. -/
theorem weighted_l1_box_constraint_set_eq_sublevel_weighted_l1_box_penalty
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) :
    weighted_l1_box_constraint_set ω α β =
      (weighted_l1_box_penalty ω α) ⁻¹' Set.Iic (β : EReal) := by
  have hbox :
      (coord ⁻¹' Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E) =
        {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} := by
    ext y
    exact mem_symmetricBox_iff α y
  ext x
  by_cases hx : ∀ i, ENNReal.ofReal |x i| ≤ α i
  · simp [weighted_l1_box_constraint_set, weighted_l1_box_penalty, extendedIndicator, hbox, hx,
      EReal.coe_le_coe_iff]
  · simp [weighted_l1_box_constraint_set, weighted_l1_box_penalty, extendedIndicator, hbox, hx,
      EReal.add_top_of_ne_bot, EReal.coe_ne_bot]

end

/-! ### Theorem_6_6 (from Chap06) -/
open scoped BigOperators

universe u v

noncomputable section

section SeparableSum

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}

/-- The separable sum of coordinatewise extended-real-valued functions on a finite dependent
product. -/
def separableSum (f : ∀ i, E i → EReal) : ((i : ι) → E i) → EReal :=
  fun x ↦ ∑ i, f i (x i)

-- Proof sketch: unfold `separableSum`; it is definitionally the finite coordinatewise sum.
/-- Evaluating `separableSum f` at `x` gives the finite sum of the coordinate functions applied to
the corresponding coordinates of `x`. -/
@[simp] theorem separableSum_apply (f : ∀ i, E i → EReal) (x : (i : ι) → E i) :
    separableSum f x = ∑ i, f i (x i) :=
  rfl

namespace PiLp

/-- The canonical `PiLp` view of the owner `separableSum`, obtained by evaluating the same
coordinatewise sum on the underlying block family. -/
abbrev separableSum (f : ∀ i, E i → EReal) : PiLp (2 : ENNReal) E → EReal :=
  fun x ↦ _root_.separableSum f x

/-- Evaluating the `PiLp` view `PiLp.separableSum` gives the same coordinatewise finite sum. -/
@[simp] theorem separableSum_apply (f : ∀ i, E i → EReal) (x : PiLp (2 : ENNReal) E) :
    PiLp.separableSum f x = ∑ i, f i (x i) :=
  rfl

end PiLp

end SeparableSum

section SeparableProx

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)]

/- Theorem 6.6 is `source-facing`: it asserts that the proximal operator of a separable sum on a
finite product is the product of the coordinatewise proximal operators. Domain sampling shows that
the canonical proximal owner already exists upstream as Chapter 6's set-valued mapping
`prox[...]`, while the genuinely new source-facing object here is only the coordinatewise finite
sum `separableSum`; on `PiLp (2 : ENNReal) E` it is used through the thin bridge
`PiLp.separableSum`. For
`EReal`-valued summands, the separability claim needs the textbook properness of each coordinate
function: no summand may take `⊥`, and every summand must have a nonempty finite domain. The
nonempty-domain part rules out degenerate everywhere-`⊤` coordinates, which would make the
product-space proximal objective identically `⊤` and destroy the coordinatewise product formula.
The theorem is therefore stated directly on `prox[...]`, with the product set expressed by
coordinatewise proximal membership and with coordinatewise properness retained from the textbook
closed proper convex setting.
-/

-- Proof sketch: unfold `prox[PiLp.separableSum f] x` and `prox[f i] (x i)` via
-- `mem_proximal_mapping_iff`, then unfold `proximal_objective` and `PiLp.separableSum`. Use
-- `PiLp.norm_sq_eq_of_L2` to rewrite the product-space quadratic term as the sum of the
-- coordinatewise quadratic terms. Properness supplies both the no-`⊥` condition and a finite
-- comparison point in every coordinate, so points with a `⊤` coordinate cannot become vacuous
-- minimizers of an identically infinite product objective. Under these hypotheses, `IsMinOn` over
-- `Set.univ` separates into the conjunction that each coordinate is a minimizer of its own
-- proximal objective.
-- Theorem 6.6 is proved below after the local coordinate-separation helpers.
/-- Helper for Theorem 6.6: coercing a finite real sum into `EReal` agrees with summing the
coerced real terms. -/
lemma ereal_coe_sum {κ : Type*} (s : Finset κ) (φ : κ → ℝ) :
    (((∑ i ∈ s, φ i : ℝ) : EReal)) = ∑ i ∈ s, ((φ i : ℝ) : EReal) := by
  classical
  -- Induct over the finite set and push the coercion through one inserted term at a time.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, hs]

/-- Helper for Theorem 6.6: the proximal objective of a separable sum is the finite sum of the
coordinatewise proximal objectives. -/
lemma separable_proximal_objective_eq_sum_coordinate_objectives
    (f : ∀ i, E i → EReal) (x y : PiLp (2 : ENNReal) E) :
    proximal_objective (PiLp.separableSum f) x y =
      ∑ i, proximal_objective (f i) (x i) (y i) := by
  -- Expand both the separable term and the `L²` penalty into coordinatewise finite sums.
  rw [proximal_objective_apply, PiLp.separableSum_apply, PiLp.norm_sq_eq_of_L2]
  simp_rw [PiLp.sub_apply]
  have hquad :
      ((((1 / 2 : ℝ) * ∑ i, ‖y i - x i‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        ∑ i, ((((1 / 2 : ℝ) * ‖y i - x i‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
    rw [Finset.mul_sum]
    simpa using
      (ereal_coe_sum Finset.univ
        (fun i : ι ↦ (1 / 2 : ℝ) * ‖y i - x i‖ ^ (2 : ℕ)))
  -- After distributing the quadratic penalty, each coordinate contributes independently.
  rw [hquad, ← Finset.sum_add_distrib]
  simp [proximal_objective_apply]

/-- Helper for Theorem 6.6: a finite sum of extended-real terms is never `⊥` when no summand is
`⊥`. -/
lemma ereal_sum_ne_bot {κ : Type*} (s : Finset κ) (φ : κ → EReal)
    (hφ : ∀ i ∈ s, φ i ≠ ⊥) :
    (∑ i ∈ s, φ i) ≠ ⊥ := by
  classical
  revert hφ
  refine Finset.induction_on s ?_ ?_
  · intro hφ
    simp
  · intro a s ha hs hφ
    -- Split off the head term and use `EReal.add_ne_bot_iff`.
    rw [Finset.sum_insert ha, EReal.add_ne_bot_iff]
    refine ⟨hφ a (by simp), hs ?_⟩
    intro i hi
    exact hφ i (by simp [hi])

/-- Helper for Theorem 6.6: a finite sum of extended-real terms is `< ⊤` when every summand is
`< ⊤`. -/
lemma ereal_sum_lt_top {κ : Type*} (s : Finset κ) (φ : κ → EReal)
    (hφ : ∀ i ∈ s, φ i < ⊤) :
    (∑ i ∈ s, φ i) < ⊤ := by
  classical
  revert hφ
  refine Finset.induction_on s ?_ ?_
  · intro hφ
    simp
  · intro a s ha hs hφ
    have ha_top : φ a < ⊤ := hφ a (by simp)
    have hs_top : (∑ i ∈ s, φ i) < ⊤ := hs (fun i hi ↦ hφ i (by simp [hi]))
    -- Adding one more finite head term keeps the finite sum finite.
    rw [Finset.sum_insert ha]
    exact EReal.add_lt_top (lt_top_iff_ne_top.mp ha_top) (lt_top_iff_ne_top.mp hs_top)

/-- Helper for Theorem 6.6: a global minimizer of the separable proximal objective has finite
coordinatewise proximal objectives. -/
lemma coordinate_objective_lt_top_of_isMinOn_separable
    (f : ∀ i, E i → EReal) (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (x y : PiLp (2 : ENNReal) E)
    (hy : IsMinOn (proximal_objective (PiLp.separableSum f) x) Set.univ y) (i : ι) :
    proximal_objective (f i) (x i) (y i) < ⊤ := by
  classical
  let G : ∀ i, E i → EReal := fun j u ↦ proximal_objective (f j) (x j) u
  have hG_ne_bot : ∀ j u, G j u ≠ ⊥ := by
    intro j u
    -- Properness rules out `⊥`, and the quadratic term is always finite.
    simpa [G, proximal_objective_apply, EReal.add_ne_bot_iff] using
      (show f j u ≠ ⊥ ∧ ((((1 / 2 : ℝ) * ‖u - x j‖ ^ (2 : ℕ)) : ℝ) : EReal) ≠ ⊥ from
        ⟨(hf_proper j).ne_bot u, EReal.coe_ne_bot _⟩)
  choose w hw using fun j ↦ (hf_proper j).effective_domain_nonempty
  let z : PiLp (2 : ENNReal) E := WithLp.toLp 2 w
  have hGz_top : ∀ j, G j (z j) < ⊤ := by
    intro j
    -- The properness witness gives a finite function value, and the quadratic term is finite.
    have hw_top : f j (w j) < ⊤ := by
      simpa using hw j
    simpa [G, z, proximal_objective_apply] using
      EReal.add_lt_top (lt_top_iff_ne_top.mp hw_top) (EReal.coe_ne_top _)
  have hz_top : proximal_objective (PiLp.separableSum f) x z < ⊤ := by
    -- Summing the finite coordinate objectives keeps the comparison point finite.
    rw [separable_proximal_objective_eq_sum_coordinate_objectives]
    exact ereal_sum_lt_top Finset.univ (fun j ↦ G j (z j)) (fun j _ ↦ hGz_top j)
  have hy_univ :
      ∀ v,
        proximal_objective (PiLp.separableSum f) x y ≤
          proximal_objective (PiLp.separableSum f) x v :=
    isMinOn_univ_iff.mp hy
  have hy_top :
      proximal_objective (PiLp.separableSum f) x y < ⊤ :=
    lt_of_le_of_lt (hy_univ z) hz_top
  have hsum_y_top :
      (∑ j, G j (y j)) < ⊤ := by
    rw [← separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := y)]
    exact hy_top
  by_contra htop
  have hrest_ne_bot :
      Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) ≠ ⊥ :=
    ereal_sum_ne_bot (Finset.univ.erase i) (fun j ↦ G j (y j))
      (fun j hj ↦ hG_ne_bot j (y j))
  have hsum_eq_top : (∑ j, G j (y j)) = ⊤ := by
    -- A single `⊤` coordinate forces the whole finite sum to be `⊤`.
    calc
      ∑ j, G j (y j) = G i (y i) + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) := by
        symm
        exact Finset.add_sum_erase Finset.univ (fun j ↦ G j (y j)) (Finset.mem_univ i)
      _ = ⊤ := by
        rw [
          show G i (y i) = ⊤ by exact le_antisymm le_top (not_lt.mp htop),
          EReal.top_add_of_ne_bot hrest_ne_bot
        ]
  exact (lt_top_iff_ne_top.mp hsum_y_top) hsum_eq_top

/-- Helper for Theorem 6.6: minimizing the separable proximal objective is equivalent to
minimizing each coordinatewise proximal objective. -/
lemma isMinOn_proximal_objective_separable_iff
    (f : ∀ i, E i → EReal) (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (x y : PiLp (2 : ENNReal) E) :
    IsMinOn (proximal_objective (PiLp.separableSum f) x) Set.univ y ↔
      ∀ i, IsMinOn (proximal_objective (f i) (x i)) Set.univ (y i) := by
  classical
  let G : ∀ i, E i → EReal := fun i u ↦ proximal_objective (f i) (x i) u
  have hG_ne_bot : ∀ i u, G i u ≠ ⊥ := by
    intro i u
    -- Properness rules out `⊥` at every coordinate objective.
    simpa [G, proximal_objective_apply, EReal.add_ne_bot_iff] using
      (show f i u ≠ ⊥ ∧ ((((1 / 2 : ℝ) * ‖u - x i‖ ^ (2 : ℕ)) : ℝ) : EReal) ≠ ⊥ from
        ⟨(hf_proper i).ne_bot u, EReal.coe_ne_bot _⟩)
  constructor
  · intro hy
    have hy_univ :
        ∀ z,
          proximal_objective (PiLp.separableSum f) x y ≤
            proximal_objective (PiLp.separableSum f) x z :=
      isMinOn_univ_iff.mp hy
    intro i
    rw [isMinOn_univ_iff]
    intro u
    let z : PiLp (2 : ENNReal) E := WithLp.toLp 2 (Function.update (fun j ↦ y j) i u)
    let r : EReal := Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j))
    have hr_ne_bot : r ≠ ⊥ := by
      -- The unchanged coordinates stay away from `⊥`.
      exact ereal_sum_ne_bot (Finset.univ.erase i) (fun j ↦ G j (y j))
        (fun j hj ↦ hG_ne_bot j (y j))
    have hGy_top : ∀ j, G j (y j) < ⊤ := by
      intro j
      exact coordinate_objective_lt_top_of_isMinOn_separable f hf_proper x y hy j
    have hr_top : r < ⊤ := by
      -- The unchanged remainder is finite because every coordinate objective at `y` is finite.
      exact ereal_sum_lt_top (Finset.univ.erase i) (fun j ↦ G j (y j))
        (fun j hj ↦ hGy_top j)
    have hr_coe : ((r.toReal : ℝ) : EReal) = r :=
      EReal.coe_toReal (lt_top_iff_ne_top.mp hr_top) hr_ne_bot
    have hyz :
        ∑ j, G j (y j) ≤ ∑ j, G j (z j) := by
      -- Rewrite the global minimizer inequality using the separable decomposition.
      rw [← separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := y),
        ← separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := z)]
      exact hy_univ z
    have hsum_y :
        ∑ j, G j (y j) = G i (y i) + r := by
      -- Split the finite sum into the `i`-th coordinate plus the unchanged remainder.
      calc
        ∑ j, G j (y j) = G i (y i) + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) := by
          symm
          exact Finset.add_sum_erase Finset.univ (fun j ↦ G j (y j)) (Finset.mem_univ i)
        _ = G i (y i) + r := by simp [r]
    have hsum_z_rest :
        Finset.sum (Finset.univ.erase i) (fun j ↦ G j (z j)) =
          Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) := by
      -- Away from the updated coordinate, the new point has the same coordinates as `y`.
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [z, Function.update, hj_ne]
    have hsum_z :
        ∑ j, G j (z j) = G i u + r := by
      -- The update point changes only the `i`-th coordinate, so the remainder is identical.
      calc
        ∑ j, G j (z j) = G i (z i) + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (z j)) := by
          symm
          exact Finset.add_sum_erase Finset.univ (fun j ↦ G j (z j)) (Finset.mem_univ i)
        _ = G i u + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (z j)) := by
          simp [z, Function.update]
        _ = G i u + Finset.sum (Finset.univ.erase i) (fun j ↦ G j (y j)) := by
          rw [hsum_z_rest]
        _ = G i u + r := by simp [r]
    have hcancel :
        G i (y i) + ((r.toReal : ℝ) : EReal) ≤
          G i u + ((r.toReal : ℝ) : EReal) := by
      simpa [hsum_y, hsum_z, hr_coe] using hyz
    -- Cancel the common finite remainder to recover the coordinatewise minimizing inequality.
    exact ((EReal.addLECancellable_coe r.toReal).add_le_add_iff_right).mp hcancel
  · intro hy
    rw [isMinOn_univ_iff]
    intro z
    have hy_univ : ∀ i u, G i (y i) ≤ G i u := by
      intro i u
      exact isMinOn_univ_iff.mp (hy i) u
    -- Sum the coordinatewise minimizing inequalities to recover the product-space minimizer.
    rw [separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := y),
      separable_proximal_objective_eq_sum_coordinate_objectives (f := f) (x := x) (y := z)]
    exact Finset.sum_le_sum (fun i hi ↦ hy_univ i (z i))

/-- Theorem 6.6: for a separable extended-real-valued function on a finite Cartesian product,
the proximal operator at `x` is the set of points whose `i`-th coordinate lies in the proximal
operator of the `i`-th summand at `x i`. This is the textbook identity
`prox_f (x₁, …, x_m) = prox_{f₁} (x₁) × ⋯ × prox_{f_m} (x_m)` expressed on
`PiLp (2 : ENNReal) E`. -/
theorem prox_separableSum_eq_coordinatewise
    (f : ∀ i, E i → EReal) (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (x : PiLp (2 : ENNReal) E) :
    prox[PiLp.separableSum f] x = {y : PiLp (2 : ENNReal) E | ∀ i, y i ∈ prox[f i] (x i)} := by
  ext y
  -- Rewrite both sides as global minimizer statements and separate the finite sum by coordinates.
  rw [mem_proximal_mapping_iff,
    isMinOn_proximal_objective_separable_iff (f := f) (hf_proper := hf_proper) (x := x) (y := y)]
  simp [mem_proximal_mapping_iff]

-- Proof sketch: rewrite membership using `prox_separableSum_eq_coordinatewise`; membership in the
-- resulting set is exactly the coordinatewise proximal-membership condition.
/-- A point `y` belongs to the proximal set of a finite separable sum exactly when each coordinate
belongs to the proximal set of the corresponding summand. -/
@[simp] theorem mem_prox_separableSum_iff
    {f : ∀ i, E i → EReal} (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    {x y : PiLp (2 : ENNReal) E} :
    y ∈ prox[PiLp.separableSum f] x ↔ ∀ i, y i ∈ prox[f i] (x i) := by
  rw [prox_separableSum_eq_coordinatewise f hf_proper x]
  rfl

end SeparableProx
