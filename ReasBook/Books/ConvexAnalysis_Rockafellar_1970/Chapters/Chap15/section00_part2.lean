import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.MetricSpace.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_15_0_12 (from Chap03) -/
noncomputable section

universe u v

attribute [local instance] Function.instDecidableLT

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.12 defines when a gauge on `R^n` is a norm by adding everywhere
  finiteness, symmetry, and strict positivity away from the origin. The owner is stated on a
  scalar-generic additive group, since the reused gauge, convexity, and symmetry ingredients
  already live there; specializing to `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the
  source ambient.
- `core/canonical`: the owner predicate already present in the chapter is the imported gauge class
  `IsGauge`, while the symmetry clause is the canonical mathlib predicate `Function.Even`.
- `bridge/view`: the equivalent clause list is most naturally rendered by companion theorems giving
  subadditivity, reconstruction from clauses (a)–(d), and absolute homogeneity.

Domain-style sampling used here:
- `Function.IsConvex` from `Theorem_4_2`, reused through the imported gauge owner `IsGauge`;
- `Function.PositivelyHomogeneous` from `Definition_4_8`, again reused through `IsGauge`;
- `IsGauge` from `Text_15_0_1`;
- `Function.Even` from the even-function API;
- the chapter's pointwise scalar-valued finiteness layer `k x < ⊤`, with the `EReal`/`toReal`
  bridge kept as a real-specialized downstream theorem;
- mathlib's seminorm/norm API as a comparison point confirming that subadditivity belongs to the
  gauge owner while symmetry plus positive definiteness is downstream structure rather than a
  second owner abstraction here.

Primitive data vs derived API:
- primitive owner: being a norm-gauge;
- derived bridge: the clause-based reconstruction theorem, and the absolute-value homogeneity
  consequence `IsGaugeNorm.map_smul_eq_abs`.

Layer target: `source-facing`, because the source is refining the chapter's gauge notion rather
than replacing it by a bundled norm.
-/

/-- Text 15.0.12: a gauge is a norm when it is finite everywhere, symmetric, and strictly positive
away from the origin. Here finiteness is recorded as `k x < ⊤`. Specializing `𝕜 = ℝ` and
`E = EuclideanSpace ℝ (Fin n)` recovers the source statement. -/
class IsGaugeNorm (k : E → WithBotTop 𝕜) : Prop extends IsGauge k where
  finite : ∀ x : E, k x < ⊤
  symmetric : Function.Even k
  pos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < k x

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm, viewed as a `WithBotTop ℝ`-valued gauge, is a canonical norm-gauge. -/
instance : IsGaugeNorm (fun x : E ↦ (‖x‖ : WithBotTop ℝ)) where
  toIsGauge :=
    { convex := by
        exact Function.isConvex_coe_of_convexOn_univ convexOn_univ_norm
      nonneg := by
        intro x
        exact WithBotTop.coe_le_coe.mpr (norm_nonneg x)
      homogeneous := by
        intro a x
        change ((‖((a : ℝ) • x)‖ : ℝ) : WithBotTop ℝ) =
          ((((a : ℝ) * ‖x‖ : ℝ)) : WithBotTop ℝ)
        simp [norm_smul, Real.norm_of_nonneg a.2.le]
      map_zero := by
        change ((‖(0 : E)‖ : ℝ) : WithBotTop ℝ) = (0 : WithBotTop ℝ)
        simp }
  finite x := by
    exact lt_top_iff_ne_top.mpr (by simp)
  symmetric := by
    intro x
    simp
  pos := by
    intro x hx
    exact WithBotTop.coe_lt_coe.mpr (norm_pos_iff.mpr hx)

end

section

variable {𝕜 : Type v} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: split on the sign of `λ`. For `λ > 0`, use positive homogeneity. For `λ < 0`,
-- rewrite `λ • x = (-λ) • (-x)` and use evenness. For `λ = 0`, both sides vanish.
private theorem map_smul_eq_abs_of_even {k : E → WithBotTop 𝕜}
    (hhom : k.PositivelyHomogeneous 𝕜) (hzero : k 0 = 0) (heven : Function.Even k)
    (a : 𝕜) (x : E) :
    k (a • x) = |a| • k x := by
  by_cases hpos : 0 < a
  · calc
      k (a • x) = a • k x := hhom.map_smul hpos x
      _ = |a| • k x := by rw [abs_of_pos hpos]
  · by_cases hneg : a < 0
    · have hneg' : 0 < -a := neg_pos.mpr hneg
      calc
        k (a • x) = k ((-a) • (-x)) := by simp
        _ = (-a) • k (-x) := hhom.map_smul hneg' (-x)
        _ = (-a) • k x := by rw [heven x]
        _ = |a| • k x := by rw [abs_of_neg hneg]
    · have ha : a = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [ha, hzero]

namespace IsGaugeNorm

variable {k : E → WithBotTop 𝕜} [hk : IsGaugeNorm k]

-- Proof sketch: combine the inherited positive homogeneity from `IsGauge` with the symmetry field
-- of `IsGaugeNorm`, then apply the generic absolute-homogeneity bridge above.
/-- A norm-gauge is absolutely homogeneous. -/
theorem map_smul_eq_abs (a : 𝕜) (x : E) :
    k (a • x) = |a| • k x :=
  map_smul_eq_abs_of_even hk.toIsGauge.homogeneous hk.toIsGauge.map_zero hk.symmetric a x

end IsGaugeNorm

end

section

variable {𝕜 : Type v} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable [ZeroLEOneClass 𝕜] [AddLeftMono 𝕜] [PosMulMono 𝕜] [PosMulReflectLT 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

namespace IsGaugeNorm

variable {k : E → WithBotTop 𝕜} [hk : IsGaugeNorm k]

-- Proof sketch: a norm-gauge is in particular a gauge, so Theorem 4.7 recovers subadditivity
-- from the inherited convexity and positive homogeneity once `⊥` is excluded by nonnegativity.
/-- A norm-gauge is subadditive. -/
theorem subadditive (x y : E) :
    k (x + y) ≤ k x + k y :=
  (Function.isConvex_iff_subadditive_of_positivelyHomogeneous
    hk.toIsGauge.homogeneous (fun z ↦ by
      have hnonneg : (0 : WithBotTop 𝕜) ≤ k z := hk.toIsGauge.nonneg z
      intro hz
      simp [hz] at hnonneg)).1 hk.toIsGauge.convex x y

end IsGaugeNorm

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

namespace IsGaugeNorm

variable {k : E → WithBotTop 𝕜} [hk : IsGaugeNorm k]

-- Proof sketch: strict positivity away from the origin gives one direction, while the inherited
-- gauge axiom `k 0 = 0` gives the reverse implication.
/-- A norm-gauge vanishes exactly at the origin. -/
theorem eq_zero_iff {x : E} :
    k x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hneq
    have hpos : (0 : WithBotTop 𝕜) < k x := hk.pos hneq
    simp [hx] at hpos
  · intro hx
    subst hx
    exact hk.toIsGauge.map_zero

/-- A norm-gauge never takes the value `⊤`. -/
theorem ne_top (x : E) :
    k x ≠ ⊤ :=
  ne_of_lt (hk.finite x)

/-- A norm-gauge never takes the value `⊥`. -/
theorem ne_bot (x : E) :
    k x ≠ ⊥ := by
  intro hx
  have hnonneg : (0 : WithBotTop 𝕜) ≤ k x := hk.toIsGauge.nonneg x
  simp [hx] at hnonneg

end IsGaugeNorm

end

section

variable {𝕜 : Type v} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

namespace IsGaugeNorm

-- Proof sketch: the hypotheses are exactly clauses (a) through (d) together with everywhere
-- scalar-valuedness, encoded by membership in the coercion range of `WithBotTop 𝕜`.
-- Theorem 4.7 gives convexity from subadditivity and positive homogeneity; the
-- scalar-valued hypothesis rules out `⊥`, so symmetry and positivity recover nonnegativity and the
-- zero value needed to build the inherited gauge structure before packaging the norm-gauge fields.
/-- A scalar-valued function satisfying clauses (a) through (d) is a norm-gauge. -/
theorem of_coe_subadditive_homogeneous_even_pos {k : E → WithBotTop 𝕜}
    (hfinite : ∀ x : E, ∃ r : 𝕜, k x = (r : WithBotTop 𝕜))
    (hsubadd : ∀ x₁ x₂ : E, k (x₁ + x₂) ≤ k x₁ + k x₂)
    (hhom : k.PositivelyHomogeneous 𝕜)
    (heven : Function.Even k)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < k x) :
    IsGaugeNorm k := by
  have hk_ne_bot : ∀ x : E, k x ≠ ⊥ := by
    intro x
    rcases hfinite x with ⟨r, hr⟩
    simp [hr]
  have hk_top : ∀ x : E, k x < ⊤ := by
    intro x
    rcases hfinite x with ⟨r, hr⟩
    exact lt_top_iff_ne_top.mpr (by simp [hr])
  have hzero : k 0 = 0 := by
    rcases hfinite 0 with ⟨r, hr⟩
    have hscale : k ((2 : 𝕜) • (0 : E)) = (2 : 𝕜) • k 0 :=
      hhom.map_smul (by norm_num : 0 < (2 : 𝕜)) (0 : E)
    have hscale' : (r : WithBotTop 𝕜) = ((2 * r : 𝕜) : WithBotTop 𝕜) := by
      simpa [hr, smul_eq_mul] using hscale
    have hreal : r = 2 * r := by
      exact WithBotTop.coe_eq_coe_iff.mp hscale'
    have hr_zero : r = 0 := by linarith
    simp [hr, hr_zero]
  refine
    { toIsGauge := ?_, finite := hk_top, symmetric := heven, pos := hpos }
  refine
    { convex :=
        (Function.isConvex_iff_subadditive_of_positivelyHomogeneous hhom hk_ne_bot).2 hsubadd
      nonneg := ?_
      homogeneous := hhom
      map_zero := by simp [hzero] }
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [hzero]
  · exact le_of_lt (hpos hx)

end IsGaugeNorm

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

namespace IsGaugeNorm

variable {k : E → WithBotTop ℝ} [hk : IsGaugeNorm k]

/-- The real value underlying a norm-gauge vanishes exactly at the origin. -/
theorem toReal_eq_zero_iff {x : E} :
    EReal.toReal (k x) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    rcases (EReal.toReal_eq_zero_iff).1 hx with hzero | htop | hbot
    · exact eq_zero_iff.1 hzero
    · exact (ne_top x htop).elim
    · exact (ne_bot x hbot).elim
  · intro hx
    exact (EReal.toReal_eq_zero_iff).2 (Or.inl (eq_zero_iff.2 hx))

end IsGaugeNorm

end

/-! ### Text_15_0_13 (from Chap03) -/
noncomputable section

open scoped BigOperators
open scoped GaugePolar
open scoped Rockafellar

section

variable {ι : Type*} [Fintype ι]

section CoordinateL1GaugeOwner

variable {𝕜 : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜]

/-- The coordinate `ℓ¹` norm on a finite coordinate space, viewed as a
`WithBotTop 𝕜`-valued gauge. Specializing `𝕜 = ℝ` and `ι = Fin n` recovers the textbook
function on `R^n`. -/
def coordinateL1Gauge (ι : Type*) [Fintype ι] : (ι → 𝕜) → WithBotTop 𝕜 :=
  fun x ↦ ((∑ i, |x i|) : 𝕜)

end CoordinateL1GaugeOwner

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]

local notation "E" => ι → 𝕜

local instance : HasPairing E E 𝕜 where
  pairing x y := ∑ i, x i * y i
local instance : HasPairing E E (WithBotTop 𝕜) := instHasPairingWithBotTop

local notation "linftyGauge" => Function.toWithBotTop (linftyNorm (ι := ι) (𝕜 := 𝕜))
local notation "l1Gauge" => (coordinateL1Gauge (𝕜 := 𝕜) ι : E → WithBotTop 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: the text defines the concrete function
  `k(x) = max {|ξ₁|, ..., |ξₙ|}` on a finite coordinate space, identifies its polar gauge with
  the coordinate `ℓ¹` norm, and concludes that these two norms form a polar pair. Specializing
  `ι = Fin n` recovers the textbook `R^n` statement.
- `core/canonical`: the owner abstractions already present in the project are the Chapter 1
  owners `coordinateL1Ball` and `linftyNorm`, the theorem
  `supportFunction_coordinateL1Ball_eq_linftyNorm`, the source-side polar-gauge construction
  `gauge_polar` from `Text_15_0_5`, and the norm-gauge predicate `IsGaugeNorm` from
  `Text_15_0_12`.
- `bridge/view`: `supportFunction_coordinateL1Ball_eq_linftyNorm` keeps the source's explicit
  coordinate `ℓ¹` unit ball as the bridge presentation of that canonical `L^∞` norm, while the
  coordinate `ℓ¹` norm remains the explicit finite sum `∑ i, |x i|`, lifted to
  `WithBotTop 𝕜`.

Domain-style sampling used here:
- the Chapter 1 owner `coordinateL1Ball`;
- the Chapter 1 owner `linftyNorm`;
- the Chapter 1 owner theorem `supportFunction_coordinateL1Ball_eq_linftyNorm`;
- the bridge theorem `supportFunction_coordinateL1Ball_eq_linftyNorm`;
- `gauge_polar` from `Text_15_0_5`;
- `IsGaugeNorm` from `Text_15_0_12`;
- the nearby finite-family owner `lpCoordinatePower` from `Text_15_0_22`;
- the owner function `supportFunction` attached to subsets of a finite coordinate space.

Primitive data vs derived API:
- primitive source-facing data: the concrete coordinate `ℓ¹` gauge;
- owner-level reused data: the concrete max-coordinate norm is expressed through the canonical
  owner `linftyNorm`;
- bridge/source view: `supportFunction_coordinateL1Ball_eq_linftyNorm` relates that owner to the
  `supportFunction` of the explicit coordinate `ℓ¹` unit ball;
- derived API: each is a norm-gauge, and each is the polar gauge of the other.

Layer target: `source-facing`, stated on the chapter's canonical finite-family owner level rather
than the concrete `𝕜 = ℝ`, `ι = Fin n` display specialization, with the `L^∞` owner reused from
Text 5.5.0.5 rather than redefined here.
-/

-- Proof sketch: rewrite the polar-gauge defining inequalities for the coordinate-maximum owner as
-- `⟪x, xStar⟫ ≤ μStar * max_i |x i|`. If `μStar = ∑ i |xStar i|`, Hölder's
-- `ℓ∞`-`ℓ¹` estimate gives an admissible majorant. Conversely, evaluate on the sign vector of
-- `xStar` to show no smaller majorant can work, yielding the exact coordinate `ℓ¹` formula.
/-- The polar gauge of the coordinate-maximum norm is the coordinate `ℓ¹` norm. -/
theorem gauge_polar_linftyNorm_eq_coordinateL1Gauge
    :
    ((linftyGauge)ᵒ : E → WithBotTop 𝕜) = l1Gauge := sorry

-- Proof sketch: the coordinate `ℓ¹` norm is finite, symmetric, positively homogeneous, and
-- subadditive by the corresponding scalar properties of absolute value and finite sums. Strict
-- positivity away from the origin follows because some coordinate of a nonzero vector has
-- nonzero absolute value and therefore contributes positively to the sum.
/-- The coordinate `ℓ¹` norm defines a norm-gauge on a finite coordinate space. -/
theorem coordinateL1Gauge_isGaugeNorm :
    IsGaugeNorm l1Gauge := sorry

-- Proof sketch: express `gauge_polar coordinateL1Gauge x` through the defining admissible-majorant
-- inequalities `⟪y, x⟫ ≤ μ * ∑ i |y i|`. Testing these inequalities on the signed coordinate basis
-- vectors forces `μ` to dominate every `|x i|`, so `μ` must dominate the coordinate supremum.
-- Conversely, taking `μ = max_i |x i|` makes the inequality hold by bounding each term
-- `|y i| |x i|` by `μ |y i|` and summing.
/-- The polar gauge of the coordinate `ℓ¹` norm is the maximum-coordinate norm. -/
theorem gauge_polar_coordinateL1Gauge_eq_linftyNorm
    :
    (l1Gaugeᵒ : E → WithBotTop 𝕜) = linftyGauge := sorry

end

/-! ### Text_15_0_14 (from Chap03) -/
/- 
Source/core/bridge triage:
- `source-facing`: Text 15.0.14 defines a metric on a carrier by the distance clauses
  positivity/separation, symmetry, and the triangle inequality.
- `core/canonical`: the primitive distance owner is `PseudoMetricSpace`; the extra primitive
  separation datum is a witness `dist x y = 0 → x = y`.
- `bridge/view`: the textbook clauses are exposed by `dist_nonneg`, `dist_eq_zero`, `dist_pos`,
  `dist_comm`, and `dist_triangle`, together with the owner bridge
  `MetricSpace.toPseudoMetricSpace`.
- Primitive data vs derived API: symmetry and triangle inequality belong to the primitive
  pseudometric layer together with nonnegativity; separation is added by the primitive witness
  `dist x y = 0 → x = y`; strict positivity away from the diagonal is then derived.
- Domain-style sampling used here: `PseudoMetricSpace`, `MetricSpace.toPseudoMetricSpace`,
  `dist_nonneg`, `dist_eq_zero`, `dist_pos`, `dist_comm`, `dist_triangle`, and
  `eq_of_dist_eq_zero`.
- Layer target: `core/canonical`, since the textbook notion is exactly the standard metric-space
  structure.
-/

/- A metric is a separated pseudometric, so the primitive distance-data owner is
`PseudoMetricSpace`. -/
recall PseudoMetricSpace

/- Text 15.0.14: a metric is the canonical mathlib notion `MetricSpace`. -/
recall MetricSpace

/- Every metric carries its underlying pseudometric owner. -/
recall MetricSpace.toPseudoMetricSpace

/- In a metric space, the primitive separation witness is
`dist x y = 0 → x = y`. -/
recall eq_of_dist_eq_zero

/- In a metric space, the distance vanishes exactly on equal points, matching the textbook
separation clause. -/
recall dist_eq_zero

/- In a pseudometric space, distances are nonnegative, matching the textbook positivity base
clause. -/
recall dist_nonneg

/- In a metric space, distinct points have strictly positive distance, matching the textbook
positivity clause. -/
recall dist_pos

/- Symmetry is already available at the pseudometric layer:
`dist x y = dist y x`. -/
recall dist_comm

/- The triangle inequality is likewise pseudometric-level:
`dist x z ≤ dist x y + dist y z`. -/
recall dist_triangle

section

variable {α : Type*}

namespace PseudoMetricSpace

/-- A pseudometric plus the primitive separation witness gives the canonical metric owner. -/
@[reducible] def toMetricSpaceOfEqOfDistEqZero [PseudoMetricSpace α]
    (hsep : ∀ {x y : α}, dist x y = 0 → x = y) : MetricSpace α :=
  { ‹PseudoMetricSpace α› with
    eq_of_dist_eq_zero := fun {x y} hxy ↦ hsep hxy }

/-- Primitive separation bridge at the pseudometric layer. -/
theorem dist_eq_zero_iff_of_eq_of_dist_eq_zero [PseudoMetricSpace α]
    (hsep : ∀ {x y : α}, dist x y = 0 → x = y) (x y : α) :
    dist x y = 0 ↔ x = y := by
  letI : MetricSpace α := toMetricSpaceOfEqOfDistEqZero hsep
  exact dist_eq_zero

/-- Separation clauses at the pseudometric layer, derived through the canonical metric owner. -/
theorem dist_separation_clauses [PseudoMetricSpace α]
    (hsep : ∀ {x y : α}, dist x y = 0 → x = y) (x y : α) :
    (dist x y = 0 ↔ x = y) ∧
      (0 < dist x y ↔ x ≠ y) := by
  letI : MetricSpace α := toMetricSpaceOfEqOfDistEqZero hsep
  exact ⟨dist_eq_zero_iff_of_eq_of_dist_eq_zero hsep x y, dist_pos⟩

/-- The primitive pseudometric distance clauses: nonnegativity, symmetry, and the triangle
inequality. -/
theorem dist_basic_clauses [PseudoMetricSpace α] (x y z : α) :
    (0 ≤ dist x y) ∧
      dist x y = dist y x ∧
      dist x z ≤ dist x y + dist y z := by
  exact ⟨dist_nonneg, dist_comm x y, dist_triangle x y z⟩

end PseudoMetricSpace

namespace MetricSpace

/-- Separation in the canonical metric owner: vanishing distance is equivalent to equality, and
strict positivity is equivalent to inequality. -/
theorem dist_separation_clauses [MetricSpace α] (x y : α) :
    (dist x y = 0 ↔ x = y) ∧
      (0 < dist x y ↔ x ≠ y) := by
  exact ⟨dist_eq_zero, dist_pos⟩

/-- Text 15.0.14 in canonical ambient form: a metric distance satisfies separation, strict
positivity away from the diagonal, symmetry, and the triangle inequality. -/
theorem dist_clauses [MetricSpace α] (x y z : α) :
    (dist x y = 0 ↔ x = y) ∧
      (0 < dist x y ↔ x ≠ y) ∧
      (0 ≤ dist x y) ∧
      dist x y = dist y x ∧
      dist x z ≤ dist x y + dist y z := by
  exact ⟨dist_eq_zero, dist_pos, dist_nonneg, dist_comm x y, dist_triangle x y z⟩

end MetricSpace

namespace PseudoMetricSpace

/-- Text 15.0.14 clause package at the primitive pseudometric layer, with separation supplied as
primitive data. -/
theorem dist_clauses [PseudoMetricSpace α]
    (hsep : ∀ {x y : α}, dist x y = 0 → x = y) (x y z : α) :
    (dist x y = 0 ↔ x = y) ∧
      (0 < dist x y ↔ x ≠ y) ∧
      (0 ≤ dist x y) ∧
      dist x y = dist y x ∧
      dist x z ≤ dist x y + dist y z := by
  letI : MetricSpace α := toMetricSpaceOfEqOfDistEqZero hsep
  simpa using (MetricSpace.dist_clauses (α := α) x y z)

end PseudoMetricSpace

end

/-! ### Text_15_0_15 (from Chap03) -/
universe u

/-!
Source/core/bridge triage:
- `source-facing`: Text 15.0.15 gives the `0/1` distance formula for the discrete metric.
- `core/canonical`: the primitive owner is `PseudoEMetricSpace.discrete`; separation and
  real-valued distance are bridge layers.
- `derived/bridge`: `EMetricSpace.discrete`, `PseudoMetricSpace.discrete`, and
  `MetricSpace.discrete`.
- `bridge/view`: coordinate-model textbook displays are specializations of this same owner-level
statement.
- Primitive data vs derived API: the primitive data is exactly the `0/1` extended-distance
formula with symmetry and triangle laws; separation and the real-valued metric interface are
derived bridges.
- Layer target: `core/canonical`, with a primitive `PseudoEMetricSpace` owner and derived
  `EMetricSpace`/`MetricSpace` bridges.
-/

namespace PseudoEMetricSpace

/-- Text 15.0.15 at the primitive owner layer: the discrete pseudo-extended metric. -/
@[reducible] noncomputable def discrete (α : Type u) : PseudoEMetricSpace α := by
  classical
  refine
    { edist := fun x y ↦ if x = y then 0 else 1
      edist_self := fun x ↦ by simp
      edist_comm := fun x y ↦ by
        by_cases hxy : x = y
        · simp [hxy]
        · simp [hxy, Ne.symm hxy]
      edist_triangle := fun x y z ↦ by
        by_cases hxy : x = y <;> by_cases hxz : x = z <;> by_cases hyz : y = z <;> simp_all }

section

attribute [local instance] Classical.decEq

variable {α : Type u}

/-- The primitive `0/1` formula for the discrete extended metric. -/
@[simp] theorem edist_discrete (x y : α) :
    (PseudoEMetricSpace.discrete α).edist x y = if x = y then 0 else 1 := by
  rfl

/-- The discrete extended metric takes only finite values. -/
@[simp] theorem edist_discrete_ne_top (x y : α) :
    (PseudoEMetricSpace.discrete α).edist x y ≠ ⊤ := by
  by_cases hxy : x = y <;> simp [edist_discrete, hxy]

end

end PseudoEMetricSpace

namespace EMetricSpace

/-- Text 15.0.15 at the separated owner layer, derived from
`PseudoEMetricSpace.discrete`. -/
@[reducible] noncomputable def discrete (α : Type u) : EMetricSpace α := by
  classical
  refine
    { PseudoEMetricSpace.discrete α with
      eq_of_edist_eq_zero := ?_ }
  intro x y hxy
  by_cases h : x = y
  · exact h
  · have hne : (PseudoEMetricSpace.discrete α).edist x y ≠ 0 := by
      simp [PseudoEMetricSpace.edist_discrete, h]
    exact (hne hxy).elim

section

attribute [local instance] Classical.decEq

variable {α : Type u}

/-- The `0/1` formula for `EMetricSpace.discrete`. -/
@[simp] theorem edist_discrete (x y : α) :
    (EMetricSpace.discrete α).edist x y = if x = y then 0 else 1 := by
  rfl

/-- The separated discrete extended metric still takes only finite values. -/
@[simp] theorem edist_discrete_ne_top (x y : α) :
    (EMetricSpace.discrete α).edist x y ≠ ⊤ := by
  simpa [EMetricSpace.edist_discrete] using
    (PseudoEMetricSpace.edist_discrete_ne_top (α := α) x y)

end

end EMetricSpace

namespace PseudoMetricSpace

/-- The real-valued pseudometric bridge for Text 15.0.15. -/
@[reducible] noncomputable def discrete (α : Type u) : PseudoMetricSpace α := by
  exact @PseudoEMetricSpace.toPseudoMetricSpace α (PseudoEMetricSpace.discrete α)
    (fun x y ↦ PseudoEMetricSpace.edist_discrete_ne_top (α := α) x y)

section

attribute [local instance] Classical.decEq

variable {α : Type u}

/-- The `0/1` formula at the pseudometric bridge layer. -/
@[simp] theorem dist_discrete (x y : α) :
    (PseudoMetricSpace.discrete α).dist x y = if x = y then 0 else 1 := by
  letI : PseudoMetricSpace α := PseudoMetricSpace.discrete α
  change (EDist.edist x y).toReal = if x = y then 0 else 1
  rw [PseudoEMetricSpace.edist_discrete (α := α) x y]
  by_cases hxy : x = y <;> simp [hxy]

/-- The corresponding extended-distance form at the pseudometric bridge layer. -/
@[simp] theorem edist_discrete (x y : α) :
    (PseudoMetricSpace.discrete α).edist x y = if x = y then 0 else 1 := by
  letI : PseudoMetricSpace α := PseudoMetricSpace.discrete α
  change edist x y = if x = y then 0 else 1
  exact PseudoEMetricSpace.edist_discrete (α := α) x y

end

end PseudoMetricSpace

namespace MetricSpace

/-- Text 15.0.15: the canonical discrete metric on any carrier `α`, with distance `0` on the
diagonal and `1` off the diagonal. -/
@[reducible]
noncomputable def discrete (α : Type u) : MetricSpace α := by
  exact @EMetricSpace.toMetricSpace α (EMetricSpace.discrete α)
    (fun x y ↦ EMetricSpace.edist_discrete_ne_top (α := α) x y)

section

attribute [local instance] Classical.decEq

variable {α : Type u}

/-- Text 15.0.15 at the canonical owner layer: under the discrete metric on any carrier `α`,
the distance is exactly the `0/1` formula. Coordinate-model textbook displays are obtained by
specialization of this same theorem. -/
@[simp] theorem dist_discrete (x y : α) :
    (MetricSpace.discrete α).dist x y = if x = y then 0 else 1 := by
  letI : MetricSpace α := MetricSpace.discrete α
  change dist x y = if x = y then 0 else 1
  have hedist : edist x y = if x = y then 0 else 1 := by
    exact EMetricSpace.edist_discrete (α := α) x y
  rw [dist_edist, hedist]
  by_cases hxy : x = y <;> simp [hxy]

/-- The corresponding extended-distance form of `MetricSpace.dist_discrete`. -/
@[simp] theorem edist_discrete (x y : α) :
    (MetricSpace.discrete α).edist x y = if x = y then 0 else 1 := by
  letI : MetricSpace α := MetricSpace.discrete α
  change edist x y = if x = y then 0 else 1
  exact EMetricSpace.edist_discrete (α := α) x y

end

end MetricSpace

/-! ### Text_15_0_16 (from Chap03) -/
section

open AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-!
Source/core/bridge triage:
- `source-facing`: Text 15.0.16 defines a special class of metrics on `R^n` by adding translation
  invariance and affine-segment scaling to the metric axioms. The source specialization to `R^n`
  is recovered by taking `E = EuclideanSpace ℝ (Fin n)`.
- `core/canonical`: the owner abstraction for the metric axioms is mathlib's `MetricSpace`, while
  the translation-invariance clause is already owned by `IsIsometricVAdd Eᵃᵒᵖ E`.
- `bridge/view`: the affine-segment formula is most naturally expressed using the canonical affine
  owner `AffineMap.lineMap`, while the source coordinate formula `((1 - t) • x) + t • y` is a
  companion view.
- Domain-style sampling used here: `MetricSpace`, `IsIsometricVAdd Eᵃᵒᵖ E` with its theorem
  `dist_add_right`, `AffineMap.lineMap`, and the normed-space theorem `dist_left_lineMap` as the
  canonical affine-segment distance pattern; on the chapter side, `IsGaugeNorm.map_smul_eq_abs`
  is the matching radial-homogeneity owner.
- Primitive data vs derived API: the metric owner `ρ : MetricSpace E` is primitive data; the only
  primitive extra axiom beyond the translation-invariant owner is radial scaling from the origin,
  while the affine-segment identities are derived API.
- Layer target: `source-facing`, implemented as a `Prop`-valued refinement of a fixed
  `MetricSpace E`.
-/

namespace MetricSpace

/-- Text 15.0.16: a Minkowski metric on a real vector space is a metric whose distance is
translation invariant and whose distance from `0` to `t • x` equals `t` times the distance from
`0` to `x` for every `t ∈ [0, 1]`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `R^n` formulation. -/
class IsMinkowskiMetric (ρ : MetricSpace E) : Prop extends (letI := ρ; IsIsometricVAdd Eᵃᵒᵖ E) where
  dist_zero_smul (x : E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ρ.dist (0 : E) (t • x) = t * ρ.dist (0 : E) x

attribute [instance] IsMinkowskiMetric.toIsIsometricVAdd

namespace IsMinkowskiMetric

variable {ρ : MetricSpace E} [hρ : ρ.IsMinkowskiMetric]

/-- In a Minkowski metric, the affine-segment point is at distance `t * dist x y` from the left
endpoint for every `t ∈ [0, 1]`. -/
theorem dist_left_lineMap (x y : E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ρ.dist x (lineMap x y t) = t * ρ.dist x y := by
  letI := ρ
  have hxy : ρ.dist (0 : E) (y - x) = ρ.dist x y := by
    simpa using (dist_add_right (0 : E) (y - x) x).symm
  calc
    ρ.dist x (lineMap x y t) = ρ.dist (0 : E) (t • (y - x)) := by
      rw [lineMap_apply]
      simpa using (dist_add_right (0 : E) (t • (y - x)) x)
    _ = t * ρ.dist (0 : E) (y - x) := hρ.dist_zero_smul (y - x) ht
    _ = t * ρ.dist x y := by rw [hxy]

/-- Text 15.0.16: in a Minkowski metric, the distance from `x` to the affine-segment point
`(1 - t) • x + t • y` is `t` times the distance from `x` to `y` for every `t ∈ [0, 1]`. -/
theorem dist_affineCombination (x y : E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ρ.dist x (((1 - t) • x) + t • y) = t * ρ.dist x y := by
  simpa [lineMap_apply_module] using dist_left_lineMap x y ht

end IsMinkowskiMetric

end MetricSpace

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard norm metric on a real normed space is a Minkowski metric. -/
instance : (inferInstance : MetricSpace E).IsMinkowskiMetric := by
  refine { dist_zero_smul := ?_ }
  intro x t ht
  rw [dist_zero_left, dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]

end

/-! ### Text_15_0_17 (from Chap03) -/
/-!
Source/core/bridge triage:
- `source-facing`: Text 15.0.17 states a bijective correspondence between norms and Minkowski
  metrics. The source specialization to `R^n` is recovered by taking
  `E = EuclideanSpace ℝ (Fin n)`.
- `core/canonical`: on the norm side, the Chapter 15 owner abstraction is `IsGaugeNorm`; on the
  metric side, the owner is the source-facing class `MetricSpace.IsMinkowskiMetric` from
  `Text_15_0_16`.
- `bridge/view`: the two source formulas `ρ(x,y) = k(x - y)` and `k(x) = ρ(x,0)` are the bridge
  maps between these owner abstractions.

Domain-style sampling used here:
- the Chapter 15 owner `IsGaugeNorm` from `Text_15_0_12`;
- `IsGaugeNorm.subadditive`, `IsGaugeNorm.map_smul_eq_abs`, and
  `IsGaugeNorm.toReal_eq_zero_iff` as the canonical derived API for
  norm-gauges;
- `MetricSpace` as the ambient owner of the metric data;
- the Chapter 15 metric owner `MetricSpace.IsMinkowskiMetric`.

Primitive data vs derived API:
- primitive norm-side data: a `WithBotTop ℝ`-valued function on `E`
  together with the owner predicate
  `IsGaugeNorm`;
- primitive metric-side data: a metric structure together with `MetricSpace.IsMinkowskiMetric`;
- derived API: the concrete maps `k ↦ ρ_k`, `ρ ↦ k_ρ`, and the inverse laws.

Layer target: `bridge/view`, because this item compares two already existing owner abstractions via
canonical constructions in each direction.
-/

noncomputable section

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private def gaugeNormDist (k : E → WithBotTop ℝ) (hk : IsGaugeNorm k) (x y : E) : ℝ :=
  letI : IsGaugeNorm k := hk
  EReal.toReal (k (x - y))

/-- The metric structure induced by a norm-gauge on a real vector space. -/
@[reducible] def minkowskiMetricOfNorm
    (k : E → WithBotTop ℝ) (hk : IsGaugeNorm k) :
    MetricSpace E where
  dist := gaugeNormDist k hk
  dist_self x := by
    have hk0 : k 0 = 0 := hk.toIsGauge.map_zero
    change EReal.toReal (k (x - x)) = 0
    calc
      EReal.toReal (k (x - x)) = EReal.toReal (k 0) := by simp
      _ = 0 := by
        rw [hk0]
        exact EReal.toReal_zero
  dist_comm x y := by
    simpa [gaugeNormDist, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (congrArg EReal.toReal (hk.symmetric (x - y))).symm
  dist_triangle x y z := by
    have hsub : k (x - z) ≤ k (x - y) + k (y - z) := by
      simpa [sub_eq_add_neg, add_assoc] using
        (show k ((x - y) + (y - z)) ≤ k (x - y) + k (y - z) from
          IsGaugeNorm.subadditive (hk := hk) (x - y) (y - z))
    have hsub' :
        (((EReal.toReal (k (x - z)) : ℝ)) : EReal) ≤
          (((EReal.toReal (k (x - y)) : ℝ)) : EReal) +
            (((EReal.toReal (k (y - z)) : ℝ)) : EReal) := by
      rw [EReal.coe_toReal (IsGaugeNorm.ne_top (hk := hk) (x - z))
          (IsGaugeNorm.ne_bot (hk := hk) (x - z))]
      rw [EReal.coe_toReal (IsGaugeNorm.ne_top (hk := hk) (x - y))
          (IsGaugeNorm.ne_bot (hk := hk) (x - y))]
      rw [EReal.coe_toReal (IsGaugeNorm.ne_top (hk := hk) (y - z))
          (IsGaugeNorm.ne_bot (hk := hk) (y - z))]
      exact hsub
    have hsub'' :
        (((gaugeNormDist k hk x z : ℝ)) : EReal) ≤
          (((gaugeNormDist k hk x y + gaugeNormDist k hk y z : ℝ)) : EReal) := by
      simpa [gaugeNormDist] using hsub'
    exact EReal.coe_le_coe_iff.mp hsub''
  eq_of_dist_eq_zero := by
    intro x y hxy
    have hxy' : EReal.toReal (k (x - y)) = 0 := by
      simpa [gaugeNormDist] using hxy
    exact sub_eq_zero.mp ((IsGaugeNorm.toReal_eq_zero_iff (hk := hk)).1 hxy')

/-- The metric induced by a norm-gauge has distance `ρ(x,y) = k(x - y)`, with the norm-gauge
value read as a real number. -/
@[simp] theorem minkowskiMetricOfNorm_dist_eq (k : E → WithBotTop ℝ) (hk : IsGaugeNorm k)
    (x y : E) :
    (minkowskiMetricOfNorm k hk).dist x y = EReal.toReal (k (x - y)) :=
  rfl

-- Proof sketch: translation invariance follows from the difference formula
-- `ρ(x,y) = k(x - y)`. For the affine-segment axiom, rewrite the difference to the segment point as
-- `t • (x - y)` and use the absolute homogeneity of `k` together with `0 ≤ t ≤ 1`.
/-- The metric induced by a norm-gauge is a Minkowski metric. -/
theorem minkowskiMetricOfNorm_isMinkowski (k : E → WithBotTop ℝ) (hk : IsGaugeNorm k) :
    (minkowskiMetricOfNorm k hk).IsMinkowskiMetric := sorry

instance (k : E → WithBotTop ℝ) [hk : IsGaugeNorm k] :
    (minkowskiMetricOfNorm k hk).IsMinkowskiMetric :=
  minkowskiMetricOfNorm_isMinkowski k hk

end

section

variable {E : Type*} [Zero E]

namespace MetricSpace

/-- A Minkowski metric recovers its canonical norm by the formula `k(x) = ρ(x,0)`. -/
def normGauge (ρ : MetricSpace E) : E → WithBotTop ℝ :=
  fun x ↦ (ρ.dist x 0 : WithBotTop ℝ)

@[simp] theorem normGauge_apply (ρ : MetricSpace E) (x : E) :
    ρ.normGauge x = (ρ.dist x 0 : WithBotTop ℝ) :=
  rfl

end MetricSpace

end

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace MetricSpace

-- Proof sketch: the function `x ↦ ρ(x,0)` is nonnegative and finite because it is a metric
-- distance. Symmetry follows from metric symmetry, positive homogeneity from the affine-segment
-- axiom and translation invariance, subadditivity from the metric triangle inequality, and
-- strict positivity away from `0` from the metric separation axiom.
/-- A Minkowski metric recovers its canonical norm-gauge by the formula `k(x) = ρ(x,0)`. -/
theorem normGauge_isGaugeNorm (ρ : MetricSpace E)
    (hρ : ρ.IsMinkowskiMetric) :
    IsGaugeNorm ρ.normGauge := sorry

instance (ρ : MetricSpace E) [hρ : ρ.IsMinkowskiMetric] :
    IsGaugeNorm ρ.normGauge :=
  normGauge_isGaugeNorm ρ hρ

end MetricSpace

-- Proof sketch: compare both norm-gauges pointwise using the distance formula
-- `ρ_k(x,0) = k(x - 0) = k x`, then use subtype extensionality.
/-- Recovering the norm from the metric induced by that norm returns the original norm. -/
@[simp] theorem MetricSpace.normGauge_minkowskiMetricOfNorm (k : E → WithBotTop ℝ)
    (hk : IsGaugeNorm k) :
    (minkowskiMetricOfNorm k hk).normGauge = k := sorry

-- Proof sketch: a Minkowski metric is determined by its values `ρ(x,0)` together with translation
-- invariance, since `ρ(x,y) = ρ(x - y, 0)`. Apply this to the recovered norm to identify every
-- distance value and then use extensionality of metric structures.
/-- Rebuilding a Minkowski metric from its recovered norm returns the original metric. -/
@[simp] theorem minkowskiMetricOfNorm_normGauge (ρ : MetricSpace E)
    (hρ : ρ.IsMinkowskiMetric) :
    minkowskiMetricOfNorm ρ.normGauge (MetricSpace.normGauge_isGaugeNorm ρ hρ) = ρ := sorry

/-- Text 15.0.17: the assignments `k ↦ ρ` with `ρ(x,y) = k(x - y)` and `ρ ↦ k` with
`k(x) = ρ(x,0)` define a canonical one-to-one correspondence between norms and Minkowski metrics on
the ambient real vector space. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers `R^n`. -/
def minkowskiMetricNormEquiv :
    { k : E → WithBotTop ℝ // IsGaugeNorm k } ≃ { ρ : MetricSpace E // ρ.IsMinkowskiMetric } where
  toFun := fun k ↦ by
    exact ⟨minkowskiMetricOfNorm k.1 k.2, minkowskiMetricOfNorm_isMinkowski k.1 k.2⟩
  invFun := fun ρ ↦ by
    exact ⟨ρ.1.normGauge, MetricSpace.normGauge_isGaugeNorm ρ.1 ρ.2⟩
  left_inv := fun k ↦ by
    apply Subtype.ext
    exact MetricSpace.normGauge_minkowskiMetricOfNorm k.1 k.2
  right_inv := fun ρ ↦ by
    apply Subtype.ext
    exact minkowskiMetricOfNorm_normGauge ρ.1 ρ.2

end

end

/-! ### Text_15_0_18 (from Chap03) -/
open scoped Pointwise

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage:
- `source-facing`: Text 15.0.18 says that a symmetric closed bounded convex set `C` with
  `0 ∈ interior C` determines a unique Minkowski metric whose radius-`ε` balls are the translates
  `x + ε C`; specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` display.
- `core/canonical`: the owner abstractions are the upstream Chapter 15 convex-body owner
  `ConvexBody E`, the canonical set-symmetry predicate `Balanced ℝ (K : Set E)` from mathlib,
  the interior predicate `interior`, and the ambient metric owner `MetricSpace E`, refined by
  `MetricSpace.IsMinkowskiMetric`, from `Text_15_0_17`.
- `bridge/view`: the ball formula is stated with the canonical metric owner `closedBall` and the
  canonical pointwise-set expression `({x} : Set E) + ε • C`, after fixing the ambient owner
  `ρ : MetricSpace E`.

Domain-style sampling used here:
- the Chapter 15 owner abstraction `MetricSpace.IsMinkowskiMetric`;
- `Balanced ℝ` on convex sets as the canonical symmetry predicate;
- `Metric.closedBall` and pointwise set operations on subsets of `E`;
- the ambient mathlib owners `MetricSpace`, `IsClosed`, `Convex`, `Bornology.IsBounded`, and
  `interior`.

Primitive data vs derived API:
- primitive input: a convex body `K : ConvexBody E` together with
  `Balanced ℝ (K : Set E)` and `(0 : E) ∈ interior (K : Set E)`;
- derived output: the unique ambient metric owner `ρ : MetricSpace E` whose closed balls are
  exactly the translates and dilates of `(K : Set E)`.

Layer target: `bridge/view`, because the source identifies the geometric body from Theorem 15.2
with the metric owner abstraction from Text 15.0.17.
-/

-- Proof sketch: Theorem 15.2 gives the unique norm whose unit ball is `C`. Transport that norm
-- across the equivalence `minkowskiMetricNormEquiv` from Text 15.0.17 to obtain a Minkowski
-- metric. The distance formula `ρ(x, y) = k (x - y)` identifies the canonical closed ball
-- `Metric.closedBall x ε` with the `ε`-sublevel set of `k` translated by `x`, and the unit-ball
-- description of `C` rewrites that set as `({x} : Set E) + ε • C`. Uniqueness follows from the
-- inverse laws of the norm-metric correspondence.
/-- Text 15.0.18: if `C` is a symmetric closed bounded convex set in a finite-dimensional real
normed space and `0 ∈ interior C`, then there exists a unique Minkowski metric whose radius-`ε`
closed ball about `x` is the translate-dilate `({x} : Set E) + ε • C` for every `ε > 0`.
Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement. -/
theorem existsUnique_minkowskiMetric_of_balanced_zero_mem_interior
    (K : ConvexBody E)
    (hK_bal : Balanced ℝ (K : Set E))
    (hK_int : (0 : E) ∈ interior (K : Set E)) :
    ∃! ρ : MetricSpace E,
      ρ.IsMinkowskiMetric ∧
        (letI := ρ
         ∀ x : E, ∀ ε > 0,
           Metric.closedBall x ε = ({x} : Set E) + ε • (K : Set E)) :=
      sorry

end

/-! ### Text_15_0_19 (from Chap03) -/
open scoped Pointwise Rockafellar

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.19 compares the Minkowski metric attached in Text 15.0.18 to the
  ambient norm metric. The textbook specialization is recovered by taking
  `E = EuclideanSpace ℝ (Fin n)`.
- `core/canonical`: the owner abstractions are the ambient norm metric on `E`, the Chapter 2
  unit-ball owner `B = Metric.closedBall (0 : E) 1`, the set-level predicates
  `Bornology.IsBounded K` and `(0 : E) ∈ interior K`, and the metric owner pair
  `ρ : MetricSpace E` together with `MetricSpace.IsMinkowskiMetric`.
- `bridge/view`: the quantitative comparison is expressed by explicit constants `α, β > 0`,
  inclusions `α • B ⊆ K ⊆ β • B`, and the resulting two-sided distance comparison.

Domain-style sampling used here:
- the boundedness owner theorem `Bornology.IsBounded.subset_closedBall`;
- `Metric.mem_interior_iff_exists_pos_closedBall_subset`;
- `Metric.closedBall` for the ambient unit ball and for the closed balls of the Minkowski metric;
- `LipschitzWith` and `AntilipschitzWith` as the canonical route from two-sided metric comparison
  to equality of topologies and Cauchy sequences.

Primitive data vs derived API:
- primitive inputs: a set `K : Set E`, the boundedness hypothesis `IsBounded K` needed for the
  outer ambient closed ball, the interior-origin hypothesis `(0 : E) ∈ interior K` needed for the
  inner ambient closed ball, and the specific closed-ball bridge data from Text 15.0.18 for a
  metric owner `ρ : MetricSpace E`;
- derived API: the ambient comparison constants `α, β`, the two-sided norm/metric inequality, the
  neighborhood-basis comparison with ambient closed balls, and the corresponding
  `CauchySeq` equivalence.

Layer target: `bridge/view`, because this item relates the metric coming from Text 15.0.18 to
the ambient norm metric while isolating the set-level bridge data actually used by the comparison
arguments.
-/

-- Proof sketch: boundedness of the set `K` gives an ambient closed ball about `0`
-- containing `K`, hence a positive dilation `β • B` of the unit ball `B`.
/-- Text 15.0.19 (1): every bounded set in a real normed space is contained in a positive
ambient dilation `β • B` of the unit ball `B`. Applied to the body from Text 15.0.18, this
supplies the outer comparison constant. -/
theorem exists_pos_subset_smul_unitClosedBall_of_isBounded
    {K : Set E} (hK_bounded : Bornology.IsBounded K) :
    ∃ β : ℝ, 0 < β ∧ K ⊆ β • B := sorry

-- Proof sketch: the hypothesis `0 ∈ interior K` provides an ambient closed ball about `0`
-- contained in `K`, hence some positive dilation `α • B` lies inside `K`.
/-- Text 15.0.19 (2): if `0 ∈ interior K`, then `K` contains a positive ambient dilation
`α • B` of the unit ball `B`. -/
theorem exists_pos_smul_unitClosedBall_subset_of_zero_mem_interior
    {K : Set E} (hK_int : (0 : E) ∈ interior K) :
    ∃ α : ℝ, 0 < α ∧ α • B ⊆ K := sorry

section MinkowskiComparison

variable {K : Set E} {ρ : MetricSpace E} [ρ.IsMinkowskiMetric]

variable (hball : letI := ρ.toPseudoMetricSpace
  ∀ x : E, ∀ ε : ℝ, 0 < ε →
    Metric.closedBall x ε = ({x} : Set E) + ε • K)

-- Proof sketch: if `C ⊆ β • B`, then the closed-ball formula from Text 15.0.18 yields
-- `closedBallₚ x ε ⊆ closedBall x (β ε)`. Evaluating this inclusion on `y` gives the lower
-- comparison `β⁻¹ dist x y ≤ ρ(x,y)`.
/-- Text 15.0.19 (3): any positive constant `β` with `K ⊆ β • B` yields the lower comparison
`β⁻¹ dist x y ≤ ρ(x,y)` between the ambient norm metric and the Minkowski metric. -/
theorem inv_mul_dist_le_minkowskiDist_of_subset_smul_unitClosedBall
    {β : ℝ} (hβ : 0 < β) (hβK : K ⊆ β • B) (x y : E) :
    β⁻¹ * dist x y ≤ ρ.dist x y := sorry

-- Proof sketch: if `α • B ⊆ C`, then the closed-ball formula gives
-- `closedBall x (α ε) ⊆ closedBallₚ x ε`. Testing membership of `y` in these balls yields the
-- upper comparison `ρ(x,y) ≤ α⁻¹ dist x y`.
/-- Text 15.0.19 (4): any positive constant `α` with `α • B ⊆ K` yields the upper comparison
`ρ(x,y) ≤ α⁻¹ dist x y` between the Minkowski metric and the ambient norm metric. -/
theorem minkowskiDist_le_inv_mul_dist_of_smul_unitClosedBall_subset
    {α : ℝ} (hα : 0 < α) (hαK : α • B ⊆ K) (x y : E) :
    ρ.dist x y ≤ α⁻¹ * dist x y := sorry

-- Proof sketch: the positive comparison constants `α, β` and clauses (3) and (4) give the
-- required two-sided distance comparison. The identity map on `E`, viewed from the
-- ambient norm metric to `ρ` and back, is Lipschitz in both directions, so the two metric
-- neighborhood filters coincide.
/-- Text 15.0.19 (5): if `α • B ⊆ K ⊆ β • B` for some positive `α, β` and the positive
`ρ`-closed balls are the sets `x + ε K`, then `ρ` and the ambient norm metric induce the same
neighborhood filter at every point `x`; equivalently, they define the same topology. For the
convex-body metric of Text 15.0.18, clauses (1) and (2) provide such `α` and `β`. -/
theorem minkowskiMetric_nhds_eq_norm_of_closedBall_eq_translate_smul
    {α β : ℝ}
    (hα : 0 < α) (hαK : α • B ⊆ K)
    (hβ : 0 < β) (hβK : K ⊆ β • B) (x : E) :
    (letI := ρ.toPseudoMetricSpace; nhds x) = nhds x := sorry

-- Proof sketch: the previous theorem makes the identity map bilipschitz between the ambient norm
-- metric and `ρ`, so it is a uniform embedding in both directions. Bilipschitz equivalent metrics
-- therefore have the same `CauchySeq` predicate.
/-- Text 15.0.19 (6): if `α • B ⊆ K ⊆ β • B` for some positive `α, β` and the positive
`ρ`-closed balls are the sets `x + ε K`, then a sequence in `E` is Cauchy for `ρ` exactly when it
is Cauchy for the ambient norm metric, formalized with the canonical owner predicate `CauchySeq`.
For the convex-body metric of Text 15.0.18, clauses (1) and (2) provide the needed comparison
constants. -/
theorem minkowskiMetric_cauchySeq_iff_norm_of_closedBall_eq_translate_smul
    {α β : ℝ}
    (hα : 0 < α) (hαK : α • B ⊆ K)
    (hβ : 0 < β) (hβK : K ⊆ β • B)
    (u : ℕ → E) :
    (letI := ρ.toPseudoMetricSpace.toUniformSpace; CauchySeq u) ↔
      CauchySeq u := sorry

end MinkowskiComparison

end

/-! ### Text_15_0_20 (from Chap03) -/
open scoped Pointwise Rockafellar

universe u v w

section

variable {𝕜 : Type v} {E : Type u} {α : Type w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.20 introduces a new property of a convex function
  `f : E → WithTopBot α` (specializing to `ℝ^n → (-∞, +∞]`): being gauge-like means that `f`
  never takes the value `⊥`, that `0` is a
  minimizer of `f`, and that every finite strict-upper sublevel set `f ⁻¹' Set.Iic β` is a
  positive scalar multiple of one fixed set.
- `core/canonical`: the existing owner abstractions are the chapter convexity predicate
  `Function.IsConvex 𝕜`, the function-side minimum owner
  `IsMinOn f Set.univ 0`, and the chapter's canonical sublevel-set style
  `f ⁻¹' Set.Iic α`.
- `bridge/view`: the later representation theorem pairs this source-facing predicate with
  `Function.IsClosedProperConvex`; closedness and properness belong there, while convexity already
  belongs to the present owner because the text defines gauge-like functions among convex
  functions.

Domain-style sampling used here:
- the project declaration `Function.IsConvex` from `Theorem_4_2`;
- the function owner `IsMinOn` together with its range-minimum bridge `IsLeast`;
- the chapter's canonical sublevel-set pattern `f ⁻¹' Set.Iic β`;
- mathlib's pointwise scalar action on sets `t • C`.

Primitive data vs derived API:
- primitive owner data: the function `f : E → WithTopBot α`;
- primitive conditions from the source: the codomain restriction `f(x) ∈ (-∞, +∞]`, convexity,
  the minimum condition that `0` realizes the least value of `f`, and proportionality of all
  finite strict-upper sublevel sets;
- the range-level least-element statement is derived API from the function-side minimum owner, so
  it should not remain a primitive field.

Layer target: `source-facing`.
-/

namespace Function

/-- Text 15.0.20: a convex function `f : E → WithTopBot α` (in particular
`f : ℝ^n → (-∞, +∞]`) is gauge-like if it never takes the value `⊥`, if `0` attains the infimum
of its values, and if every strict-upper sublevel set at a finite codomain level
`β : WithTopBot α` (i.e. `β < ⊤`) is a positive scalar multiple of one fixed set.
Closedness and properness are later hypotheses, not part of this source-facing predicate. -/
class IsGaugeLike
    (𝕜 : Type v) [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]
    (f : E → WithTopBot α) : Prop where
  bot_lt : ∀ x : E, ⊥ < f x
  convex : f.IsConvex 𝕜
  zero_isMinOn : IsMinOn f Set.univ 0
  proportional_finite_sublevel_sets :
    ∃ C : Set E,
      ∀ {β : WithTopBot α}, f 0 < β → β < ⊤ →
        ∃ t : 𝕜, 0 < t ∧ f ⁻¹' Set.Iic β = t • C

scoped[Rockafellar] notation "IsGaugeLike[" 𝕜 "]" => Function.IsGaugeLike (𝕜 := 𝕜)

namespace IsGaugeLike

/-- In a gauge-like function, `0` attains the least value of the range. -/
theorem zero_isLeast_range
    [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]
    {f : E → WithTopBot α} (hf : IsGaugeLike[𝕜] f) :
    IsLeast (Set.range f) (f 0) := by
  have hmin : ∀ x : E, f 0 ≤ f x := by
    simpa [isMinOn_univ_iff] using hf.zero_isMinOn
  refine ⟨⟨0, rfl⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hmin x

end IsGaugeLike

/-- The zero function is a canonical gauge-like function. -/
instance
    [Semiring 𝕜] [PartialOrder 𝕜] [ZeroLEOneClass 𝕜] [NeZero (1 : 𝕜)]
    [AddCommMonoid E] [MulAction 𝕜 E]
    [AddCommMonoid α] [PartialOrder α]
    [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] :
    IsGaugeLike[𝕜] (fun _ : E ↦ (0 : WithTopBot α)) where
  bot_lt _ := by
    change (((⊥ : WithBot α) : WithTop (WithBot α)) <
      (((0 : α) : WithBot α) : WithTop (WithBot α)))
    exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe 0)
  convex := Function.isConvex_zero (𝕜 := 𝕜) (E := E) (β := α)
  zero_isMinOn := by
    simp [isMinOn_univ_iff]
  proportional_finite_sublevel_sets := by
    refine ⟨Set.univ, ?_⟩
    intro β hβ0 _
    refine ⟨1, zero_lt_one, ?_⟩
    ext x
    simp [hβ0.le]

end Function

end

/-! ### Text_15_0_21 (from Chap03) -/
universe u v

section

open scoped Function

variable {E : Type u} {F : Type v} [SMul ℝ E] [SMul ℝ F]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.21 introduces the degree-`p` positive-homogeneity predicate
  `f.PositivelyHomogeneousOfDegree p`.
- `core/canonical`: the existing chapter owner for the degree-`1` case is
  `f.PositivelyHomogeneous ℝ`, so the degree-`p` owner should live in the same `Function`
  namespace rather than as a parallel global predicate.
- `bridge/view`: the degree-`1` specialization theorem `one_iff` identifies the new source-facing
  predicate with the Chapter 1 owner.

Domain-style sampling used here:
- the chapter owner `Function.PositivelyHomogeneous` from `Definition_4_8`;
- its companion theorem `Function.PositivelyHomogeneous.map_smul`;
- the neighboring chapter owners `Function.IsConvex` and `Function.IsProper`, which use the same
  short unbundled `Prop`-owner pattern for function properties;
- mathlib's scalar-power API `Real.rpow` and `Real.rpow_one` for the degree factor.

Mathlib does not expose this exact real degree-`p` positive-homogeneity owner interface, so this
file remains the canonical chapter owner for the source-facing degree-`p` notion rather than a
wrapper around an upstream declaration.

Primitive data vs derived API:
- primitive inputs: the exponent `p`, the function `f`, and the intrinsic positive-scalar law on
  `ℝ⁺`;
- derived API: the textbook binder bridge `iff_forall_pos_scalar`, the intrinsic theorem
  `iff_forall_pos`, the pointwise scaling theorems `map_smul_pos` / `map_smul`, and the degree-`1`
  bridge `one_iff`.

Layer target: `source-facing`, with the degree-`1` identification as the minimal bridge back to
the earlier chapter owner. Concrete coordinate and extended-codomain specializations are
downstream views rather than part of this owner file.
-/

namespace Function

/-- Text 15.0.21: a function is positively homogeneous of degree `p` when scaling its argument by
an intrinsic positive real scalar scales its value by the `p`th power of that scalar. Any extra
side conditions on `p` belong in downstream theorems rather than in this owner predicate, since
they do not affect the defining scaling law. -/
def PositivelyHomogeneousOfDegree (p : ℝ) (f : E → F) : Prop :=
  ∀ a : ℝ⁺, ∀ x : E, f (a • x) = (a : ℝ).rpow p • f x

variable {p : ℝ} {f : E → F}

namespace PositivelyHomogeneousOfDegree

/-- The degree-`p` owner can be read intrinsically over positive real scalars. -/
theorem iff_forall_pos :
    f.PositivelyHomogeneousOfDegree p ↔
      ∀ a : ℝ⁺, ∀ x : E, f (a • x) = (a : ℝ).rpow p • f x :=
  Iff.rfl

/-- The intrinsic positive-scalar owner is equivalent to the textbook binder form over `ℝ`. -/
theorem iff_forall_pos_scalar :
    f.PositivelyHomogeneousOfDegree p ↔
      ∀ ⦃a : ℝ⦄, 0 < a → ∀ x : E, f (a • x) = a.rpow p • f x := by
  constructor
  · intro hf a ha x
    exact hf ⟨a, ha⟩ x
  · intro hf a x
    exact hf (a := a.1) a.2 x

/-- A positively homogeneous function of degree `p` carries intrinsic positive scalar multiples to
the corresponding `p`th-power scalar multiples of its value. -/
theorem map_smul_pos (hf : f.PositivelyHomogeneousOfDegree p)
    (a : ℝ⁺) (x : E) :
    f (a • x) = (a : ℝ).rpow p • f x :=
  hf a x

/-- A positively homogeneous function of degree `p` carries each positive scalar multiple of an
argument to the corresponding `p`th-power scalar multiple of its value. -/
theorem map_smul (hf : f.PositivelyHomogeneousOfDegree p)
    {c : ℝ} (hc : 0 < c) (x : E) :
    f (c • x) = c.rpow p • f x :=
  hf ⟨c, hc⟩ x

/-- Coercing a real-valued degree-`p` positively homogeneous function to `WithTopBot ℝ` preserves
the same degree-`p` homogeneity law. -/
theorem toWithTopBot {f : E → ℝ} (hf : f.PositivelyHomogeneousOfDegree p) :
    f.toWithTopBot.PositivelyHomogeneousOfDegree p := by
  intro a x
  change ((f (a • x) : ℝ) : WithTopBot ℝ) =
      (((a : ℝ).rpow p • f x : ℝ) : WithTopBot ℝ)
  exact congrArg (fun t : ℝ ↦ (t : WithTopBot ℝ)) (hf a x)

/-- Degree-`1` positive homogeneity is exactly the Chapter 1 owner predicate
`Function.PositivelyHomogeneous`. -/
@[simp] theorem one_iff :
    f.PositivelyHomogeneousOfDegree 1 ↔ f.PositivelyHomogeneous ℝ := by
  rw [Function.PositivelyHomogeneous.iff_forall_pos, iff_forall_pos]
  constructor
  · intro hf a x
    simpa [Real.rpow_one] using hf a x
  · intro hf a x
    simpa [Real.rpow_one] using hf a x

end PositivelyHomogeneousOfDegree

end Function

end

/-! ### Text_15_0_22 (from Chap03) -/
noncomputable section

open scoped BigOperators

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.22 studies the concrete function
  `x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p` on a finite coordinate family `ι → X`.
- `core/canonical`: the owner abstractions are the chapter predicate
  `Function.IsClosedProperConvex` and the degree-`p` homogeneity owner
  `Function.PositivelyHomogeneousOfDegree`.
- `bridge/view`: the primitive homogeneity owner is stated on the raw real-valued source
  function, while the closed-proper-convex clause and the downstream-facing homogeneity bridge are
  stated on the canonical codomain lift `(lpCoordinatePower X ι p).toWithTopBot`.
  This keeps convexity on the chapter `WithTopBot ℝ` surface while avoiding a lift-only statement
  for a property that is intrinsically scalar-scaling.

Domain-style sampling used here:
- `lpCoordinatePower` is the primitive source-facing datum in this file;
- `Function.PositivelyHomogeneousOfDegree` from Text 15.0.21 for the scaling owner;
- `strictConvexOn_rpow` and `convexOn_rpow` for the scalar building block `t ↦ t ^ p`;
- `ConvexOn.map_sum_le` for finite sums of convex terms;
- `Function.toWithTopBot` from Definition 4.4 as the canonical real-to-`WithTopBot ℝ`
  codomain lift.

Primitive data vs derived API:
- primitive source data: the concrete coordinate formula defining the function, kept as a raw
totalized real-power expression so later bridge items can reuse it definitionally;
- derived API: the closed-proper-convex statement on the canonical `WithTopBot ℝ` codomain lift,
  the primitive real-valued degree-`p` positive-homogeneity statement, and the thin codomain-lift
  homogeneity bridge used downstream; convexity is restricted to the textbook regime `1 ≤ p`,
  while the homogeneity law remains valid for every real exponent `p`.

Layer target: `source-facing`, expressed using the canonical chapter owners for convexity and
positive homogeneity: primitive on `lpCoordinatePower X ι p`, and bridged to
`(lpCoordinatePower X ι p).toWithTopBot` where Chapter 15 downstream owners require the extended
codomain. The owner parameter `X` is explicit so partially-applied surfaces avoid named-argument
noise; the scalar is intrinsically `ℝ` here because both the chapter owner
`Function.PositivelyHomogeneousOfDegree` and the exponentiation bridge `Real.rpow` are real-scalar.
-/

/-- The totalized coordinate power-sum formula `x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p` on a finite
coordinate family `ι → X`. The raw definition is kept for all real exponents so downstream bridge
results can reuse the formula definitionally; the source-labeled theorems below restrict to the
intended textbook regime `1 ≤ p`. -/
def lpCoordinatePower (X : Type*) [Norm X] (ι : Type*) [Fintype ι] (p : ℝ) (x : ι → X) : ℝ :=
  (1 / p) * ∑ i : ι, ‖x i‖ ^ p

-- Proof sketch: unfold `lpCoordinatePower`; this is exactly its defining coordinate
-- formula.
/-- Evaluating `lpCoordinatePower X ι p` at `x` gives `(1 / p)` times the sum of the `p`th
powers of the coordinate norms of `x`. -/
@[simp]
theorem lpCoordinatePower_apply (X : Type*) [Norm X] (ι : Type*) [Fintype ι]
    (p : ℝ) (x : ι → X) :
    lpCoordinatePower X ι p x = (1 / p) * ∑ i : ι, ‖x i‖ ^ p := rfl

-- Proof sketch: each coordinate summand `xᵢ ↦ (1 / p) * ‖xᵢ‖ ^ p`, with `1 ≤ p`, is a finite
-- closed convex real-valued profile; summing over the finitely many coordinates preserves
-- convexity and
-- lower semicontinuity, and finiteness everywhere gives properness. Coerce the resulting real
-- function to `WithTopBot ℝ` via `Function.toWithTopBot` to match
-- `Function.IsClosedProperConvex`.
/-- Text 15.0.22 (1): for `1 ≤ p`, the function
`x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p`, viewed as `WithTopBot ℝ`-valued by coercion, is closed proper
convex. -/
theorem lpCoordinatePower_isClosedProperConvex
    (X : Type*) [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    (ι : Type*) [Fintype ι]
    (p : ℝ) (hp : 1 ≤ p) :
    ((lpCoordinatePower X ι p).toWithTopBot).IsClosedProperConvex (𝕜 := ℝ) := sorry

-- Proof sketch: for every positive scalar `c`, rewrite each coordinate norm of `c • x` with
-- `‖c • x i‖ = c * ‖x i‖`. Then `‖c • x i‖ ^ p = c ^ p * ‖x i‖ ^ p` for `0 < c`, so `c ^ p`
-- factors out of the finite sum and then out of the prefactor `(1 / p)`.
/-- Text 15.0.22 (2): the coordinate `ℓ_p` power-sum function is positively homogeneous of degree
`p` on its primitive real-valued owner. -/
theorem lpCoordinatePower_positivelyHomogeneousOfDegree
    (X : Type*) [Norm X] [SMul ℝ X] [NormSMulClass ℝ X]
    (ι : Type*) [Fintype ι]
    (p : ℝ) :
    (lpCoordinatePower X ι p).PositivelyHomogeneousOfDegree p := sorry

-- Proof sketch: coerce the primitive real-valued scaling law to `WithTopBot ℝ`, so the
-- homogeneity statement can be used directly with Chapter 15 owners sharing that codomain.
/-- Text 15.0.22 (2), codomain-lift bridge: the same degree-`p` homogeneity law on the canonical
`WithTopBot ℝ` codomain surface. -/
theorem lpCoordinatePower_positivelyHomogeneousOfDegree_toWithTopBot
    (X : Type*) [Norm X] [SMul ℝ X] [NormSMulClass ℝ X]
    (ι : Type*) [Fintype ι]
    (p : ℝ) :
    (lpCoordinatePower X ι p).toWithTopBot.PositivelyHomogeneousOfDegree p := by
  simpa using
    (lpCoordinatePower_positivelyHomogeneousOfDegree X ι p).toWithTopBot

end

/-! ### Text_15_0_23 (from Chap03) -/
section

open scoped BigOperators Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.23 computes the conjugate of the concrete function
  `x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p` on a finite coordinate family `ι → X`; the textbook scalar
  coordinate model is recovered by `X = ℝ` and `ι = Fin n`.
- `core/canonical`: the owner abstraction is the project's Fenchel conjugate `convexConjugate` on
  `WithBotTop ℝ`-valued functions on finite coordinate families.
- `bridge/view`: the source-facing function owner is `lpCoordinatePower` from
  Text 15.0.22, while the conjugate-exponent relation is expressed by the canonical predicate
  `p.HolderConjugate q`; the codomain lift is the canonical bridge `Function.toWithBotTop`.

Domain-style sampling used here:
- the owner `convexConjugate` from Defn 12.2;
- direct unfolding of the owner `convexConjugate`;
- the source-facing function `lpCoordinatePower` from Text 15.0.22;
- the canonical real inner-product pairing owner from Chapter 1;
- mathlib's `Real.HolderConjugate` as the canonical exponent relation.

Primitive data vs derived API:
- primitive inputs: the exponents `p q : ℝ` with `p.HolderConjugate q`;
- primitive ambient data: a real inner-product coordinate value type `X` and a finite index type
  `ι`, since the source formula is coordinatewise and uses no order or arithmetic on indices;
- derived API: the conjugate identity between the canonical source-facing owners
  `lpCoordinatePower X ι p` and `lpCoordinatePower X ι q`, viewed
  as `WithBotTop ℝ`-valued by the canonical codomain lift.

Layer target: `source-facing`; the item is stated directly through the canonical conjugate owner
applied to the source-facing `ℓ_p` power-sum function, on the intrinsic inner-product coordinate
layer instead of only scalar coordinates. The scalar remains `ℝ` because the exponent owner is
`Real.rpow` and the dual-exponent owner is `Real.HolderConjugate`.
-/

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]

-- Proof sketch: unfold `convexConjugate`; by symmetry of the real inner product on `ι → X`,
-- separate the Fenchel supremum into independent coordinates. Apply the degree-`p`/degree-`q`
-- conjugacy formula for `x ↦ (1 / p) * ‖x‖ ^ p` on each coordinate space `X`, then reassemble the
-- resulting sum as `lpCoordinatePower X ι q`.
/-- Text 15.0.23: if `p` and `q` are Hölder-conjugate exponents, then the Fenchel conjugate of
`x ↦ (1 / p) * ∑ i, ‖x i‖ ^ p`, viewed as `WithBotTop ℝ`-valued by coercion, is the canonical
codomain lift of `xStar ↦ (1 / q) * ∑ i, ‖xStar i‖ ^ q`. -/
theorem lpCoordinatePower_convexConjugate_eq
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ((lpCoordinatePower X ι p).toWithBotTop)⋆ =
      (lpCoordinatePower X ι q).toWithBotTop := sorry

end
