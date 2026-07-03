import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Recall
import Mathlib.Topology.Order.LeftRightLim

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_5_24_1 (from Chap05) -/
noncomputable section

open MeasureTheory

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 5.24.1 says that for a finite convex function on a real interval, the
  increment `f y - f x` is given by the interval integral of either one-sided derivative.
- `core/canonical`: in mathlib, the natural owner layer for this one-dimensional finite setting is
  `ConvexOn ℝ I f` together with the one-sided derivatives
  `derivWithin f (Set.Ioi t) t` and `derivWithin f (Set.Iio t) t`.
- `bridge/view`: the endpoint interior hypotheses are a derived way to guarantee the primitive
  segment-level condition `uIcc x y ⊆ interior I`; the canonical source theorem below is stated at
  this primitive layer, with endpoint-interior versions as wrappers.

Domain-style sampling used here:
- `ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior` and
  `ConvexOn.hasDerivWithinAt_leftDeriv_of_mem_interior`;
- `ConvexOn.monotoneOn_rightDeriv` and `ConvexOn.monotoneOn_leftDeriv`;
- `intervalIntegral.integral_eq_sub_of_hasDeriv_right`;
- `MonotoneOn.intervalIntegrable`.
-/

namespace ConvexOn

-- Textbook one-sided derivative notation for the finite-valued scalar-line layer used here.
local notation:max f "′+" => fun t => derivWithin f (Set.Ioi t) t
local notation:max f "′-" => fun t => derivWithin f (Set.Iio t) t

-- Proof sketch: under the primitive segment hypothesis `uIcc x y ⊆ interior I`, continuity on
-- `uIcc x y`, one-sided differentiability on `Ioo (min x y) (max x y)`, and interval integrability
-- of the right derivative are all available from the convex one-dimensional API, so FTC-2 applies.
/-- Corollary 5.24.1 at the primitive segment layer (right-derivative form): for a finite convex
function, if the full segment between `x` and `y` lies in `interior I`, then the increment
`f y - f x` is the interval integral of the right one-sided derivative of `f`. -/
theorem sub_eq_intervalIntegral_rightDeriv_of_uIcc_subset_interior
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hxyI : Set.uIcc x y ⊆ interior I) :
    f y - f x = ∫ t in x..y, f′+ t := by
  symm
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right ?_ ?_ ?_
  · exact (hf.continuousOn_interior).mono hxyI
  · intro t ht
    exact hf.hasDerivWithinAt_rightDeriv_of_mem_interior (hxyI (Set.uIoo_subset_uIcc_self ht))
  · exact (hf.monotoneOn_rightDeriv.mono hxyI).intervalIntegrable

-- Proof sketch: same primitive segment hypothesis as above; now use the left one-sided derivative
-- and the left-derivative convex API.
/-- Corollary 5.24.1 at the primitive segment layer (left-derivative form): for a finite convex
function, if the full segment between `x` and `y` lies in `interior I`, then the increment
`f y - f x` is the interval integral of the left one-sided derivative of `f`. -/
theorem sub_eq_intervalIntegral_leftDeriv_of_uIcc_subset_interior
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hxyI : Set.uIcc x y ⊆ interior I) :
    f y - f x = ∫ t in x..y, f′- t := by
  let g : ℝ → ℝ := f′-
  let h : ℝ → ℝ := fun u => -f (-u)
  have hg_int_xy : IntervalIntegrable g volume x y :=
    (hf.monotoneOn_leftDeriv.mono hxyI).intervalIntegrable
  have hg_int_yx : IntervalIntegrable g volume y x := hg_int_xy.symm
  have hgneg_int : IntervalIntegrable (fun u => g (-u)) volume (-y) (-x) :=
    (IntervalIntegrable.iff_comp_neg (f := g) (a := y) (b := x)).1 hg_int_yx
  have hneg_uIcc : ∀ {u : ℝ}, u ∈ Set.uIcc (-y) (-x) → -u ∈ Set.uIcc x y := by
    intro u hu
    rcases hu with ⟨humin, humax⟩
    have humin' : -max x y ≤ u := by simpa [min_neg_neg, max_comm] using humin
    have humax' : u ≤ -min x y := by simpa [max_neg_neg, min_comm] using humax
    refine ⟨?_, ?_⟩ <;> linarith
  have hcont_h : ContinuousOn h (Set.uIcc (-y) (-x)) := by
    refine (hf.continuousOn_interior.comp continuous_neg.continuousOn ?_).neg
    intro u hu
    exact hxyI (hneg_uIcc hu)
  have hderiv_h :
      ∀ u ∈ Set.Ioo (min (-y) (-x)) (max (-y) (-x)),
        HasDerivWithinAt h (g (-u)) (Set.Ioi u) u := by
    intro u hu
    have hu_mem_uIoo : u ∈ Set.uIoo (-y) (-x) := by simpa [Set.uIoo] using hu
    have hu_neg_mem_uIoo : -u ∈ Set.uIoo x y := by
      rcases hu_mem_uIoo with ⟨humin, humax⟩
      have humin' : -max x y < u := by simpa [min_neg_neg, max_comm] using humin
      have humax' : u < -min x y := by simpa [max_neg_neg, min_comm] using humax
      exact ⟨by linarith, by linarith⟩
    have hu_neg_int : -u ∈ interior I := hxyI (Set.uIoo_subset_uIcc_self hu_neg_mem_uIoo)
    have hleft : HasDerivWithinAt f (g (-u)) (Set.Iio (-u)) (-u) := by
      simpa [g] using hf.hasDerivWithinAt_leftDeriv_of_mem_interior hu_neg_int
    have hneg : HasDerivWithinAt (fun v : ℝ => -v) (-1) (Set.Ioi u) u :=
      (hasDerivAt_neg u).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun v : ℝ => -v) (Set.Ioi u) (Set.Iio (-u)) := by
      intro v hv
      have hv' : u < v := hv
      exact neg_lt_neg hv'
    have hcomp : HasDerivWithinAt (fun v : ℝ => f (-v)) ((g (-u)) * (-1)) (Set.Ioi u) u :=
      hleft.comp u hneg hmaps
    simpa [h, g, mul_comm, mul_left_comm, mul_assoc] using hcomp.neg
  have hFTC_h : h (-x) - h (-y) = ∫ u in -y..-x, g (-u) := by
    symm
    simpa [h] using
      (intervalIntegral.integral_eq_sub_of_hasDeriv_right (a := -y) (b := -x)
        hcont_h hderiv_h hgneg_int)
  have hFTC : f y - f x = ∫ u in -y..-x, g (-u) := by
    simpa [h, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hFTC_h
  calc
    f y - f x = ∫ u in -y..-x, g (-u) := hFTC
    _ = ∫ t in x..y, g t := by
      rw [intervalIntegral.integral_comp_neg (f := g) (a := -y) (b := -x)]
      simp
    _ = ∫ t in x..y, f′- t := by rfl

/-- Corollary 5.24.1, endpoint-interior wrapper (right-derivative form): if `x,y ∈ interior I`,
then the increment `f y - f x` is the interval integral of the right one-sided derivative of `f`. -/
theorem sub_eq_intervalIntegral_rightDeriv
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hx : x ∈ interior I) (hy : y ∈ interior I) :
    f y - f x = ∫ t in x..y, f′+ t := by
  refine hf.sub_eq_intervalIntegral_rightDeriv_of_uIcc_subset_interior ?_
  exact (hf.1.interior.ordConnected).uIcc_subset hx hy

/-- Corollary 5.24.1, endpoint-interior wrapper (left-derivative form): if `x,y ∈ interior I`,
then the increment `f y - f x` is the interval integral of the left one-sided derivative of `f`. -/
theorem sub_eq_intervalIntegral_leftDeriv
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hx : x ∈ interior I) (hy : y ∈ interior I) :
    f y - f x = ∫ t in x..y, f′- t := by
  refine hf.sub_eq_intervalIntegral_leftDeriv_of_uIcc_subset_interior ?_
  exact (hf.1.interior.ordConnected).uIcc_subset hx hy

end ConvexOn

/-! ### Definition_5_24_1 (from Chap05) -/
noncomputable section

open scoped SetRel

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.1 introduces the effective domain of the subdifferential
  multifunction, written in the source as `{x | ∂f(x) ≠ ∅}`.
- `core/canonical`: for set-valued maps, mathlib's owner abstraction is the relation domain
  `SetRel.dom`. For the present section, the primitive object is the pairing-level subdifferential
  relation `(x, xStar) ↦ xStar ∈ ∂[Y]f(x)` at codomain `Y`.
- `bridge/view`: the textbook set `{x | ∂f(x) ≠ ∅}` is recovered by specializing `SetRel.dom` to
  that relation, and hence (under the stronger graph ambient) to `subdifferentialGraph f`.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from
  [Definition_23_0_6](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_23_0_6.lean),
  which is the chapter owner for the subdifferential itself;
- `SetRel.dom` and `SetRel.mem_dom` from mathlib's
  [Data/Rel](.lake/packages/mathlib/Mathlib/Data/Rel.lean), the canonical owner API for
  domains of relations / set-valued maps;
- `_root_.subdifferentialGraph` from
  [Definition_5_24_3](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean),
  which is the Chapter 5 graph owner introduced just before this domain specialization;
- the earlier chapter owner `effectiveDomain`, written `dom(f)`, from
  [Definition_4_4](ConvexAnalysis_Rockafellar_1970/Chap01/Definition_4_4.lean),
  which shows the project convention that “effective domain” should land on an existing owner
  notion rather than a new wrapper.

Primitive data vs derived API:
- primitive owner input: `subdifferentialAt`;
- canonical derived API already available upstream: `SetRel.mem_dom`, expressing domain membership
  by existence of a related codomain point;
- source-facing bridge kept here: the textbook nonemptiness reformulation of `SetRel.dom`
  specialized to the subdifferential relation, with the reusable surface notation `dom∂(f)` for
  the source object `dom ∂f`.

Layer target: `bridge/view`. The mathematical content here is not a second owner beside
`subdifferentialAt`; it is the specialization of the canonical relation-domain owner to the
subdifferential relation/graph surface.

Scalar/ambient audit:
- the pairing-explicit owner `dom∂[Y](f)` now lives on the primitive scalar/ambient layer needed
  by Definition 23.0.6 itself (`Add`/`LE` on `𝕜`, `Sub` on `E`);
- the default notation `dom∂(f)` remains the canonical `Y = StrongDual 𝕜 E` specialization.

Notation evaluation:
- the exact textbook surface `dom ∂f` is not a stable Lean term form because `∂f` itself is not
  used as project notation for the subdifferential owner;
- the codomain parameter of the subdifferential owner is mathematically meaningful and not
  recoverable from `f` alone, so the canonical source-facing notation exposes both
  `dom∂[Y](f)` (pairing-explicit) and `dom∂(f)` (default `StrongDual 𝕜 E`) directly on
  the canonical relation-domain owner.
-/

set_option quotPrecheck false in
scoped[Rockafellar] notation "dom∂[" Y_ "](" f ")" =>
  SetRel.dom (fun p : E × Y_ ↦
    Prod.snd p ∈ subdifferentialAt (Y := Y_) f (Prod.fst p))

open scoped Rockafellar

section

variable [Semiring 𝕜] [TopologicalSpace 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

set_option quotPrecheck false in
scoped[Rockafellar] notation "dom∂(" f ")" =>
  SetRel.dom (fun p : E × StrongDual 𝕜 E ↦
    Prod.snd p ∈ subdifferentialAt (Y := StrongDual 𝕜 E) f (Prod.fst p))

/- Definition 5.24.1: the effective domain of `∂f` is the domain of its graph relation, namely
`f ↦ dom∂(f)`, i.e. the canonical owner `(subdifferentialGraph f).dom`. -/

end

/-- A point lies in the pairing-explicit domain owner `dom∂[Y](f)` exactly when the intrinsic
subdifferential at that point is nonempty. -/
@[simp] theorem mem_domSubdifferential_iff_nonempty {f : E → WithTopBot 𝕜}
    {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} :
    x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)).Nonempty := by
  rw [SetRel.mem_dom]
  exact Iff.rfl

/-- Definition 5.24.1, textbook wording: a point lies in `dom∂[Y](f)` exactly when `∂[Y]f(x)` is
not empty. -/
@[simp] theorem mem_domSubdifferential_iff_ne_empty {f : E → WithTopBot 𝕜}
    {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} :
    x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)) ≠ ∅ := by
  rw [mem_domSubdifferential_iff_nonempty]
  exact Set.nonempty_iff_ne_empty

/-- Compatibility wrapper for the earlier theorem name on the nonempty-domain characterization. -/
@[simp] theorem mem_domSubdifferential {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} :
    x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)).Nonempty := by
  simpa using (mem_domSubdifferential_iff_nonempty (f := f) (x := x))

/-- Compatibility wrapper for the earlier theorem name on the `≠ ∅` characterization. -/
@[simp] theorem mem_subdifferentialGraph_dom {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {x : E} :
    x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)) ≠ ∅ := by
  simpa using (mem_domSubdifferential_iff_ne_empty (f := f) (x := x))

end

/-! ### Example_5_24_1 (from Chap05) -/
noncomputable section

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 5.24.1 gives one explicit extended-real-valued convex function on `ℝ`
  and records its one-sided derivative and subdifferential profiles pointwise.
- `core/canonical`: the chapter owner abstractions are already
  `Function.toWithBotTopOn`, `Function.IsClosedProperConvex`, `Function.rightDerivative`,
  `Function.leftDerivative`, and `Function.subdifferentialAt`.
- `bridge/view`: the finite branch on `[-3, 1]` is canonically extended by `+∞` through
  `Function.toWithBotTopOn`, and Theorem 5.24.2 is the nearby bridge identifying one-dimensional
  subdifferentials with the interval between the left and right derivatives. So this example should
  stay on those owners instead of introducing a bespoke two-branch extension or a separate wrapper
  for slope intervals.

Domain-style sampling used here:
- `Function.toWithBotTopOn`, `Function.toWithBotTopOn_of_mem`, and
  `Function.toWithBotTopOn_of_notMem` from `Chap01.Remark_4_4_5`;
- `Function.IsClosedProperConvex` from
  `ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6`;
- `Function.rightDerivative` and `Function.leftDerivative` from
  `ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_1`;
- `Function.subdifferentialAt` and
  `Function.subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative` from
  `ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_2`.

Primitive data vs derived API:
- primitive concrete data introduced here: the explicit real branch
  `x ↦ |x| - 2 * sqrt (1 - x)` together with its support interval `[-3, 1]`;
- derived owner-level object: the extended-real example function obtained from those primitive data
  by the canonical owner `Function.toWithBotTopOn`;
- derived API: the theorem that the example is closed proper convex and the three explicit
  profile identifications with the Chapter 24 owners.

Layer target: `source-facing`.

The final textbook sentence about the graph of `∂f` looking like a "continuous infinite curve" is
geometric prose rather than a precise new theorem, so this statement file records the explicit
owner-level formulas instead.
-/

/-- The Chapter 24 example function
`x ↦ |x| - 2 * sqrt (1 - x)` on `[-3, 1]`, extended by `+∞` outside that interval. -/
def absMinusTwoSqrtOneSubExtension : ℝ → WithBotTop ℝ :=
  Function.toWithBotTopOn
    (fun x : ℝ ↦ |x| - 2 * Real.sqrt (1 - x))
    (Set.Icc (-3 : ℝ) 1)

-- Proof sketch: this is the canonical pointwise evaluation lemma
-- `Function.toWithBotTopOn_of_mem` for the interval support.
/-- On the interval `[-3, 1]`, the Chapter 24 example is given by its explicit finite formula. -/
@[simp] theorem absMinusTwoSqrtOneSubExtension_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc (-3 : ℝ) 1) :
    absMinusTwoSqrtOneSubExtension x =
      ((|x| - 2 * Real.sqrt (1 - x) : ℝ) : WithBotTop ℝ) := sorry

-- Proof sketch: this is the canonical pointwise evaluation lemma
-- `Function.toWithBotTopOn_of_notMem` off the interval support.
/-- Outside the interval `[-3, 1]`, the Chapter 24 example takes the value `+∞`. -/
@[simp] theorem absMinusTwoSqrtOneSubExtension_of_not_mem_Icc {x : ℝ}
    (hx : x ∉ Set.Icc (-3 : ℝ) 1) :
    absMinusTwoSqrtOneSubExtension x = (⊤ : WithBotTop ℝ) := sorry

-- Proof sketch: check directly that the finite branch on `[-3, 1]` is convex and lower
-- semicontinuous, that the extension by `+∞` is proper, and then package these three properties
-- into the canonical owner `Function.IsClosedProperConvex`.
/-- The Chapter 24 example is a closed proper convex function on `ℝ`. -/
theorem absMinusTwoSqrtOneSubExtension_isClosedProperConvex :
    absMinusTwoSqrtOneSubExtension.IsClosedProperConvex := sorry

-- Proof sketch: compute the right secant-slope envelope separately on the four source regions
-- `x ≥ 1`, `0 ≤ x < 1`, `-3 ≤ x < 0`, and `x < -3`, using the explicit finite branch on
-- `[-3, 1]` and the `+∞` extension outside.
/-- The Chapter 24 owner `Function.rightDerivative` has the explicit profile stated in the
example. -/
theorem rightDerivative_absMinusTwoSqrtOneSubExtension (x : ℝ) :
    rightDerivative absMinusTwoSqrtOneSubExtension x =
      if 1 ≤ x then
        ⊤
      else if 0 ≤ x then
        ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
      else if -3 ≤ x then
        ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
      else
        ⊥ := sorry

-- Proof sketch: compute the left secant-slope envelope region by region, paying attention to the
-- boundary points `x = 0` and `x = -3`, where the source formula distinguishes left and right
-- behavior.
/-- The Chapter 24 owner `Function.leftDerivative` has the explicit profile stated in the
example. -/
theorem leftDerivative_absMinusTwoSqrtOneSubExtension (x : ℝ) :
    leftDerivative absMinusTwoSqrtOneSubExtension x =
      if 1 ≤ x then
        ⊤
      else if 0 < x then
        ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
      else if -3 < x then
        ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
      else
        ⊥ := sorry

-- Proof sketch: combine the explicit right- and left-derivative formulas above with
-- `subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative`, then simplify the resulting
-- interval description in each source region to the stated set-valued profile.
/-- Example 5.24.1: for the explicit function
`x ↦ |x| - 2 * sqrt (1 - x)` on `[-3, 1]` and `+∞` outside, the one-dimensional
subdifferential has the stated piecewise profile:
empty for `x ≥ 1` and `x < -3`, a singleton on `0 < x < 1` and `-3 < x < 0`, the interval
`[0, 2]` at `x = 0`, and `(-∞, -1 / 2]` at `x = -3`. -/
theorem subdifferentialAt_absMinusTwoSqrtOneSubExtension (x : ℝ) :
    subdifferentialAt absMinusTwoSqrtOneSubExtension x =
      if 1 ≤ x then
        ∅
      else if 0 < x then
        {1 + (Real.sqrt (1 - x))⁻¹}
      else if x = 0 then
        Set.Icc 0 2
      else if -3 < x then
        {-1 + (Real.sqrt (1 - x))⁻¹}
      else if x = -3 then
        Set.Iic (-((1 : ℝ) / 2))
      else
        ∅ := sorry

end Function

/-! ### Proposition_5_24_1 (from Chap05) -/
noncomputable section

open scoped SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 5.24.1 starts with geometric prose about a complete
  non-decreasing curve in `ℝ²`; that descriptive first sentence is already the content of the
  Chapter 5 owner `SetRel.IsCompleteNondecreasingCurve`. The new precise mathematical content is
  the claim that the coordinate-sum parameter `T(x, x⋆) = x + x⋆` identifies the curve
  homeomorphically with `ℝ`.
- `core/canonical`: graph-like multivalued objects in this chapter are organized as relations
  `SetRel`; the coordinate-sum bridge itself uses only the additive structure of endpoint types,
  while the canonical topology owner for “continuous in both directions, one-to-one, and onto” is
  mathlib's `IsHomeomorph`.
- `bridge/view`: this file adds only the explicit coordinate-sum map on the subtype `Γ` and states
  the proposition on that map, rather than introducing a second packaged notion of “true curve”.

Domain-style sampling used here:
- `SetRel.IsCompleteNondecreasingCurve` and `Function.completeNondecreasingCurve` from
  `Items/Chap05/Definition_5_24_4.lean`;
- `IsHomeomorph` from `Mathlib/Topology/Homeomorph/Defs.lean`;
- order-boundedness owners `BddAbove` and `BddBelow` from mathlib's order API.

Primitive data vs derived API:
- primitive bridge data introduced here: for any additive relation `Γ : SetRel X Y`, the
  coordinate-sum map `Γ.coordinateSumMap : Γ → Z`, i.e. the restriction of `x + y` to the
  relation subtype `Γ`;
- primitive relation-side owner: the coordinate-sum value set `Γ.coordinateSums`;
- primitive range bridge data: generic order-theoretic lemmas saying surjective maps have
  unbounded range in codomains without top/bottom elements, used as bridge lemmas;
- derived conclusion here: if the coordinate-sum map is surjective (in particular if it is an
  `IsHomeomorph`), then `Γ.coordinateSums` is unbounded above and below.

Layer target: `bridge/view`. The first sentence of the source proposition is geometric
interpretation of the owner from Definition 5.24.4, while the formal theorem content here is the
Minty-style coordinate-sum bridge at the canonical API layer.
-/

namespace SetRel

section

variable {X Y Z : Type*} [HAdd X Y Z]

/-- The coordinate-sum parameter on a relation with additive coordinates. -/
abbrev coordinateSumMap (Γ : SetRel X Y) : Γ → Z :=
  fun p ↦ p.1.1 + p.1.2

/-- Evaluating the coordinate-sum map on a point of the graph returns the sum of its two
coordinates. -/
@[simp]
theorem coordinateSumMap_apply {Γ : SetRel X Y} {x : X} {xStar : Y}
    (h : x ~[Γ] xStar) :
    Γ.coordinateSumMap ⟨(x, xStar), h⟩ = x + xStar := rfl

/-- Intrinsic owner for the coordinate-sum values of a relation:
`{x + x⋆ | x ~[Γ] x⋆}`. -/
abbrev coordinateSums (Γ : SetRel X Y) : Set Z :=
  Set.range Γ.coordinateSumMap

/-- Membership in `Γ.coordinateSums` is exactly representability as `x + x⋆` along `Γ`. -/
@[simp]
theorem mem_coordinateSums_iff {Γ : SetRel X Y} {z : Z} :
    z ∈ Γ.coordinateSums ↔ ∃ x : X, ∃ xStar : Y, x ~[Γ] xStar ∧ z = x + xStar := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.1, p.1.2, p.2, rfl⟩
  · rintro ⟨x, xStar, h, rfl⟩
    exact ⟨⟨(x, xStar), h⟩, rfl⟩

end

end SetRel

namespace Function

section

variable {α β : Type*} [LE β]

/- Primitive order-level range bridge: surjectivity already forces the range to be all of the
codomain, so unboundedness follows as soon as the codomain has no top element. -/
namespace Surjective

/-- A surjective function into a type with `≤` and no top element has unbounded-above range. -/
theorem not_bddAbove_range [NoTopOrder β] {f : α → β} (hf : Function.Surjective f) :
    ¬ BddAbove (Set.range f) := by
  rw [hf.range_eq]
  intro h
  rcases h with ⟨a, ha⟩
  rcases NoTopOrder.exists_not_le a with ⟨b, hb⟩
  exact hb (ha (by simp))

/- Dual primitive range bridge for lower bounds. -/
/-- A surjective function into a type with `≤` and no bottom element has unbounded-below range. -/
theorem not_bddBelow_range [NoBotOrder β] {f : α → β} (hf : Function.Surjective f) :
    ¬ BddBelow (Set.range f) := by
  rw [hf.range_eq]
  intro h
  rcases h with ⟨a, ha⟩
  rcases NoBotOrder.exists_not_ge a with ⟨b, hb⟩
  exact hb (ha (by simp))

end Surjective

end

end Function

section

variable {X Y Z : Type*} [HAdd X Y Z] [LE Z]
variable {Γ : SetRel X Y}

namespace Function
namespace Surjective

-- Proof sketch: this is the coordinate-sum specialization of the generic function-level
-- surjective-range bridge above.
/-- If the coordinate-sum map on `Γ` is surjective and the codomain has no top element, then
`Γ.coordinateSums` is unbounded above. -/
theorem not_bddAbove_coordinateSums [NoTopOrder Z]
    (hT : Function.Surjective Γ.coordinateSumMap) :
    ¬ BddAbove Γ.coordinateSums :=
  hT.not_bddAbove_range

-- Proof sketch: same specialization as above, now for lower bounds.
/-- If the coordinate-sum map on `Γ` is surjective and the codomain has no bottom element, then
`Γ.coordinateSums` is unbounded below. -/
theorem not_bddBelow_coordinateSums [NoBotOrder Z]
    (hT : Function.Surjective Γ.coordinateSumMap) :
    ¬ BddBelow Γ.coordinateSums :=
  hT.not_bddBelow_range

/-- Bridge form: unboundedness of `Γ.coordinateSums` stated as unboundedness of the subtype-map
range. -/
theorem not_bddAbove_range_coordinateSumMap [NoTopOrder Z]
    (hT : Function.Surjective Γ.coordinateSumMap) :
    ¬ BddAbove (Set.range Γ.coordinateSumMap) := by
  simpa [SetRel.coordinateSums] using hT.not_bddAbove_coordinateSums

/-- Bridge form: lower-unboundedness of `Γ.coordinateSums` stated on the subtype-map range. -/
theorem not_bddBelow_range_coordinateSumMap [NoBotOrder Z]
    (hT : Function.Surjective Γ.coordinateSumMap) :
    ¬ BddBelow (Set.range Γ.coordinateSumMap) := by
  simpa [SetRel.coordinateSums] using hT.not_bddBelow_coordinateSums

end Surjective
end Function

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsHomeomorph

/-- Homeomorphic coordinate-sum parametrizations are automatically unbounded above in codomains
without top element. -/
theorem not_bddAbove_coordinateSums [NoTopOrder Z]
    (hT : IsHomeomorph Γ.coordinateSumMap) :
    ¬ BddAbove Γ.coordinateSums :=
  hT.surjective.not_bddAbove_coordinateSums

/-- Homeomorphic coordinate-sum parametrizations are automatically unbounded below in codomains
without bottom element. -/
theorem not_bddBelow_coordinateSums [NoBotOrder Z]
    (hT : IsHomeomorph Γ.coordinateSumMap) :
    ¬ BddBelow Γ.coordinateSums :=
  hT.surjective.not_bddBelow_coordinateSums

/-- Bridge form of `IsHomeomorph.not_bddAbove_coordinateSums` on the subtype-map range. -/
theorem not_bddAbove_range_coordinateSumMap [NoTopOrder Z]
    (hT : IsHomeomorph Γ.coordinateSumMap) :
    ¬ BddAbove (Set.range Γ.coordinateSumMap) := by
  simpa [SetRel.coordinateSums] using hT.not_bddAbove_coordinateSums

/-- Bridge form of `IsHomeomorph.not_bddBelow_coordinateSums` on the subtype-map range. -/
theorem not_bddBelow_range_coordinateSumMap [NoBotOrder Z]
    (hT : IsHomeomorph Γ.coordinateSumMap) :
    ¬ BddBelow (Set.range Γ.coordinateSumMap) := by
  simpa [SetRel.coordinateSums] using hT.not_bddBelow_coordinateSums

end IsHomeomorph

end

/-! ### Remark_5_24_1 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [Preorder 𝕜]
variable {E : Type u} [Sub E]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.1 compares the effective domain of the subdifferential with the
  effective domain and relative interior of the original function.
- `core/canonical`: the owner abstractions are `dom∂[Y](f)`, `dom(f)`, `riDom[𝕜](f)`, and
  intrinsic nonemptiness of `_root_.subdifferentialAt` at pairing level `Y`.
- `bridge/view`: the source set `{x | ∂f(x) ≠ ∅}` is already the canonical graph-domain owner
  `dom∂[Y](f)` from Definition 5.24.1, so this item compares existing owners
  rather than introducing a new wrapper.

Domain-style sampling used here:
- `dom∂[·](·)` and `mem_domSubdifferential_iff_nonempty` from
  `Items/Chap05/Definition_5_24_1.lean`;
- `dom(·)` and `riDom[𝕜](·)` from `Items/Chap01/Definition_4_4.lean`.

Primitive data vs derived API:
- primitive inputs: `dom(f).Nonempty` for the right inclusion and owner-level nonemptiness of
  `(∂[Y]f(x)).Nonempty` on `riDom[𝕜](f)` for the left inclusion;
- derived outputs: the left inclusion `riDom[𝕜](f) ⊆ dom∂[Y](f)`, the right
  inclusion `dom∂[Y](f) ⊆ dom(f)`, and the summarized sandwich statement.

Layer target: `bridge/view`.

Semantic-fidelity audit:
- the core owner-level statements are reduced to exact inclusion hypotheses:
  `dom(f).Nonempty` and intrinsic nonemptiness of `(∂[Y]f(x)).Nonempty` on
  `riDom[𝕜](f)`;
- the source-facing convex/proper specialization is provided separately via Theorem 23.4 in the
  pairing-level bridge section below;
- the source notation `dom ∂f` is exposed through the parser-stable surface `dom∂[Y](f)` on
  the canonical owner `(subdifferentialGraph (Y := Y) f).dom`, rather than through a new wrapper
  definition.
-/

-- Proof sketch: choose `y ∈ dom(f)` from the nonemptiness hypothesis. If `x ∈ dom∂[Y](f)`,
-- then some `xStar ∈ subdifferentialAt f x Y` satisfies the global subgradient inequality.
-- Evaluate that inequality at `y` to force `f x < ⊤`, hence `x ∈ dom(f)`.
/-- Any point where the subdifferential is nonempty belongs to the effective domain of the
function. -/
theorem domSubdifferential_subset_dom
    {f : E → WithTopBot 𝕜} (hdom : dom(f).Nonempty) :
    dom∂[Y](f) ⊆ dom(f) := by
  intro x hx
  rw [mem_domSubdifferential_iff_nonempty (Y := Y)] at hx
  rcases hx with ⟨xStar, hxStar⟩
  rcases hdom with ⟨y, hy⟩
  by_contra hx_dom
  have hfx_top : f x = ⊤ := by
    have : ¬ f x < ⊤ := by
      simpa [mem_effectiveDomain] using hx_dom
    simpa [lt_top_iff_ne_top] using this
  have hy_top : f y = ⊤ := by
    have : (⊤ : WithTopBot 𝕜) ≤ f y := by
      simpa [hfx_top] using (mem_subdifferentialAt_pairing.mp hxStar) y
    simpa using this
  exact (mem_effectiveDomain.mp hy).ne hy_top

end

section

variable {𝕜 : Type v} [Ring 𝕜] [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

-- Proof sketch: this is exactly the canonical domain-membership characterization
-- `x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)).Nonempty`, specialized to points in
-- `riDom[𝕜](f)`.
/-- Any owner-side proof that `(∂[Y]f(x)).Nonempty` on `riDom[𝕜](f)` yields
the inclusion `riDom[𝕜](f) ⊆ dom∂[Y](f)`. -/
theorem riDom_subset_domSubdifferential
    {f : E → WithTopBot 𝕜}
    (hsub_riDom : ∀ ⦃x : E⦄, x ∈ riDom[𝕜](f) → (∂[Y]f(x)).Nonempty) :
    riDom[𝕜](f) ⊆ dom∂[Y](f) := by
  intro x hx
  exact (mem_domSubdifferential_iff_nonempty (Y := Y)).2 (hsub_riDom hx)

-- Proof sketch: combine the two previous inclusion theorems.
/-- The canonical domain owner `dom∂[Y](f)` lies between `riDom[𝕜](f)` and `dom(f)` whenever
subdifferentials are nonempty on `riDom[𝕜](f)` and `dom(f)` is nonempty. -/
theorem domSubdifferential_between_riDom_and_dom
    {f : E → WithTopBot 𝕜}
    (hsub_riDom : ∀ ⦃x : E⦄, x ∈ riDom[𝕜](f) → (∂[Y]f(x)).Nonempty)
    (hdom : dom(f).Nonempty) :
    riDom[𝕜](f) ⊆ dom∂[Y](f) ∧ dom∂[Y](f) ⊆ dom(f) :=
  ⟨riDom_subset_domSubdifferential hsub_riDom,
    domSubdifferential_subset_dom hdom⟩

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

-- Proof sketch: Theorem 23.4 gives intrinsic nonemptiness of `∂[Y]f(x)` on
-- `riDom[𝕜](f)`. Feed that owner-level input directly to the primitive inclusion theorem.
/-- Every point of the relative interior of the effective domain lies in the effective domain of
the subdifferential graph for a proper convex function. -/
theorem riDom_subset_domSubdifferential_of_convex_proper
    {f : E → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    riDom[𝕜](f) ⊆ dom∂[Y](f) := by
  apply _root_.riDom_subset_domSubdifferential (f := f)
  intro x hx
  simpa using (_root_.subdifferentialAt_nonempty_of_mem_riDom
    (Y := Y) hf_convex hf_proper hx)

-- Proof sketch: combine the convex/proper left inclusion with the owner-side right inclusion.
/-- Remark 5.24.1: although the effective domain of the subdifferential need not be convex, its
canonical domain owner `dom∂[Y](f)` lies between `ri[𝕜](dom f)` and `dom(f)`. -/
theorem domSubdifferential_between_riDom_and_dom_of_convex_proper
    {f : E → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    riDom[𝕜](f) ⊆ dom∂[Y](f) ∧ dom∂[Y](f) ⊆ dom(f) :=
  ⟨riDom_subset_domSubdifferential_of_convex_proper hf_convex hf_proper,
    domSubdifferential_subset_dom hf_proper.nonempty_dom⟩

end

/-! ### Theorem_5_24_1 (from Chap05) -/
noncomputable section

open Filter
open Set
open scoped Rockafellar Topology

/-!
Source/core/bridge triage for this item.

  theorem for the right and left derivatives of a proper convex function on an ordered scalar line,
  stated at
  interior points of `dom(f)` for the continuity clauses.
- `core/canonical`: the chapter owner abstraction for directional variation is
  `Function.directionalDifferenceQuotientAt` / `Function.directionalDerivativeAt`, and the ambient
  convexity owner is `Function.IsConvex 𝕜`; properness is carried separately by
  `Function.IsProper` exactly where the one-sided continuity and finiteness clauses need it.
- `bridge/view`: the source's one-sided derivatives are the right/left secant
  slope envelopes of the Chapter 23 directional quotient owner. On `dom(f)` they agree with the
  directional derivatives in directions `1` and `-1`; off `dom(f)` the same secant-slope owner
  gives the textbook `±∞` extension without introducing a second package of chosen data.

Domain-style sampling used here:
- `Function.directionalDifferenceQuotientAt` and `Function.directionalDerivativeAt` from
  `Chap05/Lemma_23_0_1`, which are the chapter owners for directional derivatives;
- `ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior`,
  `ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior`,
  `ConvexOn.monotoneOn_rightDeriv`, `ConvexOn.monotoneOn_leftDeriv`, and
  `ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior` from
  `Mathlib/Analysis/Convex/Deriv.lean`, which organize the finite-valued one-dimensional convex
  theory around secant slopes and one-sided derivatives on the interior of the domain;
- `ConvexOn.secant_mono` from `Mathlib/Analysis/Convex/Slope.lean`, which is the canonical slope
  monotonicity owner behind the source inequality
  `f'_+(z₁) ≤ f'_-(x) ≤ f'_+(x) ≤ f'_-(z₂)`.

Primitive data vs derived API:
- primitive source-facing owners: `Function.rightDerivative` and `Function.leftDerivative`;
- derived API: the identification with the Chapter 23 directional derivative at a finite point,
  the atomic order inequalities between the one-sided derivatives, monotonicity, finiteness on
  `interior (dom(f))`, the four one-sided limit formulas, and the companion
  `Function.leftLim` / `Function.rightLim` bridge equalities;
- assumption split used below: the directional-derivative bridge uses convexity plus the explicit
  finite-point guard `x ∈ dom(f)` and `f x ≠ ⊥`, the order and monotonicity facts use only
  convexity, and the one-sided finiteness/continuity statements use convexity + properness at
  points of `interior (dom(f))`.

Layer target: `source-facing`.

Notation evaluation:
- the textbook symbols are surfaced by ordinary scoped notation as `f′+` and `f′-`, so theorem
  statements can stay close to the source while keeping the canonical owners
  `Function.rightDerivative` and `Function.leftDerivative` as definitions.
- mathlib's `rightDeriv` / `leftDeriv` are interior-point finite-valued companion owners, so they
  stay part of the domain-style sampling rather than replacing the source-facing extended-real
  owners below.
-/

namespace Function

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Internal secant-slope set for the source right derivative. This is proof-facing scaffolding,
not a second public owner. -/
private def rightDerivativeSlopeSet (f : 𝕜 → WithTopBot 𝕜) (x : 𝕜) : Set (WithTopBot 𝕜) :=
  directionalDifferenceQuotientAt f x 1 '' {t : 𝕜 | 0 < t ∧ x + t ∈ dom(f)}

/-- Internal secant-slope set for the source left derivative. This is proof-facing scaffolding,
not a second public owner. -/
private def leftDerivativeSlopeSet (f : 𝕜 → WithTopBot 𝕜) (x : 𝕜) : Set (WithTopBot 𝕜) :=
  (fun t : 𝕜 ↦ -directionalDifferenceQuotientAt f x (-1) t) ''
    {t : 𝕜 | 0 < t ∧ x - t ∈ dom(f)}

/-- The source right derivative `f'_+(x)` on the line, extended by the canonical empty-infimum /
secant-slope rule outside `dom(f)`. The definition is built directly from the Chapter 23
directional-difference owner and keeps the owner at the slope level rather than packaging extra
data. -/
def rightDerivative (f : 𝕜 → WithTopBot 𝕜) (x : 𝕜) : WithTopBot 𝕜 :=
  sInf (rightDerivativeSlopeSet f x)

/-- The source left derivative `f'_-(x)` on the line, written through the Chapter 23
directional-difference owner in direction `-1` and the same secant-slope extension rule outside
`dom(f)`. -/
def leftDerivative (f : 𝕜 → WithTopBot 𝕜) (x : 𝕜) : WithTopBot 𝕜 :=
  sSup (leftDerivativeSlopeSet f x)

/-- Textbook one-sided right derivative notation for `Function.rightDerivative`. -/
scoped[Rockafellar] notation:max f "′+" => Function.rightDerivative f

/-- Textbook one-sided left derivative notation for `Function.leftDerivative`. -/
scoped[Rockafellar] notation:max f "′-" => Function.leftDerivative f

variable {f : 𝕜 → WithTopBot 𝕜}

section Topological

variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]

-- Proof sketch: once `x ∈ dom(f)`, the secant-slope infimum defining `f'_+(x)` is exactly the
-- Chapter 23 right directional derivative in direction `1`.
/-- At a finite point of a convex function, the source right derivative is the Chapter 23
directional derivative in direction `1`. -/
theorem rightDerivative_eq_directionalDerivativeAt_one
    (hf_convex : f.IsConvex 𝕜) {x : 𝕜} (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    f′+ x = directionalDerivativeAt f x 1 := by
  sorry

-- Proof sketch: on `dom(f)`, the source left derivative is the negated Chapter 23 directional
-- derivative in direction `-1`.
/-- At a finite point of a convex function, the source left derivative is the negative of the
Chapter 23 directional derivative in direction `-1`. -/
theorem leftDerivative_eq_neg_directionalDerivativeAt_neg_one
    (hf_convex : f.IsConvex 𝕜) {x : 𝕜} (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    f′- x = -directionalDerivativeAt f x (-1) := by
  sorry

end Topological

/-- If `x` lies to the right of some finite point of `f` but does not itself belong to `dom(f)`,
then the source left derivative at `x` is `+∞`. -/
theorem leftDerivative_eq_top_of_not_mem_dom_of_nonempty_inter_Iio
    {x : 𝕜} (hx : x ∉ dom(f)) (hy : (dom(f) ∩ Iio x).Nonempty) :
    f′- x = ⊤ := by
  rcases hy with ⟨y, hy_dom, hyx⟩
  have hx_top : f x = ⊤ := by
    by_contra hx_top
    exact hx ((mem_effectiveDomain).2 (lt_top_iff_ne_top.mpr hx_top))
  let t : 𝕜 := x - y
  have ht : 0 < t := sub_pos.mpr hyx
  have hsub : x - t = y := by
    dsimp [t]
    linarith
  have hxt : x - t ∈ dom(f) := by
    simpa [hsub] using hy_dom
  have htop_mem :
      (⊤ : WithTopBot 𝕜) ∈
        (fun t : 𝕜 ↦ -directionalDifferenceQuotientAt f x (-1) t) ''
          {t : 𝕜 | 0 < t ∧ x - t ∈ dom(f)} := by
    refine ⟨t, ⟨ht, hxt⟩, ?_⟩
    change -directionalDifferenceQuotientAt f x (-1) t = ⊤
    unfold directionalDifferenceQuotientAt
    have hadd : x + t • (-1 : 𝕜) = y := by
      dsimp [t]
      linarith
    rw [hadd, hx_top]
    have hdiv : (⊥ : WithTopBot 𝕜) / (t : WithTopBot 𝕜) = ⊥ := by
      have h_inv : 0 < t⁻¹ := inv_pos.mpr ht
      simpa [WithBotTop.div_eq_mul_inv, WithBotTop.coe_inv] using
        (WithBotTop.bot_mul_coe_of_pos (a := t⁻¹) h_inv)
    change -(((show WithTopBot 𝕜 from f y) - (⊤ : WithTopBot 𝕜)) / (t : WithTopBot 𝕜)) = ⊤
    rw [show ((show WithTopBot 𝕜 from f y) - (⊤ : WithTopBot 𝕜)) = (⊥ : WithTopBot 𝕜) by simp,
      hdiv]
    simp
  unfold leftDerivative leftDerivativeSlopeSet
  exact top_le_iff.mp (le_sSup htop_mem)

/-- If `x` lies to the left of some finite point of `f` but does not itself belong to `dom(f)`,
then the source right derivative at `x` is `-∞`. -/
theorem rightDerivative_eq_bot_of_not_mem_dom_of_nonempty_inter_Ioi
    {x : 𝕜} (hx : x ∉ dom(f)) (hy : (dom(f) ∩ Ioi x).Nonempty) :
    f′+ x = ⊥ := by
  rcases hy with ⟨y, hy_dom, hxy⟩
  have hx_top : f x = ⊤ := by
    by_contra hx_top
    exact hx ((mem_effectiveDomain).2 (lt_top_iff_ne_top.mpr hx_top))
  let t : 𝕜 := y - x
  have ht : 0 < t := sub_pos.mpr hxy
  have hadd : x + t = y := by
    dsimp [t]
    linarith
  have hxt : x + t ∈ dom(f) := by
    simpa [hadd] using hy_dom
  have hbot_mem :
      (⊥ : WithTopBot 𝕜) ∈
        directionalDifferenceQuotientAt f x 1 ''
          {t : 𝕜 | 0 < t ∧ x + t ∈ dom(f)} := by
    refine ⟨t, ⟨ht, hxt⟩, ?_⟩
    unfold directionalDifferenceQuotientAt
    have hsmul : x + t • (1 : 𝕜) = y := by
      dsimp [t]
      linarith
    change (((show WithTopBot 𝕜 from f (x + t • (1 : 𝕜))) - (show WithTopBot 𝕜 from f x)) /
      (t : WithTopBot 𝕜)) = ⊥
    rw [hsmul, hx_top]
    change (((show WithTopBot 𝕜 from f y) - (⊤ : WithTopBot 𝕜)) /
      (t : WithTopBot 𝕜)) = ⊥
    have hdiv : (⊥ : WithTopBot 𝕜) / (t : WithTopBot 𝕜) = ⊥ := by
      have h_inv : 0 < t⁻¹ := inv_pos.mpr ht
      simpa [WithBotTop.div_eq_mul_inv, WithBotTop.coe_inv] using
        (WithBotTop.bot_mul_coe_of_pos (a := t⁻¹) h_inv)
    rw [show ((show WithTopBot 𝕜 from f y) - (⊤ : WithTopBot 𝕜)) = (⊥ : WithTopBot 𝕜) by simp,
      hdiv]
  unfold rightDerivative rightDerivativeSlopeSet
  exact le_bot_iff.mp (sInf_le hbot_mem)

-- Proof sketch: compare the relevant secant slopes directly. For `z < x`, every right secant at
-- `z` is bounded above by every left secant at `x` by convex slope monotonicity, and the empty
-- set cases reproduce the textbook `±∞` extension outside `dom(f)`.
/-- The source secant-order inequality `f'_+(z) ≤ f'_-(x)` for `z < x`. -/
theorem rightDerivative_le_leftDerivative_of_lt
    (hf_convex : f.IsConvex 𝕜) {z x : 𝕜} (hzx : z < x) :
    f′+ z ≤ f′- x := by
  sorry

/-- The source inequality `f'_-(x) ≤ f'_+(x)`. -/
theorem leftDerivative_le_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (x : 𝕜) :
    f′- x ≤ f′+ x := by
  sorry

/-- The source right derivative is nondecreasing. -/
theorem monotone_rightDerivative
    (hf_convex : f.IsConvex 𝕜)
    : Monotone (f′+) := by
  sorry

/-- The source left derivative is nondecreasing. -/
theorem monotone_leftDerivative
    (hf_convex : f.IsConvex 𝕜)
    : Monotone (f′-) := by
  sorry

section Topological

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]

/-- On the interior of the effective domain, the source right derivative is finite. -/
theorem rightDerivative_lt_top_of_mem_interior_dom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    f′+ x < ⊤ := by
  sorry

/-- On the interior of the effective domain, the source left derivative is finite. -/
theorem bot_lt_leftDerivative_of_mem_interior_dom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    ⊥ < f′- x := by
  sorry

-- Proof sketch: the order chain implies that `rightDerivative` is right-continuous and that its
-- left limit is `leftDerivative`; the same argument with the roles reversed gives the two formulas
-- for `leftDerivative`.
/-- On `interior (dom(f))`, the source right derivative is right-continuous. -/
theorem tendsto_rightDerivative_right
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    Tendsto (f′+) (𝓝[>] x) (𝓝 (f′+ x)) := by
  sorry

/-- On `interior (dom(f))`, the left limit of the source right derivative at `x` is the source
left derivative at `x`. -/
theorem tendsto_rightDerivative_left
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    Tendsto (f′+) (𝓝[<] x) (𝓝 (f′- x)) := by
  sorry

/-- On `interior (dom(f))`, the right limit of the source left derivative at `x` is the source
right derivative at `x`. -/
theorem tendsto_leftDerivative_right
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    Tendsto (f′-) (𝓝[>] x) (𝓝 (f′+ x)) := by
  sorry

/-- On `interior (dom(f))`, the source left derivative is left-continuous. -/
theorem tendsto_leftDerivative_left
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    Tendsto (f′-) (𝓝[<] x) (𝓝 (f′- x)) := by
  sorry

/-- On `interior (dom(f))`, the canonical strict right limit of the source right derivative agrees
with its value. -/
theorem rightLim_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    (f′+).rightLim x = f′+ x := by
  exact rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (tendsto_rightDerivative_right hf_convex hf_proper hx)

/-- On `interior (dom(f))`, the canonical strict left limit of the source right derivative is the
source left derivative. -/
theorem leftLim_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    (f′+).leftLim x = f′- x := by
  exact leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (tendsto_rightDerivative_left hf_convex hf_proper hx)

/-- The canonical strict right limit of the source left derivative is the source right derivative.
-/
theorem rightLim_leftDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    (f′-).rightLim x = f′+ x := by
  exact rightLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (tendsto_leftDerivative_right hf_convex hf_proper hx)

/-- On `interior (dom(f))`, the canonical strict left limit of the source left derivative agrees
with its value. -/
theorem leftLim_leftDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : 𝕜} (hx : x ∈ interior (dom(f))) :
    (f′-).leftLim x = f′- x := by
  exact leftLim_eq_of_tendsto (neBot_iff.mp inferInstance)
    (tendsto_leftDerivative_left hf_convex hf_proper hx)

end Topological

end Function

/-! ### Corollary_5_24_2 (from Chap05) -/
noncomputable section

open scoped Pointwise Rockafellar Topology

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core triage for this item.

- `source-facing`: Corollary 5.24.2 asserts upper semicontinuity of the directional derivative on
  `interior (dom(f)) × E` and the local upper-semicontinuity of the subdifferential map near an
  interior point of `dom(f)`.
- `core/canonical`: the owner declarations already present upstream are
  `Function.directionalDerivativeAt`, `_root_.subdifferentialAt`, the chapter effective-domain
  owner `dom(·)`, and the convergence theorem
  `Function.limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex` together with
  `Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex`
  from Theorem 5.24.8; for this item's primary theorem surfaces, the intrinsic-domain owner is
  `riDom[𝕜](f)`.
- `bridge/view`: the ambient `interior (dom(f))` forms are retained only as thin wrappers from the
  intrinsic owner layer via `interior_subset_intrinsicInterior`.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` from `Chap05/Lemma_23_0_1`;
- `Function.limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex` from
  `Chap05/Theorem_5_24_8`;
- `_root_.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `UpperSemicontinuousOn` from mathlib's semicontinuity API.

Primitive data vs derived API:
- primitive source data: a convex function `f` finite on the intrinsic domain owner
  `riDom[𝕜](f)` (owner `f.IsFiniteOn (riDom[𝕜](f))`) and a point in `riDom[𝕜](f)`;
- derived API: upper semicontinuity of `(x, y) ↦ directionalDerivativeAt f x y` on
  `riDom[𝕜](f) × E`, and the local closed-ball inclusion for the canonical dual
  subdifferential.

Layer target:
- clause `(1)`: `core/canonical`, with an ambient-interior bridge;
- clause `(2)`: `core/canonical`, with an ambient-interior bridge.

Ambient-assumption minimization:
- the directional-derivative clause uses only the finite-dimensional normed-space layer
  already required by Theorem 5.24.8, exposed at the scalar-generic layer `𝕜`;
- the canonical subdifferential inclusion stays at the dual owner
  `_root_.subdifferentialAt`, with explicit pairing codomain parameter `Y`.
-/

namespace Function

variable {f : E → WithTopBot 𝕜}

-- Proof sketch: apply Theorem 5.24.8 to the constant sequence `fSeq i = f` on the open convex set
-- `riDom[𝕜](f)`, then pass from the resulting limsup inequality along convergent sequences
-- in `riDom[𝕜](f) × E` to the canonical product-space predicate `UpperSemicontinuousOn`.
/-- Corollary 5.24.2 (1), intrinsic-domain primitive owner form: if `f` is convex and finite on
`riDom[𝕜](f)`, then `(x, y) ↦ directionalDerivativeAt f x y` is upper semicontinuous on
`riDom[𝕜](f) ×ˢ Set.univ`. -/
theorem upperSemicontinuousOn_directionalDerivativeAt_on_riDom_of_isFiniteOn
    (hf_convex : f.IsConvex 𝕜) (hf_finite_riDom : f.IsFiniteOn (riDom[𝕜](f))) :
    UpperSemicontinuousOn
      (Function.uncurry (directionalDerivativeAt f))
      (riDom[𝕜](f) ×ˢ Set.univ) := sorry

/-- Corollary 5.24.2 (1), intrinsic-domain source-facing form specialized to proper convex
functions. -/
theorem upperSemicontinuousOn_directionalDerivativeAt_on_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    UpperSemicontinuousOn
      (Function.uncurry (directionalDerivativeAt f))
      (riDom[𝕜](f) ×ˢ Set.univ) := by
  refine
    upperSemicontinuousOn_directionalDerivativeAt_on_riDom_of_isFiniteOn
      (f := f) hf_convex ?_
  intro x hx
  exact ⟨intrinsicInterior_subset hx, hf_proper.ne_bot x⟩

/-- Corollary 5.24.2 (1), source-facing ambient bridge: the intrinsic-domain theorem yields the
ambient interior-domain form. -/
theorem upperSemicontinuousOn_directionalDerivativeAt_on_interior_dom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    UpperSemicontinuousOn
      (Function.uncurry (directionalDerivativeAt f))
      (interior (dom(f)) ×ˢ Set.univ) := by
  refine
    (upperSemicontinuousOn_directionalDerivativeAt_on_riDom
      (f := f) hf_convex hf_proper).mono ?_
  intro p hp
  exact ⟨interior_subset_intrinsicInterior (𝕜 := 𝕜) hp.1, hp.2⟩

variable {Y : Type (max u v)} [NormedAddCommGroup Y] [HasPairing E Y 𝕜]

-- Proof sketch: specialize the set-valued upper-semicontinuity theorem of Theorem 5.24.8 to the
-- constant sequence `fSeq i = f` on `riDom[𝕜](f)`.
/-- Corollary 5.24.2 (2), intrinsic-domain primitive owner form: if `f` is convex and finite on
`riDom[𝕜](f)`, then for every `x ∈ riDom[𝕜](f)` and every `ε > 0` there is `δ > 0` such that
every `z ∈ Metric.closedBall x δ` satisfies
`∂[Y]f(z) ⊆ ∂[Y]f(x) + Metric.closedBall (0 : Y) ε`. -/
theorem exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_riDom_of_isFiniteOn
    (hf_convex : f.IsConvex 𝕜) (hf_finite_riDom : f.IsFiniteOn (riDom[𝕜](f)))
    {x : E} (hx : x ∈ riDom[𝕜](f)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.closedBall x δ,
      (∂[Y]f(z)) ⊆ (∂[Y]f(x)) + Metric.closedBall (0 : Y) ε := sorry

/-- Corollary 5.24.2 (2), intrinsic-domain source-facing form specialized to proper convex
functions. -/
theorem exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : E} (hx : x ∈ riDom[𝕜](f)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.closedBall x δ,
      (∂[Y]f(z)) ⊆ (∂[Y]f(x)) + Metric.closedBall (0 : Y) ε := by
  refine
    exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_riDom_of_isFiniteOn
      (f := f) (Y := Y) hf_convex ?_ hx ε hε
  intro u hu
  exact ⟨intrinsicInterior_subset hu, hf_proper.ne_bot u⟩

/-- Corollary 5.24.2 (2), source-facing ambient bridge: the intrinsic-domain theorem yields the
ambient interior-domain form. -/
theorem exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_interior_dom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : E} (hx : x ∈ interior (dom(f))) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.closedBall x δ,
      (∂[Y]f(z)) ⊆ (∂[Y]f(x)) + Metric.closedBall (0 : Y) ε := by
  exact
    exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_riDom
      (f := f) (Y := Y) hf_convex hf_proper
      (x := x) (interior_subset_intrinsicInterior (𝕜 := 𝕜) hx) ε hε

end Function

end

/-! ### Corollary_5_24_2_EuclideanBridge (from Chap05) -/
noncomputable section

open scoped Pointwise Rockafellar Topology

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function

variable {f : E → WithBotTop ℝ}

-- Proof sketch: transport the canonical dual-valued clause
-- `exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_interior_dom` through
-- `InnerProductSpace.toDualMap ℝ E`.
/-- Corollary 5.24.2 (2), Euclidean bridge form: for a proper convex function, every interior point
`x ∈ interior (dom(f))`
and every `ε > 0` admit a radius `δ > 0` such that for every
`z ∈ Metric.closedBall x δ`, the Euclidean subdifferential satisfies
`∂ᵥf(z) ⊆ ∂ᵥf(x) + Metric.closedBall (0 : E) ε`. -/
theorem exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_interior_dom_euclidean
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {x : E} (hx : x ∈ interior (dom(f))) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.closedBall x δ,
      (∂ᵥf(z)) ⊆ (∂ᵥf(x)) + Metric.closedBall (0 : E) ε := sorry

end Function

end

/-! ### Definition_5_24_2 (from Chap05) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.2 introduces the range of the subdifferential multifunction,
  written in the source as the union of fibers `⋃ {∂f(x)}`.
- `core/canonical`: for set-valued maps, mathlib's owner abstraction for the range is the relation
  codomain `SetRel.cod`. The primitive owner object here is the pairing-level relation
  `(x, x⋆) ↦ x⋆ ∈ ∂[Y]f(x)`.
- `bridge/view`: the textbook union formula for `range ∂f` is the specialization of `SetRel.cod`
  to this relation.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from
  [Definition_23_0_6](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_23_0_6.lean),
  which is the chapter owner for the subdifferential itself;
- `SetRel.cod` and `SetRel.mem_cod` from mathlib's
  [Data/Rel](.lake/packages/mathlib/Mathlib/Data/Rel.lean), the canonical owner API for the
  codomain/range of a relation.
- `_root_.subdifferentialGraph` from
  [Definition_5_24_3](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean),
  which provides the stronger graph/image bridge layer used below.

Primitive data vs derived API:
- primitive owner: the pairing-level relation `(x, x⋆) ↦ x⋆ ∈ ∂[Y]f(x)`;
- derived API: the source-facing union reformulation of its codomain;
  the existence-style membership shape is already the exact canonical owner theorem
  `SetRel.mem_cod`.

Layer target: `bridge/view`. The item does not introduce a second owner beside
`subdifferentialAt`; it specializes the canonical relation-codomain owner to the subdifferential
relation, with the graph/image lemmas kept as bridge API.
-/

set_option quotPrecheck false in
/-- Definition 5.24.2: the range of `∂f` is the codomain of its subdifferential relation. -/
abbrev codSubdifferential (f : E → WithTopBot 𝕜) {Y : Type (max u v)} [HasPairing E Y 𝕜] :
    Set Y :=
  SetRel.cod (fun p : E × Y ↦
    Prod.snd p ∈ subdifferentialAt (Y := Y) f (Prod.fst p))

set_option quotPrecheck false in
scoped[Rockafellar] notation "cod∂[" Y_ "](" f ")" =>
  _root_.codSubdifferential (f := f) (Y := Y_)

/-- A dual-side point lies in `cod∂[Y](f)` exactly when it is a subgradient at some base point. -/
@[simp] theorem mem_codSubdifferential {f : E → WithTopBot 𝕜} {Y : Type (max u v)}
    [HasPairing E Y 𝕜] {xStar : Y} :
    xStar ∈ cod∂[Y](f) ↔ ∃ x, xStar ∈ ∂[Y]f(x) := by
  rw [SetRel.mem_cod]
  exact Iff.rfl

/-- Definition 5.24.2, textbook wording: the range of `∂f` is the union of the fibers
`subdifferentialAt f x`. -/
theorem subdifferentialGraph_cod_eq_iUnion_subdifferentialAt (f : E → WithTopBot 𝕜)
    {Y : Type (max u v)} [HasPairing E Y 𝕜] :
    cod∂[Y](f) = ⋃ x, ∂[Y]f(x) := by
  ext xStar
  constructor
  · intro hxStar
    rcases (mem_codSubdifferential (f := f) (Y := Y) (xStar := xStar)).mp hxStar with ⟨x, hxSubgrad⟩
    exact Set.mem_iUnion.mpr ⟨x, hxSubgrad⟩
  · intro hxStar
    rcases Set.mem_iUnion.mp hxStar with ⟨x, hxSubgrad⟩
    exact (mem_codSubdifferential (f := f) (Y := Y) (xStar := xStar)).mpr ⟨x, hxSubgrad⟩

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

section

variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

set_option quotPrecheck false in
scoped[Rockafellar] notation "cod∂(" f ")" =>
  _root_.codSubdifferential (f := f) (Y := StrongDual 𝕜 E)

end

/-- The canonical range owner `cod∂[Y](f)` is the image of `univ` under the subdifferential
graph relation, i.e. the global subdifferential image. -/
theorem codSubdifferential_eq_subdifferentialImage_univ
    (f : E → WithTopBot 𝕜) {Y : Type (max u v)} [HasPairing E Y 𝕜] :
    cod∂[Y](f) = subdifferentialImage (f := f) (S := Set.univ) (Y := Y) := by
  change (subdifferentialGraph (Y := Y) f).cod =
      SetRel.image (subdifferentialGraph (Y := Y) f) Set.univ
  exact (SetRel.image_univ_right (R := subdifferentialGraph (Y := Y) f)).symm

/-- Default-codomain specialization of the range owner: `cod∂(f)` is exactly the global
subdifferential image at codomain `StrongDual 𝕜 E`. -/
theorem codSubdifferential_eq_subdifferentialImage_univ_default
    [HasPairing E (StrongDual 𝕜 E) 𝕜] (f : E → WithTopBot 𝕜) :
    cod∂(f) = subdifferentialImage (f := f) (S := Set.univ) := by
  simpa using codSubdifferential_eq_subdifferentialImage_univ
    (f := f) (Y := StrongDual 𝕜 E)

end

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LE 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!
Source/core/bridge triage for the inner-product-space range bridge.

- `source-facing`: later Section 24 items in the textbook model speak about vector
  subgradients.
- `core/canonical`: the owner range remains `_root_.subdifferentialGraph f |>.cod`, valued in the
  continuous dual.
- `bridge/view`: `Function.subdifferentialGraph f` transports that owner graph along
  `InnerProductSpace.toDualMap 𝕜 E`, so its codomain is exactly the vector-valued range of `∂f`.

Domain-style sampling used here:
- `_root_.subdifferentialGraph` from
  [Definition_5_24_3](ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean);
- `Function.subdifferentialAt` and `Function.subdifferentialGraph` from the Chapter 23/24 owner
  file graph;
- mathlib's canonical inner-product-to-dual map `InnerProductSpace.toDualMap`.

Primitive data vs derived API:
- primitive owner: `Function.subdifferentialGraph f`;
- derived API: the source-facing union reformulation of
  `(Function.subdifferentialGraph f).cod`; the existence-style membership shape is already the
  exact owner theorem `SetRel.mem_cod`.

Layer target: `bridge/view`.
-/

namespace Function

/-- Vector-valued range owner for the inner-product-space bridge. -/
scoped[Rockafellar] notation "cod∂ᵥ(" f ")" => SetRel.cod (Function.subdifferentialGraph f)

/-- Definition 5.24.2, textbook wording on an ordered inner-product space: the range of the
vector-valued subdifferential is the union of the sets `subdifferentialAt f x`. -/
theorem subdifferentialGraph_cod_eq_iUnion_subdifferentialAt (f : E → WithTopBot 𝕜) :
    cod∂ᵥ(f) = ⋃ x, ∂ᵥf(x) := by
  ext xStar
  constructor
  · intro hxStar
    rcases SetRel.mem_cod.mp hxStar with ⟨x, hxGraph⟩
    exact Set.mem_iUnion.mpr ⟨x, mem_subdifferentialGraph.mp hxGraph⟩
  · intro hxStar
    rcases Set.mem_iUnion.mp hxStar with ⟨x, hxSubgrad⟩
    exact SetRel.mem_cod.mpr ⟨x, mem_subdifferentialGraph.mpr hxSubgrad⟩

end Function

end
