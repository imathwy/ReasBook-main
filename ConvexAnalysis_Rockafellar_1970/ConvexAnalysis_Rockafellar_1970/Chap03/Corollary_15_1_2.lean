import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ENNReal GaugePolar NNReal RealInnerProductSpace Rockafellar

section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 15.1.2 says that for a closed convex set `C` containing `0`, the
  gauge `γ(· | C)` and the support function `δ^*(· | C)` are closed gauges polar to each other.
- `core/canonical`: the owner abstractions are the set gauge `egauge ℝ≥0`, the support function
  `supportFunction`, the set polar `Set.polar`, the gauge polar `gauge_polar`, and the chapter
  closed-gauge owner class `IsClosedGauge`.
- `bridge/view`: Rockafellar's gauge is rendered by the canonical extended gauge `egauge ℝ≥0`,
  coerced to `EReal`; the corollary is then expressed directly through the existing owner theorems
  for gauge polarity and support functions.

Domain-style sampling used here:
- `egauge_lowerSemicontinuous` from `Corollary_9_7_1`;
- `Function.isConvex_supportFunction` from `Text_5_5_0`;
- `lowerSemicontinuous_supportFunction` from `Text_13_2_3`;
- `IsClosedGauge` from `Text_15_0_24`;
- `gauge_polar_isClosedGauge` and
  `gauge_polar_egauge_eq_egauge_polar` from `Theorem_15_1`;
- `egauge_polar_eq_supportFunction` from `Theorem_14_5`.

Primitive data vs derived API:
- primitive data for the full polar-pair corollary: a set `C : Set E` with `IsClosed C`,
  `Convex ℝ C`, and `(0 : E) ∈ C`;
- primitive data for the support-function closed-gauge clause: only `(0 : E) ∈ C`, since convexity
  and lower semicontinuity of `supportFunction C` are already owner-side facts for arbitrary sets;
- primitive data for the `egauge` closed-gauge clause: `IsClosed C`, `Convex ℝ C`, and
  `C.Nonempty`, since lower semicontinuity is already owner-side and the remaining zero-value gauge
  axiom needs only a witness in `C`;
- owner-side closedness facts already available upstream:
  `egauge_lowerSemicontinuous`, `Function.isConvex_supportFunction`,
  `lowerSemicontinuous_supportFunction`, and the owner class `IsClosedGauge`;
- genuinely new corollary content kept here: the closed-gauge structures on
  `γ C` and `supportFunction C`, together with the two polar identities exchanging them.

Layer target: `bridge/view`, reusing the upstream owner declarations directly and avoiding
parallel local wrappers for closed gauges.

Ambient minimization:
- the support-function clause lives at the same seminormed real inner-product layer as the sampled
  owner declarations `supportFunction`, `Function.isConvex_supportFunction`, and
  `lowerSemicontinuous_supportFunction`;
- the `egauge` closed-gauge clause lives at the weaker real topological-module layer already used
  by `egauge_lowerSemicontinuous` and `egauge_zero_right`;
- only the two polar identities remain in the finite-dimensional real inner-product section,
  because they reuse the Chapter 14–15 polar theorems.
-/

variable {C : Set E}

-- Proof sketch: `Function.isConvex_supportFunction` and `lowerSemicontinuous_supportFunction` are
-- owner facts for every set `C`. If `0 ∈ C`, then `supportFunction C x` is nonnegative because the
-- defining supremum contains the value `⟪x, 0⟫ = 0`, and `supportFunction C 0 = 0` because every
-- inner product with `0` vanishes. These are exactly the remaining gauge clauses.
/-- If a set contains the origin, then its support function is a closed gauge. In the source
corollary the set is also assumed closed and convex, but those two hypotheses are redundant for
this owner-side closed-gauge conclusion. -/
theorem supportFunction_isClosedGauge_of_zero_mem
    (h0C : (0 : E) ∈ C) :
    IsClosedGauge (supportFunction C : E → EReal) := sorry

end

section

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {C : Set E}

local notation "γ" C => fun x ↦ (egauge ℝ≥0 C x : EReal)

-- Proof sketch: lower semicontinuity is exactly the upstream owner theorem
-- `egauge_lowerSemicontinuous`, which uses only closedness and convexity. For the remaining gauge
-- fields, `egauge ℝ≥0 C` is nonnegative by definition, positive homogeneity is built into the
-- owner `egauge`, and `γ C 0 = 0` follows from any witness `x ∈ C` because `0 = 0 • x`.
/-- For a nonempty closed convex set in a real topological module, the canonical extended gauge of
`C`, viewed in `EReal`, is a closed gauge. The source corollary's extra hypothesis `0 ∈ C` is
only needed later for the polar-pair identities, not for this owner-side closed-gauge conclusion.
-/
theorem egauge_isClosedGauge_of_isClosedConvex_nonempty
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty) :
    IsClosedGauge (γ C) := sorry

end

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E}

local notation "γ" C => fun x ↦ (egauge ℝ≥0 C x : EReal)

-- Proof sketch: combine Theorem 15.1(3),
-- `gauge_polar_egauge_eq_egauge_polar`, with Theorem 14.5,
-- `egauge_polar_eq_supportFunction`.
/-- Corollary 15.1.2: for a closed convex set `C` containing `0` in a finite-dimensional real
inner-product space, the polar of its gauge `γ(· | C)`, rendered by `γ C`, is the support
function `δ^*(· | C)`, rendered by `supportFunction C`. -/
theorem gauge_polar_egauge_eq_supportFunction_of_isClosedConvexZero
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : E) ∈ C)
    :
    (γ C)ᵒ = (supportFunction C : E → EReal) := sorry

-- Proof sketch: apply Theorem 15.1(3) to `Set.polar C`, then rewrite
-- `Set.polar (Set.polar C) = C` and `egauge ℝ≥0 (Set.polar C)` as `supportFunction C` using
-- Theorem 14.5.
/-- Dually, for a closed convex set `C` containing `0` in a finite-dimensional real inner-product
space, the polar of the support function `δ^*(· | C)` is the gauge `γ(· | C)`, rendered by
`γ C`. -/
theorem gauge_polar_supportFunction_eq_egauge_of_isClosedConvexZero
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : E) ∈ C)
    :
    (supportFunction C : E → EReal)ᵒ = γ C := sorry

end

end
