import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_9_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_7
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Rockafellar

section

variable {𝕜 : Type*} {E : Type u}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

local notation "P" => 𝕜 × E

/-!
Source/core/bridge triage:

- primary mathematical domain: closed perspectives and their support-function duality for
  closed proper convex `WithTopBot 𝕜`-valued functions;
- `source-facing`: Corollary 13.5.1 identifies the support function of the set
  `{(λ⋆, x⋆) | λ⋆ ≤ -f*(x⋆)}` with the closed perspective of `f`, whose positive
  slices are the right scalar multiples `f_λ`, whose boundary value at `λ = 0` is
  `f0⁺`, and whose negative half-space values are `+∞`.
- `core/canonical`: the owner declarations already present in the project are
  `Function.IsClosedProperConvex`, `convexConjugate`, `rightScalarMul`,
  `recessionFunction`, `lowerSemicontinuousHull`, and the raw perspective owner `perspective f`
  from Text 5.4.9.1, together with the Chapter 9 closure owner theorem
  `Function.lowerSemicontinuousHull_sublinearHull_eq_sInf_insert_recessionFunction`.
- `bridge/view`: the textbook three-branch formula is recorded directly on the source product
  space `𝕜 × E`, with no extra coordinate-transport wrapper.

Domain-style sampling used here:
- `perspective`;
- `rightScalarMul`;
- `Function.recessionFunction`;
- `Function.lowerSemicontinuousHull_sublinearHull_eq_sInf_insert_recessionFunction`.

Best owner abstraction:
- the Chapter 1 owner `perspective`, with the Chapter 9 closure formula supplying the canonical
  closed-hull computation.

Primitive data vs derived API:
- primitive input: a function `f : E → WithTopBot 𝕜`;
- primitive theorem-layer hypothesis: the chapter owner `hf : f.IsClosedProperConvex`;
- derived API: the pointwise three-branch formula for `cl(perspective f)`, stated directly on the
  intrinsic product space `𝕜 × E`.
- later bridge API in the finite-dimensional pairing section below: the support-function
  formula of the corollary.
-/

variable (f : E → WithTopBot 𝕜)

-- Proof sketch: let `h(λ, x) = f x` on the affine slice `λ = 1` and `h(λ, x) = +∞`
-- elsewhere, so
-- `perspective f = sublinearHull h` by the owner definition from Text 5.4.9.1. Applying the
-- Chapter 9 owner theorem
-- `Function.lowerSemicontinuousHull_sublinearHull_eq_sInf_insert_recessionFunction`
-- to that slice owner identifies `cl(perspective f)` with the infimum of the positive right
-- scalar multiples of `h` together with its recession value. Evaluating those two owner terms on
-- `𝕜 × E` gives exactly the positive branch
-- `((⟨p.1, le_of_lt h⟩ : Set.Ici (0 : 𝕜)) •ʳ f) p.2`, the boundary branch
-- `f0⁺ p.2`, and the negative branch `+∞`. This uses the closed proper convex owner hypothesis
-- `hf : f.IsClosedProperConvex`, since the closure formula and the `λ = 0` recession
-- identification are not valid for arbitrary `WithTopBot 𝕜`-valued functions.
/-- For closed proper convex `f`, the closed perspective owner on `𝕜 × E` has the textbook
three-branch formula from Corollary 13.5.1. -/
theorem lowerSemicontinuousHull_perspective_apply
    (hf : f.IsClosedProperConvex)
    (p : P) :
    cl(perspective f) p =
      if h : 0 < p.1 then
        ((⟨p.1, le_of_lt h⟩ : Set.Ici (0 : 𝕜)) •ʳ f) p.2
      else if p.1 = 0 then
        f0⁺ p.2
      else
        ⊤ := by
  -- This is the perspective specialization of the Chapter 9 closure formula
  -- for `cl (sublinearHull ·)`.
  sorry

end

section

variable {𝕜 : Type*} {E : Type u} {Y : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]

local instance : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

local instance : HasPairing E Y 𝕜 := instHasPairingOfHasLinearPairing
local instance : HasPairing 𝕜 𝕜 (WithTopBot 𝕜) := instHasPairingWithBotTop
local instance : HasPairing E Y (WithTopBot 𝕜) := instHasPairingWithBotTop

local notation "P" => 𝕜 × E
local notation "P⋆" => 𝕜 × Y

/-
Source/core/bridge triage for the support-function clause:

- primary mathematical domain: the support-function duality of closed perspectives;
- `source-facing`: Corollary 13.5.1 identifies the support function of
  `{(λ⋆, x⋆) | λ⋆ ≤ -f*(x⋆)}` with the closed perspective `cl(perspective f)`.
- `core/canonical`: the owner theorem is
  `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`
  from `Theorem_13_5`, applied to the slice function `h(1, x) = f x`, `h(λ, x) = +∞` for
  `λ ≠ 1` whose generated function is `perspective f`.
- `bridge/view`: the corollary rewrites the generic owner-side nonpositive sublevel set
  `{p | h⋆ p ≤ 0}` into the textbook source-facing hypograph
  `{(λ⋆, x⋆) | λ⋆ ≤ -f*(x⋆)}` on the intrinsic primal/dual product spaces
  `P = 𝕜 × E` and `P⋆ = 𝕜 × Y`.

Primitive data vs derived API:
- primitive source-facing input: a proper convex function
  `f : E → WithTopBot 𝕜`;
- core owner reused here: the Chapter 13 theorem for `cl(sublinearHull h)` applied to the
  perspective slice owner `h(1, x) = f x`, `h(λ, x) = +∞` for `λ ≠ 1`;
- derived bridge API: the explicit source-facing hypograph set
  `{(λ⋆, x⋆) | λ⋆ ≤ -f*(x⋆)}` on `P⋆`.

Layer target: `bridge/view`; this file keeps Rockafellar's explicit product-space support set while
reusing the Chapter 13 support-function owner theorem rather than introducing a parallel local
support-function wrapper for the perspective.

Domain-style sampling used here:
- `supportFunction`;
- `perspective`;
- `convexConjugate`;
- `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`.

Best owner abstraction:
- the Chapter 13 support-function theorem applied to the perspective slice owner, with this file
  keeping only the source-facing hypograph rewrite as a bridge.
-/

variable (f : E → WithTopBot 𝕜)

-- Proof sketch: apply the owner theorem
-- `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`
-- to the same slice owner `h(1, x) = f x`, `h(λ, x) = +∞` for `λ ≠ 1`, then rewrite
-- `sublinearHull h` as `perspective f`. The support set coming from that owner theorem is
-- `{p | h⋆ p ≤ 0}`. Computing the conjugate of the slice owner gives
-- `h*(λ⋆, x⋆) = λ⋆ + convexConjugate f x⋆`, so this owner-side set is exactly
-- the source-facing hypograph set `{(λ⋆, x⋆) | λ⋆ ≤ -f*(x⋆)}`.
/-
Corollary 13.5.1 in pairing-owner form: for a proper convex function
`f : E → WithTopBot 𝕜` on a finite-dimensional module `E` over an ordered field `𝕜`, with a
continuous linear pairing against `Y`, the closed perspective on `P = 𝕜 × E` is the support
function of the source-facing hypograph set
`{(λ⋆, x⋆) | λ⋆ ≤ -f*(x⋆)}` on `P⋆ = 𝕜 × Y`.
On the scalar coordinate, the pairing is the canonical multiplication pairing
`⟪a, b⟫ₚ = a * b`.
-/
theorem lowerSemicontinuousHull_perspective_eq_supportFunction_hypograph_neg_convexConjugate
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    cl(perspective f) =
      (δᵛ(· |
          ({p : P⋆ | (p.1 : WithTopBot 𝕜) ≤ -(f⋆ p.2)} : Set P⋆)) : P → WithTopBot 𝕜) := by
  -- Apply the Chapter 13 owner theorem to the perspective slice and rewrite its
  -- nonpositive conjugate sublevel as the desired hypograph.
  sorry

end
