import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_13_5_1 (from Chap03) -/
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

/-! ### Text_13_5_2 (from Chap03) -/
noncomputable section

section

open Matrix
open LinearMap.BilinMap
open scoped RealInnerProductSpace Rockafellar

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
variable (Q : Matrix (Fin n) (Fin n) ℝ) (a : E) (α : ℝ)

set_option quotPrecheck false in
local notation "q" => ((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ Q.toEuclideanLin))
set_option quotPrecheck false in
local notation "qInv" => ((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ (Q⁻¹).toEuclideanLin))
set_option quotPrecheck false in
local notation "C" => {x : E | q x + ⟪a, x⟫ + α ≤ 0}
set_option quotPrecheck false in
local notation "b" => -((Q⁻¹).toEuclideanLin a)
local notation "β" => qInv a - α

/-!
Source/core/bridge triage:

- `source-facing`: Text 13.5.2 studies the concrete elliptic sublevel set
  `C = {x | (1/2) ⟪x, Qx⟫ + ⟪a, x⟫ + α ≤ 0}` and computes its support function explicitly.
- `core/canonical`: the ambient owners are
  `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`,
  the affine-change owner `convexConjugate_affineChange`, the project support function
  `supportFunction`, the canonical quadratic-form owner
  `LinearMap.BilinMap.toQuadraticMap`, the matrix bridge theorem
  `convexConjugate_matrixQuadraticMap_eq_inverse`, the matrix positivity notion `Matrix.PosDef`,
  and the Euclidean linear action `Matrix.toEuclideanLin`.
- `bridge/view`: the final statement keeps the source-facing sublevel set
  `δᵛ(xStar | C)`.

Domain-style sampling used here:
- `lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate`;
- `supportFunction`;
- `convexConjugate_affineChange`;
- `LinearMap.BilinMap.toQuadraticMap`;
- `convexConjugate_matrixQuadraticMap_eq_inverse`;
- `Matrix.toEuclideanLin`.

Primitive data vs derived API:
- the primitive source-facing datum is the explicit elliptic sublevel-set defining
  inequality, written locally as `C` and expressed directly from the canonical operator quadratic
  owner `LinearMap.BilinMap.toQuadraticMap`;
- the derived API is the explicit support-function formula, obtained by specializing the owner
  nonpositive-sublevel support-function theorem to an affine quadratic and then rewriting the
  conjugate data in inverse-matrix form, without introducing a second wrapper for quadratic
  sublevel sets.

Layer target: `bridge/view`, keeping the concrete textbook set while expressing its support
function through the chapter's canonical support-function and conjugation owners.
-/

-- Proof sketch: apply Theorem 13.5 to the finite convex quadratic
-- `x ↦ q x + ⟪a, x⟫ + α`,
-- whose conjugate is the inverse
-- quadratic with linear term `b = -(Q⁻¹ a)` and constant term
-- `β = qInv a - α`. The
-- nonemptiness hypothesis gives `β ≥ 0`, so the closed positively homogeneous hull is obtained by
-- minimizing `(1 / (2 * λ)) ⟨xStar, Q⁻¹ xStar⟩ + ⟨b, xStar⟩ + λ β` over `λ > 0`, which yields the
-- displayed affine-plus-square-root expression.
/-- Text 13.5.2: if `C = {x | q x + ⟪a, x⟫ + α ≤ 0}`, i.e.
`C = {x | (1 / 2) ⟪x, Qx⟫ + ⟪a, x⟫ + α ≤ 0}`, with `Q` positive definite and `C` nonempty, then
the support function of `C` is the affine-plus-square-root expression obtained from `Q⁻¹`. -/
theorem supportFunction_ellipticSublevelSet_eq
    (xStar : E) (hQ : Q.PosDef) (hC : Set.Nonempty C) :
    δᵛ(xStar | C) =
      (⟪b, xStar⟫ +
          Real.sqrt (2 * β * ⟪xStar, (Q⁻¹).toEuclideanLin xStar⟫) :
        EReal) :=
  sorry

end

/-! ### Theorem_13_5 (from Chap03) -/
noncomputable section

universe u v

open scoped Rockafellar
open Function

section

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasContinuousPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 13.5 identifies two support functions coming from the zero sublevel
  sets of a closed proper convex function and of its conjugate with the closures of the positively
  homogeneous convex functions generated by `f*` and `f`, respectively.
- `core/canonical`: the owner abstractions already present in the project are `supportFunction`,
  `convexConjugate`, `lowerSemicontinuousHull`, `Function.sublinearHull`,
  `Function.IsClosedProperConvex`, and the dual owner lemmas
  `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`,
  `convexConjugate_lowerSemicontinuousHull_eq`,
  `nonpositiveSublevel_convexConjugate_eq_setOf_forall_pairing_le`.
- `bridge/view`: the theorem surface uses the chapter notation `δᵛ(· | ·)` and `cl(·)` for the
  support-function and lower-semicontinuous-hull owners, while the sets
  `{x | f(x) ≤ 0}` and `{x⋆ | f*(x⋆) ≤ 0}` are kept directly as zero sublevel sets of `f` and
  `convexConjugate f`.

Domain-style sampling used here:
- `supportFunction` from Defintion 4.8.2;
- `Function.sublinearHull` from Text 5.4.7;
- `lowerSemicontinuousHull_eq_supportFunction_setOf_forall_pairing_le` and
  `nonpositiveSublevel_convexConjugate_eq_setOf_forall_pairing_le` from Corollary 13.2.1;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` from Theorem 12.2.

Primitive data vs derived API:
- primitive input for clause `(2)`: a proper convex function
  `f : X → WithBotTop 𝕜` on a finite-dimensional module `X` over `𝕜` with a continuous linear
  pairing to `Y`, given through the owner predicates `f.IsConvex 𝕜` and `f.IsProper`;
- derived API: clause `(2)`, the source-facing identity for the generated function of `f`, and
  clause `(1)`, its dual companion for `f⋆`, obtained by combining clause `(2)` with the closed
  proper convex owner theorems for Fenchel conjugation and biconjugacy on the self-pairing layer.

Layer target: `source-facing`, stated directly with the canonical project owners rather than by
introducing a wrapper for the generated functions or a local alias for the zero sublevel sets.
-/

variable (f : X → WithBotTop 𝕜)

-- Proof sketch: apply Corollary 13.2.1 directly to the positively homogeneous convex function
-- generated by `f`, and rewrite the resulting support set with
-- `nonpositiveSublevel_convexConjugate_eq_setOf_forall_pairing_le`.
/-- Theorem 13.5 (2): for a proper convex function `f` on a finite-dimensional module with a
continuous linear pairing, the closure of the generated function, written on the theorem surface as
`cl(sublinearHull f)`, is the support function of the zero sublevel set
`{x⋆ | f*(x⋆) ≤ 0}`. Closedness is not part of this clause because the left-hand side is already a
closure. -/
theorem lowerSemicontinuousHull_generatedBy_eq_supportFunction_nonpositiveSublevel_convexConjugate
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    :
    cl(sublinearHull f) =
      (δᵛ(· | {yStar : Y | f⋆ yStar ≤ 0}) : X → WithBotTop 𝕜) := sorry

end

section

variable {𝕜 : Type*} {E : Type u}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

variable (f : E → WithBotTop 𝕜)

-- Proof sketch: apply clause (2) to `f⋆`. The closed-proper-convex owner API supplies the same
-- hypothesis for `f⋆`, and closed-convex biconjugacy rewrites the resulting nonpositive sublevel
-- set `{x | f⋆⋆ x ≤ 0}` to `{x | f x ≤ 0}`.
/-- Theorem 13.5 (1): for a closed proper convex function `f` on a finite-dimensional module with
a continuous linear self-pairing, the support function of the zero sublevel set
`{x | f x ≤ 0}` is the closure of the generated function of `f⋆`, written on
the theorem surface as `cl(sublinearHull f⋆)`. -/
theorem supportFunction_nonpositiveSublevel_eq_lowerSemicontinuousHull_generatedBy_convexConjugate
    (hf : IsClosedProperConvex[𝕜] f)
    :
    (δᵛ(· | {x : E | f x ≤ 0}) : E → WithBotTop 𝕜) = cl(sublinearHull f⋆) := sorry

end
