import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} {EStar : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup EStar] [NormedSpace ℝ EStar]
variable [HasPairing E EStar ℝ]
variable {f : E → WithBotTop ℝ}
variable (J : E →ₗ[ℝ] EStar)

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))
local notation "fStar" => (f⋆ : EStar → WithBotTop ℝ)
local notation "wStar" =>
  (fun zStar : EStar ↦ (((1 / 2 : ℝ) * ‖zStar‖ ^ 2 : ℝ) : WithBotTop ℝ))
local notation "primalEnvelope" => (f □ w : E → WithBotTop ℝ)
local notation "dualEnvelope" => (fStar □ wStar : EStar → WithBotTop ℝ)
local notation "dualEnvelopeOnPrimal" =>
  (fun z : E ↦ dualEnvelope (J z))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 31.5 is Moreau's identity for a closed proper convex function together
  with finiteness/unique-attainment of the two quadratic infimal convolutions and the optimality
  characterization of the primal/dual minimizing pair.
- `core/canonical`: the source owner layer here is pairing-first, on a primal/dual ambient
  `(E, EStar)` with explicit bridge map `J : E →ₗ[ℝ] EStar`; the canonical owners are infimal
  convolution `□`, Fenchel conjugation `f⋆`, `Function.IsClosedProperConvex`, and intrinsic
  subdifferentials `∂[EStar]f(x)`.
- `bridge/view`: the self-dual Hilbert-space formulas (`toDualMap`, `∂ᵥ`, gradients) are stated
  below as Euclidean bridge theorems; they are not the root owner layer for this item.

Domain-style sampling used here:
- `convexConjugate` / `f⋆` from `Chap03.Defn_12_2`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `_root_.subdifferentialAt` and the notation `∂ f at x` from `Chap05.Definition_23_0_6`;
- `Function.subdifferentialAt` / `∂ᵥf(x)` from the same file, used only in the bridge section.

Primitive data vs derived API:
- primitive input: a closed proper convex function `f`, represented by
  `hf : f.IsClosedProperConvex`;
- primitive primal/dual kernels:
  `w(z) = (1 / 2) ‖z‖²` on `E` and `wStar(zStar) = (1 / 2) ‖zStar‖²` on `EStar`;
- primitive bridge data: the explicit map `J : E →ₗ[ℝ] EStar`, which is mathematically essential
  because `EStar` is not recoverable from `E` in the pairing-level owner;
- derived API: Moreau identity along `J`, finiteness of both envelope values, existence/uniqueness
  of primal and dual minimizers, and intrinsic-dual optimality characterization.

Layer targets in this file:
- `source-facing` / `core-canonical`: pairing-level declarations below, with explicit `EStar` and
  `J`;
- `bridge/view`: Euclidean self-dual/gradient declarations in the final section.

Scalar note:
- the quadratic kernels are norm-squared and therefore intrinsically `ℝ`-valued, so this item
  stays on the real scalar branch and keeps norm-compatible scalar structure (`NormedSpace`) even
  when the owner is lifted away from `InnerProductSpace`.
-/

-- Proof sketch: combine the Fenchel conjugacy identity for a sum with the self-conjugacy of the
-- quadratic kernels on the primal and dual spaces, then evaluate the dual envelope along the
-- explicit bridge `J`.
/-- Theorem 31.5, pairing-owner form: for a closed proper convex function `f` and an explicit
primal-to-dual bridge `J : E →ₗ[ℝ] EStar`, the primal quadratic Moreau envelope of `f` and the
dual quadratic Moreau envelope of `f⋆`, read along `J`, add up pointwise to `w`. -/
theorem moreau_identity (hf : IsClosedProperConvex[ℝ] f) :
    (primalEnvelope + dualEnvelopeOnPrimal : E → WithBotTop ℝ) = w := sorry

-- Proof sketch: once Moreau's identity identifies `primalEnvelope z + dualEnvelope (J z)`
-- with the finite real value `w z`, the primal term cannot be `⊥` or `⊤`.
/-- The primal quadratic infimal convolution `f □ w` is finite at every point. -/
theorem primal_moreau_envelope_finite
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ⊥ < primalEnvelope z ∧ primalEnvelope z < ⊤ := sorry

-- Proof sketch: apply the same finite-value argument to the conjugate side, evaluated at the
-- dual point `J z`.
/-- The intrinsic dual quadratic infimal convolution of `f⋆` is finite along `J`. -/
theorem dual_moreau_envelope_finite
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ⊥ < dualEnvelope (J z) ∧ dualEnvelope (J z) < ⊤ := sorry

section CompleteSpace

variable [CompleteSpace E] [CompleteSpace EStar]

-- Proof sketch: the quadratic perturbation by `w(z - x)` makes the primal objective strictly
-- convex and coercive on the finite branch, so the infimum defining `(f □ w) z` is attained at a
-- unique point.
/-- For each `z`, the primal infimum defining `(f □ w) z` is attained at a unique minimizer. -/
theorem existsUnique_primal_moreau_minimizer
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ∃! x : E, IsMinOn (fun x : E ↦ f x + w (z - x)) Set.univ x := sorry

-- Proof sketch: the dual Moreau objective lives on the complete dual owner `EStar`,
-- and the dual value is read at the embedded point `J z`.
/-- For each `z`, the dual infimum defining the intrinsic dual Moreau envelope of `f⋆` at
`J z` is attained at a unique minimizer. -/
theorem existsUnique_dual_moreau_minimizer
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ∃! xStar : EStar,
      IsMinOn
        (fun yStar : EStar ↦ fStar yStar + wStar (J z - yStar))
        Set.univ xStar := sorry

-- Proof sketch: the optimality conditions for the two quadratic perturbation problems are the
-- Fenchel-Young subgradient relations for `f` and `f⋆`, linked through the explicit bridge `J`.
-- Eliminating the conjugate-side condition yields the residual identity
-- `xStar = J (z - x)` and intrinsic subgradient membership `xStar ∈ ∂[EStar]f(x)`.
/-- A primal minimizer `x` and an intrinsic dual minimizer `xStar` for the two Moreau envelopes at
the same primal point `z` are characterized exactly by the residual-dual relation
`xStar = J (z - x)` and the intrinsic subgradient condition `xStar ∈ ∂[EStar]f(x)`. -/
theorem primal_and_dual_moreau_minimizers_iff
    (hf : IsClosedProperConvex[ℝ] f) (z x : E) (xStar : EStar) :
    (IsMinOn (fun y : E ↦ f y + w (z - y)) Set.univ x ∧
        IsMinOn
          (fun yStar : EStar ↦ fStar yStar + wStar (J z - yStar))
          Set.univ xStar) ↔
      xStar = J (z - x) ∧ xStar ∈ (∂[EStar]f(x)) := sorry

end CompleteSpace
end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → WithBotTop ℝ}

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))
local notation "toDualMap" => (InnerProductSpace.toDualMap ℝ E)

local notation "fStarVec" => (f⋆ : E → WithBotTop ℝ)
local notation "primalEnvelope" => (f □ w : E → WithBotTop ℝ)
local notation "dualEnvelopeVec" => (fStarVec □ w : E → WithBotTop ℝ)
local notation "primalEnvelopeReal" => (Function.realBranch primalEnvelope : E → ℝ)
local notation "dualEnvelopeVecReal" => (Function.realBranch dualEnvelopeVec : E → ℝ)

section CompleteSpace

variable [CompleteSpace E]

-- Proof sketch: transport the intrinsic dual minimizer theorem through the Fréchet-Riesz
-- map `toDualMap` and rewrite the intrinsic subgradient condition using
-- the vector-valued bridge owner `∂ᵥ`.
/-- Euclidean bridge form of Theorem 31.5: a primal minimizer `x` and a dual vector minimizer
`xStar` for the two self-dual Hilbert-space Moreau envelopes at `z` are characterized by
`z = x + xStar` and `xStar ∈ ∂ᵥf(x)`. -/
theorem primal_and_dual_moreau_minimizers_iff_euclidean
    (hf : IsClosedProperConvex[ℝ] f) (z x xStar : E) :
    (IsMinOn (fun y : E ↦ f y + w (z - y)) Set.univ x ∧
        IsMinOn (fun yStar : E ↦ fStarVec yStar + w (z - yStar)) Set.univ xStar) ↔
      z = x + xStar ∧ xStar ∈ ∂ᵥf(x) := sorry

-- Proof sketch: the finite real branch `dualEnvelopeVec.realBranch` is differentiable at every
-- point of the ambient space, and the unique primal minimizer from Theorem 31.5 is the gradient
-- vector given by that differentiability statement.
/-- The finite real branch `((f⋆ □ w).realBranch)` has a gradient at every point. -/
theorem hasGradientAt_dual_moreau_envelope
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    HasGradientAt dualEnvelopeVecReal (∇ dualEnvelopeVecReal z) z := sorry

-- Proof sketch: the same differentiability statement holds for the primal Moreau envelope
-- `primalEnvelope.realBranch`, with gradient linked to the intrinsic dual minimizer through
-- `toDualMap`.
/-- The finite real branch `((f □ w).realBranch)` has a gradient at every point. -/
theorem hasGradientAt_primal_moreau_envelope
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    HasGradientAt primalEnvelopeReal (∇ primalEnvelopeReal z) z := sorry

-- Proof sketch: combine the previous `HasGradientAt` theorem for `dualEnvelopeVec.realBranch`
-- with the Moreau-Yosida differentiability description to identify its gradient vector with the
-- unique primal minimizer.
/-- The gradient of `((f⋆ □ w).realBranch)` is the unique primal minimizer in Moreau's theorem. -/
theorem gradient_dual_moreau_envelope_is_primal_minimizer
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    IsMinOn (fun x : E ↦ f x + w (z - x)) Set.univ
      (∇ dualEnvelopeVecReal z) := sorry

-- Proof sketch: the gradient of the primal envelope branch `primalEnvelope.realBranch` is the
-- unique self-dual Hilbert-space dual minimizer, obtained from the intrinsic dual minimizer
-- through the Fréchet-Riesz bridge map.
/-- The gradient of `((f □ w).realBranch)` is the unique Euclidean dual minimizer in Moreau's
theorem. -/
theorem gradient_primal_moreau_envelope_is_dual_minimizer
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    IsMinOn (fun xStar : E ↦ fStarVec xStar + w (z - xStar)) Set.univ
      (∇ primalEnvelopeReal z) := sorry

end CompleteSpace
end
