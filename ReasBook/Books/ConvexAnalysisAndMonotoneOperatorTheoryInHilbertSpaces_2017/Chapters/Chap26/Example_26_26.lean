import Mathlib
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap26.Proposition_26_25

open Filter
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Example 26.26 is the projected recursion
  `x_(n+1) = P_C (x_n - β B x_n)` and its convergence to a solution of the variational
  inequality over `C`.
- `core/canonical`: the Chapter 26 owner remains
  `variationalInequalityProblem (ι[C]) B.toSetValuedOperator`, together with
  `proximalForwardBackwardIteration` from Proposition 26.25.
- `bridge/view`: the only file-local data owner is the projected recursion itself; the solution
  set should reuse the canonical Chapter 26 owner rather than a duplicate local wrapper.

Semantic recall: `lean_leansearch` returned only generic weak-topology / coercivity hits for this
item, so the source-facing specialization below is built from the verified local owners
`indicator_mem_gammaZero_of_nonempty_isClosed_convex` and
`proximalForwardBackwardIteration`, with the classical set-theoretic reformulation already owned by
Example 26.21. -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (B : H → H)

local notation "VI" => variationalInequalityProblem (ι[C]) B.toSetValuedOperator
local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
local notation "P" => projectionPoint C hC_cheb

omit [CompleteSpace H] in
/-- Helper for Example 26.26: the indicator of a nonempty closed convex set belongs to `Γ₀(H)`.
This local helper avoids the current import collision through `Corollary_12_31`. -/
private theorem indicatorMemGammaZeroOfNonemptyIsClosedConvex :
    C.Nonempty → IsClosed C → Convex ℝ C → ι[C] ∈ Γ₀(H) := by
  intro hC_nonempty hC_closed hC_convex
  -- Route correction: reprove the Chapter 12 `Γ₀` fact locally instead of importing the
  -- conflicting wrapper file.
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    simpa [indicator_apply] using
      (hC_closed.isOpen_compl.lowerSemicontinuous_indicator (y := (⊤ : EReal))
        (by simp : (0 : EReal) ≤ ⊤))
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  -- Convexity of `C` gives the domain membership needed to keep the indicator finite.
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

local notation "hIndicator" =>
  indicatorMemGammaZeroOfNonemptyIsClosedConvex
    (H := H) (C := C) hC_nonempty hC_closed hC_convex

/-- The projected iteration `x_(n+1) = P_C (x_n - β B x_n)` attached to the constraint set `C`
and the single-valued operator `B`. -/
def projectedCocoerciveIteration (beta : PosReal) (x0 : H) : ℕ → H
  | 0 => x0
  | n + 1 =>
      let xn := projectedCocoerciveIteration beta x0 n
      P (xn - (beta : ℝ) • B xn)

/-- Helper for Example 26.26: the scaled proximal operator of the indicator of `C` is the metric
projection onto `C`. -/
private theorem scaledIndicatorProx_eq_projectionPoint
    (beta : PosReal) :
    Prox[beta, ι[C], hIndicator] = P := by
  let hindicator : ι[C] ∈ Γ₀(H) := hIndicator
  have hsmul_indicator : beta • ι[C] = ι[C] := by
    -- Scaling the indicator by a positive real leaves its values unchanged.
    funext y
    apply Subtype.ext
    by_cases hy : y ∈ C
    · simp [ERealFunction.indicator, hy]
    · simpa [ERealFunction.indicator, hy] using
        (EReal.coe_mul_top_of_pos beta.2 : ((beta : ℝ) : EReal) * ⊤ = ⊤)
  -- Rewrite the scaled proximity operator to the ordinary indicator proximity operator.
  change Prox[beta • ι[C], smul_mem_gammaZero (ι[C]) hindicator beta] = P
  ext y
  simpa [hsmul_indicator] using
    congrArg (fun f : H → H ↦ f y) <|
      proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex

/-- Helper for Example 26.26: at `γ = β`, the forward-backward relaxation bound is `3 / 2`. -/
private theorem forwardBackwardRelaxationBound_self (beta : PosReal) :
    SetValuedOperator.forwardBackwardRelaxationBound beta beta = (3 / 2 : ℝ) := by
  -- This is the textbook constant `2 - β / (2β) = 3 / 2`.
  dsimp [SetValuedOperator.forwardBackwardRelaxationBound]
  field_simp [beta.2.ne']
  ring

/-- Helper for Example 26.26: the constant relaxation sequence `λₙ = 1` satisfies the
divergence condition in Proposition 26.25 at `γ = β`. -/
private theorem constantOneForwardBackwardDiverges_self (beta : PosReal) :
    Tendsto
      (fun N ↦
        Finset.sum (Finset.range N)
          (fun _ ↦
            (1 : ℝ) *
              (SetValuedOperator.forwardBackwardRelaxationBound beta beta - 1)))
      atTop atTop := by
  have hconst_pos :
      0 < (1 : ℝ) * (SetValuedOperator.forwardBackwardRelaxationBound beta beta - 1) := by
    rw [forwardBackwardRelaxationBound_self (beta := beta)]
    norm_num
  -- A positive constant summand gives partial sums proportional to `N`.
  convert Tendsto.const_mul_atTop hconst_pos tendsto_natCast_atTop_atTop using 1
  ext N
  simp [forwardBackwardRelaxationBound_self (beta := beta)]
  ring

/-- The projected recursion `x_(n+1) = P_C (x_n - β B x_n)` is the specialization of the
proximal forward-backward iteration to `f = ι[C]` and `λ_n = 1`. -/
theorem projectedCocoerciveIteration_eq_proximalForwardBackwardIteration
    (beta : PosReal) (x0 : H) :
    projectedCocoerciveIteration hC_nonempty hC_closed hC_convex B beta x0 =
      proximalForwardBackwardIteration hIndicator B beta (fun _ ↦ 1) x0 := by
  funext n
  induction n with
  | zero =>
      -- Both recursions start from the prescribed initial point `x0`.
      simp [projectedCocoerciveIteration, proximalForwardBackwardIteration]
  | succ n ih =>
      -- One step of the proximal recursion collapses to the projection step when `λₙ = 1`.
      rw [projectedCocoerciveIteration, proximalForwardBackwardIteration, ih]
      rw [scaledIndicatorProx_eq_projectionPoint
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
        (beta := beta)]
      simp only [one_smul]
      abel_nf

/-- Example 26.26: let `C` be a nonempty closed convex subset of a real Hilbert space, let
`β ∈ ℝ_{++}`, and let `B : H → H` be `β`-cocoercive. If the variational inequality
`find x ∈ C such that ∀ y ∈ C, ⟪x - y, B x⟫ ≤ 0` has a solution and
`x_(n+1) = P_C (x_n - β B x_n)`, then `(x_n)` converges weakly to a solution `x` and
`(B x_n)` converges strongly to `B x`. -/
theorem projectedCocoerciveIteration_tendsto_to_variationalInequalitySolution
    (beta : PosReal)
    (hB : CocoerciveOn (beta : ℝ) (Set.univ : Set H) (fun x ↦ B x))
    (hsol : Set.Nonempty VI)
    (x0 : H) :
    ∃ x ∈ VI,
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (projectedCocoerciveIteration hC_nonempty hC_closed hC_convex B beta x0 n))
        atTop (𝓝 (toWeakSpace ℝ H x)) ∧
        Tendsto
          (fun n ↦ B (projectedCocoerciveIteration hC_nonempty hC_closed hC_convex B beta x0 n))
          atTop (𝓝 (B x)) := by
  let hindicator : ι[C] ∈ Γ₀(H) := hIndicator
  have hgamma : (beta : ℝ) < 2 * (beta : ℝ) := by
    nlinarith [beta.2]
  have hlam :
      ∀ n : ℕ,
        (1 : ℝ) ∈
          Set.Icc (0 : ℝ) (SetValuedOperator.forwardBackwardRelaxationBound beta beta) := by
    intro (_n : ℕ)
    rw [forwardBackwardRelaxationBound_self (beta := beta)]
    norm_num
  obtain ⟨x, hxVI, hxweak⟩ :=
    proximalForwardBackward_tendsto_weakly_to_variationalInequalitySolution
      (hf := hindicator) (B := B) beta beta (by simpa using hB) hgamma
      (fun _ ↦ 1) hlam (constantOneForwardBackwardDiverges_self (beta := beta)) hsol x0
  have hstrong :
      Tendsto (fun n ↦ B (proximalForwardBackwardIteration hindicator B beta (fun _ ↦ 1) x0 n))
        atTop (𝓝 (B x)) :=
    proximalForwardBackward_B_tendsto_of_mem_variationalInequalityProblem
      (hf := hindicator) (B := B) beta beta (by simpa using hB) hgamma
      (fun _ ↦ 1) hlam (constantOneForwardBackwardDiverges_self (beta := beta)) x0 hxVI
  refine ⟨x, hxVI, ?_⟩
  -- Transport both convergence clauses across the recursion identification theorem.
  constructor
  · simpa [projectedCocoerciveIteration_eq_proximalForwardBackwardIteration
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
      (B := B) (beta := beta) (x0 := x0)] using hxweak
  · simpa [projectedCocoerciveIteration_eq_proximalForwardBackwardIteration
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
      (B := B) (beta := beta) (x0 := x0)] using hstrong

end

end

end ERealFunction
