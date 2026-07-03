import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_26_32 (from Items/Chap26) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

universe u

/- Domain-style sampling for Example 26.32:
- primary domain: Chapter 26 weak SDE solutions together with the Chapter 26 duality owner
  `SatisfiesDualityAt` and the Chapter 17 Q-matrix owner language for the dual particle system;
- sampled owner declarations: `wrightFisherScalarDiffusionCoeff`,
  `GeneralizedWeakSDESolution`, `SatisfiesDualityAt`,
  `localMartingaleProblemWellPosed_of_duality`, and `HasGeneratorMatrix`;
- owner abstractions: the site-migration data is refined to the canonical owner
  `interactingWrightFisherMigrationQMatrix`, whose diagonal is derived from the off-diagonal
  migration rates, while the one-site diffusion owner is reused directly from
  `Example_26_29`; the source-facing monomial is exposed with the textbook notation `x ^ φ`, and
  the fixed-start duality statement is expressed through `SatisfiesDualityAt`;
- primitive source-facing data kept here: the interacting Wright--Fisher migration Q-matrix, the
  dual particle-system generator, and the polynomial duality monomial `x ^ φ`;
- derived API kept here: the complex-valued duality bridge needed by `SatisfiesDualityAt`, the
  dual-process existence bridge, the moment-duality corollary, the
  mixed moments and their recursion for direct `GeneralizedWeakSDESolution` inputs, and the
  weak-existence/uniqueness theorem.

Layer triage:
- source-facing: `interactingWrightFisherMigrationQMatrix`,
  `interactingWrightFisherDualQMatrix`, `exists_interactingWrightFisherDualProcess`,
  `interactingWrightFisherMonomial` together with its notation `x ^ φ`,
  `satisfiesDualityAt_interactingWrightFisherDual`, the mixed-moment identities, and
  Example 26.32 itself;
- core/canonical: `GeneralizedWeakSDESolution`, `SatisfiesDualityAt`,
  `LocalMartingaleProblemWellPosed`, `HasGeneratorMatrix`, and
  `WeakSDESolution.IsWeaklyUnique`;
- bridge/view: the deterministic initial law `Measure.dirac x` inside the canonical owner
  `GeneralizedWeakSDESolution`.
-/

/-- The diagonal diffusion coefficient of the `N`-site interacting Wright--Fisher SDE, obtained
coordinatewise from the canonical one-site Wright--Fisher coefficient. The coordinates are driven
by independent Brownian noises with variances `γ x(i) (1 - x(i))`. -/
def interactingWrightFisherDiffusionCoeff (N : ℕ) (γ : ℝ) :
    NNReal → (Fin N → ℝ) → Fin N → Fin N → ℝ :=
  fun t x i j ↦
    if i = j then wrightFisherScalarDiffusionCoeff γ t (x i) else 0

-- The source semantics treats only the off-diagonal migration rates as primitive; the diagonal is
-- implementation data derived from the zero-row-sum rule.
private def interactingWrightFisherMigrationDiagonal (N : ℕ)
    (r : ∀ i j : Fin N, i ≠ j → NNReal)
    (i : Fin N) : ℝ :=
  -∑ j : Fin N, if h : i = j then (0 : ℝ) else r i j h

/-- The site-migration Q-matrix whose off-diagonal entries are the primitive migration rates and
whose diagonal is derived by the zero-row-sum rule. -/
def interactingWrightFisherMigrationQMatrix (N : ℕ)
    (r : ∀ i j : Fin N, i ≠ j → NNReal) :
    Fin N → Fin N → ℝ :=
  fun i j ↦ if h : i = j then interactingWrightFisherMigrationDiagonal N r i else r i j h

-- Proof sketch: on the finite site space `Fin N`, the off-diagonal entries are exactly the given
-- nonnegative migration rates, and the derived diagonal was defined so that the finite row sum is
-- `0`.
/-- The interacting Wright--Fisher site-migration matrix is a Q-matrix when the off-diagonal
migration rates are given as nonnegative primitive data. -/
theorem interactingWrightFisherMigrationQMatrix_isQMatrix
    (N : ℕ) (r : ∀ i j : Fin N, i ≠ j → NNReal) :
    IsQMatrix (interactingWrightFisherMigrationQMatrix N r) := sorry

/-- The migration drift of the `N`-site interacting Wright--Fisher SDE, written as the action of
the canonical site-migration Q-matrix on the coordinate function. -/
def interactingWrightFisherDriftCoeff (N : ℕ)
    (r : ∀ i j : Fin N, i ≠ j → NNReal) :
    NNReal → (Fin N → ℝ) → Fin N → ℝ :=
  fun _ x i ↦ ∑ j : Fin N, interactingWrightFisherMigrationQMatrix N r i j * x j

/-- Moving one particle from site `i` to site `j` in the dual particle system. When `i = j`, no
state change occurs. -/
def interactingWrightFisherMigrationTarget (N : ℕ) (φ : Fin N → ℕ) (i j : Fin N) :
    Fin N → ℕ :=
  if i = j then φ else Function.update (Function.update φ i (φ i - 1)) j (φ j + 1)

/-- Coalescing one pair at site `i` in the dual particle system removes one particle from that
site. -/
def interactingWrightFisherCoalescenceTarget (N : ℕ) (φ : Fin N → ℕ) (i : Fin N) :
    Fin N → ℕ :=
  Function.update φ i (φ i - 1)

/-- The coalescing migration generator dual to the interacting Wright--Fisher diffusion. A state
`φ` records finitely many ancestral particles at each site. -/
def interactingWrightFisherDualQMatrix (N : ℕ) (γ : ℝ)
    (r : ∀ i j : Fin N, i ≠ j → NNReal) :
    (Fin N → ℕ) → (Fin N → ℕ) → ℝ :=
  fun φ η ↦
    (∑ i : Fin N, ∑ j : Fin N,
      if η = interactingWrightFisherMigrationTarget N φ i j then
        (φ i : ℝ) * interactingWrightFisherMigrationQMatrix N r i j
      else 0) +
      (∑ i : Fin N,
        if η = interactingWrightFisherCoalescenceTarget N φ i then
          γ * (Nat.choose (φ i) 2 : ℝ)
        else 0) +
      if η = φ then
        ∑ i : Fin N, -(γ * (Nat.choose (φ i) 2 : ℝ))
      else 0

/-- The polynomial duality monomial `x^φ = ∏ᵢ x(i)^{φ(i)}`. This is the source-facing owner for
Example 26.32; the complex-valued duality observable used by `SatisfiesDualityAt` is obtained from
it by the canonical coercion `ℝ → ℂ`. -/
def interactingWrightFisherMonomial {N : ℕ} (x : Fin N → ℝ) (φ : Fin N → ℕ) : ℝ :=
  ∏ i : Fin N, x i ^ φ i

scoped infixr:80 " ^ " => interactingWrightFisherMonomial

/-- The canonical complex-valued duality observable is the coerced monomial `x^φ`. -/
theorem interactingWrightFisherMonomial_coe {N : ℕ} (x : Fin N → ℝ) (φ : Fin N → ℕ) :
    ((x ^ φ : ℝ) : ℂ) = ∏ i : Fin N, (x i : ℂ) ^ φ i := by
  simp [interactingWrightFisherMonomial]

-- Proof sketch: every exponent in the zero particle configuration is `0`, so each factor in the
-- finite product is `x i ^ 0 = 1`.
/-- The interacting Wright--Fisher duality monomial at the zero particle configuration is `1`. -/
theorem interactingWrightFisherMonomial_zero (N : ℕ) (x : Fin N → ℝ) :
    (x ^ (0 : Fin N → ℕ)) = 1 := sorry

-- Proof sketch: off the diagonal, the only positive contributions come from particle migrations
-- and pairwise coalescences, both of which have nonnegative rates; on the diagonal, the chosen
-- migration term together with the coalescence losses enforces row sum `0`.
/-- The coalescing migration generator of the interacting Wright--Fisher dual particle system is a
Q-matrix when the off-diagonal migration rates are given as nonnegative primitive data. -/
theorem interactingWrightFisherDualQMatrix_isQMatrix
    (N : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (r : ∀ i j : Fin N, i ≠ j → NNReal) :
    IsQMatrix (interactingWrightFisherDualQMatrix N γ r) := sorry

-- Proof sketch: from an initial particle configuration `φ`, the total particle number
-- `∑ i, φ i` is preserved by migration and decreased by coalescence, so the dual chain stays in
-- the finite set of configurations with total mass at most `∑ i, φ i`. Restrict the Q-matrix to
-- that finite invariant class, apply `exists_markovProcessRealization_of_bounded_qMatrix` there,
-- and then regard the resulting process as `(Fin N → ℕ)`-valued.
/-- For `γ ≥ 0`, the interacting Wright--Fisher coalescing-migration dual admits a continuous-time
Markov realization whose transition semigroup has generator matrix
`interactingWrightFisherDualQMatrix N γ r`. -/
theorem exists_interactingWrightFisherDualProcess
    (N : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (r : ∀ i j : Fin N, i ≠ j → NNReal) :
    ∃ κ : NNReal → Kernel (Fin N → ℕ) (Fin N → ℕ),
      HasGeneratorMatrix κ (interactingWrightFisherDualQMatrix N γ r) ∧
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (Q : (Fin N → ℕ) → ProbabilityMeasure Ω')
          (Y : NNReal → Ω' → (Fin N → ℕ)),
          IsMarkovProcessRealization κ Q Y := sorry

section InteractingWrightFisherWeakSolutions

variable {N : ℕ} {γ : ℝ} {x : Fin N → ℝ}
variable {r : ∀ i j : Fin N, i ≠ j → NNReal}

local notation "IWFWeakSolution" =>
  GeneralizedWeakSDESolution
    (Measure.dirac x)
    (interactingWrightFisherDiffusionCoeff N γ)
    (interactingWrightFisherDriftCoeff N r)

/-- The mixed moment `m^{x,φ}(t) = E_x[X_t^φ]` of an interacting Wright--Fisher weak solution. -/
def interactingWrightFisherMixedMoment
    (L : IWFWeakSolution) (φ : Fin N → ℕ) (t : NNReal) : ℝ :=
  ∫ ω, (L ω t) ^ φ ∂L.μ

-- Proof sketch: identify the polynomial observable with the canonical complex-valued duality
-- function obtained by coercing `x ^ φ` into `ℂ`, use the explicit coalescing-migration generator
-- on `Fin N → ℕ`, and verify the fixed-start duality identity by Itô's formula together with the
-- dual generator computation.
/-- The source-facing interacting Wright--Fisher duality of Example 26.32, expressed through the
fixed-start duality owner `SatisfiesDualityAt`. -/
theorem satisfiesDualityAt_interactingWrightFisherDual
    (L : IWFWeakSolution)
    (hγ : 0 ≤ γ)
    (hx : ∀ i : Fin N, x i ∈ Set.Icc (0 : ℝ) 1)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, ∀ i : Fin N, L ω t i ∈ Set.Icc (0 : ℝ) 1)
    {Ω' : Type u} [MeasurableSpace Ω']
    {κ : NNReal → Kernel (Fin N → ℕ) (Fin N → ℕ)}
    {Q : (Fin N → ℕ) → ProbabilityMeasure Ω'}
    {Y : NNReal → Ω' → (Fin N → ℕ)}
    [IsMarkovProcessRealization κ Q Y]
    (hY_generator : HasGeneratorMatrix κ (interactingWrightFisherDualQMatrix N γ r)) :
    SatisfiesDualityAt L.μ (pathProcess L.X) x Q (fun _ ↦ Y)
      (fun u ψ ↦ ((u ^ ψ : ℝ) : ℂ)) := sorry

-- Proof sketch: this is the real-valued moment form of
-- `satisfiesDualityAt_interactingWrightFisherDual`, obtained by evaluating the coerced monomial at
-- the chosen initial state `x`.
/-- The interacting Wright--Fisher moment duality identity:
`E_x[X_t^φ] = E_φ[x^{Y_t}]`. -/
theorem interactingWrightFisherMixedMoment_eq_dualExpectation
    (L : IWFWeakSolution)
    (hγ : 0 ≤ γ)
    (hx : ∀ i : Fin N, x i ∈ Set.Icc (0 : ℝ) 1)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, ∀ i : Fin N, L ω t i ∈ Set.Icc (0 : ℝ) 1)
    {Ω' : Type u} [MeasurableSpace Ω']
    {κ : NNReal → Kernel (Fin N → ℕ) (Fin N → ℕ)}
    {Q : (Fin N → ℕ) → ProbabilityMeasure Ω'}
    {Y : NNReal → Ω' → (Fin N → ℕ)}
    [IsMarkovProcessRealization κ Q Y]
    (hY_generator : HasGeneratorMatrix κ (interactingWrightFisherDualQMatrix N γ r))
    (φ : Fin N → ℕ) (t : NNReal) :
    interactingWrightFisherMixedMoment L φ t =
      ∫ ω, x ^ (Y t ω) ∂(Q φ) := sorry

-- Proof sketch: for the zero particle configuration the monomial observable is identically `1`,
-- so its expectation under any probability law is also `1`.
/-- The mixed moment corresponding to the zero particle configuration is constantly `1`. -/
theorem interactingWrightFisherMixedMoment_zero (L : IWFWeakSolution) :
    interactingWrightFisherMixedMoment L 0 = fun _ ↦ 1 := sorry

-- Proof sketch: for `γ ≥ 0`, apply Itô's formula to the polynomial observable `x ↦ x^φ`, use
-- the explicit diagonal diffusion and migration drift coefficients, and then take expectations.
-- The resulting terms are exactly the migration and coalescence contributions in formula
-- `(26.33)`.
/-- For `γ ≥ 0`, if an interacting Wright--Fisher weak solution remains in `[0,1]^S`, then its
mixed moments satisfy the linear integral system from formula `(26.33)`. -/
theorem interactingWrightFisherMixedMoment_recursion
    (L : IWFWeakSolution)
    (hγ : 0 ≤ γ)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, ∀ i : Fin N, L ω t i ∈ Set.Icc (0 : ℝ) 1)
    (φ : Fin N → ℕ) (t : NNReal) :
    interactingWrightFisherMixedMoment L φ t =
      x ^ φ +
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          (∑ i : Fin N, ∑ j : Fin N,
            (φ i : ℝ) * interactingWrightFisherMigrationQMatrix N r i j *
              (interactingWrightFisherMixedMoment L
                  (interactingWrightFisherMigrationTarget N φ i j) s.toNNReal -
                interactingWrightFisherMixedMoment L φ s.toNNReal)) +
            γ *
              (∑ i : Fin N,
                (Nat.choose (φ i) 2 : ℝ) *
                  (interactingWrightFisherMixedMoment L
                      (interactingWrightFisherCoalescenceTarget N φ i) s.toNNReal -
                    interactingWrightFisherMixedMoment L φ s.toNNReal)) := sorry

end InteractingWrightFisherWeakSolutions

-- Proof sketch: realize the dual coalescing-migration chain by
-- `exists_interactingWrightFisherDualProcess`, verify
-- `satisfiesDualityAt_interactingWrightFisherDual` for every Dirac initial state in `[0,1]^S`,
-- and then apply the chapter's canonical duality criterion
-- `localMartingaleProblemWellPosed_of_duality`.
/-- Owner-level companion to Example 26.32: for nonnegative off-diagonal migration rates and
`γ ≥ 0`, the interacting Wright--Fisher local martingale problem is well-posed. -/
theorem interactingWrightFisherLocalMartingaleProblemWellPosed
    (N : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (r : ∀ i j : Fin N, i ≠ j → NNReal) :
    LocalMartingaleProblemWellPosed
      (diffusionMatrixOfCoefficient (interactingWrightFisherDiffusionCoeff N γ))
      (interactingWrightFisherDriftCoeff N r) := sorry

-- Proof sketch: combine the owner-level well-posedness theorem
-- `interactingWrightFisherLocalMartingaleProblemWellPosed` with the standard SDE/local-
-- martingale-problem bridge; the dual-process existence enters upstream through
-- `exists_interactingWrightFisherDualProcess`, and one may choose the resulting realization
-- inside the invariant cube `[0,1]^S`.
/-- Example 26.32: for nonnegative off-diagonal migration rates and `γ ≥ 0`, the interacting
Wright--Fisher SDE on `S = {1, ..., N}` started from `x ∈ [0,1]^S` admits a weak solution, and
this solution is unique in law. Moreover, one may choose the realization so that every coordinate
stays in `[0,1]` for all times. -/
theorem exists_interactingWrightFisherWeakSolution_isWeaklyUnique
    (N : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (r : ∀ i j : Fin N, i ≠ j → NNReal) (x : Fin N → ℝ)
    (hx : ∀ i : Fin N, x i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ L :
        GeneralizedWeakSDESolution
          (Measure.dirac x)
          (interactingWrightFisherDiffusionCoeff N γ)
          (interactingWrightFisherDriftCoeff N r),
      L.IsWeaklyUnique ∧
        ∀ ω : L.Ω, ∀ t : NNReal, ∀ i : Fin N, L ω t i ∈ Set.Icc (0 : ℝ) 1 := sorry

end ProbabilityTheory
