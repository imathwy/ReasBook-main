import BauschkeLean.Chap06.Proposition_6_44
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap13.Example_13_43
import BauschkeLean.Chap24.Proposition_24_19
import BauschkeLean.Chap28.Proposition_28_16

open Filter
open scoped InnerProductSpace Pointwise Topology

noncomputable section

universe u v

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Example 28.17 is the cone-constrained specialization of the primal-dual
  forward-backward recursion `(28.67)` for a positively homogeneous penalty.
- `core/canonical`: Proposition 28.16 already provides the stable primal-dual owner on `Argmin`,
  `Prox`, and weak convergence in `WeakSpace ℝ`.
- `bridge/view`: this file keeps the explicit cone projection `P_K`, the dual projector
  `P_(∂ ψ 0)`, and the textbook dual objective from Example 19.8, while the later proof can pass
  through the Proposition 28.16 orbit by rewriting `Prox_(γ ψ*)` as `P_(∂ ψ 0)`.
Semantic recall: `lean_leansearch` returned only generic projection/cone infrastructure, so the
owner choice follows the verified local Chapter 19/28 APIs instead. -/

section ConePrimalDualAlgorithm

variable {H : Type u} {G : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

variable {K : Set H} (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
variable (hK_convex : Convex ℝ K)
variable {ψ : G → Set.Ioi (⊥ : EReal)} (hψ : ψ ∈ Γ₀(G))
variable (hψ_ph : PositivelyHomogeneous ψ.asEReal)
variable (z : H) (r : G) (L : H →L[ℝ] G)

local notation "D" => (∂ ψ) 0
local notation "hK_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex
local notation "hK_gammaZero" =>
  indicator_mem_gammaZero_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex
local notation "dualObj" =>
  fun v : G ↦
    (1 / 2 : ℝ) * Metric.infDist (z - L.adjoint v) (Set.polarCone K) ^ 2 + ⟪v, r⟫_ℝ
local notation "primalObj" =>
  fun x : H ↦
    (ψ (L x - r) : EReal) + ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))

omit hK_nonempty hK_closed hK_convex z r L in
/-- The subdifferential at `0` of a positively homogeneous `Γ₀` function is Chebyshev, so the
textbook projector `P_(∂ ψ(0))` used in Example 28.17 is well defined. -/
theorem subdifferentialZero_isChebyshev_of_positivelyHomogeneous_mem_gammaZero
    (hψ : ψ ∈ Γ₀(G)) (hψ_ph : PositivelyHomogeneous ψ.asEReal) :
    IsChebyshev D := by
  simpa using
    (isChebyshev_smul_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero
      hψ_ph hψ (1 : PosReal) : IsChebyshev (((1 : ℝ) • ((∂ ψ) 0) : Set G)))

local notation "hD_cheb" =>
  subdifferentialZero_isChebyshev_of_positivelyHomogeneous_mem_gammaZero
    hψ hψ_ph

/-- For a positively homogeneous member of `Γ₀(G)`, the scaled proximal operator of `ψ*`
is the metric projection onto `(∂ ψ) 0`. This is the projector notation used in
Example 28.17. -/
theorem
    prox_gammaZeroConjugate_eq_projection_subdifferentialZero_of_positivelyHomogeneous_mem_gammaZero
    (γ : PosReal) :
    Prox⋆[γ, ψ, hψ] = P[D, hD_cheb] := by
  obtain ⟨_, hminorant_nonempty, hminorant_closed, hminorant_convex⟩ :=
    eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero hψ_ph hψ
  have hzero : (ψ 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hψ_ph hψ
  have hminorant_eq : linearMinorantSet ψ = D :=
    linearMinorantSet_eq_subdifferential_zero hzero
  have hD_nonempty : Set.Nonempty D := by
    simpa [← hminorant_eq] using hminorant_nonempty
  have hD_closed : IsClosed D := by
    simpa [← hminorant_eq] using hminorant_closed
  have hD_convex : Convex ℝ D := by
    simpa [← hminorant_eq] using hminorant_convex
  have hconj :
      (fun v : G ↦ (ψ∗[hψ] v : EReal)) = (ι[D]).asEReal :=
    by
      funext v
      calc
        (ψ∗[hψ] v : EReal) = ψ.asEReal∗ v := by
          rw [gammaZeroConjugate_apply]
        _ = (σ[D])∗ v := by
          rw [eq_supportFunction_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero
            hψ_ph hψ]
        _ = ((ι[D]).asEReal)∗∗ v := by
          rw [← conjugate_indicator_eq_supportFunction D]
        _ = ((ι[D]).asEReal) v := by
          simpa using congrFun
            (biconjugate_indicator_eq_indicator_of_isClosed_convex D hD_closed hD_convex) v
  have hscaled : γ • ψ∗[hψ] = ι[D] := by
    funext v
    apply Subtype.ext
    change (((γ : ℝ) : EReal) * (ψ∗[hψ] v : EReal)) = (ι[D] v : EReal)
    rw [show (ψ∗[hψ] v : EReal) = (ι[D] v : EReal) from congrFun hconj v]
    by_cases hv : v ∈ D
    · simp [ERealFunction.indicator, hv]
    · simpa [ERealFunction.indicator, hv] using
        (EReal.coe_mul_top_of_pos γ.2 : ((γ : ℝ) : EReal) * ⊤ = ⊤)
  let hD_gammaZero :
      ι[D] ∈ Γ₀(G) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex
  have hproxIndicator :
      Prox[ι[D], hD_gammaZero] = P[D, hD_cheb] := by
    simpa [hD_gammaZero] using
      (proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hD_nonempty hD_closed hD_convex :
        Prox[ι[D], indicator_mem_gammaZero_of_nonempty_isClosed_convex
          hD_nonempty hD_closed hD_convex] =
          P[D, isChebyshev_of_nonempty_isClosed_convex
            hD_nonempty hD_closed hD_convex])
  ext x
  have hxIndicator : IsProxPoint (ι[D]) x (P[D, hD_cheb] x) := by
    rw [← hproxIndicator]
    exact proximityOperator_isProxPoint (ι[D])
      (hasUniqueProxPoint_of_mem_gammaZero (ι[D]) hD_gammaZero) x
  have hxScaled : IsProxPoint (γ • ψ∗[hψ]) x (P[D, hD_cheb] x) := by
    simpa [hscaled] using hxIndicator
  change
      Prox⋆[γ, ψ, hψ] x =
    P[D, hD_cheb] x
  simpa using
    (eq_proximityOperator_of_isProxPoint
      (γ • ψ∗[hψ])
      (hasUniqueProxPoint_of_mem_gammaZero
        (γ • ψ∗[hψ])
        (smul_mem_gammaZero (ψ∗[hψ]) (gammaZeroConjugate_mem_gammaZero hψ) γ))
      hxScaled).symm

/-- A pair of sequences `x` and `v` satisfies the recursion `(28.67)` of Example 28.17 when it
starts from `v0`, projects `z - L^* v_n` onto `K`, and updates `v_(n+1)` by relaxed projection
onto `D = (∂ ψ) 0`. -/
structure IsConePositivelyHomogeneousPrimalDualOrbit
    (γ : PosReal) (lam : ℝ) (v0 : G) (x : ℕ → H) (v : ℕ → G) : Prop where
  /-- The dual orbit starts at the prescribed point `v0`. -/
  v_zero : v 0 = v0
  /-- The primal update is `x_n = P_K(z - L^* v_n)`. -/
  x_eq : ∀ n : ℕ, x n = P[K, hK_cheb] (z - L.adjoint (v n))
  /-- The relaxed dual update is
  `v_(n+1) = v_n + λ (P_D(v_n + γ(Lx_n - r)) - v_n)`. -/
  v_succ_eq : ∀ n : ℕ,
    v (n + 1) =
      v n + lam • (P[D, hD_cheb] (v n + (γ : ℝ) • (L (x n) - r)) - v n)

local notation "ConePrimalDualOrbit" =>
  IsConePositivelyHomogeneousPrimalDualOrbit
    hK_nonempty hK_closed hK_convex hψ hψ_ph z r L

namespace IsConePositivelyHomogeneousPrimalDualOrbit

/-- The recursion `(28.67)` is the constant-relaxation specialization of the Proposition 28.16
orbit with `φ = ι[K]` and `Prox_(γ ψ*) = P_(∂ ψ(0))`. -/
theorem toIsProximalCompositePrimalDualOrbit
    {γ : PosReal} {lam : ℝ} {v0 : G} {x : ℕ → H} {v : ℕ → G}
    (hOrbit :
      ConePrimalDualOrbit γ lam v0 x v) :
    IsProximalCompositePrimalDualOrbit
      hK_gammaZero hψ z r L γ (fun _ : ℕ ↦ lam) v0 x v := by
  have hproxK : Prox[ι[K], hK_gammaZero] = P[K, hK_cheb] := by
    simpa using
      (proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hK_nonempty hK_closed hK_convex :
        Prox[ι[K], indicator_mem_gammaZero_of_nonempty_isClosed_convex
          hK_nonempty hK_closed hK_convex] =
          P[K, isChebyshev_of_nonempty_isClosed_convex
            hK_nonempty hK_closed hK_convex])
  have hproxD :=
    prox_gammaZeroConjugate_eq_projection_subdifferentialZero_of_positivelyHomogeneous_mem_gammaZero
      hψ hψ_ph γ
  have hproxD_explicit :
      Prox[γ, ψ∗[hψ], gammaZeroConjugate_mem_gammaZero hψ] = P[D, hD_cheb] := by
    simpa using hproxD
  refine ⟨hOrbit.v_zero, ?_, ?_⟩
  · intro n
    simpa [← hproxK] using hOrbit.x_eq n
  · intro n
    simpa [← hproxD_explicit] using hOrbit.v_succ_eq n

/-- The source-facing recursion `(28.67)` and the Proposition 28.16 orbit are equivalent after
rewriting `Prox_ι[K]` and `Prox_(γ ψ*)` as the textbook projectors `P_K` and `P_(∂ ψ(0))`. -/
theorem iff_isProximalCompositePrimalDualOrbit
    {γ : PosReal} {lam : ℝ} {v0 : G} {x : ℕ → H} {v : ℕ → G} :
    ConePrimalDualOrbit γ lam v0 x v ↔
    IsProximalCompositePrimalDualOrbit
      hK_gammaZero hψ z r L γ (fun _ : ℕ ↦ lam) v0 x v := by
  have hproxK : Prox[ι[K], hK_gammaZero] = P[K, hK_cheb] := by
    simpa using
      (proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hK_nonempty hK_closed hK_convex :
        Prox[ι[K], indicator_mem_gammaZero_of_nonempty_isClosed_convex
          hK_nonempty hK_closed hK_convex] =
          P[K, isChebyshev_of_nonempty_isClosed_convex
            hK_nonempty hK_closed hK_convex])
  have hproxD :=
    prox_gammaZeroConjugate_eq_projection_subdifferentialZero_of_positivelyHomogeneous_mem_gammaZero
      hψ hψ_ph γ
  have hproxD_explicit :
      Prox[γ, ψ∗[hψ], gammaZeroConjugate_mem_gammaZero hψ] = P[D, hD_cheb] := by
    simpa using hproxD
  constructor
  · intro hOrbit
    exact hOrbit.toIsProximalCompositePrimalDualOrbit
  · intro hOrbit
    refine ⟨hOrbit.v_zero, ?_, ?_⟩
    · intro n
      simpa [hproxK] using hOrbit.x_eq n
    · intro n
      simpa [hproxD_explicit] using hOrbit.v_succ_eq n

end IsConePositivelyHomogeneousPrimalDualOrbit

/-- Example 28.17 (1): let `K` be a nonempty closed convex cone in `H`, let `ψ ∈ Γ₀(G)` be
positively homogeneous, set `D = (∂ ψ) 0`, let `z ∈ H`, let `r ∈ G`, and let
`L : H →L[ℝ] G` satisfy `r ∈ sri (L '' K - effectiveDomain ψ)`. Let
`γ ∈ ]0, 2 / ‖L‖²[`, set `δ = 2 - γ ‖L‖² / 2`, let `λ ∈ ]0, δ[`, and let
`(x, v)` satisfy the recursion `(28.67)`. Then `(v_n)` converges weakly to a dual solution
`vbar` of `(28.66)`, and the unique primal solution `xbar` of `(28.65)` satisfies
`xbar = P_K(z - L^* vbar)`. -/
theorem conePositivelyHomogeneousPrimalDual_exists_weakDualLimit
    (hsri : r ∈ Set.strongRelativeInterior (L '' K - effectiveDomain ψ))
    (hK_cone : IsCone K)
    (γ : PosReal) (hγ : (γ : ℝ) < 2 / ‖L‖ ^ (2 : ℕ))
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) (proximalCompositePrimalDualRelaxationBound γ L))
    (v0 : G) {x : ℕ → H} {v : ℕ → G}
    (hOrbit : ConePrimalDualOrbit γ lam v0 x v) :
    ∃ xbar ∈ Argmin[K] primalObj,
      ∃ vbar ∈ Argmin[D] dualObj,
        Argmin[K] primalObj = ({xbar} : Set H) ∧
          Tendsto (fun n : ℕ ↦ toWeakSpace ℝ G (v n)) atTop
            (𝓝 (toWeakSpace ℝ G vbar)) ∧
          xbar = P[K, hK_cheb] (z - L.adjoint vbar) := sorry

/-- Example 28.17 (2): under the hypotheses of Example 28.17, the primal iterates `(x_n)`
converge strongly to the unique minimizer `xbar` of `(28.65)`. -/
theorem conePositivelyHomogeneousPrimalDual_exists_strongPrimalLimit
    (hsri : r ∈ Set.strongRelativeInterior (L '' K - effectiveDomain ψ))
    (hK_cone : IsCone K)
    (γ : PosReal) (hγ : (γ : ℝ) < 2 / ‖L‖ ^ (2 : ℕ))
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) (proximalCompositePrimalDualRelaxationBound γ L))
    (v0 : G) {x : ℕ → H} {v : ℕ → G}
    (hOrbit : ConePrimalDualOrbit γ lam v0 x v) :
    ∃ xbar ∈ Argmin[K] primalObj,
      Argmin[K] primalObj = ({xbar} : Set H) ∧ Tendsto x atTop (𝓝 xbar) := sorry

end ConePrimalDualAlgorithm

end ERealFunction
