import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap28.Proposition_28_16

open Filter
open Set
open scoped InnerProductSpace Pointwise Topology

noncomputable section

universe u v

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Example 28.18 is the best-approximation specialization of the primal-dual
  recursion `(28.70)` on the feasible set `C ∩ L ⁻¹' D`.
- `core/canonical`: Proposition 28.16 already provides the stable orbit owner for the
  proximal-composite problem over `Argmin`, `Prox`, and weak convergence in `WeakSpace ℝ`.
- `bridge/view`: this file keeps the textbook feasible set, the source-facing norm objective from
  Chapter 19, the support-function dual objective, and the projection recursion, while exposing
  the orbit as the `φ = ι[C]`, `ψ = ι[D]`, `r = 0` specialization of Proposition 28.16 for
  downstream reuse. The half squared-distance objective is only an internal bridge to the owner
  theorem behind Proposition 28.16.
-/

/- Semantic recall: `lean_leansearch` only surfaced generic projection results here, so the owner
choice follows the verified Chapter 28 primal-dual algorithm API from `Proposition_28_16`
together with the Chapter 19 best-approximation specialization. -/

section BestApproximationPrimalDualAlgorithm

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for the best-approximation specialization: `0 ∈ sri (L '' C - D)` forces `C` to be
nonempty. -/
private theorem nonempty_of_zero_mem_sri_image_sub_left
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ Set.strongRelativeInterior (L '' C - D)) :
    C.Nonempty := sorry

/-- Helper for the best-approximation specialization: `0 ∈ sri (L '' C - D)` forces `D` to be
nonempty. -/
private theorem nonempty_of_zero_mem_sri_image_sub_right
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ Set.strongRelativeInterior (L '' C - D)) :
    D.Nonempty := sorry

/-- The feasible set of the constrained best-approximation problem `(28.68)`. -/
def bestApproximationFeasibleSet (C : Set H) (D : Set K) (L : H →L[ℝ] K) : Set H :=
  C ∩ L ⁻¹' D

/-- The primal objective in `(28.68)`, namely `x ↦ ‖x - z‖`. -/
def bestApproximationPrimalObjective (z : H) : H → EReal :=
  fun x ↦ (‖x - z‖ : ℝ)

/-- The dual objective in `(28.69)`, namely
`v ↦ (1 / 2) ‖z - L^* v‖² - (1 / 2) d_C(z - L^* v)² + σ_D(v)`. -/
def bestApproximationDualObjective
    (C : Set H) (D : Set K) (z : H) (L : H →L[ℝ] K) : K → EReal :=
  fun v ↦
    ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ (2 : ℕ) : ℝ) : EReal) -
      ((((1 / 2 : ℝ) * Metric.infDist (z - L.adjoint v) C ^ (2 : ℕ) : ℝ) : EReal))) +
        σ[D] v

variable {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable {D : Set K} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
variable (z : H) (L : H →L[ℝ] K)
variable (hsri : (0 : K) ∈ Set.strongRelativeInterior (L '' C - D))

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex
    (nonempty_of_zero_mem_sri_image_sub_left C D L hsri) hC_closed hC_convex

local notation "hC_gamma" =>
  indicator_mem_gammaZero_of_nonempty_isClosed_convex
    (nonempty_of_zero_mem_sri_image_sub_left C D L hsri) hC_closed hC_convex

local notation "hD_gamma" =>
  indicator_mem_gammaZero_of_nonempty_isClosed_convex
    (nonempty_of_zero_mem_sri_image_sub_right C D L hsri) hD_closed hD_convex

local notation "hD_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex
    (nonempty_of_zero_mem_sri_image_sub_right C D L hsri) hD_closed hD_convex

local notation "P_C" => P[C, hC_cheb]
local notation "P_D" => P[D, hD_cheb]

/-- A pair of sequences `x` and `v` satisfies the primal-dual projection recursion `(28.70)` for
the best-approximation problem attached to `C`, `D`, `z`, `L`, `γ`, `λ`, and `v0`. -/
structure IsBestApproximationPrimalDualOrbit
    (γ : PosReal) (lam : ℝ) (v0 : K) (x : ℕ → H) (v : ℕ → K) : Prop where
  /-- The dual orbit starts at the prescribed point `v0`. -/
  v_zero : v 0 = v0
  /-- The primal update is `x_n = P_C(z - L^* v_n)`. -/
  x_eq : ∀ n : ℕ, x n = P_C (z - L.adjoint (v n))
  /-- The dual update is
  `v_(n+1) = v_n + γ λ (L x_n - P_D(γ⁻¹ v_n + L x_n))`. -/
  v_succ_eq : ∀ n : ℕ,
    v (n + 1) =
      v n +
        (((γ : ℝ) * lam) •
          (L (x n) - P_D (((γ : ℝ)⁻¹ • v n) + L (x n))))

local notation "BestApproximationPrimalDualOrbit" =>
  IsBestApproximationPrimalDualOrbit
    hC_closed hC_convex hD_closed hD_convex z L hsri

namespace IsBestApproximationPrimalDualOrbit

/-- The recursion `(28.70)` is the constant-relaxation specialization of the Proposition 28.16
orbit with `φ = ι[C]`, `ψ = ι[D]`, and `r = 0`. -/
theorem toIsProximalCompositePrimalDualOrbit
    {γ : PosReal} {lam : ℝ} {v0 : K} {x : ℕ → H} {v : ℕ → K}
    (hOrbit : BestApproximationPrimalDualOrbit γ lam v0 x v) :
    IsProximalCompositePrimalDualOrbit
      hC_gamma hD_gamma z (0 : K) L γ (fun _ : ℕ ↦ lam) v0 x v := sorry

end IsBestApproximationPrimalDualOrbit

/-- Internal bridge for Example 28.18: the source-facing primal argmin set is the singleton
projection point selected by any dual minimizer, matching the Chapter 19 best-approximation
surface. -/
private theorem bestApproximationPrimalArgmin_eq_singleton_projection_of_mem_dualArgmin
    {vbar : K} (hvbar : vbar ∈ Argmin (bestApproximationDualObjective C D z L)) :
    Argmin[bestApproximationFeasibleSet C D L] (bestApproximationPrimalObjective z) =
      ({P_C (z - L.adjoint vbar)} : Set H) := sorry

/-- Example 28.18 (1): let `C` and `D` be closed convex subsets of real Hilbert spaces, let
`z ∈ H`, and let `L : H →L[ℝ] K` satisfy `0 ∈ sri (L '' C - D)`. Let `γ ∈ ]0, 2 / ‖L‖²[`, set
`δ = 2 - γ ‖L‖² / 2`, let `λ ∈ ]0, δ[`, and let `(x, v)` satisfy `(28.70)`. Then `v_n`
converges weakly to a minimizer `vbar` of the dual objective `(28.69)`, and the unique primal
solution `xbar` of `(28.68)` satisfies `xbar = P_C(z - L^* vbar)`. -/
theorem bestApproximationPrimalDual_exists_weakDualLimit
    (γ : PosReal) (hγ : (γ : ℝ) < 2 / ‖L‖ ^ (2 : ℕ))
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) (proximalCompositePrimalDualRelaxationBound γ L))
    (v0 : K) {x : ℕ → H} {v : ℕ → K}
    (hOrbit : BestApproximationPrimalDualOrbit γ lam v0 x v) :
    ∃ vbar ∈ Argmin (bestApproximationDualObjective C D z L),
      ∃ xbar ∈
          Argmin[bestApproximationFeasibleSet C D L] (bestApproximationPrimalObjective z) ∩
            ({P_C (z - L.adjoint vbar)} : Set H),
        Tendsto (fun n : ℕ ↦ toWeakSpace ℝ K (v n)) atTop (𝓝 (toWeakSpace ℝ K vbar)) := sorry

/-- Example 28.18 (2): under the hypotheses of Example 28.18, the primal solution of `(28.68)`
is unique. -/
theorem bestApproximationPrimalDual_primalArgmin_singleton
    (γ : PosReal) (hγ : (γ : ℝ) < 2 / ‖L‖ ^ (2 : ℕ))
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) (proximalCompositePrimalDualRelaxationBound γ L))
    (v0 : K) {x : ℕ → H} {v : ℕ → K}
    (hOrbit : BestApproximationPrimalDualOrbit γ lam v0 x v) :
    ∃ xbar ∈ Argmin[bestApproximationFeasibleSet C D L] (bestApproximationPrimalObjective z),
      Argmin[bestApproximationFeasibleSet C D L] (bestApproximationPrimalObjective z) =
        ({xbar} : Set H) := sorry

/-- Example 28.18 (3): under the hypotheses of Example 28.18, the primal iterates `(x_n)`
converge strongly to the unique minimizer `xbar` of `(28.68)`. -/
theorem bestApproximationPrimalDual_exists_strongPrimalLimit
    (γ : PosReal) (hγ : (γ : ℝ) < 2 / ‖L‖ ^ (2 : ℕ))
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) (proximalCompositePrimalDualRelaxationBound γ L))
    (v0 : K) {x : ℕ → H} {v : ℕ → K}
    (hOrbit : BestApproximationPrimalDualOrbit γ lam v0 x v) :
    ∃ xbar ∈ Argmin[bestApproximationFeasibleSet C D L] (bestApproximationPrimalObjective z),
      Argmin[bestApproximationFeasibleSet C D L] (bestApproximationPrimalObjective z) =
          ({xbar} : Set H) ∧
        Tendsto x atTop (𝓝 xbar) := sorry

end BestApproximationPrimalDualAlgorithm

end ERealFunction
