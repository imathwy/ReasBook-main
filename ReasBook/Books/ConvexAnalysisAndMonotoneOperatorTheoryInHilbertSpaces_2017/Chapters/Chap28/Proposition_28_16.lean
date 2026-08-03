import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap19.Proposition_19_5
import BauschkeLean.Chap28.Corollary_28_9

open Filter
open scoped InnerProductSpace Pointwise Topology

noncomputable section

universe u v

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Proposition 28.16 is the primal-dual forward-backward recursion `(28.58)` for
  the proximal composite objective from Proposition 19.5.
- `core/canonical`: the stable local owners are `Argmin`, `Prox`,
  `proximalCompositePrimalObjective`, `proximalCompositeDualObjective`, and weak convergence in
  `WeakSpace ℝ`.
- `bridge/view`: the source parameter `δ = 2 - γ ‖L‖² / 2` and the coupled sequences `(x_n, v_n)`
  are kept explicit, while primal uniqueness is exposed by the singleton-`Argmin` surface built on
  the Chapter 19 objective owners.
Semantic recall: `lean_leansearch` only surfaced generic convexity/proximal entries here, so the
owner choice follows the verified Chapter 28 local APIs together with the textbook formulas. -/

section ProximalCompositePrimalDualAlgorithm

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The relaxation bound `δ = 2 - γ ‖L‖² / 2` from Proposition 28.16. -/
def proximalCompositePrimalDualRelaxationBound
    (γ : PosReal) (L : H →L[ℝ] K) : ℝ :=
  2 - (γ : ℝ) * ‖L‖ ^ (2 : ℕ) / 2

omit [CompleteSpace H] [CompleteSpace K] in
/-- Expanding `proximalCompositePrimalDualRelaxationBound γ L` gives the textbook formula
`2 - γ ‖L‖² / 2`. -/
@[simp] theorem proximalCompositePrimalDualRelaxationBound_eq
    (γ : PosReal) (L : H →L[ℝ] K) :
    proximalCompositePrimalDualRelaxationBound γ L = 2 - (γ : ℝ) * ‖L‖ ^ (2 : ℕ) / 2 := rfl

/-- A pair of sequences `x` and `v` satisfies the primal-dual recursion `(28.58)` for the
proximal composite problem attached to `φ`, `ψ`, `z`, `r`, `L`, `γ`, `lam`, and `v0`. -/
structure IsProximalCompositePrimalDualOrbit
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    {ψ : K → Set.Ioi (⊥ : EReal)} (hψ : ψ ∈ Γ₀(K))
    (z : H) (r : K) (L : H →L[ℝ] K) (γ : PosReal) (lam : ℕ → ℝ) (v0 : K)
    (x : ℕ → H) (v : ℕ → K) : Prop where
  /-- The dual orbit starts at the prescribed point `v0`. -/
  v_zero : v 0 = v0
  /-- The primal iterate is `x_n = Prox_φ(z - L^* v_n)`. -/
  x_eq : ∀ n : ℕ, x n = Prox[φ, hφ] (z - L.adjoint (v n))
  /-- The relaxed forward-backward step is
  `v_(n+1) = v_n + λ_n (Prox_(γ ψ^*)(v_n + γ (L x_n - r)) - v_n)`. -/
  v_succ_eq : ∀ n : ℕ,
    v (n + 1) =
      v n +
        lam n •
          (Prox[γ, ψ∗[hψ], gammaZeroConjugate_mem_gammaZero hψ]
              (v n + (γ : ℝ) • (L (x n) - r)) -
            v n)

/-- Proposition 28.16 (1): let `φ ∈ Γ₀(H)`, let `ψ ∈ Γ₀(K)`, let `z ∈ H`, let `r ∈ K`, and let
`L : H →L[ℝ] K` satisfy `r ∈ sri (L '' effectiveDomain φ - effectiveDomain ψ)`. Let
`γ ∈ ]0, 2 / ‖L‖²[`, set `δ = 2 - γ ‖L‖² / 2`, let `(λ_n)` lie in `]0, δ[` with
`0 < sInf (Set.range lam)` and `sSup (Set.range lam) < δ`, and let `(x_n, v_n)` satisfy `(28.58)`.
Then `v_n` converges weakly to a dual solution `vbar`, and the unique primal solution `xbar`
satisfies `xbar = Prox_φ (z - L^* vbar)`. The primal and dual argmin sets use the canonical
Chapter 19 owners `proximalCompositePrimalObjective` and `proximalCompositeDualObjective`. -/
theorem proximalCompositePrimalDual_exists_weakDualLimit
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    {ψ : K → Set.Ioi (⊥ : EReal)} (hψ : ψ ∈ Γ₀(K))
    (z : H) (r : K) (L : H →L[ℝ] K)
    (hsri : r ∈ Set.strongRelativeInterior (L '' effectiveDomain φ - effectiveDomain ψ))
    (γ : PosReal) (hγ : (γ : ℝ) < 2 / ‖L‖ ^ (2 : ℕ))
    (lam : ℕ → ℝ)
    (hlam :
      ∀ n : ℕ, lam n ∈ Set.Ioo (0 : ℝ) (proximalCompositePrimalDualRelaxationBound γ L))
    (hlam_inf : 0 < sInf (Set.range lam))
    (hlam_sup : sSup (Set.range lam) < proximalCompositePrimalDualRelaxationBound γ L)
    (v0 : K) {x : ℕ → H} {v : ℕ → K}
    (hOrbit : IsProximalCompositePrimalDualOrbit hφ hψ z r L γ lam v0 x v) :
    ∃ xbar ∈ Argmin (proximalCompositePrimalObjective φ ψ z r L),
      ∃ vbar ∈ Argmin (proximalCompositeDualObjective φ ψ hψ z r L),
        Argmin (proximalCompositePrimalObjective φ ψ z r L) = ({xbar} : Set H) ∧
          Tendsto (fun n : ℕ ↦ toWeakSpace ℝ K (v n)) atTop (𝓝 (toWeakSpace ℝ K vbar)) ∧
          xbar = Prox[φ, hφ] (z - L.adjoint vbar) := sorry

/-- Proposition 28.16 (2): under the hypotheses of Proposition 28.16, the primal iterates
`(x_n)` converge strongly to the unique minimizer `xbar` of
`proximalCompositePrimalObjective φ ψ z r L`. -/
theorem proximalCompositePrimalDual_exists_strongPrimalLimit
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    {ψ : K → Set.Ioi (⊥ : EReal)} (hψ : ψ ∈ Γ₀(K))
    (z : H) (r : K) (L : H →L[ℝ] K)
    (hsri : r ∈ Set.strongRelativeInterior (L '' effectiveDomain φ - effectiveDomain ψ))
    (γ : PosReal) (hγ : (γ : ℝ) < 2 / ‖L‖ ^ (2 : ℕ))
    (lam : ℕ → ℝ)
    (hlam :
      ∀ n : ℕ, lam n ∈ Set.Ioo (0 : ℝ) (proximalCompositePrimalDualRelaxationBound γ L))
    (hlam_inf : 0 < sInf (Set.range lam))
    (hlam_sup : sSup (Set.range lam) < proximalCompositePrimalDualRelaxationBound γ L)
    (v0 : K) {x : ℕ → H} {v : ℕ → K}
    (hOrbit : IsProximalCompositePrimalDualOrbit hφ hψ z r L γ lam v0 x v) :
    ∃ xbar ∈ Argmin (proximalCompositePrimalObjective φ ψ z r L),
      Argmin (proximalCompositePrimalObjective φ ψ z r L) = ({xbar} : Set H) ∧
        Tendsto x atTop (𝓝 xbar) := sorry

end ProximalCompositePrimalDualAlgorithm

end ERealFunction
