import BauschkeLean.Chap28.Example_28_18

open Filter
open Set
open scoped InnerProductSpace Pointwise Topology

noncomputable section

universe u v

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Example 28.19 is the equality-constrained recursion `(28.73)` for the
  best-approximation problem over `C ∩ L ⁻¹' {r}`.
- `core/canonical`: Example 28.18 already owns the constrained best-approximation problem on
  `bestApproximationFeasibleSet C D L` together with its primal-dual orbit.
- `bridge/view`: this file keeps the source recursion explicit and identifies it with the
  `D = {r}`, `γ = 1`, `λ = 1` specialization of `IsBestApproximationPrimalDualOrbit`. -/

section EqualityConstrainedBestApproximationPrimalDualAlgorithm

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Membership in `sri (L '' C)` forces the source set `C` to be nonempty. -/
private theorem nonempty_of_mem_sri_image
    (C : Set H) (r : K) (L : H →L[ℝ] K)
    (hsri : r ∈ Set.strongRelativeInterior (L '' C)) :
    C.Nonempty := sorry

omit [CompleteSpace H] [CompleteSpace K] in
/-- Translating the strong-relative-interior point `r ∈ L '' C` to the origin yields the
regularity set `L '' C - {r}` used by Example 28.18. -/
private theorem zero_mem_sri_image_sub_singleton_of_mem_sri_image
    (C : Set H) (r : K) (L : H →L[ℝ] K)
    (hsri : r ∈ Set.strongRelativeInterior (L '' C)) :
    (0 : K) ∈ Set.strongRelativeInterior (L '' C - ({r} : Set K)) := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hr_image, hcone⟩
  refine Set.mem_strongRelativeInterior_iff.mpr ⟨?_, ?_⟩
  · exact Set.mem_sub.mpr ⟨r, hr_image, r, by simp, sub_self r⟩
  · simpa using hcone

omit [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- The singleton constraint set `{r}` is nonempty. -/
private theorem singleton_nonempty (r : K) : ({r} : Set K).Nonempty :=
  ⟨r, by simp⟩

variable {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (z : H) {r : K} (L : H →L[ℝ] K)
variable (hsri : r ∈ Set.strongRelativeInterior (L '' C))

local notation "hsri0" => zero_mem_sri_image_sub_singleton_of_mem_sri_image C r L hsri
local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex
    (nonempty_of_mem_sri_image C r L hsri) hC_closed hC_convex
local notation "hD_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex
    (singleton_nonempty r) isClosed_singleton (convex_singleton r)

local notation "P_C" => P[C, hC_cheb]
local notation "BestApproximationOrbit" =>
  IsBestApproximationPrimalDualOrbit
    hC_closed hC_convex isClosed_singleton (convex_singleton r) z L hsri0

/-- A pair of sequences `x` and `v` satisfies the primal-dual recursion `(28.73)` for the
equality-constrained best-approximation problem attached to `C`, `z`, `r`, `L`, and `v0`. -/
structure IsEqualityConstrainedBestApproximationOrbit
    (v0 : K) (x : ℕ → H) (v : ℕ → K) : Prop where
  /-- The dual orbit starts at the prescribed point `v0`. -/
  v_zero : v 0 = v0
  /-- The primal update is `x_n = P_C(z - L^* v_n)`. -/
  x_eq (n : ℕ) : x n = P_C (z - L.adjoint (v n))
  /-- The dual update is `v_(n+1) = v_n + L x_n - r`. -/
  v_succ_eq (n : ℕ) : v (n + 1) = v n + (L (x n) - r)

namespace IsEqualityConstrainedBestApproximationOrbit

/-- The recursion `(28.73)` is the singleton-constraint specialization of Example 28.18 with
`D = {r}`, `γ = 1`, and `λ = 1`. -/
theorem toIsBestApproximationPrimalDualOrbit
    {v0 : K} {x : ℕ → H} {v : ℕ → K}
    (hOrbit :
      IsEqualityConstrainedBestApproximationOrbit
        hC_closed hC_convex z L hsri v0 x v) :
    BestApproximationOrbit (1 : PosReal) (1 : ℝ) v0 x v := by
  refine ⟨hOrbit.v_zero, hOrbit.x_eq, ?_⟩
  intro n
  simpa [projectionPoint_singleton_eq] using hOrbit.v_succ_eq n

/-- Conversely, the `D = {r}`, `γ = 1`, `λ = 1` specialization of Example 28.18 recovers the
source recursion `(28.73)`. -/
theorem ofIsBestApproximationPrimalDualOrbit
    {v0 : K} {x : ℕ → H} {v : ℕ → K}
    (hOrbit : BestApproximationOrbit (1 : PosReal) (1 : ℝ) v0 x v) :
    IsEqualityConstrainedBestApproximationOrbit
      hC_closed hC_convex z L hsri v0 x v := by
  refine ⟨hOrbit.v_zero, hOrbit.x_eq, ?_⟩
  intro n
  simpa [projectionPoint_singleton_eq] using hOrbit.v_succ_eq n

/-- The source recursion `(28.73)` and the singleton-constraint specialization of Example 28.18
are equivalent. -/
theorem iff_isBestApproximationPrimalDualOrbit
    {v0 : K} {x : ℕ → H} {v : ℕ → K} :
    IsEqualityConstrainedBestApproximationOrbit
        hC_closed hC_convex z L hsri v0 x v ↔
      BestApproximationOrbit (1 : PosReal) (1 : ℝ) v0 x v := by
  constructor
  · intro hOrbit
    exact hOrbit.toIsBestApproximationPrimalDualOrbit
  · intro hOrbit
    exact IsEqualityConstrainedBestApproximationOrbit.ofIsBestApproximationPrimalDualOrbit
      hC_closed hC_convex z L hsri hOrbit

end IsEqualityConstrainedBestApproximationOrbit

/-- Example 28.19 (1): let `C` be a closed convex subset of `H`, let `z ∈ H`, let `r ∈ K`, and
let `L : H →L[ℝ] K` satisfy `‖L‖ = 1` and `r ∈ sri (L '' C)`. Let `(x, v)` satisfy the recursion
`(28.73)`. Then `(v_n)` converges weakly to a minimizer `vbar` of `(28.72)`, and the unique
solution `xbar` of `(28.71)` satisfies `xbar = P_C(z - L^* vbar)`. -/
theorem equalityConstrainedBestApproximation_exists_weakDualLimit
    (hL_norm : ‖L‖ = 1)
    (v0 : K) {x : ℕ → H} {v : ℕ → K}
    (hOrbit :
      IsEqualityConstrainedBestApproximationOrbit
        hC_closed hC_convex z L hsri v0 x v) :
    ∃ vbar ∈ Argmin (bestApproximationDualObjective C ({r} : Set K) z L),
      ∃ xbar ∈
          Argmin[bestApproximationFeasibleSet C ({r} : Set K) L]
            (bestApproximationPrimalObjective z) ∩
            ({P_C (z - L.adjoint vbar)} : Set H),
        Tendsto (fun n : ℕ ↦ toWeakSpace ℝ K (v n)) atTop
          (𝓝 (toWeakSpace ℝ K vbar)) := sorry

/-- Example 28.19 (2): under the hypotheses of Example 28.19, the primal solution of `(28.71)`
is unique. -/
theorem equalityConstrainedBestApproximation_primalArgmin_singleton
    (hL_norm : ‖L‖ = 1)
    (v0 : K) {x : ℕ → H} {v : ℕ → K}
    (hOrbit :
      IsEqualityConstrainedBestApproximationOrbit
        hC_closed hC_convex z L hsri v0 x v) :
    ∃ xbar ∈
        Argmin[bestApproximationFeasibleSet C ({r} : Set K) L]
          (bestApproximationPrimalObjective z),
      Argmin[bestApproximationFeasibleSet C ({r} : Set K) L]
        (bestApproximationPrimalObjective z) = ({xbar} : Set H) := sorry

/-- Example 28.19 (3): under the hypotheses of Example 28.19, the primal iterates `(x_n)`
converge strongly to the unique minimizer `xbar` of `(28.71)`. -/
theorem equalityConstrainedBestApproximation_exists_strongPrimalLimit
    (hL_norm : ‖L‖ = 1)
    (v0 : K) {x : ℕ → H} {v : ℕ → K}
    (hOrbit :
      IsEqualityConstrainedBestApproximationOrbit
        hC_closed hC_convex z L hsri v0 x v) :
    ∃ xbar ∈
        Argmin[bestApproximationFeasibleSet C ({r} : Set K) L]
          (bestApproximationPrimalObjective z),
      Argmin[bestApproximationFeasibleSet C ({r} : Set K) L]
        (bestApproximationPrimalObjective z) = ({xbar} : Set H) ∧
        Tendsto x atTop (𝓝 xbar) := sorry

end EqualityConstrainedBestApproximationPrimalDualAlgorithm

end ERealFunction
