import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary_35_7_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_35_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_35_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_35_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter Function Set
open scoped Gradient Rockafellar Topology

universe u v w

namespace Bifunction

section StrongDualOwner

variable {𝕜 : Type w}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [FiniteDimensional 𝕜 (U × V)]

variable {C : Set U} {D : Set V}
variable {K : U → V → 𝕜}
variable {KSeq : ℕ → U → V → 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing` (canonical owner): Theorem 35.10 is first exposed at the strong-dual owner
  layer, as convergence of the partial Fréchet-derivative owner `prodFDeriv K` on `C ×ˢ D`.
- `core/canonical`: the owner chain is Chapter 35 value convergence (`Theorem_35_4`),
  saddle-subdifferential continuity (`Theorem_35_7` / `Corollary_35_7_1`), and singleton-fiber
  identification at differentiability points (`Theorem_35_8`).
- `bridge/view`: the Euclidean product gradient `Bifunction.gradient` is downstream of this owner,
  obtained only after an inner-product Fréchet-Riesz bridge.

Layer target: `core/canonical` in this section.
-/

/-- Strong-dual owner for the partial Fréchet-derivative pair of a bifunction. -/
abbrev prodFDeriv (K : U → V → 𝕜) : U × V → StrongDual 𝕜 U × StrongDual 𝕜 V :=
  fun p ↦ (fderiv 𝕜 (fun u' ↦ K u' p.2) p.1, fderiv 𝕜 (K p.1) p.2)

-- Proof sketch: derive the limit-side concave-convex owner from Chapter 35 value convergence,
-- pass to local upper-semicontinuity of saddle subdifferentials, identify all fibers as
-- singleton products of partial Fréchet derivatives using Theorem 35.8, and conclude local
-- uniform convergence of the selected strong-dual branch.
/-- Canonical companion to Theorem 35.10 at the strong-dual owner layer: locally uniform
convergence of finite differentiable concave-convex bifunctions on `C ×ˢ D` forces locally
uniform convergence of the partial Fréchet-derivative pair in
`StrongDual 𝕜 U × StrongDual 𝕜 V`. -/
theorem tendstoLocallyUniformlyOn_prodFDeriv_of_tendstoLocallyUniformlyOn_uncurry_on_relativelyOpen
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_diff : DifferentiableOn 𝕜 (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn 𝕜 (uncurry (KSeq i)) (C ×ˢ D))
    (hloc : TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D)) :
    TendstoLocallyUniformlyOn
      (fun i ↦ prodFDeriv (KSeq i))
      (prodFDeriv K)
      atTop (C ×ˢ D) := sorry

-- Proof sketch: first upgrade pointwise convergence on `C ×ˢ D` to local uniform convergence via
-- Theorem 35.4, then apply the canonical strong-dual theorem above and restrict to the chosen
-- closed bounded set `S`.
/-- Theorem 35.10, canonical owner form: if differentiable concave-convex bifunctions `KSeq i`
converge pointwise on `C ×ˢ D` to differentiable `K`, then their strong-dual partial
Fréchet-derivative pair converges uniformly on every closed bounded subset of `C ×ˢ D`. -/
theorem
    prodFDeriv_tendstoUniformlyOn_on_closed_bounded_of_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_diff : DifferentiableOn 𝕜 (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn 𝕜 (uncurry (KSeq i)) (C ×ˢ D))
    (hlimit : ∀ p ∈ C ×ˢ D, Tendsto (fun i ↦ uncurry (KSeq i) p) atTop (𝓝 (uncurry K p)))
    {S : Set (U × V)} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ C ×ˢ D) :
    TendstoUniformlyOn
      (fun i ↦ prodFDeriv (KSeq i))
      (prodFDeriv K)
      atTop S := sorry

-- Proof sketch: specialize the closed-bounded theorem to singleton subsets.
/-- Pointwise strong-dual derivative convergence on `C ×ˢ D`, obtained from the closed-bounded
uniform convergence form by singleton specialization. -/
theorem prodFDeriv_tendsto_of_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_diff : DifferentiableOn 𝕜 (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn 𝕜 (uncurry (KSeq i)) (C ×ˢ D))
    (hlimit : ∀ p ∈ C ×ˢ D, Tendsto (fun i ↦ uncurry (KSeq i) p) atTop (𝓝 (uncurry K p)))
    (p : U × V) (hp : p ∈ C ×ˢ D) :
    Tendsto (fun i ↦ prodFDeriv (KSeq i) p) atTop (𝓝 (prodFDeriv K p)) := sorry

end StrongDualOwner

section EuclideanGradientBridge

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ (U × V)]

variable {C : Set U} {D : Set V}
variable {K : U → V → ℝ}
variable {KSeq : ℕ → U → V → ℝ}

/-!
`EuclideanGradientBridge` keeps the textbook gradient surface as a downstream view.
The owner-level theorem for this file is the strong-dual section above.
-/

-- Proof sketch: transport the strong-dual partial-derivative convergence through
-- `InnerProductSpace.toDual` on each factor and rewrite in product coordinates as
-- `Bifunction.gradient`.
/-- Euclidean bridge companion to Theorem 35.10: local uniform convergence of
`uncurry (KSeq i)` on `C ×ˢ D` implies local uniform convergence of `Bifunction.gradient`. -/
theorem tendstoLocallyUniformlyOn_gradient_of_tendstoLocallyUniformlyOn_uncurry_on_relativelyOpen
    (hC_open : IsRelativelyOpen ℝ C) (hD_open : IsRelativelyOpen ℝ D)
    (hK_diff : DifferentiableOn ℝ (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn ℝ C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn ℝ (uncurry (KSeq i)) (C ×ˢ D))
    (hloc : TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D)) :
    TendstoLocallyUniformlyOn (fun i ↦ gradient (KSeq i)) (gradient K) atTop (C ×ˢ D) := sorry

-- Proof sketch: combine the pointwise-to-local-uniform value upgrade with the gradient bridge
-- theorem above and restrict to `S`.
/-- Theorem 35.10 (Euclidean gradient view): on a relatively open product domain, pointwise
convergence of differentiable concave-convex bifunctions implies uniform convergence of gradients
on every closed bounded subset. -/
theorem
    gradient_tendstoUniformlyOn_on_closed_bounded_of_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen ℝ C) (hD_open : IsRelativelyOpen ℝ D)
    (hK_diff : DifferentiableOn ℝ (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn ℝ C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn ℝ (uncurry (KSeq i)) (C ×ˢ D))
    (hlimit : ∀ p ∈ C ×ˢ D, Tendsto (fun i ↦ uncurry (KSeq i) p) atTop (𝓝 (uncurry K p)))
    {S : Set (U × V)} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ C ×ˢ D) :
    TendstoUniformlyOn (fun i ↦ gradient (KSeq i)) (gradient K) atTop S := sorry

-- Proof sketch: specialize the closed-bounded gradient theorem to singleton subsets.
/-- Pointwise Euclidean-gradient convergence on `C ×ˢ D`, obtained by singleton specialization of
Theorem 35.10's closed-bounded form. -/
theorem gradient_tendsto_of_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen ℝ C) (hD_open : IsRelativelyOpen ℝ D)
    (hK_diff : DifferentiableOn ℝ (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn ℝ C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn ℝ (uncurry (KSeq i)) (C ×ˢ D))
    (hlimit : ∀ p ∈ C ×ˢ D, Tendsto (fun i ↦ uncurry (KSeq i) p) atTop (𝓝 (uncurry K p)))
    (p : U × V) (hp : p ∈ C ×ˢ D) :
    Tendsto (fun i ↦ gradient (KSeq i) p) atTop (𝓝 (gradient K p)) := sorry

end EuclideanGradientBridge

end Bifunction
