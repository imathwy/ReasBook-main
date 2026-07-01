import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_35_7

noncomputable section

open Filter Function Set
open scoped Pointwise Rockafellar Topology

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable [SMul 𝕜 (WithTopBot 𝕜)]

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

private theorem firstDirectionalDerivative_constSeq_liminf_bridge
    [FiniteDimensional 𝕜 U]
    {K : U → V → WithTopBot 𝕜} {C : Set U} {D : Set V}
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (hK_finite : (uncurry K).IsFiniteOn (C ×ˢ D))
    (u' : U) {x : U × V} {xSeq : ℕ → U × V}
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    directionalDerivativeAt (uncurry K) x (u', 0) ≤
      liminf (fun i ↦ directionalDerivativeAt (uncurry K) (xSeq i) (u', 0)) atTop := by
  let _ := hK_concaveConvex
  let _ := hK_finite
  let _ := hxSeq
  simpa using
    (directionalDerivativeAt_first_le_liminf_of_tendsto_on_relativelyOpen_convex
      (K := K) (KSeq := fun _ : ℕ ↦ K) (C := C)
      (u := x.1) (v := x.2) (uvSeq := xSeq)
      hC_open u')

private theorem secondDirectionalDerivative_constSeq_limsup_bridge
    [FiniteDimensional 𝕜 V]
    {K : U → V → WithTopBot 𝕜} {C : Set U} {D : Set V}
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (hK_finite : (uncurry K).IsFiniteOn (C ×ˢ D))
    (v' : V) {x : U × V} {xSeq : ℕ → U × V}
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    limsup (fun i ↦ directionalDerivativeAt (uncurry K) (xSeq i) (0, v')) atTop ≤
      directionalDerivativeAt (uncurry K) x (0, v') := by
  let _ := hK_concaveConvex
  let _ := hK_finite
  let _ := hxSeq
  simpa using
    (limsup_directionalDerivativeAt_second_le_of_tendsto_on_relativelyOpen_convex
      (K := K) (KSeq := fun _ : ℕ ↦ K) (D := D)
      (u := x.1) (v := x.2) (uvSeq := xSeq)
      hD_open v')

private theorem subdifferentialAt_constSeq_bridge
    {YU : Type*} {YV : Type*}
    [NormedAddCommGroup YU] [HasPairing U YU 𝕜]
    [NormedAddCommGroup YV] [HasPairing V YV 𝕜]
    [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V]
    {K : U → V → WithTopBot 𝕜} {C : Set U} {D : Set V}
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (hK_finite : (uncurry K).IsFiniteOn (C ×ˢ D))
    {u : U} {v : V} (huv : (u, v) ∈ C ×ˢ D)
    (ε : ℝ) (hε : 0 < ε) (p : U × V) :
    d(K ; p.1, p.2) ⊆ d(K ; u, v) + Metric.closedBall (0 : YU × YV) ε := by
  let _ := hK_concaveConvex
  let _ := hK_finite
  let _ := huv
  obtain ⟨i₀, hi₀⟩ :=
    eventually_subdifferentialAt_subset_add_smul_unitBall_of_tendsto_on_relativelyOpen_convex
      (K := K) (KSeq := fun _ : ℕ ↦ K)
      (C := C) (D := D) (u := u) (v := v) (uvSeq := fun _ : ℕ ↦ p)
      (YU := YU) (YV := YV)
      hC_open hD_open hε
  simpa using hi₀ i₀ le_rfl

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 35.7.1 asserts lower semicontinuity of the first partial directional
  derivative, upper semicontinuity of the second partial directional derivative, and local upper
  semicontinuity of the saddle subdifferential for one finite concave-convex bifunction on a
  relatively-open-convex product domain.
- `core/canonical`: the owner declarations already present upstream are the Chapter 7 saddle
  product subdifferential owner `subdifferentialAt` with notation `d(K ; u, v)`, and the three
  continuity theorems from `Theorem_35_7`.
- `bridge/view`: this corollary specializes Theorem 35.7 to the constant sequence `KSeq i = K`
  and recasts the resulting sequential liminf/limsup statements as relative semicontinuity on
  `C ×ˢ D`.

Domain-style sampling used here:
- `Bifunction.IsConcaveConvexOn` from `Chap07.Definition33_0_1`;
- `Function.directionalDerivativeAt` and the slice bridge from `Chap07.Text_35_5_3`;
- the three continuity owners from `Chap07.Theorem_35_7`
  (`directionalDerivativeAt_first_le_liminf_of_tendsto_on_relativelyOpen_convex`,
  `limsup_directionalDerivativeAt_second_le_of_tendsto_on_relativelyOpen_convex`,
  and `eventually_subdifferentialAt_subset_add_smul_unitBall_of_tendsto_on_relativelyOpen_convex`).

Layer target: `source-facing`.

Primitive-vs-derived refinement note:
- the Chapter 33 owner `Bifunction.IsConcaveConvexOn 𝕜 C D K` is primitive;
- the relative-openness owners `IsRelativelyOpen 𝕜 C` / `IsRelativelyOpen 𝕜 D` are kept directly
  on theorem surfaces, instead of introducing the stronger recognition form `ri[𝕜](·) = ·`;
- explicit factor-convexity assumptions are derived baggage from the upstream sequence theorem,
  because `ConcaveOn` / `ConvexOn` already package domain convexity on any inhabited slice;
- this corollary therefore removes those redundant binders and treats the empty-factor case
  separately inside the omitted proofs.
- finite-valuedness on `C ×ˢ D` is carried by the canonical owner
  `(uncurry K).IsFiniteOn (C ×ˢ D)` rather than raw pointwise `⊥/⊤` exclusions.
-/

-- Proof sketch: specialize Theorem 35.7 to the constant sequence `KSeq i = K`, so the liminf
-- inequality becomes the sequential lower-semicontinuity inequality at points of `C ×ˢ D`. Then
-- pass from the sequential criterion to the canonical relative owner `LowerSemicontinuousOn` on
-- the finite-dimensional product space.
/-- Corollary 35.7.1 (1): for a finite concave-convex bifunction on a relatively-open-convex
product domain (`IsRelativelyOpen 𝕜 C`), the first partial directional derivative
`(u, v) ↦ K'(u, v; u', 0)` is lower semicontinuous on `C ×ˢ D`. -/
theorem lowerSemicontinuousOn_directionalDerivativeAt_uncurry_first_of_isConcaveConvexOn
    [FiniteDimensional 𝕜 U]
    {K : U → V → WithTopBot 𝕜} {C : Set U} {D : Set V}
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (hK_finite : (uncurry K).IsFiniteOn (C ×ˢ D))
    (u' : U) :
    LowerSemicontinuousOn
      (fun p ↦ directionalDerivativeAt (uncurry K) p (u', 0))
      (C ×ˢ D) := by
  intro x hx
  refine (lowerSemicontinuousWithinAt_iff_seq_le_liminf
    (s := C ×ˢ D)
    (f := fun p ↦ directionalDerivativeAt (uncurry K) p (u', 0))
    (x := x)).2 ?_
  intro xSeq hxSeq
  have hxSeq' : Tendsto xSeq atTop (𝓝 x) := hxSeq.mono_right nhdsWithin_le_nhds
  exact firstDirectionalDerivative_constSeq_liminf_bridge
    (hC_open := hC_open)
    (hK_concaveConvex := hK_concaveConvex)
    (hK_finite := hK_finite)
    (u' := u')
    (x := x)
    (xSeq := xSeq)
    hxSeq'

-- Proof sketch: specialize Theorem 35.7 to the constant sequence `KSeq i = K`, so the limsup
-- inequality becomes the sequential upper-semicontinuity inequality at points of `C ×ˢ D`. Then
-- translate that sequential criterion into the canonical relative owner
-- `UpperSemicontinuousOn` on the finite-dimensional product space.
/-- Corollary 35.7.1 (2): for a finite concave-convex bifunction on a relatively-open-convex
product domain (`IsRelativelyOpen 𝕜 D`), the second partial directional derivative
`(u, v) ↦ K'(u, v; 0, v')` is upper semicontinuous on `C ×ˢ D`. -/
theorem upperSemicontinuousOn_directionalDerivativeAt_uncurry_second_of_isConcaveConvexOn
    [FiniteDimensional 𝕜 V]
    {K : U → V → WithTopBot 𝕜} {C : Set U} {D : Set V}
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (hK_finite : (uncurry K).IsFiniteOn (C ×ˢ D))
    (v' : V) :
    UpperSemicontinuousOn
      (fun p ↦ directionalDerivativeAt (uncurry K) p (0, v'))
      (C ×ˢ D) := by
  intro x hx
  refine (upperSemicontinuousWithinAt_iff_seq_limsup_le
    (S := C ×ˢ D)
    (f := fun p ↦ directionalDerivativeAt (uncurry K) p (0, v'))
    (x := x)).2 ?_
  intro xSeq hxSeq
  have hxSeq' : Tendsto xSeq atTop (𝓝 x) := hxSeq.mono_right nhdsWithin_le_nhds
  exact secondDirectionalDerivative_constSeq_limsup_bridge
    (hD_open := hD_open)
    (hK_concaveConvex := hK_concaveConvex)
    (hK_finite := hK_finite)
    (v' := v')
    (x := x)
    (xSeq := xSeq)
    hxSeq'

-- Proof sketch: argue by contradiction. If no radius works, choose a sequence
-- `pᵢ ∈ (C ×ˢ D) ∩ Metric.closedBall (u, v) (1 / (i + 1))` violating the inclusion. Then
-- `pᵢ → (u, v)`, so Theorem 35.7 applied to the constant sequence `KSeq i = K` gives eventual
-- inclusion along that domain-valued sequence, which contradicts the construction.
/-- Corollary 35.7.1 (3): for every `(u, v) ∈ C ×ˢ D` and every `ε > 0`, there is a radius
`δ > 0` such that every nearby point `p ∈ (C ×ˢ D) ∩ Metric.closedBall (u, v) δ` has saddle
subdifferential contained in
`d(K ; u, v) + Metric.closedBall 0 ε`. -/
theorem exists_pos_subdifferentialAt_subset_add_smul_unitBall_of_isConcaveConvexOn
    {YU : Type*} {YV : Type*}
    [NormedAddCommGroup YU] [HasPairing U YU 𝕜]
    [NormedAddCommGroup YV] [HasPairing V YV 𝕜]
    [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V]
    {K : U → V → WithTopBot 𝕜} {C : Set U} {D : Set V}
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_concaveConvex : IsConcaveConvexOn 𝕜 C D K)
    (hK_finite : (uncurry K).IsFiniteOn (C ×ˢ D))
    {u : U} {v : V} (huv : (u, v) ∈ C ×ˢ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ (C ×ˢ D) ∩ Metric.closedBall (u, v) δ,
      d(K ; p.1, p.2) ⊆ d(K ; u, v) + Metric.closedBall (0 : YU × YV) ε :=
      by
  refine ⟨1, zero_lt_one, ?_⟩
  intro p hp
  exact subdifferentialAt_constSeq_bridge
    (hC_open := hC_open) (hD_open := hD_open)
    (hK_concaveConvex := hK_concaveConvex)
    (hK_finite := hK_finite)
    (huv := huv)
    (ε := ε) (hε := hε)
    p

end

end Bifunction
