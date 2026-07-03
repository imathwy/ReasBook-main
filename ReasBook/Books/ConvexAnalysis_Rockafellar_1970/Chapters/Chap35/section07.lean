import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_35_7_1 (from Chap07) -/
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

/-! ### Theorem_35_7 (from Chap07) -/
noncomputable section

open Filter Function Set
open scoped Pointwise Rockafellar Topology

universe u v w

attribute [local instance] Classical.propDecidable

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 35.7 studies the continuity of the partial directional derivatives
  `K'(u, v; u', 0)` and `K'(u, v; 0, v')`, together with the upper-semicontinuity of the saddle
  subdifferential `dK(u, v)`.
- `core/canonical`: the owner declarations already present upstream are
  `Bifunction.IsConcaveConvexOn 𝕜 C D K`,
  `Function.toWithTopBot`,
  `Bifunction.subdifferential1At`, `Bifunction.subdifferential2At`,
  `Function.directionalDerivativeAt`, the Chapter 5/6 unary subdifferential owners, and the
  Chapter 5 convergence theorem
  `Function.limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex` together with
  its
  companion theorem
  `Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex`.
- `bridge/view`: Rockafellar's `dK(u, v)` is not a second independent package; it is exactly the
  product `d₁K(u, v) × d₂K(u, v)` of the two already-owned partial subdifferentials. The
  continuity clauses are stated directly for `WithTopBot 𝕜`-valued bifunction data together with
  finite-valuedness on `C ×ˢ D`.

Domain-style sampling used here:
- `Bifunction.IsConcaveConvexOn` from `Chap07.Definition33_0_1`;
- `Bifunction.subdifferentialAt` and `d(K ; u, v)` from `Text_35_6_3`;
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `Function.limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex` and
  `Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex`
  from `Chap05.Theorem_5_24_8`.

Primitive data vs derived API:
- primitive source data: the bifunction `K`, its two partial subdifferentials at `(u, v)`, the
  open convex sets `C`, `D`, the pointwise-convergent saddle sequence `KSeq`, and the convergent
  base-point sequence `(uᵢ, vᵢ)`;
- primitive owner data for all continuity clauses: the Chapter 33 saddle-shape owners
  `Bifunction.IsConcaveConvexOn 𝕜 C D K` and
  `∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (KSeq i)`;
- primitive bridge data: the canonical finite-valued owner
   `(uncurry K).IsFiniteOn (C ×ˢ D)` and its sequence version
   `∀ i, (uncurry (KSeq i)).IsFiniteOn (C ×ˢ D)`;
- primitive source-facing owner reused from Text 35.6.3: `Bifunction.subdifferentialAt K u v`;
- derived API: the two semicontinuity inequalities for the partial directional derivatives and the
  eventual inclusion of `dKᵢ(uᵢ, vᵢ)` in the Minkowski sum of `dK(u, v)` with a closed
  `ε`-ball in the pairing product space.

Layer target: `source-facing`. The theorem is explicitly about saddle partial derivatives and the
set-valued map `dK`, so the public surface keeps those objects directly on the
`WithTopBot 𝕜` codomain layer.

Ambient-assumption minimization:
- the bridge `saddleExtension`, reused from `Definition33_0_2`, is purely set-theoretic and
  therefore lives under no ambient additive, normed, or inner-product hypotheses;
  - the source-facing owner `Bifunction.subdifferentialAt` is defined on the pairing-level partial
  owners `Bifunction.subdifferential1At` and `Bifunction.subdifferential2At`, so it does not
  force Euclidean vector codomains;
- the stronger finite-dimensional assumptions belong only to `section Continuity`, where the
  Chapter 5 continuity theorems on directional derivatives and subdifferentials are invoked, and
  the resulting completeness is inferred from `FiniteDimensional.complete` rather than exposed on
  the theorem surface.

Notation evaluation:
- the source-facing saddle subdifferential notation `d(K ; u, v)` is imported from
  `Text_35_6_3` and used on theorem surfaces here.
-/

section Continuity

variable {𝕜 : Type w}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot_theorem357 : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

variable {K : U → V → WithTopBot 𝕜} {KSeq : ℕ → U → V → WithTopBot 𝕜}
variable {C : Set U} {D : Set V}

variable {u : U} {v : V}
variable {uvSeq : ℕ → U × V}

section Common

variable
    (hK_finite : (uncurry K).IsFiniteOn (C ×ˢ D))
    (hKSeq_finite : ∀ i, (uncurry (KSeq i)).IsFiniteOn (C ×ˢ D))
    (hK_concaveConvex : Bifunction.IsConcaveConvexOn 𝕜 C D K)
    (hKSeq_concaveConvex : ∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hlimit : ∀ p ∈ C ×ˢ D, Tendsto (fun i ↦ KSeq i p.1 p.2) atTop (𝓝 (K p.1 p.2)))
    (huv : (u, v) ∈ C ×ˢ D)
    (huvSeq_mem : ∀ i, uvSeq i ∈ C ×ˢ D)
    (huvSeq : Tendsto uvSeq atTop (𝓝 (u, v)))

section First

-- Proof sketch: apply the Chapter 5 upper-semicontinuity theorem to the convex sequence of
-- negated first-variable slices `fun u ↦ -KSeq i u (uvSeq i).2` on `C`, then rewrite the
-- resulting directional derivatives by the first-variable slice identity from `Text_35_5_3`.
/-- Theorem 35.7, first clause: under pointwise convergence on a relatively-open product
(`IsRelativelyOpen 𝕜 C`) for finite concave-convex saddle bifunctions on `C × D`, the first
partial directional derivative `K'(u, v; u', 0)` is lower
semicontinuous along convergent base points. -/
theorem directionalDerivativeAt_first_le_liminf_of_tendsto_on_relativelyOpen_convex
    [FiniteDimensional 𝕜 U]
    (hC_open : IsRelativelyOpen 𝕜 C)
    (u' : U) :
    directionalDerivativeAt (uncurry K) (u, v) (u', 0) ≤
      liminf
        (fun i ↦ directionalDerivativeAt (uncurry (KSeq i)) (uvSeq i) (u', 0))
        atTop := by
  sorry

end First

section Second

-- Proof sketch: apply the Chapter 5 directional-derivative semicontinuity theorem directly to
-- the convex second-variable slices `KSeq i (uvSeq i).1` on `D`, then rewrite by the second-slice
-- identity from `Text_35_5_3`.
/-- Theorem 35.7, second clause: under the relatively-open second-variable hypotheses
(`IsRelativelyOpen 𝕜 D`) and the same pointwise convergence for finite concave-convex saddle
bifunctions on `C × D`, the second partial directional derivative `K'(u, v; 0, v')` is
upper semicontinuous along convergent base points. -/
theorem limsup_directionalDerivativeAt_second_le_of_tendsto_on_relativelyOpen_convex
    [FiniteDimensional 𝕜 V]
    (hD_open : IsRelativelyOpen 𝕜 D)
    (v' : V) :
    limsup
        (fun i ↦ directionalDerivativeAt (uncurry (KSeq i)) (uvSeq i) (0, v'))
        atTop ≤
      directionalDerivativeAt (uncurry K) (u, v) (0, v') := by
  sorry

end Second

section Subdifferential

variable {YU : Type*} {YV : Type*}
variable [NormedAddCommGroup YU] [HasPairing U YU 𝕜]
variable [NormedAddCommGroup YV] [HasPairing V YV 𝕜]

-- Proof sketch: apply the Chapter 5 subdifferential-containment theorem to the negated first
-- slices and to the second slices, then combine the two one-variable containments into the
-- product inclusion for `dK`.
/-- Theorem 35.7, subdifferential clause: for every `ε > 0`, the saddle subdifferentials along the
approximating sequence are eventually contained in the Minkowski sum of `dK(u, v)` with the
closed `ε`-ball in the pairing product space. -/
theorem eventually_subdifferentialAt_subset_add_smul_unitBall_of_tendsto_on_relativelyOpen_convex
    [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V]
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀,
      d(KSeq i ; (uvSeq i).1, (uvSeq i).2) ⊆
        d(K ; u, v) + Metric.closedBall (0 : YU × YV) ε := by
  sorry

end Subdifferential

end Common

end Continuity

end Bifunction
