import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Sequences

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_25_5_1 (from Chap05) -/
noncomputable section

open Filter
open scoped Gradient Topology Pointwise Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [Preorder 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 25.5.1 is the continuity statement for single-valued
  subdifferential fibers on a relatively open convex region where the convex extended-real-valued
  function is finite. The ambient-gradient surface is only a companion on ambient-open convex
  sets, where the ordinary gradient is actually the correct owner.
- `core/canonical`: the owner abstractions already present upstream are the pairing-valued owner
  `_root_.subdifferentialAt` from Definition 23.0.6, the Chapter 5 continuity theorem
  `Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex`
  from Theorem 5.24.8, and the intrinsic-topology owner `Continuous` on the subtype `C`.
- `bridge/view`: the dual-gradient theorem is the Fréchet-Riesz transport of the ambient-open
  gradient companion through `InnerProductSpace.toDual ℝ E`.

Domain-style sampling used here:
- `_root_.subdifferentialAt` (Definition 23.0.6);
- `Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex`
  (Theorem 5.24.8), which already owns the set-valued upper-semicontinuity layer;
- `Continuous`, `SeqContinuous.continuous`, and the Chapter 10 sequence bridge
  `continuousOn_iff_tendsto_along_sequences`, which identify the canonical relative-topology
  owner surface behind sequence formulations;
- `Function.realBranch` from `Chap02.Theorem_10_4`, which already owns the finite real branch of a
  `WithTopBot ℝ`-valued function for the ambient gradient bridge;
- `Function.subdifferentialWithinAt_eq_singleton_gradient` from `Chap05.Theorem_25_1`, which shows
  that on genuine ambient-open domains the chapter already relates differentiability to singleton
  subdifferentials without any extra local wrapper;
- `InnerProductSpace.toDual` and gradient notation `∇` for the Euclidean bridge/view.

Primitive data vs derived API:
- primitive owner data: an intrinsic branch `g : C → Y` into a pairing-side codomain of the
  subdifferential owner together with singleton fibers and the eventual closed-ball containment
  owner for nearby subdifferentials;
- source hypotheses supplying that primitive containment in Corollary 25.5.1: a relatively open
  convex set `C`, convexity of `f`, finiteness on `C`, and a convergent sequence `xSeq → x` in
  `C`;
- derived API: continuity of the selected pairing-side subgradient branch on the intrinsic
  subtype `C`,
  plus the intrinsic relatively-open gradient-view bridge forms in inner-product spaces and their
  ambient-open sequence-level
  companions.

Layer target:
- `tendsto_subgradientSelection_of_eventually_subdifferentialAt_subset_add_closedBall`:
  `core/canonical` primitive sequence criterion;
- `continuous_subgradientSelection_on_relativelyOpen_convex`: `core/canonical`;
- `continuous_toDual_gradient_realBranch_on_relativelyOpen_convex_of_differentiableAt`:
  `bridge/view`;
- `continuous_gradient_realBranch_on_relativelyOpen_convex_of_differentiableAt`: `bridge/view`;
- `continuous_gradient_realBranch_on_open_convex`: ambient-open corollary;
- the three `tendsto_*` theorems below are companion sequence bridges.

Ambient-assumption minimization:
- the core theorem is pairing-based and does not assume an inner product;
- finite-dimensionality appears only because the reused Chapter 5 continuity owner theorem lives
  there;
- inner-product structure is introduced only in the gradient-view section.
- the canonical subdifferential-continuity owners in this file are scalar-generic over
  `WithTopBot 𝕜` and pairing `HasPairing E Y 𝕜`;
- real scalars appear only in the ambient gradient-view bridge, where the upstream owner
  `Function.realBranch` is intrinsically real.
-/

/-- Primitive sequence criterion for Corollary 25.5.1 at the canonical owner level: if the
subdifferentials along `xSeq` are eventually contained in arbitrarily small closed-ball
neighborhoods of the singleton fiber at `x`, then the selected branch `g (xSeq i)` converges to
`g x`. -/
theorem tendsto_subgradientSelection_of_eventually_subdifferentialAt_subset_add_closedBall
    {f : E → WithTopBot 𝕜} {C : Set E}
    {Y : Type (max u v)} [NormedAddCommGroup Y] [HasPairing E Y 𝕜]
    {g : C → Y}
    (hg_mem : ∀ x : C, g x ∈ ∂[Y]f((x : E)))
    (hsub_singleton : ∀ x : C, (∂[Y]f((x : E))).Subsingleton)
    {x : C} {xSeq : ℕ → C}
    (husc :
      ∀ ε > 0, ∃ i₀ : ℕ, ∀ i ≥ i₀,
        ∂[Y]f((xSeq i : E)) ⊆
          ∂[Y]f((x : E)) +
            Metric.closedBall (0 : Y) ε) :
    Tendsto (fun i ↦ g (xSeq i)) atTop (𝓝 (g x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨i₀, hi₀⟩ := husc (ε / 2) hε2
  refine Filter.eventually_atTop.2 ⟨i₀, ?_⟩
  intro i hi
  have hgi_mem : g (xSeq i) ∈ ∂[Y]f((xSeq i : E)) :=
    hg_mem (xSeq i)
  have hgi_add :
      g (xSeq i) ∈ ∂[Y]f((x : E)) +
        Metric.closedBall (0 : Y) (ε / 2) :=
    hi₀ i hi (by simpa using hgi_mem)
  rcases Set.mem_add.1 hgi_add with ⟨u, hu, v, hv, huv⟩
  have hu_eq : u = g x :=
    ((hsub_singleton x) (hg_mem x) hu).symm
  have hdist_v : dist v (0 : Y) ≤ ε / 2 :=
    (Metric.mem_closedBall.1 hv)
  have hdist_le : dist (g (xSeq i)) (g x) ≤ ε / 2 := by
    have hgi_eq : g (xSeq i) = g x + v := by
      have : g x + v = g (xSeq i) := by
        exact hu_eq ▸ huv
      exact this.symm
    calc
      dist (g (xSeq i)) (g x) = dist (g x + v) (g x) := by
        exact congrArg (fun t ↦ dist t (g x)) hgi_eq
      _ = dist (g x + v) (g x + (0 : Y)) := by simp
      _ = dist v (0 : Y) := dist_add_left (g x) v (0 : Y)
      _ ≤ ε / 2 := hdist_v
  exact lt_of_le_of_lt hdist_le (by linarith)

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- Companion sequence bridge for Corollary 25.5.1: on a relatively open convex region where a
convex extended-real-valued function is finite, any single-valued branch of the canonical
pairing-valued subdifferential owner is continuous along convergent sequences in that region. -/
theorem tendsto_subgradientSelection_of_tendsto_on_relativelyOpen_convex
    {f : E → WithTopBot 𝕜} {C : Set E}
    (hC_open : IsRelativelyOpen 𝕜 C) (hC_convex : Convex 𝕜 C)
    (hf_convex : f.IsConvex 𝕜)
    (hf_finite : f.IsFiniteOn C)
    {Y : Type (max u v)} [NormedAddCommGroup Y] [HasPairing E Y 𝕜]
    {g : C → Y}
    (hg_mem : ∀ x : C, g x ∈ ∂[Y]f((x : E)))
    (hsub_singleton : ∀ x : C, (∂[Y]f((x : E))).Subsingleton)
    {x : C} {xSeq : ℕ → C} (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    Tendsto (fun i ↦ g (xSeq i)) atTop (𝓝 (g x)) := by
  refine tendsto_subgradientSelection_of_eventually_subdifferentialAt_subset_add_closedBall
    hg_mem hsub_singleton ?_
  intro ε hε
  have hf_convexOn : ConvexOn 𝕜 C f := by
    simpa [Function.IsConvex, Function.IsConvexOn] using hf_convex
  obtain ⟨i₀, hi₀⟩ :=
    Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex
      (fSeq := fun _ : ℕ ↦ f) (f := f) (Y := Y)
      hC_open hf_convexOn (fun _ ↦ hf_convexOn)
      hf_finite (fun _ ↦ hf_finite) (fun y hy ↦ tendsto_const_nhds)
      x.2 (fun i ↦ (xSeq i).2) ((tendsto_subtype_rng).1 hxSeq) ε hε
  exact ⟨i₀, hi₀⟩

/-- Corollary 25.5.1, canonical owner form: on a relatively open convex region where a convex
extended-real-valued function is finite, any single-valued branch of the canonical pairing-valued
subdifferential owner is continuous on the intrinsic subtype `C`. -/
theorem continuous_subgradientSelection_on_relativelyOpen_convex
    {f : E → WithTopBot 𝕜} {C : Set E}
    (hC_open : IsRelativelyOpen 𝕜 C) (hC_convex : Convex 𝕜 C)
    (hf_convex : f.IsConvex 𝕜)
    (hf_finite : f.IsFiniteOn C)
    {Y : Type (max u v)} [NormedAddCommGroup Y] [HasPairing E Y 𝕜]
    {g : C → Y}
    (hg_mem : ∀ x : C, g x ∈ ∂[Y]f((x : E)))
    (hsub_singleton : ∀ x : C, (∂[Y]f((x : E))).Subsingleton) :
    Continuous g := by
  apply SeqContinuous.continuous
  intro y x hy
  simpa using
    tendsto_subgradientSelection_of_tendsto_on_relativelyOpen_convex
      hC_open hC_convex hf_convex hf_finite hg_mem hsub_singleton hy

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function

/-
The canonical relatively-open theorem in this file is the owner-level continuity result for
single-valued subgradient selections. The gradient bridge is kept on the same intrinsic
relative-open layer: pointwise ambient differentiability on `C` supplies singleton ambient
subdifferentials pointwise, while ambient-open formulations are downstream corollaries.
-/

/-- Corollary 25.5.1, dual-gradient bridge in intrinsic topology: on a relatively open convex set
`C`, if the finite real branch is pointwise ambient-differentiable and finite on `C`, then the
dual gradient branch carried by `InnerProductSpace.toDual ℝ E` is continuous on the intrinsic
subtype `C`. -/
theorem continuous_toDual_gradient_realBranch_on_relativelyOpen_convex_of_differentiableAt
    {f : E → WithTopBot ℝ} {C : Set E}
    (hC_open : IsRelativelyOpen ℝ C) (hC_convex : Convex ℝ C)
    (hf_convex : f.IsConvex ℝ)
    (hf_finite : f.IsFiniteOn C)
    (hfd : ∀ x, x ∈ C → DifferentiableAt ℝ f.realBranch x) :
    Continuous (fun x : C ↦ InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E))) := by
  let fExt : E → WithTopBot ℝ := Function.toWithTopBotOn f.realBranch C
  have hEqC : Set.EqOn f (fun x ↦ ((f.realBranch x : ℝ) : WithTopBot ℝ)) C := by
    intro x hx
    have hfin := hf_finite x hx
    have hneTop : f x ≠ ⊤ := ne_of_lt (mem_effectiveDomain.mp hfin.1)
    have hneBot : f x ≠ ⊥ := hfin.2
    simpa [Function.realBranch] using (EReal.coe_toReal hneTop hneBot).symm
  have hconv_C_realCoe : ConvexOn ℝ C (fun x ↦ ((f.realBranch x : ℝ) : WithTopBot ℝ)) := by
    refine ⟨hC_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx_epi : (x, f.realBranch x) ∈ epi f := by
      exact (mem_epi_restrict_iff).2 ⟨by simp, by simpa [hEqC hx]⟩
    have hy_epi : (y, f.realBranch y) ∈ epi f := by
      exact (mem_epi_restrict_iff).2 ⟨by simp, by simpa [hEqC hy]⟩
    have hmid_epi_set :
        (a • x + b • y, a * f.realBranch x + b * f.realBranch y) ∈ epi f := by
      simpa [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using
        hf_convex hx_epi hy_epi ha hb hab
    have hmid_epi :
        f (a • x + b • y) ≤ ((a * f.realBranch x + b * f.realBranch y : ℝ) : WithTopBot ℝ) := by
      exact (mem_epi_restrict_iff.1 hmid_epi_set).2
    have hmid_mem : a • x + b • y ∈ C := hC_convex hx hy ha hb hab
    have hmid_eq : f (a • x + b • y) =
        ((f.realBranch (a • x + b • y) : ℝ) : WithTopBot ℝ) :=
      hEqC hmid_mem
    exact (show ((f.realBranch (a • x + b • y) : ℝ) : WithTopBot ℝ) ≤
        ((a * f.realBranch x + b * f.realBranch y : ℝ) : WithTopBot ℝ) by
      simpa [hmid_eq] using hmid_epi)
  have hconv_C_real : ConvexOn ℝ C f.realBranch := by
    rcases hconv_C_realCoe with ⟨hC_convex', hineq⟩
    refine ⟨hC_convex', ?_⟩
    intro x hx y hy a b ha hb hab
    have hleE :
        (((f.realBranch (a • x + b • y) : ℝ) : WithTopBot ℝ)) ≤
          a • (((f.realBranch x : ℝ) : WithTopBot ℝ)) +
            b • (((f.realBranch y : ℝ) : WithTopBot ℝ)) :=
      hineq hx hy ha hb hab
    have hleCoe :
        (((f.realBranch (a • x + b • y) : ℝ) : WithTopBot ℝ)) ≤
          (((a * f.realBranch x + b * f.realBranch y : ℝ) : WithTopBot ℝ)) := by
      change (((f.realBranch (a • x + b • y) : ℝ) : WithTopBot ℝ)) ≤
        (((a : ℝ) : WithTopBot ℝ) * (((f.realBranch x : ℝ) : WithTopBot ℝ)) +
          ((b : ℝ) : WithTopBot ℝ) * (((f.realBranch y : ℝ) : WithTopBot ℝ)))
      simpa [smul_eq_mul] using hleE
    exact (WithTopBot.coe_le_coe.1 hleCoe)
  have hfExt_convex : fExt.IsConvex ℝ := by
    exact (isConvex_toWithTopBotOn_iff (C := C) (f := f.realBranch)).2 hconv_C_real
  have hfExt_finite : fExt.IsFiniteOn C := by
    intro x hx
    constructor
    · change fExt x < ⊤
      simpa [fExt, Function.toWithTopBotOn_of_mem (f := f.realBranch) (C := C) hx] using
        (WithTopBot.coe_lt_top (f.realBranch x))
    · simpa [fExt, Function.toWithTopBotOn_of_mem (f := f.realBranch) (C := C) hx] using
        (WithTopBot.coe_ne_bot (f.realBranch x))
  have hC_ri : ri[ℝ](C) = C := hC_open
  have hg_mem :
      ∀ x : C,
        (InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E))) ∈
          (∂ fExt at (x : E)) := by
    intro x
    have hx_ri : (x : E) ∈ ri[ℝ](C) := by simpa [hC_ri] using x.2
    have hfdx : DifferentiableAt ℝ f.realBranch (x : E) := hfd (x : E) x.2
    have hsingle_raw :=
      Function.subdifferentialWithinAt_eq_singleton_toDual_gradient
        hconv_C_real hx_ri hfdx
    have hsingle :
        (∂ fExt at (x : E)) =
          {InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E))} := by
      simpa [fExt, _root_.subdifferentialWithinAt] using hsingle_raw
    exact hsingle ▸ Set.mem_singleton _
  have hsub_singleton : ∀ x : C, (∂ fExt at (x : E)).Subsingleton := by
    intro x
    have hx_ri : (x : E) ∈ ri[ℝ](C) := by simpa [hC_ri] using x.2
    have hfdx : DifferentiableAt ℝ f.realBranch (x : E) := hfd (x : E) x.2
    have hsingle_raw :=
      Function.subdifferentialWithinAt_eq_singleton_toDual_gradient
        hconv_C_real hx_ri hfdx
    have hsingle :
        (∂ fExt at (x : E)) =
          {InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E))} := by
      simpa [fExt, _root_.subdifferentialWithinAt] using hsingle_raw
    exact hsingle ▸
      (Set.subsingleton_singleton :
        ({InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E))} : Set (StrongDual ℝ E)).Subsingleton)
  have hcont :
      Continuous (fun x : C ↦ InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E))) :=
    continuous_subgradientSelection_on_relativelyOpen_convex
      (f := fExt) hC_open hC_convex
      hfExt_convex hfExt_finite hg_mem hsub_singleton
  exact hcont

/-- Ambient-open corollary of the intrinsic dual-gradient bridge above. -/
theorem continuous_toDual_gradient_realBranch_on_open_convex
    {f : E → WithTopBot ℝ} {C : Set E}
    (hC_open : IsOpen C) (hC_convex : Convex ℝ C)
    (hf_convex : f.IsConvex ℝ)
    (hf_finite : f.IsFiniteOn C)
    (hfd : DifferentiableOn ℝ f.realBranch C) :
    Continuous (fun x : C ↦ InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E))) := by
  refine continuous_toDual_gradient_realBranch_on_relativelyOpen_convex_of_differentiableAt
    hC_open.isRelativelyOpen hC_convex hf_convex hf_finite ?_
  intro x hx
  exact hfd.differentiableAt (hC_open.mem_nhds hx)

/-- Companion sequence bridge for Corollary 25.5.1 in the ambient-open dual-gradient view. -/
theorem tendsto_toDual_gradient_realBranch_of_tendsto_on_open_convex
    {f : E → WithTopBot ℝ} {C : Set E}
    (hC_open : IsOpen C) (hC_convex : Convex ℝ C)
    (hf_convex : f.IsConvex ℝ)
    (hf_finite : f.IsFiniteOn C)
    (hfd : DifferentiableOn ℝ f.realBranch C)
    {x : E} (hx : x ∈ C)
    {xSeq : ℕ → E} (hxSeq_mem : ∀ i, xSeq i ∈ C)
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    Tendsto
      (fun i ↦ InnerProductSpace.toDual ℝ E (∇ f.realBranch (xSeq i)))
      atTop
      (𝓝 (InnerProductSpace.toDual ℝ E (∇ f.realBranch x))) := by
  have hcont :
      Continuous (fun y : C ↦ InnerProductSpace.toDual ℝ E (∇ f.realBranch (y : E))) :=
    continuous_toDual_gradient_realBranch_on_open_convex
      hC_open hC_convex hf_convex hf_finite hfd
  have hxSeq' : Tendsto (fun i ↦ (⟨xSeq i, hxSeq_mem i⟩ : C)) atTop (𝓝 ⟨x, hx⟩) := by
    exact (tendsto_subtype_rng).2 hxSeq
  simpa using (hcont.tendsto ⟨x, hx⟩).comp hxSeq'

/-- Corollary 25.5.1, intrinsic gradient bridge form: on a relatively open convex set `C`, if
the finite real branch is pointwise ambient-differentiable and finite on `C`, then the ambient
gradient is continuous on the intrinsic subtype `C`. -/
theorem continuous_gradient_realBranch_on_relativelyOpen_convex_of_differentiableAt
    {f : E → WithTopBot ℝ} {C : Set E}
    (hC_open : IsRelativelyOpen ℝ C) (hC_convex : Convex ℝ C)
    (hf_convex : f.IsConvex ℝ)
    (hf_finite : f.IsFiniteOn C)
    (hfd : ∀ x, x ∈ C → DifferentiableAt ℝ f.realBranch x) :
    Continuous (fun x : C ↦ ∇ f.realBranch (x : E)) := by
  have hdual :
      Continuous (fun x : C ↦ InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E))) :=
    continuous_toDual_gradient_realBranch_on_relativelyOpen_convex_of_differentiableAt
      hC_open hC_convex hf_convex hf_finite hfd
  have hpull :
      Continuous
        (fun x : C ↦
          (InnerProductSpace.toDual ℝ E).symm
            (InnerProductSpace.toDual ℝ E (∇ f.realBranch (x : E)))) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp hdual
  simpa using hpull

/-- Corollary 25.5.1, source-facing ambient-gradient form: on an open convex set `C` where the
convex function `f` is finite and the finite real branch `f.realBranch` is differentiable, the
ambient gradient is continuous on the intrinsic subtype `C`. -/
theorem continuous_gradient_realBranch_on_open_convex
    {f : E → WithTopBot ℝ} {C : Set E}
    (hC_open : IsOpen C) (hC_convex : Convex ℝ C)
    (hf_convex : f.IsConvex ℝ)
    (hf_finite : f.IsFiniteOn C)
    (hfd : DifferentiableOn ℝ f.realBranch C) :
    Continuous (fun x : C ↦ ∇ f.realBranch (x : E)) := by
  refine continuous_gradient_realBranch_on_relativelyOpen_convex_of_differentiableAt
    hC_open.isRelativelyOpen hC_convex hf_convex hf_finite ?_
  intro x hx
  exact hfd.differentiableAt (hC_open.mem_nhds hx)

/-- Companion sequence bridge for Corollary 25.5.1 in the ambient-open gradient view. -/
theorem tendsto_gradient_realBranch_of_tendsto_on_open_convex
    {f : E → WithTopBot ℝ} {C : Set E}
    (hC_open : IsOpen C) (hC_convex : Convex ℝ C)
    (hf_convex : f.IsConvex ℝ)
    (hf_finite : f.IsFiniteOn C)
    (hfd : DifferentiableOn ℝ f.realBranch C)
    {x : E} (hx : x ∈ C)
    {xSeq : ℕ → E} (hxSeq_mem : ∀ i, xSeq i ∈ C)
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) :
    Tendsto (fun i ↦ ∇ f.realBranch (xSeq i)) atTop
      (𝓝 (∇ f.realBranch x)) := by
  have hcont : Continuous (fun y : C ↦ ∇ f.realBranch (y : E)) :=
    continuous_gradient_realBranch_on_open_convex
      hC_open hC_convex hf_convex hf_finite hfd
  have hxSeq' : Tendsto (fun i ↦ (⟨xSeq i, hxSeq_mem i⟩ : C)) atTop (𝓝 ⟨x, hx⟩) := by
    exact (tendsto_subtype_rng).2 hxSeq
  simpa using (hcont.tendsto ⟨x, hx⟩).comp hxSeq'

end Function

end

/-! ### Corollary_25_5_2 (from Chap05) -/
noncomputable section

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 25.5.2 states that the differentiability locus `D` from Theorem 25.5
  is a `G_delta` subset of `interior (dom(f))`.
- `core/canonical`: the owner abstractions are mathlib's `IsGδ`, the ambient interior
  `interior (dom(f))`, and the Chapter 25 owner
  `Function.differentiabilitySetWithinInteriorDom`.
- `bridge/view`: the chapter owner from Theorem 25.5 already fixes the differentiability locus as
  the intrinsic owner `differentiabilitySetWithinInteriorDom f`; any coordinate-direction argument
  from Theorems 25.2 and 25.4 is only an internal route to this owner, not a second public
  surface.

Domain-style sampling used here:
- `Function.HasLinearDirectionalDerivativeAt` from `Chap05.Theorem_25_2`;
- `Function.twoSidedDirectionalDerivativeSet` from `Chap05.Theorem_25_4`;
- `Function.differentiabilitySetWithinInteriorDom` from `Chap05.Theorem_25_5`;
- `IsGδ.setOf_continuousAt` from `Mathlib/Topology/GDelta/MetrizableSpace`;
- `IsGδ.iInter` from mathlib's `Topology/GDelta`.

Primitive data vs derived API:
- primitive source data: a proper convex function `f : E → WithBotTop 𝕜`;
- primitive owner surfaces: `twoSidedDirectionalDerivativeSet f y` in one fixed direction and
  `differentiabilitySetWithinInteriorDom f`;
- derived API: the `IsGδ` conclusions for those intrinsic subtype sets.

Ambient-assumption minimization:
- no inner-product structure appears in the public owner
  `differentiabilitySetWithinInteriorDom f`;
- the surrounding Chapter 25 owner theorem `Function.dense_differentiabilitySetWithinInteriorDom`
  already lives on finite-dimensional normed spaces over `𝕜`, so this corollary should remain on that
  same ambient layer instead of re-specializing to Euclidean gradient infrastructure.

Layer target: `core/canonical`; the corollary stays directly on the differentiability-locus owner
from Theorem 25.5 rather than reopening a coordinate-level public interface.
-/

-- Proof sketch: first show that for each fixed direction `y`, the owner
-- `twoSidedDirectionalDerivativeSet f y` is `G_delta`; then express the intrinsic
-- differentiability locus `differentiabilitySetWithinInteriorDom f` as the finite intersection of
-- these owner sets along a finite basis and apply `IsGδ.iInter`.
/-- For a fixed direction, the intrinsic two-sided directional-derivative locus from Theorem 25.4
is a `G_delta` subset of `interior (dom(f))`. -/
theorem isGδ_twoSidedDirectionalDerivativeSet
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) (y : E) :
    IsGδ (twoSidedDirectionalDerivativeSet f y) := sorry

private theorem differentiabilitySetWithinInteriorDom_eq_iInter_twoSidedDirectionalDerivativeSet
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    differentiabilitySetWithinInteriorDom f =
      ⋂ i, twoSidedDirectionalDerivativeSet f ((Module.finBasis 𝕜 E) i) := sorry

/-- Corollary 25.5.2: for a proper convex function on a finite-dimensional normed space over `𝕜`,
the intrinsic Rockafellar locus in `interior (dom(f))` is a `G_delta` subset. -/
theorem isGδ_differentiabilitySetWithinInteriorDom
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    IsGδ (differentiabilitySetWithinInteriorDom f) := by
  rw [differentiabilitySetWithinInteriorDom_eq_iInter_twoSidedDirectionalDerivativeSet
    hf_proper hf_convex]
  exact IsGδ.iInter fun i ↦
    isGδ_twoSidedDirectionalDerivativeSet hf_proper hf_convex ((Module.finBasis 𝕜 E) i)

end Function

end

/-! ### Theorem_25_5 (from Chap05) -/
noncomputable section

open scoped Gradient Topology

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.5 studies the set `D` of points in `interior (dom(f))` where
  Rockafellar's directional differentiability criterion holds, then asserts density of `D`,
  measure-zero complement in `interior (dom(f))`, and continuity of the gradient map on `D` in
  the real inner-product bridge.
- `core/canonical`: the owner abstraction for `D` is
  `Function.HasLinearDirectionalDerivativeAt`, i.e. linearity of
  `y ↦ directionalDerivativeAt f x y` in the Chapter 25 canonical owner layer
  `f : E → WithBotTop 𝕜`.
- `bridge/view`: the proof route for clauses (1) and (2) factors through the directional owner
  `Function.twoSidedDirectionalDerivativeSet` from Theorem 25.4 in each basis direction and the
  Chapter 25 criterion of Theorem 25.2; clause (3) then adds the real inner-product gradient owner
  `∇` and the singleton-subdifferential continuity bridge of Corollary 25.5.1.

Domain-style sampling used here:
- `Function.HasLinearDirectionalDerivativeAt` and
  `Function.differentiableAt_iff_hasLinearDirectionalDerivativeAt` from `Chap05.Theorem_25_2`;
- `Function.twoSidedDirectionalDerivativeSet` and
  `Function.volume_diff_twoSidedDirectionalDerivativeSetAmbient_eq_zero` from
  `Chap05.Theorem_25_4`;
- `Function.continuous_gradient_realBranch_on_open_convex` from
  `Chap05.Corollary_25_5_1`.

Primitive data vs derived API:
- primitive source data: a proper convex function `f : E → WithBotTop 𝕜`;
- primitive owner surface: the canonical intrinsic Rockafellar-locus
  `differentiabilitySetWithinInteriorDom f`;
- derived API: its density, its ambient measure-zero complement statement, and, after adding the
  real Riesz-identification layer, continuity of the restricted gradient map.

Ambient-assumption minimization:
- the owner definitions below stay at the primitive module/topology layer required by
  `Function.HasLinearDirectionalDerivativeAt`;
- clauses (1) and (2) move to the scalar-generic finite-dimensional normed-space layer already
  used by Chapter 25 directional-derivative owners;
- only clause (3) uses the Euclidean gradient owner `∇`, so only that clause is kept in the
  stronger finite-dimensional real inner-product setting.

Layer target: `source-facing`, stated directly on the canonical subtype set inside
`interior (dom(f))` rather than through a parallel local alias.
-/

/- The intrinsic Rockafellar-locus `D` from Theorem 25.5. -/
/-- The set of points of `interior (dom(f))` where Rockafellar's directional criterion
(`HasLinearDirectionalDerivativeAt`) holds. For finite convex real-valued branches, this matches
ordinary differentiability via Theorem 25.2. -/
def differentiabilitySetWithinInteriorDom (f : E → WithBotTop 𝕜) :
    Set (interior (dom(f))) :=
  {x | f.HasLinearDirectionalDerivativeAt (x : E)}

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [OrderTopology (WithBotTop 𝕜)] in
@[simp] theorem mem_differentiabilitySetWithinInteriorDom
    {f : E → WithBotTop 𝕜} {x : interior (dom(f))} :
    x ∈ differentiabilitySetWithinInteriorDom f ↔
      f.HasLinearDirectionalDerivativeAt (x : E) :=
  Iff.rfl

/-- Ambient owner of `differentiabilitySetWithinInteriorDom`, keeping theorem surfaces free from
subtype-image coercion noise. -/
def differentiabilitySetWithinInteriorDomAmbient (f : E → WithBotTop 𝕜) : Set E :=
  {x | x ∈ interior (dom(f)) ∧ f.HasLinearDirectionalDerivativeAt x}

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [OrderTopology (WithBotTop 𝕜)] in
@[simp] theorem mem_differentiabilitySetWithinInteriorDomAmbient
    {f : E → WithBotTop 𝕜} {x : E} :
    x ∈ differentiabilitySetWithinInteriorDomAmbient f ↔
      x ∈ interior (dom(f)) ∧ f.HasLinearDirectionalDerivativeAt x :=
  Iff.rfl

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [OrderTopology (WithBotTop 𝕜)] in
theorem differentiabilitySetWithinInteriorDomAmbient_eq_image
    {f : E → WithBotTop 𝕜} :
    differentiabilitySetWithinInteriorDomAmbient f =
      Subtype.val '' differentiabilitySetWithinInteriorDom f := by
  ext x
  constructor
  · rintro ⟨hx_int, hx_diff⟩
    exact ⟨⟨x, hx_int⟩, hx_diff, rfl⟩
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x'.2, hx'⟩

end Function

end

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function

-- Proof sketch: choose a finite basis of `E`, apply Theorem 25.4 to each basis
-- direction to obtain dense two-sided directional-derivative sets with measure-zero complements,
-- intersect those finitely many dense sets, and use Theorem 25.2 to identify that finite
-- intersection with `differentiabilitySetWithinInteriorDom f`.
/-- Theorem 25.5 (1): for a proper convex function on a finite-dimensional normed space over
`𝕜`, the intrinsic Rockafellar-locus `D` is dense in `interior (dom(f))`. -/
theorem dense_differentiabilitySetWithinInteriorDom
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    Dense (differentiabilitySetWithinInteriorDom f) := sorry

-- Proof sketch: as in clause (1), express
-- `differentiabilitySetWithinInteriorDom f` as the
-- finite intersection of the basis-direction two-sided directional-derivative sets from Theorem
-- 25.4, then take the finite union of their measure-zero complements inside `interior (dom(f))`.
/-- Theorem 25.5 (2): for any additive Haar measure on a finite-dimensional normed space over
`𝕜`, the complement of the intrinsic Rockafellar-locus `D` in `interior (dom(f))` has measure
zero. -/
theorem volume_diff_differentiabilitySetWithinInteriorDom_eq_zero
    [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : E → WithBotTop 𝕜} (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    μ
        ((interior (dom(f))) \
          differentiabilitySetWithinInteriorDomAmbient f) =
      0 := sorry

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function

-- Proof sketch: on
-- `differentiabilitySetWithinInteriorDom f`, Theorem 25.1 identifies
-- the
-- subdifferential with the singleton carried by the gradient of `f.realBranch`; Corollary 25.5.1
-- then gives continuity of that singleton branch on the open convex set `interior (dom(f))`,
-- which restricts to continuity of the gradient map on the intrinsic subtype `D`.
/-- Theorem 25.5 (3): the gradient mapping of the finite real branch is continuous on the
Rockafellar-locus `D` in the real inner-product bridge. -/
theorem continuous_gradientOn_differentiabilitySetWithinInteriorDom
    {f : E → WithBotTop ℝ} (hf_proper : f.IsProper) (hf_convex : f.IsConvex ℝ) :
    Continuous
      (fun x : differentiabilitySetWithinInteriorDom f ↦
        ∇ f.realBranch (x : E)) := sorry

end Function

end
