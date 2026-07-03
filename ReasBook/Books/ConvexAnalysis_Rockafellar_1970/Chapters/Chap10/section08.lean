import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_10_8_1 (from Chap02) -/
section

open scoped Rockafellar Topology
open Set
open Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
  [OrderTopology 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 10.8.1 on a finite-dimensional normed ambient space over `𝕜` fixes a
  relatively open convex set `C`, a finite convex
  function `f` on `C`, and a sequence of finite convex functions `fSeq` on `C` satisfying the
  pointwise upper-limit inequality `limsup fSeq i x ≤ f x`. It concludes an eventual uniform upper
  bound `fSeq i x ≤ f x + ε` on each compact subset `S ⊆ C`, with the closed-bounded
  finite-dimensional specialization provided as a downstream bridge theorem.
- `core/canonical`: the relevant owner abstractions are the chapter relative-openness owner
  `IsRelativelyOpen 𝕜 C`, `ConvexOn`,
  the owner convergence theorem
  `convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit`, the compact-subset bridge
  `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact`, closedness `IsClosed`,
  boundedness `Bornology.IsBounded`, and the sequence limsup expressed on the canonical extended
  order layer as
  `limsup (fun i ↦ (fSeq i x : WithBotTop 𝕜)) atTop ≤ (f x : WithBotTop 𝕜)`.
- `bridge/view`: the proof route passes through Theorem 10.8 by replacing `fSeq i` with the
  canonical pointwise supremum `fSeq i ⊔ f`, using `ConvexOn.sup`; the public statement stays
  source-facing as an eventual one-sided uniform estimate instead of packaging that auxiliary
  sequence.

Domain-style sampling used here:
- `IsRelativelyOpen 𝕜 C` from `Text_6_11`;
- `ConvexOn 𝕜 C` for finite convex `𝕜`-valued functions on `C`;
- `ConvexOn.sup` for the auxiliary upper envelope `fSeq i ⊔ f`;
- `convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit` and
  `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact` from Theorem 10.8 and mathlib;
- `tendsto_of_le_liminf_of_limsup_le`, `le_liminf_iff'`, and `limsup_le_iff'` for converting the
  one-sided limsup hypothesis on `fSeq` into pointwise convergence of the auxiliary sequence
  `fSeq i ⊔ f`;
- `IsCompact` as the canonical intrinsic owner for subset control, with
  `Metric.isCompact_of_isClosed_isBounded` used only in the bridge specialization.

Primitive data vs derived API:
- primitive inputs: the relatively open set `C`, the convex function `f`, the convex sequence
  `fSeq`, the pointwise limsup upper bound on `C`, and a compact subset `S ⊆ C`;
- derived API: eventual uniform domination of `fSeq` by `f + ε` on `S`; the closed-bounded
  finite-dimensional form is derived from compactness.

Layer target: `source-facing`, centered on the intrinsic compact-subset owner and the chapter's
relative-openness owner `IsRelativelyOpen 𝕜 C`; the textbook closed-bounded finite-dimensional
phrasing appears as a corollary bridge.
-/

-- Proof sketch: define `g i = fSeq i ⊔ f`. Each `g i` is finite and convex on `C` by
-- `ConvexOn.sup`, and the limsup hypothesis together with the constant lower bound
-- `f x ≤ g i x` forces `g i x → f x` for every `x ∈ C` via the liminf/limsup owner theorem
-- `tendsto_of_le_liminf_of_limsup_le`. Apply the owner theorem
-- `convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit` and then pass to the compact-set
-- consequence via `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact`; for large `i`,
-- the estimate `g i x ≤ f x + ε` implies
-- `fSeq i x ≤ f x + ε`.
/-- Canonical compact-subset form of Corollary 10.8.1: on a finite-dimensional normed ambient
space over `𝕜`, if `f` is convex on a relatively open convex set `C` and `fSeq` is a sequence of
convex functions on `C` with pointwise `limsup (fSeq i x) ≤ f x` on the
`WithBotTop 𝕜` codomain layer, then for every compact subset `S ⊆ C` and every `ε > 0`,
eventually `fSeq i x ≤ f x + ε` uniformly on `S`. -/
theorem eventually_le_add_of_limsup_le_of_convexOn_on_compact
    (fSeq : ℕ → E → 𝕜) (f : E → 𝕜) {C S : Set E} (hC_open : IsRelativelyOpen 𝕜 C)
    (hf_convex : ConvexOn 𝕜 C f) (hfSeq_convex : ∀ i, ConvexOn 𝕜 C (fSeq i))
    (hlimsup : ∀ x ∈ C,
      limsup (fun i ↦ (fSeq i x : WithBotTop 𝕜)) atTop ≤ (f x : WithBotTop 𝕜))
    (hS_compact : IsCompact S) (hS_subset : S ⊆ C)
    (ε : 𝕜) (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x ∈ S, fSeq i x ≤ f x + ε := by
  let g : ℕ → E → 𝕜 := fun i ↦ fSeq i ⊔ f
  have hf_le_g : ∀ i x, f x ≤ g i x := fun i x ↦ le_max_right (fSeq i x) (f x)
  have hSeq_le_g : ∀ i x, fSeq i x ≤ g i x := fun i x ↦ le_max_left (fSeq i x) (f x)
  have hg_convex : ∀ i, ConvexOn 𝕜 C (g i) := fun i ↦ (hfSeq_convex i).sup hf_convex
  have hg_tendsto : ∀ x ∈ C, Tendsto (fun i ↦ g i x) atTop (𝓝 (f x)) := by
    intro x hx
    have hg_bddAbove : atTop.IsBoundedUnder (· ≤ ·) (fun i ↦ g i x) := by
      refine ⟨f x + 1, ?_⟩
      change ∀ᶠ i in atTop, g i x ≤ f x + 1
      have hupper : ∀ᶠ i in atTop, (fSeq i x : WithBotTop 𝕜) < ((f x + 1 : 𝕜) : WithBotTop 𝕜) := by
        exact eventually_lt_of_limsup_lt
          (lt_of_le_of_lt (hlimsup x hx)
            (WithBotTop.coe_lt_coe.2 (lt_add_of_pos_right (f x) zero_lt_one)))
      filter_upwards [hupper] with i hi
      exact max_le (le_of_lt (by simpa using hi)) (by linarith)
    have hg_bddBelow : atTop.IsBoundedUnder (· ≥ ·) (fun i ↦ g i x) := by
      refine ⟨f x, ?_⟩
      change ∀ᶠ i in atTop, f x ≤ g i x
      exact .of_forall fun i ↦ hf_le_g i x
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ hg_bddAbove hg_bddBelow
    · exact (le_liminf_iff' hg_bddAbove.isCoboundedUnder_ge hg_bddBelow).2 fun y hy ↦
        .of_forall fun i ↦ hy.le.trans (hf_le_g i x)
    · refine (limsup_le_iff' hg_bddBelow.isCoboundedUnder_le hg_bddAbove).2 fun y hy ↦ ?_
      have hupper : ∀ᶠ i in atTop, (fSeq i x : WithBotTop 𝕜) < (y : WithBotTop 𝕜) := by
        exact eventually_lt_of_limsup_lt
          (lt_of_le_of_lt (hlimsup x hx) (by simpa using hy))
      filter_upwards [hupper] with i hi
      exact max_le (le_of_lt (by simpa using hi)) hy.le
  have hg_loc : TendstoLocallyUniformlyOn g f atTop C :=
    (convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit
      g hC_open hg_convex hg_tendsto).2
  have hg_uniform : TendstoUniformlyOn g f atTop S :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS_compact).1 <|
      hg_loc.mono hS_subset
  have hf_const_uniform : TendstoUniformlyOn (fun _ : ℕ => f) f atTop S := by
    intro u hu
    exact .of_forall fun _ x hx => refl_mem_uniformity hu
  have hsub_uniform : TendstoUniformlyOn (fun i x ↦ g i x - f x) (fun _ ↦ (0 : 𝕜)) atTop S := by
    simpa using hg_uniform.sub hf_const_uniform
  have hsub_eventually : ∀ᶠ i in atTop, ∀ x ∈ S, g i x - f x ≤ ε :=
    TendstoUniformlyOn.eventually_forall_le (u := (0 : 𝕜)) (v := ε)
      hε hsub_uniform (by intro x hx; simp)
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hsub_eventually
  refine ⟨i₀, ?_⟩
  intro i hi x hx
  have hmax_le : max (fSeq i x) (f x) ≤ f x + ε := by
    have hsub_le : max (fSeq i x) (f x) - f x ≤ ε := by
      simpa [g] using hi₀ i hi x hx
    linarith
  exact (hSeq_le_g i x).trans hmax_le

end

section

open scoped Rockafellar Topology
open Set
open Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
  [OrderTopology 𝕜] [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Corollary 10.8.1 in the textbook closed-bounded finite-dimensional form. This is the
closed-bounded bridge of the canonical compact-subset theorem
`eventually_le_add_of_limsup_le_of_convexOn_on_compact`. -/
theorem eventually_le_add_of_limsup_le_of_convexOn_on_closed_bounded
    (fSeq : ℕ → E → 𝕜) (f : E → 𝕜) {C S : Set E} (hC_open : IsRelativelyOpen 𝕜 C)
    (hf_convex : ConvexOn 𝕜 C f) (hfSeq_convex : ∀ i, ConvexOn 𝕜 C (fSeq i))
    (hlimsup : ∀ x ∈ C,
      limsup (fun i ↦ (fSeq i x : WithBotTop 𝕜)) atTop ≤ (f x : WithBotTop 𝕜))
    (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S) (hS_subset : S ⊆ C)
    (ε : 𝕜) (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x ∈ S, fSeq i x ≤ f x + ε :=
  letI : ProperSpace E := FiniteDimensional.proper (𝕜 := 𝕜) (E := E)
  eventually_le_add_of_limsup_le_of_convexOn_on_compact
    fSeq f hC_open hf_convex hfSeq_convex hlimsup
    (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded) hS_subset ε hε

end

/-! ### Theorem_10_8 (from Chap02) -/
section

open scoped Rockafellar Topology
open Set
open Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable (fSeq : ℕ → E → 𝕜) {C : Set E} (hC_open : IsRelativelyOpen 𝕜 C)
  (hf_convex : ∀ i, ConvexOn 𝕜 C (fSeq i))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.8 starts with a relatively open convex set `C`, a sequence of
  convex functions on `C`, and pointwise convergence on a subset `C' ⊆ C` dense in `C`. It
  concludes existence of a convex pointwise limit on all of `C` together with local uniform
  convergence on `C`.
- `core/canonical`: the owner abstractions are the chapter owner
  `IsRelativelyOpen 𝕜 C`, `ConvexOn`, pointwise
  convergence `Tendsto (fun i ↦ f i x) atTop (𝓝 l)`, relative density written as `C' ⊆ C`
  together with `C ⊆ intrinsicClosure 𝕜 C'`, and mathlib's owner predicate
  `TendstoLocallyUniformlyOn`.
- `bridge/view`: Rockafellar's phrase "the limit exists and is finite" is rendered here by a
  `𝕜`-valued function `f : E → 𝕜` together with pointwise convergence to `f`.

Domain-style sampling used here:
- `IsRelativelyOpen 𝕜 C` (chapter owner surface for relative openness);
- `ConvexOn 𝕜 C`;
- `intrinsicClosure 𝕜` for the relative-density hypothesis `C' ⊆ C` and
  `C ⊆ intrinsicClosure 𝕜 C'`;
- `Tendsto ... atTop (𝓝 ...)` for pointwise convergence;
- `TendstoLocallyUniformlyOn` as the canonical owner for convergence on `C`.
- `NormedAddCommGroup`, `NormedSpace`, and `FiniteDimensional` for the ambient layer where
  Chapter 10's local-uniform convex convergence results are formulated.

Primitive data vs derived API:
- primitive inputs: the relative-openness owner `IsRelativelyOpen 𝕜 C`, the sequence `fSeq`,
  convexity of each `fSeq i`
  on `C`, a dense subset `C' ⊆ C`, and pointwise convergence on `C'`;
- derived API: existence of a `𝕜`-valued convex limit on `C` together with the owner predicate
  `TendstoLocallyUniformlyOn fSeq f atTop C`.

Layer target: `source-facing`, with the dense-subset theorem centered on the canonical locally
uniform owner and the pure pointwise conclusion kept only as a companion view.
-/

include hC_open hf_convex

-- Proof sketch: obtain local uniform Cauchy control from the dense-subset convergence assumptions,
-- hence pointwise Cauchy at every point of `C`. Define the `𝕜`-valued limit function by these
-- pointwise limits; convexity is preserved by
-- passing to the limit in the convexity inequality.
/-- Theorem 10.8 in canonical owner form: if a sequence of convex functions on a relatively open
convex set `C` has pointwise limits on a subset `C' ⊆ C` whose intrinsic closure contains `C`,
then there is a `𝕜`-valued convex function on `C` to which the sequence converges locally
uniformly on `C`. -/
theorem exists_convex_tendstoLocallyUniformlyOn_of_dense_pointwise
    {C' : Set E} (hC'_subset : C' ⊆ C) (hC'_dense : C ⊆ intrinsicClosure 𝕜 C')
    (hlimit_dense : ∀ x ∈ C', ∃ l : 𝕜, Tendsto (fun i ↦ fSeq i x) atTop (𝓝 l)) :
    ∃ f : E → 𝕜, ConvexOn 𝕜 C f ∧ TendstoLocallyUniformlyOn fSeq f atTop C := sorry

-- Proof sketch: apply the dense-subset theorem with `C' = C`. Then use uniqueness of limits in the
-- Hausdorff codomain `𝕜` to identify the produced limit with the prescribed pointwise limit `f`.
/-- Companion specialization of Theorem 10.8: if the pointwise limit on `C` is already specified
as a `𝕜`-valued function `f`, then `f` is convex on `C` and the convergence is locally uniform on
`C`. -/
theorem convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit
    {f : E → 𝕜} (hlimit : ∀ x ∈ C, Tendsto (fun i ↦ fSeq i x) atTop (𝓝 (f x))) :
    ConvexOn 𝕜 C f ∧ TendstoLocallyUniformlyOn fSeq f atTop C := by
  obtain ⟨g, hg_convex, hg_tendsto⟩ :=
    exists_convex_tendstoLocallyUniformlyOn_of_dense_pointwise
      fSeq hC_open hf_convex Subset.rfl subset_intrinsicClosure (fun x hx ↦ ⟨f x, hlimit x hx⟩)
  have hgf : C.EqOn g f := fun x hx ↦
    tendsto_nhds_unique (hg_tendsto.tendsto_at hx) (hlimit x hx)
  exact ⟨hg_convex.congr hgf, hg_tendsto.congr_right hgf⟩

omit hC_open hf_convex

end
