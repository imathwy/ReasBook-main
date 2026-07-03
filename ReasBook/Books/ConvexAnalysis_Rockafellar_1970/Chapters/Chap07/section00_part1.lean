import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_7_0_1 (from Chap02) -/
section

open Filter
open scoped Topology

/-!
Source/core/bridge triage:

- `source-facing`: the item defines lower semicontinuity at a point for a function
  `f : s → [-∞, +∞]` by a sequential liminf inequality.
- `core/canonical`: for a subset domain, the owner abstraction is
  `LowerSemicontinuousWithinAt` (relative topology).
- `bridge/view`: the equivalent liminf formulation is the standard theorem
  `lowerSemicontinuousWithinAt_iff_le_liminf`; the textbook sequence formulation is recorded
  below as a source-facing companion theorem.
- Layer target: the relative theorem is `core/canonical`; the ambient-domain theorem is a thin
  specialization to `s = univ`.

Mathlib sampling used here:
- `LowerSemicontinuousWithinAt`;
- `lowerSemicontinuousWithinAt_iff_le_liminf`;
- `mem_closure_iff_seq_limit`;
- `Filter.liminf`.
-/

/- Text 7.0.1: for a function defined on a subset `s`, lower semicontinuity at a point relative
   to `s` is the canonical notion `LowerSemicontinuousWithinAt`. -/
recall LowerSemicontinuousWithinAt

/- The liminf characterization of lower semicontinuity within a set is the standard theorem
`f x ≤ liminf f (𝓝[s] x)`. -/
recall lowerSemicontinuousWithinAt_iff_le_liminf

universe u v

variable {α : Type u} [TopologicalSpace α]
variable {γ : Type v}

/-- Filter-map liminf consequence of the canonical owner `LowerSemicontinuousWithinAt`. -/
theorem LowerSemicontinuousWithinAt.le_liminf_comp [ConditionallyCompleteLinearOrderBot γ]
    [OrderTop γ]
    {s : Set α} {f : α → γ} {x : α}
    (hx : LowerSemicontinuousWithinAt f s x) {ι : Type*} {l : Filter ι} {u : ι → α}
    (hu : Tendsto u l (𝓝[s] x)) :
    f x ≤ liminf (f ∘ u) l := by
  have h_le : f x ≤ liminf f (𝓝[s] x) := by
    refine (Filter.le_liminf_iff).2 ?_
    intro y hy
    exact (lowerSemicontinuousWithinAt_iff.mp hx) y hy
  have h_liminf :
      liminf f (𝓝[s] x) ≤ liminf (f ∘ u) l := by
    simpa [liminf_comp] using
      (liminf_le_liminf_of_le hu : liminf f (𝓝[s] x) ≤ liminf f (map u l))
  exact h_le.trans h_liminf

/-- Filter-level bridge: `LowerSemicontinuousWithinAt` is equivalent to the liminf inequality
along every map/filter converging to `𝓝[s] x`. -/
theorem lowerSemicontinuousWithinAt_iff_le_liminf_comp [ConditionallyCompleteLinearOrderBot γ]
    [OrderTop γ]
    {s : Set α} {f : α → γ} {x : α} :
    LowerSemicontinuousWithinAt f s x ↔
      ∀ {ι : Type u} {l : Filter ι} {u : ι → α},
        Tendsto u l (𝓝[s] x) → f x ≤ liminf (f ∘ u) l := by
  constructor
  · intro hx _ _ _ hu
    exact hx.le_liminf_comp hu
  · intro h
    refine LowerSemicontinuousWithinAt.of_frequently ?_
    intro y hy_frequently
    have hself : f x ≤ liminf (f ∘ (fun t : α ↦ t)) (𝓝[s] x) :=
      h (l := 𝓝[s] x) (u := fun t : α ↦ t) tendsto_id
    have hle : liminf (f ∘ (fun t : α ↦ t)) (𝓝[s] x) ≤ y := by
      exact liminf_le_of_frequently_le hy_frequently
    exact hself.trans hle

/-- Sequence-liminf consequence of the canonical owner `LowerSemicontinuousWithinAt`. -/
theorem LowerSemicontinuousWithinAt.seq_le_liminf [ConditionallyCompleteLinearOrderBot γ]
    [OrderTop γ]
    {s : Set α} {f : α → γ} {x : α}
    (hx : LowerSemicontinuousWithinAt f s x) :
    ∀ u : ℕ → α, Tendsto u atTop (𝓝[s] x) → f x ≤ liminf (f ∘ u) atTop := by
  intro u hu
  exact hx.le_liminf_comp hu

-- Proof sketch for the converse: apply the owner-side frequent-value criterion
-- `LowerSemicontinuousWithinAt.of_frequently`, rewrite it as an ambient closure statement of a
-- relative sublevel set, and use the Fréchet-Urysohn sequential characterization of closure.
/-- In Fréchet-Urysohn spaces, the textbook sequence-liminf criterion implies
`LowerSemicontinuousWithinAt`. -/
theorem lowerSemicontinuousWithinAt_of_seq_le_liminf [ConditionallyCompleteLinearOrderBot γ]
    [FrechetUrysohnSpace α]
    {s : Set α} {f : α → γ} {x : α}
    (hseq : ∀ u : ℕ → α, Tendsto u atTop (𝓝[s] x) → f x ≤ liminf (f ∘ u) atTop) :
    LowerSemicontinuousWithinAt f s x := by
  refine LowerSemicontinuousWithinAt.of_frequently fun y hy_frequently ↦ ?_
  have hx_closure : x ∈ closure (s ∩ {z : α | f z ≤ y}) :=
    mem_closure_iff_frequently.2 <|
      (frequently_nhdsWithin_iff.1 hy_frequently).mono fun z hz ↦ ⟨hz.2, hz.1⟩
  rcases mem_closure_iff_seq_limit.1 hx_closure with ⟨u, hu_mem, hu_tendsto⟩
  have hu_within : Tendsto u atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu_tendsto
      (Eventually.of_forall fun n ↦ (hu_mem n).1)
  exact (hseq u hu_within).trans <|
    liminf_le_of_frequently_le <| Frequently.of_forall fun n ↦ (hu_mem n).2

/-- The textbook sequential criterion for lower semicontinuity relative to a subset is equivalent
to the canonical within-set formulation. -/
theorem lowerSemicontinuousWithinAt_iff_seq_le_liminf [ConditionallyCompleteLinearOrderBot γ]
    [OrderTop γ]
    [FrechetUrysohnSpace α]
    {s : Set α} {f : α → γ} {x : α} :
    LowerSemicontinuousWithinAt f s x ↔
      ∀ u : ℕ → α, Tendsto u atTop (𝓝[s] x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · exact fun hx ↦ hx.seq_le_liminf
  · exact lowerSemicontinuousWithinAt_of_seq_le_liminf

/-- Ambient-domain specialization (`s = univ`) of
`lowerSemicontinuousWithinAt_iff_le_liminf_comp`. -/
theorem lowerSemicontinuousAt_iff_le_liminf_comp [ConditionallyCompleteLinearOrderBot γ]
    [OrderTop γ]
    {f : α → γ} {x : α} :
    LowerSemicontinuousAt f x ↔
      ∀ {ι : Type u} {l : Filter ι} {u : ι → α},
        Tendsto u l (𝓝 x) → f x ≤ liminf (f ∘ u) l := by
  simpa [lowerSemicontinuousWithinAt_univ_iff, nhdsWithin_univ] using
    (lowerSemicontinuousWithinAt_iff_le_liminf_comp (s := (Set.univ : Set α)) (f := f) (x := x))

/-- Sequence-liminf consequence of `LowerSemicontinuousAt` (ambient-domain case). -/
theorem LowerSemicontinuousAt.seq_le_liminf [ConditionallyCompleteLinearOrderBot γ]
    [OrderTop γ]
    {f : α → γ} {x : α}
    (hx : LowerSemicontinuousAt f x) :
    ∀ u : ℕ → α, Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  simpa [nhdsWithin_univ] using
    (hx.lowerSemicontinuousWithinAt (s := Set.univ)).seq_le_liminf

/-- Ambient-domain specialization (`s = univ`) of
`lowerSemicontinuousWithinAt_iff_seq_le_liminf`. -/
theorem lowerSemicontinuousAt_iff_seq_le_liminf [ConditionallyCompleteLinearOrderBot γ]
    [OrderTop γ]
    [FrechetUrysohnSpace α]
    {f : α → γ} {x : α} :
    LowerSemicontinuousAt f x ↔
      ∀ u : ℕ → α, Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  simpa [lowerSemicontinuousWithinAt_univ_iff] using
    (lowerSemicontinuousWithinAt_iff_seq_le_liminf (s := (Set.univ : Set α)) (f := f) (x := x))

theorem lowerSemicontinuousAt_of_seq_le_liminf [ConditionallyCompleteLinearOrderBot γ]
    [FrechetUrysohnSpace α]
    {f : α → γ} {x : α}
    (hseq : ∀ u : ℕ → α, Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop) :
    LowerSemicontinuousAt f x := by
  rw [← lowerSemicontinuousWithinAt_univ_iff]
  refine lowerSemicontinuousWithinAt_of_seq_le_liminf (s := (Set.univ : Set α)) ?_
  intro u hu
  have hu' : Tendsto u atTop (𝓝 x) := by
    simpa [nhdsWithin_univ] using hu
  exact hseq u hu'

end

/-! ### Text_7_0_2 (from Chap02) -/
/- 
Source/core/bridge triage:
- `source-facing`: Text 7.0.2 defines upper semicontinuity at a point `x` relative to a subset `S`
  by the sequence condition `f x ≥ limsup f (x_i)` for every sequence in `S` converging to `x`,
  and then rewrites it as a limsup-over-nearby-points condition.
- `core/canonical`: the owner abstraction in mathlib for upper semicontinuity relative to a set is
  `UpperSemicontinuousWithinAt`.
- `bridge/view`: the filter-based limsup reformulation is the canonical theorem
  `upperSemicontinuousWithinAt_iff_limsup_le`, while the textbook sequential formulation is
  recorded below as a thin source-facing companion theorem. The source specializes to `ℝ^n`, but
  the sequential bridge only uses the Fréchet-Urysohn sequential-closure layer of the ambient
  topology and the bounded conditionally-complete linear order layer (for instance
  `WithTopBot α`) needed for `limsup`.
- Primitive data vs derived API: the primitive notion is the within-set semicontinuity predicate;
  the limsup inequality and sequential criterion are derived owner API.
- Layer target: the main entry is `core/canonical`, while the equivalence is a `bridge/view`
  recall of the canonical characterization theorem together with a source-facing sequential bridge.
- Mathlib sampling used here:
  `UpperSemicontinuousWithinAt`,
  `upperSemicontinuousWithinAt_iff_limsup_le`,
  `frequently_nhdsWithin_iff`,
  `mem_closure_iff_seq_limit`.
-/

/- Text 7.0.2: the textbook notion that `f` is upper semi-continuous at `x` relative to `S`,
expressed by the sequence inequality `f x ≥ limsup f (x_i)` for every sequence `x_i ∈ S` with
`x_i → x`, is the canonical mathlib notion `UpperSemicontinuousWithinAt`. -/
recall UpperSemicontinuousWithinAt

/- The textbook limsup reformulation is the standard filter characterization of upper
semicontinuity within a set. -/
recall upperSemicontinuousWithinAt_iff_limsup_le

section

variable {α : Type*} [TopologicalSpace α]
variable {γ : Type*} [ConditionallyCompleteLinearOrder γ] [BoundedOrder γ]

open scoped Topology
open Filter

-- Owner-level bridge: upper semicontinuity within `S` controls limsup along any filter-map
-- converging to `𝓝[S] x`. This is the primitive filter layer; the sequential theorem below is a
-- source-facing specialization.
/-- If `f` is upper semicontinuous at `x` relative to `S`, then along any map `u` converging to
`𝓝[S] x` the limsup of `f ∘ u` is bounded above by `f x`. -/
theorem UpperSemicontinuousWithinAt.limsup_comp_le {S : Set α} {f : α → γ} {x : α}
    (husc : UpperSemicontinuousWithinAt f S x) {ι : Type*} {l : Filter ι} {u : ι → α}
    (hu : Tendsto u l (𝓝[S] x)) :
    limsup (f ∘ u) l ≤ f x := by
  rw [Filter.limsup_le_iff]
  intro y hy
  exact hu <| (upperSemicontinuousWithinAt_iff.1 husc) y hy

/-- Weak-order owner bridge for within-set upper semicontinuity: at the
`ConditionallyCompleteLinearOrder`/`BoundedOrder` codomain layer, the owner predicate is equivalent
to the within-filter limsup inequality. Unlike mathlib's
`upperSemicontinuousWithinAt_iff_limsup_le`, this does not require `CompleteLinearOrder`. -/
theorem upperSemicontinuousWithinAt_iff_limsup_within_le {S : Set α} {f : α → γ} {x : α} :
    UpperSemicontinuousWithinAt f S x ↔ limsup f (𝓝[S] x) ≤ f x := by
  constructor
  · intro husc
    rw [Filter.limsup_le_iff]
    intro y hy
    exact (upperSemicontinuousWithinAt_iff.1 husc) y hy
  · intro h_limsup
    rw [upperSemicontinuousWithinAt_iff]
    intro y hy
    exact Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt h_limsup hy)

/-- Ambient-domain weak-order bridge (`S = univ`) of
`upperSemicontinuousWithinAt_iff_limsup_within_le`. -/
theorem upperSemicontinuousAt_iff_limsup_nhds_le {f : α → γ} {x : α} :
    UpperSemicontinuousAt f x ↔ limsup f (𝓝 x) ≤ f x := by
  simpa [upperSemicontinuousWithinAt_univ_iff, nhdsWithin_univ] using
    (upperSemicontinuousWithinAt_iff_limsup_within_le (S := (Set.univ : Set α)))

section

variable [FrechetUrysohnSpace α]

-- Proof sketch: the owner-level filter bridge above gives the sequence direction immediately.
-- For the converse, use the frequent-value characterization of `UpperSemicontinuousWithinAt`,
-- rewrite the frequent witness as a closure statement for the upper-level set inside `S`, and
-- apply the Fréchet-Urysohn sequence characterization of closure.
/-- The intrinsic sequential criterion for upper semicontinuity relative to a subset (sequences
converging to `𝓝[S] x`) is equivalent to the canonical within-set formulation. -/
theorem upperSemicontinuousWithinAt_iff_seq_limsup_le {S : Set α} {f : α → γ} {x : α} :
    UpperSemicontinuousWithinAt f S x ↔
      ∀ u : ℕ → α, Tendsto u atTop (𝓝[S] x) → limsup (f ∘ u) atTop ≤ f x := by
  constructor
  · intro husc u hu_within
    exact husc.limsup_comp_le hu_within
  · intro hseq
    refine UpperSemicontinuousWithinAt.of_frequently fun y hfreq ↦ ?_
    have hx_closure : x ∈ closure (S ∩ {z | y ≤ f z}) :=
      mem_closure_iff_frequently.2 <|
        (frequently_nhdsWithin_iff.1 hfreq).mono fun z hz ↦ ⟨hz.2, hz.1⟩
    rcases mem_closure_iff_seq_limit.1 hx_closure with ⟨u, hu_mem, hu_tendsto⟩
    have huS : ∀ n, u n ∈ S := fun n ↦ (hu_mem n).1
    have hu_within : Tendsto u atTop (𝓝[S] x) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu_tendsto
        (Eventually.of_forall huS)
    have hu_limsup : y ≤ limsup (f ∘ u) atTop :=
      le_limsup_of_frequently_le <| .of_forall fun n ↦ (hu_mem n).2
    exact hu_limsup.trans <| hseq u hu_within

/-- Ambient-domain specialization (`S = univ`) of
`upperSemicontinuousWithinAt_iff_seq_limsup_le`. -/
theorem upperSemicontinuousAt_iff_seq_limsup_le {f : α → γ} {x : α} :
    UpperSemicontinuousAt f x ↔
      ∀ u : ℕ → α, Tendsto u atTop (𝓝 x) → limsup (f ∘ u) atTop ≤ f x := by
  simpa [upperSemicontinuousWithinAt_univ_iff] using
    (upperSemicontinuousWithinAt_iff_seq_limsup_le (S := (Set.univ : Set α)))

end
end

/-! ### Lemma_7_0_3 (from Chap02) -/
section

universe u v

open scoped Topology
open Filter

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 7.0.3 compares the textbook sequential upper-limit condition on a subset
  `S` with the nearby-point limsup condition at `x`.
- `core/canonical`: the owner abstraction is `UpperSemicontinuousWithinAt`.
- `bridge/view`: the sequential side is the source-facing criterion from Text 7.0.2, while the
  nearby-point side is the canonical filter inequality `limsup f (𝓝[S] x) ≤ f x`, which in the
  Euclidean metric specialization matches the textbook `limsup_{y → x}` defined through suprema on
  small balls.
- Primitive data vs derived API: there is no new primitive data in this file. Both displayed
  conditions are derived characterizations of the same owner predicate
  `UpperSemicontinuousWithinAt f S x`.
- Layer target: this item stays at `bridge/view`; it should compose the upstream sequential bridge
  from Text 7.0.2 with the weak-order owner bridge
  `upperSemicontinuousWithinAt_iff_limsup_within_le`, rather than introduce a second local
  semicontinuity notion or low-level filter plumbing.

Domain-style sampling used here:
- `UpperSemicontinuousWithinAt`;
- `upperSemicontinuousWithinAt_iff_seq_limsup_le`.
-/

variable {α : Type u} [TopologicalSpace α]
variable {γ : Type v}

section FilterMap

variable [ConditionallyCompleteLattice γ] [BoundedOrder γ]

/-- If `limsup f (𝓝[S] x) ≤ f x`, then any map converging to `𝓝[S] x` satisfies the corresponding
limsup upper bound. This direction does not need Fréchet-Urysohn assumptions. -/
theorem limsup_comp_le_of_limsup_within_le {S : Set α} {f : α → γ} {x : α}
    {ι : Type*} {l : Filter ι} {u : ι → α}
    (h_limsup : limsup f (𝓝[S] x) ≤ f x) (hu : Tendsto u l (𝓝[S] x)) :
    limsup (f ∘ u) l ≤ f x := by
  calc
    limsup (f ∘ u) l = limsup f (Filter.map u l) := by
      simp [Filter.limsup_comp]
    _ ≤ limsup f (𝓝[S] x) := Filter.limsup_le_limsup_of_le hu
    _ ≤ f x := h_limsup

/-- If `limsup f (𝓝[S] x) ≤ f x`, then every sequence converging to `𝓝[S] x` satisfies the
textbook upper-limit inequality. This direction does not need Fréchet-Urysohn assumptions. -/
theorem seq_limsup_le_of_limsup_within_le {S : Set α} {f : α → γ} {x : α}
    (h_limsup : limsup f (𝓝[S] x) ≤ f x) :
    ∀ u : ℕ → α, Tendsto u atTop (𝓝[S] x) → limsup (f ∘ u) atTop ≤ f x := by
  intro u hu
  exact limsup_comp_le_of_limsup_within_le h_limsup hu

/-- Canonical filter-map bridge: `limsup f (𝓝[S] x) ≤ f x` is equivalent to requiring the same
limsup upper bound along every map/filter converging to `𝓝[S] x`. -/
theorem limsup_within_le_iff_limsup_comp_le {S : Set α} {f : α → γ} {x : α} :
    (∀ {ι : Type u} {l : Filter ι} {u : ι → α},
      Tendsto u l (𝓝[S] x) → limsup (f ∘ u) l ≤ f x) ↔
      limsup f (𝓝[S] x) ≤ f x := by
  constructor
  · intro h
    simpa [Function.comp] using
      (h (l := 𝓝[S] x) (u := fun z : α ↦ z)
        (by
          simpa using
            (tendsto_id : Tendsto (fun z : α ↦ z) (𝓝[S] x) (𝓝[S] x))))
  · intro h _ _ _ hu
    exact limsup_comp_le_of_limsup_within_le h hu

end FilterMap

section

variable [ConditionallyCompleteLinearOrder γ] [BoundedOrder γ]
variable [FrechetUrysohnSpace α]

-- Proof sketch: compose the intrinsic sequential characterization from Text 7.0.2 with the
-- owner-level bridge
-- `upperSemicontinuousWithinAt_iff_limsup_within_le`. This keeps the sequence side
-- at the relative topology layer `𝓝[S] x` instead of splitting out ambient convergence plus
-- separate membership hypotheses.
/-- Lemma 7.0.3: the intrinsic sequential upper-limit condition at `x` relative to `S` is
equivalent to the canonical within-set filter limsup inequality `limsup f (𝓝[S] x) ≤ f x`, which
for Euclidean specialization is the nearby-point formula `f(x) ≥ limsup_{y → x, y ∈ S} f(y)`. -/
theorem seq_limsup_le_iff_limsup_within_le {S : Set α} {f : α → γ} {x : α} :
    (∀ u : ℕ → α, Tendsto u atTop (𝓝[S] x) → limsup (f ∘ u) atTop ≤ f x) ↔
      limsup f (𝓝[S] x) ≤ f x := by
  constructor
  · intro h_seq
    exact (upperSemicontinuousWithinAt_iff_limsup_within_le).1 <|
      (upperSemicontinuousWithinAt_iff_seq_limsup_le).2 h_seq
  · intro h_limsup
    exact (upperSemicontinuousWithinAt_iff_seq_limsup_le).1 <|
      (upperSemicontinuousWithinAt_iff_limsup_within_le).2 h_limsup

/-- If every sequence converging to `𝓝[S] x` satisfies the textbook upper-limit inequality, then
`limsup f (𝓝[S] x) ≤ f x`. -/
theorem limsup_within_le_of_seq_limsup_le {S : Set α} {f : α → γ} {x : α}
    (h_seq : ∀ u : ℕ → α, Tendsto u atTop (𝓝[S] x) → limsup (f ∘ u) atTop ≤ f x) :
    limsup f (𝓝[S] x) ≤ f x := by
  exact (seq_limsup_le_iff_limsup_within_le).1 h_seq

end
end

/-! ### Text_7_0_4 (from Chap02) -/
noncomputable section

section

variable {α : Type*} [TopologicalSpace α]

open Function

/-
Source/core/bridge triage:
- `source-facing`: Text 7.0.4 introduces the lower semi-continuous hull of a function in a
  concrete finite-dimensional model as
  the greatest lower semicontinuous function majorized by the given function.
- `core/canonical`: the owner abstractions are the real-epigraph owner `epi`, the chapter
  epigraph-to-function owner `Function.verticalInfimum`, and mathlib's predicate
  `LowerSemicontinuous`.
- `bridge/view`: the source wording "greatest lower semicontinuous minorant" is derived API on top
  of the canonical owner construction obtained by taking the vertical infimum of the closed
  epigraph `closure (epi f)`.

Domain-style sampling used here:
- `epi`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_le_of_mem`;
- `Function.verticalInfimum_le_of_epi_subset`;
- `Function.le_verticalInfimum_of_subset_epi`;
- `lowerSemicontinuous_iff_isClosed_epigraph`;
- `LowerSemicontinuous.isClosed_epigraph`.

Primitive data vs derived API:
- the primitive datum is the function `f : α → WithTopBot 𝕜`;
- the owner construction is the function attached by `Function.verticalInfimum` to the closed
  epigraph `closure (epi f)`;
- the source-facing main statements are the epigraph-closure identity
  `closure (epi f) = epi cl(f)` and the `IsGreatest` characterization of `cl(f)` among lower
  semicontinuous minorants of `f`;
- lower semicontinuity and the pointwise bound `cl(f) ≤ f` are derived companions from that
  owner-level epigraph description.

Layer target: `source-facing`; this file keeps Rockafellar's closure `cl(f)` as the public owner,
but it is refined to grow from the earlier chapter owner `Function.verticalInfimum` on epigraph
sets instead of from a parallel local subtype-of-minorants wrapper.
-/

/-- Text 7.0.4: the lower semi-continuous hull of an extended-codomain function, specialized in
the source to a concrete finite-dimensional model, is the function attached to
the closed scalar epigraph `closure (epi f)` by
the chapter owner `Function.verticalInfimum`. The later source-facing theorem below shows that this
is exactly the greatest lower semicontinuous minorant of `f`. -/
def lowerSemicontinuousHull {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜]
    (f : α → WithTopBot 𝕜) : α → WithTopBot 𝕜 :=
  verticalInfimum (closure (epi f))

scoped[Rockafellar] notation "cl(" f ")" => lowerSemicontinuousHull f

section CoreLattice

variable {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜]

open scoped Rockafellar

/-- The closure `cl(f)` is majorized by the original function. -/
theorem lowerSemicontinuousHull_le_of_noBot [NoBotOrder 𝕜] (f : α → WithTopBot 𝕜) :
    cl(f) ≤ f := by
  simpa [lowerSemicontinuousHull] using
    (verticalInfimum_le_of_epi_subset
      (subset_closure : epi f ⊆ closure (epi f)) :
        verticalInfimum (closure (epi f)) ≤ f)

/-- Any closed-epigraph minorant of `f` lies below the closure `cl(f)`. -/
private theorem le_lowerSemicontinuousHull_of_isClosed_epi
    {f g : α → WithTopBot 𝕜} (hg_closed : IsClosed (epi g)) (hg_le : g ≤ f) :
    g ≤ cl(f) := by
  have hsubset : closure (epi f) ⊆ epi g := by
    have hfg : epi f ⊆ epi g := by
      intro p hp
      rcases p with ⟨x, μ⟩
      rw [mem_epi_iff] at hp ⊢
      exact le_trans (hg_le x) hp
    exact closure_minimal hfg hg_closed
  simpa [lowerSemicontinuousHull] using
    (le_verticalInfimum_of_subset_epi hsubset :
      g ≤ verticalInfimum (closure (epi f)))

/-- A closed-epigraph function is fixed by the closure operator `cl(·)`. -/
theorem cl_eq_self_of_isClosed_epi
    [NoBotOrder 𝕜] {f : α → WithTopBot 𝕜} (hf_closed : IsClosed (epi f)) :
    cl(f) = f :=
  le_antisymm (lowerSemicontinuousHull_le_of_noBot f)
    (le_lowerSemicontinuousHull_of_isClosed_epi hf_closed le_rfl)

end CoreLattice

section GenericCodomain

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]

open scoped Rockafellar

private theorem mem_closure_epi_of_le
    [OrderTopology 𝕜]
    {f : α → WithTopBot 𝕜} {x : α} {μ ν : 𝕜}
    (hμ : (x, μ) ∈ closure (epi f)) (hμν : μ ≤ ν) :
    (x, ν) ∈ closure (epi f) := by
  let raise : α × 𝕜 → α × 𝕜 := fun p ↦ (p.1, max p.2 ν)
  have hraise : Continuous raise := by
    continuity
  have hraise_epi : raise '' epi f ⊆ epi f := by
    rintro _ ⟨⟨x', r'⟩, hp, rfl⟩
    rw [mem_epi_iff] at hp ⊢
    exact le_trans hp (by exact_mod_cast (le_max_left r' ν))
  have hraise_closure : raise '' closure (epi f) ⊆ closure (epi f) := by
    calc
      raise '' closure (epi f) ⊆ closure (raise '' epi f) :=
        image_closure_subset_closure_image hraise
      _ ⊆ closure (epi f) := closure_mono hraise_epi
  have hraise_eq : raise (x, μ) = (x, ν) := by
    ext
    · rfl
    · change max μ ν = ν
      exact max_eq_right hμν
  exact hraise_eq ▸ hraise_closure ⟨(x, μ), hμ, rfl⟩

/-- The closed scalar epigraph of `cl(f)` is exactly the closure of the scalar epigraph of `f`. -/
theorem closure_epi_eq_epi_lowerSemicontinuousHull
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    (f : α → WithTopBot 𝕜) :
    closure (epi f) = epi cl(f) := by
  ext p
  rcases p with ⟨x, μ⟩
  constructor
  · intro hp
    exact mem_epi_iff.mpr (verticalInfimum_le_of_mem hp)
  · intro hp
    have hclosed :
        IsClosed {r : 𝕜 | (x, r) ∈ closure (epi f)} := by
      have hcont : Continuous fun r : 𝕜 ↦ (x, r) := by
        continuity
      simpa using (isClosed_closure : IsClosed (closure (epi f))).preimage hcont
    have hclosure_section :
        closure {r : 𝕜 | (x, r) ∈ closure (epi f)} =
          ((↑) : 𝕜 → WithTopBot 𝕜) ⁻¹' Set.Ici
            (verticalInfimum (closure (epi f)) x) := by
      have hupper :
          ∀ {r s : 𝕜}, r ∈ verticalSection (closure (epi f)) x → r ≤ s →
            s ∈ verticalSection (closure (epi f)) x := by
        intro r s hr hrs
        have hr' : (x, r) ∈ closure (epi f) := by
          simpa [verticalSection] using hr
        have hs' : (x, s) ∈ closure (epi f) :=
          mem_closure_epi_of_le (f := f) hr' hrs
        simpa [verticalSection] using hs'
      simpa [verticalSection] using
        (closure_verticalSection_eq_preimage_Ici_of_upward_closed
          (F := closure (epi f)) (x := x) hupper)
    have hfiber : μ ∈ {r : 𝕜 | (x, r) ∈ closure (epi f)} := by
      rw [← hclosed.closure_eq, hclosure_section]
      simpa [lowerSemicontinuousHull, Set.preimage, Set.Ici] using (mem_epi_iff.mp hp)
    exact hfiber

/-- `cl(f)` is the greatest closed-epigraph minorant of `f`. -/
private theorem isGreatest_closedEpiMinorant_lowerSemicontinuousHull
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    [NoBotOrder 𝕜]
    (f : α → WithTopBot 𝕜) :
    IsGreatest {g : α → WithTopBot 𝕜 | IsClosed (epi g) ∧ g ≤ f} (cl(f)) := by
  refine ⟨?_, ?_⟩
  · have hcl : IsClosed (epi (cl(f))) := by
      rw [← closure_epi_eq_epi_lowerSemicontinuousHull (f := f)]
      exact isClosed_closure
    exact ⟨hcl, lowerSemicontinuousHull_le_of_noBot f⟩
  · intro g hg
    exact le_lowerSemicontinuousHull_of_isClosed_epi hg.1 hg.2

/-- Canonical form: the closure `cl(f)` is lower semicontinuous. -/
theorem lowerSemicontinuous_lowerSemicontinuousHull
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    [NoMinOrder 𝕜] [Nonempty 𝕜]
    (f : α → WithTopBot 𝕜) :
    LowerSemicontinuous (cl(f)) := by
  apply lowerSemicontinuous_of_isClosed_epi
  rw [← closure_epi_eq_epi_lowerSemicontinuousHull (f := f)]
  exact isClosed_closure

/-- Any lower semicontinuous minorant of `f` lies below `cl(f)`. -/
theorem le_lowerSemicontinuousHull_of_lowerSemicontinuous
    [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
    {f g : α → WithTopBot 𝕜} (hg_lsc : LowerSemicontinuous g) (hg_le : g ≤ f) :
    g ≤ cl(f) :=
  le_lowerSemicontinuousHull_of_isClosed_epi
    (isClosed_epi_of_lowerSemicontinuous hg_lsc) hg_le

/-- The closure `cl(f)` is the greatest lower semicontinuous minorant of `f`. -/
theorem isGreatest_lowerSemicontinuousHull
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    [NoBotOrder 𝕜]
    [NoMinOrder 𝕜] [Nonempty 𝕜]
    (f : α → WithTopBot 𝕜) :
    IsGreatest {g : α → WithTopBot 𝕜 | LowerSemicontinuous g ∧ g ≤ f} (cl(f)) := by
  refine ⟨?_, ?_⟩
  · exact ⟨
      lowerSemicontinuous_lowerSemicontinuousHull f,
      lowerSemicontinuousHull_le_of_noBot f⟩
  · intro g hg
    exact le_lowerSemicontinuousHull_of_lowerSemicontinuous hg.1 hg.2

/-- Every lower semicontinuous function is fixed by `cl(·)`. -/
theorem lowerSemicontinuousHull_eq_self
    [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
    {f : α → WithTopBot 𝕜} (hf_lsc : LowerSemicontinuous f) :
    cl(f) = f :=
  cl_eq_self_of_isClosed_epi
    (isClosed_epi_of_lowerSemicontinuous hf_lsc)

end GenericCodomain

section GenericConsequences

open scoped Rockafellar

/-- The closure `cl(f)` is majorized by the original function. -/
theorem lowerSemicontinuousHull_le
    {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [NoBotOrder 𝕜]
    (f : α → WithTopBot 𝕜) :
    cl(f) ≤ f := by
  exact lowerSemicontinuousHull_le_of_noBot f

/-- Any lower semicontinuous minorant of `f` lies below the closure `cl(f)`. -/
theorem le_lowerSemicontinuousHull
    {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
    {f g : α → WithTopBot 𝕜} (hg_lsc : LowerSemicontinuous g) (hg_le : g ≤ f) :
    g ≤ cl(f) := by
  exact le_lowerSemicontinuousHull_of_lowerSemicontinuous hg_lsc hg_le

/-- The closure operator `cl(·)` is monotone with respect to pointwise order. -/
theorem lowerSemicontinuousHull_mono
    {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    [NoBotOrder 𝕜]
    {f g : α → WithTopBot 𝕜} (hfg : f ≤ g) :
    cl(f) ≤ cl(g) := by
  have hcl_closed : IsClosed (epi (cl(f))) := by
    rw [← closure_epi_eq_epi_lowerSemicontinuousHull (f := f)]
    exact isClosed_closure
  have hcl_le_g : cl(f) ≤ g := fun x ↦ le_trans (lowerSemicontinuousHull_le f x) (hfg x)
  exact le_lowerSemicontinuousHull_of_isClosed_epi (f := g) hcl_closed hcl_le_g

/-- Taking the closure `cl(f)` preserves the global infimum of an extended-real-valued function.
-/
theorem iInf_lowerSemicontinuousHull_eq_iInf
    {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
    (f : α → WithTopBot 𝕜) :
    (⨅ x, cl(f) x) = ⨅ x, f x := by
  refine le_antisymm (iInf_mono fun x ↦ lowerSemicontinuousHull_le f x) ?_
  refine le_iInf fun x ↦ ?_
  exact le_lowerSemicontinuousHull lowerSemicontinuous_const (fun y ↦ iInf_le f y) x

end GenericConsequences

end

/-! ### Text_7_0_5 (from Chap02) -/
section

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.5 explains how the chapter closure of a convex function is read:
  the closure surface is still `cl(·)`, while the exceptional improper case is tracked through the
  existing proper/improper API.
- `core/canonical`: the owner abstractions are the Chapter 2 closure owner
  `lowerSemicontinuousHull`, written `cl(·)`, and the Chapter 1 properness owner
  `Function.IsProper`.
- `bridge/view`: this item should not introduce a second public closure owner. Its mathematical
  content is the bridge from the source's branchwise prose to the already canonical owners
  `cl(·)` and `Function.IsProper`.

Domain-style sampling used here:
- `lowerSemicontinuousHull` and the notation `cl(·)` from `Text_7_0_4`;
- `Function.IsProper` from `Definition_4_6`;
- `Function.IsProper.ne_bot` from `Definition_4_6`;
- `Function.not_isProper_iff` from `Definition_4_7`.

Primitive data vs derived API:
- primitive data: a function `f : E → WithTopBot 𝕜`;
- owner abstractions: the closure operator `cl(f)` and the properness predicate `f.IsProper`;
- derived bridge: properness excludes the value `⊥`, while improperness is exactly empty
  effective domain or bottom attainment somewhere (via
  `Function.not_isProper_iff`).

Layer target: `bridge/view`. Since the chapter already fixed `cl(·)` as the closure surface and
nearby downstream statements use that owner directly, this file keeps only the canonical recalls
needed to read Text 7.0.5 without introducing any parallel closure owner.
-/

/- Text 7.0.5 continues to use the chapter properness owner on extended-codomain functions. -/
recall Function.IsProper

/- Text 7.0.5 continues to use the Chapter 2 closure surface `cl(·)`. -/
recall lowerSemicontinuousHull

/- On the proper branch of Text 7.0.5, the function never takes the value `⊥`. -/
recall Function.IsProper.ne_bot

/- The improper branch is exactly the failure of properness: empty effective domain or bottom
attainment somewhere is the source-facing restatement of the canonical bridge
`Function.not_isProper_iff`. -/
recall Function.not_isProper_iff

end

/-! ### Text_7_0_6 (from Chap02) -/
section

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.6 introduces the textbook terminology that a convex function is
  "closed" exactly when it is lower semicontinuous, equivalently when its epigraph is closed.
- `core/canonical`: the owner abstraction is `LowerSemicontinuous` on the chapter codomain layer
  `WithTopBot α`.
- `bridge/view`: the epigraph formulation is read on the chapter epigraph owner `epi` via
  `lowerSemicontinuous_iff_isClosed_epi` together with its two direction theorems.

Domain-style sampling used here:
- `LowerSemicontinuous`;
- `epi`;
- `lowerSemicontinuous_iff_isClosed_epi`;
- `isClosed_epi_of_lowerSemicontinuous`;
- `lowerSemicontinuous_of_isClosed_epi`.

Primitive data vs derived API:
- primitive datum: a function `f : E → WithTopBot α` on a topological domain;
- canonical owner: `LowerSemicontinuous f`;
- derived API: the closed-`epi` characterization.

Layer target: `bridge/view`. This item is a direct recall of the canonical owner and its epigraph
characterization, so no parallel local owner such as `Function.IsClosed` is kept.
-/

/- Text 7.0.6 uses the canonical owner `LowerSemicontinuous` for the source terminology
"closed function". -/
recall LowerSemicontinuous

/- Text 7.0.6 reads epigraph closedness on the canonical epigraph owner `epi`. -/
recall epi

/- Closedness of a function in the sense of Text 7.0.6 is equivalently closedness of its
chapter epigraph owner `epi`. -/
recall lowerSemicontinuous_iff_isClosed_epi

/- Forward epigraph bridge on the canonical owner surface. -/
recall isClosed_epi_of_lowerSemicontinuous

/- Reverse epigraph bridge on the canonical owner surface. -/
recall lowerSemicontinuous_of_isClosed_epi

end

/-! ### Text_7_0_7 (from Chap02) -/
section

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 7.0.7 isolates the endpoint-valued behavior of closed improper convex
  functions.
- `core/canonical`: the owner predicates already fixed in Chapter 2 are `Function.IsConvex 𝕜`,
  `Function.IsProper`, and `LowerSemicontinuous`; the canonical endpoint functions are the
  endpoint values `⊥` and `⊤` in `WithBotTop 𝕜`.
- `bridge/view`: Corollary 7.2.1 already supplies the key owner-side bridge
  `Function.IsConvex.eq_bot_of_mem_dom_of_lowerSemicontinuous`, which identifies the
  effective-domain branch with value `⊥`. The complementary branch is value `⊤` by the owner
  `dom(·)`.

Domain-style sampling used here:
- `Function.IsProper`;
- `LowerSemicontinuous`;
- `Function.IsConvex.eq_bot_of_mem_dom_of_lowerSemicontinuous`;
- the primitive bridge `Function.eq_bot_or_eq_top_of_eq_bot_on_dom`;
- the endpoint values `⊥` and `⊤` in `WithBotTop 𝕜`.

Primitive data vs derived API:
- primitive source inputs: `f : E → WithBotTop 𝕜` with `f.IsConvex 𝕜`,
  `LowerSemicontinuous f`, and
  `¬ f.IsProper`;
- derived source-facing output: the pointwise endpoint dichotomy
  `∀ x, f x = ⊥ ∨ f x = ⊤`.

Layer target: `source-facing`; this remark remains a theorem about the existing closedness,
convexity, and properness owners. The `dom` case split is factored through the primitive endpoint
bridge `Function.eq_bot_or_eq_top_of_eq_bot_on_dom` rather than inlined in the convex theorem.
-/

namespace Function

variable {β X : Type*} [PartialOrder β] [OrderTop β] [Bot β]
variable {f : X → β}

/-- Primitive endpoint bridge: if a function equals `⊥` at each point of its effective domain,
then every value is an endpoint `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_eq_bot_on_dom
    (hbot : ∀ ⦃x : X⦄, x ∈ dom(f) → f x = ⊥) (x : X) :
    f x = ⊥ ∨ f x = ⊤ := by
  by_cases hx : x ∈ dom(f)
  · exact .inl (hbot hx)
  · exact .inr <| by
      by_contra hxtop
      exact hx <| by
        simpa [mem_effectiveDomain] using (lt_of_le_of_ne le_top hxtop)

end Function

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: Corollary 7.2.1 provides the primitive input `f = ⊥` on `dom(f)`. The endpoint
-- dichotomy then follows from `Function.eq_bot_or_eq_top_of_eq_bot_on_dom`.
/-- Text 7.0.7 (owner form): a lower semicontinuous improper convex `WithBotTop 𝕜`-valued function
on a finite-dimensional normed space over an ordered scalar field is pointwise endpoint-valued:
for every `x`, one has `f x = ⊥` or `f x = ⊤`. -/
theorem eq_bot_or_eq_top_of_lowerSemicontinuous_of_not_isProper
    (hf : f.IsConvex 𝕜) (hf_lsc : LowerSemicontinuous f)
    (hf_not_proper : ¬ f.IsProper) :
    ∀ x : E, f x = ⊥ ∨ f x = ⊤ := by
  intro x
  exact Function.eq_bot_or_eq_top_of_eq_bot_on_dom
    (f := f)
    (hbot := fun {x} hx ↦
      hf.eq_bot_of_mem_dom_of_lowerSemicontinuous hf_lsc hf_not_proper hx) x

end Function.IsConvex

end

/-! ### Text_7_0_8 (from Chap02) -/
section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "reciprocalIoiExtension" =>
  Function.toWithBotTopOn (fun x : 𝕜 ↦ x⁻¹) (Set.Ioi (0 : 𝕜))

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.8 is an existence remark asserting that closed proper convexity does
  not force the effective domain to be closed.
- `core/canonical`: the existing owner predicates are `IsClosedProperConvex[𝕜]`, the
  effective-domain notation `dom(·)`, and ambient closedness `IsClosed`.
- `bridge/view`: the canonical witness is the direct owner
  `Function.toWithBotTopOn (fun x : 𝕜 ↦ x⁻¹) (Set.Ioi (0 : 𝕜))`, and the pure existence statement
  is a direct corollary.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `dom(·)` from `Chap01.Definition_4_4`, imported transitively there;
- the Chapter 1 extension-by-`+∞` owner `Function.toWithBotTopOn` and the reciprocal closedness
  theorem `lowerSemicontinuous_reciprocal_Ioi_extension` from `Text_7_0_9`;
- the convex-extension bridge `isConvex_toWithBotTopOn_iff` from `Chap01.Remark_4_4_5`.

Layer target: `source-facing`. The theorem records the textbook possibility statement directly,
while exposing the canonical reciprocal-on-`(0, ∞)` witness at the owner surface.
-/

-- Proof sketch: for
-- `f := Function.toWithBotTopOn (fun x : 𝕜 ↦ x⁻¹) (Set.Ioi (0 : 𝕜))`, convexity comes from
-- `convexOn_zpow (-1)` plus `isConvex_toWithBotTopOn_iff`, closedness from Text 7.0.9, properness
-- from `f 1 = 1` and absence of `⊥`, and `dom(f) = Set.Ioi 0`, which is not closed in `𝕜`.
/-- Text 7.0.8 (canonical witness form): the reciprocal extension
`Function.toWithBotTopOn (fun x ↦ x⁻¹) (Set.Ioi 0)` is closed proper convex, while its effective
domain is not closed. -/
theorem reciprocal_Ioi_extension_isClosedProperConvex_and_nonclosed_domain :
    IsClosedProperConvex[𝕜] reciprocalIoiExtension ∧
      ¬ IsClosed (dom(reciprocalIoiExtension)) := by
  let f : 𝕜 → WithBotTop 𝕜 := reciprocalIoiExtension
  have hconvOn_inv : ConvexOn 𝕜 (Set.Ioi (0 : 𝕜)) (fun x : 𝕜 ↦ x⁻¹) := by
    simpa [one_div, zpow_neg_one] using
      (convexOn_zpow (-1 : ℤ) :
        ConvexOn 𝕜 (Set.Ioi (0 : 𝕜)) (fun t : 𝕜 ↦ t ^ (-1 : ℤ)))
  have hconv : f.IsConvex 𝕜 := by
    simpa [f, reciprocalIoiExtension] using
      (isConvex_toWithBotTopOn_iff
        (C := Set.Ioi (0 : 𝕜)) (f := fun x : 𝕜 ↦ x⁻¹)).2 hconvOn_inv
  have hproper : f.IsProper := by
    rw [Function.isProper_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · change (1 : 𝕜) ∈ dom(reciprocalIoiExtension)
      rw [effectiveDomain_reciprocal_Ioi_extension]
      simp
    · intro x
      simpa [f] using reciprocal_Ioi_extension_ne_bot x
  have hclosed : LowerSemicontinuous f := by
    simpa [f, reciprocalIoiExtension] using
      (lowerSemicontinuous_reciprocal_Ioi_extension :
        LowerSemicontinuous reciprocalIoiExtension)
  have hnonclosed_dom : ¬ IsClosed (dom(f)) := by
    intro hclosed_dom
    have hzero_closure : (0 : 𝕜) ∈ closure (dom(f)) := by
      simp [f, effectiveDomain_reciprocal_Ioi_extension, closure_Ioi]
    have hzero_dom : (0 : 𝕜) ∈ dom(f) := by
      simpa [hclosed_dom.closure_eq] using hzero_closure
    have hzero_pos : (0 : 𝕜) < 0 := by
      have hzero_Ioi := hzero_dom
      simp [f, effectiveDomain_reciprocal_Ioi_extension] at hzero_Ioi
    exact (lt_irrefl (0 : 𝕜)) hzero_pos
  refine ⟨?_, ?_⟩
  · have hf : IsClosedProperConvex[𝕜] f := ⟨hconv, hproper, hclosed⟩
    simpa [f] using hf
  · simpa [f] using hnonclosed_dom

/-- Text 7.0.8 (existence form): there exists a closed proper convex `WithBotTop 𝕜`-valued
function on `𝕜` whose effective domain is not closed. -/
theorem exists_closedProperConvex_with_nonclosed_domain :
    ∃ f : 𝕜 → WithBotTop 𝕜, IsClosedProperConvex[𝕜] f ∧ ¬ IsClosed (dom(f)) := by
  refine ⟨reciprocalIoiExtension, ?_⟩
  simpa using reciprocal_Ioi_extension_isClosedProperConvex_and_nonclosed_domain

end

/-! ### Text_7_0_9 (from Chap02) -/
noncomputable section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 7.0.9 is the concrete example `f(x) = 1 / x` for `x > 0` and `f(x) = +∞`
  for `x ≤ 0`, asserted to be closed.
- `core/canonical`: Chapter 7 uses `LowerSemicontinuous` as the owner for closed extended-real
  functions, and Chapter 1 uses `f.toWithBotTopOn C` as the owner for extension by `+∞`
  outside a set.
- `bridge/view`: the source branch formulas on `(0, ∞)` and `(-∞, 0]` are kept as specialized
  lemmas for the canonical owner `(fun x : 𝕜 ↦ x⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))`;
  no parallel wrapper definition is introduced.

Domain-style sampling used here:
- `LowerSemicontinuous`;
- `lowerSemicontinuous_iff_isClosed_sublevel`;
- `epi`;
- `Function.toWithBotTopOn` / dot-notation `f.toWithBotTopOn C`;
- `Function.toWithBotTopOn_of_mem` / `Function.toWithBotTopOn_of_notMem`;
- the source-facing bridge `epi_reciprocal_Ioi_extension_eq_hyperbolaEpigraph`.

Layer target: `core/canonical` with a source-facing pointwise bridge.
-/

section

variable {𝕜 : Type*} [Preorder 𝕜] [Zero 𝕜] [Inv 𝕜]

-- Proof sketch: unfold `Function.toWithBotTopOn` and split on whether `x ∈ Set.Ioi (0 : 𝕜)`. On
-- the positive branch the extension agrees with `x ↦ x⁻¹`, while outside that set it is `+∞`.
/-- On the positive half-line, the canonical extension of `x ↦ x⁻¹` to `WithBotTop 𝕜` agrees with
the finite reciprocal branch. -/
@[simp] theorem reciprocal_Ioi_extension_of_pos {x : 𝕜} (hx : 0 < x) :
    ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x = (x⁻¹ : 𝕜) := by
  simpa using
    (Function.toWithBotTopOn_of_mem
      (f := fun y : 𝕜 ↦ y⁻¹) (C := Set.Ioi (0 : 𝕜)) hx)

/-- Outside the positive half-line, the canonical extension of `x ↦ x⁻¹` to `WithBotTop 𝕜`
takes value `+∞`. -/
@[simp] theorem reciprocal_Ioi_extension_of_not_pos {x : 𝕜} (hx : ¬ 0 < x) :
    ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x = (⊤ : WithBotTop 𝕜) := by
  exact
    Function.toWithBotTopOn_of_notMem
      (f := fun y : 𝕜 ↦ y⁻¹) (C := Set.Ioi (0 : 𝕜))
      (by simpa [Set.mem_Ioi] using hx)

/-- The effective domain of the reciprocal extension is exactly the positive half-line. -/
theorem effectiveDomain_reciprocal_Ioi_extension :
    dom((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) = Set.Ioi (0 : 𝕜) := by
  ext x
  rw [mem_effectiveDomain]
  by_cases hx : x ∈ Set.Ioi (0 : 𝕜)
  · have hx' : 0 < x := hx
    simpa [hx, reciprocal_Ioi_extension_of_pos hx']
      using (WithBotTop.coe_lt_top (x⁻¹))
  · simp [Function.toWithBotTopOn, hx]

/-- The reciprocal extension never takes the value `-∞`. -/
theorem reciprocal_Ioi_extension_ne_bot (x : 𝕜) :
    ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x ≠ (⊥ : WithBotTop 𝕜) := by
  by_cases hx : x ∈ Set.Ioi (0 : 𝕜)
  · have hx' : 0 < x := hx
    rw [reciprocal_Ioi_extension_of_pos hx']
    exact WithBotTop.coe_ne_bot (x⁻¹)
  · simp [Function.toWithBotTopOn, hx]

end

section

variable {𝕜 : Type*}
variable [GroupWithZero 𝕜] [Preorder 𝕜]

-- Proof sketch: unfold membership in `epi` and use the two branch lemmas for the extension. The
-- `x ≤ 0` branch is impossible in the global epigraph because it would force `⊤ ≤ r`.
/-- The scalar epigraph of the reciprocal extension is exactly the source-facing owner
`hyperbolaEpigraph`. -/
theorem epi_reciprocal_Ioi_extension_eq_hyperbolaEpigraph :
    epi ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) = hyperbolaEpigraph := by
  ext p
  rcases p with ⟨x, r⟩
  constructor
  · intro hp
    rw [mem_epi_iff] at hp
    by_cases hx_pos : 0 < x
    · have hxr : x⁻¹ ≤ r := by
        exact (WithBotTop.coe_le_coe).1
          (by simpa [reciprocal_Ioi_extension_of_pos hx_pos] using hp)
      exact (mem_hyperbolaEpigraph_iff).2 ⟨hx_pos, hxr⟩
    · have htop : (⊤ : WithBotTop 𝕜) ≤ (r : WithBotTop 𝕜) := by
        simpa [reciprocal_Ioi_extension_of_not_pos hx_pos] using hp
      exact (lt_irrefl (⊤ : WithBotTop 𝕜)
        (lt_of_le_of_lt htop (WithBotTop.coe_lt_top r))).elim
  · intro hp
    rw [mem_epi_iff]
    rcases (mem_hyperbolaEpigraph_iff).1 hp with ⟨hx_pos, hxr⟩
    exact by
      simpa [reciprocal_Ioi_extension_of_pos hx_pos] using
        ((WithBotTop.coe_le_coe).2 hxr : ((x⁻¹ : 𝕜) : WithBotTop 𝕜) ≤ r)

end

section

variable {𝕜 : Type*}
variable [DivisionRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [NoMinOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/-- Text 7.0.9: the function `f(x) = 1 / x` for `x > 0` and `f(x) = +∞` for `x ≤ 0`, written
canonically as `(fun x ↦ x⁻¹).toWithBotTopOn (Set.Ioi 0)`, is closed; that is, it is
lower semicontinuous.

Assumption layer note: this theorem uses the Chapter 7 scalar-sublevel characterization
`lowerSemicontinuous_iff_isClosed_sublevel` directly, so it does not rely on any deferred
closed-epigraph lemma in the hyperbola owner file. -/
theorem lowerSemicontinuous_reciprocal_Ioi_extension :
    LowerSemicontinuous ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) := by
  refine (lowerSemicontinuous_iff_isClosed_sublevel_withBotTop
    (f := (fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜)))).2 ?_
  intro r
  by_cases hr : 0 < r
  · have hsublevel :
      {x : 𝕜 |
          ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x ≤ r} =
        Set.Ici (r⁻¹) := by
      ext x
      constructor
      · intro hx
        by_cases hx_pos : 0 < x
        · have hxr : x⁻¹ ≤ r := by
            exact (WithBotTop.coe_le_coe).1
              (by simpa [reciprocal_Ioi_extension_of_pos hx_pos] using hx)
          refine (inv_le_inv₀ (a := x) (b := r⁻¹) hx_pos (inv_pos.2 hr)).1 ?_
          simpa [inv_inv] using hxr
        · have htop : (⊤ : WithBotTop 𝕜) ≤ (r : WithBotTop 𝕜) := by
            have htop' := hx
            simp [reciprocal_Ioi_extension_of_not_pos hx_pos] at htop'
          simp at htop
      · intro hx
        have hx_pos : 0 < x := lt_of_lt_of_le (inv_pos.2 hr) hx
        have hxr : x⁻¹ ≤ r := by
          simpa [inv_inv] using
            ((inv_le_inv₀ (a := x) (b := r⁻¹) hx_pos (inv_pos.2 hr)).2 hx)
        exact by
          simpa [reciprocal_Ioi_extension_of_pos hx_pos] using
            ((WithBotTop.coe_le_coe).2 hxr :
              ((x⁻¹ : 𝕜) : WithBotTop 𝕜) ≤ r)
    simpa [hsublevel] using (isClosed_Ici : IsClosed (Set.Ici (r⁻¹ : 𝕜)))
  · have hr_nonpos : r ≤ 0 := le_of_not_gt hr
    have hsublevel :
        {x : 𝕜 |
            ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x ≤ r} = ∅ := by
      ext x
      constructor
      · intro hx
        by_cases hx_pos : 0 < x
        · have hxr : x⁻¹ ≤ r := by
            exact (WithBotTop.coe_le_coe).1
              (by simpa [reciprocal_Ioi_extension_of_pos hx_pos] using hx)
          have h0lt_r : (0 : 𝕜) < r := lt_of_lt_of_le (inv_pos.2 hx_pos) hxr
          exact (False.elim (not_lt_of_ge hr_nonpos h0lt_r))
        · have htop : (⊤ : WithBotTop 𝕜) ≤ (r : WithBotTop 𝕜) := by
            have htop' := hx
            simp [reciprocal_Ioi_extension_of_not_pos hx_pos] at htop'
          simp at htop
      · simp
    rw [hsublevel]
    exact isClosed_empty

end

/-! ### Text_7_0_10 (from Chap02) -/
section

universe u

open scoped Rockafellar

variable {α : Type u} [TopologicalSpace α]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.10 identifies Rockafellar's closure `cl(f)` with the neighborhood
  liminf of `f`.
- `core/canonical`: the owner abstraction is still the Chapter 2 lower-semicontinuous hull
  `lowerSemicontinuousHull`, written `cl(·)`, together with mathlib's filter owner `Filter.liminf`.
- `bridge/view`: the epigraph-closure theorem
  `closure_epi_eq_epi_lowerSemicontinuousHull` from `Text_7_0_4` bridges the owner `cl(·)` to the
  neighborhood-filter characterization used here.

Domain-style sampling used here:
- `lowerSemicontinuousHull` / `cl(·)`;
- `closure_epi_eq_epi_lowerSemicontinuousHull`;
- `Filter.liminf_le_iff`;
- `mem_closure_iff_nhds`.

Layer target: `source-facing`; this file keeps the textbook liminf formula directly on the chapter
owner `cl(·)` rather than introducing a parallel wrapper around neighborhood liminf data.
-/

/- Text 7.0.10 (1): the epigraph of the closure `cl(f)` is exactly the closure of the epigraph of
`f`. This is the canonical Chapter 2 epigraph-closure theorem for the owner `cl(·)`. -/
recall closure_epi_eq_epi_lowerSemicontinuousHull

-- Proof sketch: for any `μ`, membership of `(x, μ)` in `closure (epi f)` is characterized by
-- approaching epigraph points `(y, ν)` with `y → x` and `f y ≤ ν → μ`. This identifies the least
-- such height over `x` with the neighborhood-filter liminf of `f` at `x`; combine this with the
-- epigraph identity from clause (1).
/-- Bridge-level form: if `closure (epi f)` is already identified with `epi cl(f)`, then `cl(f)` is
the pointwise neighborhood-filter liminf. -/
theorem lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    [NoBotOrder 𝕜]
    (f : α → WithBotTop 𝕜) (x : α)
    (hclosure : closure (epi f) = epi cl(f)) :
    cl(f) x = Filter.liminf f (nhds x) := by
  refine WithBot.eq_of_forall_le_coe_iff ?_
  intro a
  cases a with
  | top =>
      simp
  | coe α =>
      have hliminf :
          Filter.liminf f (nhds x) ≤ (α : WithBotTop 𝕜) ↔
            ∀ y > (α : WithBotTop 𝕜), ∃ᶠ z in nhds x, f z < y :=
        Filter.liminf_le_iff
      constructor
      · intro hcl
        have hmem : (x, α) ∈ closure (epi f) := by
          have h' : (x, α) ∈ epi cl(f) := mem_epi_iff.mpr hcl
          simpa [hclosure] using h'
        refine hliminf.2 ?_
        intro y hy
        refine (Filter.frequently_iff).2 ?_
        intro u hu
        by_cases hy_top : y = (⊤ : WithBotTop 𝕜)
        · have ht : u ×ˢ (Set.univ : Set 𝕜) ∈ nhds (x, α) := by
            simpa [nhds_prod_eq] using
              (Filter.prod_mem_prod hu (show (Set.univ : Set 𝕜) ∈ nhds α from Filter.univ_mem))
          rcases (mem_closure_iff_nhds.1 hmem) (u ×ˢ (Set.univ : Set 𝕜)) ht with ⟨p, hp⟩
          rcases hp with ⟨hpU, hpEpi⟩
          rcases hpU with ⟨hzU, -⟩
          refine ⟨p.1, hzU, ?_⟩
          have hfne : f p.1 ≠ (⊤ : WithBotTop 𝕜) := by
            intro hf_top
            exact (not_le_of_gt (WithBotTop.coe_lt_top p.2)) (hf_top ▸ (mem_epi_iff.mp hpEpi))
          simpa [hy_top] using (lt_top_iff_ne_top.mpr hfne)
        · have hy_bot : y ≠ (⊥ : WithBotTop 𝕜) := by
            intro hy_bot
            have hcontra : ¬ ((α : WithBotTop 𝕜) < (⊥ : WithBotTop 𝕜)) := by simp
            exact hcontra (hy_bot ▸ hy)
          lift y to 𝕜 using ⟨hy_top, hy_bot⟩ with β hβ
          have hαβ : α < β := by
            exact (WithBotTop.coe_lt_coe).1 (by simpa [hβ] using hy)
          have ht : u ×ˢ Set.Iio β ∈ nhds (x, α) := by
            simpa [nhds_prod_eq] using (Filter.prod_mem_prod hu (Iio_mem_nhds hαβ))
          rcases (mem_closure_iff_nhds.1 hmem) (u ×ˢ Set.Iio β) ht with ⟨p, hp⟩
          rcases hp with ⟨hpU, hpEpi⟩
          rcases hpU with ⟨hzU, hμβ⟩
          refine ⟨p.1, hzU, ?_⟩
          have hf_lt : f p.1 < ((β : 𝕜) : WithBotTop 𝕜) :=
            lt_of_le_of_lt (mem_epi_iff.mp hpEpi) ((WithBotTop.coe_lt_coe).2 hμβ)
          simpa [hβ] using hf_lt
      · intro hlim
        have hmem : (x, α) ∈ closure (epi f) := by
          refine (mem_closure_iff_nhds).2 ?_
          intro s hs
          rcases (mem_nhds_prod_iff.mp hs) with ⟨u, hu, v, hv, huv⟩
          rcases exists_Ico_subset_of_mem_nhds hv (exists_gt α) with ⟨β, hαβ, hβv⟩
          rcases exists_between hαβ with ⟨γ, hαγ, hγβ⟩
          have hfreq_lt : ∃ᶠ z in nhds x, f z < ((γ : 𝕜) : WithBotTop 𝕜) :=
            hliminf.1 hlim ((γ : 𝕜) : WithBotTop 𝕜) ((WithBotTop.coe_lt_coe).2 hαγ)
          rcases (Filter.frequently_iff.1 hfreq_lt) hu with ⟨z, hzU, hzlt⟩
          refine ⟨(z, γ), ?_⟩
          refine ⟨huv ?_, mem_epi_iff.mpr (le_of_lt hzlt)⟩
          exact ⟨hzU, hβv ⟨hαγ.le, hγβ⟩⟩
        have h' : (x, α) ∈ epi cl(f) := by
          simpa [hclosure] using hmem
        exact mem_epi_iff.mp h'

/-- The closure owner `cl(·)` is the pointwise neighborhood-filter liminf. -/
@[simp] theorem lowerSemicontinuousHull_apply_eq_liminf_nhds
    [NoBotOrder 𝕜]
    (f : α → WithBotTop 𝕜) (x : α) :
    cl(f) x = Filter.liminf f (nhds x) := by
  exact lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (x := x) (closure_epi_eq_epi_lowerSemicontinuousHull f)

/-- Function-level form: the closure `cl(f)` is the neighborhood-filter liminf of `f`. -/
theorem lowerSemicontinuousHull_eq_liminf_nhds_of_closure_epi_eq
    [NoBotOrder 𝕜]
    (f : α → WithBotTop 𝕜)
    (hclosure : closure (epi f) = epi cl(f)) :
    cl(f) = fun x ↦ Filter.liminf f (nhds x) := by
  funext x
  exact lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (x := x) hclosure

/-- Function-level form: the closure `cl(f)` is the neighborhood-filter liminf of `f`. -/
theorem lowerSemicontinuousHull_eq_liminf_nhds
    [NoBotOrder 𝕜]
    (f : α → WithBotTop 𝕜) :
    cl(f) = fun x ↦ Filter.liminf f (nhds x) := by
  exact lowerSemicontinuousHull_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (closure_epi_eq_epi_lowerSemicontinuousHull f)

end

/-! ### Text_7_0_11 (from Chap02) -/
section

universe u

open scoped Rockafellar

variable {X : Type u} [TopologicalSpace X]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.11 identifies the scalar `α`-sublevel set of the closure `cl(f)` with
  the intersection of the closures of the scalar `μ`-sublevel sets of `f` over all `μ > α`.
- `core/canonical`: the owner is still the Chapter 2 lower-semicontinuous hull
  `lowerSemicontinuousHull`, written `cl(·)`, together with ambient set closure and the canonical
  scalar sublevel sets as preimages `f ⁻¹' Set.Iic a`.
- `bridge/view`: this file first records the primitive bridge "if `cl(f)` is identified pointwise
  with neighborhood liminf, then the source set identity follows"; Text 7.0.10 then supplies that
  liminf bridge for the chapter owner.

Domain-style sampling used here:
- `lowerSemicontinuousHull` / `cl(·)` from `Text_7_0_4`;
- `lowerSemicontinuousHull_apply_eq_liminf_nhds` from `Text_7_0_10`;
- `Filter.liminf_le_iff` and `mem_closure_iff_frequently` from mathlib's filter/topology API.

Layer target: `source-facing`, with a primitive liminf-bridge lemma on canonical preimage owners
and a derived source theorem on textbook set-builder sublevel notation.
-/

-- Proof sketch: assume `g` is identified pointwise with neighborhood liminf of `f`. If
-- `g x ≤ α`, every `μ > α` has neighborhood liminf of `f` at `x` strictly below `μ`, so every
-- neighborhood of `x` meets the `μ`-sublevel set of `f`; hence `x` lies in the closure of that
-- sublevel set. Conversely, if `x` belongs to every such closure, then for each `μ > α` there
-- are points arbitrarily close to `x` with `f ≤ μ`, forcing `liminf f (nhds x) ≤ μ`; letting
-- `μ ↓ α` yields `g x ≤ α`.
/-- Primitive liminf bridge: if `g` is identified pointwise with the neighborhood liminf of `f`,
then the closed scalar `α`-sublevel preimage of `g` is the intersection of closures of higher
closed-sublevel preimages of `f`. -/
theorem sublevel_preimage_eq_iInter_closure_higher_preimages_of_hliminf
    (f g : X → WithBotTop 𝕜) (α : 𝕜)
    (hliminf : g = fun x ↦ Filter.liminf f (nhds x)) :
    g ⁻¹' Set.Iic (α : WithBotTop 𝕜) =
      ⋂ μ : Set.Ioi (α : WithBotTop 𝕜), closure (f ⁻¹' Set.Iic (μ : WithBotTop 𝕜)) := by
  ext x
  have liminf_le_iff {β : WithBotTop 𝕜} :
      Filter.liminf f (nhds x) ≤ β ↔ ∀ y > β, ∃ᶠ z in nhds x, f z < y :=
    Filter.liminf_le_iff Filter.isCobounded_ge_of_top Filter.isBounded_ge_of_bot
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro μ
    have hx' : g x ≤ (α : WithBotTop 𝕜) := by
      simpa [Set.mem_preimage, Set.mem_Iic] using hx
    have hlim : Filter.liminf f (nhds x) ≤ (α : WithBotTop 𝕜) := by
      simpa [hliminf] using hx'
    have hαμ : (α : WithBotTop 𝕜) < (μ : WithBotTop 𝕜) := μ.2
    have hfreq_lt : ∃ᶠ y in nhds x, f y < (μ : WithBotTop 𝕜) :=
      (liminf_le_iff.1 hlim) (μ : WithBotTop 𝕜) hαμ
    have hfreq_le : ∃ᶠ y in nhds x, f y ≤ (μ : WithBotTop 𝕜) :=
      hfreq_lt.mono (fun _ hy ↦ le_of_lt hy)
    exact (mem_closure_iff_frequently).2 <| by
      simpa [Set.mem_preimage, Set.mem_Iic] using hfreq_le
  · intro hx
    have hfreq_le :
        ∀ μ : Set.Ioi (α : WithBotTop 𝕜), ∃ᶠ y in nhds x, f y ≤ (μ : WithBotTop 𝕜) := by
      intro μ
      have hμclosure : x ∈ closure (f ⁻¹' Set.Iic (μ : WithBotTop 𝕜)) :=
        (Set.mem_iInter.mp hx) μ
      exact (mem_closure_iff_frequently).1 hμclosure |>.mono <| by
        intro y hy
        simpa [Set.mem_preimage, Set.mem_Iic] using hy
    have hlim : Filter.liminf f (nhds x) ≤ (α : WithBotTop 𝕜) := by
      refine liminf_le_iff.2 ?_
      intro y hy
      by_cases hy_top : y = (⊤ : WithBotTop 𝕜)
      · obtain ⟨μ, hαμ⟩ := exists_gt α
        let μ' : Set.Ioi (α : WithBotTop 𝕜) := ⟨(μ : WithBotTop 𝕜), (WithBotTop.coe_lt_coe).2 hαμ⟩
        have hμfreq := hfreq_le μ'
        have hμlt_top : (μ' : WithBotTop 𝕜) < (⊤ : WithBotTop 𝕜) := by
          exact lt_top_iff_ne_top.mpr (by
            change (μ : WithBotTop 𝕜) ≠ (⊤ : WithBotTop 𝕜)
            exact WithBotTop.coe_ne_top μ)
        exact hμfreq.mono (fun z hz ↦ lt_of_le_of_lt hz (hy_top ▸ hμlt_top))
      · have hy_bot : y ≠ (⊥ : WithBotTop 𝕜) := by
          intro hy_bot
          simp [hy_bot] at hy
        lift y to 𝕜 using ⟨hy_top, hy_bot⟩ with ν hν
        have hαν : α < ν := by
          exact (WithBotTop.coe_lt_coe).1 (by simpa [hν] using hy)
        obtain ⟨μ, hαμ, hμν⟩ := exists_between hαν
        let μ' : Set.Ioi (α : WithBotTop 𝕜) :=
          ⟨(μ : WithBotTop 𝕜), (WithBotTop.coe_lt_coe).2 hαμ⟩
        have hμfreq := hfreq_le μ'
        have hμ'ν : (μ' : WithBotTop 𝕜) < (ν : WithBotTop 𝕜) := by
          change (μ : WithBotTop 𝕜) < (ν : WithBotTop 𝕜)
          exact (WithBotTop.coe_lt_coe).2 hμν
        exact hμfreq.mono (fun z hz ↦ lt_of_le_of_lt hz hμ'ν)
    have hx' : g x ≤ (α : WithBotTop 𝕜) := by
      simpa [hliminf] using hlim
    simpa [Set.mem_preimage, Set.mem_Iic] using hx'

variable [TopologicalSpace 𝕜]

/-- Bridge-level specialization to Rockafellar's closure owner `cl(·)`. -/
theorem lowerSemicontinuousHull_sublevel_preimage_eq_iInter_closure_higher_preimages_of_hliminf
    (f : X → WithBotTop 𝕜) (α : 𝕜)
    (hliminf : cl(f) = fun x ↦ Filter.liminf f (nhds x)) :
    (cl(f)) ⁻¹' Set.Iic (α : WithBotTop 𝕜) =
      ⋂ μ : Set.Ioi (α : WithBotTop 𝕜), closure (f ⁻¹' Set.Iic (μ : WithBotTop 𝕜)) := by
  simpa using sublevel_preimage_eq_iInter_closure_higher_preimages_of_hliminf
    (f := f) (g := cl(f)) (α := α) (hliminf := hliminf)

variable [OrderTopology 𝕜]
variable [NoBotOrder 𝕜]

/-- Text 7.0.11: for each scalar `α`, the closed `α`-sublevel set of the closure `cl(f)` is the
intersection of the closures of the higher closed scalar sublevel sets of `f`. -/
theorem lowerSemicontinuousHull_sublevel_eq_iInter_closure_higher_sublevels
    (f : X → WithBotTop 𝕜) (α : 𝕜) :
    {x | cl(f) x ≤ α} =
      ⋂ μ : Set.Ioi (α : WithBotTop 𝕜), closure {x | f x ≤ (μ : WithBotTop 𝕜)} := by
  simpa [Set.ext_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic] using
    (lowerSemicontinuousHull_sublevel_preimage_eq_iInter_closure_higher_preimages_of_hliminf
      (f := f) (α := α)
      (hliminf := lowerSemicontinuousHull_eq_liminf_nhds (f := f)))

end

/-! ### Text_7_0_12 (from Chap02) -/
section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 7.0.12 records three basic order properties of the Chapter 7 closure
  operator: `cl(f) ≤ f`, monotonicity under pointwise order, and preservation of the global
  infimum.
- `core/canonical`: the owner construction is `lowerSemicontinuousHull`, written `cl(·)`, and the
  corresponding owner theorems now all live upstream in `Text_7_0_4`.
- `bridge/view`: this item contributes no new owner data or wrapper layer; it is a direct
  source-facing recall of the canonical closure-order API.

Domain-style sampling used here:
- `lowerSemicontinuousHull_le`;
- `lowerSemicontinuousHull_mono`;
- `iInf_lowerSemicontinuousHull_eq_iInf`.

Primitive data vs derived API:
- primitive owner data: a function `f : α → WithBotTop 𝕜`;
- derived API: the pointwise minorant property, monotonicity of `cl(·)`, and the `iInf`
  invariance already exposed by the owner file.

Layer target: `bridge/view`. This file is a direct canonical recall surface for the three source
clauses rather than a second home for owner theorems.
-/

/- Text 7.0.12 (1): for every extended-codomain function, the closure `cl(f)` is pointwise
majorized by `f`. This is exactly the canonical owner theorem
`lowerSemicontinuousHull_le`. -/
recall lowerSemicontinuousHull_le

/- Text 7.0.12 (2): the closure operator `cl(·)` is monotone with respect to pointwise order.
This is the canonical owner theorem `lowerSemicontinuousHull_mono`. -/
recall lowerSemicontinuousHull_mono

/- Text 7.0.12 (3): taking the closure `cl(f)` preserves the global infimum of an
extended-codomain function. This is the canonical owner theorem
`iInf_lowerSemicontinuousHull_eq_iInf`. -/
recall iInf_lowerSemicontinuousHull_eq_iInf

end

/-! ### Text_7_0_13 (from Chap02) -/
section

universe u

open scoped Rockafellar

variable {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [DenselyOrdered α]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [ClosedIciTopology 𝕜] [Zero 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.13 is the half-line specialization of Rockafellar's statement that the
  lower-semicontinuous hull of an open-set indicator fills in the boundary.
- `core/canonical`: the owner abstraction in this chapter is
  `lowerSemicontinuousHull_indicator_eq_indicator_closure`.
- `bridge/view`: the only extra step here is the order-topology identity
  `closure (Set.Ioi a) = Set.Ici a` from local nonemptiness of `Set.Ioi a`.

Domain-style sampling used here:
- `lowerSemicontinuousHull_indicator_eq_indicator_closure`;
- `closure_Ioi'`;
- the indicator owner `δ[𝕜](· | C)`.

Layer target: this file first records the canonical `a`-level half-line owner and then recovers
the textbook `0`-specialization as a direct instance.
-/

/-- Canonical half-line owner: for any `a`, the lower-semicontinuous hull of the indicator of
`(a, ∞)` is the indicator of `[a, ∞)`. -/
theorem lowerSemicontinuousHull_indicator_Ioi_eq_indicator_Ici (a : α)
    (ha : (Set.Ioi a).Nonempty) :
    cl((δ[𝕜](· | Set.Ioi a))) = (δ[𝕜](· | Set.Ici a)) := by
  simpa [closure_Ioi' (a := a) ha] using
    lowerSemicontinuousHull_indicator_eq_indicator_closure (Set.Ioi a)

-- Proof sketch: instantiate the canonical `a`-level theorem at `a = 0`.
/-- Text 7.0.13: the lower-semicontinuous hull of the indicator of `(0, ∞)` is the indicator of
`[0, ∞)`. -/
theorem lowerSemicontinuousHull_zero_on_pos_top_on_nonpos
    [Zero α] (h0 : (Set.Ioi (0 : α)).Nonempty)
    :
    cl((δ[𝕜](· | Set.Ioi (0 : α)))) = (δ[𝕜](· | Set.Ici (0 : α))) := by
  simpa using
    lowerSemicontinuousHull_indicator_Ioi_eq_indicator_Ici (a := (0 : α)) h0

end
