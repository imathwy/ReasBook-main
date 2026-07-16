import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
