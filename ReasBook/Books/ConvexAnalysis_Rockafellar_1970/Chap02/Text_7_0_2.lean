import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
