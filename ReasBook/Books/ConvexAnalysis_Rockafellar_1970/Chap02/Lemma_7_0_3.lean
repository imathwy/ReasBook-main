import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_2

-- Declarations for this item will be appended below by the statement pipeline.

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
