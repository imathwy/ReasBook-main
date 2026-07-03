import Mathlib.Tactic.Recall
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Sequences

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_0_1 (from Chap02) -/
/-!
Source/core/bridge triage:
- `source-facing`: Definition 10.0.1 names continuity relative to a subset.
- `core/canonical`: the owner is `ContinuousOn`.
- `bridge/view`: the intrinsic bridge is continuity of the restriction to the subtype,
  using `continuousOn_iff_continuous_restrict` and `continuous_iff_continuousAt`.

Abstraction checks:
- codomain/ambient/scalar layers are already fully generic;
- no concrete model owner is introduced;
- for pointwise statements, prefer the intrinsic subtype view over ambient phrasing.
-/
/- Definition 10.0.1: A function is continuous relative to a subset precisely in the canonical
mathlib sense of being `ContinuousOn` on that subset. -/
recall ContinuousOn

/- Intrinsic pointwise continuity of the restriction is the canonical companion view. -/
recall continuous_iff_continuousAt

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Companion bridge for Definition 10.0.1: relative continuity on `S` is equivalent to
pointwise continuity of the restriction on the subtype `S`. -/
theorem continuousOn_iff_forall_continuousAt_restrict
    {f : X → Y} {S : Set X} :
    ContinuousOn f S ↔ ∀ x : S, ContinuousAt (S.restrict f) x := by
  rw [continuousOn_iff_continuous_restrict, continuous_iff_continuousAt]

end

/- Subtype-restriction continuity is the canonical bridge view of relative continuity. -/
recall continuousOn_iff_continuous_restrict

/-! ### Theorem_10_0_2 (from Chap02) -/
section

open Filter Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-
Source/core/bridge triage:
- `source-facing`: the theorem is the sequential criterion for continuity relative to a subset
  `S ⊆ X`.
- `core/canonical`: the owner notion is `ContinuousOn f S`, as fixed in Definition 10.0.1.
- `bridge/view`: the sequence criterion is stated intrinsically on the subtype `S`, then identified
  with continuity of the restriction `S.restrict f`.
- Domain-style sampling used here:
  `ContinuousOn`, `ContinuousOn.restrict`, and `SeqContinuous.continuous`.
- Primitive data vs derived API: no new owner object is introduced here; the theorem is a direct
  characterization of the existing owner notion `ContinuousOn`.
- Layer target: `bridge/view`, with the public statement using intrinsic sequence data on the
  relative domain `S`.
- Ambient-abstraction check: the proof recovers continuity of the restriction from sequential
  continuity only on the relative domain `S`. The mathematically relevant owner layer is therefore
  the subtype carrying
  `[SequentialSpace S]`, which is weaker than assuming a global Fréchet-Urysohn structure on `X`
  and still covers the textbook case `X = ℝ^n`.
-/

-- Proof sketch: pass from `ContinuousOn f S` to the restriction `S.restrict f` and apply
-- sequential continuity on the subtype `S`; conversely, recover continuity of the restriction from
-- sequential continuity via `continuous_iff_seqContinuous`.
/-- Canonical owner-level bridge for Theorem 10.0.2: relative continuity on `S` is exactly
sequential continuity of the restriction `S.restrict f` when the relative domain is sequential. -/
theorem continuousOn_iff_seqContinuous
    {f : X → Y} {S : Set X} [SequentialSpace S] :
    ContinuousOn f S ↔ SeqContinuous (S.restrict f) := by
  rw [continuousOn_iff_continuous_restrict, continuous_iff_seqContinuous]

/-- Theorem 10.0.2, intrinsic sequence criterion on the relative domain: a function is continuous
relative to `S` iff for every `x : S`, every sequence in `S` converging to `x` has image sequence
under the restriction `S.restrict f` converging to `(S.restrict f) x`. The source applies this to
subsets of `ℝ^n`; here the assumptions remain on the weaker canonical owner layer that only
requires the relative domain `S` itself to be sequential. -/
theorem continuousOn_iff_tendsto_restrict_along_sequences
    {f : X → Y} {S : Set X} [SequentialSpace S] :
    ContinuousOn f S ↔
      ∀ x : S, ∀ y : ℕ → S, Tendsto y atTop (nhds x) →
        Tendsto ((S.restrict f) ∘ y) atTop (nhds ((S.restrict f) x)) := by
  constructor
  · intro hf x y hy
    have hseq : SeqContinuous (S.restrict f) :=
      continuousOn_iff_seqContinuous.1 hf
    simpa [Function.comp] using hseq (x := y) (p := x) hy
  · intro hseq_surface
    have hseq : SeqContinuous (S.restrict f) := by
      intro y x hy
      simpa using hseq_surface x y hy
    exact continuousOn_iff_seqContinuous.2 hseq

/-- Theorem 10.0.2, source-facing sequence companion: a function is continuous relative to `S`
iff for every `x : S`, every sequence in `S` converging to `x` has image sequence under the
function `f` converging to `f x`. This is a direct bridge view of the intrinsic restriction-based
criterion `continuousOn_iff_tendsto_restrict_along_sequences`. -/
theorem continuousOn_iff_tendsto_along_sequences
    {f : X → Y} {S : Set X} [SequentialSpace S] :
    ContinuousOn f S ↔
      ∀ x : S, ∀ y : ℕ → S, Tendsto y atTop (nhds x) →
        Tendsto (fun n ↦ f (y n)) atTop (nhds (f x)) := by
  simpa [Function.comp] using
    (continuousOn_iff_tendsto_restrict_along_sequences (f := f) (S := S))

end
