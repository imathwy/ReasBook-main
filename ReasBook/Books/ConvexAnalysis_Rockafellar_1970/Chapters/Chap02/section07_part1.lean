/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section01_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part1

noncomputable section
open scoped Topology

section Chap02
section Section07

/-- Text 7.0.1: Let `f : S → [-∞, +∞]` with `S ⊆ R^n` and `x ∈ S`. Then `f` is lower
semicontinuous at `x` if for every sequence `x_i ⊂ S` with `x_i → x`,
`f x ≤ liminf (fun i => f (x_i))`. Equivalently, `f x ≤ liminf_{y → x} f y`. -/
def LowerSemicontinuousAtSeq {n : Nat} (S : Set (EuclideanSpace Real (Fin n)))
    (f : S → EReal) (x : S) : Prop :=
  ∀ u : ℕ → S,
    Filter.Tendsto (fun i => (u i : EuclideanSpace Real (Fin n))) Filter.atTop
      (𝓝 (x : EuclideanSpace Real (Fin n))) →
      f x ≤ Filter.liminf (fun i => f (u i)) Filter.atTop

/-- A frequently occurring subset near `x` yields a sequence in that subset converging to `x`. -/
lemma exists_seq_tendsto_of_frequently {n : Nat}
    {S : Set (EuclideanSpace Real (Fin n))} {x : S} {s : Set S}
    (h : ∃ᶠ z in 𝓝 x, z ∈ s) :
    ∃ u : ℕ → S, (∀ n, u n ∈ s) ∧
      Filter.Tendsto (fun i => (u i : EuclideanSpace Real (Fin n))) Filter.atTop
        (𝓝 (x : EuclideanSpace Real (Fin n))) := by
  have hx : x ∈ closure s := (mem_closure_iff_frequently).2 h
  rcases (mem_closure_iff_seq_limit).1 hx with ⟨u, hu_mem, hu_tend⟩
  refine ⟨u, hu_mem, ?_⟩
  exact (tendsto_subtype_rng (f := u) (x := x)).1 hu_tend

/-- Lower semicontinuity implies the sequential liminf inequality. -/
lemma lowerSemicontinuousAtSeq_of_lowerSemicontinuousAt {n : Nat}
    (S : Set (EuclideanSpace Real (Fin n))) (f : S → EReal) (x : S) :
    LowerSemicontinuousAt f x → LowerSemicontinuousAtSeq S f x := by
  intro hx u hu
  have hx' : f x ≤ Filter.liminf f (𝓝 x) :=
    (lowerSemicontinuousAt_iff_le_liminf (f := f) (x := x)).1 hx
  have hu' : Filter.Tendsto u Filter.atTop (𝓝 x) :=
    (tendsto_subtype_rng (f := u) (x := x)).2 hu
  have hmap : Filter.map u Filter.atTop ≤ 𝓝 x := hu'
  have hlim : Filter.liminf f (𝓝 x) ≤ Filter.liminf f (Filter.map u Filter.atTop) :=
    Filter.liminf_le_liminf_of_le hmap
  have hle : f x ≤ Filter.liminf f (Filter.map u Filter.atTop) :=
    le_trans hx' hlim
  simpa [Filter.liminf, Filter.map_map] using hle

/-- Sequential lower semicontinuity implies filter lower semicontinuity. -/
lemma lowerSemicontinuousAt_of_lowerSemicontinuousAtSeq {n : Nat}
    (S : Set (EuclideanSpace Real (Fin n))) (f : S → EReal) (x : S) :
    LowerSemicontinuousAtSeq S f x → LowerSemicontinuousAt f x := by
  intro hseq y hy
  by_contra hnot
  have hfreq' : ∃ᶠ z in 𝓝 x, ¬ y < f z := (Filter.not_eventually).1 hnot
  have hfreq : ∃ᶠ z in 𝓝 x, f z ≤ y := by
    refine hfreq'.mono ?_
    intro z hz
    exact (lt_or_ge y (f z)).resolve_left hz
  rcases
      exists_seq_tendsto_of_frequently (S := S) (x := x)
        (s := {z : S | f z ≤ y}) hfreq with
    ⟨u, hu_mem, hu_tend⟩
  have hlim : f x ≤ Filter.liminf (fun i => f (u i)) Filter.atTop :=
    hseq u hu_tend
  have hfreq_seq : ∃ᶠ i in Filter.atTop, f (u i) ≤ y :=
    Filter.Frequently.of_forall (fun n => by simpa using hu_mem n)
  have hlim_le : Filter.liminf (fun i => f (u i)) Filter.atTop ≤ y :=
    Filter.liminf_le_of_frequently_le hfreq_seq
  have hcontr : f x ≤ y := le_trans hlim hlim_le
  exact (not_lt_of_ge hcontr) hy

/-- The sequential definition agrees with mathlib's `LowerSemicontinuousAt` on the subtype. -/
theorem lowerSemicontinuousAtSeq_iff_lowerSemicontinuousAt {n : Nat}
    (S : Set (EuclideanSpace Real (Fin n))) (f : S → EReal) (x : S) :
    LowerSemicontinuousAtSeq S f x ↔ LowerSemicontinuousAt f x := by
  constructor
  · exact lowerSemicontinuousAt_of_lowerSemicontinuousAtSeq (S := S) (f := f) (x := x)
  · exact lowerSemicontinuousAtSeq_of_lowerSemicontinuousAt (S := S) (f := f) (x := x)

/-- Text 7.0.2: With `f, S, x` as above, `f` is upper semicontinuous at `x` if for
every sequence `x_i ⊂ S` with `x_i → x`, `f x ≥ limsup (fun i => f (x_i))`.
Equivalently, `f x ≥ limsup_{y → x} f y`. -/
def UpperSemicontinuousAtSeq {n : Nat} (S : Set (EuclideanSpace Real (Fin n)))
    (f : S → EReal) (x : S) : Prop :=
  ∀ u : ℕ → S,
    Filter.Tendsto (fun i => (u i : EuclideanSpace Real (Fin n))) Filter.atTop
      (𝓝 (x : EuclideanSpace Real (Fin n))) →
      f x ≥ Filter.limsup (fun i => f (u i)) Filter.atTop

/-- Upper semicontinuity implies the sequential limsup inequality. -/
lemma upperSemicontinuousAtSeq_of_upperSemicontinuousAt {n : Nat}
    (S : Set (EuclideanSpace Real (Fin n))) (f : S → EReal) (x : S) :
    UpperSemicontinuousAt f x → UpperSemicontinuousAtSeq S f x := by
  intro hx u hu
  have hx' : Filter.limsup f (𝓝 x) ≤ f x :=
    (upperSemicontinuousAt_iff_limsup_le (f := f) (x := x)).1 hx
  have hu' : Filter.Tendsto u Filter.atTop (𝓝 x) :=
    (tendsto_subtype_rng (f := u) (x := x)).2 hu
  have hmap : Filter.map u Filter.atTop ≤ 𝓝 x := hu'
  have hlim : Filter.limsup f (Filter.map u Filter.atTop) ≤ Filter.limsup f (𝓝 x) :=
    Filter.limsup_le_limsup_of_le hmap
  have hle : Filter.limsup f (Filter.map u Filter.atTop) ≤ f x :=
    le_trans hlim hx'
  simpa [Filter.limsup, Filter.map_map] using hle

/-- Sequential upper semicontinuity implies filter upper semicontinuity. -/
lemma upperSemicontinuousAt_of_upperSemicontinuousAtSeq {n : Nat}
    (S : Set (EuclideanSpace Real (Fin n))) (f : S → EReal) (x : S) :
    UpperSemicontinuousAtSeq S f x → UpperSemicontinuousAt f x := by
  intro hseq y hy
  by_contra hnot
  have hfreq' : ∃ᶠ z in 𝓝 x, ¬ f z < y := (Filter.not_eventually).1 hnot
  have hfreq : ∃ᶠ z in 𝓝 x, y ≤ f z := by
    refine hfreq'.mono ?_
    intro z hz
    exact (lt_or_ge (f z) y).resolve_left hz
  rcases
      exists_seq_tendsto_of_frequently (S := S) (x := x)
        (s := {z : S | y ≤ f z}) hfreq with
    ⟨u, hu_mem, hu_tend⟩
  have hlim : Filter.limsup (fun i => f (u i)) Filter.atTop ≤ f x := by
    simpa using (hseq u hu_tend)
  have hfreq_seq : ∃ᶠ i in Filter.atTop, y ≤ f (u i) :=
    Filter.Frequently.of_forall (fun n => by simpa using hu_mem n)
  have hlim_le : y ≤ Filter.limsup (fun i => f (u i)) Filter.atTop :=
    Filter.le_limsup_of_frequently_le hfreq_seq
  have hcontr : y ≤ f x := le_trans hlim_le hlim
  exact (not_lt_of_ge hcontr) hy

/-- The sequential definition agrees with mathlib's `UpperSemicontinuousAt` on the subtype. -/
theorem upperSemicontinuousAtSeq_iff_upperSemicontinuousAt {n : Nat}
    (S : Set (EuclideanSpace Real (Fin n))) (f : S → EReal) (x : S) :
    UpperSemicontinuousAtSeq S f x ↔ UpperSemicontinuousAt f x := by
  constructor
  · exact upperSemicontinuousAt_of_upperSemicontinuousAtSeq (S := S) (f := f) (x := x)
  · exact upperSemicontinuousAtSeq_of_upperSemicontinuousAt (S := S) (f := f) (x := x)

/-- Lemma 7.0.3. Let `S` be a subset of `R^n`, `f : S → [-infty, +infty]`, and `x in S`. The
following are
equivalent: (i) for every sequence `x_i` in `S` with `x_i -> x`,
`f x >= limsup (fun i => f (x_i))`; (ii) `f x >= limsup_{y -> x} f y`, where
`limsup_{y -> x} f y := lim_{epsilon -> 0} sup { f y | y in S, |y - x| < epsilon }`. -/
lemma upperSemicontinuousAtSeq_iff_limsup_nhds {n : Nat}
    (S : Set (EuclideanSpace Real (Fin n))) (f : S → EReal) (x : S) :
    UpperSemicontinuousAtSeq S f x ↔
      f x ≥ Filter.limsup (fun y : S => f y) (𝓝 x) := by
  simpa using
    (upperSemicontinuousAtSeq_iff_upperSemicontinuousAt (S := S) (f := f) (x := x)).trans
      (upperSemicontinuousAt_iff_limsup_le (f := f) (x := x))

/-- A non-bottom `EReal` exceeds some real number. -/
lemma exists_real_not_le_of_ne_bot {x : EReal} (hx : x ≠ (⊥ : EReal)) :
    ∃ α : Real, ¬ x ≤ (α : EReal) := by
  classical
  cases x using EReal.rec with
  | bot =>
      cases hx rfl
  | coe r =>
      refine ⟨r - 1, ?_⟩
      have hlt : (r - 1 : Real) < r := by linarith
      have hltE : ((r - 1 : Real) : EReal) < (r : EReal) := by
        simpa using (EReal.coe_lt_coe_iff).2 hlt
      exact not_le_of_gt hltE
  | top =>
      refine ⟨0, ?_⟩
      simp [top_le_iff]

/-- Real sublevel sets control the bottom sublevel set. -/
lemma isClosed_sublevel_bot_of_closed_sublevels {n : Nat}
    {f : (Fin n → Real) → EReal}
    (h : ∀ α : Real, IsClosed {x | f x ≤ (α : EReal)}) :
    IsClosed {x | f x ≤ (⊥ : EReal)} := by
  have hclosed : IsClosed (⋂ α : Real, {x | f x ≤ (α : EReal)}) := by
    refine isClosed_iInter ?_
    intro α
    simpa using h α
  have hset :
      {x | f x ≤ (⊥ : EReal)} = ⋂ α : Real, {x | f x ≤ (α : EReal)} := by
    ext x
    constructor
    · intro hx
      have hx' : ∀ α : Real, f x ≤ (α : EReal) := by
        intro α
        exact le_trans hx bot_le
      simpa using hx'
    · intro hx
      have hx' : ∀ α : Real, f x ≤ (α : EReal) := by
        simpa using hx
      have hbot : f x = (⊥ : EReal) := by
        by_contra hne
        rcases exists_real_not_le_of_ne_bot (x := f x) hne with ⟨α, hα⟩
        exact hα (hx' α)
      simp [hbot]
  exact hset.symm ▸ hclosed

/-- Lower semicontinuity is equivalent to closed real sublevel sets. -/
lemma lowerSemicontinuous_iff_closed_sublevel {n : Nat} (f : (Fin n → Real) → EReal) :
    LowerSemicontinuous f ↔ ∀ α : Real, IsClosed {x | f x ≤ (α : EReal)} := by
  constructor
  · intro hf α
    have h :=
      (lowerSemicontinuous_iff_isClosed_preimage (f := f)).1 hf (α : EReal)
    simpa [Set.preimage, Set.Iic] using h
  · intro h
    refine (lowerSemicontinuous_iff_isClosed_preimage (f := f)).2 ?_
    refine (EReal.forall).2 ?_
    refine ⟨?_, ?_, ?_⟩
    · have hbot : IsClosed {x | f x ≤ (⊥ : EReal)} :=
        isClosed_sublevel_bot_of_closed_sublevels (f := f) h
      change IsClosed {x | f x ≤ (⊥ : EReal)}
      exact hbot
    · simp [Set.preimage, Set.Iic]
    · intro α
      have hα : IsClosed {x | f x ≤ (α : EReal)} := h α
      change IsClosed {x | f x ≤ (α : EReal)}
      exact hα

/-- Closedness of the epigraph implies closedness of every real sublevel set. -/
lemma closed_sublevel_of_closed_epigraph {n : Nat} {f : (Fin n → Real) → EReal}
    (h : IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) f)) :
    ∀ α : Real, IsClosed {x | f x ≤ (α : EReal)} := by
  intro α
  have hcont : Continuous (fun x : Fin n → Real => (x, α)) := by
    simpa using (Continuous.prodMk_left (X := (Fin n → Real)) (Y := Real) α)
  have hpre :
      (fun x : Fin n → Real => (x, α)) ⁻¹'
          epigraph (S := (Set.univ : Set (Fin n → Real))) f =
        {x | f x ≤ (α : EReal)} := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨Set.mem_univ x, hx⟩
  have hclosed :
      IsClosed ((fun x : Fin n → Real => (x, α)) ⁻¹'
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
    h.preimage hcont
  simpa [hpre] using hclosed

/-- Closed real sublevel sets imply closedness of the epigraph. -/
lemma closed_epigraph_of_closed_sublevel {n : Nat} {f : (Fin n → Real) → EReal}
    (h : ∀ α : Real, IsClosed {x | f x ≤ (α : EReal)}) :
    IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
  have hsc : LowerSemicontinuous f :=
    (lowerSemicontinuous_iff_closed_sublevel (f := f)).2 h
  have hclosed :
      IsClosed {p : (Fin n → Real) × EReal | f p.1 ≤ p.2} :=
    hsc.isClosed_epigraph
  have hcont : Continuous (fun p : (Fin n → Real) × Real => (p.1, (p.2 : EReal))) := by
    refine Continuous.prodMk continuous_fst ?_
    exact continuous_coe_real_ereal.comp continuous_snd
  have hpre :
      (fun p : (Fin n → Real) × Real => (p.1, (p.2 : EReal))) ⁻¹'
          {p : (Fin n → Real) × EReal | f p.1 ≤ p.2} =
        epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
    ext p
    constructor
    · intro hp
      exact ⟨Set.mem_univ p.1, hp⟩
    · intro hp
      exact hp.2
  have hclosed' :
      IsClosed ((fun p : (Fin n → Real) × Real => (p.1, (p.2 : EReal))) ⁻¹'
        {p : (Fin n → Real) × EReal | f p.1 ≤ p.2}) :=
    hclosed.preimage hcont
  simpa [hpre] using hclosed'

/-- Theorem 7.1. Let `f : ℝ^n → [-∞, +∞]`. The following are equivalent:
(a) `f` is lower semicontinuous on `ℝ^n`;
(b) `{x | f x ≤ α}` is closed for every `α ∈ ℝ`;
(c) the epigraph of `f` is closed in `ℝ^{n+1}`. -/
theorem lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph {n : Nat}
    (f : (Fin n → Real) → EReal) :
    ((LowerSemicontinuous f ↔ ∀ α : Real, IsClosed {x | f x ≤ (α : EReal)}) ∧
      ((∀ α : Real, IsClosed {x | f x ≤ (α : EReal)}) ↔
        IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) f))) := by
  refine ⟨lowerSemicontinuous_iff_closed_sublevel (f := f), ?_⟩
  constructor
  · intro h
    exact closed_epigraph_of_closed_sublevel (f := f) h
  · intro h
    exact closed_sublevel_of_closed_epigraph (f := f) h

/-- Text 7.0.4: Given any function `f` on `ℝ^n`, there exists a greatest lower
semicontinuous function majorized by `f`; this function is called the lower
semicontinuous hull of `f`. The pointwise supremum of lower semicontinuous
minorants of `f` is lower semicontinuous. -/
lemma lscHull_candidate_lsc {n : Nat} (f : (Fin n → Real) → EReal) :
    LowerSemicontinuous (fun x =>
      ⨆ h :
        {h : (Fin n → Real) → EReal // LowerSemicontinuous h ∧ h ≤ f}, h.1 x) := by
  classical
  refine lowerSemicontinuous_iSup ?_
  intro h
  exact h.property.1

/-- The pointwise supremum of lower semicontinuous minorants of `f` lies below `f`. -/
lemma lscHull_candidate_le {n : Nat} (f : (Fin n → Real) → EReal) :
    (fun x =>
        ⨆ h :
          {h : (Fin n → Real) → EReal // LowerSemicontinuous h ∧ h ≤ f}, h.1 x) ≤ f := by
  intro x
  refine iSup_le ?_
  intro h
  exact h.property.2 x

/-- Any lower semicontinuous `h ≤ f` is bounded above by the candidate hull. -/
lemma lscHull_candidate_max {n : Nat} {f : (Fin n → Real) → EReal}
    {h : (Fin n → Real) → EReal} (hh : LowerSemicontinuous h) (hle : h ≤ f) :
    h ≤
      (fun x =>
        ⨆ h' :
          {h : (Fin n → Real) → EReal // LowerSemicontinuous h ∧ h ≤ f}, h'.1 x) := by
  intro x
  exact
    le_iSup (fun h' :
        {h : (Fin n → Real) → EReal // LowerSemicontinuous h ∧ h ≤ f} => h'.1 x)
      ⟨h, hh, hle⟩

theorem exists_lowerSemicontinuousHull {n : Nat} (f : (Fin n → Real) → EReal) :
    ∃ g : (Fin n → Real) → EReal,
      LowerSemicontinuous g ∧ g ≤ f ∧
        ∀ h : (Fin n → Real) → EReal, LowerSemicontinuous h → h ≤ f → h ≤ g := by
  classical
  let g : (Fin n → Real) → EReal :=
    fun x =>
      ⨆ h :
        {h : (Fin n → Real) → EReal // LowerSemicontinuous h ∧ h ≤ f}, h.1 x
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [g] using (lscHull_candidate_lsc (f := f))
  · simpa [g] using (lscHull_candidate_le (f := f))
  · intro h hh hle
    simpa [g] using (lscHull_candidate_max (f := f) (h := h) hh hle)

/-- Text 7.0.4: The lower semicontinuous hull of `f`. -/
noncomputable def lowerSemicontinuousHull {n : Nat} (f : (Fin n → Real) → EReal) :
    (Fin n → Real) → EReal := by
  classical
  exact Classical.choose (exists_lowerSemicontinuousHull (n := n) f)

/-- Text 7.0.5: The closure of a convex function `f` is the lower semicontinuous hull
when `f` is never `-∞`, whereas it is the constant function `-∞` when `f` is an
improper convex function with `f x = -∞` for some `x`. -/
noncomputable def convexFunctionClosure {n : Nat} (f : (Fin n → Real) → EReal) :
    (Fin n → Real) → EReal := by
  classical
  by_cases h : ∀ x, f x ≠ (⊥ : EReal)
  · exact lowerSemicontinuousHull f
  · exact fun _ => (⊥ : EReal)

/-- Text 7.0.6: A convex function is called closed if it is lower semicontinuous on `ℝ^n`. -/
def ClosedConvexFunction {n : Nat} (f : (Fin n → Real) → EReal) : Prop :=
  ConvexFunction f ∧ LowerSemicontinuous f

/-- Text 7.0.6: A proper convex function is closed iff it is lower semicontinuous. -/
theorem properConvexFunction_closed_iff_lowerSemicontinuous {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ClosedConvexFunction f ↔ LowerSemicontinuous f := by
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  constructor
  · intro hclosed
    exact hclosed.2
  · intro hls
    exact ⟨hconv, hls⟩

/- Text 7.0.7: The only closed improper convex functions are the constant functions
`+∞` and `-∞`. -/
/-- The constant `⊤` function is closed and improper. -/
lemma closed_improper_const_top {n : Nat} :
    ClosedConvexFunction (fun _ : (Fin n → Real) => (⊤ : EReal)) ∧
      ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun _ : (Fin n → Real) => (⊤ : EReal)) := by
  have hset_epi :
      epigraph (Set.univ : Set (Fin n → Real)) (fun _ => (⊤ : EReal)) = (∅) := by
    ext p
    constructor
    · intro hp
      exact (not_top_le_coe p.2) hp.2
    · intro hp
      exact hp.elim
  have hconv : ConvexFunction (fun _ : (Fin n → Real) => (⊤ : EReal)) := by
    unfold ConvexFunction ConvexFunctionOn
    simpa [hset_epi] using
      (convex_empty : Convex ℝ (∅ : Set ((Fin n → Real) × Real)))
  have hlsc : LowerSemicontinuous (fun _ : (Fin n → Real) => (⊤ : EReal)) := by
    refine (lowerSemicontinuous_iff_closed_sublevel
      (f := fun _ : (Fin n → Real) => (⊤ : EReal))).2 ?_
    intro α
    have hset :
        {x : (Fin n → Real) | (⊤ : EReal) ≤ (α : EReal)} =
          (∅ : Set (Fin n → Real)) := by
      ext x
      constructor
      · intro hx
        exact (not_top_le_coe α) hx
      · intro hx
        exact hx.elim
    simp
  have hclosed : ClosedConvexFunction (fun _ : (Fin n → Real) => (⊤ : EReal)) :=
    ⟨hconv, hlsc⟩
  have himproper :
      ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun _ : (Fin n → Real) => (⊤ : EReal)) := by
    refine ⟨?_, ?_⟩
    · simpa [ConvexFunction] using hconv
    · intro hproper
      rcases hproper with ⟨_, hne_epi, _⟩
      rcases hne_epi with ⟨p, hp⟩
      simp [hset_epi] at hp
  exact ⟨hclosed, himproper⟩

/-- The constant `⊥` function is closed and improper. -/
lemma closed_improper_const_bot {n : Nat} :
    ClosedConvexFunction (fun _ : (Fin n → Real) => (⊥ : EReal)) ∧
      ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun _ : (Fin n → Real) => (⊥ : EReal)) := by
  have hset_epi :
      epigraph (Set.univ : Set (Fin n → Real)) (fun _ => (⊥ : EReal)) =
        (Set.univ : Set ((Fin n → Real) × Real)) := by
    ext p
    constructor
    · intro hp
      exact Set.mem_univ p
    · intro hp
      exact ⟨by exact Set.mem_univ p.1, bot_le⟩
  have hconv : ConvexFunction (fun _ : (Fin n → Real) => (⊥ : EReal)) := by
    unfold ConvexFunction ConvexFunctionOn
    simpa [hset_epi] using
      (convex_univ : Convex ℝ (Set.univ : Set ((Fin n → Real) × Real)))
  have hlsc : LowerSemicontinuous (fun _ : (Fin n → Real) => (⊥ : EReal)) := by
    refine (lowerSemicontinuous_iff_closed_sublevel
      (f := fun _ : (Fin n → Real) => (⊥ : EReal))).2 ?_
    intro α
    have hset :
        {x : (Fin n → Real) | (⊥ : EReal) ≤ (α : EReal)} =
          (Set.univ : Set (Fin n → Real)) := by
      ext x
      constructor
      · intro hx
        exact Set.mem_univ x
      · intro hx
        simp
    simp
  have hclosed : ClosedConvexFunction (fun _ : (Fin n → Real) => (⊥ : EReal)) :=
    ⟨hconv, hlsc⟩
  have himproper :
      ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun _ : (Fin n → Real) => (⊥ : EReal)) := by
    refine ⟨?_, ?_⟩
    · simpa [ConvexFunction] using hconv
    · intro hproper
      rcases hproper with ⟨_, _, hnotbot⟩
      have hbot := hnotbot (0 : Fin n → Real) (by simp)
      exact hbot rfl
  exact ⟨hclosed, himproper⟩

/-- An improper convex function has empty epigraph or attains `⊥` on the set. -/
lemma improperConvexFunctionOn_cases_epigraph_empty_or_bot {n : Nat}
    {S : Set (Fin n → Real)} {f : (Fin n → Real) → EReal}
    (h : ImproperConvexFunctionOn S f) :
    (¬ Set.Nonempty (epigraph S f)) ∨ ∃ x ∈ S, f x = (⊥ : EReal) := by
  classical
  rcases h with ⟨hconv, hnotproper⟩
  by_cases hne : Set.Nonempty (epigraph S f)
  · by_cases hbot : ∀ x ∈ S, f x ≠ (⊥ : EReal)
    · have hproper : ProperConvexFunctionOn S f := ⟨hconv, hne, hbot⟩
      exact (hnotproper hproper).elim
    · right
      push_neg at hbot
      rcases hbot with ⟨x, hxS, hxbot⟩
      exact ⟨x, hxS, hxbot⟩
  · left
    exact hne

/-- If the epigraph is empty, then the function is identically `⊤` on `S`. -/
lemma epigraph_empty_imp_forall_top {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} (h : ¬ Set.Nonempty (epigraph S f)) :
    ∀ x ∈ S, f x = (⊤ : EReal) := by
  classical
  intro x hxS
  by_contra hne
  have hlt : f x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hne
  have hxdom : x ∈ effectiveDomain S f := by
    have hx' : x ∈ {x | x ∈ S ∧ f x < (⊤ : EReal)} := ⟨hxS, hlt⟩
    simpa [effectiveDomain_eq] using hx'
  have hdom : Set.Nonempty (effectiveDomain S f) := ⟨x, hxdom⟩
  have hne_epi : Set.Nonempty (epigraph S f) :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain (S := S) (f := f)).2 hdom
  exact h hne_epi

/-- If `f` attains `⊥`, then its closure is the constant `⊥` function. -/
lemma convexFunctionClosure_eq_bot_of_exists_bot {n : Nat}
    {f : (Fin n → Real) → EReal} (h : ∃ x, f x = (⊥ : EReal)) :
    convexFunctionClosure f = (fun _ => (⊥ : EReal)) := by
  classical
  have h' : ¬ ∀ x, f x ≠ (⊥ : EReal) := by
    intro hne
    rcases h with ⟨x, hx⟩
    exact hne x hx
  simp [convexFunctionClosure, h']

/-- The closure of the constant `⊤` function is itself. -/
lemma convexFunctionClosure_const_top {n : Nat} :
    convexFunctionClosure (fun _ : (Fin n → Real) => (⊤ : EReal)) =
      (fun _ : (Fin n → Real) => (⊤ : EReal)) := by
  classical
  have hne :
      ∀ x : (Fin n → Real),
        (fun _ : (Fin n → Real) => (⊤ : EReal)) x ≠ (⊥ : EReal) := by
    intro x
    simp
  have hspec :=
    Classical.choose_spec
      (exists_lowerSemicontinuousHull (n := n)
        (fun _ : (Fin n → Real) => (⊤ : EReal)))
  have hls : LowerSemicontinuous (fun _ : (Fin n → Real) => (⊤ : EReal)) := by
    refine (lowerSemicontinuous_iff_closed_sublevel
      (f := fun _ : (Fin n → Real) => (⊤ : EReal))).2 ?_
    intro α
    have hset :
        {x : (Fin n → Real) | (⊤ : EReal) ≤ (α : EReal)} =
          (∅ : Set (Fin n → Real)) := by
      ext x
      constructor
      · intro hx
        exact (not_top_le_coe α) hx
      · intro hx
        exact hx.elim
    simp
  have hle :
      lowerSemicontinuousHull (fun _ : (Fin n → Real) => (⊤ : EReal)) ≤
        (fun _ : (Fin n → Real) => (⊤ : EReal)) :=
    hspec.2.1
  have hge :
      (fun _ : (Fin n → Real) => (⊤ : EReal)) ≤
        lowerSemicontinuousHull (fun _ : (Fin n → Real) => (⊤ : EReal)) := by
    have hle_self :
        (fun _ : (Fin n → Real) => (⊤ : EReal)) ≤
          (fun _ : (Fin n → Real) => (⊤ : EReal)) := by
      intro x
      rfl
    exact hspec.2.2 _ hls hle_self
  have hEq :
      lowerSemicontinuousHull (fun _ : (Fin n → Real) => (⊤ : EReal)) =
        (fun _ : (Fin n → Real) => (⊤ : EReal)) :=
    le_antisymm hle hge
  simp [convexFunctionClosure, hEq]

theorem closed_improperConvexFunction_eq_top_or_bot {n : Nat}
    {f : (Fin n → Real) → EReal} :
    (convexFunctionClosure f = f ∧
        ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) ↔
      f = (fun _ => (⊤ : EReal)) ∨ f = (fun _ => (⊥ : EReal)) := by
  constructor
  · intro h
    rcases h with ⟨hcl, himp⟩
    rcases
        improperConvexFunctionOn_cases_epigraph_empty_or_bot
          (S := (Set.univ : Set (Fin n → Real))) (f := f) himp with
      hcase | hcase
    · left
      funext x
      have hx : x ∈ (Set.univ : Set (Fin n → Real)) := by simp
      exact
        epigraph_empty_imp_forall_top (S := (Set.univ : Set (Fin n → Real))) (f := f)
          hcase x hx
    · right
      rcases hcase with ⟨x, hxS, hxbot⟩
      have hclbot :
          convexFunctionClosure f = (fun _ => (⊥ : EReal)) :=
        convexFunctionClosure_eq_bot_of_exists_bot (f := f) ⟨x, hxbot⟩
      calc
        f = convexFunctionClosure f := by symm; exact hcl
        _ = (fun _ => (⊥ : EReal)) := hclbot
  · intro h
    rcases h with h | h
    · subst h
      refine ⟨?_, (closed_improper_const_top (n := n)).2⟩
      simpa using (convexFunctionClosure_const_top (n := n))
    · subst h
      refine ⟨?_, (closed_improper_const_bot (n := n)).2⟩
      have hcl :
          convexFunctionClosure (fun _ : (Fin n → Real) => (⊥ : EReal)) =
            (fun _ : (Fin n → Real) => (⊥ : EReal)) :=
        convexFunctionClosure_eq_bot_of_exists_bot
          (f := fun _ : (Fin n → Real) => (⊥ : EReal)) ⟨(0 : Fin n → Real), rfl⟩
      simpa using hcl

/-- Convexity of the reciprocal on `(0, ∞)` extended by `⊤` outside. -/
lemma convexFunctionOn_inv_pos_aux :
    ConvexFunctionOn Set.univ (fun x : Fin 1 → Real =>
      if 0 < x 0 then ((1 / x 0 : Real) : EReal) else (⊤ : EReal)) := by
  have hconv_real :
      ConvexOn ℝ {x : Fin 1 → Real | 0 < x 0} (fun x : Fin 1 → Real => 1 / x 0) := by
    simpa [Set.preimage, LinearMap.proj_apply, one_div] using
      (convexOn_comp_proj (s := Set.Ioi (0 : ℝ))
        (f := fun r : ℝ => r⁻¹) convexOn_inv_Ioi)
  have hconv :
      ConvexFunctionOn Set.univ (fun x : Fin 1 → Real =>
        if x ∈ {x : Fin 1 → Real | 0 < x 0} then ((1 / x 0 : Real) : EReal) else
          (⊤ : EReal)) :=
    convexFunctionOn_univ_if_top (C := {x : Fin 1 → Real | 0 < x 0})
      (g := fun x : Fin 1 → Real => 1 / x 0) hconv_real
  simpa using hconv

/-- Lower semicontinuity of the reciprocal on `(0, ∞)` extended by `⊤` outside. -/
lemma lowerSemicontinuous_inv_pos_aux :
    LowerSemicontinuous (fun x : Fin 1 → Real =>
      if 0 < x 0 then ((1 / x 0 : Real) : EReal) else (⊤ : EReal)) := by
  classical
  refine (lowerSemicontinuous_iff_closed_sublevel
    (f := fun x : Fin 1 → Real =>
      if 0 < x 0 then ((1 / x 0 : Real) : EReal) else (⊤ : EReal))).2 ?_
  intro α
  by_cases hα : α ≤ 0
  · have hset :
        {x : Fin 1 → Real |
            (if 0 < x 0 then ((1 / x 0 : Real) : EReal) else (⊤ : EReal))
              ≤ (α : EReal)} = (∅ : Set (Fin 1 → Real)) := by
      ext x; constructor
      · intro hx
        by_cases hx0 : 0 < x 0
        · have hle : (1 / x 0 : Real) ≤ α := by
            simpa [hx0] using hx
          have hpos : 0 < (1 / x 0 : Real) := by
            exact one_div_pos.mpr hx0
          have hαpos : 0 < α := lt_of_lt_of_le hpos hle
          exact (not_lt_of_ge hα) hαpos
        · have hx'' := hx
          simp [hx0] at hx''
      · intro hx
        exact hx.elim
    rw [hset]
    simp
  · have hαpos : 0 < α := lt_of_not_ge hα
    have hset :
        {x : Fin 1 → Real |
            (if 0 < x 0 then ((1 / x 0 : Real) : EReal) else (⊤ : EReal))
              ≤ (α : EReal)} = {x : Fin 1 → Real | (1 / α : Real) ≤ x 0} := by
      ext x; constructor
      · intro hx
        by_cases hx0 : 0 < x 0
        · have hle : (1 / x 0 : Real) ≤ α := by
            simpa [hx0] using hx
          exact (one_div_le (ha := hx0) (hb := hαpos)).1 hle
        · have hx'' := hx
          simp [hx0] at hx''
      · intro hx
        have hx0 : 0 < x 0 := by
          have hpos : 0 < (1 / α : Real) := one_div_pos.mpr hαpos
          exact lt_of_lt_of_le hpos hx
        have hle : (1 / x 0 : Real) ≤ α :=
          (one_div_le (ha := hx0) (hb := hαpos)).2 hx
        simpa [hx0] using (show ((1 / x 0 : Real) : EReal) ≤ (α : EReal) by
          simpa using hle)
    have hclosed :
        IsClosed {x : Fin 1 → Real | (1 / α : Real) ≤ x 0} := by
      have hcont : Continuous (fun x : Fin 1 → Real => x 0) := by
        simpa using (continuous_apply (i := (0 : Fin 1)))
      have hset' :
          {x : Fin 1 → Real | (1 / α : Real) ≤ x 0} =
            (fun x : Fin 1 → Real => x 0) ⁻¹' Set.Ici (1 / α) := by
        ext x; rfl
      simpa [hset'] using (isClosed_Ici.preimage hcont)
    rw [hset]
    exact hclosed

/-- The effective domain of the reciprocal example is the positive half-line. -/
lemma effectiveDomain_inv_pos_eq :
    effectiveDomain (Set.univ : Set (Fin 1 → Real))
        (fun x : Fin 1 → Real =>
          if 0 < x 0 then ((1 / x 0 : Real) : EReal) else (⊤ : EReal)) =
      {x : Fin 1 → Real | 0 < x 0} := by
  ext x
  by_cases hx0 : 0 < x 0
  · have : x ∈ {x : Fin 1 → Real | 0 < x 0} := by
      simp [hx0]
    simp [effectiveDomain_eq, hx0, this]
  · have : x ∉ {x : Fin 1 → Real | 0 < x 0} := by
      simp [hx0]
    simp [effectiveDomain_eq, hx0, this]

/-- The positive half-line in `Fin 1 → Real` is not closed. -/
lemma not_isClosed_effectiveDomain_inv_pos :
    ¬ IsClosed {x : Fin 1 → Real | 0 < x 0} := by
  intro hclosed
  have hmem : (0 : Fin 1 → Real) ∈ closure {x : Fin 1 → Real | 0 < x 0} := by
    refine (mem_closure_iff_seq_limit).2 ?_
    let u : ℕ → Fin 1 → Real := fun n => fun _ => 1 / ((n : ℝ) + 1)
    refine ⟨u, ?_, ?_⟩
    · intro n
      have hn : 0 < (n : ℝ) + 1 := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        have h1 : (0 : ℝ) < (1 : ℝ) := by norm_num
        exact add_pos_of_nonneg_of_pos hn0 h1
      have hpos : 0 < (1 / ((n : ℝ) + 1)) := one_div_pos.mpr hn
      simpa [u] using hpos
    · refine (tendsto_pi_nhds).2 ?_
      intro i
      simpa [u] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hnot : (0 : Fin 1 → Real) ∉ {x : Fin 1 → Real | 0 < x 0} := by
    simp
  have hclosure :
      closure {x : Fin 1 → Real | 0 < x 0} = {x : Fin 1 → Real | 0 < x 0} :=
    hclosed.closure_eq
  have hmem' : (0 : Fin 1 → Real) ∈ {x : Fin 1 → Real | 0 < x 0} := by
    have hmem' := hmem
    rw [hclosure] at hmem'
    exact hmem'
  exact hnot hmem'

/-- Text 7.0.8: It can happen that a closed proper convex function has a domain that is not
closed. -/
theorem exists_closed_proper_convexFunction_domain_not_closed :
    ∃ n : Nat, ∃ f : (Fin n → Real) → EReal,
      ClosedConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f ∧
          ¬ IsClosed (effectiveDomain (S := (Set.univ : Set (Fin n → Real))) f) := by
  classical
  let f : (Fin 1 → Real) → EReal :=
    fun x => if 0 < x 0 then ((1 / x 0 : Real) : EReal) else (⊤ : EReal)
  refine ⟨1, f, ?_, ?_, ?_⟩
  · have hconv_on : ConvexFunctionOn Set.univ f := by
      simpa [f] using convexFunctionOn_inv_pos_aux
    have hconv : ConvexFunction f := by
      simpa [ConvexFunction] using hconv_on
    have hlsc : LowerSemicontinuous f := by
      simpa [f] using lowerSemicontinuous_inv_pos_aux
    exact ⟨hconv, hlsc⟩
  · have hconv_on : ConvexFunctionOn Set.univ f := by
      simpa [f] using convexFunctionOn_inv_pos_aux
    have hnonempty :
        Set.Nonempty (epigraph (Set.univ : Set (Fin 1 → Real)) f) := by
      refine ⟨((fun _ : Fin 1 => (1 : Real)), (1 : Real)), ?_⟩
      have hpos : 0 < (1 : Real) := by norm_num
      have hle : f (fun _ : Fin 1 => (1 : Real)) ≤ (1 : EReal) := by
        simp [f, hpos]
      have hmem :
          (fun _ : Fin 1 => (1 : Real)) ∈ (Set.univ : Set (Fin 1 → Real)) := by
        simp
      exact ⟨hmem, hle⟩
    have hbot : ∀ x ∈ (Set.univ : Set (Fin 1 → Real)), f x ≠ (⊥ : EReal) := by
      intro x hx
      by_cases hx0 : 0 < x 0 <;> simp [f, hx0]
    exact ⟨hconv_on, hnonempty, hbot⟩
  · have hdom :
        effectiveDomain (S := (Set.univ : Set (Fin 1 → Real))) f =
          {x : Fin 1 → Real | 0 < x 0} := by
      simpa [f] using effectiveDomain_inv_pos_eq
    simpa [hdom] using not_isClosed_effectiveDomain_inv_pos

/-- Text 7.0.9: For example, the function `f(x) = 1/x` for `x > 0` and `f(x) = +∞`
for `x ≤ 0` is closed. -/
theorem closedConvexFunction_inv_pos :
    ClosedConvexFunction (fun x : (Fin 1 → Real) =>
      if 0 < x 0 then ((1 / (x 0) : Real) : EReal) else (⊤ : EReal)) := by
  refine ⟨?_, ?_⟩
  · have hconv_on : ConvexFunctionOn Set.univ (fun x : Fin 1 → Real =>
      if 0 < x 0 then ((1 / x 0 : Real) : EReal) else (⊤ : EReal)) := by
      simpa using convexFunctionOn_inv_pos_aux
    simpa [ConvexFunction] using hconv_on
  · simpa using lowerSemicontinuous_inv_pos_aux

/-- If `g` is lower semicontinuous and `g ≤ f`, then `closure (epi f) ⊆ epi g`. -/
lemma closure_epigraph_subset_epigraph_of_lsc_le {n : Nat}
    {f g : (Fin n → Real) → EReal}
    (hg : LowerSemicontinuous g) (hle : g ≤ f) :
    closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) ⊆
      epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
  have hsubset :
      epigraph (S := (Set.univ : Set (Fin n → Real))) f ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
    intro p hp
    have hfp : f p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := f)).1 hp
    have hgp : g p.1 ≤ (p.2 : EReal) := le_trans (hle p.1) hfp
    exact (mem_epigraph_univ_iff (f := g)).2 hgp
  have hclosed_sub :
      ∀ α : Real, IsClosed {x | g x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := g)).1 hg
  have hclosed :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) g) :=
    closed_epigraph_of_closed_sublevel (f := g) hclosed_sub
  exact closure_minimal hsubset hclosed

/-- A lower semicontinuous minorant lies below the liminf of its majorant. -/
lemma lowerSemicontinuous_le_liminf_of_le {n : Nat}
    {f g : (Fin n → Real) → EReal}
    (hg : LowerSemicontinuous g) (hle : g ≤ f) :
    ∀ x, g x ≤ Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) := by
  intro x
  have hle_liminf_g :
      g x ≤ Filter.liminf (fun y : Fin n → Real => g y) (𝓝 x) := by
    simpa using (hg.le_liminf x)
  have h_eventually :
      ∀ᶠ y in 𝓝 x, g y ≤ f y :=
    Filter.Eventually.of_forall (fun y => hle y)
  have hle_liminf :
      Filter.liminf (fun y : Fin n → Real => g y) (𝓝 x) ≤
        Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) :=
    Filter.liminf_le_liminf h_eventually
  exact le_trans hle_liminf_g hle_liminf

/-- The closure of an epigraph is upward closed in the second coordinate. -/
lemma closure_epigraph_upward {n : Nat} {f : (Fin n → Real) → EReal}
    {x : Fin n → Real} {μ ν : Real} (hμν : μ ≤ ν) :
    (x, μ) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) →
      (x, ν) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
  intro hx
  let T : ((Fin n → Real) × Real) → ((Fin n → Real) × Real) :=
    fun p => (p.1, p.2 + (ν - μ))
  have hcont : Continuous T := by
    have hfst : Continuous (fun p : (Fin n → Real) × Real => p.1) := continuous_fst
    have hsnd : Continuous (fun p : (Fin n → Real) × Real => p.2 + (ν - μ)) := by
      simpa using (continuous_snd.add continuous_const)
    exact hfst.prodMk hsnd
  have himage :
      T '' epigraph (S := (Set.univ : Set (Fin n → Real))) f ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
    intro p hp
    rcases hp with ⟨p, hp, rfl⟩
    rcases p with ⟨y, t⟩
    have hfp : f y ≤ (t : EReal) := (mem_epigraph_univ_iff (f := f)).1 hp
    have hle : (t : EReal) ≤ (t + (ν - μ) : Real) := by
      exact (EReal.coe_le_coe_iff).2 (by linarith)
    have hfp' : f y ≤ (t + (ν - μ) : Real) := le_trans hfp hle
    exact (mem_epigraph_univ_iff (f := f)).2 hfp'
  have hximage :
      T (x, μ) ∈ closure (T '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    have hsubset :=
      image_closure_subset_closure_image (f := T)
        (s := epigraph (S := (Set.univ : Set (Fin n → Real))) f) hcont
    have hxmem :
        T (x, μ) ∈ T '' closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
      exact ⟨(x, μ), hx, rfl⟩
    exact hsubset hxmem
  have hclosure :
      closure (T '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) ⊆
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
    closure_mono himage
  have hxT : T (x, μ) = (x, ν) := by
    ext <;> simp [T]
  exact hclosure (by simpa [hxT] using hximage)

/-- The function obtained by taking the infimum of each vertical slice of the epigraph closure. -/
noncomputable def epigraphClosureInf {n : Nat} (f : (Fin n → Real) → EReal) :
    (Fin n → Real) → EReal :=
  fun x =>
    sInf ((fun μ : Real => (μ : EReal)) '' {μ : Real |
      (x, μ) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)})

/-- The closure of an epigraph is the epigraph of `epigraphClosureInf`. -/
lemma closure_epigraph_eq_epigraph_sInf {n : Nat} (f : (Fin n → Real) → EReal) :
    epigraph (S := (Set.univ : Set (Fin n → Real))) (epigraphClosureInf f) =
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
  classical
  ext p
  rcases p with ⟨x, μ⟩
  constructor
  · intro hp
    have hμ :
        epigraphClosureInf f x ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := epigraphClosureInf f)).1 hp
    let A : Set EReal :=
      (fun t : Real => (t : EReal)) '' {t : Real |
        (x, t) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)}
    have hA : epigraphClosureInf f x = sInf A := rfl
    have hmem_seq :
        ∀ k : ℕ,
          (x, μ + 1 / ((k : ℝ) + 1)) ∈
            closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
      intro k
      have hpos : 0 < (1 / ((k : ℝ) + 1)) := by
        have hden : 0 < (k : ℝ) + 1 := by nlinarith
        exact one_div_pos.2 hden
      have hμlt_real : μ < μ + 1 / ((k : ℝ) + 1) := by linarith
      have hμlt :
          (μ : EReal) < (μ + 1 / ((k : ℝ) + 1) : ℝ) := by
        exact (EReal.coe_lt_coe_iff).2 hμlt_real
      have hlt :
          sInf A < (μ + 1 / ((k : ℝ) + 1) : ℝ) := by
        have hμ' : sInf A ≤ (μ : EReal) := by simpa [hA] using hμ
        exact lt_of_le_of_lt hμ' hμlt
      rcases (sInf_lt_iff).1 hlt with ⟨a, haA, haLt⟩
      rcases haA with ⟨μ0, hμ0, rfl⟩
      have hμ0lt : μ0 < μ + 1 / ((k : ℝ) + 1) :=
        (EReal.coe_lt_coe_iff).1 haLt
      have hμ0le : μ0 ≤ μ + 1 / ((k : ℝ) + 1) := le_of_lt hμ0lt
      exact
        closure_epigraph_upward (f := f) (x := x) (μ := μ0)
          (ν := μ + 1 / ((k : ℝ) + 1)) hμ0le hμ0
    have h_tendsto :
        Filter.Tendsto (fun k : ℕ => (x, μ + 1 / ((k : ℝ) + 1))) Filter.atTop
          (𝓝 (x, μ)) := by
      refine (Prod.tendsto_iff
        (seq := fun k : ℕ => (x, μ + 1 / ((k : ℝ) + 1)))
        (p := (x, μ))).2 ?_
      constructor
      · simp
      · have hconst :
            Filter.Tendsto (fun _ : ℕ => μ) Filter.atTop (𝓝 μ) :=
          tendsto_const_nhds
        have hdiv :
            Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
              Filter.atTop (𝓝 (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using (hconst.add hdiv)
    have hclosed :
        IsClosed (closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)) :=
      isClosed_closure
    have hmem_eventually :
        ∀ᶠ k : ℕ in Filter.atTop,
          (x, μ + 1 / ((k : ℝ) + 1)) ∈
            closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
      Filter.Eventually.of_forall hmem_seq
    exact hclosed.mem_of_tendsto h_tendsto hmem_eventually
  · intro hp
    have hmem :
        ((μ : EReal)) ∈
          (fun t : Real => (t : EReal)) '' {t : Real |
            (x, t) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)} :=
      ⟨μ, hp, rfl⟩
    have hle : epigraphClosureInf f x ≤ (μ : EReal) := sInf_le hmem
    exact (mem_epigraph_univ_iff (f := epigraphClosureInf f)).2 hle

/-- Points in the closure of the epigraph bound the liminf from above. -/
lemma liminf_le_of_mem_closure_epigraph {n : Nat} {f : (Fin n → Real) → EReal}
    {x : Fin n → Real} {μ : Real}
    (hmem :
      (x, μ) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)) :
    Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ (μ : EReal) := by
  refine
    (Filter.liminf_le_iff (f := 𝓝 x) (u := fun y : Fin n → Real => f y)
      (x := (μ : EReal))).2 ?_
  intro y hy
  obtain ⟨r, hμr, hry⟩ := EReal.exists_between_coe_real hy
  have hμr' : μ < r := (EReal.coe_lt_coe_iff).1 hμr
  have hfreq_r : ∃ᶠ z in 𝓝 x, f z < (r : EReal) := by
    refine (Filter.frequently_iff).2 ?_
    intro U hU
    have hV : Set.Iio r ∈ 𝓝 μ := Iio_mem_nhds hμr'
    have hprod : U ×ˢ Set.Iio r ∈ 𝓝 (x, μ) := prod_mem_nhds hU hV
    have hclosure := (mem_closure_iff_nhds).1 hmem
    rcases hclosure (U ×ˢ Set.Iio r) hprod with ⟨p, hp⟩
    rcases hp with ⟨hpU, hpE⟩
    rcases hpU with ⟨hxU, htIio⟩
    have hfp : f p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_univ_iff (f := f)).1 hpE
    have htlt : (p.2 : EReal) < (r : EReal) :=
      (EReal.coe_lt_coe_iff).2 htIio
    have hlt : f p.1 < (r : EReal) := lt_of_le_of_lt hfp htlt
    exact ⟨p.1, hxU, hlt⟩
  exact hfreq_r.mono (fun z hz => lt_trans hz hry)

/-- Text 7.0.10: The epigraph of the closure of `f` is the closure of the epigraph of `f`.
Consequently, `(convexFunctionClosure f)(x) = liminf_{y → x} f(y)`. -/
theorem epigraph_convexFunctionClosure_eq_closure_epigraph {n : Nat}
    (f : (Fin n → Real) → EReal) (hbot : ∀ x, f x ≠ (⊥ : EReal)) :
    epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) ∧
      ∀ x : Fin n → Real,
        convexFunctionClosure f x =
          Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) := by
  classical
  set g := lowerSemicontinuousHull f
  have hspec :=
    Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f)
  have hls : LowerSemicontinuous g := by
    simpa [g] using hspec.1
  have hle : g ≤ f := by
    simpa [g] using hspec.2.1
  have hclosure :
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) g :=
    closure_epigraph_subset_epigraph_of_lsc_le (f := f) (g := g) hls hle
  have hliminf :
      ∀ x, g x ≤ Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) :=
    lowerSemicontinuous_le_liminf_of_le (f := f) (g := g) hls hle
  set g0 := epigraphClosureInf f
  have hclosure_eq :
      epigraph (S := (Set.univ : Set (Fin n → Real))) g0 =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    simpa [g0] using (closure_epigraph_eq_epigraph_sInf (f := f))
  have hls0 : LowerSemicontinuous g0 := by
    have hclosed_epi :
        IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) g0) := by
      simp [hclosure_eq]
    have hclosed_sub :
        ∀ α : Real, IsClosed {x | g0 x ≤ (α : EReal)} :=
      closed_sublevel_of_closed_epigraph (f := g0) hclosed_epi
    exact (lowerSemicontinuous_iff_closed_sublevel (f := g0)).2 hclosed_sub
  have hle0 : g0 ≤ f := by
    intro x
    by_cases htop : f x = (⊤ : EReal)
    · simp [htop]
    · have hbotx : f x ≠ (⊥ : EReal) := hbot x
      have hxmem :
          (x, (f x).toReal) ∈
            closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
        have hle_fx : f x ≤ (f x).toReal := EReal.le_coe_toReal htop
        have hxepi :
            (x, (f x).toReal) ∈
              epigraph (S := (Set.univ : Set (Fin n → Real))) f :=
          (mem_epigraph_univ_iff (f := f)).2 hle_fx
        exact subset_closure hxepi
      have hle_toReal : g0 x ≤ (f x).toReal := by
        have hmem :
            ((f x).toReal : EReal) ∈
              (fun t : Real => (t : EReal)) '' {t : Real |
                (x, t) ∈
                  closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)} :=
          ⟨(f x).toReal, hxmem, rfl⟩
        exact sInf_le hmem
      have hcoe : ((f x).toReal : EReal) = f x :=
        EReal.coe_toReal htop hbotx
      simpa [hcoe] using hle_toReal
  have hle_g0 : g0 ≤ g := hspec.2.2 g0 hls0 hle0
  have hsubset :
      epigraph (S := (Set.univ : Set (Fin n → Real))) g ⊆
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    have hsubset' :
        epigraph (S := (Set.univ : Set (Fin n → Real))) g ⊆
          epigraph (S := (Set.univ : Set (Fin n → Real))) g0 := by
      intro p hp
      have hgp : g p.1 ≤ (p.2 : EReal) :=
        (mem_epigraph_univ_iff (f := g)).1 hp
      have hle' : g0 p.1 ≤ g p.1 := hle_g0 p.1
      exact (mem_epigraph_univ_iff (f := g0)).2 (le_trans hle' hgp)
    simpa [hclosure_eq] using hsubset'
  have hEq :
      epigraph (S := (Set.univ : Set (Fin n → Real))) g =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    exact subset_antisymm hsubset hclosure
  refine ⟨?_, ?_⟩
  · simpa [convexFunctionClosure, hbot, g] using hEq
  · intro x
    have hle' : g x ≤ Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) := hliminf x
    have hge' :
        Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ g x := by
      by_cases hx_top : g x = (⊤ : EReal)
      · simp [hx_top]
      by_cases hx_bot : g x = (⊥ : EReal)
      · have hforall :
            ∀ μ : ℝ,
              Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ (μ : EReal) := by
          intro μ
          have hxepi :
              (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
            have hleμ : g x ≤ (μ : EReal) := by
              simp [hx_bot]
            exact (mem_epigraph_univ_iff (f := g)).2 hleμ
          have hxmem :
              (x, μ) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
            simpa [hEq] using hxepi
          exact liminf_le_of_mem_closure_epigraph (f := f) hxmem
        have hbot' :
            Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) = (⊥ : EReal) := by
          apply (EReal.eq_bot_iff_forall_lt
            (x := Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x))).2
          intro μ
          have hle :
              Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤
                ((μ - 1) : EReal) := hforall (μ - 1)
          have hlt : ((μ - 1 : ℝ) : EReal) < (μ : EReal) := by
            have hlt' : μ - 1 < μ := by linarith
            exact (EReal.coe_lt_coe_iff).2 hlt'
          exact lt_of_le_of_lt hle hlt
        simp [hx_bot, hbot']
      · have hxcoe : ((g x).toReal : EReal) = g x :=
          EReal.coe_toReal hx_top hx_bot
        have hxepi :
            (x, (g x).toReal) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
          have hle_toReal : g x ≤ (g x).toReal := EReal.le_coe_toReal hx_top
          exact (mem_epigraph_univ_iff (f := g)).2 hle_toReal
        have hxmem :
            (x, (g x).toReal) ∈
              closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
          simpa [hEq] using hxepi
        have hle_toReal :
            Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤
              ((g x).toReal : EReal) :=
          liminf_le_of_mem_closure_epigraph (f := f) hxmem
        simpa [hxcoe] using hle_toReal
    simpa [convexFunctionClosure, hbot, g] using (le_antisymm hle' hge')

/-- A liminf bound yields membership in all closed real sublevel sets above `α`. -/
lemma liminf_le_mem_iInter_closure_sublevel {n : Nat}
    {f : (Fin n → Real) → EReal} {α : Real} {x : Fin n → Real} :
    Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ (α : EReal) →
      x ∈ ⋂ (μ : {μ : Real // μ > α}),
        closure {y | f y ≤ ((μ : Real) : EReal)} := by
  intro hlim
  simp
  intro μ hμ
  have hlt : (α : EReal) < ((μ : Real) : EReal) := by
    exact (EReal.coe_lt_coe_iff).2 hμ
  have hfreq :
      ∃ᶠ y in 𝓝 x, f y < ((μ : Real) : EReal) := by
    have hlim' :=
      (Filter.liminf_le_iff (f := 𝓝 x) (u := fun y : Fin n → Real => f y)
        (x := (α : EReal))).1 hlim
    exact hlim' _ hlt
  have hfreq_le :
      ∃ᶠ y in 𝓝 x, f y ≤ ((μ : Real) : EReal) :=
    hfreq.mono (fun y hy => le_of_lt hy)
  refine (mem_closure_iff_frequently).2 ?_
  simpa using hfreq_le

/-- Membership in all closed real sublevel sets above `α` forces the liminf bound. -/
lemma liminf_le_of_mem_iInter_closure_sublevel {n : Nat}
    {f : (Fin n → Real) → EReal} {α : Real} {x : Fin n → Real} :
    x ∈ ⋂ (μ : {μ : Real // μ > α}),
        closure {y | f y ≤ ((μ : Real) : EReal)} →
      Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ (α : EReal) := by
  classical
  intro hx
  by_contra hgt
  have hlt : (α : EReal) < Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) :=
    lt_of_not_ge hgt
  obtain ⟨μ, hαμ, hμlt⟩ := EReal.exists_between_coe_real hlt
  have hμ : μ > α := (EReal.coe_lt_coe_iff).1 hαμ
  have hxμ :
      x ∈ closure {y | f y ≤ ((μ : Real) : EReal)} := by
    have hx' :
        ∀ μ : {μ : Real // μ > α},
          x ∈ closure {y | f y ≤ ((μ : Real) : EReal)} := by
      simpa using hx
    exact hx' ⟨μ, hμ⟩
  have hfreq :
      ∃ᶠ y in 𝓝 x, f y ≤ ((μ : Real) : EReal) := by
    have := (mem_closure_iff_frequently).1 hxμ
    simpa using this
  have hlim :
      Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ ((μ : Real) : EReal) :=
    Filter.liminf_le_of_frequently_le hfreq
  exact (not_lt_of_ge hlim) hμlt
end Section07
end Chap02
