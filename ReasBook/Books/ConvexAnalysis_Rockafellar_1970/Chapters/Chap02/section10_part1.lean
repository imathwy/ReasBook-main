/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Guangxuan Pan, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section02_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part9

noncomputable section

section Chap02
section Section10

open scoped BigOperators

/-- Definition 10.0.1. Let `f : ℝ^n → ℝ` be a function and let `S ⊆ ℝ^n`.
The function `f` is continuous relative to `S` if the restriction of `f` to `S`
(denoted `f|_S`) is continuous on `S`. -/
def Function.ContinuousRelativeTo {n : Nat} (f : EuclideanSpace Real (Fin n) → Real)
    (S : Set (EuclideanSpace Real (Fin n))) : Prop :=
  ContinuousOn f S

/-- If a sequence in a subset `S` converges in the ambient space, then it also converges in the
topology `nhdsWithin _ S`. -/
lemma Function.tendsto_nhdsWithin_of_forall_mem {n : Nat} {S : Set (EuclideanSpace Real (Fin n))}
    {x : EuclideanSpace Real (Fin n)} {y : ℕ → EuclideanSpace Real (Fin n)}
    (hyS : ∀ k, y k ∈ S) (hy : Filter.Tendsto y Filter.atTop (nhds x)) :
    Filter.Tendsto y Filter.atTop (nhdsWithin x S) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within y hy (Filter.Eventually.of_forall hyS)

/-- From `ContinuousRelativeTo f S` (i.e. `ContinuousOn f S`), every sequence in `S` converging to
`x ∈ S` has `f (y k) → f x`. -/
lemma Function.continuousRelativeTo_imp_seq_tendsto {n : Nat}
    {f : EuclideanSpace Real (Fin n) → Real} {S : Set (EuclideanSpace Real (Fin n))} :
    Function.ContinuousRelativeTo f S →
      ∀ x ∈ S,
        ∀ y : ℕ → EuclideanSpace Real (Fin n),
          (∀ k, y k ∈ S) →
            Filter.Tendsto y Filter.atTop (nhds x) →
              Filter.Tendsto (fun k => f (y k)) Filter.atTop (nhds (f x)) := by
  intro hf x hx y hyS hy
  have hf' : ContinuousOn f S := by
    simpa [Function.ContinuousRelativeTo] using hf
  have hyWithin : Filter.Tendsto y Filter.atTop (nhdsWithin x S) :=
    Function.tendsto_nhdsWithin_of_forall_mem (S := S) hyS hy
  exact (hf'.continuousWithinAt hx).tendsto.comp hyWithin

/-- A sequence in a subtype `S` converging to `x` yields an ambient sequence converging to `x`. -/
lemma Function.seq_in_subtype_to_seq_in_ambient {n : Nat} {S : Set (EuclideanSpace Real (Fin n))}
    {u : ℕ → S} {x : S} (hu : Filter.Tendsto u Filter.atTop (nhds x)) :
    Filter.Tendsto (fun k => (u k : EuclideanSpace Real (Fin n))) Filter.atTop (nhds (x : _)) :=
  (continuous_subtype_val.tendsto x).comp hu

/-- If every ambient sequence in `S` converging to `x ∈ S` satisfies `f (y k) → f x`, then `f` is
continuous relative to `S`. -/
lemma Function.seq_tendsto_imp_continuousRelativeTo_via_restrict {n : Nat}
    {f : EuclideanSpace Real (Fin n) → Real} {S : Set (EuclideanSpace Real (Fin n))}
    (hseq :
      ∀ x ∈ S,
        ∀ y : ℕ → EuclideanSpace Real (Fin n),
          (∀ k, y k ∈ S) →
            Filter.Tendsto y Filter.atTop (nhds x) →
              Filter.Tendsto (fun k => f (y k)) Filter.atTop (nhds (f x))) :
    Function.ContinuousRelativeTo f S := by
  have hcont : Continuous (S.restrict f) := by
    rw [continuous_iff_continuousAt]
    intro x
    -- Use sequential characterization of `ContinuousAt` on the subtype.
    rw [ContinuousAt]
    refine (tendsto_nhds_iff_seq_tendsto (f := S.restrict f) (a := x) (b := (S.restrict f) x)).2 ?_
    intro u hu
    have hy :
        Filter.Tendsto (fun k => (u k : EuclideanSpace Real (Fin n))) Filter.atTop (nhds (x : _)) :=
      Function.seq_in_subtype_to_seq_in_ambient (S := S) hu
    have hyS : ∀ k, (u k : EuclideanSpace Real (Fin n)) ∈ S := fun k => (u k).property
    have hfseq :=
      hseq (x : EuclideanSpace Real (Fin n)) x.property (fun k => (u k : _)) hyS hy
    simpa [Function.comp, Set.restrict_eq] using hfseq
  have hOn : ContinuousOn f S := (continuousOn_iff_continuous_restrict).2 hcont
  simpa [Function.ContinuousRelativeTo] using hOn

/-- Theorem 10.0.2. Let `f : ℝ^n → ℝ` and `S ⊆ ℝ^n`.
Then `f` is continuous relative to `S` if and only if for every `x ∈ S` and every sequence
`(y_k) ⊆ S` with `y_k → x`, one has `f(y_k) → f(x)`. -/
theorem Function.continuousRelativeTo_iff_seq_tendsto {n : Nat}
    (f : EuclideanSpace Real (Fin n) → Real) (S : Set (EuclideanSpace Real (Fin n))) :
    Function.ContinuousRelativeTo f S ↔
      ∀ x ∈ S,
        ∀ y : ℕ → EuclideanSpace Real (Fin n),
          (∀ k, y k ∈ S) →
            Filter.Tendsto y Filter.atTop (nhds x) →
              Filter.Tendsto (fun k => f (y k)) Filter.atTop (nhds (f x)) := by
  constructor
  · exact Function.continuousRelativeTo_imp_seq_tendsto (f := f) (S := S)
  · intro hseq
    exact Function.seq_tendsto_imp_continuousRelativeTo_via_restrict (f := f) (S := S) hseq

/-- Theorem 10.1. A convex function `f` on `ℝ^n` is continuous relative to any relatively open
convex set `C` in its effective domain, in particular relative to `ri (dom f)`. -/
theorem convexFunctionOn_continuousOn_of_relOpen_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {C : Set (Fin n → Real)} (hCconv : Convex ℝ C)
    (hCsub : C ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hCrelOpen : euclideanRelativelyOpen n
      ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C)) :
    ContinuousOn f C := by
  classical
  set CE : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C
  -- Extend `f` by `⊤` outside `C` so that `C` becomes the effective domain.
  let g : (Fin n → Real) → EReal := fun x => if x ∈ C then f x else (⊤ : EReal)
  have hEq : Set.EqOn f g C := by
    intro x hx
    simp [g, hx]
  have hdomg : effectiveDomain (Set.univ : Set (Fin n → Real)) g = C := by
    ext x
    constructor
    · intro hxdomg
      have hxlt : g x < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hxdomg
      by_cases hxC : x ∈ C
      · exact hxC
      · exfalso
        simp [g, hxC] at hxlt
    · intro hxC
      have hxdomf : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := hCsub hxC
      have hxlt : f x < (⊤ : EReal) := by
        have hx' : x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal) := by
          simpa [effectiveDomain_eq] using hxdomf
        exact hx'.2
      have hxlt' : g x < (⊤ : EReal) := by simpa [g, hxC] using hxlt
      have : x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ g x < (⊤ : EReal)} :=
        ⟨by simp, hxlt'⟩
      simpa [effectiveDomain_eq] using this
  -- Convexity is preserved under extension by `⊤` outside a convex set.
  have hconv_epi_univ : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunctionOn] using hf
  have hconv_epi_C : Convex ℝ (epigraph C f) := by
    intro p hp q hq a b ha hb hab
    have hp' : p.1 ∈ C ∧ f p.1 ≤ (p.2 : EReal) := by
      simpa [epigraph] using hp
    have hq' : q.1 ∈ C ∧ f q.1 ≤ (q.2 : EReal) := by
      simpa [epigraph] using hq
    have hpU : p ∈ epigraph (Set.univ : Set (Fin n → Real)) f := ⟨by trivial, hp'.2⟩
    have hqU : q ∈ epigraph (Set.univ : Set (Fin n → Real)) f := ⟨by trivial, hq'.2⟩
    have hcombU :
        a • p + b • q ∈ epigraph (Set.univ : Set (Fin n → Real)) f :=
      hconv_epi_univ hpU hqU ha hb hab
    have hcombC : (a • p + b • q).1 ∈ C := by
      simpa using hCconv hp'.1 hq'.1 ha hb hab
    exact ⟨hcombC, hcombU.2⟩
  have hepigraph :
      epigraph (Set.univ : Set (Fin n → Real)) g = epigraph C f := by
    ext p
    constructor
    · intro hp
      have hp' : (Set.univ : Set (Fin n → Real)) p.1 ∧ g p.1 ≤ (p.2 : EReal) := by
        simpa [epigraph] using hp
      have hle : g p.1 ≤ (p.2 : EReal) := hp'.2
      by_cases hC : p.1 ∈ C
      · have hle' : f p.1 ≤ (p.2 : EReal) := by simpa [g, hC] using hle
        exact ⟨hC, hle'⟩
      · simp [g, hC] at hle
    · intro hp
      refine ⟨by trivial, ?_⟩
      have hgpf : g p.1 = f p.1 := by
        simpa [g] using
          (if_pos hp.1 : (if p.1 ∈ C then f p.1 else (⊤ : EReal)) = f p.1)
      simpa [hgpf] using hp.2
  have hg : ConvexFunction g := by
    unfold ConvexFunction ConvexFunctionOn
    -- `epi g = epi f` over `C`, and convexity on `C` follows from convexity on `univ`.
    simpa [hepigraph] using hconv_epi_C
  have hcontg :
      ContinuousOn (fun x : EuclideanSpace Real (Fin n) => g (x : Fin n → Real))
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) g)) :=
    convexFunction_continuousOn_ri_effectiveDomain (n := n) (f := g) hg
  have hpre :
      ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) g) = CE := by
    simp [CE, hdomg]
  have hcontgCE_ri :
      ContinuousOn (fun x : EuclideanSpace Real (Fin n) => g (x : Fin n → Real))
        (euclideanRelativeInterior n CE) := by
    simpa [hpre] using hcontg
  have hCrelOpen' : euclideanRelativeInterior n CE = CE := by
    simpa [euclideanRelativelyOpen, CE] using hCrelOpen
  have hcontgCE :
      ContinuousOn (fun x : EuclideanSpace Real (Fin n) => g (x : Fin n → Real)) CE := by
    simpa [hCrelOpen'] using hcontgCE_ri
  -- Pull back continuity along `toLp` to conclude continuity of `g` on `C`.
  have hcont_toLp :
      Continuous
        (fun x : Fin n → Real =>
          (WithLp.toLp (p := (2 : ENNReal)) x : EuclideanSpace Real (Fin n))) := by
    simpa [EuclideanSpace] using
      (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => Real))
  have hmap :
      Set.MapsTo
        (fun x : Fin n → Real =>
          (WithLp.toLp (p := (2 : ENNReal)) x : EuclideanSpace Real (Fin n))) C CE := by
    intro x hx
    -- `toLp` is a section of `ofLp`, so this lands back in `C`.
    simpa [CE, WithLp.ofLp_toLp] using hx
  have hcontgC :
      ContinuousOn (fun x : Fin n → Real => g x) C := by
    have hcomp :
        ContinuousOn
          (fun x : Fin n → Real =>
            (fun y : EuclideanSpace Real (Fin n) => g (y : Fin n → Real))
              (WithLp.toLp (p := (2 : ENNReal)) x))
          C :=
      hcontgCE.comp hcont_toLp.continuousOn hmap
    refine hcomp.congr ?_
    intro x hx
    simp
  exact hcontgC.congr hEq

/-- Theorem 10.1 (in particular). A convex function `f` on `ℝ^n` is continuous relative to
`ri (dom f)`, where `dom f` is the effective domain. -/
theorem convexFunctionOn_continuousOn_relativeInterior_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ContinuousOn (fun x : EuclideanSpace Real (Fin n) => f (x : Fin n → Real))
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
  have hf' : ConvexFunction f := by
    simpa [ConvexFunction] using hf
  simpa using
    (convexFunction_continuousOn_ri_effectiveDomain (n := n) (f := f) hf')

/-- For a real-valued function, coercion to `EReal` is finite everywhere, hence its effective
domain over `univ` is `univ`. -/
lemma effectiveDomain_univ_coe_real {n : Nat} (f : (Fin n → Real) → Real) :
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) = Set.univ := by
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    simp [effectiveDomain_eq, lt_top_iff_ne_top]

/-- The whole Euclidean space is relatively open in itself (`ri univ = univ`). -/
lemma euclideanRelativelyOpen_univ (n : Nat) :
    euclideanRelativelyOpen n (Set.univ : Set (EuclideanSpace Real (Fin n))) := by
  simpa [euclideanRelativelyOpen] using
    (euclideanRelativeInterior_affineSubspace_eq n
      (⊤ : AffineSubspace Real (EuclideanSpace Real (Fin n))))

/-- A real-valued map is continuous iff its coercion to `EReal` is continuous. -/
lemma continuous_coe_ereal_iff_continuous {α : Type*} [TopologicalSpace α] {f : α → Real} :
    (Continuous fun a => (f a : EReal)) ↔ Continuous f := by
  simpa using (EReal.continuous_coe_iff (f := f))

/-- Corollary 10.1.1. A convex function finite on all of `ℝ^n` is necessarily continuous. -/
theorem convexFunctionOn_continuous_of_real {n : Nat} {f : (Fin n → Real) → Real}
    (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal))) :
    Continuous f := by
  classical
  have hCsub :
      (Set.univ : Set (Fin n → Real)) ⊆
        effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) := by
    simp [effectiveDomain_univ_coe_real (n := n) f]
  have hCrelOpen :
      euclideanRelativelyOpen n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          (Set.univ : Set (Fin n → Real))) := by
    simpa using (euclideanRelativelyOpen_univ n)
  have hcontOn :
      ContinuousOn (fun x : Fin n → Real => (f x : EReal)) (Set.univ : Set (Fin n → Real)) :=
    convexFunctionOn_continuousOn_of_relOpen_effectiveDomain (n := n)
      (f := fun x => (f x : EReal)) hf (C := Set.univ) (hCconv := convex_univ)
      (hCsub := hCsub) (hCrelOpen := hCrelOpen)
  have hcont : Continuous (fun x : Fin n → Real => (f x : EReal)) := by
    exact (continuousOn_univ).1 hcontOn
  exact (continuous_coe_ereal_iff_continuous (f := f)).1 hcont

/-- Any element of a bounded-above range is bounded above by its `sSup`. -/
lemma le_csSup_range_apply {n : Nat} {T : Type*} [Nonempty T]
    (f : (Fin n → Real) → T → Real) (hbdd : ∀ x, BddAbove (Set.range fun t : T => f x t))
    (x : Fin n → Real) (t : T) :
    f x t ≤ sSup (Set.range fun t : T => f x t) :=
  le_csSup (hbdd x) ⟨t, rfl⟩

/-- The pointwise supremum of a family of convex functions is convex. -/
lemma convexOn_sSup_range_of_convexOn {n : Nat} {T : Type*} [Nonempty T]
    (f : (Fin n → Real) → T → Real)
    (hconv : ∀ t, ConvexOn ℝ (Set.univ : Set (Fin n → Real)) (fun x => f x t))
    (hbdd : ∀ x, BddAbove (Set.range fun t : T => f x t)) :
    ConvexOn ℝ (Set.univ : Set (Fin n → Real))
      (fun x => sSup (Set.range fun t : T => f x t)) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Reduce to scalar multiplication on `ℝ` rather than `SMul`.
  simp [smul_eq_mul]
  have hne :
      (Set.range fun t : T => f (a • x + b • y) t).Nonempty := by
    simpa using Set.range_nonempty (fun t : T => f (a • x + b • y) t)
  refine csSup_le hne ?_
  intro r hr
  rcases hr with ⟨t, rfl⟩
  have hxy :
      f (a • x + b • y) t ≤ a * f x t + b * f y t := by
    simpa [smul_eq_mul] using (hconv t).2 hx hy ha hb hab
  have hxle : f x t ≤ sSup (Set.range fun t : T => f x t) :=
    le_csSup_range_apply (f := f) hbdd x t
  have hyle : f y t ≤ sSup (Set.range fun t : T => f y t) :=
    le_csSup_range_apply (f := f) hbdd y t
  have hmulx :
      a * f x t ≤ a * sSup (Set.range fun t : T => f x t) :=
    mul_le_mul_of_nonneg_left hxle ha
  have hmuly :
      b * f y t ≤ b * sSup (Set.range fun t : T => f y t) :=
    mul_le_mul_of_nonneg_left hyle hb
  have hadd :
      a * f x t + b * f y t ≤
        a * sSup (Set.range fun t : T => f x t) +
          b * sSup (Set.range fun t : T => f y t) :=
    add_le_add hmulx hmuly
  exact le_trans hxy hadd

/-- A convex real-valued function on all of `ℝ^n` is continuous. -/
lemma continuous_of_convexOn_univ {n : Nat} {h : (Fin n → Real) → Real}
    (hh : ConvexOn ℝ (Set.univ : Set (Fin n → Real)) h) : Continuous h := by
  have hcontOn : ContinuousOn h (Set.univ : Set (Fin n → Real)) := by
    simpa [interior_univ] using (hh.continuousOn_interior (C := (Set.univ : Set (Fin n → Real))))
  exact (continuousOn_univ).1 hcontOn

/-- Theorem 10.1.2. Let `T` be an arbitrary index set and let `f : ℝ^n × T → ℝ` be a function
such that:

- for each `t ∈ T`, the function `x ↦ f(x,t)` is convex on `ℝ^n`;
- for each `x ∈ ℝ^n`, the function `t ↦ f(x,t)` is bounded above on `T`.

Define `h(x) := sup { f(x,t) | t ∈ T }`. Then `h` is a finite convex function on `ℝ^n`, and
`h(x)` depends continuously on `x`. -/
theorem convexOn_continuous_sSup_range {n : Nat} {T : Type*} [Nonempty T]
    (f : (Fin n → Real) → T → Real)
    (hconv : ∀ t, ConvexOn ℝ (Set.univ : Set (Fin n → Real)) (fun x => f x t))
    (hbdd : ∀ x, BddAbove (Set.range fun t : T => f x t)) :
    (let h : (Fin n → Real) → Real := fun x => sSup (Set.range fun t : T => f x t)
    ConvexOn ℝ (Set.univ : Set (Fin n → Real)) h ∧ Continuous h) := by
  classical
  -- Eliminate the `let h := ...` binder in the goal.
  simp
  have hhconv :
      ConvexOn ℝ (Set.univ : Set (Fin n → Real))
        (fun x => sSup (Set.range fun t : T => f x t)) :=
    convexOn_sSup_range_of_convexOn (f := f) hconv hbdd
  refine ⟨hhconv, ?_⟩
  exact continuous_of_convexOn_univ (h := fun x => sSup (Set.range fun t : T => f x t)) hhconv

/-- The inf-set in Theorem 10.1.3 is nonempty. -/
lemma sInf_image_add_nonempty {n : Nat} {f : (Fin n → Real) → Real} {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) (x : Fin n → Real) :
    (f '' ((fun y => y + x) '' C)).Nonempty := by
  rcases hCne with ⟨y, hyC⟩
  refine ⟨f (y + x), ?_⟩
  refine ⟨y + x, ?_, rfl⟩
  exact ⟨y, hyC, rfl⟩

/-- For `ε > 0`, there is a point in `C` whose translate is `ε`-close above the infimum. -/
lemma exists_mem_C_lt_sInf_add {n : Nat} {f : (Fin n → Real) → Real} {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) (x : Fin n → Real) {ε : Real} (hε : 0 < ε) :
    ∃ y ∈ C, f (y + x) < sInf (f '' ((fun y => y + x) '' C)) + ε := by
  classical
  set S : Set Real := f '' ((fun y => y + x) '' C)
  have hSne : S.Nonempty := by
    simpa [S] using sInf_image_add_nonempty (f := f) (C := C) hCne x
  rcases Real.lt_sInf_add_pos (s := S) hSne hε with ⟨v, hvS, hvlt⟩
  rcases hvS with ⟨u, hu, rfl⟩
  rcases hu with ⟨y, hyC, rfl⟩
  refine ⟨y, hyC, ?_⟩
  simpa [S] using hvlt

/-- If all the inf-sets are bounded below, the pointwise infimum of translates of a convex
function is convex. -/
lemma convexOn_sInf_image_add_of_bddBelow {n : Nat} {f : (Fin n → Real) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (Fin n → Real)) f) {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (hbdd : ∀ x, BddBelow (f '' ((fun y => y + x) '' C))) :
    ConvexOn ℝ (Set.univ : Set (Fin n → Real))
      (fun x => sInf (f '' ((fun y => y + x) '' C))) := by
  refine ⟨convex_univ, ?_⟩
  intro x1 _ x2 _ a b ha hb hab
  -- Use an `ε`-approximation argument at `x1` and `x2`.
  refine le_of_forall_pos_lt_add ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases exists_mem_C_lt_sInf_add (f := f) (C := C) hCne x1 hε2 with ⟨y1, hy1C, hy1lt⟩
  rcases exists_mem_C_lt_sInf_add (f := f) (C := C) hCne x2 hε2 with ⟨y2, hy2C, hy2lt⟩
  set y : Fin n → Real := a • y1 + b • y2
  have hyC : y ∈ C := hCconv hy1C hy2C ha hb hab
  set z : Fin n → Real := a • x1 + b • x2
  have hyz :
      y + z = a • (y1 + x1) + b • (y2 + x2) := by
    ext i
    -- pointwise on coordinates, this is a distributivity/commutativity identity
    simp [y, z, Pi.add_apply, Pi.smul_apply]
    ring
  have hzmem :
      f (y + z) ∈ f '' ((fun t => t + z) '' C) := by
    refine ⟨y + z, ?_, rfl⟩
    exact ⟨y, hyC, rfl⟩
  have hsz_le : sInf (f '' ((fun t => t + z) '' C)) ≤ f (y + z) :=
    csInf_le (hbdd z) hzmem
  have hf_le :
      f (y + z) ≤ a * f (y1 + x1) + b * f (y2 + x2) := by
    have hf' :=
      hf.2 (by trivial : y1 + x1 ∈ (Set.univ : Set (Fin n → Real)))
        (by trivial : y2 + x2 ∈ (Set.univ : Set (Fin n → Real))) ha hb hab
    -- Rewrite `y + z` into the required convex combination and scalar actions as multiplication.
    simpa [hyz, smul_eq_mul] using hf'
  have hz_le :
      sInf (f '' ((fun t => t + z) '' C)) ≤ a * f (y1 + x1) + b * f (y2 + x2) :=
    le_trans hsz_le hf_le
  have hx1le : f (y1 + x1) ≤ sInf (f '' ((fun t => t + x1) '' C)) + ε / 2 :=
    le_of_lt hy1lt
  have hx2le : f (y2 + x2) ≤ sInf (f '' ((fun t => t + x2) '' C)) + ε / 2 :=
    le_of_lt hy2lt
  have hmul1 :
      a * f (y1 + x1) ≤ a * (sInf (f '' ((fun t => t + x1) '' C)) + ε / 2) :=
    mul_le_mul_of_nonneg_left hx1le ha
  have hmul2 :
      b * f (y2 + x2) ≤ b * (sInf (f '' ((fun t => t + x2) '' C)) + ε / 2) :=
    mul_le_mul_of_nonneg_left hx2le hb
  have hadd :
      a * f (y1 + x1) + b * f (y2 + x2) ≤
        a * (sInf (f '' ((fun t => t + x1) '' C)) + ε / 2) +
          b * (sInf (f '' ((fun t => t + x2) '' C)) + ε / 2) :=
    add_le_add hmul1 hmul2
  have hεbound :
      a * (sInf (f '' ((fun t => t + x1) '' C)) + ε / 2) +
          b * (sInf (f '' ((fun t => t + x2) '' C)) + ε / 2) =
        (a * sInf (f '' ((fun t => t + x1) '' C)) +
            b * sInf (f '' ((fun t => t + x2) '' C))) +
          ε / 2 := by
    -- Expand and use `a + b = 1`.
    calc
      a * (sInf (f '' ((fun t => t + x1) '' C)) + ε / 2) +
          b * (sInf (f '' ((fun t => t + x2) '' C)) + ε / 2) =
          (a * sInf (f '' ((fun t => t + x1) '' C)) +
              b * sInf (f '' ((fun t => t + x2) '' C))) +
            (a + b) * (ε / 2) := by
            ring
      _ = (a * sInf (f '' ((fun t => t + x1) '' C)) +
              b * sInf (f '' ((fun t => t + x2) '' C))) +
            ε / 2 := by
            simp [hab]
  have hz_le' :
      sInf (f '' ((fun t => t + z) '' C)) ≤
        (a * sInf (f '' ((fun t => t + x1) '' C)) + b * sInf (f '' ((fun t => t + x2) '' C))) +
          ε / 2 := by
    have := le_trans hz_le (le_trans hadd (le_of_eq hεbound))
    simpa using this
  have hlt :
      (a * sInf (f '' ((fun t => t + x1) '' C)) + b * sInf (f '' ((fun t => t + x2) '' C))) +
          ε / 2 <
        (a * sInf (f '' ((fun t => t + x1) '' C)) + b * sInf (f '' ((fun t => t + x2) '' C))) +
          ε := by
    -- `ε/2 < ε` since `ε > 0`.
    have hhalf : ε / 2 < ε := by linarith
    exact add_lt_add_right hhalf
      (a * sInf (f '' ((fun t => t + x1) '' C)) + b * sInf (f '' ((fun t => t + x2) '' C)))
  exact lt_of_le_of_lt hz_le' hlt

/-- Theorem 10.1.3. Let `f : ℝ^n → ℝ` be a convex function finite on all of `ℝ^n`, and let
`C ⊆ ℝ^n` be a nonempty convex set. For each `x ∈ ℝ^n`, define `h(x) := inf {f(y) | y ∈ C + x}`.

Then `h` is convex on `ℝ^n`, and `h` depends continuously on `x`. -/
theorem convexOn_continuous_sInf_image_add {n : Nat} {f : (Fin n → Real) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (Fin n → Real)) f) {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (hbdd : ∀ x, BddBelow (f '' ((fun y => y + x) '' C))) :
    (let h : (Fin n → Real) → Real := fun x => sInf (f '' ((fun y => y + x) '' C))
    ConvexOn ℝ (Set.univ : Set (Fin n → Real)) h ∧ Continuous h) := by
  classical
  -- Eliminate the `let h := ...` binder in the goal.
  dsimp
  have hhconv :
      ConvexOn ℝ (Set.univ : Set (Fin n → Real))
        (fun x => sInf (f '' ((fun y => y + x) '' C))) :=
    convexOn_sInf_image_add_of_bddBelow (hf := hf) (C := C) hCne hCconv hbdd
  refine ⟨hhconv, ?_⟩
  exact continuous_of_convexOn_univ (h := fun x => sInf (f '' ((fun y => y + x) '' C))) hhconv

/-- Theorem 10.1.4. Define `f : ℝ^2 → (-∞, +∞]` by

- `f(ξ₁, ξ₂) = ξ₂^2 / (2 ξ₁)` if `ξ₁ > 0`,
- `f(0, 0) = 0`,
- `f(ξ₁, ξ₂) = +∞` otherwise.

Then `f` is convex with effective domain `{(ξ₁, ξ₂) | ξ₁ > 0} ∪ {(0,0)}`.
Moreover, `f` is the support function of the convex set
`C = {(η₁, η₂) | η₁ + η₂^2 / 2 ≤ 0}` (i.e. the supremum of `⟪ξ, η⟫` over `η ∈ C`).

The function is continuous at every point of its effective domain except at `(0,0)`, where it is
only lower semicontinuous. In particular, for any `α > 0`,
`lim_{t → 0} f(t^2/(2α), t) = α`, while `lim_{t ↓ 0} f(t • x) = 0` for every `x` with `x₁ > 0`. -/
noncomputable def quadraticOverLinearEReal (ξ : Fin 2 → Real) : EReal :=
  if ξ 0 > 0 then ((ξ 1) ^ 2 / (2 * ξ 0) : Real)
  else if ξ 0 = 0 ∧ ξ 1 = 0 then (0 : EReal)
  else (⊤ : EReal)

/-- The convex set `C = {(η₁, η₂) | η₁ + η₂^2/2 ≤ 0}` appearing in Theorem 10.1.4. -/
def quadraticOverLinearSupportSet : Set (Fin 2 → Real) :=
  {η | η 0 + η 1 ^ 2 / 2 ≤ 0}

/-- Expand `dotProduct` on `Fin 2` as a two-term sum. -/
lemma dotProduct_fin2 (ξ η : Fin 2 → Real) :
    dotProduct ξ η = ξ 0 * η 0 + ξ 1 * η 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- The set of dot products `⟪ξ,η⟫` with `η ∈ quadraticOverLinearSupportSet`, seen in `EReal`. -/
def quadraticOverLinearSupportValues (ξ : Fin 2 → Real) : Set EReal :=
  {z : EReal | ∃ η ∈ quadraticOverLinearSupportSet, z = ((dotProduct ξ η : Real) : EReal)}

/-- The quadratic-over-linear function is nonnegative everywhere (as an `EReal`-valued map). -/
lemma zero_le_quadraticOverLinearEReal (ξ : Fin 2 → Real) :
    (0 : EReal) ≤ quadraticOverLinearEReal ξ := by
  by_cases hpos : ξ 0 > 0
  · have hden : 0 < 2 * ξ 0 := by nlinarith
    have : 0 ≤ (ξ 1) ^ 2 / (2 * ξ 0) := by
      exact div_nonneg (sq_nonneg (ξ 1)) (le_of_lt hden)
    simpa [quadraticOverLinearEReal, hpos] using (EReal.coe_nonneg.2 this)
  · by_cases hzero : ξ 0 = 0 ∧ ξ 1 = 0
    · simp [quadraticOverLinearEReal, hzero]
    · simp [quadraticOverLinearEReal, hpos, hzero]

/-- A completing-the-square bound for a concave quadratic. -/
lemma concave_quadratic_bound {a b t : Real} (ha : 0 < a) :
    (- (a / 2) * t ^ 2 + b * t) ≤ b ^ 2 / (2 * a) := by
  have hden : 0 < 2 * a := by nlinarith
  -- Multiply both sides by `2*a` (positive) and reduce to a square.
  refine (le_div_iff₀ hden).2 ?_
  have hsq : 0 ≤ (a * t - b) ^ 2 := sq_nonneg (a * t - b)
  -- `b^2 - ((-a/2)*t^2 + b*t)*(2a) = (a*t - b)^2`.
  have hident :
      b ^ 2 - (- (a / 2) * t ^ 2 + b * t) * (2 * a) = (a * t - b) ^ 2 := by
    ring
  have : (- (a / 2) * t ^ 2 + b * t) * (2 * a) ≤ b ^ 2 := by
    have : 0 ≤ b ^ 2 - (- (a / 2) * t ^ 2 + b * t) * (2 * a) := by
      -- Rewrite the difference as a square.
      rw [hident]
      exact hsq
    linarith
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- Upper bound on `⟪ξ,η⟫` when `η ∈ quadraticOverLinearSupportSet` and `ξ₁ > 0`. -/
lemma quadraticOverLinear_supportSet_dotProduct_le_quadraticBound {ξ η : Fin 2 → Real}
    (hξ : 0 < ξ 0) (hη : η ∈ quadraticOverLinearSupportSet) :
    (dotProduct ξ η : Real) ≤ (ξ 1) ^ 2 / (2 * ξ 0) := by
  have hη0 : η 0 ≤ - (η 1 ^ 2) / 2 := by
    have : η 0 + η 1 ^ 2 / 2 ≤ 0 := hη
    linarith
  have hmul :
      ξ 0 * η 0 ≤ ξ 0 * (- (η 1 ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left hη0 (le_of_lt hξ)
  have hdot_le :
      dotProduct ξ η ≤ ξ 0 * (- (η 1 ^ 2) / 2) + ξ 1 * η 1 := by
    -- Expand `dotProduct` on `Fin 2` and use the bound on `η 0`.
    have : ξ 0 * η 0 + ξ 1 * η 1 ≤ ξ 0 * (- (η 1 ^ 2) / 2) + ξ 1 * η 1 := by
      linarith [hmul]
    simpa [dotProduct_fin2, add_assoc, add_left_comm, add_comm] using this
  have hquad :
      ξ 0 * (- (η 1 ^ 2) / 2) + ξ 1 * η 1 ≤ (ξ 1) ^ 2 / (2 * ξ 0) := by
    -- Rewrite as `(- (ξ0/2) * t^2 + ξ1*t) ≤ ξ1^2/(2*ξ0)` with `t = η1`.
    have := concave_quadratic_bound (a := ξ 0) (b := ξ 1) (t := η 1) hξ
    have hrew :
        ξ 0 * (- (η 1 ^ 2) / 2) + ξ 1 * η 1 = - (ξ 0 / 2) * (η 1) ^ 2 + ξ 1 * η 1 := by
      ring
    simpa [hrew]
  exact le_trans hdot_le hquad

/-- For `ξ₁ > 0`, there is `η ∈ quadraticOverLinearSupportSet` attaining the quadratic bound. -/
lemma exists_supportSet_attains_quadraticBound {ξ : Fin 2 → Real} (hξ : 0 < ξ 0) :
    ∃ η ∈ quadraticOverLinearSupportSet,
      (dotProduct ξ η : Real) = (ξ 1) ^ 2 / (2 * ξ 0) := by
  classical
  let t : Real := ξ 1 / ξ 0
  let η : Fin 2 → Real := ![-(t ^ 2) / 2, t]
  refine ⟨η, ?_, ?_⟩
  · -- Membership in the support set is by equality.
    have : η 0 + η 1 ^ 2 / 2 = 0 := by
      simp [η, t]
      ring
    have : η 0 + η 1 ^ 2 / 2 ≤ 0 := by simp [this]
    simpa [quadraticOverLinearSupportSet] using this
  · have hξ0 : ξ 0 ≠ 0 := ne_of_gt hξ
    -- Compute `⟪ξ,η⟫` explicitly.
    have hη0 : η 0 = -(t ^ 2) / 2 := by simp [η]
    have hη1 : η 1 = t := by simp [η]
    have hdot : (dotProduct ξ η : Real) = ξ 0 * (-(t ^ 2) / 2) + ξ 1 * t := by
      calc
        (dotProduct ξ η : Real) = ξ 0 * η 0 + ξ 1 * η 1 := dotProduct_fin2 ξ η
        _ = ξ 0 * (-(t ^ 2) / 2) + ξ 1 * t := by simp [hη0, hη1]
    -- Simplify to the claimed value.
    -- We use `field_simp` to clear denominators in `t = ξ1/ξ0`.
    have hsimp : ξ 0 * (-(t ^ 2) / 2) + ξ 1 * t = (ξ 1) ^ 2 / (2 * ξ 0) := by
      -- `t = ξ1/ξ0`.
      simp [t, div_eq_mul_inv]
      field_simp [hξ0]
      ring
    exact hdot.trans hsimp

/-- `ξ = 0` in `Fin 2 → ℝ` iff both coordinates are zero. -/
lemma fin2_eq_zero_iff (ξ : Fin 2 → Real) : ξ = 0 ↔ ξ 0 = 0 ∧ ξ 1 = 0 := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]

/-- If `b < ⊤` in `EReal`, it is below some real coercion. -/
lemma exists_lt_coe_of_lt_top {b : EReal} (hb : b < (⊤ : EReal)) : ∃ r : Real, b < (r : EReal) := by
  by_cases hbot : b = (⊥ : EReal)
  · subst hbot
    refine ⟨0, ?_⟩
    simp
  · have htop : b ≠ (⊤ : EReal) := ne_of_lt hb
    refine ⟨b.toReal + 1, ?_⟩
    have hbcoe : b = (b.toReal : EReal) := (EReal.coe_toReal htop hbot).symm
    have hlt : (b.toReal : EReal) < ((b.toReal + 1 : Real) : EReal) :=
      (EReal.coe_lt_coe_iff.2 (lt_add_one b.toReal))
    rw [hbcoe]
    exact hlt

/-- If `ξ₁ > 0`, the support supremum equals the quadratic bound. -/
lemma sSup_quadraticOverLinearSupportValues_of_pos {ξ : Fin 2 → Real} (hξ : 0 < ξ 0) :
    sSup (quadraticOverLinearSupportValues ξ) = (( (ξ 1) ^ 2 / (2 * ξ 0) : Real) : EReal) := by
  classical
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro z hz
    rcases hz with ⟨η, hη, rfl⟩
    exact (EReal.coe_le_coe_iff.2 (quadraticOverLinear_supportSet_dotProduct_le_quadraticBound
      (ξ := ξ) (η := η) hξ hη))
  · rcases exists_supportSet_attains_quadraticBound (ξ := ξ) hξ with ⟨η, hη, hdot⟩
    have hzmem :
        ((dotProduct ξ η : Real) : EReal) ∈ quadraticOverLinearSupportValues ξ :=
      ⟨η, hη, rfl⟩
    simpa [hdot] using (le_sSup hzmem)

/-- For `ξ = 0`, the support supremum equals `0`. -/
lemma sSup_quadraticOverLinearSupportValues_zero :
    sSup (quadraticOverLinearSupportValues (0 : Fin 2 → Real)) = (0 : EReal) := by
  classical
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro z hz
    rcases hz with ⟨η, hη, rfl⟩
    simp
  · have hη : (0 : Fin 2 → Real) ∈ quadraticOverLinearSupportSet := by
      simp [quadraticOverLinearSupportSet]
    have hzmem :
        ((dotProduct (0 : Fin 2 → Real) (0 : Fin 2 → Real) : Real) : EReal) ∈
          quadraticOverLinearSupportValues (0 : Fin 2 → Real) :=
      ⟨0, hη, rfl⟩
    simpa [dotProduct_fin2] using (le_sSup hzmem)

/-- If `ξ₁ < 0`, the support supremum is `⊤` (unbounded above). -/
lemma sSup_quadraticOverLinearSupportValues_eq_top_of_neg {ξ : Fin 2 → Real} (hξ : ξ 0 < 0) :
    sSup (quadraticOverLinearSupportValues ξ) = (⊤ : EReal) := by
  classical
  refine (sSup_eq_top).2 ?_
  intro b hb
  rcases exists_lt_coe_of_lt_top (b := b) hb with ⟨r, hbr⟩
  let M : Real := max 0 r + 1
  have hrM : r < M := by
    have hrle : r ≤ max 0 r := le_max_right 0 r
    have : max 0 r < max 0 r + 1 := lt_add_one (max 0 r)
    exact lt_of_le_of_lt hrle this
  have hMpos : 0 < M := by
    have : 0 ≤ max 0 r := le_max_left 0 r
    linarith [this]
  have hbM : b < (M : EReal) :=
    lt_trans hbr ((EReal.coe_lt_coe_iff).2 hrM)
  -- Choose `η = (M/ξ0, 0)`, which lies in the support set since `M/ξ0 ≤ 0` for `ξ0 < 0`.
  let η : Fin 2 → Real := ![M / (ξ 0), 0]
  have hηmem : η ∈ quadraticOverLinearSupportSet := by
    have hη0 : η 0 ≤ 0 := by
      have : M / (ξ 0) < 0 := div_neg_of_pos_of_neg hMpos hξ
      exact le_of_lt this
    simpa [quadraticOverLinearSupportSet, η] using hη0
  have hξ0 : ξ 0 ≠ 0 := ne_of_lt hξ
  have hdot : (dotProduct ξ η : Real) = M := by
    have hη0 : η 0 = M / (ξ 0) := by simp [η]
    have hη1 : η 1 = 0 := by simp [η]
    calc
      (dotProduct ξ η : Real) = ξ 0 * η 0 + ξ 1 * η 1 := dotProduct_fin2 ξ η
      _ = ξ 0 * (M / (ξ 0)) + ξ 1 * 0 := by simp [hη0, hη1]
      _ = ξ 0 * (M / (ξ 0)) := by ring
      _ = ξ 0 * M / (ξ 0) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = M := by
        simpa using (mul_div_cancel_left₀ (b := M) (a := ξ 0) hξ0)
  refine ⟨(M : EReal), ⟨η, hηmem, by simp [hdot]⟩, hbM⟩

/-- If `ξ₁ = 0` and `ξ₂ ≠ 0`, the support supremum is `⊤` (unbounded above). -/
lemma sSup_quadraticOverLinearSupportValues_eq_top_of_zero_ne {ξ : Fin 2 → Real}
    (hξ0 : ξ 0 = 0) (hξ1 : ξ 1 ≠ 0) :
    sSup (quadraticOverLinearSupportValues ξ) = (⊤ : EReal) := by
  classical
  refine (sSup_eq_top).2 ?_
  intro b hb
  rcases exists_lt_coe_of_lt_top (b := b) hb with ⟨r, hbr⟩
  let M : Real := max 0 r + 1
  have hrM : r < M := by
    have hrle : r ≤ max 0 r := le_max_right 0 r
    have : max 0 r < max 0 r + 1 := lt_add_one (max 0 r)
    exact lt_of_le_of_lt hrle this
  have hMpos : 0 < M := by
    have : 0 ≤ max 0 r := le_max_left 0 r
    linarith [this]
  have hbM : b < (M : EReal) :=
    lt_trans hbr ((EReal.coe_lt_coe_iff).2 hrM)
  let t : Real := M / (ξ 1)
  let η : Fin 2 → Real := ![-(t ^ 2) / 2, t]
  have hηmem : η ∈ quadraticOverLinearSupportSet := by
    have : η 0 + η 1 ^ 2 / 2 = 0 := by
      simp [η]
      ring
    have : η 0 + η 1 ^ 2 / 2 ≤ 0 := by simp [this]
    simpa [quadraticOverLinearSupportSet] using this
  have hdot : (dotProduct ξ η : Real) = M := by
    calc
      (dotProduct ξ η : Real) = ξ 0 * η 0 + ξ 1 * η 1 := dotProduct_fin2 ξ η
      _ = ξ 1 * t := by simp [η, hξ0]
      _ = ξ 1 * (M / (ξ 1)) := by simp [t]
      _ = ξ 1 * M / (ξ 1) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = M := by
        simpa using (mul_div_cancel_left₀ (b := M) (a := ξ 1) hξ1)
  refine ⟨(M : EReal), ⟨η, hηmem, by simp [hdot]⟩, hbM⟩

/-- Compute the support supremum in closed form. -/
lemma sSup_quadraticOverLinearSupportValues (ξ : Fin 2 → Real) :
    sSup (quadraticOverLinearSupportValues ξ) =
      if ξ 0 > 0 then (( (ξ 1) ^ 2 / (2 * ξ 0) : Real) : EReal)
      else if ξ 0 = 0 ∧ ξ 1 = 0 then (0 : EReal)
      else (⊤ : EReal) := by
  by_cases hpos : ξ 0 > 0
  · simpa [hpos] using sSup_quadraticOverLinearSupportValues_of_pos (ξ := ξ) hpos
  · by_cases hzero : ξ 0 = 0 ∧ ξ 1 = 0
    · have hξ : ξ = 0 := (fin2_eq_zero_iff ξ).2 hzero
      subst hξ
      simp [sSup_quadraticOverLinearSupportValues_zero]
    · have hle0 : ξ 0 ≤ 0 := le_of_not_gt hpos
      by_cases hneg : ξ 0 < 0
      · simpa [hpos, hzero] using sSup_quadraticOverLinearSupportValues_eq_top_of_neg (ξ := ξ) hneg
      · have hξ0 : ξ 0 = 0 := le_antisymm hle0 (le_of_not_gt hneg)
        have hξ1 : ξ 1 ≠ 0 := by
          intro h
          exact hzero ⟨hξ0, h⟩
        simpa [hpos, hzero] using
          sSup_quadraticOverLinearSupportValues_eq_top_of_zero_ne (ξ := ξ) hξ0 hξ1

/-- Support function representation for `quadraticOverLinearEReal` (as a pointwise equality). -/
theorem quadraticOverLinearEReal_eq_supportFunction_aux :
    quadraticOverLinearEReal =
      fun ξ => sSup (quadraticOverLinearSupportValues ξ) := by
  funext ξ
  -- Both sides are given by the same case split.
  simp [quadraticOverLinearEReal, sSup_quadraticOverLinearSupportValues]

/-- For fixed `η`, the map `ξ ↦ ⟪ξ,η⟫` (coerced to `EReal`) is convex on `ℝ^2`. -/
lemma convexFunctionOn_ereal_dotProduct_fixed (η : Fin 2 → Real) :
    ConvexFunctionOn (Set.univ : Set (Fin 2 → Real))
      (fun ξ => ((dotProduct ξ η : Real) : EReal)) := by
  -- First show real convexity (in fact, affinity) of `ξ ↦ ⟪ξ,η⟫`.
  have hconv :
      ConvexOn ℝ (Set.univ : Set (Fin 2 → Real)) (fun ξ => dotProduct ξ η) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hlin :
        dotProduct (a • x + b • y) η = a * dotProduct x η + b * dotProduct y η := by
      simp [smul_eq_mul, mul_add, add_assoc, add_left_comm, mul_comm]
    exact le_of_eq hlin
  exact
    convexFunctionOn_of_convexOn_real (S := (Set.univ : Set (Fin 2 → Real)))
      (g := fun ξ => dotProduct ξ η) hconv

/-- The `EReal` support function `ξ ↦ sSup {⟪ξ,η⟫ | η ∈ C}` is convex. -/
lemma convexFunctionOn_supportFunctionEReal (C : Set (Fin 2 → Real)) :
    ConvexFunctionOn (Set.univ : Set (Fin 2 → Real))
      (fun ξ =>
        sSup {z : EReal | ∃ η ∈ C, z = ((dotProduct ξ η : Real) : EReal)}) := by
  classical
  let ι := {η // η ∈ C}
  let f : ι → (Fin 2 → Real) → EReal := fun η ξ => ((dotProduct ξ η.1 : Real) : EReal)
  have hf : ∀ η : ι, ConvexFunctionOn (Set.univ : Set (Fin 2 → Real)) (f η) := by
    intro η
    simpa [f] using convexFunctionOn_ereal_dotProduct_fixed η.1
  have hsSup :
      (fun ξ =>
          sSup {z : EReal | ∃ η ∈ C, z = ((dotProduct ξ η : Real) : EReal)}) =
        fun ξ => iSup (fun η : ι => f η ξ) := by
    funext ξ
    have hset :
        {z : EReal | ∃ η ∈ C, z = ((dotProduct ξ η : Real) : EReal)} =
          Set.range (fun η : ι => ((dotProduct ξ η.1 : Real) : EReal)) := by
      ext z
      constructor
      · rintro ⟨η, hη, rfl⟩
        exact ⟨⟨η, hη⟩, rfl⟩
      · rintro ⟨η, rfl⟩
        exact ⟨η.1, η.2, rfl⟩
    -- `sSup` over this set is the `iSup` over the corresponding range.
    rw [hset, sSup_range]
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 2 → Real))
        (fun ξ => iSup (fun η : ι => f η ξ)) :=
    convexFunctionOn_iSup (f := f) hf
  simpa [hsSup.symm] using hconv

/-- Theorem 10.1.4 (convexity): the quadratic-over-linear extended-valued function is convex. -/
theorem convexFunctionOn_quadraticOverLinearEReal :
    ConvexFunctionOn (Set.univ : Set (Fin 2 → Real)) quadraticOverLinearEReal := by
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 2 → Real))
        (fun ξ => sSup (quadraticOverLinearSupportValues ξ)) := by
    -- This is the support function of `quadraticOverLinearSupportSet`.
    simpa [quadraticOverLinearSupportValues] using
      (convexFunctionOn_supportFunctionEReal (C := quadraticOverLinearSupportSet))
  -- Conclude by rewriting `quadraticOverLinearEReal` as the support function.
  simpa [quadraticOverLinearEReal_eq_supportFunction_aux] using hconv

/-- Theorem 10.1.4 (effective domain): `dom f = {ξ | ξ₁ > 0} ∪ {(0,0)}`. -/
theorem effectiveDomain_quadraticOverLinearEReal :
    effectiveDomain (Set.univ : Set (Fin 2 → Real)) quadraticOverLinearEReal =
      {ξ : Fin 2 → Real | ξ 0 > 0} ∪ {0} := by
  ext ξ
  by_cases hpos : ξ 0 > 0
  · simp [effectiveDomain_eq, quadraticOverLinearEReal, hpos]
  · by_cases hzero : ξ 0 = 0 ∧ ξ 1 = 0
    · have hξ : ξ = 0 := (fin2_eq_zero_iff ξ).2 hzero
      simp [effectiveDomain_eq, quadraticOverLinearEReal, hξ]
    · have hξ : ξ ≠ 0 := by
        intro h
        subst h
        exact hzero ⟨rfl, rfl⟩
      simp [effectiveDomain_eq, quadraticOverLinearEReal, hpos, hzero, hξ]

/-- Theorem 10.1.4 (convex set): `C = {(η₁, η₂) | η₁ + η₂^2/2 ≤ 0}` is convex. -/
theorem convex_quadraticOverLinearSupportSet :
    Convex ℝ quadraticOverLinearSupportSet := by
  intro η hη θ hθ a b ha hb hab
  have hη0 : η 0 ≤ - (η 1 ^ 2) / 2 := by
    have hη' : η 0 + η 1 ^ 2 / 2 ≤ 0 := hη
    have hη0' : η 0 ≤ - (η 1 ^ 2 / 2) := by
      have := add_le_add_right hη' (-(η 1 ^ 2 / 2))
      simpa [add_assoc, add_left_comm, add_comm] using this
    simpa [neg_div] using hη0'
  have hθ0 : θ 0 ≤ - (θ 1 ^ 2) / 2 := by
    have hθ' : θ 0 + θ 1 ^ 2 / 2 ≤ 0 := hθ
    have hθ0' : θ 0 ≤ - (θ 1 ^ 2 / 2) := by
      have := add_le_add_right hθ' (-(θ 1 ^ 2 / 2))
      simpa [add_assoc, add_left_comm, add_comm] using this
    simpa [neg_div] using hθ0'
  have hsquare :
      (a * η 1 + b * θ 1) ^ 2 ≤ a * (η 1) ^ 2 + b * (θ 1) ^ 2 := by
    have hb' : b = 1 - a := by linarith [hab]
    have hnonneg : 0 ≤ a * b * (η 1 - θ 1) ^ 2 := by
      exact mul_nonneg (mul_nonneg ha hb) (sq_nonneg (η 1 - θ 1))
    have hdiff :
        a * (η 1) ^ 2 + b * (θ 1) ^ 2 - (a * η 1 + b * θ 1) ^ 2 =
          a * b * (η 1 - θ 1) ^ 2 := by
      -- Reduce to the usual variance identity using `b = 1 - a`.
      simp [hb', pow_two]
      ring
    have : 0 ≤ a * (η 1) ^ 2 + b * (θ 1) ^ 2 - (a * η 1 + b * θ 1) ^ 2 := by
      simpa [hdiff] using hnonneg
    linarith
  have h0le :
      a * η 0 + b * θ 0 ≤ a * (- (η 1 ^ 2) / 2) + b * (- (θ 1 ^ 2) / 2) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hη0 ha) (mul_le_mul_of_nonneg_left hθ0 hb)
  have hsqdiv :
      (a * η 1 + b * θ 1) ^ 2 / 2 ≤ (a * (η 1) ^ 2 + b * (θ 1) ^ 2) / 2 := by
    exact div_le_div_of_nonneg_right hsquare (by linarith : 0 ≤ (2 : Real))
  have hsum :
      (a * η 0 + b * θ 0) + (a * η 1 + b * θ 1) ^ 2 / 2 ≤
        a * (- (η 1 ^ 2) / 2) + b * (- (θ 1 ^ 2) / 2) + (a * (η 1) ^ 2 + b * (θ 1) ^ 2) / 2 :=
    add_le_add h0le hsqdiv
  have hcancel :
      a * (- (η 1 ^ 2) / 2) + b * (- (θ 1 ^ 2) / 2) + (a * (η 1) ^ 2 + b * (θ 1) ^ 2) / 2 = 0 := by
    ring
  have : (a * η 0 + b * θ 0) + (a * η 1 + b * θ 1) ^ 2 / 2 ≤ 0 := by
    exact le_trans hsum (by simp [hcancel])
  simpa [quadraticOverLinearSupportSet, smul_eq_mul, Pi.add_apply, Pi.smul_apply, add_assoc,
    add_left_comm, add_comm, mul_add, add_mul] using this

/-- Theorem 10.1.4 (support function): `f` is the support function of `C`. -/
theorem quadraticOverLinearEReal_eq_supportFunction :
    quadraticOverLinearEReal =
      fun ξ =>
        sSup
          {z : EReal |
            ∃ η ∈ quadraticOverLinearSupportSet, z = ((dotProduct ξ η : Real) : EReal)} := by
  simpa [quadraticOverLinearSupportValues] using quadraticOverLinearEReal_eq_supportFunction_aux

/-- Theorem 10.1.4 (continuity away from `(0,0)`): `f` is continuous at every nonzero point of
its effective domain. -/
theorem continuousAt_quadraticOverLinearEReal_of_mem_effectiveDomain {x : Fin 2 → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin 2 → Real)) quadraticOverLinearEReal)
    (hx0 : x ≠ 0) :
    ContinuousAt quadraticOverLinearEReal x := by
  -- From the effective-domain characterization, nonzero points in the domain satisfy `x 0 > 0`.
  have hx' :
      x ∈ ({ξ : Fin 2 → Real | ξ 0 > 0} ∪ {0}) := by
    simpa [effectiveDomain_quadraticOverLinearEReal] using hx
  have hxpos : x 0 > 0 := by
    rcases hx' with hxpos | hxzero
    · exact hxpos
    · exact (hx0 (by simpa using hxzero)).elim
  have hopen : IsOpen {y : Fin 2 → Real | y 0 > 0} :=
    isOpen_Ioi.preimage (continuous_apply 0)
  have hxmem : x ∈ {y : Fin 2 → Real | y 0 > 0} := hxpos
  have h_eventually : ∀ᶠ y in nhds x, y 0 > 0 := by
    simpa using (hopen.mem_nhds hxmem)
  have hEq :
      (fun y => quadraticOverLinearEReal y) =ᶠ[nhds x]
        fun y => (((y 1) ^ 2 / (2 * y 0) : Real) : EReal) := by
    filter_upwards [h_eventually] with y hy
    simp [quadraticOverLinearEReal, hy]
  have hxden : (2 * x 0) ≠ 0 := by nlinarith [hxpos.ne']
  have hcontReal :
      ContinuousAt (fun y : Fin 2 → Real => (y 1) ^ 2 / (2 * y 0)) x := by
    have hnum : ContinuousAt (fun y : Fin 2 → Real => (y 1) ^ 2) x := by
      simpa using ((continuous_apply 1).continuousAt.pow 2)
    have hden : ContinuousAt (fun y : Fin 2 → Real => (2 * y 0)) x := by
      simpa [mul_comm] using ((continuous_const.mul (continuous_apply 0)).continuousAt)
    exact hnum.div hden hxden
  have hcontE :
      ContinuousAt (fun y : Fin 2 → Real => (((y 1) ^ 2 / (2 * y 0) : Real) : EReal)) x :=
    ContinuousAt.comp (x := x)
      (f := fun y : Fin 2 → Real => (y 1) ^ 2 / (2 * y 0))
      (g := fun r : Real => (r : EReal))
      (hg := continuous_coe_real_ereal.continuousAt) (hf := hcontReal)
  exact hcontE.congr_of_eventuallyEq hEq


end Section10
end Chap02
