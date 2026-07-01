/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part16
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter
open Set

/-- The indicator function of a nonempty convex set is proper convex on `Set.univ`. -/
lemma section16_properConvexFunctionOn_indicatorFunction_univ {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (hCne : C.Nonempty) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction C) := by
  simpa using
    (properConvexFunctionOn_indicator_of_convex_of_nonempty (C := C) hC hCne)

/-- The convex hull of indicator functions is the indicator of the convex hull of the union. -/
lemma section16_convexHullFunctionFamily_indicatorFunction_eq_indicatorFunction_convexHull_iUnion
    {n : ℕ} {ι : Sort _} (C : ι → Set (Fin n → ℝ)) :
    convexHullFunctionFamily (fun i => indicatorFunction (C i)) =
      indicatorFunction (convexHull ℝ (⋃ i, C i)) := by
  classical
  funext x
  let S : Set ((Fin n → ℝ) × ℝ) :=
    ⋃ i, epigraph (Set.univ : Set (Fin n → ℝ)) (indicatorFunction (C i))
  let Sx : Set ℝ := {μ : ℝ | (x, μ) ∈ convexHull ℝ S}
  have hsubset0 : S ⊆ {p : (Fin n → ℝ) × ℝ | 0 ≤ p.2} := by
    intro p hp
    rcases Set.mem_iUnion.1 hp with ⟨i, hi⟩
    have hle :
        indicatorFunction (C i) p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_univ_iff (f := indicatorFunction (C i))).1 hi
    by_cases hp1 : p.1 ∈ C i
    · have hle' := hle
      simp [indicatorFunction, hp1] at hle'
      exact hle'
    · have hle' := hle
      simp [indicatorFunction, hp1] at hle'
  have hconv0 : Convex ℝ {p : (Fin n → ℝ) × ℝ | 0 ≤ p.2} := by
    intro p hp q hq a b ha hb hsum
    have hp0 : 0 ≤ p.2 := hp
    have hq0 : 0 ≤ q.2 := hq
    have hnonneg : 0 ≤ a * p.2 + b * q.2 := by nlinarith
    have hnonneg' : 0 ≤ a • p.2 + b • q.2 := by
      simpa [smul_eq_mul] using hnonneg
    simpa [Prod.snd_add] using hnonneg'
  have hS_nonneg : convexHull ℝ S ⊆ {p : (Fin n → ℝ) × ℝ | 0 ≤ p.2} :=
    convexHull_min hsubset0 hconv0
  have hx_of_mem :
      ∀ μ, (x, μ) ∈ convexHull ℝ S → x ∈ convexHull ℝ (⋃ i, C i) := by
    intro μ hmem
    let fst : ((Fin n → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ) := LinearMap.fst ℝ (Fin n → ℝ) ℝ
    have himage :
        fst '' convexHull ℝ S = convexHull ℝ (fst '' S) := by
      simpa using (LinearMap.image_convexHull (f := fst) (s := S))
    have hxmem : x ∈ fst '' convexHull ℝ S := by
      exact ⟨(x, μ), hmem, rfl⟩
    have hxmem' : x ∈ convexHull ℝ (fst '' S) := by
      simpa [himage] using hxmem
    have himageS : fst '' S = ⋃ i, C i := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        rcases Set.mem_iUnion.1 hp with ⟨i, hi⟩
        have hle :
            indicatorFunction (C i) p.1 ≤ (p.2 : EReal) :=
          (mem_epigraph_univ_iff (f := indicatorFunction (C i))).1 hi
        by_cases hp1 : p.1 ∈ C i
        · exact Set.mem_iUnion.2 ⟨i, hp1⟩
        · have hle' := hle
          simp [indicatorFunction, hp1] at hle'
      · intro hy
        rcases Set.mem_iUnion.1 hy with ⟨i, hyi⟩
        refine ⟨(y, 0), ?_, rfl⟩
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        apply (mem_epigraph_univ_iff (f := indicatorFunction (C i))).2
        simp [indicatorFunction, hyi]
    simpa [himageS] using hxmem'
  by_cases hx : x ∈ convexHull ℝ (⋃ i, C i)
  · have hmem0 : (0 : ℝ) ∈ Sx := by
      have hmem : (x, (0 : ℝ)) ∈ convexHull ℝ S := by
        let inl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) × ℝ :=
          LinearMap.inl ℝ (Fin n → ℝ) ℝ
        have hximg : (x, (0 : ℝ)) ∈ inl '' convexHull ℝ (⋃ i, C i) := by
          refine ⟨x, hx, ?_⟩
          simp [inl]
        have himage :
            inl '' convexHull ℝ (⋃ i, C i) =
              convexHull ℝ (inl '' (⋃ i, C i)) := by
          simpa using (LinearMap.image_convexHull (f := inl) (s := ⋃ i, C i))
        have hximg' : (x, (0 : ℝ)) ∈ convexHull ℝ (inl '' (⋃ i, C i)) := by
          simpa [himage] using hximg
        have hsubset : inl '' (⋃ i, C i) ⊆ S := by
          intro p hp
          rcases hp with ⟨y, hy, rfl⟩
          rcases Set.mem_iUnion.1 hy with ⟨i, hyi⟩
          refine Set.mem_iUnion.2 ⟨i, ?_⟩
          apply (mem_epigraph_univ_iff (f := indicatorFunction (C i))).2
          simp [indicatorFunction, hyi]
        exact (convexHull_mono hsubset) hximg'
      exact hmem
    have hle0 :
        sInf ((fun μ : ℝ => (μ : EReal)) '' Sx) ≤ (0 : EReal) := by
      refine sInf_le ?_
      exact ⟨0, hmem0, rfl⟩
    have hge0 :
        (0 : EReal) ≤ sInf ((fun μ : ℝ => (μ : EReal)) '' Sx) := by
      refine le_sInf ?_
      intro z hz
      rcases hz with ⟨μ, hμ, rfl⟩
      have hμ0 : 0 ≤ μ := by
        have hmem : (x, μ) ∈ convexHull ℝ S := hμ
        have hmem' : (x, μ) ∈ {p : (Fin n → ℝ) × ℝ | 0 ≤ p.2} :=
          hS_nonneg hmem
        simpa using hmem'
      exact (EReal.coe_le_coe_iff).2 hμ0
    have hEq :
        sInf ((fun μ : ℝ => (μ : EReal)) '' Sx) = (0 : EReal) :=
      le_antisymm hle0 hge0
    simp [convexHullFunctionFamily, Sx, S, hEq, indicatorFunction, hx]
  · have hSempty : Sx = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro μ hμ
      exact hx (hx_of_mem μ hμ)
    simp [convexHullFunctionFamily, Sx, S, hSempty, indicatorFunction, hx]

/-- Support function of the convex hull of a union as a supremum of support functions. -/
lemma section16_supportFunctionEReal_convexHull_iUnion {n : ℕ} {ι : Sort _}
    (C : ι → Set (Fin n → ℝ)) (hC : ∀ i, Convex ℝ (C i)) (hCne : ∀ i, (C i).Nonempty) :
    supportFunctionEReal (convexHull ℝ (⋃ i, C i)) =
      fun xStar => sSup (Set.range fun i => supportFunctionEReal (C i) xStar) := by
  classical
  have hproper :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction (C i)) := by
    intro i
    exact section16_properConvexFunctionOn_indicatorFunction_univ (hC i) (hCne i)
  have hsup :=
    section16_fenchelConjugate_convexHullFunctionFamily
      (f := fun i => indicatorFunction (C i)) hproper
  simpa
      [section16_convexHullFunctionFamily_indicatorFunction_eq_indicatorFunction_convexHull_iUnion,
        section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using hsup

/-- Corollary 16.5.1.1: Let `C i` be a non-empty convex set in `ℝⁿ` for each `i` in an index set.
Let `D` be the convex hull of the union `⋃ i, C i`. Then the support function satisfies

`δ^*(· | D) = sup { δ^*(· | C i) | i }`,

where `δ^*(· | C)` is represented by `supportFunctionEReal C`. -/
theorem section16_deltaStar_convexHull_iUnion {n : ℕ} {ι : Sort _} (C : ι → Set (Fin n → ℝ))
    (hC : ∀ i, Convex ℝ (C i)) (hCne : ∀ i, (C i).Nonempty) :
    supportFunctionEReal (convexHull ℝ (⋃ i, C i)) =
      fun xStar => sSup (Set.range fun i => supportFunctionEReal (C i) xStar) := by
  simpa using (section16_supportFunctionEReal_convexHull_iUnion (C := C) hC hCne)

/-- Applying Theorem 16.5.1 to the family of conjugates yields the supremum of closures. -/
lemma section16_fenchelConjugate_convexHullFunctionFamily_fenchelConjugate_eq_sSup_convexFunctionClosure
    {n : ℕ} {ι : Sort _} (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (convexHullFunctionFamily fun i => fenchelConjugate n (f i)) =
      fun x => sSup (Set.range fun i => convexFunctionClosure (f i) x) := by
  classical
  have hproper :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fenchelConjugate n (f i)) := by
    intro i
    simpa using (proper_fenchelConjugate_of_proper (n := n) (f := f i) (hf i))
  have hsup :=
    section16_fenchelConjugate_convexHullFunctionFamily
      (f := fun i => fenchelConjugate n (f i)) (hf := hproper)
  have hbiconj :
      ∀ i, fenchelConjugate n (fenchelConjugate n (f i)) = convexFunctionClosure (f i) := by
    intro i
    have hconv : ConvexFunction (f i) := by
      simpa [ConvexFunction] using (hf i).1
    simpa using
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n)
        (f := f i) hconv)
  simpa [hbiconj] using hsup

/-- The convex hull of the conjugate family is a convex function. -/
lemma section16_convexFunction_convexHullFunctionFamily_fenchelConjugate {n : ℕ} {ι : Sort _}
    (f : ι → (Fin n → ℝ) → EReal) :
    ConvexFunction (convexHullFunctionFamily fun i => fenchelConjugate n (f i)) := by
  have hminor :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (convexHullFunctionFamily fun i => fenchelConjugate n (f i)) ∧
        (∀ i, convexHullFunctionFamily (fun i => fenchelConjugate n (f i)) ≤
          fun x => fenchelConjugate n (f i) x) ∧
        ∀ h : (Fin n → ℝ) → EReal,
          ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h →
          (∀ i, h ≤ fun x => fenchelConjugate n (f i) x) →
          h ≤ convexHullFunctionFamily fun i => fenchelConjugate n (f i) := by
    simpa using
      (convexHullFunctionFamily_greatest_convex_minorant
        (f := fun i => fenchelConjugate n (f i)))
  simpa [ConvexFunction] using hminor.1

/-- The conjugate of the supremum of closures is the closure of the convex hull of conjugates. -/
lemma section16_fenchelConjugate_sSup_convexFunctionClosure_eq_via_biconjugate
    {n : ℕ} {ι : Sort _} (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (fun x => sSup (Set.range fun i => convexFunctionClosure (f i) x)) =
      convexFunctionClosure (convexHullFunctionFamily fun i => fenchelConjugate n (f i)) := by
  have hkey :=
    section16_fenchelConjugate_convexHullFunctionFamily_fenchelConjugate_eq_sSup_convexFunctionClosure
      (f := f) hf
  have hconv :=
    section16_convexFunction_convexHullFunctionFamily_fenchelConjugate (f := f)
  calc
    fenchelConjugate n (fun x => sSup (Set.range fun i => convexFunctionClosure (f i) x)) =
        fenchelConjugate n
          (fenchelConjugate n (convexHullFunctionFamily fun i => fenchelConjugate n (f i))) := by
      rw [← hkey]
    _ = convexFunctionClosure (convexHullFunctionFamily fun i => fenchelConjugate n (f i)) := by
      simpa using
        (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n)
          (f := convexHullFunctionFamily fun i => fenchelConjugate n (f i)) hconv)

/-- Theorem 16.5.2: Let `f i` be a proper convex function on `ℝ^n` for each `i` in an (arbitrary)
index set. Then the Fenchel conjugate of the pointwise supremum of the closures `cl f_i` is the
closure of the convex hull of the conjugates:

`(sup {cl f_i | i ∈ I})^* = cl (conv {f_i^* | i ∈ I})`.

Here `cl` is the convex-function closure `convexFunctionClosure`, `sup` is modeled pointwise by
`x ↦ sSup (range fun i => ·)`, `conv` is `convexHullFunctionFamily`, and `f_i^*` is
`fenchelConjugate n (f i)`. -/
theorem section16_fenchelConjugate_sSup_convexFunctionClosure_eq_convexFunctionClosure_convexHullFunctionFamily
    {n : ℕ} {ι : Sort _} (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (fun x => sSup (Set.range fun i => convexFunctionClosure (f i) x)) =
      convexFunctionClosure (convexHullFunctionFamily fun i => fenchelConjugate n (f i)) := by
  simpa using
    (section16_fenchelConjugate_sSup_convexFunctionClosure_eq_via_biconjugate (f := f) hf)

/-- Pointwise supremum of indicator functions of closures is the indicator of the intersection. -/
lemma section16_sSup_range_indicatorFunction_closure_eq_indicatorFunction_iInter_closure
    {n : ℕ} {ι : Sort _} [Nonempty ι] (C : ι → Set (Fin n → ℝ)) :
    (fun x => sSup (Set.range fun i => indicatorFunction (closure (C i)) x)) =
      indicatorFunction (⋂ i, closure (C i)) := by
  classical
  funext x
  by_cases hx : x ∈ ⋂ i, closure (C i)
  · have hle :
        sSup (Set.range fun i => indicatorFunction (closure (C i)) x) ≤ (0 : EReal) := by
      refine sSup_le ?_
      intro z hz
      rcases hz with ⟨i, rfl⟩
      have hx_i : x ∈ closure (C i) := (Set.mem_iInter.mp hx i)
      simp [indicatorFunction, hx_i]
    have hge :
        (0 : EReal) ≤ sSup (Set.range fun i => indicatorFunction (closure (C i)) x) := by
      rcases (inferInstance : Nonempty ι) with ⟨i0⟩
      have hx_i0 : x ∈ closure (C i0) := (Set.mem_iInter.mp hx i0)
      have hmem :
          indicatorFunction (closure (C i0)) x ∈
            Set.range fun i => indicatorFunction (closure (C i)) x := ⟨i0, rfl⟩
      have hle' : (0 : EReal) ≤ indicatorFunction (closure (C i0)) x := by
        simp [indicatorFunction, hx_i0]
      exact le_trans hle' (le_sSup hmem)
    have hsup :
        sSup (Set.range fun i => indicatorFunction (closure (C i)) x) = (0 : EReal) :=
      le_antisymm hle hge
    simpa [indicatorFunction, hx] using hsup
  · have hx' : ∃ i, x ∉ closure (C i) := by
      by_contra h'
      have hforall : ∀ i, x ∈ closure (C i) := by
        intro i
        by_contra hx_i
        exact h' ⟨i, hx_i⟩
      exact hx (Set.mem_iInter.mpr hforall)
    rcases hx' with ⟨i0, hx_i0⟩
    have hmem :
        indicatorFunction (closure (C i0)) x ∈
          Set.range fun i => indicatorFunction (closure (C i)) x := ⟨i0, rfl⟩
    have htop : indicatorFunction (closure (C i0)) x = (⊤ : EReal) := by
      simp [indicatorFunction, hx_i0]
    have hge :
        (⊤ : EReal) ≤ sSup (Set.range fun i => indicatorFunction (closure (C i)) x) := by
      simpa [htop] using (le_sSup hmem)
    have hsup :
        sSup (Set.range fun i => indicatorFunction (closure (C i)) x) = (⊤ : EReal) :=
      le_antisymm le_top hge
    simpa [indicatorFunction, hx] using hsup

/-- Support function of the intersection of closures as a convex hull closure. -/
lemma section16_supportFunctionEReal_iInter_closure_eq_convexFunctionClosure_convexHullFunctionFamily
    {n : ℕ} {ι : Sort _} [Nonempty ι] (C : ι → Set (Fin n → ℝ))
    (hC : ∀ i, Convex ℝ (C i)) (hCne : ∀ i, (C i).Nonempty) :
    supportFunctionEReal (⋂ i, closure (C i)) =
      convexFunctionClosure (convexHullFunctionFamily fun i => supportFunctionEReal (C i)) := by
  classical
  have hproper :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction (C i)) := by
    intro i
    exact section16_properConvexFunctionOn_indicatorFunction_univ (hC i) (hCne i)
  have hcl :
      ∀ i, convexFunctionClosure (indicatorFunction (C i)) = indicatorFunction (closure (C i)) := by
    intro i
    simpa using
      (section16_convexFunctionClosure_indicatorFunction_eq_indicatorFunction_closure
        (C i) (hC i) (hCne i))
  have hsup :=
    section16_fenchelConjugate_sSup_convexFunctionClosure_eq_convexFunctionClosure_convexHullFunctionFamily
      (f := fun i => indicatorFunction (C i)) hproper
  simpa [hcl, section16_sSup_range_indicatorFunction_closure_eq_indicatorFunction_iInter_closure,
    section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal] using hsup

/-- Corollary 16.5.1.2: Let `C i` be a non-empty convex set in `ℝ^n` for each `i` in an index set.
Let `C` be the intersection `⋂ i, closure (C i)`. Then the support function satisfies

`δ^*(· | C) = cl (conv { δ^*(· | C i) | i })`.

Moreover,

`δ^*(· | D) = sup { δ^*(· | C i) | i }`.

In this development, `δ^*` is `supportFunctionEReal`, `cl` is `convexFunctionClosure`, and `conv`
is `convexHullFunctionFamily`. -/
theorem section16_supportFunctionEReal_iInter_closure_eq_convexFunctionClosure_convexHullFunctionFamily_and_convexHull_iUnion
    {n : ℕ} {ι : Sort _} [Nonempty ι] (C : ι → Set (Fin n → ℝ))
    (hC : ∀ i, Convex ℝ (C i)) (hCne : ∀ i, (C i).Nonempty) :
    let C' : Set (Fin n → ℝ) := ⋂ i, closure (C i)
    let D : Set (Fin n → ℝ) := convexHull ℝ (⋃ i, C i)
    (supportFunctionEReal C' =
        convexFunctionClosure (convexHullFunctionFamily fun i => supportFunctionEReal (C i))) ∧
      (supportFunctionEReal D = fun xStar => sSup (Set.range fun i => supportFunctionEReal (C i) xStar)) := by
  refine ⟨?_, ?_⟩
  · simpa using
      (section16_supportFunctionEReal_iInter_closure_eq_convexFunctionClosure_convexHullFunctionFamily
        (C := C) hC hCne)
  · simpa using (section16_deltaStar_convexHull_iUnion (C := C) hC hCne)

/-- The sublevel set `{x | dotProduct x xStar ≤ 1}` is convex. -/
lemma section16_convex_set_dotProduct_le_one {n : ℕ} (xStar : Fin n → ℝ) :
    Convex ℝ {x : Fin n → ℝ | (dotProduct x xStar : ℝ) ≤ 1} := by
  intro x hx y hy a b ha hb hsum
  have hx' : (dotProduct x xStar : ℝ) ≤ 1 := by
    simpa using hx
  have hy' : (dotProduct y xStar : ℝ) ≤ 1 := by
    simpa using hy
  have hcalc :
      dotProduct (a • x + b • y) xStar =
        a * dotProduct x xStar + b * dotProduct y xStar := by
    simp [smul_eq_mul]
  have hineq : (dotProduct (a • x + b • y) xStar : ℝ) ≤ 1 := by
    nlinarith [hcalc, hx', hy', ha, hb, hsum]
  simpa using hineq

/-- Polar inclusion from the convex hull of a union to the intersection of polars. -/
lemma section16_polar_convexHull_iUnion_subset_iInter_polars {n : ℕ} {ι : Sort _}
    (C : ι → Set (Fin n → ℝ)) (xStar : Fin n → ℝ)
    (h : ∀ x ∈ convexHull ℝ (⋃ i, C i), (dotProduct x xStar : ℝ) ≤ 1) :
    ∀ i, ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1 := by
  intro i x hx
  have hx' : x ∈ convexHull ℝ (⋃ i, C i) := by
    exact (subset_convexHull ℝ (⋃ i, C i)) (Set.mem_iUnion.2 ⟨i, hx⟩)
  exact h x hx'

/-- Polar inclusion from the intersection of polars to the polar of the convex hull of a union. -/
lemma section16_iInter_polars_subset_polar_convexHull_iUnion {n : ℕ} {ι : Sort _}
    (C : ι → Set (Fin n → ℝ)) (xStar : Fin n → ℝ)
    (h : ∀ i, ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1) :
    ∀ x ∈ convexHull ℝ (⋃ i, C i), (dotProduct x xStar : ℝ) ≤ 1 := by
  intro x hx
  let H : Set (Fin n → ℝ) := {x : Fin n → ℝ | (dotProduct x xStar : ℝ) ≤ 1}
  have hconv : Convex ℝ H := by
    simpa [H] using (section16_convex_set_dotProduct_le_one (xStar := xStar))
  have hsubset : (⋃ i, C i) ⊆ H := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
    simpa [H] using h i x hx
  have hconvHull : convexHull ℝ (⋃ i, C i) ⊆ H := convexHull_min hsubset hconv
  simpa [H] using hconvHull hx

/-- Corollary 16.5.2.1: Let `C i` be a convex set in `ℝ^n` for each `i` in an index set. Then the
polar of the convex hull of the family equals the intersection of the polars:

`(conv { C_i | i ∈ I })^∘ = ⋂ { C_i^∘ | i ∈ I }`.

In this development, `conv { C_i | i ∈ I }` is represented by `convexHull ℝ (⋃ i, C i)`, and the
polar of a set `S` is represented by `{xStar | ∀ x ∈ S, (dotProduct x xStar : ℝ) ≤ 1}`. -/
theorem section16_polar_convexHull_iUnion_eq_iInter_polars {n : ℕ} {ι : Sort _}
    (C : ι → Set (Fin n → ℝ)) :
    {xStar : Fin n → ℝ | ∀ x ∈ convexHull ℝ (⋃ i, C i), (dotProduct x xStar : ℝ) ≤ 1} =
      ⋂ i, {xStar : Fin n → ℝ | ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1} := by
  ext xStar
  constructor
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro i
    exact (section16_polar_convexHull_iUnion_subset_iInter_polars (C := C) xStar hx i)
  · intro hx
    have hx' : ∀ i, ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1 := by
      intro i x hxC
      have hxmem :
          xStar ∈ {xStar : Fin n → ℝ | ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1} :=
        (Set.mem_iInter.1 hx i)
      exact hxmem x hxC
    exact (section16_iInter_polars_subset_polar_convexHull_iUnion (C := C) xStar hx')

/-- A common point in the intersection of closures yields a proper convex hull of support
functions with a finite `≤ 1` sublevel. -/
lemma section16_properConvexFunctionOn_convexHullFunctionFamily_supportFamily_of_exists_common_point
    {n : ℕ} {ι : Sort _} [Nonempty ι] (C : ι → Set (Fin n → ℝ))
    (hC : ∀ i, Convex ℝ (C i)) (hInter : (⋂ i, closure (C i)).Nonempty) :
    let g : ι → (Fin n → ℝ) → EReal := fun i => supportFunctionEReal (C i)
    let h := convexHullFunctionFamily g
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h ∧
      iInf (fun xStar => h xStar) < (1 : EReal) := by
  classical
  rcases hInter with ⟨x0, hx0⟩
  have hx0i : ∀ i, x0 ∈ closure (C i) := by
    intro i
    exact (Set.mem_iInter.1 hx0 i)
  have hCne : ∀ i, (C i).Nonempty := by
    intro i
    by_contra hne
    have hCi : C i = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    have : x0 ∈ closure (C i) := hx0i i
    simp [hCi] at this
  let g : ι → (Fin n → ℝ) → EReal := fun i => supportFunctionEReal (C i)
  let h := convexHullFunctionFamily g
  have hminor := convexHullFunctionFamily_greatest_convex_minorant (f := g)
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [h] using hminor.1
  have hle : ∀ i, h ≤ g i := by
    intro i
    simpa [h] using hminor.2.1 i
  let l : (Fin n → ℝ) → EReal := fun xStar => ((dotProduct x0 xStar : ℝ) : EReal)
  have hlconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) l := by
    have hlin :=
      section16_convexFunctionOn_dotProduct_sub_const (b := x0) (μ := (0 : ℝ))
    simpa [l, dotProduct_comm] using hlin
  have hcl : ∀ i, supportFunctionEReal (C i) = supportFunctionEReal (closure (C i)) := by
    intro i
    calc
      supportFunctionEReal (C i) =
          fenchelConjugate n (indicatorFunction (C i)) := by
            symm
            exact section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := C i)
      _ = fenchelConjugate n (convexFunctionClosure (indicatorFunction (C i))) := by
            symm
            exact
              (fenchelConjugate_eq_of_convexFunctionClosure (n := n)
                (f := indicatorFunction (C i)))
      _ = fenchelConjugate n (indicatorFunction (closure (C i))) := by
            simp [section16_convexFunctionClosure_indicatorFunction_eq_indicatorFunction_closure,
              hC i, hCne i]
      _ = supportFunctionEReal (closure (C i)) := by
            exact
              section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
                (C := closure (C i))
  have hlle : ∀ i, l ≤ g i := by
    intro i xStar
    have hmem :
        ((dotProduct x0 xStar : ℝ) : EReal) ∈
          {z : EReal | ∃ x ∈ closure (C i), z = ((dotProduct x xStar : ℝ) : EReal)} :=
      ⟨x0, hx0i i, rfl⟩
    have hle' :
        ((dotProduct x0 xStar : ℝ) : EReal) ≤ supportFunctionEReal (closure (C i)) xStar := by
      simpa [supportFunctionEReal] using (le_sSup hmem)
    simpa [g, l, (hcl i).symm] using hle'
  have hlin_le_h : l ≤ h := by
    have hgreat := hminor.2.2 (h := l) hlconv hlle
    simpa [h] using hgreat
  have hbot : ∀ xStar, h xStar ≠ (⊥ : EReal) := by
    intro xStar hbot
    have hlebot : l xStar ≤ (⊥ : EReal) := by
      simpa [hbot] using hlin_le_h xStar
    have hlebot' : l xStar = (⊥ : EReal) := (le_bot_iff).1 hlebot
    exact (EReal.coe_ne_bot (dotProduct x0 xStar)) hlebot'
  have h0le : h (0 : Fin n → ℝ) ≤ (0 : EReal) := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hgi0 : g i0 (0 : Fin n → ℝ) = (0 : EReal) := by
      have hnonempty : (∃ x, x ∈ C i0) := hCne i0
      have hsup :
          sSup {z : EReal | (∃ x, x ∈ C i0) ∧ z = 0} = (0 : EReal) := by
        simp [hnonempty]
      have hsup' :
          sSup
              {z : EReal |
                ∃ x ∈ C i0, z = ((dotProduct x (0 : Fin n → ℝ) : ℝ) : EReal)} =
            (0 : EReal) := by
        simpa using hsup
      simpa [g, supportFunctionEReal] using hsup'
    have hle0 : h (0 : Fin n → ℝ) ≤ g i0 (0 : Fin n → ℝ) := (hle i0) _
    simpa [hgi0] using hle0
  have hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → ℝ)) h) := by
    refine ⟨((0 : Fin n → ℝ), (0 : ℝ)), ?_⟩
    simpa [mem_epigraph_univ_iff] using h0le
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    refine ⟨hconv, hne, ?_⟩
    intro xStar _
    exact hbot xStar
  have hInf : iInf (fun xStar => h xStar) < (1 : EReal) := by
    have hInf_le : iInf (fun xStar => h xStar) ≤ h (0 : Fin n → ℝ) := by
      exact iInf_le _ _
    have h0lt : h (0 : Fin n → ℝ) < (1 : EReal) := by
      have hlt : (0 : EReal) < (1 : EReal) := by simp
      exact lt_of_le_of_lt h0le hlt
    exact lt_of_le_of_lt hInf_le h0lt
  exact ⟨hproper, hInf⟩

/-- Raising the second coordinate preserves membership in the convex hull of a union of epigraphs. -/
lemma section16_convexHull_union_epigraph_mono_snd {n : ℕ} {ι : Sort _}
    {g : ι → (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {μ μ' : ℝ}
    (hmem :
      (x, μ) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i)))
    (hle : μ ≤ μ') :
    (x, μ') ∈
      convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i)) := by
  classical
  rcases
      (mem_convexHull_union_epigraph_iff_fin_combo (f := g) (x := x) (μ := μ)).1 hmem with
    ⟨m, idx, lam, x', μ0, hlam, hsum1, hsumx, hsumμ, hleμ⟩
  let δ : ℝ := μ' - μ
  have hδ : 0 ≤ δ := sub_nonneg.mpr hle
  let μ1 : Fin m → ℝ := fun i => μ0 i + δ
  have hsumμ' : Finset.univ.sum (fun i => lam i * μ1 i) = μ' := by
    have hsumδ :
        Finset.univ.sum (fun i => lam i * δ) =
          (Finset.univ.sum fun i => lam i) * δ := by
      simpa using (Finset.sum_mul (s := Finset.univ) (f := lam) (a := δ)).symm
    calc
      Finset.univ.sum (fun i => lam i * μ1 i) =
          Finset.univ.sum (fun i => lam i * μ0 i) +
            Finset.univ.sum (fun i => lam i * δ) := by
          simp [μ1, mul_add, Finset.sum_add_distrib]
      _ = μ + (Finset.univ.sum fun i => lam i) * δ := by
          simp [hsumμ, hsumδ]
      _ = μ + δ := by simp [hsum1]
      _ = μ' := by simp [δ]
  have hleμ' : ∀ i, g (idx i) (x' i) ≤ (μ1 i : EReal) := by
    intro i
    have hμle : (μ0 i : EReal) ≤ (μ1 i : EReal) := by
      exact (EReal.coe_le_coe_iff).2 (by linarith [hδ])
    exact le_trans (hleμ i) hμle
  exact
    (mem_convexHull_union_epigraph_iff_fin_combo (f := g) (x := x) (μ := μ')).2
      ⟨m, idx, lam, x', μ1, hlam, hsum1, hsumx, hsumμ', hleμ'⟩

/-- A small epigraph height above `1` appears in the convex hull of the union of epigraphs. -/
lemma section16_exists_mem_convexHull_union_epigraph_lt_one_add_eps_of_hle_one {n : ℕ} {ι : Sort _}
    (g : ι → (Fin n → ℝ) → EReal) {xStar : Fin n → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hle : convexHullFunctionFamily g xStar ≤ (1 : EReal)) :
    ∃ μ : ℝ, μ < 1 + ε ∧
      (xStar, μ) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i)) := by
  classical
  let A : Set EReal :=
    (fun μ : ℝ => (μ : EReal)) ''
      {μ : ℝ |
        (xStar, μ) ∈
          convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i))}
  have hdef : convexHullFunctionFamily g xStar = sInf A := by
    simp [convexHullFunctionFamily, A]
  have hlt1 : ((1 : ℝ) : EReal) < ((1 + ε : ℝ) : EReal) := by
    exact (EReal.coe_lt_coe_iff).2 (by linarith)
  have hlt : sInf A < ((1 + ε : ℝ) : EReal) := by
    have hle' : convexHullFunctionFamily g xStar ≤ (1 : EReal) := hle
    have hlt' : convexHullFunctionFamily g xStar < ((1 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hle' hlt1
    simpa [hdef] using hlt'
  have hexists : ∃ a ∈ A, a < ((1 + ε : ℝ) : EReal) := by
    by_contra hcontra
    push_neg at hcontra
    have hle' : ((1 + ε : ℝ) : EReal) ≤ sInf A := by
      refine le_sInf ?_
      intro a ha
      exact hcontra a ha
    have : ((1 + ε : ℝ) : EReal) < ((1 + ε : ℝ) : EReal) := lt_of_le_of_lt hle' hlt
    exact (lt_irrefl _ this)
  rcases hexists with ⟨a, haA, hltA⟩
  rcases haA with ⟨μ, hμ, rfl⟩
  have hμlt : μ < 1 + ε := (EReal.coe_lt_coe_iff).1 hltA
  exact ⟨μ, hμlt, hμ⟩

/-- Positive homogeneity scales epigraph points. -/
lemma section16_epigraph_univ_posHom_smul_mem {n : ℕ} {g : (Fin n → ℝ) → EReal}
    (hpos : PositivelyHomogeneous g) {x : Fin n → ℝ} {μ t : ℝ} (ht : 0 < t)
    (hmem : (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) g) :
    (t • x, t * μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) g := by
  have hle : g x ≤ (μ : EReal) := by
    simpa [mem_epigraph_univ_iff] using hmem
  have ht' : (0 : EReal) ≤ (t : EReal) :=
    (EReal.coe_le_coe_iff).2 (le_of_lt ht)
  have hle' : (t : EReal) * g x ≤ (t : EReal) * (μ : EReal) :=
    mul_le_mul_of_nonneg_left hle ht'
  have hpos' : g (t • x) = (t : EReal) * g x := hpos x t ht
  have hle'' : g (t • x) ≤ (t * μ : EReal) := by
    calc
      g (t • x) = (t : EReal) * g x := hpos'
      _ ≤ (t : EReal) * (μ : EReal) := hle'
      _ = (t * μ : EReal) := by
            simp
  simpa [mem_epigraph_univ_iff] using hle''

/-- Scaling preserves membership in the convex hull of a union of epigraphs. -/
lemma section16_convexHull_union_epigraph_smul_mem {n : ℕ} {ι : Sort _}
    {g : ι → (Fin n → ℝ) → EReal} (hpos : ∀ i, PositivelyHomogeneous (g i))
    {x : Fin n → ℝ} {μ t : ℝ} (ht : 0 < t)
    (hmem :
      (x, μ) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i))) :
    (t • x, t * μ) ∈
      convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i)) := by
  classical
  rcases
      (mem_convexHull_union_epigraph_iff_fin_combo (f := g) (x := x) (μ := μ)).1 hmem with
    ⟨m, idx, lam, x', μ', hlam, hsum1, hsumx, hsumμ, hleμ⟩
  let x'' : Fin m → (Fin n → ℝ) := fun i => t • x' i
  let μ'' : Fin m → ℝ := fun i => t * μ' i
  have hsumx' : Finset.univ.sum (fun i => lam i • x'' i) = t • x := by
    calc
      Finset.univ.sum (fun i => lam i • x'' i) =
          Finset.univ.sum (fun i => t • (lam i • x' i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [x'', smul_smul, mul_comm]
      _ = t • Finset.univ.sum (fun i => lam i • x' i) := by
            simpa using
              (Finset.smul_sum (s := Finset.univ) (f := fun i => lam i • x' i) (r := t)).symm
      _ = t • x := by
            simp [hsumx]
  have hsumμ' : Finset.univ.sum (fun i => lam i * μ'' i) = t * μ := by
    calc
      Finset.univ.sum (fun i => lam i * μ'' i) =
          Finset.univ.sum (fun i => (lam i * μ' i) * t) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [μ'', mul_comm, mul_left_comm]
      _ = (Finset.univ.sum fun i => lam i * μ' i) * t := by
            simpa using
              (Finset.sum_mul (s := Finset.univ) (f := fun i => lam i * μ' i) (a := t)).symm
      _ = t * μ := by
            simp [hsumμ, mul_comm]
  have hleμ' : ∀ i, g (idx i) (x'' i) ≤ (μ'' i : EReal) := by
    intro i
    have ht' : (0 : EReal) ≤ (t : EReal) :=
      (EReal.coe_le_coe_iff).2 (le_of_lt ht)
    have hpos' : g (idx i) (x'' i) = (t : EReal) * g (idx i) (x' i) := by
      simpa [x''] using (hpos (idx i) (x' i) t ht)
    have hle' : (t : EReal) * g (idx i) (x' i) ≤ (t : EReal) * (μ' i : EReal) :=
      mul_le_mul_of_nonneg_left (hleμ i) ht'
    calc
      g (idx i) (x'' i) = (t : EReal) * g (idx i) (x' i) := hpos'
      _ ≤ (t : EReal) * (μ' i : EReal) := hle'
      _ = (μ'' i : EReal) := by
            simp [μ'']
  exact
    (mem_convexHull_union_epigraph_iff_fin_combo (f := g) (x := t • x) (μ := t * μ)).2
      ⟨m, idx, lam, x'', μ'', hlam, hsum1, hsumx', hsumμ', hleμ'⟩

/-- Closedness and convexity of the closure of the convex hull of level-1 sublevels. -/
lemma section16_closedConvex_closure_convexHull_iUnion_sublevels
    {n : ℕ} {ι : Sort _} {g : ι → (Fin n → ℝ) → EReal} :
    IsClosed
        (closure
          (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}))) ∧
      Convex ℝ
        (closure
          (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}))) := by
  constructor
  · exact isClosed_closure
  ·
    have hconv :
        Convex ℝ (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) := by
      simpa using
        (convex_convexHull ℝ (s := ⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}))
    exact hconv.closure

/-- A separating continuous linear functional for a point outside the closed convex hull. -/
lemma section16_exists_sep_clm_of_not_mem_closure_convexHull_iUnion_sublevels
    {n : ℕ} {ι : Sort _} {g : ι → (Fin n → ℝ) → EReal} {xStar : Fin n → ℝ}
    (hx :
      xStar ∉
        closure
          (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}))) :
    ∃ φ : (Fin n → ℝ) →L[ℝ] ℝ, ∃ u : ℝ,
      (∀ y ∈
          closure
            (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})),
          φ y ≤ u) ∧
        u < φ xStar := by
  classical
  set K :=
    closure
      (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) with hK
  have hclosed : IsClosed K := by
    simp [hK]
  have hconv : Convex ℝ K := by
    simp [hK]
    exact (section16_closedConvex_closure_convexHull_iUnion_sublevels (g := g)).2
  obtain ⟨φ, u, hφ, hu⟩ :=
    geometric_hahn_banach_closed_point (E := (Fin n → ℝ)) (s := K) (x := xStar) hconv hclosed
      (by simpa [hK] using hx)
  refine ⟨φ, u, ?_, hu⟩
  intro y hy
  exact le_of_lt (hφ y hy)

/-- A separator bounded on the level-1 sublevel controls positive-height epigraph points. -/
lemma section16_clm_le_mul_snd_of_mem_epigraph_of_pos {n : ℕ} {ι : Sort _}
    {g : ι → (Fin n → ℝ) → EReal} {i : ι} (hpos : PositivelyHomogeneous (g i))
    {φ : (Fin n → ℝ) →L[ℝ] ℝ} {u : ℝ}
    (hbound : ∀ z, g i z ≤ (1 : EReal) → φ z ≤ u)
    {x : Fin n → ℝ} {μ : ℝ}
    (hmem : (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i)) (hμ : 0 < μ) :
    φ x ≤ u * μ := by
  have hle : g i x ≤ (μ : EReal) := by
    simpa [mem_epigraph_univ_iff] using hmem
  have hμpos : 0 < (μ⁻¹ : ℝ) := inv_pos.mpr hμ
  have hμpos' : (0 : EReal) ≤ (μ⁻¹ : EReal) :=
    (EReal.coe_le_coe_iff).2 (le_of_lt hμpos)
  have hpos' : g i (μ⁻¹ • x) = (μ⁻¹ : EReal) * g i x := hpos x (μ⁻¹) hμpos
  have hle' : g i (μ⁻¹ • x) ≤ (1 : EReal) := by
    have hle'' : (μ⁻¹ : EReal) * g i x ≤ (μ⁻¹ : EReal) * (μ : EReal) :=
      mul_le_mul_of_nonneg_left hle hμpos'
    have hμne : μ ≠ 0 := by linarith
    calc
      g i (μ⁻¹ • x) = (μ⁻¹ : EReal) * g i x := hpos'
      _ ≤ (μ⁻¹ : EReal) * (μ : EReal) := hle''
      _ = ((μ⁻¹ * μ : ℝ) : EReal) := by
          exact (EReal.coe_mul (μ⁻¹) μ).symm
      _ = (1 : EReal) := by
          simp [inv_mul_cancel₀ hμne]
  have hφ : φ (μ⁻¹ • x) ≤ u := hbound _ hle'
  have hlin : φ (μ⁻¹ • x) = (μ⁻¹ : ℝ) * φ x := by
    simp [smul_eq_mul]
  have hφ' : (μ⁻¹ : ℝ) * φ x ≤ u := by
    simpa [hlin] using hφ
  have hμnonneg : 0 ≤ μ := le_of_lt hμ
  have hmul : (μ⁻¹ * φ x) * μ = φ x := by
    have hμne : μ ≠ 0 := by linarith
    calc
      (μ⁻¹ * φ x) * μ = μ⁻¹ * (φ x * μ) := by
          simp [mul_assoc]
      _ = μ⁻¹ * (μ * φ x) := by
          simp [mul_comm]
      _ = (μ⁻¹ * μ) * φ x := by
          simp [mul_assoc]
      _ = φ x := by
          simp [inv_mul_cancel₀ hμne]
  have hmul' : (μ⁻¹ * φ x) * μ ≤ u * μ :=
    mul_le_mul_of_nonneg_right hφ' hμnonneg
  simpa [hmul, mul_comm, mul_left_comm, mul_assoc] using hmul'

/-- The `μ = 1` slice of a convex hull of epigraphs lies in the closure of the hull of slices. -/
lemma section16_slice_one_convexHull_union_epigraph_subset_closure_convexHull_sublevels
    {n : ℕ} {ι : Sort _} {g : ι → (Fin n → ℝ) → EReal}
    (hpos : ∀ i, PositivelyHomogeneous (g i))
    (hnonneg : ∀ i x, (0 : EReal) ≤ g i x) :
    {xStar : Fin n → ℝ |
      (xStar, (1 : ℝ)) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i))} ⊆
      closure
        (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) := by
  intro xStar hxStar
  classical
  rcases
      (mem_convexHull_union_epigraph_iff_fin_combo (f := g) (x := xStar) (μ := 1)).1
        hxStar with
    ⟨m, idx, lam, x', μ', hlam, hsum1, hsumx, hsumμ, hleμ⟩
  have hμnonneg : ∀ i, 0 ≤ μ' i := by
    intro i
    have h0le : (0 : EReal) ≤ g (idx i) (x' i) := hnonneg (idx i) (x' i)
    have hle : (0 : EReal) ≤ (μ' i : EReal) := le_trans h0le (hleμ i)
    exact (EReal.coe_le_coe_iff).1 hle
  let K : Set (Fin n → ℝ) :=
    convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})
  have hmemK : ∀ ε : ℝ, ε > 0 → ((1 + ε)⁻¹) • xStar ∈ K := by
    intro ε hε
    let μ'' : Fin m → ℝ := fun i => μ' i + ε
    have hμ''pos : ∀ i, 0 < μ'' i := by
      intro i
      have hμ' := hμnonneg i
      linarith
    let y : Fin m → (Fin n → ℝ) := fun i => (μ'' i)⁻¹ • x' i
    let w : Fin m → ℝ := fun i => (1 + ε)⁻¹ * (lam i * μ'' i)
    have hμ''le : ∀ i, (μ' i : EReal) ≤ (μ'' i : EReal) := by
      intro i
      exact (EReal.coe_le_coe_iff).2 (by linarith [hμnonneg i, hε])
    have hy : ∀ i, y i ∈ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}) := by
      intro i
      have hleμ'' : g (idx i) (x' i) ≤ (μ'' i : EReal) := le_trans (hleμ i) (hμ''le i)
      have hmem_epi :
          (x' i, μ'' i) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g (idx i)) := by
        simpa [mem_epigraph_univ_iff] using hleμ''
      have hmem_epi' :
          ((μ'' i)⁻¹ • x' i, (μ'' i)⁻¹ * μ'' i) ∈
            epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g (idx i)) := by
        exact
          section16_epigraph_univ_posHom_smul_mem (g := g (idx i)) (hpos (idx i))
            (x := x' i) (μ := μ'' i) (t := (μ'' i)⁻¹)
            (ht := inv_pos.mpr (hμ''pos i)) hmem_epi
      have hne : μ'' i ≠ 0 := ne_of_gt (hμ''pos i)
      have hle1 : g (idx i) (y i) ≤ (1 : EReal) := by
        have hle' :
            g (idx i) (y i) ≤ ((μ'' i)⁻¹ * μ'' i : EReal) := by
          simpa [y, mem_epigraph_univ_iff] using hmem_epi'
        have hmu : (μ'' i)⁻¹ * μ'' i = (1 : ℝ) := by
          simpa using (inv_mul_cancel₀ hne)
        have hmulE : (μ'' i : EReal)⁻¹ * (μ'' i : EReal) = (1 : EReal) := by
          calc
            (μ'' i : EReal)⁻¹ * (μ'' i : EReal) =
                ((μ'' i)⁻¹ : EReal) * (μ'' i : EReal) := by
                  simp
            _ = ((μ'' i)⁻¹ * μ'' i : ℝ) := by
                  exact (EReal.coe_mul (μ'' i)⁻¹ (μ'' i)).symm
            _ = (1 : EReal) := by
                  simp [hmu]
        calc
          g (idx i) (y i) ≤ (μ'' i : EReal)⁻¹ * (μ'' i : EReal) := by
            simpa using hle'
          _ = (1 : EReal) := hmulE
      exact Set.mem_iUnion.2 ⟨idx i, by simpa [y] using hle1⟩
    have hw0 : ∀ i, 0 ≤ w i := by
      intro i
      have h1 : 0 ≤ (1 + ε)⁻¹ := by
        exact le_of_lt (inv_pos.mpr (by linarith))
      have h2 : 0 ≤ lam i * μ'' i := mul_nonneg (hlam i) (le_of_lt (hμ''pos i))
      exact mul_nonneg h1 h2
    have hsumμ'' : Finset.univ.sum (fun i => lam i * μ'' i) = 1 + ε := by
      have hsumε :
          Finset.univ.sum (fun i => lam i * ε) =
            (Finset.univ.sum fun i => lam i) * ε := by
        simpa using (Finset.sum_mul (s := Finset.univ) (f := lam) (a := ε)).symm
      calc
        Finset.univ.sum (fun i => lam i * μ'' i) =
            Finset.univ.sum (fun i => lam i * μ' i + lam i * ε) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [μ'', mul_add]
        _ = Finset.univ.sum (fun i => lam i * μ' i) +
              Finset.univ.sum (fun i => lam i * ε) := by
              simp [Finset.sum_add_distrib]
        _ = 1 + ε := by
              calc
                Finset.univ.sum (fun i => lam i * μ' i) +
                    Finset.univ.sum (fun i => lam i * ε) =
                    1 + (Finset.univ.sum fun i => lam i) * ε := by
                      simp [hsumμ, hsumε]
                _ = 1 + ε := by simp [hsum1]
    have hsumw : (∑ i, w i) = 1 := by
      have hne : (1 + ε) ≠ 0 := by linarith
      calc
        (∑ i, w i) = (1 + ε)⁻¹ * ∑ i, lam i * μ'' i := by
          simpa [w, mul_comm, mul_left_comm, mul_assoc] using
            (Finset.mul_sum (a := (1 + ε)⁻¹) (f := fun i => lam i * μ'' i)
              (s := Finset.univ)).symm
        _ = (1 + ε)⁻¹ * (1 + ε) := by simp [hsumμ'']
        _ = 1 := by simp [hne]
    have hsumy : (∑ i, w i • y i) = ((1 + ε)⁻¹) • xStar := by
      have hμ''ne : ∀ i, μ'' i ≠ 0 := by
        intro i
        exact ne_of_gt (hμ''pos i)
      calc
        (∑ i, w i • y i) =
            ∑ i, (1 + ε)⁻¹ • (lam i • x' i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              have hne := hμ''ne i
              calc
                w i • y i =
                    ((1 + ε)⁻¹ * (lam i * μ'' i)) • ((μ'' i)⁻¹ • x' i) := by rfl
                _ = ((1 + ε)⁻¹ * lam i) • x' i := by
                      calc
                        ((1 + ε)⁻¹ * (lam i * μ'' i)) • ((μ'' i)⁻¹ • x' i) =
                            ((1 + ε)⁻¹ * (lam i * μ'' i) * (μ'' i)⁻¹) • x' i := by
                              simp [smul_smul, mul_assoc]
                        _ = ((1 + ε)⁻¹ * lam i) • x' i := by
                              simp [mul_assoc, mul_left_comm, mul_comm, hne]
                _ = (1 + ε)⁻¹ • (lam i • x' i) := by
                      simp [smul_smul]
        _ = (1 + ε)⁻¹ • ∑ i, lam i • x' i := by
            simpa using
              (Finset.smul_sum (s := Finset.univ) (r := (1 + ε)⁻¹)
                (f := fun i => lam i • x' i)).symm
        _ = (1 + ε)⁻¹ • xStar := by simp [hsumx]
    have hmem :
        ((1 + ε)⁻¹) • xStar ∈
          convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}) := by
      refine (mem_convexHull_iff_exists_fintype (R := ℝ)
        (s := ⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})
        (x := ((1 + ε)⁻¹) • xStar)).2 ?_
      refine ⟨Fin m, inferInstance, w, y, ?_, ?_, ?_, ?_⟩
      · intro i
        simpa using hw0 i
      · simpa using hsumw
      · intro i
        simpa using hy i
      · simpa using hsumy
    simpa [K] using hmem
  have hlim :
      Tendsto (fun ε : ℝ => ((1 + ε)⁻¹) • xStar) (𝓝[>] (0 : ℝ)) (𝓝 xStar) := by
    have hcont_add : ContinuousAt (fun ε : ℝ => (1 + ε)) 0 := by
      simpa using (continuousAt_const.add continuousAt_id)
    have hcont_inv' : ContinuousAt (fun t : ℝ => t⁻¹) ((1 : ℝ) + 0) := by
      simp
    have hcont_inv : ContinuousAt (fun ε : ℝ => (1 + ε)⁻¹) 0 :=
      hcont_inv'.comp hcont_add
    have hcont :
        ContinuousAt (fun ε : ℝ => ((1 + ε)⁻¹) • xStar) 0 :=
      hcont_inv.smul continuousAt_const
    have hlim0 :
        Tendsto (fun ε : ℝ => ((1 + ε)⁻¹) • xStar) (𝓝 (0 : ℝ)) (𝓝 xStar) := by
      simpa using hcont.tendsto
    exact hlim0.mono_left nhdsWithin_le_nhds
  have hmem_event :
      ∀ᶠ ε in (𝓝[>] (0 : ℝ)), ((1 + ε)⁻¹) • xStar ∈ K := by
    have hpos_event : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), ε ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    refine hpos_event.mono ?_
    intro ε hε
    have hε' : 0 < ε := by simpa using hε
    exact hmemK ε hε'
  have hxStar : xStar ∈ closure K := mem_closure_of_tendsto hlim hmem_event
  simpa [K] using hxStar

/-- Normalize a convex-hull epigraph point at height `1 + ε` to the level-1 sublevel hull,
landing in the closure. -/
lemma section16_mem_convexHull_iUnion_sublevels_one_of_mem_convexHull_union_epigraph_one_add_eps
    {n : ℕ} {ι : Sort _} {g : ι → (Fin n → ℝ) → EReal}
    (hpos : ∀ i, PositivelyHomogeneous (g i))
    (hnonneg : ∀ i x, (0 : EReal) ≤ g i x) {xStar : Fin n → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hmem :
      (xStar, 1 + ε) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i))) :
    ((1 + ε)⁻¹) • xStar ∈
      closure
        (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) := by
  have hpos_eps : 0 < 1 + ε := by linarith
  have ht : 0 < (1 + ε)⁻¹ := by
    simpa using (inv_pos.mpr hpos_eps)
  have hmem' :
      ((1 + ε)⁻¹ • xStar, (1 : ℝ)) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i)) := by
    have hmem'' :=
      section16_convexHull_union_epigraph_smul_mem (g := g) hpos (x := xStar) (μ := 1 + ε)
        (t := (1 + ε)⁻¹) ht hmem
    have hne : (1 + ε) ≠ 0 := by
      exact ne_of_gt hpos_eps
    have hmul : (1 + ε)⁻¹ * (1 + ε) = (1 : ℝ) := by
      simpa using (inv_mul_cancel₀ hne)
    simpa [hmul] using hmem''
  exact
    (section16_slice_one_convexHull_union_epigraph_subset_closure_convexHull_sublevels
      (g := g) hpos hnonneg) hmem'

end Section16
end Chap03
