/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part15

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology

section Chap02
section Section09

/-- The common recession function vanishes at the origin. -/
lemma k_zero_eq_zero {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {k : (Fin n → Real) → EReal}
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i))
    (hk :
      ∀ (i : Fin m) (y : Fin n → Real),
        k y = sSup { r : EReal | ∃ x : Fin n → Real, r = f i (x + y) - f i x })
    (hm : 0 < m) :
    k 0 = (0 : EReal) := by
  classical
  let i0 : Fin m := ⟨0, hm⟩
  rcases exists_point_ne_top_of_proper (hproper i0) with ⟨x0, hx0_top⟩
  have hx0_bot : f i0 x0 ≠ (⊥ : EReal) := (hproper i0).2.2 x0 (by simp)
  have hmem0 :
      (0 : EReal) ∈
        { r : EReal | ∃ x : Fin n → Real, r = f i0 (x + 0) - f i0 x } := by
    refine ⟨x0, ?_⟩
    have hsub' : f i0 x0 - f i0 x0 = 0 := EReal.sub_self hx0_top hx0_bot
    simpa using hsub'.symm
  have hsup_le :
      sSup { r : EReal | ∃ x : Fin n → Real, r = f i0 (x + 0) - f i0 x } ≤ (0 : EReal) := by
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, rfl⟩
    simpa using (EReal.sub_self_le_zero (x := f i0 x))
  have hsup_ge :
      (0 : EReal) ≤
        sSup { r : EReal | ∃ x : Fin n → Real, r = f i0 (x + 0) - f i0 x } :=
    le_sSup hmem0
  have hsup_eq :
      sSup { r : EReal | ∃ x : Fin n → Real, r = f i0 (x + 0) - f i0 x } = (0 : EReal) :=
    le_antisymm hsup_le hsup_ge
  simpa [hk i0 0] using hsup_eq

/-- The vertical direction `(0,1)` lies in the recession cone of the convex hull. -/
lemma zero_one_mem_recessionCone_convexHull_union_epigraph {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {k : (Fin n → Real) → EReal}
    (hclosed : ∀ i, ClosedConvexFunction (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i))
    (hk :
      ∀ (i : Fin m) (y : Fin n → Real),
        k y = sSup { r : EReal | ∃ x : Fin n → Real, r = f i (x + y) - f i x })
    (hm : 0 < m) :
    let C0 : Set ((Fin n → Real) × Real) :=
      convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i))
    (0, (1 : Real)) ∈ Set.recessionCone C0 := by
  classical
  intro C0
  have hC0 :
      IsClosed C0 ∧
        Set.recessionCone C0 = epigraph (Set.univ : Set (Fin n → Real)) k := by
    simpa [C0] using
      (convexHull_union_epigraph_closed_recession_prod (f := f) (k := k)
        (hclosed := hclosed) (hproper := hproper) hk hm)
  have hk0 : k 0 = (0 : EReal) := k_zero_eq_zero (hproper := hproper) (hk := hk) hm
  have hmem : (0, (1 : Real)) ∈ epigraph (Set.univ : Set (Fin n → Real)) k := by
    apply (mem_epigraph_univ_iff (f := k)).2
    have hle : (0 : EReal) ≤ (1 : EReal) := by
      exact (EReal.coe_le_coe_iff).2 (by norm_num)
    simp [hk0]
  simpa [hC0.2] using hmem

/-- The convex-hull epigraph is an actual epigraph for the convex-hull function family. -/
lemma epigraph_convexHullFunctionFamily_eq_convexHull {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hsubset :
      convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)) ⊆
        epigraph (Set.univ : Set (Fin n → Real)) (convexHullFunctionFamily f))
    (hclosed :
      IsClosed (convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i))))
    (hrec :
      (0, (1 : Real)) ∈
        Set.recessionCone
          (convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)))) :
    epigraph (Set.univ : Set (Fin n → Real)) (convexHullFunctionFamily f) =
      convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
  classical
  apply Set.Subset.antisymm
  · intro p hp
    rcases p with ⟨x, μ⟩
    let C0 : Set ((Fin n → Real) × Real) :=
      convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i))
    have hle :
        convexHullFunctionFamily f x ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := convexHullFunctionFamily f)).1 hp
    let Sx : Set ℝ := { μ : ℝ | (x, μ) ∈ C0 }
    have hEq :
        convexHullFunctionFamily f x =
          sInf ((fun μ : ℝ => (μ : EReal)) '' Sx) := by
      have hEq' :=
        congrArg (fun g => g x) (convexHullFunctionFamily_eq_inf_section_ereal (f := f))
      simpa [Sx, C0] using hEq'
    have hseq :
        ∀ k : ℕ, (x, μ + 1 / ((k : ℝ) + 1)) ∈ C0 := by
      intro k
      have hpos : 0 < (1 / ((k : ℝ) + 1)) := by
        have hden : 0 < (k : ℝ) + 1 := by nlinarith
        exact one_div_pos.2 hden
      have hμlt_real : μ < μ + 1 / ((k : ℝ) + 1) := by linarith
      have hμlt :
          (μ : EReal) < (μ + 1 / ((k : ℝ) + 1) : ℝ) :=
        (EReal.coe_lt_coe_iff).2 hμlt_real
      have hlt :
          convexHullFunctionFamily f x < (μ + 1 / ((k : ℝ) + 1) : ℝ) :=
        lt_of_le_of_lt hle hμlt
      have hlt' :
          sInf ((fun μ : ℝ => (μ : EReal)) '' Sx) <
            (μ + 1 / ((k : ℝ) + 1) : ℝ) := by
        simpa [hEq] using hlt
      rcases (sInf_lt_iff).1 hlt' with ⟨z, hz, hzlt⟩
      rcases hz with ⟨μ', hμ', rfl⟩
      have hμ'lt : μ' < μ + 1 / ((k : ℝ) + 1) :=
        (EReal.coe_lt_coe_iff).1 hzlt
      have hdiff_nonneg : 0 ≤ μ + 1 / ((k : ℝ) + 1) - μ' := by linarith
      have hmem' :
          (x, μ') + (μ + 1 / ((k : ℝ) + 1) - μ') • (0, (1 : Real)) ∈ C0 :=
        hrec hμ' (t := μ + 1 / ((k : ℝ) + 1) - μ') hdiff_nonneg
      simpa [C0, smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hmem'
    have htend :
        Filter.Tendsto (fun k : ℕ => (x, μ + 1 / ((k : ℝ) + 1))) Filter.atTop
          (𝓝 (x, μ)) := by
      refine (Prod.tendsto_iff
        (seq := fun k : ℕ => (x, μ + 1 / ((k : ℝ) + 1)))
        (p := (x, μ))).2 ?_
      constructor
      · exact
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (𝓝 x))
      · have hconst :
            Filter.Tendsto (fun _ : ℕ => μ) Filter.atTop (𝓝 μ) := tendsto_const_nhds
        have hdiv :
            Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
              Filter.atTop (𝓝 (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have hsum := hconst.add hdiv
        simpa [add_zero] using hsum
    have hmem :
        ∀ᶠ k : ℕ in Filter.atTop,
          (x, μ + 1 / ((k : ℝ) + 1)) ∈ C0 :=
      Filter.Eventually.of_forall hseq
    exact hclosed.mem_of_tendsto htend hmem
  · exact hsubset

/-- The convex-hull function family is never `⊥`. -/
lemma convexHullFunctionFamily_ne_bot {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {k : (Fin n → Real) → EReal}
    (hclosed : ∀ i, ClosedConvexFunction (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i))
    (hk :
      ∀ (i : Fin m) (y : Fin n → Real),
        k y = sSup { r : EReal | ∃ x : Fin n → Real, r = f i (x + y) - f i x })
    (hm : 0 < m) :
    let fconv : (Fin n → Real) → EReal := convexHullFunctionFamily f
    ∀ x : Fin n → Real, fconv x ≠ (⊥ : EReal) := by
  classical
  intro fconv x
  by_contra hbot
  let C0 : Set ((Fin n → Real) × Real) :=
    convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i))
  have hC :
      ∀ i,
        Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) ∧
          IsClosed (epigraph (Set.univ : Set (Fin n → Real)) (f i)) ∧
          Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f i)) :=
    epigraph_family_closed_convex_nonempty (hclosed := hclosed) (hproper := hproper)
  have hC0 :
      IsClosed C0 ∧
        Set.recessionCone C0 = epigraph (Set.univ : Set (Fin n → Real)) k := by
    simpa [C0] using
      (convexHull_union_epigraph_closed_recession_prod (f := f) (k := k)
        (hclosed := hclosed) (hproper := hproper) hk hm)
  have hrec_dir :
      (0, (1 : Real)) ∈ Set.recessionCone C0 := by
    simpa [C0] using
      (zero_one_mem_recessionCone_convexHull_union_epigraph (f := f) (k := k)
        (hclosed := hclosed) (hproper := hproper) hk hm)
  have hgreat :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) fconv ∧
        (∀ i, fconv ≤ f i) ∧
        ∀ h : (Fin n → Real) → EReal,
          ConvexFunctionOn (Set.univ : Set (Fin n → Real)) h →
          (∀ i, h ≤ f i) → h ≤ fconv := by
    simpa [fconv] using (convexHullFunctionFamily_greatest_convex_minorant (f := f))
  have hsubset :
      C0 ⊆ epigraph (Set.univ : Set (Fin n → Real)) fconv := by
    simpa [C0] using
      (convexHull_union_epigraph_subset_epigraph_of_minorant (f := f) (h := fconv)
        hgreat.1 hgreat.2.1)
  have hEq :
      epigraph (Set.univ : Set (Fin n → Real)) fconv = C0 :=
    epigraph_convexHullFunctionFamily_eq_convexHull hsubset hC0.1 hrec_dir
  have hline :
      ∀ t : Real, 0 ≤ t → (x, 0) + t • (0, (-1 : Real)) ∈ C0 := by
    intro t ht
    have hmem_epi :
        (x, -t) ∈ epigraph (Set.univ : Set (Fin n → Real)) fconv := by
      apply (mem_epigraph_univ_iff (f := fconv)).2
      have hle : (⊥ : EReal) ≤ (-t : Real) := bot_le
      simp [hbot]
    have hmem_C0 : (x, -t) ∈ C0 := by
      simpa [hEq] using hmem_epi
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hmem_C0
  let e := prodLinearEquiv_append (n := n)
  let Cemb : Set (EuclideanSpace Real (Fin (n + 1))) := e '' C0
  have hC0ne : Set.Nonempty C0 := by
    let i0 : Fin m := ⟨0, hm⟩
    rcases (hC i0).1 with ⟨p, hp⟩
    have hne_union : (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)).Nonempty := by
      refine ⟨p, ?_⟩
      exact Set.mem_iUnion.mpr ⟨i0, hp⟩
    simpa [C0] using (hne_union.convexHull (𝕜 := Real))
  have hCemb_ne : Set.Nonempty Cemb := hC0ne.image e
  have hCemb_closed : IsClosed Cemb := by
    let hhome := (e.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hclosed' : IsClosed ((hhome : _ → _) '' C0) :=
      (hhome.isClosed_image (s := C0)).2 hC0.1
    simpa [Cemb, hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  have hCemb_conv : Convex Real Cemb := by
    have hC0conv : Convex Real C0 := by
      simpa [C0] using (convex_convexHull (𝕜 := Real)
        (s := ⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)))
    simpa [Cemb] using hC0conv.linear_image e.toLinearMap
  have hline_emb :
      ∀ t : Real, 0 ≤ t → e (x, 0) + t • e (0, (-1 : Real)) ∈ Cemb := by
    intro t ht
    have hmem : (x, 0) + t • (0, (-1 : Real)) ∈ C0 := hline t ht
    refine ⟨(x, 0) + t • (0, (-1 : Real)), hmem, ?_⟩
    have hmap :
        e ((x, 0) + t • (0, (-1 : Real))) =
          e (x, 0) + t • e (0, (-1 : Real)) := by
      calc
        e ((x, 0) + t • (0, (-1 : Real))) =
            e (x, 0) + e (t • (0, (-1 : Real))) := by
          exact e.map_add (x, 0) (t • (0, (-1 : Real)))
        _ = e (x, 0) + t • e (0, (-1 : Real)) := by
          simpa using congrArg (fun v => e (x, 0) + v) (e.map_smul t (0, (-1 : Real)))
    exact hmap
  have hrec_emb : e (0, (-1 : Real)) ∈ Set.recessionCone Cemb :=
    halfline_mem_recessionCone (C := Cemb) hCemb_ne hCemb_closed hCemb_conv hline_emb
  have hrec0 : (0, (-1 : Real)) ∈ Set.recessionCone C0 := by
    have hrec_image :
        Set.recessionCone Cemb = e '' Set.recessionCone C0 := by
      simpa [Cemb] using (recessionCone_image_linearEquiv (e := e) (C := C0))
    have hrec_emb' : e (0, (-1 : Real)) ∈ e '' Set.recessionCone C0 := by
      simpa [hrec_image] using hrec_emb
    rcases hrec_emb' with ⟨v, hv, hv_eq⟩
    have hv' : v = (0, (-1 : Real)) := by
      apply e.injective
      simp [hv_eq]
    simpa [hv'] using hv
  have hmem_k :
      (0, (-1 : Real)) ∈ epigraph (Set.univ : Set (Fin n → Real)) k := by
    simpa [hC0.2] using hrec0
  have hle_k : k 0 ≤ (-1 : EReal) :=
    (mem_epigraph_univ_iff (f := k)).1 hmem_k
  have hk0 : k 0 = (0 : EReal) := k_zero_eq_zero (hproper := hproper) (hk := hk) hm
  have hle_real : (0 : Real) ≤ (-1 : Real) := by
    have hle' : (0 : EReal) ≤ (-1 : EReal) := by simpa [hk0] using hle_k
    exact (EReal.coe_le_coe_iff).1 hle'
  linarith

/-- Corollary 9.8.3 9.8.3.1. Let `f₁, …, fₘ` be closed proper convex functions on `ℝ^n`
all having the same recession function `k`. Then `f = conv {f₁, …, fₘ}` is closed and
proper and likewise has `k` as its recession function. In the formula for `f(x)` in
Theorem 5.6, the infimum is attained for each `x` by some convex combination. -/
theorem convexHullFunctionFamily_closed_proper_recession_and_attained {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {k : (Fin n → Real) → EReal}
    (hclosed : ∀ i, ClosedConvexFunction (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i))
    (hk :
      ∀ (i : Fin m) (y : Fin n → Real),
        k y = sSup { r : EReal | ∃ x : Fin n → Real, r = f i (x + y) - f i x })
    (hm : 0 < m) :
    let fconv : (Fin n → Real) → EReal := convexHullFunctionFamily f
    ClosedConvexFunction fconv ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fconv ∧
      (∀ y : Fin n → Real,
        k y =
          sSup { r : EReal | ∃ x : Fin n → Real, r = fconv (x + y) - fconv x }) ∧
      (∀ x : Fin n → Real,
        ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
          (∀ i, 0 ≤ lam i) ∧
          (Finset.univ.sum (fun i => lam i) = 1) ∧
          (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
          fconv x =
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i))) := by
  classical
  intro fconv
  have hgreat :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) fconv ∧
        (∀ i, fconv ≤ f i) ∧
        ∀ h : (Fin n → Real) → EReal,
          ConvexFunctionOn (Set.univ : Set (Fin n → Real)) h →
          (∀ i, h ≤ f i) → h ≤ fconv := by
    simpa [fconv] using (convexHullFunctionFamily_greatest_convex_minorant (f := f))
  have hconv : ConvexFunction fconv := by
    simpa [ConvexFunction] using hgreat.1
  have hC :
      ∀ i,
        Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) ∧
          IsClosed (epigraph (Set.univ : Set (Fin n → Real)) (f i)) ∧
          Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f i)) :=
    epigraph_family_closed_convex_nonempty (hclosed := hclosed) (hproper := hproper)
  let C0 : Set ((Fin n → Real) × Real) :=
    convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i))
  have hsubset_epi : C0 ⊆ epigraph (Set.univ : Set (Fin n → Real)) fconv := by
    simpa [C0] using
      (convexHull_union_epigraph_subset_epigraph_of_minorant (f := f) (h := fconv)
        hgreat.1 hgreat.2.1)
  have hformula :
      ∀ x : Fin n → Real,
        fconv x =
          sInf { z : EReal |
            ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
              (∀ i, 0 ≤ lam i) ∧
              (Finset.univ.sum (fun i => lam i) = 1) ∧
              (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
              z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) } := by
    simpa [fconv] using
      (convexHullFunctionFamily_eq_sInf_convexCombination_univ (f := f) hproper)
  have hC0_closed_recession :
      IsClosed C0 ∧
        Set.recessionCone C0 = epigraph (Set.univ : Set (Fin n → Real)) k := by
    simpa [C0] using
      (convexHull_union_epigraph_closed_recession_prod (f := f) (k := k)
        (hclosed := hclosed) (hproper := hproper) hk hm)
  have hrec_dir :
      (0, (1 : Real)) ∈ Set.recessionCone C0 := by
    simpa [C0] using
      (zero_one_mem_recessionCone_convexHull_union_epigraph (f := f) (k := k)
        (hclosed := hclosed) (hproper := hproper) hk hm)
  have hEq_epi :
      epigraph (Set.univ : Set (Fin n → Real)) fconv = C0 :=
    epigraph_convexHullFunctionFamily_eq_convexHull hsubset_epi hC0_closed_recession.1 hrec_dir
  refine And.intro ?_ ?_
  · refine ⟨hconv, ?_⟩
    -- lower semicontinuity of `fconv` will follow from closedness of its epigraph
    -- identified with the convex hull of the epigraph family.
    have hclosed_epi :
        IsClosed (epigraph (Set.univ : Set (Fin n → Real)) fconv) := by
      simpa [hEq_epi] using hC0_closed_recession.1
    have hsub :
        ∀ α : Real, IsClosed {x | fconv x ≤ (α : EReal)} := by
      exact
        (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := fconv)).2.2
          hclosed_epi
    have hls : LowerSemicontinuous fconv :=
      (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := fconv)).1.2 hsub
    exact hls
  · -- properness, recession formula, and attainment use the closed convex hull
    -- of the epigraphs and the sInf/convex-combination formula.
    have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) fconv := by
      simpa [ConvexFunction] using hconv
    have hC0ne : Set.Nonempty C0 := by
      let i0 : Fin m := ⟨0, hm⟩
      rcases (hC i0).1 with ⟨p, hp⟩
      have hne_union :
          (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)).Nonempty := by
        refine ⟨p, ?_⟩
        exact Set.mem_iUnion.mpr ⟨i0, hp⟩
      simpa [C0] using (hne_union.convexHull (𝕜 := Real))
    have hne_epi : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) fconv) := by
      simpa [hEq_epi] using hC0ne
    have hnotbot : ∀ x : Fin n → Real, fconv x ≠ (⊥ : EReal) := by
      simpa [fconv] using
        (convexHullFunctionFamily_ne_bot (f := f) (k := k) hclosed hproper hk hm)
    have hproper_fconv :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fconv := by
      refine ⟨hconv_on, hne_epi, ?_⟩
      intro x hx
      exact hnotbot x
    have hrec_fconv :
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) fconv) =
          epigraph (Set.univ : Set (Fin n → Real)) k := by
      simpa [hEq_epi] using hC0_closed_recession.2
    let k' : (Fin n → Real) → EReal :=
      fun y =>
        sSup { r : EReal | ∃ x : Fin n → Real, r = fconv (x + y) - fconv x }
    have hrec_k' :
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) fconv) =
          epigraph (Set.univ : Set (Fin n → Real)) k' := by
      let f' : Fin 1 → (Fin n → Real) → EReal := fun _ => fconv
      have hconv' :
          ∀ i, Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f' i)) := by
        intro i
        have hconv_on' : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) fconv := by
          simpa [ConvexFunction] using hconv
        simpa [f'] using (convex_epigraph_of_convexFunctionOn (f := fconv) (hf := hconv_on'))
      have hproper' :
          ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f' i) := by
        intro i
        simpa [f'] using hproper_fconv
      have hk' :
          ∀ (i : Fin 1) (y : Fin n → Real),
            k' y = sSup { r : EReal | ∃ x : Fin n → Real, r = f' i (x + y) - f' i x } := by
        intro i y
        rfl
      have hrec' :=
        (recessionCone_epigraph_eq_epigraph_k (f := f') (k := k')
          (hconv := hconv') (hproper := hproper') hk') (0 : Fin 1)
      simpa [f'] using hrec'
    have hEq_k :
        epigraph (Set.univ : Set (Fin n → Real)) k =
          epigraph (Set.univ : Set (Fin n → Real)) k' := by
      exact hrec_fconv.symm.trans hrec_k'
    have hsubset_k' :
        epigraph (Set.univ : Set (Fin n → Real)) k' ⊆
          epigraph (Set.univ : Set (Fin n → Real)) k := by
      intro p hp
      simpa [hEq_k] using hp
    have hsubset_k :
        epigraph (Set.univ : Set (Fin n → Real)) k ⊆
          epigraph (Set.univ : Set (Fin n → Real)) k' := by
      intro p hp
      simpa [hEq_k] using hp
    have hinf_k' :
        (fun y => sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
          (y, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) k' })) = k' := by
      apply le_antisymm
      · exact
          le_of_epigraph_subset_inf_section (h := k')
            (F := epigraph (Set.univ : Set (Fin n → Real)) k') (by intro p hp; exact hp)
      · exact
          le_inf_section_of_subset_epigraph (h := k')
            (F := epigraph (Set.univ : Set (Fin n → Real)) k') (by intro p hp; exact hp)
    have hinf_k :
        (fun y => sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
          (y, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) k })) = k := by
      apply le_antisymm
      · exact
          le_of_epigraph_subset_inf_section (h := k)
            (F := epigraph (Set.univ : Set (Fin n → Real)) k) (by intro p hp; exact hp)
      · exact
          le_inf_section_of_subset_epigraph (h := k)
            (F := epigraph (Set.univ : Set (Fin n → Real)) k) (by intro p hp; exact hp)
    have hk_le : k ≤ k' := by
      have hle_inf :
          k ≤ fun y => sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
            (y, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) k' }) :=
        le_inf_section_of_subset_epigraph (h := k)
          (F := epigraph (Set.univ : Set (Fin n → Real)) k') hsubset_k'
      simpa [hinf_k'] using hle_inf
    have hk_ge : k' ≤ k := by
      have hle_inf :
          k' ≤ fun y => sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
            (y, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) k }) :=
        le_inf_section_of_subset_epigraph (h := k')
          (F := epigraph (Set.univ : Set (Fin n → Real)) k) hsubset_k
      simpa [hinf_k] using hle_inf
    have hk_eq : k = k' := funext (fun y => le_antisymm (hk_le y) (hk_ge y))
    have hk_formula :
        ∀ y : Fin n → Real,
          k y =
            sSup { r : EReal | ∃ x : Fin n → Real, r = fconv (x + y) - fconv x } := by
      intro y
      simp [k', hk_eq]
    have hattain :
        ∀ x : Fin n → Real,
          ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = 1) ∧
            (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
            fconv x =
              Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
      intro x
      by_cases htop : fconv x = ⊤
      · let i0 : Fin m := ⟨0, hm⟩
        refine ⟨fun i => if i = i0 then 1 else 0, fun _ => x, ?_, ?_, ?_, ?_⟩
        · intro i
          by_cases h : i = i0 <;> simp [h]
        · classical
          simp [i0]
        · classical
          simp [i0]
        · have hle : fconv x ≤ f i0 x := hgreat.2.1 i0 x
          have hfi_top : f i0 x = ⊤ := top_unique (by simpa [htop] using hle)
          classical
          have hsum :
              Finset.univ.sum (fun i =>
                ((if i = i0 then 1 else 0 : Real) : EReal) * f i x) = f i0 x := by
            have hsum' :
                Finset.univ.sum (fun i =>
                  ((if i = i0 then 1 else 0 : Real) : EReal) * f i x) =
                  ((if i0 = i0 then 1 else 0 : Real) : EReal) * f i0 x := by
              refine Finset.sum_eq_single (s := Finset.univ) (a := i0)
                (f := fun i : Fin m =>
                  ((if i = i0 then 1 else 0 : Real) : EReal) * f i x) ?_ ?_
              · intro i hi hne
                simp [hne]
              · simp
            simpa using hsum'
          have hsum' : (⊤ : EReal) =
              Finset.univ.sum (fun i =>
                ((if i = i0 then 1 else 0 : Real) : EReal) * f i x) := by
            have hsum'' :
                Finset.univ.sum (fun i =>
                  ((if i = i0 then 1 else 0 : Real) : EReal) * f i x) = (⊤ : EReal) := by
              simpa [hfi_top] using hsum
            exact hsum''.symm
          simpa [htop] using hsum'
      · have hnotbot : fconv x ≠ (⊥ : EReal) := hnotbot x
        set μ : ℝ := (fconv x).toReal
        have hμ : (μ : EReal) = fconv x := by
          simpa [μ] using (EReal.coe_toReal htop hnotbot)
        have hmem_epi :
            (x, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) fconv := by
          apply (mem_epigraph_univ_iff (f := fconv)).2
          have hle : fconv x ≤ (μ : EReal) := by
            simp [hμ]
          exact hle
        have hmem_C0 : (x, μ) ∈ C0 := by
          simpa [hEq_epi] using hmem_epi
        rcases
            (mem_convexHull_union_epigraph_iff_fin_combo (f := f) (x := x) (μ := μ)).1
              hmem_C0 with
          ⟨m', idx, lam, x', μ', h0, hsum1, hsumx, hsumμ, hle⟩
        rcases merge_epigraph_combo_finset (f := f) (hf := hproper) (idx := idx)
            (lam := lam) (x' := x') (μ' := μ') h0 hsum1 hsumx hsumμ hle with
          ⟨s, lam', x'', μ'', h0', hsupport, hsum1', hsumx', hsumμ', hle'⟩
        have hsum1_univ : Finset.univ.sum (fun i => lam' i) = 1 := by
          classical
          have hsum1'' :
              Finset.univ.sum (fun i => lam' i) = s.sum (fun i => lam' i) := by
            have hsum1''' :
                s.sum (fun i => lam' i) = Finset.univ.sum (fun i => lam' i) := by
              refine Finset.sum_subset (s₁ := s) (s₂ := Finset.univ) ?_ ?_
              · intro i hi
                exact Finset.mem_univ i
              · intro i hi hnot
                exact hsupport i hnot
            exact hsum1'''.symm
          simpa [hsum1''] using hsum1'
        have hsumx_univ :
            Finset.univ.sum (fun i => lam' i • x'' i) = x := by
          classical
          have hsumx'' :
              Finset.univ.sum (fun i => lam' i • x'' i) =
                s.sum (fun i => lam' i • x'' i) := by
            have hsumx''' :
                s.sum (fun i => lam' i • x'' i) =
                  Finset.univ.sum (fun i => lam' i • x'' i) := by
              refine Finset.sum_subset (s₁ := s) (s₂ := Finset.univ) ?_ ?_
              · intro i hi
                exact Finset.mem_univ i
              · intro i hi hnot
                simp [hsupport i hnot]
            exact hsumx'''.symm
          simpa [hsumx''] using hsumx'
        have hsumμ_univ :
            Finset.univ.sum (fun i => lam' i * μ'' i) = μ := by
          classical
          have hsumμ'' :
              Finset.univ.sum (fun i => lam' i * μ'' i) =
                s.sum (fun i => lam' i * μ'' i) := by
            have hsumμ''' :
                s.sum (fun i => lam' i * μ'' i) =
                  Finset.univ.sum (fun i => lam' i * μ'' i) := by
              refine Finset.sum_subset (s₁ := s) (s₂ := Finset.univ) ?_ ?_
              · intro i hi
                exact Finset.mem_univ i
              · intro i hi hnot
                simp [hsupport i hnot]
            exact hsumμ'''.symm
          simpa [hsumμ''] using hsumμ'
        have hmemB :
            Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * f i (x'' i)) ∈
              { z : EReal |
                ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
                  (∀ i, 0 ≤ lam i) ∧
                  (Finset.univ.sum (fun i => lam i) = 1) ∧
                  (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
                  z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) } := by
          exact ⟨lam', x'', h0', hsum1_univ, hsumx_univ, rfl⟩
        have hle_fconv :
            fconv x ≤
              Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * f i (x'' i)) := by
          have hle := sInf_le hmemB
          have hformula_x := hformula x
          simpa [hformula_x] using hle
        have hsum_le :
            Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * f i (x'' i)) ≤
              Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) := by
          classical
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcoeff : (0 : EReal) ≤ ((lam' i : Real) : EReal) := by
            exact (EReal.coe_le_coe_iff).2 (h0' i)
          exact mul_le_mul_of_nonneg_left (hle' i) hcoeff
        have hsumμ_univ' :
            Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) =
              (μ : EReal) := by
          have hsumμ_univ_coe' :
              Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * (μ'' i : EReal)) =
                ((Finset.univ.sum (fun i => lam' i * μ'' i) : Real) : EReal) := by
            classical
            refine Finset.induction_on (s := (Finset.univ : Finset (Fin m))) ?h0 ?hstep
            · simp
            · intro a s ha hs
              simp [Finset.sum_insert, ha, EReal.coe_add, EReal.coe_mul]
              rw [hs]
          have hsumμ_univ_coe :
              ((Finset.univ.sum (fun i => lam' i * μ'' i) : Real) : EReal) = (μ : EReal) := by
            exact congrArg (fun r : Real => (r : EReal)) hsumμ_univ
          exact hsumμ_univ_coe'.trans hsumμ_univ_coe
        have hle_sum :
            Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * f i (x'' i)) ≤ (μ : EReal) := by
          simpa [hsumμ_univ'] using hsum_le
        have hsum_eq :
            fconv x =
              Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * f i (x'' i)) := by
          have hle' : Finset.univ.sum (fun i => ((lam' i : Real) : EReal) * f i (x'' i)) ≤
              fconv x := by
            simpa [hμ] using hle_sum
          exact le_antisymm hle_fconv hle'
        exact ⟨lam', x'', h0', hsum1_univ, hsumx_univ, hsum_eq⟩
    exact ⟨hproper_fconv, hk_formula, hattain⟩

end Section09
end Chap02
