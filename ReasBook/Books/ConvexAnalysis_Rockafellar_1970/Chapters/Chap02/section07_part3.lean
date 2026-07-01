/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part2

noncomputable section
open scoped Topology

section Chap02
section Section07

/-- An improper convex function with nonempty effective domain attains `⊥` there. -/
lemma improperConvexFunctionOn_exists_bot_of_effectiveDomain_nonempty {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hne : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∃ u ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, f u = (⊥ : EReal) := by
  rcases
      improperConvexFunctionOn_cases_epigraph_empty_or_bot
        (S := (Set.univ : Set (Fin n → Real))) (f := f) hf with
    hcase | hcase
  · have hne_epi :
        Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f) :=
      (nonempty_epigraph_iff_nonempty_effectiveDomain
            (S := (Set.univ : Set (Fin n → Real))) (f := f)).2 hne
    exact (hcase hne_epi).elim
  · rcases hcase with ⟨u, huS, hubot⟩
    have hu_dom :
        u ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      have hlt : f u < (⊤ : EReal) := by
        simp [hubot]
      have hu' :
          u ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} :=
        ⟨by simp [huS], hlt⟩
      simpa [effectiveDomain_eq] using hu'
    exact ⟨u, hu_dom, hubot⟩

/-- Inverting an affine combination on a line. -/
lemma affine_combo_inverse {n : Nat} {u x y : EuclideanSpace Real (Fin n)} {μ : Real}
    (hμ : μ ≠ 0)
    (hy : y = (1 - μ) • u + μ • x) :
    x = (1 - μ⁻¹) • u + μ⁻¹ • y := by
  have hy' : y = AffineMap.lineMap u x μ := by
    simpa [AffineMap.lineMap_apply_module] using hy
  have hx' : AffineMap.lineMap u y μ⁻¹ = x := by
    simp [hy', hμ]
  calc
    x = AffineMap.lineMap u y μ⁻¹ := by simpa using hx'.symm
    _ = (1 - μ⁻¹) • u + μ⁻¹ • y := by
      simp [AffineMap.lineMap_apply_module]

/-- A convex combination with a `⊥` point is `⊥` when the other point is finite. -/
lemma convex_combo_eq_bot_of_bot_point {n : Nat} {f : (Fin n → Real) → EReal}
    (hconv : ConvexFunctionOn (Set.univ) f) {u y x : EuclideanSpace Real (Fin n)}
    (hu : f u = (⊥ : EReal)) (hy : f y < (⊤ : EReal)) {lam : Real}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hx : x = (1 - lam) • u + lam • y) :
    f x = (⊥ : EReal) := by
  refine (EReal.eq_bot_iff_forall_lt (x := f x)).2 ?_
  intro r
  rcases EReal.exists_between_coe_real hy with ⟨β, hfyβ, -⟩
  let α : Real := (r - lam * β) / (1 - lam)
  have hfuα : f u < (α : EReal) := by
    simp [hu]
  have hstrict :=
    (convexFunctionOn_univ_iff_strict_inequality (f := f)).1 hconv u y α β lam
      hfuα hfyβ hlam0 hlam1
  have hcoeff_real : (1 - lam) * α + lam * β = r := by
    have hne : (1 - lam) ≠ 0 := by linarith
    calc
      (1 - lam) * α + lam * β =
          (1 - lam) * ((r - lam * β) / (1 - lam)) + lam * β := by rfl
      _ = (r - lam * β) + lam * β := by
        field_simp [hne]
      _ = r := by ring
  have hcoeff :
      ((1 - lam : Real) : EReal) * (α : EReal) +
          ((lam : Real) : EReal) * (β : EReal) = (r : EReal) := by
    calc
      ((1 - lam : Real) : EReal) * (α : EReal) +
            ((lam : Real) : EReal) * (β : EReal) =
          (((1 - lam) * α + lam * β : Real) : EReal) := by
        simp [EReal.coe_mul, EReal.coe_add, add_comm]
      _ = (r : EReal) := by simp [hcoeff_real]
  have hstrict' :
      f x <
        ((1 - lam : Real) : EReal) * (α : EReal) + ((lam : Real) : EReal) * (β : EReal) := by
    simpa [hx] using hstrict
  exact lt_of_lt_of_eq hstrict' hcoeff

/-- Theorem 7.2: If `f` is an improper convex function, then `f x = -∞` for every
`x ∈ ri (dom f)`. Thus an improper convex function is necessarily infinite except perhaps
at relative boundary points of its effective domain. -/
theorem improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      f x = (⊥ : EReal) := by
  intro x hxri
  set C :
      Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hxC : x ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hxri
  have hne_dom : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    refine ⟨(x : Fin n → Real), ?_⟩
    simpa [C] using hxC
  rcases
      improperConvexFunctionOn_exists_bot_of_effectiveDomain_nonempty
        (f := f) hf hne_dom with
    ⟨u0, hu0_dom, hu0_bot⟩
  let u : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm u0
  have huC : u ∈ C := by
    have hu' : (u : Fin n → Real) ∈
        effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      simpa [u] using hu0_dom
    simpa [C] using hu'
  have hu_bot : f u = (⊥ : EReal) := by
    simpa [u] using hu0_bot
  have hCconv : Convex Real C := by
    have hconv_dom :
        Convex Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1
    simpa [C] using
      (Convex.linear_preimage (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f)
        hconv_dom (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap)
  have hCne : C.Nonempty := ⟨x, hxC⟩
  have h_ext :=
    (euclideanRelativeInterior_iff_forall_exists_affine_combination_mem n C hCconv hCne
          x).1 hxri
  rcases h_ext u huC with ⟨μ, hμ1, hyC⟩
  set y : EuclideanSpace Real (Fin n) := (1 - μ) • u + μ • x
  have hy_dom : (y : Fin n → Real) ∈
      effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    have hyC' : y ∈ C := by
      simpa [y] using hyC
    simpa [C] using hyC'
  have hy_lt_top : f y < (⊤ : EReal) := by
    have hy' :
        (y : Fin n → Real) ∈
          {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
      simpa [effectiveDomain_eq] using hy_dom
    simpa using hy'.2
  have hμpos : 0 < μ := by linarith
  have hμne : μ ≠ 0 := ne_of_gt hμpos
  have hx_eq : x = (1 - μ⁻¹) • u + μ⁻¹ • y := by
    have hy_def : y = (1 - μ) • u + μ • x := by rfl
    exact affine_combo_inverse (u := u) (x := x) (y := y) hμne hy_def
  have hmuinv0 : 0 < μ⁻¹ := inv_pos.mpr hμpos
  have hmuinv1 : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ1
  exact
    convex_combo_eq_bot_of_bot_point (f := f) hf.1 (u := u) (y := y) (x := x) hu_bot
      hy_lt_top hmuinv0 hmuinv1 hx_eq

/-- Lower semicontinuity implies the `⊥`-sublevel set is closed. -/
lemma lsc_isClosed_sublevel_bot {n : Nat} {f : (Fin n → Real) → EReal}
    (hls : LowerSemicontinuous f) :
    IsClosed {x | f x ≤ (⊥ : EReal)} := by
  have hclosed : ∀ α : Real, IsClosed {x | f x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hls
  exact isClosed_sublevel_bot_of_closed_sublevels (f := f) hclosed

/-- Lower semicontinuity extends `f = ⊥` from `ri (dom f)` to its closure. -/
lemma improperConvexFunctionOn_eq_bot_on_closure_ri_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hls : LowerSemicontinuous f)
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ x ∈
      closure
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f)),
      f x = (⊥ : EReal) := by
  intro x hx
  set C :
      Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f
  set D : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      {x | f x ≤ (⊥ : EReal)}
  have hclosed : IsClosed D := by
    have hclosed' : IsClosed {x | f x ≤ (⊥ : EReal)} :=
      lsc_isClosed_sublevel_bot (f := f) hls
    have hcont :
        Continuous (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) := by
      simpa using (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).continuous
    simpa [D] using hclosed'.preimage hcont
  have hsubset : euclideanRelativeInterior n C ⊆ D := by
    intro y hy
    have hybot :=
      improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) hf y hy
    simp [D, hybot]
  have hxmem : x ∈ D := (closure_minimal hsubset hclosed) (by simpa [C] using hx)
  have hx_le : f x ≤ (⊥ : EReal) := by
    simpa [D] using hxmem
  exact le_antisymm hx_le bot_le

/-- Points of the effective domain lie in the closure of its relative interior. -/
lemma mem_closure_ri_effectiveDomain_of_mem {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) ∈
      closure
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
  set C :
      Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f
  set x' : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
  have hCconv : Convex Real C := by
    have hconv_dom :
        Convex Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1
    simpa [C] using
      (Convex.linear_preimage (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f)
        hconv_dom (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap)
  have hcl_eq :
      closure (euclideanRelativeInterior n C) = closure C :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C hCconv).1
  have hxC : x' ∈ C := by
    simpa [C, x'] using hx
  have hx_closure : x' ∈ closure C :=
    subset_closure hxC
  simpa [C, hcl_eq, x'] using hx_closure

/-- Corollary 7.2.1. A lower semi-continuous improper convex function can have no finite
values. -/
theorem lowerSemicontinuous_improperConvexFunction_no_finite_values {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hls : LowerSemicontinuous f) :
    ∀ x, f x = (⊤ : EReal) ∨ f x = (⊥ : EReal) := by
  show ∀ x, f x = (⊤ : EReal) ∨ f x = (⊥ : EReal)
  intro x
  by_cases htop : f x = (⊤ : EReal)
  · exact Or.inl htop
  · have hx_lt_top : f x < (⊤ : EReal) := by
      exact (lt_top_iff_ne_top).2 htop
    have hx_dom : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      have hx' :
          x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} :=
        ⟨by simp, hx_lt_top⟩
      simpa [effectiveDomain_eq] using hx'
    set x' : EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
    have hx_closure :
        x' ∈
          closure
            (euclideanRelativeInterior n
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :=
      by
        simpa [x'] using
          (mem_closure_ri_effectiveDomain_of_mem (f := f) hf hx_dom)
    have hx_bot :
        f x = (⊥ : EReal) := by
      simpa [x'] using
        (improperConvexFunctionOn_eq_bot_on_closure_ri_effectiveDomain
            (f := f) hls hf x' hx_closure)
    exact Or.inr hx_bot

/-- Corollary 7.2.2. Let `f` be an improper convex function. Then `cl f` is a closed
improper convex function and agrees with `f` on `ri (dom f)`. -/
theorem convexFunctionClosure_closed_improperConvexFunctionOn_and_agrees_on_ri
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (ClosedConvexFunction (convexFunctionClosure f) ∧
        ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (convexFunctionClosure f)) ∧
      ∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        convexFunctionClosure f x = f x := by
  classical
  by_cases hbot : ∃ x, f x = (⊥ : EReal)
  · have hcl : convexFunctionClosure f = (fun _ => (⊥ : EReal)) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := f) hbot
    have hclosed_improper :
        ClosedConvexFunction (convexFunctionClosure f) ∧
          ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real))
            (convexFunctionClosure f) := by
      simpa [hcl] using (closed_improper_const_bot (n := n))
    refine ⟨hclosed_improper, ?_⟩
    intro x hx
    have hx_bot :
        f x = (⊥ : EReal) :=
      improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) hf x hx
    simp [hcl, hx_bot]
  · have hcase :=
      improperConvexFunctionOn_cases_epigraph_empty_or_bot
        (S := (Set.univ : Set (Fin n → Real))) (f := f) hf
    have hne : ¬ Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f) := by
      rcases hcase with hcase | hcase
      · exact hcase
      · rcases hcase with ⟨x, -, hxbot⟩
        exact (hbot ⟨x, hxbot⟩).elim
    have htop : f = (fun _ => (⊤ : EReal)) := by
      funext x
      have hx : x ∈ (Set.univ : Set (Fin n → Real)) := by simp
      exact
        epigraph_empty_imp_forall_top (S := (Set.univ : Set (Fin n → Real))) (f := f)
          hne x hx
    have hcl :
        convexFunctionClosure f = (fun _ => (⊤ : EReal)) := by
      simpa [htop] using (convexFunctionClosure_const_top (n := n))
    have hclosed_improper :
        ClosedConvexFunction (convexFunctionClosure f) ∧
          ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real))
            (convexFunctionClosure f) := by
      simpa [hcl] using (closed_improper_const_top (n := n))
    refine ⟨hclosed_improper, ?_⟩
    intro x hx
    have hx_top : convexFunctionClosure f x = (⊤ : EReal) := by
      simp [hcl]
    simpa [htop] using hx_top

/-- A proper convex function on `univ` is strictly above `⊥` everywhere. -/
lemma properConvexFunctionOn_univ_imp_bot_lt {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ x, (⊥ : EReal) < f x := by
  intro x
  have hnotbot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  exact (bot_lt_iff_ne_bot).2 hnotbot

/-- Relative openness of the effective domain forces `⊥` on it for improper functions. -/
lemma improperConvexFunctionOn_eq_bot_on_effectiveDomain_of_relOpen {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hopen : euclideanRelativelyOpen n
      ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f, f x = (⊥ : EReal) := by
  intro x hx
  set x' : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
  have hxC :
      x' ∈
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simpa [x'] using hx
  have hopen' :
      euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) =
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simpa [euclideanRelativelyOpen] using hopen
  have hxri :
      x' ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    simpa [hopen'] using hxC
  have hxbot :=
    improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) hf x' hxri
  simpa [x'] using hxbot

/-- Points outside the effective domain on `univ` must take value `⊤`. -/
lemma not_mem_effectiveDomain_univ_imp_eq_top {n : Nat}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hx : x ∉ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    f x = (⊤ : EReal) := by
  classical
  by_contra hne
  have hlt : f x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hne
  have hxmem :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    have hx' :
        x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} :=
      ⟨by simp, hlt⟩
    simpa [effectiveDomain_eq] using hx'
  exact hx hxmem

/-- Corollary 7.2.3. If `f` is a convex function whose effective domain is relatively open
(for instance if `effectiveDomain Set.univ f = Set.univ`), then either `f x > -∞` for every
`x` or `f x` is infinite for every `x`. -/
theorem convexFunction_relativelyOpen_effectiveDomain_or_infinite {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f)
    (hopen : euclideanRelativelyOpen n
      ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    (∀ x, (⊥ : EReal) < f x) ∨ (∀ x, f x = (⊤ : EReal) ∨ f x = (⊥ : EReal)) := by
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f
  · left
    exact properConvexFunctionOn_univ_imp_bot_lt (f := f) hproper
  · right
    have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      simpa [ConvexFunction] using hf
    have himproper :
        ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      exact ⟨hconv_on, hproper⟩
    intro x
    by_cases hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f
    · have hxbot :
          f x = (⊥ : EReal) :=
        improperConvexFunctionOn_eq_bot_on_effectiveDomain_of_relOpen
          (f := f) himproper hopen x hx
      exact Or.inr hxbot
    · have hxtop :
          f x = (⊤ : EReal) :=
        not_mem_effectiveDomain_univ_imp_eq_top (f := f) hx
      exact Or.inl hxtop

/-- The closure of an improper convex function agrees with the function on `ri (dom f)`. -/
lemma convexFunctionClosure_agrees_on_ri_of_improper {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      convexFunctionClosure f x = f x := by
  exact
    (convexFunctionClosure_closed_improperConvexFunctionOn_and_agrees_on_ri
        (f := f) hf).2

/-- The epigraph of the constant `⊥` function is all of `ℝ^n × ℝ`. -/
lemma epigraph_const_bot_univ {n : Nat} :
    epigraph (S := (Set.univ : Set (Fin n → Real))) (fun _ => (⊥ : EReal)) =
      (Set.univ : Set ((Fin n → Real) × Real)) := by
  ext p
  constructor
  · intro hp
    exact Set.mem_univ p
  · intro hp
    exact ⟨Set.mem_univ p.1, bot_le⟩

/-- If an improper convex function attains `⊥` and has dense effective domain,
then its epigraph has dense closure. -/
lemma closure_epigraph_univ_of_exists_bot {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (_hbot : ∃ x, f x = (⊥ : EReal))
    (hdense : closure (effectiveDomain (Set.univ : Set (Fin n → Real)) f) = Set.univ) :
    closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
      (Set.univ : Set ((Fin n → Real) × Real)) := by
  classical
  set C :
      Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hCconv : Convex Real C := by
    have hconv_dom :
        Convex Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1
    simpa [C] using
      (Convex.linear_preimage
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f)
        hconv_dom
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap)
  have hcl_C : closure C = Set.univ := by
    have hpre :
        closure C =
          (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            closure (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      simpa [C] using
        (Homeomorph.preimage_closure
            (h := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toHomeomorph)
            (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f)).symm
    calc
      closure C =
          (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            closure (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := hpre
      _ =
          (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            (Set.univ : Set (Fin n → Real)) := by
          simp [hdense]
      _ = (Set.univ : Set (EuclideanSpace Real (Fin n))) := by
        simp
  have hcl_ri :
      closure (euclideanRelativeInterior n C) =
        (Set.univ : Set (EuclideanSpace Real (Fin n))) := by
    have hcl_ri_C :=
      (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C hCconv).1
    simpa [hcl_C] using hcl_ri_C
  set A : Set (Fin n → Real) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ''
      (euclideanRelativeInterior n C)
  have hA_dense : Dense A := by
    have hdenseRange :
        DenseRange (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) := by
      intro y
      refine subset_closure ?_
      refine ⟨(EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y, ?_⟩
      simp
    have hcont :
        Continuous (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) := by
      simpa using (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).continuous
    have hri_dense : Dense (euclideanRelativeInterior n C) := by
      intro x
      simp [hcl_ri]
    simpa [A] using
      (DenseRange.dense_image
        (f := fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real))
        hdenseRange hcont hri_dense)
  have hprod_dense :
      Dense (A ×ˢ (Set.univ : Set Real)) := by
    have h_univ_dense : Dense (Set.univ : Set Real) := by
      intro x
      simp
    exact Dense.prod hA_dense h_univ_dense
  have hsubset :
      A ×ˢ (Set.univ : Set Real) ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
    intro p hp
    rcases hp with ⟨hx, -⟩
    rcases hx with ⟨y, hy, hyEq⟩
    have hybot : f y = (⊥ : EReal) :=
      improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) hf y hy
    have hybot' : f p.1 = (⊥ : EReal) := by
      simpa [hyEq] using hybot
    refine (mem_epigraph_univ_iff (f := f)).2 ?_
    simp [hybot']
  have hdense_epi :
      Dense (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
    Dense.mono hsubset hprod_dense
  ext p
  constructor
  · intro hp
    exact Set.mem_univ p
  · intro hp
    exact hdense_epi p

/-- Text 7.0.15: Even when a convex function `f` has `-∞` somewhere, its closure `cl f`
is not drastically different: they coincide on `ri (dom f)`, and when `dom f` is dense
their epigraphs have the same closure. -/
theorem convexFunctionClosure_agrees_on_ri_and_same_epigraph_closure {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hdense : closure (effectiveDomain (Set.univ : Set (Fin n → Real)) f) = Set.univ) :
    (∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        convexFunctionClosure f x = f x) ∧
      closure (epigraph (S := (Set.univ : Set (Fin n → Real)))
        (convexFunctionClosure f)) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
  classical
  have hri :
      ∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        convexFunctionClosure f x = f x :=
    convexFunctionClosure_agrees_on_ri_of_improper (f := f) hf
  by_cases hbot : ∃ x, f x = (⊥ : EReal)
  · have hcl :
        convexFunctionClosure f = (fun _ => (⊥ : EReal)) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := f) hbot
    have hleft :
        closure (epigraph (S := (Set.univ : Set (Fin n → Real)))
          (convexFunctionClosure f)) =
          (Set.univ : Set ((Fin n → Real) × Real)) := by
      simp [hcl, epigraph_const_bot_univ]
    have hright :
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
          (Set.univ : Set ((Fin n → Real) × Real)) :=
      closure_epigraph_univ_of_exists_bot (f := f) hf hbot hdense
    have hclosure :
        closure (epigraph (S := (Set.univ : Set (Fin n → Real)))
          (convexFunctionClosure f)) =
          closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
      calc
        closure (epigraph (S := (Set.univ : Set (Fin n → Real)))
            (convexFunctionClosure f)) =
            (Set.univ : Set ((Fin n → Real) × Real)) := hleft
        _ = closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
          simp [hright]
    exact ⟨hri, hclosure⟩
  · have hbot' : ∀ x, f x ≠ (⊥ : EReal) := by
      intro x hx
      exact hbot ⟨x, hx⟩
    have h_epi :
        epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
          closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
      (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot').1
    have hclosure :
        closure (epigraph (S := (Set.univ : Set (Fin n → Real)))
          (convexFunctionClosure f)) =
          closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
      simp [h_epi]
    exact ⟨hri, hclosure⟩

/-
Remark 7.0.21: The closure operation can be regarded as a normalization; for many
purposes one may restrict attention to closed convex functions with
`convexFunctionClosure f = f`.
-/
/-- A lower semicontinuous function equals its lower semicontinuous hull. -/
lemma lowerSemicontinuousHull_eq_of_lsc {n : Nat} {f : (Fin n → Real) → EReal}
    (hls : LowerSemicontinuous f) :
    lowerSemicontinuousHull f = f := by
  classical
  have hspec :=
    Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f)
  have hle : lowerSemicontinuousHull f ≤ f := hspec.2.1
  have hge : f ≤ lowerSemicontinuousHull f := by
    have hle_self : f ≤ f := by
      intro x
      rfl
    exact hspec.2.2 f hls hle_self
  exact le_antisymm hle hge

/-- If `f` is lower semicontinuous and never `⊥`, then its closure is itself. -/
lemma convexFunctionClosure_eq_of_no_bot {n : Nat} {f : (Fin n → Real) → EReal}
    (hls : LowerSemicontinuous f) (hbot : ∀ x, f x ≠ (⊥ : EReal)) :
    convexFunctionClosure f = f := by
  classical
  have hEq : lowerSemicontinuousHull f = f :=
    lowerSemicontinuousHull_eq_of_lsc (n := n) (f := f) hls
  simp [convexFunctionClosure, hbot, hEq]

theorem convexFunctionClosure_eq_of_closedConvexFunction {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ClosedConvexFunction f)
    (hbot : ∀ x, f x ≠ (⊥ : EReal)) :
    convexFunctionClosure f = f := by
  exact convexFunctionClosure_eq_of_no_bot (f := f) hf.2 hbot

/-- Rewriting the line infimum as an infimum over the projection fiber. -/
lemma example_inf_over_line_convex_g_eq_sInf_fiber
    {f : (Fin 2 → Real) → EReal} (x : Fin 1 → Real) :
    (iInf (fun xi2 : Real =>
      f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) =
      sInf { z : EReal | ∃ u : Fin 2 → Real,
        projectionLinearMap (by decide : 1 ≤ 2) u = x ∧ z = f u } := by
  classical
  let S : Set EReal :=
    { z : EReal | ∃ u : Fin 2 → Real,
        projectionLinearMap (by decide : 1 ≤ 2) u = x ∧ z = f u }
  have hset :
      S = Set.range (fun xi2 : Real =>
        f (fun i : Fin 2 => if i = 0 then x 0 else xi2)) := by
    ext z; constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u 1, ?_⟩
      have hu0 :
          u 0 = x 0 := by
        have hu' := (projectionLinearMap_eq_iff (hmn := (by decide : 1 ≤ 2)) u x).1 hu
        simpa using hu' 0
      have hu_eq : u = fun i : Fin 2 => if i = 0 then x 0 else u 1 := by
        funext i
        fin_cases i
        · simp [hu0]
        · simp
      rw [hu_eq]
      simp
    · rintro ⟨xi2, rfl⟩
      refine ⟨(fun i : Fin 2 => if i = 0 then x 0 else xi2), ?_, rfl⟩
      refine (projectionLinearMap_eq_iff (hmn := (by decide : 1 ≤ 2)) _ _).2 ?_
      intro i
      fin_cases i
      · simp
  have h :
      iInf (fun xi2 : Real =>
          f (fun i : Fin 2 => if i = 0 then x 0 else xi2)) =
        sInf (Set.range (fun xi2 : Real =>
          f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) := by
    symm
    simpa using
      (sInf_range (f := fun xi2 : Real =>
        f (fun i : Fin 2 => if i = 0 then x 0 else xi2)))
  calc
    iInf (fun xi2 : Real =>
        f (fun i : Fin 2 => if i = 0 then x 0 else xi2)) =
        sInf (Set.range (fun xi2 : Real =>
          f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) := h
    _ = sInf S := by simp [hset]

/-- The fiber infimum of a convex function is convex. -/
lemma example_inf_over_line_convex_g_convex
    {f : (Fin 2 → Real) → EReal} (hfconv : ConvexFunction f) :
    ConvexFunction (fun x : Fin 1 → Real =>
      iInf (fun xi2 : Real =>
        f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) := by
  classical
  have hfconv_on :
      ConvexFunctionOn (S := (Set.univ : Set (Fin 2 → Real))) f := by
    simpa [ConvexFunction] using hfconv
  have hconv_on :
      ConvexFunctionOn (S := (Set.univ : Set (Fin 1 → Real)))
        (fun y =>
          sInf { z : EReal | ∃ u : Fin 2 → Real,
            projectionLinearMap (by decide : 1 ≤ 2) u = y ∧ z = f u }) := by
    simpa using
      (convexFunctionOn_inf_fiber_linearMap
        (A := projectionLinearMap (by decide : 1 ≤ 2)) (h := f) hfconv_on)
  have hfun :
      (fun y : Fin 1 → Real =>
          sInf { z : EReal | ∃ u : Fin 2 → Real,
            projectionLinearMap (by decide : 1 ≤ 2) u = y ∧ z = f u }) =
        (fun y : Fin 1 → Real =>
          iInf (fun xi2 : Real =>
            f (fun i : Fin 2 => if i = 0 then y 0 else xi2))) := by
    funext y
    symm
    exact example_inf_over_line_convex_g_eq_sInf_fiber (f := f) y
  have hconv_on' :
      ConvexFunctionOn (S := (Set.univ : Set (Fin 1 → Real)))
        (fun y : Fin 1 → Real =>
          iInf (fun xi2 : Real =>
            f (fun i : Fin 2 => if i = 0 then y 0 else xi2))) := by
    simpa [hfun] using hconv_on
  simpa [ConvexFunction] using hconv_on'

/-- The infimum along a vertical line is strictly below `⊤` when `f` is finite. -/
lemma example_inf_over_line_convex_g_lt_top
    {f : (Fin 2 → Real) → EReal}
    (hfinite : ∀ x, f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ∀ x : Fin 1 → Real,
      (iInf (fun xi2 : Real =>
        f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) < (⊤ : EReal) := by
  intro x
  have hle :
      iInf (fun xi2 : Real =>
        f (fun i : Fin 2 => if i = 0 then x 0 else xi2)) ≤
        f (fun i : Fin 2 => if i = 0 then x 0 else 0) := by
    exact iInf_le _ 0
  have hlt :
      f (fun i : Fin 2 => if i = 0 then x 0 else 0) < (⊤ : EReal) :=
    (lt_top_iff_ne_top).2 (hfinite _).1
  exact lt_of_le_of_lt hle hlt

/-- The effective domain of the line infimum is all of `ℝ`. -/
lemma example_inf_over_line_convex_effectiveDomain_univ
    {f : (Fin 2 → Real) → EReal}
    (hfinite : ∀ x, f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    effectiveDomain (S := (Set.univ : Set (Fin 1 → Real)))
      (fun x : Fin 1 → Real =>
        iInf (fun xi2 : Real =>
          f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) = Set.univ := by
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    have hlt :=
      example_inf_over_line_convex_g_lt_top (f := f) hfinite x
    have hx' :
        x ∈ (Set.univ : Set (Fin 1 → Real)) ∧
          (iInf (fun xi2 : Real =>
            f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) < (⊤ : EReal) := by
      exact ⟨by simp, hlt⟩
    simpa [effectiveDomain_eq] using hx'

/-- Corollary 7.2.3 applied to the infimum along vertical lines. -/
lemma example_inf_over_line_convex_dichotomy
    {f : (Fin 2 → Real) → EReal}
    (hfconv : ConvexFunction f)
    (hfinite : ∀ x, f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    (∀ x : Fin 1 → Real,
        (iInf (fun xi2 : Real =>
          f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) ≠ (⊤ : EReal) ∧
        (iInf (fun xi2 : Real =>
          f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) ≠ (⊥ : EReal)) ∨
      (∀ x : Fin 1 → Real,
        (iInf (fun xi2 : Real =>
          f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) = (⊥ : EReal)) := by
  classical
  let gfun : (Fin 1 → Real) → EReal :=
    fun x =>
      iInf (fun xi2 : Real => f (fun i : Fin 2 => if i = 0 then x 0 else xi2))
  have hconv_g : ConvexFunction gfun := by
    simpa [gfun] using (example_inf_over_line_convex_g_convex (f := f) hfconv)
  have heff :
      effectiveDomain (S := (Set.univ : Set (Fin 1 → Real))) gfun = Set.univ := by
    simpa [gfun] using (example_inf_over_line_convex_effectiveDomain_univ (f := f) hfinite)
  have huniv :
      euclideanRelativelyOpen 1 (Set.univ : Set (EuclideanSpace Real (Fin 1))) := by
    have hri :
        euclideanRelativeInterior 1 (Set.univ : Set (EuclideanSpace Real (Fin 1))) =
          (Set.univ : Set (EuclideanSpace Real (Fin 1))) := by
      simpa using
        (euclideanRelativeInterior_affineSubspace_eq 1
          (⊤ : AffineSubspace Real (EuclideanSpace Real (Fin 1))))
    simpa [euclideanRelativelyOpen] using hri
  have hopen :
      euclideanRelativelyOpen 1
        ((fun x : EuclideanSpace Real (Fin 1) => (x : Fin 1 → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin 1 → Real)) gfun) := by
    simpa [heff] using huniv
  have hcor :=
    convexFunction_relativelyOpen_effectiveDomain_or_infinite (f := gfun) hconv_g hopen
  have hnotop : ∀ x, gfun x ≠ (⊤ : EReal) := by
    intro x
    have hlt :
        gfun x < (⊤ : EReal) := by
      simpa [gfun] using
        (example_inf_over_line_convex_g_lt_top (f := f) hfinite x)
    exact ne_of_lt hlt
  have hcases :
      (∀ x, gfun x ≠ (⊤ : EReal) ∧ gfun x ≠ (⊥ : EReal)) ∨
        (∀ x, gfun x = (⊥ : EReal)) := by
    cases hcor with
    | inl hpos =>
        left
        intro x
        exact ⟨hnotop x, ne_of_gt (hpos x)⟩
    | inr hcase =>
        right
        intro x
        rcases hcase x with htop | hbot
        · exact (hnotop x htop).elim
        · exact hbot
  simpa [gfun] using hcases

/-- Bounded below on one vertical line implies bounded below on all vertical lines. -/
lemma example_inf_over_line_convex_bdd_below
    {f : (Fin 2 → Real) → EReal}
    (hfconv : ConvexFunction f)
    (hfinite : ∀ x, f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    (∃ xi1 : Real, ∃ m : Real, ∀ xi2 : Real,
        (m : EReal) ≤ f (fun i : Fin 2 => if i = 0 then xi1 else xi2)) →
      ∀ xi1 : Real, ∃ m : Real, ∀ xi2 : Real,
        (m : EReal) ≤ f (fun i : Fin 2 => if i = 0 then xi1 else xi2) := by
  classical
  intro hexists
  rcases hexists with ⟨xi1, m, hm⟩
  let gfun : (Fin 1 → Real) → EReal :=
    fun x =>
      iInf (fun xi2 : Real => f (fun i : Fin 2 => if i = 0 then x 0 else xi2))
  have hgle : (m : EReal) ≤ gfun (fun _ : Fin 1 => xi1) := by
    refine le_iInf ?_
    intro xi2
    exact hm xi2
  have hcases :
      (∀ x, gfun x ≠ (⊤ : EReal) ∧ gfun x ≠ (⊥ : EReal)) ∨
        (∀ x, gfun x = (⊥ : EReal)) := by
    simpa [gfun] using (example_inf_over_line_convex_dichotomy (f := f) hfconv hfinite)
  cases hcases with
  | inl hfinite_g =>
      intro xi1'
      refine ⟨(gfun (fun _ : Fin 1 => xi1')).toReal, ?_⟩
      intro xi2
      have hle :
          gfun (fun _ : Fin 1 => xi1') ≤
            f (fun i : Fin 2 => if i = 0 then xi1' else xi2) := by
        exact iInf_le _ xi2
      have hnotop : gfun (fun _ : Fin 1 => xi1') ≠ (⊤ : EReal) :=
        (hfinite_g (fun _ : Fin 1 => xi1')).1
      have hnotbot : gfun (fun _ : Fin 1 => xi1') ≠ (⊥ : EReal) :=
        (hfinite_g (fun _ : Fin 1 => xi1')).2
      have hcoe :
          ((gfun (fun _ : Fin 1 => xi1')).toReal : EReal) =
            gfun (fun _ : Fin 1 => xi1') :=
        EReal.coe_toReal hnotop hnotbot
      simpa [hcoe] using hle
  | inr hbot_all =>
      exfalso
      have hbot := hbot_all (fun _ : Fin 1 => xi1)
      have hgle' := hgle
      rw [hbot] at hgle'
      have hbot_le : (m : EReal) ≤ (⊥ : EReal) := hgle'
      have hlt : (⊥ : EReal) < (m : EReal) := EReal.bot_lt_coe m
      exact (not_lt_of_ge hbot_le hlt)

/-- Example 7.0.22: Let `f` be a finite convex function on `ℝ^2` and define
`g(xi1) = inf_{xi2 ∈ ℝ} f(xi1, xi2)`. Then `g` is convex and `dom g = ℝ`.
By Corollary 7.2.3, either `g(xi1)` is finite for all `xi1` or `g(xi1) = -∞` for all `xi1`.
Consequently, if `f` is bounded below on one line parallel to the `xi2`-axis,
then it is bounded below on every such line. -/
theorem example_inf_over_line_convex
    {f : (Fin 2 → Real) → EReal}
    (hfconv : ConvexFunction f)
    (hfinite : ∀ x, f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    let g : (Fin 1 → Real) → EReal :=
      fun x =>
        iInf (fun xi2 : Real => f (fun i : Fin 2 => if i = 0 then x 0 else xi2))
    ;
    ConvexFunction g ∧
      effectiveDomain (S := (Set.univ : Set (Fin 1 → Real))) g = Set.univ ∧
      ((∀ x, g x ≠ (⊤ : EReal) ∧ g x ≠ (⊥ : EReal)) ∨
        (∀ x, g x = (⊥ : EReal))) ∧
      ((∃ xi1 : Real, ∃ m : Real, ∀ xi2 : Real,
          (m : EReal) ≤ f (fun i : Fin 2 => if i = 0 then xi1 else xi2)) →
        ∀ xi1 : Real, ∃ m : Real, ∀ xi2 : Real,
          (m : EReal) ≤ f (fun i : Fin 2 => if i = 0 then xi1 else xi2)) := by
  classical
  dsimp
  have hconv :
      ConvexFunction (fun x : Fin 1 → Real =>
        iInf (fun xi2 : Real => f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) :=
    example_inf_over_line_convex_g_convex (f := f) hfconv
  have heff :
      effectiveDomain (S := (Set.univ : Set (Fin 1 → Real)))
          (fun x : Fin 1 → Real =>
            iInf (fun xi2 : Real =>
              f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) = Set.univ :=
    example_inf_over_line_convex_effectiveDomain_univ (f := f) hfinite
  have hdich :
      (∀ x : Fin 1 → Real,
          (iInf (fun xi2 : Real =>
            f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) ≠ (⊤ : EReal) ∧
          (iInf (fun xi2 : Real =>
            f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) ≠ (⊥ : EReal)) ∨
        (∀ x : Fin 1 → Real,
          (iInf (fun xi2 : Real =>
            f (fun i : Fin 2 => if i = 0 then x 0 else xi2))) = (⊥ : EReal)) :=
    example_inf_over_line_convex_dichotomy (f := f) hfconv hfinite
  have hbdd :
      (∃ xi1 : Real, ∃ m : Real, ∀ xi2 : Real,
          (m : EReal) ≤ f (fun i : Fin 2 => if i = 0 then xi1 else xi2)) →
        ∀ xi1 : Real, ∃ m : Real, ∀ xi2 : Real,
          (m : EReal) ≤ f (fun i : Fin 2 => if i = 0 then xi1 else xi2) :=
    example_inf_over_line_convex_bdd_below (f := f) hfconv hfinite
  exact ⟨hconv, heff, hdich, hbdd⟩

/-- Remark 7.0.23: Theorems 7.2 and later show that comparisons between `f` and `cl f`
hinge on relative interiors; in particular, the set `ri (epi f)` plays a key role. -/
def riEpigraph {n : Nat} (f : (Fin n → Real) → EReal) :
    Set (EuclideanSpace Real (Fin (n + 1))) :=
  euclideanRelativeInterior (n + 1)
    ((appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f))

end Section07
end Chap02
