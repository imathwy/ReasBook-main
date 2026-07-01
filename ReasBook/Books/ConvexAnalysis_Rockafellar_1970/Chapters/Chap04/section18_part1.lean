/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part1

open scoped Pointwise

section Chap04
section Section18

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- Defn 18.1 (the face of a convex set). Let `C` be a convex set. A subset `C' ⊆ C` is a *face*
of `C` if, for every closed line segment in `C`, whenever the relative interior of the segment
(i.e. the open segment) is contained in `C'`, then both endpoints of the segment belong to `C'`. -/
def IsFace (C C' : Set E) : Prop :=
  Convex 𝕜 C ∧ IsExtreme 𝕜 C C'

/-- A positive pair of coefficients summing to `1` yields a nonempty open segment. -/
lemma openSegment_nonempty_of_exists_pos_add_eq_one
    (hcoeff : ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ a + b = 1) (x y : E) :
    (openSegment 𝕜 x y).Nonempty := by
  rcases hcoeff with ⟨a, b, ha, hb, hab⟩
  refine ⟨a • x + b • y, ?_⟩
  exact ⟨a, b, ha, hb, hab, rfl⟩

/-- Text 18.0.1 (empty set is a face of itself). Let `C` be a convex set. The empty set `∅` is a
face of `C`. -/
theorem isFace_empty (C : Set E) (hC : Convex 𝕜 C) :
    IsFace (𝕜 := 𝕜) C (∅ : Set E) := by
  refine ⟨hC, ?_⟩
  refine ⟨by simp, ?_⟩
  intro x hx y hy z hz hseg
  cases hz

/-- Text 18.0.2 (convex set is a face of itself). Let `C` be a convex set. The set `C` itself is a
face of `C`. -/
theorem isFace_self (C : Set E) (hC : Convex 𝕜 C) : IsFace (𝕜 := 𝕜) C C := by
  exact ⟨hC, IsExtreme.refl (𝕜 := 𝕜) (A := C)⟩

/-- Defn 18.2 (the extreme point of a convex set). A point `x ∈ C` is an *extreme point* of `C` if
there is no nontrivial way to write `x` as a convex combination `(1 - λ) y + λ z` with `y ∈ C`,
`z ∈ C` and `0 < λ < 1`, except by taking `y = z = x`. Equivalently, `x` belongs to no open
segment with endpoints in `C` unless both endpoints are `x`. -/
def IsExtremePoint (C : Set E) (x : E) : Prop :=
  x ∈ C ∧ ∀ ⦃y z : E⦄, y ∈ C → z ∈ C → x ∈ openSegment 𝕜 y z → y = x ∧ z = x

/-- Defn 18.2 (the extreme point of a convex set): the book definition is equivalent to membership
in the mathlib set of extreme points `C.extremePoints 𝕜`. -/
theorem isExtremePoint_iff_mem_extremePoints (C : Set E) (x : E) :
    IsExtremePoint (𝕜 := 𝕜) C x ↔ x ∈ C.extremePoints 𝕜 := by
  constructor
  · intro hx
    refine (mem_extremePoints (𝕜 := 𝕜) (A := C) (x := x)).2 ?_
    refine ⟨hx.1, ?_⟩
    intro y hy z hz hseg
    exact hx.2 hy hz hseg
  · intro hx
    rcases (mem_extremePoints (𝕜 := 𝕜) (A := C) (x := x)).1 hx with ⟨hxC, hxseg⟩
    refine ⟨hxC, ?_⟩
    intro y z hy hz hseg
    exact hxseg y hy z hz hseg

/-- Text 18.0.3 (zero-dimensional faces are extreme points). The zero-dimensional faces of a
convex set `C` (informally: singleton faces `{x}`) are equivalent to the extreme points of `C`. -/
theorem isFace_singleton_iff_isExtremePoint (C : Set E) (x : E) :
    IsFace (𝕜 := 𝕜) C ({x} : Set E) ↔ (Convex 𝕜 C ∧ IsExtremePoint (𝕜 := 𝕜) C x) := by
  simp [IsFace, isExtremePoint_iff_mem_extremePoints]

/-- Defn 18.3 (extreme ray). For a convex cone, an *extreme ray* is a face that is a half-line
emanating from the origin; equivalently, it is a face of the form `{t • x | t ≥ 0}` for some
nonzero vector `x`. -/
def IsExtremeRay (K : ConvexCone 𝕜 E) (R : Set E) : Prop :=
  IsFace (𝕜 := 𝕜) (K : Set E) R ∧ ∃ x : E, x ≠ 0 ∧ R = (fun t : 𝕜 => t • x) '' Set.Ici (0 : 𝕜)

/-- Defn 18.4 (extreme direction). If `C'` is a half-line face of a convex set `C`, the direction
of `C'` is called an *extreme direction* of `C` (an “extreme point of `C` at infinity”).

This helper predicate says that `d` is a (nonzero) direction vector of a half-line set `C'`,
meaning `C'` can be parameterized as `x + t • d` for `t ≥ 0`. -/
def IsDirectionOf (C' : Set E) (d : E) : Prop :=
  ∃ x : E, d ≠ 0 ∧ C' = (fun t : 𝕜 => x + t • d) '' Set.Ici (0 : 𝕜)

/-- Defn 18.4 (half-line face). A *half-line face* of a convex set `C` is a face `C'` of `C` that
is a half-line (ray) in the ambient space. -/
def IsHalfLineFace (C C' : Set E) : Prop :=
  IsFace (𝕜 := 𝕜) C C' ∧ ∃ d : E, IsDirectionOf (𝕜 := 𝕜) C' d

/-- Defn 18.4 (extreme direction). A vector `d` is an *extreme direction* of a convex set `C` if it
is the direction of some half-line face `C'` of `C`. -/
def IsExtremeDirection (C : Set E) (d : E) : Prop :=
  ∃ C' : Set E, IsHalfLineFace (𝕜 := 𝕜) C C' ∧ IsDirectionOf (𝕜 := 𝕜) C' d

section Maximizers

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- Text 18.0.5 (Properties of the set of maximizers). Let `C` be a convex set in `ℝⁿ` and let `h`
be a linear functional. Define `C'` as the set of points where `h` attains its maximum over `C`,
so `C' = {x ∈ C | h x = α}` where `α = sup_C h`. -/
def maximizers (C : Set F) (h : F →ₗ[ℝ] ℝ) : Set F :=
  {x : F | x ∈ C ∧ IsMaxOn (fun x => h x) C x}

/-- Membership in the set of maximizers amounts to being in `C` and maximizing `h` on `C`. -/
lemma mem_maximizers_iff {C : Set F} {h : F →ₗ[ℝ] ℝ} {x : F} :
    x ∈ maximizers C h ↔ x ∈ C ∧ ∀ y ∈ C, h y ≤ h x := by
  constructor
  · intro hx
    rcases hx with ⟨hxC, hxmax⟩
    exact ⟨hxC, (isMaxOn_iff).1 hxmax⟩
  · intro hx
    rcases hx with ⟨hxC, hxmax⟩
    exact ⟨hxC, (isMaxOn_iff).2 hxmax⟩

/-- Any two maximizers have the same objective value. -/
lemma h_eq_of_mem_maximizers {C : Set F} {h : F →ₗ[ℝ] ℝ} {x y : F}
    (hx : x ∈ maximizers C h) (hy : y ∈ maximizers C h) :
    h x = h y := by
  rcases (mem_maximizers_iff (x := x)).1 hx with ⟨hxC, hxmax⟩
  rcases (mem_maximizers_iff (x := y)).1 hy with ⟨hyC, hymax⟩
  exact le_antisymm (hymax x hxC) (hxmax y hyC)

/-- A point in `C` with the same value as a maximizer is itself a maximizer. -/
lemma mem_maximizers_of_mem_of_eq_value {C : Set F} {h : F →ₗ[ℝ] ℝ} {x x' : F}
    (hx : x ∈ maximizers C h) (hx'C : x' ∈ C) (hxeq : h x' = h x) :
    x' ∈ maximizers C h := by
  rcases (mem_maximizers_iff (x := x)).1 hx with ⟨_, hxmax⟩
  refine (mem_maximizers_iff (x := x')).2 ?_
  refine ⟨hx'C, ?_⟩
  intro y hyC
  simpa [hxeq] using (hxmax y hyC)

/-- Linear functionals agree on convex combinations of maximizers. -/
lemma h_convexCombo_eq_max {C : Set F} {h : F →ₗ[ℝ] ℝ} {x y : F} {a b : ℝ}
    (hx : x ∈ maximizers C h) (hy : y ∈ maximizers C h) (hab : a + b = 1) :
    h (a • x + b • y) = h x := by
  have hxhy : h x = h y := h_eq_of_mem_maximizers (x := x) (y := y) hx hy
  calc
    h (a • x + b • y) = h (a • x) + h (b • y) := by
      simp
    _ = a • h x + b • h y := by
      rw [h.map_smul, h.map_smul]
    _ = a • h x + b • h x := by simp [hxhy]
    _ = (a + b) • h x := by
      rw [← add_smul]
    _ = h x := by
      simp [hab]

/-- Text 18.0.5 (Properties of the set of maximizers): the set of maximizers of a linear
functional on a convex set is convex. -/
theorem convex_maximizers (C : Set F) (h : F →ₗ[ℝ] ℝ) (hC : Convex ℝ C) :
    Convex ℝ (maximizers C h) := by
  intro x hx y hy a b ha hb hab
  have hxC : x ∈ C := (mem_maximizers_iff (x := x)).1 hx |>.1
  have hyC : y ∈ C := (mem_maximizers_iff (x := y)).1 hy |>.1
  have hxyC : a • x + b • y ∈ C := hC hxC hyC ha hb hab
  have hxy : h (a • x + b • y) = h x :=
    h_convexCombo_eq_max (C := C) (h := h) (x := x) (y := y) (a := a) (b := b) hx hy hab
  exact mem_maximizers_of_mem_of_eq_value (C := C) (h := h) (x := x)
    (x' := a • x + b • y) hx hxyC hxy

/-- A maximizer inside an open segment forces equal endpoint values. -/
lemma h_eq_endpoints_of_mem_openSegment_of_mem_maximizers {C : Set F} {h : F →ₗ[ℝ] ℝ}
    {x y z : F} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ openSegment ℝ x y)
    (hzmax : z ∈ maximizers C h) :
    h x = h z ∧ h y = h z := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  rcases (mem_maximizers_iff (x := a • x + b • y)).1 hzmax with ⟨_, hzmax⟩
  have hx_le : h x ≤ h (a • x + b • y) := hzmax x hx
  have hy_le : h y ≤ h (a • x + b • y) := hzmax y hy
  have hz_eq : h (a • x + b • y) = a • h x + b • h y := by
    simp
  have hz_right :
      a • h (a • x + b • y) + b • h (a • x + b • y) = h (a • x + b • y) := by
    calc
      a • h (a • x + b • y) + b • h (a • x + b • y)
          = (a + b) • h (a • x + b • y) := by
              simpa using (add_smul a b (h (a • x + b • y))).symm
      _ = h (a • x + b • y) := by
              simp [hab]
  have hx_eq : h x = h (a • x + b • y) := by
    by_contra hne
    have hx_lt : h x < h (a • x + b • y) := lt_of_le_of_ne hx_le hne
    have h1 : a • h x < a • h (a • x + b • y) := by
      have h1' : a * h x < a * h (a • x + b • y) :=
        mul_lt_mul_of_pos_left hx_lt ha
      simpa [smul_eq_mul] using h1'
    have h2 : b • h y ≤ b • h (a • x + b • y) := by
      have h2' : b * h y ≤ b * h (a • x + b • y) :=
        mul_le_mul_of_nonneg_left hy_le (le_of_lt hb)
      simpa [smul_eq_mul] using h2'
    have hlt :
        a • h x + b • h y < a • h (a • x + b • y) + b • h (a • x + b • y) :=
      add_lt_add_of_lt_of_le h1 h2
    have hlt' : a • h x + b • h y < h (a • x + b • y) := by
      calc
        a • h x + b • h y
            < a • h (a • x + b • y) + b • h (a • x + b • y) := hlt
        _ = h (a • x + b • y) := hz_right
    have : h (a • x + b • y) < h (a • x + b • y) := by
      calc
        h (a • x + b • y) = a • h x + b • h y := hz_eq
        _ < h (a • x + b • y) := hlt'
    exact (lt_irrefl _ this)
  have hy_eq : h y = h (a • x + b • y) := by
    by_contra hne
    have hy_lt : h y < h (a • x + b • y) := lt_of_le_of_ne hy_le hne
    have h1 : b • h y < b • h (a • x + b • y) := by
      have h1' : b * h y < b * h (a • x + b • y) :=
        mul_lt_mul_of_pos_left hy_lt hb
      simpa [smul_eq_mul] using h1'
    have h2 : a • h x ≤ a • h (a • x + b • y) := by
      have h2' : a * h x ≤ a * h (a • x + b • y) :=
        mul_le_mul_of_nonneg_left hx_le (le_of_lt ha)
      simpa [smul_eq_mul] using h2'
    have hlt :
        a • h x + b • h y < a • h (a • x + b • y) + b • h (a • x + b • y) :=
      add_lt_add_of_le_of_lt h2 h1
    have hlt' : a • h x + b • h y < h (a • x + b • y) := by
      calc
        a • h x + b • h y
            < a • h (a • x + b • y) + b • h (a • x + b • y) := hlt
        _ = h (a • x + b • y) := hz_right
    have : h (a • x + b • y) < h (a • x + b • y) := by
      calc
        h (a • x + b • y) = a • h x + b • h y := hz_eq
        _ < h (a • x + b • y) := hlt'
    exact (lt_irrefl _ this)
  exact ⟨hx_eq, hy_eq⟩

/-- Endpoints of an open segment containing a maximizer are maximizers. -/
lemma mem_maximizers_endpoints_of_mem_openSegment {C : Set F} {h : F →ₗ[ℝ] ℝ}
    {x y z : F} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ openSegment ℝ x y)
    (hzmax : z ∈ maximizers C h) :
    x ∈ maximizers C h ∧ y ∈ maximizers C h := by
  rcases h_eq_endpoints_of_mem_openSegment_of_mem_maximizers (hx := hx) (hy := hy)
      (hz := hz) (hzmax := hzmax) with ⟨hxz, hyz⟩
  rcases (mem_maximizers_iff (x := z)).1 hzmax with ⟨_, hzmax_le⟩
  have hxmax : x ∈ maximizers C h := by
    refine (mem_maximizers_iff (x := x)).2 ?_
    refine ⟨hx, ?_⟩
    intro w hwC
    have hwle : h w ≤ h z := hzmax_le w hwC
    simpa [hxz] using hwle
  have hymax : y ∈ maximizers C h := by
    refine (mem_maximizers_iff (x := y)).2 ?_
    refine ⟨hy, ?_⟩
    intro w hwC
    have hwle : h w ≤ h z := hzmax_le w hwC
    simpa [hyz] using hwle
  exact ⟨hxmax, hymax⟩

/-- Text 18.0.5 (Properties of the set of maximizers): if a maximizer lies in the relative interior
of a line segment in `C`, then every point of that segment is a maximizer. -/
theorem segment_subset_maximizers_of_mem_openSegment (C : Set F) (h : F →ₗ[ℝ] ℝ) (hC : Convex ℝ C)
    {x y z : F} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ openSegment ℝ x y)
    (hzmax : z ∈ maximizers C h) :
    segment ℝ x y ⊆ maximizers C h := by
  rcases mem_maximizers_endpoints_of_mem_openSegment (hx := hx) (hy := hy) (hz := hz)
      (hzmax := hzmax) with ⟨hxmax, hymax⟩
  exact (convex_maximizers C h hC).segment_subset hxmax hymax

/-- Text 18.0.6. Let `C` be a convex set and let `h` be a linear functional. Let `α = sup_{x ∈ C} h x`.
If `α < ∞`, define the set of maximizers `C' = {x ∈ C | h x = α}`. Then `C'` is a face of `C`. -/
theorem isFace_maximizers (C : Set F) (h : F →ₗ[ℝ] ℝ) (hC : Convex ℝ C) :
    IsFace (𝕜 := ℝ) C (maximizers C h) := by
  refine ⟨hC, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx y hy z hzmax hzseg
    rcases mem_maximizers_endpoints_of_mem_openSegment (hx := hx) (hy := hy) (hz := hzseg)
        (hzmax := hzmax) with ⟨hxmax, _⟩
    exact hxmax

/-- Defn 18.5 (Exposed face, directions and rays). Let `C` be a convex set. A subset `F ⊆ C` is an
*exposed face* of `C` if there exists a linear functional `h` (coming from a supporting hyperplane)
such that `F` is exactly the set of maximizers of `h` over `C`, i.e.
`F = {x ∈ C | h x = sup_{y ∈ C} h y}`.

The *exposed directions* of `C` (exposed points at infinity) are the direction vectors of exposed
half-line faces of `C`.

An *exposed ray* of a convex cone is an exposed face which is a half-line emanating from the
origin. -/
def IsExposedFace (C Face : Set F) : Prop :=
  Convex ℝ C ∧ Face ⊆ C ∧ ∃ h : F →ₗ[ℝ] ℝ, Face = maximizers C h

/-- Maximizers with an attained upper bound are exactly a level set. -/
lemma maximizers_eq_inter_levelset_of_le_of_exists_eq {C : Set F} {h : F →ₗ[ℝ] ℝ} {a : ℝ}
    (hle : ∀ x ∈ C, h x ≤ a) (hex : ∃ x ∈ C, h x = a) :
    maximizers C h = C ∩ {x : F | h x = a} := by
  ext x
  constructor
  · intro hx
    rcases (mem_maximizers_iff (x := x)).1 hx with ⟨hxC, hxmax⟩
    refine ⟨hxC, ?_⟩
    have hxle : h x ≤ a := hle x hxC
    rcases hex with ⟨x0, hx0C, hx0eq⟩
    have hxae : a ≤ h x := by
      have h0le : h x0 ≤ h x := hxmax x0 hx0C
      simpa [hx0eq] using h0le
    exact le_antisymm hxle hxae
  · intro hx
    rcases hx with ⟨hxC, hxeq⟩
    have hxeq' : h x = a := by simpa using hxeq
    refine (mem_maximizers_iff (x := x)).2 ?_
    refine ⟨hxC, ?_⟩
    intro y hyC
    have hyle : h y ≤ a := hle y hyC
    simpa [hxeq'] using hyle

/-- Maximizers of the zero functional are the whole set. -/
lemma maximizers_zero_eq (C : Set F) :
    maximizers C (0 : F →ₗ[ℝ] ℝ) = C := by
  ext x
  constructor
  · intro hx
    rcases (mem_maximizers_iff (x := x)).1 hx with ⟨hxC, _⟩
    exact hxC
  · intro hxC
    refine (mem_maximizers_iff (x := x)).2 ?_
    refine ⟨hxC, ?_⟩
    intro y hyC
    simp

/-- Text 18.0.7. Let `C` be a convex set. A nonempty proper subset `Face ⊂ C` is an exposed face of
`C` if and only if there exists a nontrivial supporting hyperplane `H` to `C` such that
`Face = C ∩ H`. -/
theorem isExposedFace_iff_exists_supportingHyperplane (C Face : Set F)
    (hC : Convex ℝ C) (hFace_nonempty : Face.Nonempty) (hFace_proper : Face ⊂ C) :
    IsExposedFace (C := C) Face ↔
      ∃ (h : F →ₗ[ℝ] ℝ) (a : ℝ),
        h ≠ 0 ∧ (∀ x ∈ C, h x ≤ a) ∧ (∃ x ∈ C, h x = a) ∧ Face = C ∩ {x : F | h x = a} := by
  constructor
  · intro hExposed
    rcases hExposed with ⟨_, hFace_sub, ⟨h, hFace_eq⟩⟩
    rcases hFace_nonempty with ⟨x0, hx0Face⟩
    have hx0C : x0 ∈ C := hFace_sub hx0Face
    have hx0max : x0 ∈ maximizers C h := by
      simpa [hFace_eq] using hx0Face
    rcases (mem_maximizers_iff (x := x0)).1 hx0max with ⟨_, hx0max_le⟩
    let a : ℝ := h x0
    have hle : ∀ x ∈ C, h x ≤ a := by
      intro x hxC
      have := hx0max_le x hxC
      simpa [a] using this
    have hex : ∃ x ∈ C, h x = a := by
      refine ⟨x0, hx0C, ?_⟩
      simp [a]
    have hneq : h ≠ 0 := by
      intro hzero
      have hmax_eq : maximizers C h = C := by
        simpa [hzero] using (maximizers_zero_eq (C := C))
      have hFace_eqC : Face = C := by
        simp [hFace_eq, hmax_eq]
      have hFace_ne : Face ≠ C := by
        intro hEq
        apply hFace_proper.2
        intro x hx
        exact hEq.symm ▸ hx
      exact hFace_ne hFace_eqC
    have hFace_eq' : Face = C ∩ {x : F | h x = a} := by
      have hmax_eq' : maximizers C h = C ∩ {x : F | h x = a} :=
        maximizers_eq_inter_levelset_of_le_of_exists_eq (h := h) (a := a) hle hex
      simpa [hFace_eq] using hmax_eq'
    exact ⟨h, a, hneq, hle, hex, hFace_eq'⟩
  · rintro ⟨h, a, _hneq, hle, hex, hFace_eq⟩
    refine ⟨hC, ?_, ?_⟩
    · intro x hxFace
      have hx : x ∈ C ∩ {x : F | h x = a} := by
        simpa [hFace_eq] using hxFace
      exact hx.1
    · refine ⟨h, ?_⟩
      have hmax_eq : maximizers C h = C ∩ {x : F | h x = a} :=
        maximizers_eq_inter_levelset_of_le_of_exists_eq (h := h) (a := a) hle hex
      calc
        Face = C ∩ {x : F | h x = a} := hFace_eq
        _ = maximizers C h := by
          symm
          exact hmax_eq

/-- Defn 18.5 (exposed point). A point `x ∈ C` is an *exposed point* of a convex set `C` if the
singleton face `{x}` is an exposed face of `C` (i.e. `{x}` is the set of maximizers of some linear
functional on `C`). -/
def IsExposedPoint (C : Set F) (x : F) : Prop :=
  IsExposedFace C ({x} : Set F)

/-- Text 18.0.8. Let `C` be a convex set. If `x ∈ C` is an exposed point, then `x` is an extreme
point of `C`. -/
theorem isExtremePoint_of_isExposedPoint (C : Set F) {x : F} (hx : IsExposedPoint C x) :
    IsExtremePoint (𝕜 := ℝ) C x := by
  dsimp [IsExposedPoint, IsExposedFace] at hx
  rcases hx with ⟨hC, -, ⟨h, hxEq⟩⟩
  have hface : IsFace (𝕜 := ℝ) C ({x} : Set F) := by
    simpa [hxEq.symm] using (isFace_maximizers C h hC)
  have hxext :
      Convex ℝ C ∧ IsExtremePoint (𝕜 := ℝ) C x :=
    (isFace_singleton_iff_isExtremePoint (𝕜 := ℝ) (C := C) (x := x)).1 hface
  exact hxext.2

/-- Defn 18.5 (exposed half-line face). A half-line face `C'` of a convex set `C` is *exposed* if
it is an exposed face of `C` (equivalently: it is the set of maximizers of some linear functional
over `C`). -/
def IsExposedHalfLineFace (C C' : Set F) : Prop :=
  IsHalfLineFace (𝕜 := ℝ) C C' ∧ IsExposedFace C C'

/-- Defn 18.5 (exposed direction). A vector `d` is an *exposed direction* of a convex set `C` if it
is the direction of some exposed half-line face of `C`. -/
def IsExposedDirection (C : Set F) (d : F) : Prop :=
  ∃ C' : Set F, IsExposedHalfLineFace C C' ∧ IsDirectionOf (𝕜 := ℝ) C' d

/-- Text 18.0.9. The *exposed directions* (exposed points at infinity) of a convex set `C` are
defined to be the directions of the exposed half-line faces of `C`. -/
def exposedDirections (C : Set F) : Set F :=
  {d : F | IsExposedDirection C d}

/-- Defn 18.5 (exposed ray). A set `R` is an *exposed ray* of a convex cone `K` if it is an exposed
face of `K` and it is a half-line of the form `{t • x | t ≥ 0}` for some nonzero `x`. -/
def IsExposedRay (K : ConvexCone ℝ F) (R : Set F) : Prop :=
  IsExposedFace (C := (K : Set F)) R ∧
    ∃ x : F, x ≠ 0 ∧ R = (fun t : ℝ => t • x) '' Set.Ici (0 : ℝ)

/-- Text 18.0.10. Let `R` be an exposed ray of a convex set `C` (typically defined via the recession
cone `0⁺ C`). Then `R` is an extreme ray.

In this file we formulate the statement for an exposed ray of a convex cone `K` (e.g. `K = 0⁺ C`),
showing that every exposed ray is an extreme ray. -/
theorem isExtremeRay_of_isExposedRay (K : ConvexCone ℝ F) (R : Set F) (hR : IsExposedRay K R) :
    IsExtremeRay (𝕜 := ℝ) K R := by
  rcases hR with ⟨hExposed, hRay⟩
  rcases hExposed with ⟨hKconv, -, ⟨h, hRmax⟩⟩
  have hface : IsFace (𝕜 := ℝ) (K : Set F) R := by
    simpa [hRmax] using (isFace_maximizers (C := (K : Set F)) (h := h) hKconv)
  exact ⟨hface, hRay⟩

/-- The example set in `ℝ³` used to exhibit a non-exposed extreme point. -/
abbrev exampleC : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x : EuclideanSpace ℝ (Fin 3) | x 2 = 0 ∧ (max (x 0) 0) ^ 2 ≤ x 1}

/-- A convex-combination bound for `r ↦ (max r 0)^2`. -/
lemma max_sq_le_convex_comb {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (max (a * x + b * y) 0) ^ 2 ≤ a * (max x 0) ^ 2 + b * (max y 0) ^ 2 := by
  set u : ℝ := max x 0
  set v : ℝ := max y 0
  have hx_le : a * x ≤ a * u := mul_le_mul_of_nonneg_left (le_max_left x 0) ha
  have hy_le : b * y ≤ b * v := mul_le_mul_of_nonneg_left (le_max_left y 0) hb
  have hxy_le : a * x + b * y ≤ a * u + b * v := add_le_add hx_le hy_le
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    exact le_max_right _ _
  have hv_nonneg : 0 ≤ v := by
    dsimp [v]
    exact le_max_right _ _
  have hsum_nonneg : 0 ≤ a * u + b * v := by
    exact add_nonneg (mul_nonneg ha hu_nonneg) (mul_nonneg hb hv_nonneg)
  have hmax_le : max (a * x + b * y) 0 ≤ a * u + b * v := by
    exact (max_le_iff).2 ⟨hxy_le, hsum_nonneg⟩
  have hmax_nonneg : 0 ≤ max (a * x + b * y) 0 := le_max_right _ _
  have hsq1 : (max (a * x + b * y) 0) ^ 2 ≤ (a * u + b * v) ^ 2 := by
    have h := mul_le_mul hmax_le hmax_le hmax_nonneg hsum_nonneg
    simpa [pow_two] using h
  have hconv : ConvexOn ℝ (Set.univ : Set ℝ) (fun t : ℝ => t ^ 2) := by
    simpa using (Even.convexOn_pow (n := 2) (by decide : Even (2 : ℕ)))
  have hsq2 : (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
    have h := hconv.2 (by simp : u ∈ (Set.univ : Set ℝ)) (by simp : v ∈ (Set.univ : Set ℝ))
      ha hb hab
    simpa [smul_eq_mul, pow_two] using h
  exact le_trans hsq1 hsq2

/-- The example set `exampleC` is convex. -/
lemma convex_exampleC : Convex ℝ exampleC := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx2, hxineq⟩
  rcases hy with ⟨hy2, hyineq⟩
  have h2 : (a • x + b • y) 2 = 0 := by
    simp [hx2, hy2]
  have hsq :
      (max ((a • x + b • y) 0) 0) ^ 2 ≤
        a * (max (x 0) 0) ^ 2 + b * (max (y 0) 0) ^ 2 := by
    simpa [smul_eq_mul] using
      (max_sq_le_convex_comb (x := x 0) (y := y 0) (a := a) (b := b) ha hb hab)
  have hineq :
      (max ((a • x + b • y) 0) 0) ^ 2 ≤ (a • x + b • y) 1 := by
    have hineq' :
        a * (max (x 0) 0) ^ 2 + b * (max (y 0) 0) ^ 2 ≤ a * (x 1) + b * (y 1) := by
      have hx' : a * (max (x 0) 0) ^ 2 ≤ a * x 1 := mul_le_mul_of_nonneg_left hxineq ha
      have hy' : b * (max (y 0) 0) ^ 2 ≤ b * y 1 := mul_le_mul_of_nonneg_left hyineq hb
      exact add_le_add hx' hy'
    have h := le_trans hsq hineq'
    simpa [smul_eq_mul] using h
  exact ⟨h2, hineq⟩

/-- The origin is an extreme point of `exampleC`. -/
lemma isExtremePoint_origin_exampleC :
    IsExtremePoint (𝕜 := ℝ) exampleC (0 : EuclideanSpace ℝ (Fin 3)) := by
  refine ⟨by simp [exampleC], ?_⟩
  intro y z hy hz hseg
  rcases hy with ⟨hy2, hyineq⟩
  rcases hz with ⟨hz2, hzineq⟩
  rcases hseg with ⟨a, b, ha, hb, hab, hsum⟩
  have h1_eq : a * y 1 + b * z 1 = (0 : ℝ) := by
    have h1 := congrArg (fun v => v 1) hsum
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using h1
  have hy1_nonneg : 0 ≤ y 1 := by
    have hnonneg : 0 ≤ (max (y 0) 0) ^ 2 := by exact sq_nonneg _
    exact le_trans hnonneg hyineq
  have hz1_nonneg : 0 ≤ z 1 := by
    have hnonneg : 0 ≤ (max (z 0) 0) ^ 2 := by exact sq_nonneg _
    exact le_trans hnonneg hzineq
  have hy1_eq : y 1 = 0 := by nlinarith [h1_eq, ha, hb, hy1_nonneg, hz1_nonneg]
  have hz1_eq : z 1 = 0 := by nlinarith [h1_eq, ha, hb, hy1_nonneg, hz1_nonneg]
  have hy0_le : y 0 ≤ 0 := by
    have hle : (max (y 0) 0) ^ 2 ≤ 0 := by
      simpa [hy1_eq] using hyineq
    have hnonneg : 0 ≤ (max (y 0) 0) ^ 2 := by exact sq_nonneg _
    have hsq : (max (y 0) 0) ^ 2 = 0 := by
      exact le_antisymm hle hnonneg
    have hmax0 : max (y 0) 0 = 0 := by
      have hnonneg : 0 ≤ max (y 0) 0 := le_max_right _ _
      nlinarith [hsq, hnonneg]
    have hy0_le' : y 0 ≤ max (y 0) 0 := le_max_left _ _
    simpa [hmax0] using hy0_le'
  have hz0_le : z 0 ≤ 0 := by
    have hle : (max (z 0) 0) ^ 2 ≤ 0 := by
      simpa [hz1_eq] using hzineq
    have hnonneg : 0 ≤ (max (z 0) 0) ^ 2 := by exact sq_nonneg _
    have hsq : (max (z 0) 0) ^ 2 = 0 := by
      exact le_antisymm hle hnonneg
    have hmax0 : max (z 0) 0 = 0 := by
      have hnonneg : 0 ≤ max (z 0) 0 := le_max_right _ _
      nlinarith [hsq, hnonneg]
    have hz0_le' : z 0 ≤ max (z 0) 0 := le_max_left _ _
    simpa [hmax0] using hz0_le'
  have h0_eq : a * y 0 + b * z 0 = (0 : ℝ) := by
    have h0 := congrArg (fun v => v 0) hsum
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using h0
  have hy0_eq : y 0 = 0 := by nlinarith [h0_eq, ha, hb, hy0_le, hz0_le]
  have hz0_eq : z 0 = 0 := by nlinarith [h0_eq, ha, hb, hy0_le, hz0_le]
  have hy_eq : y = (0 : EuclideanSpace ℝ (Fin 3)) := by
    ext i
    fin_cases i
    · simp [hy0_eq]
    · simp [hy1_eq]
    · simp [hy2]
  have hz_eq : z = (0 : EuclideanSpace ℝ (Fin 3)) := by
    ext i
    fin_cases i
    · simp [hz0_eq]
    · simp [hz1_eq]
    · simp [hz2]
  exact ⟨hy_eq, hz_eq⟩

/-- The origin is not an exposed point of `exampleC`. -/
lemma not_isExposedPoint_origin_exampleC :
    ¬ IsExposedPoint exampleC (0 : EuclideanSpace ℝ (Fin 3)) := by
  intro hExposed
  dsimp [IsExposedPoint, IsExposedFace] at hExposed
  rcases hExposed with ⟨_hconv, _hFace_sub, ⟨h, hFace_eq⟩⟩
  have h0max : (0 : EuclideanSpace ℝ (Fin 3)) ∈ maximizers exampleC h := by
    have h0mem : (0 : EuclideanSpace ℝ (Fin 3)) ∈ ({0} : Set (EuclideanSpace ℝ (Fin 3))) := by
      simp
    simpa [hFace_eq] using h0mem
  rcases (mem_maximizers_iff (C := exampleC) (h := h) (x := 0)).1 h0max with ⟨_h0C, hmax_le⟩
  have hle : ∀ y ∈ exampleC, h y ≤ 0 := by
    intro y hy
    have := hmax_le y hy
    simpa using this
  let v0 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let v1 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let a : ℝ := h v0
  let b : ℝ := h v1
  have hv0_neg_mem : (-1 : ℝ) • v0 ∈ exampleC := by
    have hneg : (-1 : ℝ) ≤ 0 := by linarith
    refine ⟨?_, ?_⟩
    · simp [v0]
    · have hmax : max (-1 : ℝ) 0 = 0 := by
        exact max_eq_right hneg
      simp [v0]
  have ha_nonneg : 0 ≤ a := by
    have hneg := hle ((-1 : ℝ) • v0) hv0_neg_mem
    have hneg' : h ((-1 : ℝ) • v0) = -a := by
      simp [a, v0]
    have : -a ≤ 0 := by
      simpa [hneg'] using hneg
    linarith
  have hv1_mem : v1 ∈ exampleC := by
    refine ⟨?_, ?_⟩
    · simp [v1]
    · simp [v1]
  have hb_nonpos : b ≤ 0 := by
    have hb := hle v1 hv1_mem
    simpa [b] using hb
  by_cases ha : a = 0
  · have hy_mem : (-1 : ℝ) • v0 ∈ maximizers exampleC h := by
      have hy_eq : h ((-1 : ℝ) • v0) = h (0 : EuclideanSpace ℝ (Fin 3)) := by
        have hneg' : h ((-1 : ℝ) • v0) = -a := by
          simp [a, v0]
        calc
          h ((-1 : ℝ) • v0) = -a := hneg'
          _ = 0 := by simp [ha]
          _ = h (0 : EuclideanSpace ℝ (Fin 3)) := by simp
      exact mem_maximizers_of_mem_of_eq_value
        (C := exampleC) (h := h) (x := 0) (x' := (-1 : ℝ) • v0) h0max hv0_neg_mem hy_eq
    have hy_ne : (-1 : ℝ) • v0 ≠ (0 : EuclideanSpace ℝ (Fin 3)) := by
      intro hzero
      have hcoord := congrArg (fun v => v 0) hzero
      simp [v0] at hcoord
    have hy_in_singleton : (-1 : ℝ) • v0 ∈ ({0} : Set (EuclideanSpace ℝ (Fin 3))) := by
      simpa [hFace_eq] using hy_mem
    exact hy_ne (by simpa using hy_in_singleton)
  · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (ne_comm.mp ha)
    have hb_neg : b < 0 := by
      by_contra hb0
      have hb0' : b = 0 := le_antisymm hb_nonpos (le_of_not_gt hb0)
      have hv0v1_mem : v0 + v1 ∈ exampleC := by
        refine ⟨?_, ?_⟩
        · simp [v0, v1]
        · simp [v0, v1]
      have hpos := hle (v0 + v1) hv0v1_mem
      have hcalc : h (v0 + v1) = a := by
        simp [a, b, v0, v1, hb0']
      have : a ≤ 0 := by
        simpa [hcalc] using hpos
      exact (lt_irrefl _ (lt_of_lt_of_le ha_pos this))
    let x0 : ℝ := -a / b
    have hx0_pos : 0 < x0 := by
      have hbpos : 0 < -b := by linarith
      have hx0' : 0 < a / (-b) := div_pos ha_pos hbpos
      have hx0_eq : x0 = a / (-b) := by
        simp [x0, div_neg, neg_div]
      simpa [hx0_eq] using hx0'
    let y : EuclideanSpace ℝ (Fin 3) := x0 • v0 + (x0 ^ 2) • v1
    have hy_mem : y ∈ exampleC := by
      have hx0_nonneg : 0 ≤ x0 := le_of_lt hx0_pos
      refine ⟨?_, ?_⟩
      · simp [y, v0, v1]
      · have hmax : max x0 0 = x0 := by
          exact max_eq_left hx0_nonneg
        simp [y, v0, v1, hmax]
    have hy_eq : h y = h (0 : EuclideanSpace ℝ (Fin 3)) := by
      have hcalc :
          h y = x0 * a + (x0 ^ 2) * b := by
        calc
          h y = h (x0 • v0) + h ((x0 ^ 2) • v1) := by
            simp [y]
          _ = x0 • h v0 + (x0 ^ 2) • h v1 := by
            simp
          _ = x0 * a + (x0 ^ 2) * b := by
            simp [a, b, smul_eq_mul]
      have hzero : x0 * a + (x0 ^ 2) * b = 0 := by
        have hb_ne : b ≠ 0 := ne_of_lt hb_neg
        have hlin : a + b * x0 = 0 := by
          dsimp [x0]
          have hmul : b * (-a / b) = -a := by
            field_simp [hb_ne]
          calc
            a + b * (-a / b) = a + (-a) := by
              simp [hmul]
            _ = 0 := by ring
        calc
          x0 * a + (x0 ^ 2) * b
              = x0 * (a + b * x0) := by
                  ring
          _ = x0 * 0 := by
                  simp [hlin]
          _ = 0 := by simp
      simp [hcalc, hzero]
    have hy_max : y ∈ maximizers exampleC h :=
      mem_maximizers_of_mem_of_eq_value
        (C := exampleC) (h := h) (x := 0) (x' := y) h0max hy_mem hy_eq
    have hy_ne : y ≠ (0 : EuclideanSpace ℝ (Fin 3)) := by
      intro hzero
      have hcoord := congrArg (fun v => v 0) hzero
      have : x0 = 0 := by
        simpa [y, v0, v1] using hcoord
      have hx0_eq : (0 : ℝ) = x0 := by
        simpa using this.symm
      linarith [hx0_pos, hx0_eq]
    have hy_in_singleton : y ∈ ({0} : Set (EuclideanSpace ℝ (Fin 3))) := by
      simpa [hFace_eq] using hy_max
    exact hy_ne (by simpa using hy_in_singleton)

/-- Text 18.0.11 (Not every extreme point is an exposed point). In general, an extreme point of a
convex set need not be an exposed point. A concrete example is obtained by taking `C` to be the
convex hull of a torus in `ℝ³`: if `D` is the flat disk forming the “top” face of `C`, then any
point on the relative boundary (rim) of `D` is an extreme point of `C` but is not an exposed point
of `C`. -/
theorem exists_isExtremePoint_not_isExposedPoint :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 3))) (x : EuclideanSpace ℝ (Fin 3)),
      Convex ℝ C ∧ IsExtremePoint (𝕜 := ℝ) C x ∧ ¬ IsExposedPoint C x := by
  refine ⟨exampleC, 0, convex_exampleC, isExtremePoint_origin_exampleC, ?_⟩
  simpa using not_isExposedPoint_origin_exampleC

end Maximizers

/-- Text 18.0.12 (Transitivity of Faces). Let `C` be a convex set.

(1) If `C''` is a face of `C'` and `C'` is a face of `C`, then `C''` is a face of `C`.

(2) In particular, if `x` is an extreme point of a face `C'` of `C`, then `x` is an extreme point
of `C`. -/
theorem isFace_trans {C C' C'' : Set E} (hC' : IsFace (𝕜 := 𝕜) C C') (hC'' : IsFace (𝕜 := 𝕜) C' C'') :
    IsFace (𝕜 := 𝕜) C C'' := by
  refine ⟨hC'.1, ?_⟩
  exact IsExtreme.trans (hAB := hC'.2) (hBC := hC''.2)

theorem isExtremePoint_of_isFace_of_isExtremePoint {C C' : Set E} {x : E} (hC' : IsFace (𝕜 := 𝕜) C C')
    (hx : IsExtremePoint (𝕜 := 𝕜) C' x) : IsExtremePoint (𝕜 := 𝕜) C x := by
  refine ⟨hC'.2.subset hx.1, ?_⟩
  intro y z hy hz hxyz
  have hy' : y ∈ C' :=
    hC'.2.left_mem_of_mem_openSegment (x := y) (y := z) (z := x) hy hz hx.1 hxyz
  have hz' : z ∈ C' :=
    IsExtreme.right_mem_of_mem_openSegment (h := hC'.2) (x := y) (y := z) (z := x) hy hz hx.1 hxyz
  exact hx.2 hy' hz' hxyz

/-- Text 18.0.13. If `C'` is a face of `C`, and `D` is a convex set satisfying `C' ⊆ D ⊆ C`, then
`C'` is also a face of `D`. -/
theorem isFace_of_isFace_of_subset {C C' D : Set E} (hC' : IsFace (𝕜 := 𝕜) C C') (hD : Convex 𝕜 D)
    (hC'D : C' ⊆ D) (hDC : D ⊆ C) :
    IsFace (𝕜 := 𝕜) D C' := by
  refine ⟨hD, ?_⟩
  exact IsExtreme.mono (hAC := hC'.2) (hBA := hDC) (hCB := hC'D)

/-- If `t > 0` and `y = z + t • (z - x)`, then `z` is in the open segment from `x` to `y`. -/
lemma mem_openSegment_of_point_beyond {n : ℕ} {x z y : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (ht : 0 < t) (hy : y = z + t • (z - x)) :
    z ∈ openSegment ℝ x y := by
  have hpos : 0 < (1 + t) := by linarith
  have hne : (1 + t) ≠ 0 := by linarith
  let a : ℝ := t / (1 + t)
  let b : ℝ := 1 / (1 + t)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos ht hpos
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos one_pos hpos
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [a, b, hne]
    simp [add_comm]
  refine ⟨a, b, ha, hb, hab, ?_⟩
  have hxcoeff : a - b * t = (0 : ℝ) := by
    dsimp [a, b]
    field_simp [a, b, hne]
    simp
  have hzcoeff : b + b * t = (1 : ℝ) := by
    dsimp [a, b]
    field_simp [a, b, hne]
  calc
    a • x + b • y
        = a • x + b • (z + t • (z - x)) := by simp [hy]
    _ = a • x + b • z + (b * t) • (z - x) := by
          simp [smul_add, smul_smul, add_assoc]
    _ = a • x + b • z + ((b * t) • z - (b * t) • x) := by
          simp [smul_sub, add_assoc]
    _ = (a • x - (b * t) • x) + (b • z + (b * t) • z) := by
          abel
    _ = (a - b * t) • x + (b + b * t) • z := by
          simp [sub_smul, add_smul]
    _ = z := by
          simp [hxcoeff, hzcoeff]

/-- From `z ∈ ri D` and `x ∈ D`, `x ≠ z`, build `y ∈ D` with `z` in the open segment `x–y`. -/
lemma exists_mem_openSegment_of_mem_euclideanRelativeInterior {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {z x : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ euclideanRelativeInterior n D) (hx : x ∈ D) (hxz : x ≠ z) :
    ∃ y ∈ D, z ∈ openSegment ℝ x y := by
  rcases hz with ⟨hz_aff, ε, hε, hsubset⟩
  have hx_aff : x ∈ affineSpan ℝ D := (subset_affineSpan ℝ D) hx
  let v : EuclideanSpace ℝ (Fin n) := z - x
  have hv : v ≠ 0 := by
    intro hv
    apply hxz
    have hzx : z = x := sub_eq_zero.mp (by simpa [v] using hv)
    exact hzx.symm
  have hvpos : 0 < ‖v‖ := by
    simpa [v] using (norm_pos_iff.mpr hv)
  let t : ℝ := (ε / 2) / ‖v‖
  have htpos : 0 < t := by
    have hεhalf : 0 < ε / 2 := by linarith
    exact div_pos hεhalf hvpos
  let y : EuclideanSpace ℝ (Fin n) := z + t • v
  have hnorm : ‖t • v‖ ≤ ε := by
    have htnonneg : 0 ≤ t := le_of_lt htpos
    calc
      ‖t • v‖ = |t| * ‖v‖ := by
        simpa [Real.norm_eq_abs] using (norm_smul t v)
      _ = t * ‖v‖ := by
        simp [abs_of_nonneg htnonneg]
      _ = ε / 2 := by
        dsimp [t]
        have hvne : ‖v‖ ≠ 0 := ne_of_gt hvpos
        field_simp [hvne]
      _ ≤ ε := by linarith
  have hmem_ball : t • v ∈ ε • euclideanUnitBall n := by
    have hmem : t • v ∈ {y | ‖y‖ ≤ ε} := by
      exact hnorm
    have hball :
        {y | ‖y‖ ≤ ε} = ε • euclideanUnitBall n :=
      euclidean_normBall_eq_smul_unitBall n ε (le_of_lt hε)
    simpa [hball] using hmem
  have hvdir : z -ᵥ x ∈ (affineSpan ℝ D).direction :=
    AffineSubspace.vsub_mem_direction hz_aff hx_aff
  have hy_aff' :
      (t • (z -ᵥ x)) +ᵥ z ∈ affineSpan ℝ D :=
    AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.smul_mem _ _ hvdir) hz_aff
  have hy_aff : y ∈ affineSpan ℝ D := by
    simpa [y, v, vadd_eq_add, vsub_eq_sub, add_comm, add_left_comm, add_assoc] using hy_aff'
  have hy_ball : y ∈ (fun y => z + y) '' (ε • euclideanUnitBall n) := by
    refine ⟨t • v, hmem_ball, ?_⟩
    simp [y]
  have hy_mem : y ∈ D := hsubset ⟨hy_ball, hy_aff⟩
  have hy_seg : z ∈ openSegment ℝ x y := by
    have hy' : y = z + t • (z - x) := by
      simp [y, v]
    exact mem_openSegment_of_point_beyond (x := x) (z := z) (y := y) htpos hy'
  exact ⟨y, hy_mem, hy_seg⟩

/-- Theorem 18.1. Let `C` be a convex set, and let `C'` be a face of `C`. If `D` is a convex set
in `C` such that `ri D` meets `C'`, then `D ⊆ C'`. -/
theorem subset_of_isFace_of_convex_of_euclideanRelativeInterior_inter {n : ℕ}
    {C C' D : Set (EuclideanSpace ℝ (Fin n))} (hC' : IsFace (𝕜 := ℝ) C C')
    (hDC : D ⊆ C) (hri : (euclideanRelativeInterior n D ∩ C').Nonempty) :
    D ⊆ C' := by
  rcases hri with ⟨z, hz⟩
  rcases hz with ⟨hzri, hzC'⟩
  intro x hxD
  by_cases hxz : x = z
  · simpa [hxz] using hzC'
  · rcases exists_mem_openSegment_of_mem_euclideanRelativeInterior (z := z) (x := x) hzri hxD hxz
      with ⟨y, hyD, hzseg⟩
    have hxC : x ∈ C := hDC hxD
    have hyC : y ∈ C := hDC hyD
    exact hC'.2.left_mem_of_mem_openSegment hxC hyC hzC' hzseg

/-- Relative interior of a nonempty convex set in `ℝⁿ` is nonempty. -/
lemma euclideanRelativeInterior_nonempty_of_convex_of_nonempty {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C) (hCne : C.Nonempty) :
    (euclideanRelativeInterior n C).Nonempty := by
  rcases euclideanRelativeInterior_closure_convex_affineSpan n C hC with
    ⟨_hconv_closure, _hconv_ri, _haff_closure, _haff_ri, hri_nonempty⟩
  exact hri_nonempty hCne

/-- Relative interior is monotone under inclusion when affine spans coincide. -/
lemma euclideanRelativeInterior_mono_of_subset_of_affineSpan_eq {n : ℕ}
    {A B : Set (EuclideanSpace ℝ (Fin n))} (hAB : A ⊆ B)
    (haff : affineSpan ℝ A = affineSpan ℝ B) :
    euclideanRelativeInterior n A ⊆ euclideanRelativeInterior n B := by
  intro x hx
  rcases hx with ⟨hx_aff, ε, hε, hxsub⟩
  refine ⟨?_, ε, hε, ?_⟩
  · simpa [haff] using hx_aff
  · intro y hy
    have hy' :
        y ∈ ((fun y => x + y) '' (ε • euclideanUnitBall n)) ∩
          (affineSpan ℝ A : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa [haff.symm] using hy
    exact hAB (hxsub hy')

/-- The affine span of `C ∩ closure C'` equals the affine span of `C'` when `C' ⊆ C`. -/
lemma affineSpan_inter_closure_eq_affineSpan {n : ℕ}
    {C C' : Set (EuclideanSpace ℝ (Fin n))} (hC' : C' ⊆ C) :
    affineSpan ℝ (C ∩ closure C') = affineSpan ℝ C' := by
  have hspan : affineSpan ℝ (closure C') = affineSpan ℝ C' := by
    simpa using (affineSpan_closure_eq (n := n) C')
  apply le_antisymm
  · have hmono :
      affineSpan ℝ (C ∩ closure C') ≤ affineSpan ℝ (closure C') := by
        exact affineSpan_mono ℝ (by intro x hx; exact hx.2)
    simpa [hspan] using hmono
  · have hsubset : C' ⊆ C ∩ closure C' := by
      intro x hx
      exact ⟨hC' hx, subset_closure hx⟩
    exact affineSpan_mono ℝ hsubset

/-- Corollary 18.1.1. If `C'` is a face of a convex set `C`, then `C' = C ∩ closure C'`. In
particular, if `C` is closed, then `C'` is closed. -/
theorem isFace_eq_inter_closure {n : ℕ} {C C' : Set (EuclideanSpace ℝ (Fin n))}
    (hC' : IsFace (𝕜 := ℝ) C C') (hC'conv : Convex ℝ C') :
    C' = C ∩ closure C' := by
  by_cases hC'empty : C' = ∅
  · simp [hC'empty]
  have hC'ne : C'.Nonempty := Set.nonempty_iff_ne_empty.mpr hC'empty
  apply le_antisymm
  · intro x hx
    exact ⟨hC'.2.subset hx, subset_closure hx⟩
  · let D : Set (EuclideanSpace ℝ (Fin n)) := C ∩ closure C'
    have hC'subD : C' ⊆ D := by
      intro x hx
      exact ⟨hC'.2.subset hx, subset_closure hx⟩
    have haff : affineSpan ℝ D = affineSpan ℝ C' :=
      affineSpan_inter_closure_eq_affineSpan (C := C) (C' := C') hC'.2.subset
    have hriC' : (euclideanRelativeInterior n C').Nonempty :=
      euclideanRelativeInterior_nonempty_of_convex_of_nonempty hC'conv hC'ne
    rcases hriC' with ⟨z, hzri⟩
    have hzC' : z ∈ C' := (euclideanRelativeInterior_subset_closure n C').1 hzri
    have hzriD : z ∈ euclideanRelativeInterior n D :=
      (euclideanRelativeInterior_mono_of_subset_of_affineSpan_eq
        (A := C') (B := D) hC'subD haff.symm) hzri
    have hri : (euclideanRelativeInterior n D ∩ C').Nonempty :=
      ⟨z, ⟨hzriD, hzC'⟩⟩
    have hDsub : D ⊆ C' :=
      subset_of_isFace_of_convex_of_euclideanRelativeInterior_inter
        (C := C) (C' := C') (D := D) hC' (by intro x hx; exact hx.1) hri
    intro x hx
    exact hDsub hx

/-- Corollary 18.1.1. If `C'` is a face of a closed convex set `C`, then `C'` is closed. -/
theorem isClosed_of_isFace {n : ℕ} {C C' : Set (EuclideanSpace ℝ (Fin n))}
    (hC' : IsFace (𝕜 := ℝ) C C') (hC'conv : Convex ℝ C') (hC : IsClosed C) :
    IsClosed C' := by
  have hEq : C' = C ∩ closure C' :=
    isFace_eq_inter_closure (C := C) (C' := C') hC' hC'conv
  have hclosed : IsClosed (C ∩ closure C') := hC.inter isClosed_closure
  exact hEq ▸ hclosed

/-- If `C'` and `D` are faces of `C` and `ri D` meets `C'`, then `D ⊆ C'`. -/
lemma subset_of_isFace_of_isFace_of_ri_inter {n : ℕ}
    {C C' D : Set (EuclideanSpace ℝ (Fin n))} (hC' : IsFace (𝕜 := ℝ) C C')
    (hD : IsFace (𝕜 := ℝ) C D)
    (hri : (euclideanRelativeInterior n D ∩ C').Nonempty) :
    D ⊆ C' := by
  exact subset_of_isFace_of_convex_of_euclideanRelativeInterior_inter
    (C := C) (C' := C') (D := D) hC' hD.2.subset hri

/-- Corollary 18.1.2. If `C'` and `C''` are faces of a convex set `C` such that `ri C'` and `ri C''`
have a point in common, then actually `C' = C''`. -/
theorem isFace_eq_of_euclideanRelativeInterior_inter {n : ℕ}
    {C C' C'' : Set (EuclideanSpace ℝ (Fin n))} (hC' : IsFace (𝕜 := ℝ) C C')
    (hC'' : IsFace (𝕜 := ℝ) C C'')
    (hri : (euclideanRelativeInterior n C' ∩ euclideanRelativeInterior n C'').Nonempty) :
    C' = C'' := by
  rcases hri with ⟨z, hz⟩
  have hzC' : z ∈ C' := (euclideanRelativeInterior_subset_closure n C').1 hz.1
  have hzC'' : z ∈ C'' := (euclideanRelativeInterior_subset_closure n C'').1 hz.2
  have hriC''C' : (euclideanRelativeInterior n C'' ∩ C').Nonempty :=
    ⟨z, ⟨hz.2, hzC'⟩⟩
  have hriC'C'' : (euclideanRelativeInterior n C' ∩ C'').Nonempty :=
    ⟨z, ⟨hz.1, hzC''⟩⟩
  have hsub1 : C'' ⊆ C' :=
    subset_of_isFace_of_isFace_of_ri_inter (C := C) (C' := C') (D := C'') hC' hC'' hriC''C'
  have hsub2 : C' ⊆ C'' :=
    subset_of_isFace_of_isFace_of_ri_inter (C := C) (C' := C'') (D := C') hC'' hC' hriC'C''
  exact Set.Subset.antisymm hsub2 hsub1

/-- If `ri C` meets a face `C'`, then `C' = C`. -/
lemma isFace_eq_of_euclideanRelativeInterior_inter_self {n : ℕ}
    {C C' : Set (EuclideanSpace ℝ (Fin n))} (hC' : IsFace (𝕜 := ℝ) C C')
    (hri : (euclideanRelativeInterior n C ∩ C').Nonempty) :
    C' = C := by
  have hsub : C ⊆ C' :=
    subset_of_isFace_of_convex_of_euclideanRelativeInterior_inter
      (C := C) (C' := C') (D := C) hC' (by intro x hx; exact hx) hri
  exact Set.Subset.antisymm hC'.2.subset hsub

/-- Corollary 18.1.3. Let `C` be a convex set, and let `C'` be a face of `C` other than `C` itself.
Then `C'` is entirely contained in the relative boundary of `C`. -/
theorem isFace_subset_euclideanRelativeBoundary_of_ne {n : ℕ}
    {C C' : Set (EuclideanSpace ℝ (Fin n))} (hC' : IsFace (𝕜 := ℝ) C C') (hne : C' ≠ C) :
    C' ⊆ euclideanRelativeBoundary n C := by
  intro x hxC'
  have hxC : x ∈ C := hC'.2.subset hxC'
  have hxcl : x ∈ closure C := subset_closure hxC
  have hxnotri : x ∉ euclideanRelativeInterior n C := by
    intro hxri
    have hri : (euclideanRelativeInterior n C ∩ C').Nonempty :=
      ⟨x, ⟨hxri, hxC'⟩⟩
    exact hne (isFace_eq_of_euclideanRelativeInterior_inter_self hC' hri)
  simpa [euclideanRelativeBoundary] using And.intro hxcl hxnotri

/-- Corollary 18.1.3. Let `C` be a convex set, and let `C'` be a face of `C` other than `C` itself.
Then `dim C' < dim C` (formalized as a strict inequality between the finranks of the directions of
the affine spans of `C'` and `C`). -/
theorem finrank_direction_affineSpan_lt_of_isFace_ne {n : ℕ}
    {C C' : Set (EuclideanSpace ℝ (Fin n))} (hC' : IsFace (𝕜 := ℝ) C C') (hne : C' ≠ C)
    (hC'conv : Convex ℝ C') (hC'ne : C'.Nonempty) (hCne : C.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ C').direction < Module.finrank ℝ (affineSpan ℝ C).direction := by
  exact euclidean_dim_lt_of_convex_subset_relativeBoundary n C' C hC'conv hC'.1 hC'ne hCne
    (isFace_subset_euclideanRelativeBoundary_of_ne (C := C) (C' := C') hC' hne)

/-- The type of faces of a set `C`, using the predicate `IsFace (𝕜 := 𝕜) C`. -/
def FaceOf (C : Set E) : Type _ :=
  {C' : Set E // IsFace (𝕜 := 𝕜) C C'}

/-- Faces are ordered by inclusion of their carriers. -/
instance FaceOf.instPartialOrder (C : Set E) : PartialOrder (FaceOf (𝕜 := 𝕜) C) where
  le F G := F.1 ⊆ G.1
  le_refl F := by
    intro x hx
    exact hx
  le_trans F G H hFG hGH := by
    intro x hx
    exact hGH (hFG hx)
  le_antisymm F G hFG hGF := by
    apply Subtype.ext
    exact Set.Subset.antisymm hFG hGF

/-- The infimum of a set of faces, defined by intersecting all faces (and `C`). -/
def FaceOf.sInf (C : Set E) (hC : Convex 𝕜 C) (S : Set (FaceOf (𝕜 := 𝕜) C)) :
    FaceOf (𝕜 := 𝕜) C := by
  classical
  refine ⟨⋂ i : Option {F // F ∈ S}, (match i with | none => C | some F => (F.1.1 : Set E)), ?_⟩
  refine ⟨hC, ?_⟩
  haveI : Nonempty (Option {F // F ∈ S}) := ⟨none⟩
  refine isExtreme_iInter (A := C) ?_
  intro i
  cases i with
  | none =>
      simpa using (IsExtreme.refl (𝕜 := 𝕜) (A := C))
  | some F =>
      exact F.1.2.2

/-- The infimum defined above is a greatest lower bound. -/
lemma FaceOf.isGLB_sInf (C : Set E) (hC : Convex 𝕜 C) (S : Set (FaceOf (𝕜 := 𝕜) C)) :
    IsGLB S (FaceOf.sInf (𝕜 := 𝕜) C hC S) := by
  classical
  refine ⟨?_, ?_⟩
  · intro F hF x hx
    have hx' : x ∈ ⋂ i : Option {F // F ∈ S},
        (match i with | none => C | some F => (F.1.1 : Set E)) := by
      simpa [FaceOf.sInf] using hx
    have hx'' := (Set.mem_iInter.mp hx') (some ⟨F, hF⟩)
    simpa using hx''
  · intro B hB
    have hB' : ∀ F ∈ S, B ≤ F := by
      simpa [lowerBounds] using hB
    intro x hxB
    have hx' : ∀ i : Option {F // F ∈ S},
        x ∈ (match i with | none => C | some F => (F.1.1 : Set E)) := by
      intro i
      cases i with
      | none =>
          exact B.2.2.subset hxB
      | some F =>
          exact (hB' F.1 F.2) hxB
    have hx'' : x ∈ ⋂ i : Option {F // F ∈ S},
        (match i with | none => C | some F => (F.1.1 : Set E)) :=
      Set.mem_iInter_of_mem hx'
    simpa [FaceOf.sInf] using hx''

/-- Text 18.1.1 (Lattice Structure of Faces). Let `C` be a convex set in `ℝⁿ`, and let `𝓕(C)` be
the collection of all faces of `C`. Ordered by set inclusion `⊆`, `𝓕(C)` is a complete lattice.
Moreover, every strictly decreasing chain of faces in `𝓕(C)` has finite length (equivalently:
there is no infinite strictly decreasing sequence of faces). -/
theorem faces_completeLattice {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC : Convex ℝ C) :
    ∃ inst : CompleteLattice (FaceOf (𝕜 := ℝ) C),
      (letI := inst
      ∀ F G : FaceOf (𝕜 := ℝ) C, (F ≤ G ↔ F.1 ⊆ G.1)) := by
  classical
  letI : InfSet (FaceOf (𝕜 := ℝ) C) :=
    ⟨fun S => FaceOf.sInf (𝕜 := ℝ) C hC S⟩
  have hGLB :
      ∀ S : Set (FaceOf (𝕜 := ℝ) C), IsGLB S (sInf S) := by
    intro S
    simpa using (FaceOf.isGLB_sInf (𝕜 := ℝ) (C := C) hC S)
  let inst : CompleteLattice (FaceOf (𝕜 := ℝ) C) :=
    completeLatticeOfInf (FaceOf (𝕜 := ℝ) C) hGLB
  refine ⟨inst, ?_⟩
  intro F G
  rfl

/-- Text 18.1.1 (Lattice Structure of Faces): there is no infinite strictly decreasing chain of
faces of a convex set (formulated as the nonexistence of a sequence `f : ℕ → Set` of faces with
`f (k+1) ⊂ f k` for all `k`). -/
theorem not_exists_faces_strictlyDecreasingChain {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    ¬ ∃ f : ℕ → Set (EuclideanSpace ℝ (Fin n)),
        (∀ k, IsFace (𝕜 := ℝ) C (f k)) ∧ (∀ k, Convex ℝ (f k)) ∧ (∀ k, f (k + 1) ⊂ f k) := by
  rintro ⟨f, hfFace, hfConvex, hfChain⟩
  let d : ℕ → ℕ := fun k =>
    Module.finrank ℝ (affineSpan ℝ (f k)).direction
  have hdim : ∀ k, d (k + 1) < d k := by
    intro k
    have hsubsetCk : f k ⊆ C := (hfFace k).2.subset
    have hsubset : f (k + 1) ⊆ f k :=
      (Set.ssubset_iff_subset_ne).1 (hfChain k) |>.1
    have hExtreme : IsExtreme ℝ (f k) (f (k + 1)) :=
      IsExtreme.mono (hAC := (hfFace (k + 1)).2) (hBA := hsubsetCk) (hCB := hsubset)
    have hFace' : IsFace (𝕜 := ℝ) (f k) (f (k + 1)) := ⟨hfConvex k, hExtreme⟩
    have hne : f (k + 1) ≠ f k :=
      (Set.ssubset_iff_subset_ne).1 (hfChain k) |>.2
    have hCne : (f k).Nonempty := Set.nonempty_of_ssubset' (hfChain k)
    have hC'ne : (f (k + 1)).Nonempty := Set.nonempty_of_ssubset' (hfChain (k + 1))
    exact
      finrank_direction_affineSpan_lt_of_isFace_ne (C := f k) (C' := f (k + 1)) hFace' hne
        (hfConvex (k + 1)) hC'ne hCne
  have hne : (Set.range d).Nonempty := ⟨d 0, ⟨0, rfl⟩⟩
  set m : ℕ := WellFounded.min Nat.lt_wfRel.wf (Set.range d) hne
  have hm_mem : m ∈ Set.range d := by
    simpa [m] using (WellFounded.min_mem Nat.lt_wfRel.wf (Set.range d) hne)
  rcases hm_mem with ⟨k, hk⟩
  have hmk : d (k + 1) < m := by
    simpa [hk] using hdim k
  have hmem : d (k + 1) ∈ Set.range d := ⟨k + 1, rfl⟩
  have hnot : ¬ d (k + 1) < m := by
    intro hlt
    have hnot' := WellFounded.not_lt_min Nat.lt_wfRel.wf (Set.range d) hne hmem
    exact hnot' (by simpa [m] using hlt)
  exact hnot hmk

section Exposed

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- If `D ⊆ C` contains all maximizers of `h` on `C`, then the maximizers on `D` are exactly the
maximizers on `C`, provided the maximizers on `C` are nonempty. -/
lemma maximizers_eq_inter_of_subset_of_nonempty {C D : Set F} (h : F →ₗ[ℝ] ℝ) (hDC : D ⊆ C)
    (hmax : maximizers C h ⊆ D) (hnonempty : (maximizers C h).Nonempty) :
    maximizers D h = maximizers C h ∩ D := by
  ext x; constructor
  · intro hx
    rcases hnonempty with ⟨x0, hx0⟩
    rcases hx with ⟨hxD, hxmaxD⟩
    have hx0D : x0 ∈ D := hmax hx0
    have hx0_max : ∀ y ∈ C, h y ≤ h x0 := (isMaxOn_iff).1 hx0.2
    have hx_max : ∀ y ∈ D, h y ≤ h x := (isMaxOn_iff).1 hxmaxD
    have hx0_le_x : h x0 ≤ h x := hx_max x0 hx0D
    have hxC : ∀ y ∈ C, h y ≤ h x := by
      intro y hyC
      exact le_trans (hx0_max y hyC) hx0_le_x
    have hxC' : IsMaxOn (fun x => h x) C x := (isMaxOn_iff).2 hxC
    have hxCmem : x ∈ C := hDC hxD
    exact ⟨⟨hxCmem, hxC'⟩, hxD⟩
  · intro hx
    rcases hx with ⟨hxC, hxD⟩
    have hxmaxD : IsMaxOn (fun x => h x) D x := IsMaxOn.on_subset hxC.2 hDC
    exact ⟨hxD, hxmaxD⟩

/-- Text 18.0.13. If `C'` is exposed in `C`, and `D` is a convex set satisfying `C' ⊆ D ⊆ C`, then
`C'` is also exposed in `D` (assuming `C'` is nonempty). -/
theorem isExposedFace_of_isExposedFace_of_subset {C C' D : Set F}
    (hC' : IsExposedFace (C := C) C') (hC'nonempty : C'.Nonempty) (hD : Convex ℝ D) (hC'D : C' ⊆ D)
    (hDC : D ⊆ C) :
    IsExposedFace (C := D) C' := by
  rcases hC' with ⟨_, _, ⟨h, hC'Eq⟩⟩
  refine ⟨hD, hC'D, ?_⟩
  refine ⟨h, ?_⟩
  have hmax : maximizers C h ⊆ D := by
    intro x hx
    have hx' : x ∈ C' := by
      simpa [hC'Eq] using hx
    exact hC'D hx'
  have hnonempty : (maximizers C h).Nonempty := by
    rcases hC'nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [hC'Eq] using hx
  have hEq : maximizers D h = maximizers C h ∩ D :=
    maximizers_eq_inter_of_subset_of_nonempty (h := h) hDC hmax hnonempty
  calc
    C' = maximizers C h := hC'Eq
    _ = maximizers C h ∩ D := by
      symm
      exact Set.inter_eq_left.mpr hmax
    _ = maximizers D h := by
      symm
      exact hEq

end Exposed

/-- Nonnegative scaling preserves membership in a recession cone. -/
lemma smul_mem_recessionCone_of_mem {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {y : E}
    (hy : y ∈ Set.recessionCone C) {t : ℝ} (ht : 0 ≤ t) :
    t • y ∈ Set.recessionCone C := by
  intro x hx s hs
  have hst : 0 ≤ s * t := mul_nonneg hs ht
  have hmem := hy hx hst
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hmem

/-- An extreme direction yields a recession direction for closed convex sets in `ℝⁿ`. -/
lemma mem_recessionCone_of_isExtremeDirection {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C) {d : EuclideanSpace ℝ (Fin n)}
    (hd : IsExtremeDirection (𝕜 := ℝ) C d) :
    d ∈ Set.recessionCone C := by
  rcases hd with ⟨C', hhalf, hdir⟩
  rcases hhalf with ⟨hface, _⟩
  rcases hdir with ⟨x0, hdne, hC'Eq⟩
  have hdir' : IsDirectionOf (𝕜 := ℝ) C' d := ⟨x0, hdne, hC'Eq⟩
  have hsubset : C' ⊆ C := hface.2.subset
  have hx0C' : x0 ∈ C' := by
    have : x0 + (0 : ℝ) • d ∈ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) :=
      ⟨0, by simp, by simp⟩
    simpa [hC'Eq] using this
  have hx0C : x0 ∈ C := hsubset hx0C'
  have hCne : C.Nonempty := ⟨x0, hx0C⟩
  have hconv : Convex ℝ C := hface.1
  have hex : ∃ x, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C := by
    refine ⟨x0, ?_⟩
    intro t ht
    have : x0 + t • d ∈ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) :=
      ⟨t, ht, rfl⟩
    exact hsubset (by simpa [hC'Eq] using this)
  exact
    (recessionCone_of_exists_halfline (n := n) (C := C) hCne hCclosed hconv (y := d) hdne hex).1

/-- Text 18.0.14. Every extreme direction (and every exposed direction) of a closed convex set `C`
is also an extreme direction (respectively: exposed direction) of the recession cone `0⁺ C`
(formalized as `Set.recessionCone C`); however, the converse implication does not hold in general. -/
theorem isExtremeDirection_recessionCone_of_isExtremeDirection {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCclosed : IsClosed C)
    {d : EuclideanSpace ℝ (Fin n)} (hd : IsExtremeDirection (𝕜 := ℝ) C d) :
    IsExtremeDirection (𝕜 := ℝ) (Set.recessionCone C) d := by
  rcases hd with ⟨C', hhalf, hdir⟩
  rcases hhalf with ⟨hface, _⟩
  rcases hdir with ⟨x0, hdne, hC'Eq⟩
  have hdir' : IsDirectionOf (𝕜 := ℝ) C' d := ⟨x0, hdne, hC'Eq⟩
  have hsubset : C' ⊆ C := hface.2.subset
  have hx0C' : x0 ∈ C' := by
    have : x0 + (0 : ℝ) • d ∈ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) :=
      ⟨0, by simp, by simp⟩
    simpa [hC'Eq] using this
  have hx0C : x0 ∈ C := hsubset hx0C'
  have hconv : Convex ℝ C := hface.1
  have hhalf' : IsHalfLineFace (𝕜 := ℝ) C C' := ⟨hface, ⟨d, hdir'⟩⟩
  have hdrec : d ∈ Set.recessionCone C :=
    mem_recessionCone_of_isExtremeDirection (hCclosed := hCclosed) ⟨C', hhalf', hdir'⟩
  let R : Set (EuclideanSpace ℝ (Fin n)) := (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ)
  have hdirR : IsDirectionOf (𝕜 := ℝ) R d := by
    refine ⟨0, hdne, ?_⟩
    simp [R]
  refine ⟨R, ?_, hdirR⟩
  refine ⟨?_, ⟨d, hdirR⟩⟩
  refine ⟨recessionCone_convex (C := C) hconv, ?_⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact smul_mem_recessionCone_of_mem hdrec ht
  · intro u hu v hv z hz hseg
    have hx0uC : x0 + u ∈ C := by
      have := hu hx0C (t := (1 : ℝ)) (by exact zero_le_one)
      simpa using this
    have hx0vC : x0 + v ∈ C := by
      have := hv hx0C (t := (1 : ℝ)) (by exact zero_le_one)
      simpa using this
    have hx0zC' : x0 + z ∈ C' := by
      rcases hz with ⟨t, ht, rfl⟩
      have : x0 + t • d ∈ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) :=
        ⟨t, ht, rfl⟩
      simpa [hC'Eq] using this
    have hx0zseg :
        x0 + z ∈ openSegment ℝ (x0 + u) (x0 + v) := by
      exact
        (mem_openSegment_translate (𝕜 := ℝ) x0 (x := z) (b := u) (c := v)).2 hseg
    have hx0uC' : x0 + u ∈ C' :=
      hface.2.left_mem_of_mem_openSegment hx0uC hx0vC hx0zC' hx0zseg
    rcases (by simpa [hC'Eq] using hx0uC') with ⟨t, ht, ht_eq⟩
    exact ⟨t, ht, ht_eq⟩

/-- Exposed directions are extreme directions. -/
lemma isExtremeDirection_of_isExposedDirection {F : Type*} [AddCommGroup F] [Module ℝ F]
    {C : Set F} {d : F} (hd : IsExposedDirection C d) : IsExtremeDirection (𝕜 := ℝ) C d := by
  rcases hd with ⟨C', hhalf, hdir⟩
  exact ⟨C', hhalf.1, hdir⟩

/-- The parabola epigraph in `ℝ²`. -/
abbrev parabolaSet : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 1 ≥ (x 0) ^ 2}

/-- The vertical direction in `ℝ²`. -/
abbrev verticalDir : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]

/-- The parabola epigraph is convex. -/
lemma convex_parabola_set : Convex ℝ parabolaSet := by
  intro x hx y hy a b ha hb hab
  have hx' : x 1 ≥ (x 0) ^ 2 := by simpa [parabolaSet] using hx
  have hy' : y 1 ≥ (y 0) ^ 2 := by simpa [parabolaSet] using hy
  have hsq : (a * x 0 + b * y 0) ^ 2 ≤ a * (x 0) ^ 2 + b * (y 0) ^ 2 := by
    have hconv : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 2) := by
      simpa using (Even.convexOn_pow (n := 2) (by decide : Even (2 : ℕ)))
    have hx0 : x 0 ∈ (Set.univ : Set ℝ) := by simp
    have hy0 : y 0 ∈ (Set.univ : Set ℝ) := by simp
    have h := hconv.2 hx0 hy0 ha hb hab
    simpa [smul_eq_mul, pow_two] using h
  have hineq : a * x 1 + b * y 1 ≥ (a * x 0 + b * y 0) ^ 2 := by
    have h1 : a * (x 0) ^ 2 + b * (y 0) ^ 2 ≤ a * x 1 + b * y 1 := by
      nlinarith [hx', hy', ha, hb]
    exact le_trans hsq h1
  have hineq' : (a • x + b • y) 1 ≥ ((a • x + b • y) 0) ^ 2 := by
    simpa using hineq
  simpa [parabolaSet] using hineq'

/-- The parabola epigraph has no vertical half-line faces. -/
lemma parabola_no_vertical_halfLineFace {x0 : EuclideanSpace ℝ (Fin 2)}
    {C' : Set (EuclideanSpace ℝ (Fin 2))}
    (hC' : C' = (fun t : ℝ => x0 + t • verticalDir) '' Set.Ici (0 : ℝ)) :
    ¬ IsFace (𝕜 := ℝ) parabolaSet C' := by
  intro hface
  set s : ℝ := 2 * |x0 0| + 1
  have hs_nonneg : 0 ≤ s := by nlinarith [abs_nonneg (x0 0)]
  let m : EuclideanSpace ℝ (Fin 2) := x0 + s • verticalDir
  let p : EuclideanSpace ℝ (Fin 2) := !₂[x0 0 - 1, x0 1 + s]
  let q : EuclideanSpace ℝ (Fin 2) := !₂[x0 0 + 1, x0 1 + s]
  have hx0C' : x0 ∈ C' := by
    have hx0C' :
        x0 + (0 : ℝ) • verticalDir ∈ (fun t : ℝ => x0 + t • verticalDir) '' Set.Ici (0 : ℝ) :=
      ⟨0, by simp, by simp⟩
    rw [hC']
    convert hx0C' using 1
    · simp
  have hx0C : x0 ∈ parabolaSet := hface.2.subset hx0C'
  have hx0C1 : x0 1 ≥ (x0 0) ^ 2 := by simpa [parabolaSet] using hx0C
  have hpC : p ∈ parabolaSet := by
    have hle : -x0 0 ≤ |x0 0| := neg_le_abs (x0 0)
    have hineq : x0 1 + s ≥ (x0 0 - 1) ^ 2 := by
      nlinarith [hx0C1, hle]
    have hp' : p 1 ≥ (p 0) ^ 2 := by simpa [p] using hineq
    simpa [parabolaSet] using hp'
  have hqC : q ∈ parabolaSet := by
    have hle : x0 0 ≤ |x0 0| := le_abs_self (x0 0)
    have hineq : x0 1 + s ≥ (x0 0 + 1) ^ 2 := by
      nlinarith [hx0C1, hle]
    have hq' : q 1 ≥ (q 0) ^ 2 := by simpa [q] using hineq
    simpa [parabolaSet] using hq'
  have hmC' : m ∈ C' := by
    have : m ∈ (fun t : ℝ => x0 + t • verticalDir) '' Set.Ici (0 : ℝ) := ⟨s, hs_nonneg, rfl⟩
    simpa [m, hC'] using this
  have hmseg : m ∈ openSegment ℝ p q := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    fin_cases i
    · simp [m, p, q, verticalDir]
      ring
    · simp [m, p, q, verticalDir]
      ring
  have hpC' : p ∈ C' :=
    hface.2.left_mem_of_mem_openSegment (x := p) (y := q) (z := m) hpC hqC hmC' hmseg
  rcases (by simpa [hC'] using hpC') with ⟨t, ht, ht_eq⟩
  have hcoord : (x0 0 : ℝ) = x0 0 - 1 := by
    have hcoord' := congrArg (fun v => v 0) ht_eq
    simpa [p, verticalDir] using hcoord'
  linarith

/-- Text 18.0.14 (converse fails for extreme directions). There exists a closed convex set `C` and a
vector `d` such that `d` is an extreme direction of `0⁺ C` but not an extreme direction of `C`. -/
theorem exists_isExtremeDirection_recessionCone_not_isExtremeDirection :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 2))) (d : EuclideanSpace ℝ (Fin 2)),
      IsClosed C ∧ Convex ℝ C ∧
        IsExtremeDirection (𝕜 := ℝ) (Set.recessionCone C) d ∧ ¬ IsExtremeDirection (𝕜 := ℝ) C d := by
  classical
  let C : Set (EuclideanSpace ℝ (Fin 2)) := parabolaSet
  let d : EuclideanSpace ℝ (Fin 2) := verticalDir
  have hCclosed : IsClosed C := by
    simpa [C, parabolaSet] using isClosed_parabola
  have hCconv : Convex ℝ C := by
    simpa [C, parabolaSet] using convex_parabola_set
  have hdne : d ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
    intro hd0
    have h := congrArg (fun v => v 1) hd0
    have h' : (1 : ℝ) = 0 := by
      simp [d] at h
    exact one_ne_zero h'
  have hrec_eq' :
      Set.recessionCone C = {z : EuclideanSpace ℝ (Fin 2) | z 0 = 0 ∧ 0 ≤ z 1} := by
    simpa [C, parabolaSet] using recessionCone_parabola_eq
  have hRay :
      {z : EuclideanSpace ℝ (Fin 2) | z 0 = 0 ∧ 0 ≤ z 1} =
        (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ) := by
    ext z
    constructor
    · rintro ⟨hz0, hz1⟩
      refine ⟨z 1, hz1, ?_⟩
      ext i
      fin_cases i
      · simp [d, hz0]
      · simp [d]
    · rintro ⟨t, ht, rfl⟩
      have ht' : 0 ≤ t := by simpa using ht
      simp [d, verticalDir, ht']
  have hrec_eq : Set.recessionCone C = (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ) :=
    hrec_eq'.trans hRay
  have hdir : IsDirectionOf (𝕜 := ℝ) (Set.recessionCone C) d := by
    refine ⟨0, hdne, ?_⟩
    simpa using (hrec_eq : Set.recessionCone C = (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ))
  have hface : IsFace (𝕜 := ℝ) (Set.recessionCone C) (Set.recessionCone C) := by
    exact isFace_self (C := Set.recessionCone C) (recessionCone_convex (C := C) hCconv)
  have hhalf : IsHalfLineFace (𝕜 := ℝ) (Set.recessionCone C) (Set.recessionCone C) := by
    exact ⟨hface, ⟨d, hdir⟩⟩
  have hExtreme : IsExtremeDirection (𝕜 := ℝ) (Set.recessionCone C) d := by
    exact ⟨Set.recessionCone C, hhalf, hdir⟩
  have hnotExtreme : ¬ IsExtremeDirection (𝕜 := ℝ) C d := by
    intro hdext
    rcases hdext with ⟨C', hhalf', hdir'⟩
    rcases hdir' with ⟨x0, _hdne, hC'Eq⟩
    exact parabola_no_vertical_halfLineFace (x0 := x0) (C' := C') hC'Eq hhalf'.1
  exact ⟨C, d, hCclosed, hCconv, hExtreme, hnotExtreme⟩

end Section18
end Chap04
