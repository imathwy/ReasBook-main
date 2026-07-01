/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Suwan Wu, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part7

open scoped Pointwise

section Chap03
section Section11

/-- If `affineSpan ℝ C = ⊤`, then `intrinsicInterior ℝ C` agrees with the usual `interior C`. -/
lemma cor11_6_1_intrinsicInterior_eq_interior_of_affineSpan_eq_top {n : Nat}
    (C : Set (Fin n → Real)) (hspan : affineSpan ℝ C = ⊤) :
    intrinsicInterior ℝ C = interior C := by
  classical
  -- Reduce the affine span to `⊤`, so the intrinsic interior is taken in the subtype `Set.univ`.
  have h₁ :
      intrinsicInterior ℝ C =
        ((↑) : (↥(Set.univ : Set (Fin n → Real)) → (Fin n → Real))) ''
          interior (((↑) : (↥(Set.univ : Set (Fin n → Real)) → (Fin n → Real))) ⁻¹' C) := by
    rw [intrinsicInterior]
    rw [hspan]
    rfl
  -- Transport `interior` along the homeomorphism `(Set.univ : Set X) ≃ₜ X`.
  let e : (Set.univ : Set (Fin n → Real)) ≃ₜ (Fin n → Real) :=
    Homeomorph.Set.univ (Fin n → Real)
  have hpre :
      interior (e ⁻¹' C) = e ⁻¹' interior C := by
    simpa using (e.preimage_interior C).symm
  -- Finish by rewriting everything in terms of `e` and using `Equiv.image_preimage`.
  have h₂ :
      ((↑) : (↥(Set.univ : Set (Fin n → Real)) → (Fin n → Real))) ''
          interior (((↑) : (↥(Set.univ : Set (Fin n → Real)) → (Fin n → Real))) ⁻¹' C) =
        interior C := by
    -- `e.toEquiv` is `Equiv.Set.univ`, whose `toFun` is `Subtype.val`.
    calc
      ((↑) : (↥(Set.univ : Set (Fin n → Real)) → (Fin n → Real))) ''
          interior (((↑) : (↥(Set.univ : Set (Fin n → Real)) → (Fin n → Real))) ⁻¹' C)
          =
          e '' interior (e ⁻¹' C) := by
            rfl
      _ = e '' (e ⁻¹' interior C) := by simp [hpre]
      _ = interior C := by
            simp
  simpa [h₁] using h₂

/-- If `affineSpan ℝ C ≠ ⊤` and `0 < n`, then every point of `C` admits a nonzero normal
vector coming from a hyperplane containing `C`. -/
lemma cor11_6_1_exists_normal_of_affineSpan_ne_top {n : Nat} (hn : 0 < n)
    {C : Set (Fin n → Real)} (hspan : affineSpan ℝ C ≠ ⊤) :
    ∀ x, x ∈ C → ∃ b : Fin n → Real, b ≠ 0 ∧ ∀ y, y ∈ C → y ⬝ᵥ b ≤ x ⬝ᵥ b := by
  intro x hxC
  rcases
      exists_hyperplane_superset_affineSpan_of_affineSpan_ne_top (n := n) hn C hspan with
    ⟨b, β, hb0, hCsub, _hAsub⟩
  refine ⟨b, hb0, ?_⟩
  intro y hyC
  have hyEq : y ⬝ᵥ b = β := by simpa using hCsub hyC
  have hxEq : x ⬝ᵥ b = β := by simpa using hCsub hxC
  simp [hyEq, hxEq]

/-- If `affineSpan ℝ C = ⊤`, then a point in the (ambient) boundary of `C` is disjoint from the
intrinsic interior of `C` (as a singleton set). -/
lemma cor11_6_1_disjoint_singleton_intrinsicInterior_of_mem_frontier_of_affineSpan_eq_top
    {n : Nat} {C : Set (Fin n → Real)} (hspan : affineSpan ℝ C = ⊤) {x : Fin n → Real}
    (hxfr : x ∈ frontier C) :
    Disjoint ({x} : Set (Fin n → Real)) (intrinsicInterior ℝ C) := by
  classical
  have hri :
      intrinsicInterior ℝ C = interior C :=
    cor11_6_1_intrinsicInterior_eq_interior_of_affineSpan_eq_top (n := n) C hspan
  have hxnot : x ∉ intrinsicInterior ℝ C := by
    intro hxri
    have : x ∈ interior C := by simpa [hri] using hxri
    exact hxfr.2 this
  refine Set.disjoint_left.2 ?_
  intro z hz hxz
  have hz' : z = x := by simpa [Set.mem_singleton_iff] using hz
  subst hz'
  exact hxnot hxz

/-- From Theorem 11.6 (with `D = {x}`), extract a nonzero normal vector to `C` at `x`. -/
lemma cor11_6_1_exists_normal_of_disjoint_singleton_intrinsicInterior {n : Nat}
    {C : Set (Fin n → Real)} (hC : Convex Real C) {x : Fin n → Real} (hxC : x ∈ C)
    (hdisj : Disjoint ({x} : Set (Fin n → Real)) (intrinsicInterior ℝ C)) :
    ∃ b : Fin n → Real, b ≠ 0 ∧ ∀ y, y ∈ C → y ⬝ᵥ b ≤ x ⬝ᵥ b := by
  classical
  have hsubset : ({x} : Set (Fin n → Real)) ⊆ C := by
    intro z hz
    have hz' : z = x := by simpa [Set.mem_singleton_iff] using hz
    simpa [hz'] using hxC
  have hiff :=
    exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior (n := n)
      (C := C) (D := ({x} : Set (Fin n → Real))) hC (Set.singleton_nonempty x)
      (convex_singleton x) hsubset
  rcases (hiff.2 hdisj) with ⟨H, hHnontriv, hDH⟩
  rcases hHnontriv with ⟨hHsupport, _hCnot⟩
  rcases hHsupport with ⟨b, β, hb0, hHdef, hC_le, _hx_touch⟩
  have hxH : x ∈ H := hDH (by simp)
  have hxEq : x ⬝ᵥ b = β := by simpa [hHdef] using hxH
  have hxEq' : β = x ⬝ᵥ b := hxEq.symm
  refine ⟨b, hb0, ?_⟩
  intro y hyC
  have hyLe : y ⬝ᵥ b ≤ β := hC_le y hyC
  simpa [hxEq'] using hyLe

/-- Corollary 11.6.1. A convex set has a non-zero normal at each of its boundary points. -/
theorem exists_nonzero_normal_of_mem_frontier_of_convex (n : Nat) (C : Set (Fin n → Real))
    (hC : Convex Real C) :
    ∀ x, x ∈ C → x ∈ frontier C → ∃ b : Fin n → Real, b ≠ 0 ∧ ∀ y, y ∈ C → y ⬝ᵥ b ≤ x ⬝ᵥ b := by
  classical
  cases n with
  | zero =>
      intro x hxC hxfr
      haveI : Subsingleton (Fin 0 → Real) := by infer_instance
      have hCuniv : C = (Set.univ : Set (Fin 0 → Real)) := by
        ext y
        constructor
        · intro _hy
          trivial
        · intro _hy
          have hyx : y = x := Subsingleton.elim y x
          simpa [hyx] using hxC
      simp [hCuniv] at hxfr
  | succ n =>
      intro x hxC hxfr
      have hn : 0 < Nat.succ n := Nat.succ_pos n
      by_cases hspan : affineSpan ℝ C = ⊤
      · have hdisj :
            Disjoint ({x} : Set (Fin (Nat.succ n) → Real)) (intrinsicInterior ℝ C) :=
          cor11_6_1_disjoint_singleton_intrinsicInterior_of_mem_frontier_of_affineSpan_eq_top
            (n := Nat.succ n) (C := C) hspan hxfr
        exact
          cor11_6_1_exists_normal_of_disjoint_singleton_intrinsicInterior (n := Nat.succ n)
            (C := C) hC (x := x) hxC hdisj
      · exact
          cor11_6_1_exists_normal_of_affineSpan_ne_top (n := Nat.succ n) hn (C := C)
            (hspan := hspan) x hxC

/-- If `x ∈ intrinsicFrontier ℝ C`, then the singleton `{x}` is disjoint from `intrinsicInterior ℝ C`. -/
lemma cor11_6_2_disjoint_singleton_intrinsicInterior_of_mem_intrinsicFrontier {n : Nat}
    {C : Set (Fin n → Real)} {x : Fin n → Real} (hx : x ∈ intrinsicFrontier ℝ C) :
    Disjoint ({x} : Set (Fin n → Real)) (intrinsicInterior ℝ C) := by
  classical
  refine Set.disjoint_singleton_left.2 ?_
  intro hxint
  have hx' := hx
  -- Rewrite `intrinsicFrontier` as `intrinsicClosure \ intrinsicInterior` to extract the contradiction.
  rw [← intrinsicClosure_diff_intrinsicInterior (𝕜 := ℝ) (s := C)] at hx'
  exact hx'.2 hxint

/-- A nontrivial supporting hyperplane gives a point of `C` where the defining linear functional is
strictly smaller than its boundary value. -/
lemma cor11_6_2_exists_lt_of_isSupportingHyperplane_of_not_subset {n : Nat}
    {C H : Set (Fin n → Real)} (hH : IsSupportingHyperplane n C H) (hCnot : ¬ C ⊆ H) :
    ∃ (b : Fin n → Real) (β : Real),
      b ≠ 0 ∧ H = {x : Fin n → Real | x ⬝ᵥ b = β} ∧ (∀ x, x ∈ C → x ⬝ᵥ b ≤ β) ∧
        ∃ y0, y0 ∈ C ∧ y0 ⬝ᵥ b < β := by
  classical
  rcases hH with ⟨b, β, hb0, hHdef, hC_le, _hx⟩
  rcases Set.not_subset.1 hCnot with ⟨y0, hy0C, hy0notH⟩
  have hy0ne : y0 ⬝ᵥ b ≠ β := by
    intro hEq
    have : y0 ∈ H := by simp [hHdef, hEq]
    exact hy0notH this
  have hy0lt : y0 ⬝ᵥ b < β := lt_of_le_of_ne (hC_le y0 hy0C) hy0ne
  exact ⟨b, β, hb0, hHdef, hC_le, ⟨y0, hy0C, hy0lt⟩⟩

/-- If a linear functional attains a strict maximum over `C` at `x`, then `x` is not in the
intrinsic interior of `C`. -/
lemma cor11_6_2_not_mem_intrinsicInterior_of_isMaxOn_of_exists_lt {n : Nat}
    {C : Set (Fin n → Real)} {x : Fin n → Real} {l : StrongDual ℝ (Fin n → Real)}
    (hexists : ∃ y, y ∈ C ∧ l y < l x) (hxmax : IsMaxOn (fun y => l y) C x) :
    x ∉ intrinsicInterior ℝ C := by
  classical
  rcases hexists with ⟨y0, hy0C, hy0lt⟩
  intro hxint
  rcases exists_isOpen_inter_affineSpan_eq_intrinsicInterior n C with ⟨U, hUopen, hUeq⟩
  have hxU : x ∈ U := by
    have : x ∈ U ∩ (affineSpan ℝ C : Set (Fin n → Real)) := by
      simpa [hUeq] using hxint
    exact this.1
  have hxA : x ∈ (affineSpan ℝ C : Set (Fin n → Real)) := by
    have : x ∈ U ∩ (affineSpan ℝ C : Set (Fin n → Real)) := by
      simpa [hUeq] using hxint
    exact this.2
  have hy0A : y0 ∈ (affineSpan ℝ C : Set (Fin n → Real)) := subset_affineSpan ℝ C hy0C
  have hUnhds : U ∈ nhds x := hUopen.mem_nhds hxU
  rcases Metric.mem_nhds_iff.1 hUnhds with ⟨ε, hεpos, hball⟩
  have hy0ne : y0 ≠ x := by
    intro hxy
    subst hxy
    exact (lt_irrefl (l y0)) hy0lt
  have hnormpos : 0 < ‖y0 - x‖ := (norm_pos_iff).2 (sub_ne_zero.2 hy0ne)
  set t : Real := ε / (2 * ‖y0 - x‖)
  have htpos : 0 < t := by
    have hdenpos : 0 < (2 * ‖y0 - x‖) := mul_pos (by norm_num) hnormpos
    exact div_pos hεpos hdenpos
  set z : Fin n → Real := AffineMap.lineMap x y0 (-t)
  have hzU : z ∈ U := by
    have hzball : z ∈ Metric.ball x ε := by
      have hdist : dist z x < ε := by
        have hnorm : ‖z - x‖ < ε := by
          have hnorm_eq : ‖z - x‖ = t * ‖y0 - x‖ := by
            simp [z, AffineMap.lineMap_apply_module', norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
          have hmul : t * ‖y0 - x‖ = ε / 2 := by
            have hnormne : (‖y0 - x‖ : Real) ≠ 0 := ne_of_gt hnormpos
            calc
              t * ‖y0 - x‖
                  = (ε / (2 * ‖y0 - x‖)) * ‖y0 - x‖ := by
                      rfl
              _ = (ε * ‖y0 - x‖) / (2 * ‖y0 - x‖) := by
                      simp [div_mul_eq_mul_div]
              _ = (‖y0 - x‖ * ε) / (‖y0 - x‖ * 2) := by
                      simp [mul_comm]
              _ = ε / 2 := by
                      simpa [mul_assoc] using
                        (mul_div_mul_left (a := ε) (b := (2 : Real)) (c := ‖y0 - x‖) hnormne)
          have : (ε / 2) < ε := by nlinarith [hεpos]
          exact lt_of_eq_of_lt (by simp [hnorm_eq, hmul]) this
        simpa [dist_eq_norm] using hnorm
      simpa [Metric.mem_ball] using hdist
    exact hball hzball
  have hzA : z ∈ (affineSpan ℝ C : Set (Fin n → Real)) := by
    simpa [z] using (AffineMap.lineMap_mem (Q := affineSpan ℝ C) (-t) hxA hy0A)
  have hzint : z ∈ intrinsicInterior ℝ C := by
    have hzmem : z ∈ U ∩ (affineSpan ℝ C : Set (Fin n → Real)) := ⟨hzU, hzA⟩
    simpa [hUeq] using hzmem
  have hzC : z ∈ C := (intrinsicInterior_subset (𝕜 := ℝ) (s := C)) hzint
  have hxmax' : ∀ y ∈ C, l y ≤ l x := (isMaxOn_iff).1 hxmax
  have hlz : l z = l x + t * (l x - l y0) := by
    -- Expand the affine combination and use linearity.
    have : l z = (-t) * (l y0 - l x) + l x := by
      simp [z, AffineMap.lineMap_apply_module', map_add, map_smul, sub_eq_add_neg]
      ring
    calc
      l z = (-t) * (l y0 - l x) + l x := this
      _ = l x + t * (l x - l y0) := by ring
  have hlt : l x < l z := by
    have hdiff : 0 < l x - l y0 := sub_pos.2 hy0lt
    -- `t` is positive, so moving past `x` in direction `(x - y0)` increases the value of `l`.
    nlinarith [hlz, htpos, hdiff]
  have hzle : l z ≤ l x := hxmax' z hzC
  exact (not_lt_of_ge hzle) hlt

/-- Corollary 11.6.2. Let `C` be a convex set. An `x ∈ C` is a relative boundary point of `C`
if and only if there exists a linear function `h` not constant on `C` such that `h` achieves its
maximum over `C` at `x`. (Here "relative boundary" is interpreted as membership in
`intrinsicFrontier ℝ C`.) -/
theorem mem_intrinsicFrontier_iff_exists_isMaxOn_linearFunctional (n : Nat)
    (C : Set (Fin n → Real)) (hC : Convex Real C) (x : Fin n → Real) :
    x ∈ C ∧ x ∈ intrinsicFrontier ℝ C ↔
      ∃ l : StrongDual ℝ (Fin n → Real),
        (∃ y, y ∈ C ∧ l y < l x) ∧ IsMaxOn (fun y => l y) C x ∧ x ∈ C := by
  classical
  constructor
  · rintro ⟨hxC, hxfr⟩
    have hdisj :
        Disjoint ({x} : Set (Fin n → Real)) (intrinsicInterior ℝ C) :=
      cor11_6_2_disjoint_singleton_intrinsicInterior_of_mem_intrinsicFrontier (n := n)
        (C := C) (x := x) hxfr
    have hsubset : ({x} : Set (Fin n → Real)) ⊆ C := by
      intro z hz
      have hz' : z = x := by simpa [Set.mem_singleton_iff] using hz
      simpa [hz'] using hxC
    have hiff :=
      exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior (n := n)
        (C := C) (D := ({x} : Set (Fin n → Real))) hC (Set.singleton_nonempty x)
        (convex_singleton x) hsubset
    rcases (hiff.2 hdisj) with ⟨H, hHnontriv, hDH⟩
    rcases hHnontriv with ⟨hHsupport, hCnot⟩
    rcases
        cor11_6_2_exists_lt_of_isSupportingHyperplane_of_not_subset (n := n) (C := C) (H := H)
          hHsupport hCnot with
      ⟨b, β, hb0, hHdef, hC_le, ⟨y0, hy0C, hy0ltβ⟩⟩
    have hxH : x ∈ H := hDH (by simp)
    have hxEq : x ⬝ᵥ b = β := by simpa [hHdef] using hxH
    refine ⟨dotProduct_strongDual (n := n) b, ?_, ?_, hxC⟩
    · refine ⟨y0, hy0C, ?_⟩
      simpa [dotProduct_strongDual_apply, hxEq] using hy0ltβ
    · refine (isMaxOn_iff).2 ?_
      intro y hyC
      have hyLe : y ⬝ᵥ b ≤ β := hC_le y hyC
      simpa [dotProduct_strongDual_apply, hxEq] using hyLe
  · rintro ⟨l, ⟨y0, hy0C, hy0lt⟩, hxmax, hxC⟩
    have hxnot :
        x ∉ intrinsicInterior ℝ C :=
      cor11_6_2_not_mem_intrinsicInterior_of_isMaxOn_of_exists_lt (n := n) (C := C) (x := x)
        (l := l) ⟨y0, hy0C, hy0lt⟩ hxmax
    have hxcl : x ∈ intrinsicClosure ℝ C := subset_intrinsicClosure (𝕜 := ℝ) (s := C) hxC
    refine ⟨hxC, ?_⟩
    have : x ∈ intrinsicClosure ℝ C \ intrinsicInterior ℝ C := ⟨hxcl, hxnot⟩
    -- Rewrite `intrinsicFrontier` as `intrinsicClosure \ intrinsicInterior`.
    rw [← intrinsicClosure_diff_intrinsicInterior (𝕜 := ℝ) (s := C)]
    exact this

/-- `HyperplaneSeparatesProperly` is symmetric in the two sets. -/
lemma hyperplaneSeparatesProperly_comm {n : Nat} {H C₁ C₂ : Set (Fin n → Real)} :
    HyperplaneSeparatesProperly n H C₁ C₂ → HyperplaneSeparatesProperly n H C₂ C₁ := by
  rintro ⟨hsep, hnot⟩
  rcases hsep with ⟨hC₁ne, hC₂ne, b, β, hb0, hH, hcases⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hC₂ne, hC₁ne, b, β, hb0, hH, ?_⟩
    cases hcases with
    | inl h =>
        exact Or.inr h
    | inr h =>
        exact Or.inl h
  · intro hboth
    exact hnot (by simpa [and_comm] using hboth)

/-- If `x ⬝ᵥ b ≤ β` for all `x ∈ C`, then `((fun x ↦ x ⬝ᵥ b) '' C)` is bounded above. -/
lemma bddAbove_image_dotProduct_of_forall_le {n : Nat} {C : Set (Fin n → Real)}
    (b : Fin n → Real) (β : Real) (h : ∀ x, x ∈ C → x ⬝ᵥ b ≤ β) :
    BddAbove ((fun x : Fin n → Real => x ⬝ᵥ b) '' C) := by
  refine ⟨β, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact h x hx

/-- On a cone, a dot-product bounded above must be nonpositive everywhere. -/
lemma thm11_7_dotProduct_le_zero_of_isConeSet_of_bddAbove {n : Nat} {C : Set (Fin n → Real)}
    (hcone : IsConeSet n C) {b : Fin n → Real}
    (hbdd : BddAbove ((fun x : Fin n → Real => x ⬝ᵥ b) '' C)) :
    ∀ x, x ∈ C → x ⬝ᵥ b ≤ 0 := by
  classical
  rcases hbdd with ⟨M, hM⟩
  intro x hxC
  by_contra hxle
  have hxpos : 0 < x ⬝ᵥ b := lt_of_not_ge (by simpa using hxle)
  have hxne : x ⬝ᵥ b ≠ 0 := ne_of_gt hxpos
  let t : Real := (|M| + 1) / (x ⬝ᵥ b)
  have htpos : 0 < t := by
    have hnumpos : 0 < |M| + 1 := by
      have : 0 ≤ |M| := abs_nonneg M
      linarith
    exact div_pos hnumpos hxpos
  have htxC : t • x ∈ C := hcone x hxC t htpos
  have hleM : (t • x) ⬝ᵥ b ≤ M := by
    have : (t • x) ⬝ᵥ b ∈ (fun y : Fin n → Real => y ⬝ᵥ b) '' C := ⟨t • x, htxC, rfl⟩
    exact hM this
  have hdot : (t • x) ⬝ᵥ b = t * (x ⬝ᵥ b) := by
    simp [smul_dotProduct]
  have htdot : t * (x ⬝ᵥ b) = |M| + 1 := by
    simp [t, div_eq_mul_inv, hxne]
  have htxdot : (t • x) ⬝ᵥ b = |M| + 1 := by
    simpa [hdot] using htdot
  have hMlt : M < |M| + 1 := by
    have hMle : M ≤ |M| := le_abs_self M
    have habslt : |M| < |M| + 1 := lt_add_of_pos_right _ (by norm_num)
    exact lt_of_le_of_lt hMle habslt
  have : M < (t • x) ⬝ᵥ b := by simpa [htxdot] using hMlt
  exact (not_lt_of_ge hleM) this

/-- For a nonempty cone, a bounded-above dot-product has supremum `0`. -/
lemma thm11_7_sSup_image_dotProduct_eq_zero_of_isConeSet {n : Nat} {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) (hcone : IsConeSet n C) (b : Fin n → Real)
    (hbdd : BddAbove ((fun x : Fin n → Real => x ⬝ᵥ b) '' C)) :
    sSup ((fun x : Fin n → Real => x ⬝ᵥ b) '' C) = (0 : Real) := by
  classical
  set S : Set Real := (fun x : Fin n → Real => x ⬝ᵥ b) '' C
  have hSne : S.Nonempty := by
    rcases hCne with ⟨x0, hx0⟩
    exact ⟨x0 ⬝ᵥ b, ⟨x0, hx0, rfl⟩⟩
  have hle0 : ∀ a ∈ S, a ≤ (0 : Real) := by
    intro a ha
    rcases ha with ⟨x, hx, rfl⟩
    exact thm11_7_dotProduct_le_zero_of_isConeSet_of_bddAbove (n := n) (C := C) hcone (b := b)
      hbdd x hx
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hSne hle0 ?_
  intro w hw
  rcases hCne with ⟨x0, hx0⟩
  have hx0le0 : x0 ⬝ᵥ b ≤ 0 :=
    thm11_7_dotProduct_le_zero_of_isConeSet_of_bddAbove (n := n) (C := C) hcone (b := b) hbdd x0
      hx0
  rcases lt_or_eq_of_le hx0le0 with hx0lt | hx0eq
  · -- If `x0 ⬝ᵥ b < 0`, scale `x0` to get a value strictly between `w` and `0`.
    let t : Real := w / (2 * (x0 ⬝ᵥ b))
    have htpos : 0 < t := by
      have hdenneg : 2 * (x0 ⬝ᵥ b) < 0 := mul_neg_of_pos_of_neg (by norm_num) hx0lt
      exact div_pos_of_neg_of_neg hw hdenneg
    have htx0C : t • x0 ∈ C := hcone x0 hx0 t htpos
    refine ⟨(t • x0) ⬝ᵥ b, ⟨t • x0, htx0C, rfl⟩, ?_⟩
    have hdot : (t • x0) ⬝ᵥ b = t * (x0 ⬝ᵥ b) := by
      simp [smul_dotProduct]
    have hx0ne : x0 ⬝ᵥ b ≠ 0 := ne_of_lt hx0lt
    have hmul : t * (x0 ⬝ᵥ b) = w / 2 := by
      simp [t, div_eq_mul_inv, hx0ne, mul_left_comm, mul_comm]
    have hdot' : (t • x0) ⬝ᵥ b = w / 2 := by
      simpa [hdot] using hmul
    have hwlt : w < w / 2 := by nlinarith
    simpa [hdot'] using hwlt
  · -- If `x0 ⬝ᵥ b = 0`, then `0 ∈ S`, so any `w < 0` is below some point of `S`.
    refine ⟨x0 ⬝ᵥ b, ⟨x0, hx0, rfl⟩, ?_⟩
    simpa [hx0eq] using hw

/-- Theorem 11.7. Let `C₁` and `C₂` be non-empty subsets of `ℝ^n`, at least one of which is a
cone. If there exists a hyperplane which separates `C₁` and `C₂` properly, then there exists a
hyperplane which separates `C₁` and `C₂` properly and passes through the origin. -/
theorem exists_hyperplaneSeparatesProperly_through_origin_of_isConeSet (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hcone : IsConeSet n C₁ ∨ IsConeSet n C₂) :
    (∃ H, HyperplaneSeparatesProperly n H C₁ C₂) →
      ∃ H, HyperplaneSeparatesProperly n H C₁ C₂ ∧ (0 : Fin n → Real) ∈ H := by
  classical
  intro hexists
  have aux (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
      (hC₂cone : IsConeSet n C₂) :
      (∃ H, HyperplaneSeparatesProperly n H C₁ C₂) →
        ∃ H, HyperplaneSeparatesProperly n H C₁ C₂ ∧ (0 : Fin n → Real) ∈ H := by
    intro hexists
    rcases hexists with ⟨H₀, hsep₀⟩
    rcases hyperplaneSeparatesProperly_oriented n H₀ C₁ C₂ hsep₀ with
      ⟨b, β, hb0, hH₀, hC₁β, hC₂β, hnot₀⟩
    let S : Set Real := (fun x : Fin n → Real => x ⬝ᵥ b) '' C₂
    have hBdd : BddAbove S :=
      bddAbove_image_dotProduct_of_forall_le (n := n) (C := C₂) b β (fun x hx => hC₂β x hx)
    let β' : Real := sSup S
    let H : Set (Fin n → Real) := {x : Fin n → Real | x ⬝ᵥ b = β'}
    have hSnonempty : S.Nonempty := Set.image_nonempty.2 hC₂ne
    have hβ'leβ : β' ≤ β := by
      refine csSup_le hSnonempty ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hC₂β x hx
    have hC₂β' : ∀ x ∈ C₂, x ⬝ᵥ b ≤ β' := by
      intro x hx
      have : x ⬝ᵥ b ≤ sSup S := by
        refine le_csSup hBdd ?_
        exact ⟨x, hx, rfl⟩
      simpa [β', S] using this
    have hC₁β' : ∀ x ∈ C₁, β' ≤ x ⬝ᵥ b := by
      intro x hx
      exact le_trans hβ'leβ (hC₁β x hx)
    have hsep : HyperplaneSeparatesProperly n H C₁ C₂ := by
      refine ⟨?_, ?_⟩
      · refine ⟨hC₁ne, hC₂ne, b, β', hb0, rfl, ?_⟩
        refine Or.inr ?_
        refine ⟨?_, ?_⟩
        · intro x hx
          exact hC₂β' x hx
        · intro x hx
          exact hC₁β' x hx
      · -- Properness: either `β' = β` and we reuse `hnot₀`, or `β' < β` and then `C₁ ⊄ H`.
        rcases lt_or_eq_of_le hβ'leβ with hlt | heq
        · rcases hC₁ne with ⟨x0, hx0⟩
          have hx0gt : β' < x0 ⬝ᵥ b := lt_of_lt_of_le hlt (hC₁β x0 hx0)
          have hx0not : x0 ∉ H := by
            simp [H, ne_of_gt hx0gt]
          intro hboth
          exact hx0not (hboth.1 hx0)
        · have hHeq : H = H₀ := by
            subst heq
            simpa [H] using hH₀.symm
          simpa [hHeq] using hnot₀
    have hβ'zero : β' = 0 := by
      simpa [β', S] using
        thm11_7_sSup_image_dotProduct_eq_zero_of_isConeSet (n := n) (C := C₂) hC₂ne hC₂cone b
          (by simpa [S] using hBdd)
    have h0mem : (0 : Fin n → Real) ∈ H := by
      simp [H, hβ'zero]
    exact ⟨H, hsep, h0mem⟩
  cases hcone with
  | inr hC₂cone =>
      exact aux C₁ C₂ hC₁ne hC₂ne hC₂cone hexists
  | inl hC₁cone =>
      -- Swap the sets so the cone is on the right, then swap back.
      rcases hexists with ⟨H, hsep⟩
      have hsep' : HyperplaneSeparatesProperly n H C₂ C₁ :=
        hyperplaneSeparatesProperly_comm (n := n) (H := H) (C₁ := C₁) (C₂ := C₂) hsep
      rcases aux C₂ C₁ hC₂ne hC₁ne hC₁cone ⟨H, hsep'⟩ with ⟨H', hsep'', h0H'⟩
      refine ⟨H', ?_, h0H'⟩
      exact hyperplaneSeparatesProperly_comm (n := n) (H := H') (C₁ := C₂) (C₂ := C₁) hsep''

/-- If `a ∉ K` for a nonempty closed convex set `K`, then there is a dot-product functional
strictly separating `a` from `K` in the sense `x ⬝ᵥ b ≤ β < a ⬝ᵥ b`. -/
lemma cor11_7_1_exists_strict_dotProduct_separator_of_not_mem {n : Nat}
    {K : Set (Fin n → Real)} (hKne : K.Nonempty) (hKclosed : IsClosed K) (hKconv : Convex Real K)
    {a : Fin n → Real} (ha : a ∉ K) :
    ∃ (b : Fin n → Real) (β : Real),
      b ≠ 0 ∧ (∀ x ∈ K, x ⬝ᵥ b ≤ β) ∧ β < a ⬝ᵥ b := by
  classical
  have hdisj0 : Disjoint ({a} : Set (Fin n → Real)) K := by
    refine Set.disjoint_left.2 ?_
    intro x hxA hxK
    have hx : x = a := by simpa [Set.mem_singleton_iff] using hxA
    subst hx
    exact ha hxK
  have hdisj : Disjoint (closure ({a} : Set (Fin n → Real))) (closure K) := by
    simpa [closure_singleton, hKclosed.closure_eq] using hdisj0
  have hbounded : Bornology.IsBounded ({a} : Set (Fin n → Real)) ∨ Bornology.IsBounded K :=
    Or.inl
      (show Bornology.IsBounded ({a} : Set (Fin n → Real)) from
        (Bornology.isBounded_singleton (x := a)))
  rcases
      exists_hyperplaneSeparatesStrongly_of_disjoint_closure_convex_of_bounded (n := n)
        ({a} : Set (Fin n → Real)) K (Set.singleton_nonempty a) hKne (convex_singleton a) hKconv
        hdisj hbounded with
    ⟨H, hHstrong⟩
  rcases hHstrong with ⟨_hAne, _hKne, b, β, hb0, _hHdef, ε, hεpos, hcases⟩
  let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
  have hcases' :
      (({a} + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
            K + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) ∨
        (K + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
          {a} + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b})) := by
    simpa [B] using hcases
  have h0B : (0 : Fin n → Real) ∈ B := by simp [B]
  have h0smulB : (0 : Fin n → Real) ∈ (ε • B) := by
    refine ⟨0, h0B, by simp⟩
  have ha_mem_add : a ∈ ({a} : Set (Fin n → Real)) + (ε • B) := by
    refine ⟨a, by simp, 0, h0smulB, by simp⟩
  have hK_mem_add : ∀ x ∈ K, x ∈ K + (ε • B) := by
    intro x hxK
    refine ⟨x, hxK, 0, h0smulB, by simp⟩
  cases hcases' with
  | inr h =>
      refine ⟨b, β, hb0, ?_, ?_⟩
      · intro x hxK
        have hxlt : x ⬝ᵥ b < β := h.1 (hK_mem_add x hxK)
        exact le_of_lt hxlt
      · exact h.2 ha_mem_add
  | inl h =>
      refine ⟨-b, -β, ?_, ?_, ?_⟩
      · simpa using neg_ne_zero.mpr hb0
      · intro x hxK
        have hxgt : β < x ⬝ᵥ b := h.2 (hK_mem_add x hxK)
        have hxlt : x ⬝ᵥ (-b) < -β := by
          simpa [dotProduct_neg] using (neg_lt_neg hxgt)
        exact le_of_lt hxlt
      · have halt : a ⬝ᵥ b < β := h.1 ha_mem_add
        have : -β < a ⬝ᵥ (-b) := by
          simpa [dotProduct_neg] using (neg_lt_neg halt)
        exact this

/-- If `a ∉ K` for a nonempty closed convex cone `K`, then some homogeneous closed half-space
contains `K` but excludes `a`. -/
lemma cor11_7_1_exists_homogeneous_halfspace_superset_excluding_of_not_mem {n : Nat}
    {K : Set (Fin n → Real)} (hKne : K.Nonempty) (hKclosed : IsClosed K) (hK : IsConvexCone n K)
    {a : Fin n → Real} (ha : a ∉ K) :
    ∃ b : Fin n → Real, b ≠ 0 ∧ K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} ∧ 0 < a ⬝ᵥ b := by
  classical
  rcases
      cor11_7_1_exists_strict_dotProduct_separator_of_not_mem (n := n) (K := K) hKne hKclosed
        hK.2 ha with
    ⟨b, β, hb0, hKleβ, hβlt⟩
  have hbdd : BddAbove ((fun x : Fin n → Real => x ⬝ᵥ b) '' K) :=
    bddAbove_image_dotProduct_of_forall_le (n := n) (C := K) b β (fun x hx => hKleβ x hx)
  have hKle0 : ∀ x ∈ K, x ⬝ᵥ b ≤ 0 :=
    thm11_7_dotProduct_le_zero_of_isConeSet_of_bddAbove (n := n) (C := K) hK.1 (b := b) hbdd
  have h0leβ : 0 ≤ β := by
    have hSnonempty : ((fun x : Fin n → Real => x ⬝ᵥ b) '' K).Nonempty :=
      Set.image_nonempty.2 hKne
    have hsSup :
        sSup ((fun x : Fin n → Real => x ⬝ᵥ b) '' K) = (0 : Real) :=
      thm11_7_sSup_image_dotProduct_eq_zero_of_isConeSet (n := n) (C := K) hKne hK.1 b hbdd
    have : sSup ((fun x : Fin n → Real => x ⬝ᵥ b) '' K) ≤ β := by
      refine csSup_le hSnonempty ?_
      intro y hy
      rcases hy with ⟨x, hxK, rfl⟩
      exact hKleβ x hxK
    simpa [hsSup] using this
  have ha_pos : 0 < a ⬝ᵥ b := lt_of_le_of_lt h0leβ hβlt
  refine ⟨b, hb0, ?_, ha_pos⟩
  intro x hxK
  exact hKle0 x hxK

/-- Corollary 11.7.1: A non-empty closed convex cone `K ⊆ ℝ^n` is the intersection of the
homogeneous closed half-spaces which contain it (a homogeneous half-space being one with the
origin on its boundary). -/
theorem isClosed_convexCone_eq_iInter_homogeneous_closedHalfspaces (n : Nat)
    (K : Set (Fin n → Real)) (hKne : K.Nonempty) (hKclosed : IsClosed K) (hK : IsConvexCone n K) :
    (⋂ (b : Fin n → Real) (_hb : b ≠ 0)
        (_hKb : K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}), {x : Fin n → Real | x ⬝ᵥ b ≤ 0}) = K := by
  classical
  ext a
  constructor
  · intro ha
    by_contra haK
    rcases
        cor11_7_1_exists_homogeneous_halfspace_superset_excluding_of_not_mem (n := n) (K := K)
          hKne hKclosed hK (a := a) haK with
      ⟨b, hb0, hKb, ha_pos⟩
    have ha_mem : a ∈ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
      have h1 :
          a ∈
            ⋂ (_hb : b ≠ 0) (_hKb : K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
              {x : Fin n → Real | x ⬝ᵥ b ≤ 0} :=
        (Set.mem_iInter.1 ha) b
      have h2 :
          a ∈
            ⋂ (_hKb : K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
              {x : Fin n → Real | x ⬝ᵥ b ≤ 0} :=
        (Set.mem_iInter.1 h1) hb0
      exact (Set.mem_iInter.1 h2) hKb
    have ha_le : a ⬝ᵥ b ≤ 0 := by simpa using ha_mem
    exact (not_lt_of_ge ha_le) ha_pos
  · intro haK
    refine Set.mem_iInter.2 ?_
    intro b
    refine Set.mem_iInter.2 ?_
    intro hb
    refine Set.mem_iInter.2 ?_
    intro hKb
    exact hKb haK

/-- The closure of a cone set (closed under positive scalar multiplication) is again a cone set. -/
lemma cor11_7_2_isConeSet_closure {n : Nat} {K : Set (Fin n → Real)} (hK : IsConeSet n K) :
    IsConeSet n (closure K) := by
  intro x hx t ht
  have hcont : Continuous fun y : Fin n → Real => t • y := by
    simpa using (continuous_const.smul (continuous_id : Continuous fun y : Fin n → Real => y))
  have hx' : t • x ∈ (fun y : Fin n → Real => t • y) '' closure K := ⟨x, hx, rfl⟩
  have hx'' : t • x ∈ closure ((fun y : Fin n → Real => t • y) '' K) :=
    (image_closure_subset_closure_image (f := fun y : Fin n → Real => t • y) (s := K) hcont) hx'
  have himage : (fun y : Fin n → Real => t • y) '' K ⊆ K := by
    intro z hz
    rcases hz with ⟨y, hyK, rfl⟩
    exact hK y hyK t ht
  exact (closure_mono himage) hx''

/-- A homogeneous closed half-space `{x | x ⬝ᵥ b ≤ 0}` is closed. -/
lemma cor11_7_2_isClosed_homogeneousClosedHalfspace {n : Nat} (b : Fin n → Real) :
    IsClosed {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  have hcont : Continuous fun x : Fin n → Real => x ⬝ᵥ b := by
    simpa using
      (continuous_id.dotProduct (continuous_const : Continuous fun _ : (Fin n → Real) => b))
  simpa [Set.preimage, Set.Iic] using (isClosed_Iic.preimage hcont)

/-- The homogeneous closed half-space `{x | x ⬝ᵥ b ≤ 0}` as a bundled `ConvexCone`. -/
def cor11_7_2_homogeneousClosedHalfspaceCone {n : Nat} (b : Fin n → Real) :
    ConvexCone Real (Fin n → Real) where
  carrier := {x : Fin n → Real | x ⬝ᵥ b ≤ 0}
  smul_mem' := by
    intro c hc x hx
    have : c • (x ⬝ᵥ b) ≤ 0 :=
      smul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hx
    simpa [smul_dotProduct] using this
  add_mem' := by
    intro x hx y hy
    have : x ⬝ᵥ b + y ⬝ᵥ b ≤ 0 := add_nonpos hx hy
    simpa [add_dotProduct] using this

/-- If a homogeneous closed half-space `{x | x ⬝ᵥ b ≤ 0}` contains `S`, then it contains the
closure of the convex cone hull of `S`. -/
lemma cor11_7_2_closure_hull_subset_halfspace_of_subset {n : Nat} (S : Set (Fin n → Real))
    (b : Fin n → Real) (hSb : S ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}) :
    closure (ConvexCone.hull Real S : Set (Fin n → Real)) ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  let HbCone : ConvexCone Real (Fin n → Real) := cor11_7_2_homogeneousClosedHalfspaceCone (n := n) b
  have hHullSub : (ConvexCone.hull Real S : Set (Fin n → Real)) ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
    have hS' : S ⊆ (HbCone : Set (Fin n → Real)) := by
      simpa [HbCone, cor11_7_2_homogeneousClosedHalfspaceCone] using hSb
    have hhull : ConvexCone.hull Real S ≤ HbCone :=
      ConvexCone.hull_min (C := HbCone) hS'
    intro x hx
    have : x ∈ (HbCone : Set (Fin n → Real)) := hhull hx
    simpa [HbCone, cor11_7_2_homogeneousClosedHalfspaceCone] using this
  have hclosed : IsClosed {x : Fin n → Real | x ⬝ᵥ b ≤ 0} :=
    cor11_7_2_isClosed_homogeneousClosedHalfspace (n := n) b
  exact closure_minimal hHullSub hclosed

/-- For `K = closure (ConvexCone.hull ℝ S)`, intersecting all homogeneous closed half-spaces
containing `S` is the same as intersecting those containing `K`. -/
lemma cor11_7_2_intersections_over_S_vs_over_closure_hull (n : Nat) (S : Set (Fin n → Real)) :
    (⋂ (b : Fin n → Real) (_hb : b ≠ 0)
        (_hSb : S ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}), {x : Fin n → Real | x ⬝ᵥ b ≤ 0}) =
      ⋂ (b : Fin n → Real) (_hb : b ≠ 0)
        (_hKb : closure (ConvexCone.hull Real S : Set (Fin n → Real)) ⊆
            {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
          {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  classical
  set K : Set (Fin n → Real) := closure (ConvexCone.hull Real S : Set (Fin n → Real))
  have hSK : S ⊆ K := by
    intro x hxS
    exact subset_closure (ConvexCone.subset_hull (R := Real) (s := S) hxS)
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro b
    refine Set.mem_iInter.2 ?_
    intro hb
    refine Set.mem_iInter.2 ?_
    intro hKb
    have hx' :
        x ∈
          ⋂ (_hSb : S ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
            {x : Fin n → Real | x ⬝ᵥ b ≤ 0} :=
      (Set.mem_iInter.1 ((Set.mem_iInter.1 hx) b) hb)
    have hSb : S ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := fun y hyS => hKb (hSK hyS)
    exact (Set.mem_iInter.1 hx') hSb
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro b
    refine Set.mem_iInter.2 ?_
    intro hb
    refine Set.mem_iInter.2 ?_
    intro hSb
    have hKb :
        K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
      have : closure (ConvexCone.hull Real S : Set (Fin n → Real)) ⊆
          {x : Fin n → Real | x ⬝ᵥ b ≤ 0} :=
        cor11_7_2_closure_hull_subset_halfspace_of_subset (n := n) S b hSb
      simpa [K] using this
    have hx' :
        x ∈
          ⋂ (_hKb : K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
            {x : Fin n → Real | x ⬝ᵥ b ≤ 0} :=
      (Set.mem_iInter.1 ((Set.mem_iInter.1 hx) b) hb)
    exact (Set.mem_iInter.1 hx') hKb

/-- Corollary 11.7.2: Let `S` be any subset of `ℝ^n`, and let `K` be the closure of the convex
cone generated by `S`. Then `K` is the intersection of all homogeneous closed half-spaces
containing `S` (a homogeneous closed half-space is one of the form `{x | x ⬝ᵥ b ≤ 0}` with
`b ≠ 0`). -/
theorem closure_convexConeHull_eq_iInter_homogeneous_closedHalfspaces (n : Nat)
    (S : Set (Fin n → Real)) (hSne : S.Nonempty) :
    closure (ConvexCone.hull Real S : Set (Fin n → Real)) =
      ⋂ (b : Fin n → Real) (_hb : b ≠ 0)
        (_hSb : S ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}), {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  classical
  set K : Set (Fin n → Real) := closure (ConvexCone.hull Real S : Set (Fin n → Real))
  have hKne : K.Nonempty := by
    rcases hSne with ⟨x, hxS⟩
    refine ⟨x, ?_⟩
    refine subset_closure ?_
    exact ConvexCone.subset_hull (R := Real) (s := S) hxS
  have hKclosed : IsClosed K := by
    simp [K]
  have hKcone : IsConvexCone n K := by
    have hconeHull : IsConeSet n (ConvexCone.hull Real S : Set (Fin n → Real)) := by
      intro x hx t ht
      exact (ConvexCone.hull Real S).smul_mem ht hx
    have hconeK : IsConeSet n K := by
      simpa [K] using (cor11_7_2_isConeSet_closure (n := n) (K := (ConvexCone.hull Real S :
        Set (Fin n → Real))) hconeHull)
    have hconvHull : Convex Real (ConvexCone.hull Real S : Set (Fin n → Real)) :=
      (ConvexCone.hull Real S).convex
    have hconvK : Convex Real K := by
      simpa [K] using hconvHull.closure
    exact ⟨hconeK, hconvK⟩
  have hcor71 :
      (⋂ (b : Fin n → Real) (_hb : b ≠ 0)
          (_hKb : K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
        {x : Fin n → Real | x ⬝ᵥ b ≤ 0}) = K :=
    isClosed_convexCone_eq_iInter_homogeneous_closedHalfspaces (n := n) (K := K) hKne hKclosed hKcone
  have hswap :
      (⋂ (b : Fin n → Real) (_hb : b ≠ 0)
          (_hSb : S ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
        {x : Fin n → Real | x ⬝ᵥ b ≤ 0}) =
        ⋂ (b : Fin n → Real) (_hb : b ≠ 0)
          (_hKb : K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
            {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
    simpa [K] using (cor11_7_2_intersections_over_S_vs_over_closure_hull (n := n) S)
  calc
    closure (ConvexCone.hull Real S : Set (Fin n → Real)) = K := by simp [K]
    _ = ⋂ (b : Fin n → Real) (_hb : b ≠ 0)
          (_hKb : K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
            {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
          simpa using hcor71.symm
    _ = ⋂ (b : Fin n → Real) (_hb : b ≠ 0)
          (_hSb : S ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0}),
            {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
          simpa using hswap.symm

/-- In positive dimension, there exists a nonzero vector in `ℝ^n` (as functions `Fin n → ℝ`). -/
lemma cor11_7_3_exists_nonzero_vector_of_pos {n : Nat} (hn : 0 < n) :
    ∃ b : Fin n → Real, b ≠ 0 := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨fun i : Fin n => if i = i0 then (1 : Real) else 0, ?_⟩
  intro hb0
  have : (1 : Real) = 0 := by
    simpa [i0] using congrArg (fun f : Fin n → Real => f i0) hb0
  exact one_ne_zero this

/-- If `K = ∅` in positive dimension, then `K` lies in a homogeneous closed half-space
`{x | x ⬝ᵥ b ≤ 0}` with `b ≠ 0`. -/
lemma cor11_7_3_exists_subset_halfspace_of_empty {n : Nat} (hn : 0 < n) (K : Set (Fin n → Real))
    (hKempty : K = ∅) :
    ∃ b : Fin n → Real, b ≠ 0 ∧ K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  rcases cor11_7_3_exists_nonzero_vector_of_pos (n := n) hn with ⟨b, hb0⟩
  refine ⟨b, hb0, ?_⟩
  simp [hKempty]

/-- From a proper separating hyperplane through the origin between `{a}` and `K`, extract a
nonzero normal `b` for a homogeneous closed half-space containing `K`. -/
lemma cor11_7_3_extract_homogeneous_halfspace_of_sep_through_origin {n : Nat}
    {K : Set (Fin n → Real)} {a : Fin n → Real} {H : Set (Fin n → Real)}
    (hsep : HyperplaneSeparatesProperly n H ({a} : Set (Fin n → Real)) K)
    (h0 : (0 : Fin n → Real) ∈ H) :
    ∃ b : Fin n → Real, b ≠ 0 ∧ K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  classical
  rcases hyperplaneSeparatesProperly_oriented n H ({a} : Set (Fin n → Real)) K hsep with
    ⟨b, β, hb0, hHdef, _ha, hKle, _hproper⟩
  have hβ0 : β = 0 := by
    have : (0 : Real) = β := by
      simpa [hHdef] using h0
    simpa using this.symm
  refine ⟨b, hb0, ?_⟩
  intro x hxK
  have hxle : x ⬝ᵥ b ≤ β := hKle x hxK
  simpa [hβ0] using hxle

/-- Corollary 11.7.3: Let `K` be a convex cone in `ℝ^n` other than `ℝ^n` itself. Then `K` is
contained in some homogeneous closed half-space of `ℝ^n`. In other words, there exists some
vector `b ≠ 0` such that `x ⬝ᵥ b ≤ 0` for every `x ∈ K`. -/

theorem exists_subset_homogeneous_closedHalfspace_of_isConvexCone_ne_univ (n : Nat) (hn : 0 < n)
    (K : Set (Fin n → Real)) (hK : IsConvexCone n K) (hKne : K ≠ Set.univ) :
    ∃ b : Fin n → Real, b ≠ 0 ∧ K ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ 0} := by
  classical
  by_cases hKempty : K = ∅
  ·
    exact cor11_7_3_exists_subset_halfspace_of_empty (n := n) hn K hKempty
  ·
    have hKne' : K.Nonempty := Set.nonempty_iff_ne_empty.2 hKempty
    rcases ((Set.ne_univ_iff_exists_notMem (s := K)).1 hKne) with ⟨a, haK⟩
    rcases
        cor11_5_2_exists_hyperplaneSeparatesProperly_point (n := n) (C := K) (a := a) hKne'
          hK.2 haK with
      ⟨H₀, hsep₀⟩
    rcases
        exists_hyperplaneSeparatesProperly_through_origin_of_isConeSet (n := n)
          ({a} : Set (Fin n → Real)) K (Set.singleton_nonempty a) hKne' (Or.inr hK.1)
          ⟨H₀, hsep₀⟩ with
      ⟨H, hsep, h0H⟩
    exact
      cor11_7_3_extract_homogeneous_halfspace_of_sep_through_origin (n := n) (K := K) (a := a)
        (H := H) hsep h0H

end Section11
end Chap03
