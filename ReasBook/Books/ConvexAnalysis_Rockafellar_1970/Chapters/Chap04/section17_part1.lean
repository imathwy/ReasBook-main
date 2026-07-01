/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section02_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part2

open scoped BigOperators Pointwise

section Chap04
section Section17

/-- Definition 17.0.1 (Convex combination). Let `x₁, …, xₘ ∈ ℝⁿ` and let coefficients
`λ₁, …, λₘ` satisfy `λ i ≥ 0` for all `i` and `∑ i, λ i = 1`. Then the vector
`∑ i, λ i • x i` is called a convex combination of the points `x₁, …, xₘ`. -/
def IsConvexWeights (m : Nat) (w : Fin m → Real) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∑ i, w i = (1 : Real))

/-- The weighted sum `∑ i, w i • x i`. -/
def convexCombination (n m : Nat) (x : Fin m → Fin n → Real) (w : Fin m → Real) : Fin n → Real :=
  ∑ i, w i • x i

/-- If `w` are nonnegative and sum to `1`, then `∑ i, w i • x i` is a convex combination
in the sense of `IsConvexCombination`. -/
theorem isConvexCombination_of_isConvexWeights (n m : Nat) (x : Fin m → Fin n → Real)
    (w : Fin m → Real) (hw : IsConvexWeights m w) :
    IsConvexCombination n m x (convexCombination n m x w) := by
  rcases hw with ⟨hw_nonneg, hw_sum⟩
  refine ⟨w, hw_nonneg, hw_sum, ?_⟩
  rfl

/-- Definition 17.0.2 (Convex hull). For `S ⊆ ℝⁿ`, the convex hull of `S`, denoted `conv(S)`,
is the set of all convex combinations of finitely many points of `S`; equivalently, it is the
smallest convex set containing `S`. -/
abbrev conv {n : Nat} (S : Set (Fin n → Real)) : Set (Fin n → Real) :=
  convexHull ℝ S

/-- Helper: extract a finite affinely independent positive convex combination. -/
lemma caratheodory_aux_exists_affineIndependent_pos {n : Nat} {S : Set (Fin n → Real)}
    {x : Fin n → Real} (hx : x ∈ conv S) :
    ∃ (ι : Type) (_ : Fintype ι) (z : ι → Fin n → Real) (w : ι → Real),
      Set.range z ⊆ S ∧ AffineIndependent ℝ z ∧ (∀ i, 0 < w i) ∧
        (∑ i, w i = 1) ∧ (∑ i, w i • z i = x) := by
  simpa [conv] using (eq_pos_convex_span_of_mem_convexHull (x := x) (s := S) (hx := hx))

/-- Helper: an affinely independent family in `ℝⁿ` has cardinality at most `n + 1`. -/
lemma caratheodory_aux_card_le_n_add_one {n : Nat} {ι : Type _} [Fintype ι]
    {z : ι → Fin n → Real} (hz : AffineIndependent ℝ z) :
    Fintype.card ι ≤ n + 1 := by
  classical
  have hcard :
      Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
    AffineIndependent.card_le_finrank_succ hz
  have hfinrank :
      Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤
        Module.finrank ℝ (Fin n → Real) := by
    simpa using
      (Submodule.finrank_mono (le_top :
        vectorSpan ℝ (Set.range z) ≤ (⊤ : Submodule ℝ (Fin n → Real))))
  have hcard' :
      Fintype.card ι ≤ Module.finrank ℝ (Fin n → Real) + 1 := by
    exact le_trans hcard (Nat.add_le_add_right hfinrank 1)
  have hdim : Module.finrank ℝ (Fin n → Real) = n := by
    simp
  simpa [hdim] using hcard'

/-- Helper: reindex a finite convex combination to `Fin m`. -/
lemma caratheodory_aux_reindex_to_Fin {n : Nat} {S : Set (Fin n → Real)} {x : Fin n → Real}
    {ι : Type _} [Fintype ι] (z : ι → Fin n → Real) (w : ι → Real)
    (hzS : Set.range z ⊆ S) (hw_pos : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1)
    (hw_x : ∑ i, w i • z i = x) :
    ∃ (x' : Fin (Fintype.card ι) → Fin n → Real) (w' : Fin (Fintype.card ι) → Real),
      (∀ i, x' i ∈ S) ∧ IsConvexWeights (Fintype.card ι) w' ∧
        x = convexCombination n (Fintype.card ι) x' w' := by
  classical
  let m := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let x' : Fin m → Fin n → Real := fun j => z (e.symm j)
  let w' : Fin m → Real := fun j => w (e.symm j)
  refine ⟨x', w', ?_, ?_, ?_⟩
  · intro j
    apply hzS
    exact ⟨e.symm j, rfl⟩
  · refine ⟨?_, ?_⟩
    · intro j
      exact le_of_lt (hw_pos (e.symm j))
    · have hsum' : (∑ j, w' j) = ∑ i, w i := by
        simpa [w'] using (Equiv.sum_comp e.symm (fun i => w i))
      calc
        ∑ j, w' j = ∑ i, w i := hsum'
        _ = 1 := hw_sum
  · have hsum' : (∑ j, w' j • x' j) = ∑ i, w i • z i := by
      simpa [w', x'] using (Equiv.sum_comp e.symm (fun i => w i • z i))
    have hx' : convexCombination n m x' w' = x := by
      calc
        convexCombination n m x' w' = ∑ i, w i • z i := by
          simpa [convexCombination] using hsum'
        _ = x := hw_x
    simpa [m] using hx'.symm

/-- Theorem 17.0.3 (Carath\'eodory). Let `S ⊆ ℝⁿ`. For every `x ∈ conv(S)`, there exist
`x₁, …, xₘ ∈ S` and coefficients `λ₁, …, λₘ ≥ 0` such that
`x = ∑ i, λ i • x i`, `∑ i, λ i = 1`, and `m ≤ n + 1`. -/
theorem caratheodory {n : Nat} {S : Set (Fin n → Real)} {x : Fin n → Real} :
    x ∈ conv S →
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (x' : Fin m → Fin n → Real) (w : Fin m → Real),
          (∀ i, x' i ∈ S) ∧ IsConvexWeights m w ∧ x = convexCombination n m x' w := by
  intro hx
  classical
  obtain ⟨ι, _inst, z, w, hzS, hz_aff, hw_pos, hw_sum, hw_x⟩ :=
    caratheodory_aux_exists_affineIndependent_pos (n := n) (S := S) (x := x) hx
  have hm_le : Fintype.card ι ≤ n + 1 :=
    caratheodory_aux_card_le_n_add_one (n := n) (z := z) hz_aff
  obtain ⟨x', w', hx'S, hw', hx_eq⟩ :=
    caratheodory_aux_reindex_to_Fin (n := n) (S := S) (x := x)
      (z := z) (w := w) hzS hw_pos hw_sum hw_x
  refine ⟨Fintype.card ι, hm_le, x', w', hx'S, hw', hx_eq⟩

/-- Definition 17.0.4 (Mixed convex hull). Let `S = S₀ ∪ S₁`, where `S₀ ⊆ ℝⁿ` is a set of
points and `S₁` is a set of directions. The (mixed) convex hull `conv(S)` is the smallest
convex set `C ⊆ ℝⁿ` such that:

(1) `C ⊇ S₀`;
(2) `C` recedes in all directions in `S₁`, i.e. for every `d ∈ S₁`, `x ∈ C`, and `t ≥ 0`,
`x + t • d ∈ C`. -/
def mixedConvexHull {n : Nat} (S₀ S₁ : Set (Fin n → Real)) : Set (Fin n → Real) :=
  ⋂₀ {C : Set (Fin n → Real) |
    Convex ℝ C ∧ S₀ ⊆ C ∧ ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ t : Real, 0 ≤ t → x + t • d ∈ C}

/-- Definition 17.0.5 (`ray S₁` and `cone S₁`, LaTeX label `def:ray-cone`). Let `ray S₁` be the
set consisting of the origin and all vectors whose directions belong to `S₁`, i.e. all vectors
of the form `t • d` with `d ∈ S₁` and `t ≥ 0`. Define `cone(S₁) := conv(ray S₁)`. Equivalently,
`cone(S₁)` is the convex cone generated by all vectors whose directions belong to `S₁`. -/
abbrev ray (n : Nat) (S₁ : Set (Fin n → Real)) : Set (Fin n → Real) :=
  Set.insert (0 : Fin n → Real) (rayNonneg n S₁)

/-- The cone obtained as the convex hull of `ray S₁`. -/
abbrev cone (n : Nat) (S₁ : Set (Fin n → Real)) : Set (Fin n → Real) :=
  conv (ray n S₁)

/-- The ray lies in the generated cone. -/
lemma cone_eq_convexConeGenerated_aux_ray_subset_convexConeGenerated (n : Nat)
    (S₁ : Set (Fin n → Real)) :
    ray n S₁ ⊆ convexConeGenerated n S₁ := by
  intro x hx
  have hx' : x = 0 ∨ x ∈ rayNonneg n S₁ := by
    simpa [ray, Set.mem_insert_iff] using hx
  cases hx' with
  | inl hx0 =>
      subst hx0
      change (0 : Fin n → Real) ∈
          Set.insert 0 (ConvexCone.hull Real S₁ : Set (Fin n → Real))
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
  | inr hxRay =>
      exact rayNonneg_subset_convexConeGenerated n S₁ hxRay

/-- Positive scaling sends the ray into itself. -/
lemma cone_eq_convexConeGenerated_aux_ray_smul_subset {n : Nat} {S₁ : Set (Fin n → Real)}
    {c : Real} (hc : 0 < c) :
    c • ray n S₁ ⊆ ray n S₁ := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' : x = 0 ∨ x ∈ rayNonneg n S₁ := by
    simpa [ray, Set.mem_insert_iff] using hx
  cases hx' with
  | inl hx0 =>
      subst hx0
      have h0 : (0 : Fin n → Real) ∈ ray n S₁ :=
        (Set.mem_insert_iff).2 (Or.inl rfl)
      simpa using h0
  | inr hxRay =>
      rcases hxRay with ⟨d, hdS₁, t, ht, rfl⟩
      have hct : 0 ≤ c * t := mul_nonneg (le_of_lt hc) ht
      have : c • (t • d) ∈ rayNonneg n S₁ := by
        refine ⟨d, hdS₁, c * t, hct, ?_⟩
        simp [smul_smul]
      exact (Set.mem_insert_iff).2 (Or.inr this)

/-- The cone is closed under positive scaling. -/
lemma cone_eq_convexConeGenerated_aux_pos_smul_mem_cone {n : Nat} {S₁ : Set (Fin n → Real)}
    {c : Real} (hc : 0 < c) {x : Fin n → Real} (hx : x ∈ cone n S₁) :
    c • x ∈ cone n S₁ := by
  have hx' : x ∈ convexHull Real (ray n S₁) := by
    simpa [cone, conv] using hx
  have hsubset : c • ray n S₁ ⊆ ray n S₁ :=
    cone_eq_convexConeGenerated_aux_ray_smul_subset (n := n) (S₁ := S₁) hc
  have hx'' : c • x ∈ c • convexHull Real (ray n S₁) := ⟨x, hx', rfl⟩
  have hx''' : c • x ∈ convexHull Real (c • ray n S₁) := by
    have h :
        c • convexHull Real (ray n S₁) =
          convexHull Real (c • ray n S₁) := by
      simpa using
        (convexHull_smul (𝕜:=Real) (a:=c) (s:=ray n S₁)).symm
    simpa [h] using hx''
  have hsubsetHull :
      convexHull Real (c • ray n S₁) ⊆ convexHull Real (ray n S₁) :=
    convexHull_min (hsubset.trans (subset_convexHull (𝕜:=Real) (s:=ray n S₁)))
      (convex_convexHull Real (ray n S₁))
  have hx'''' : c • x ∈ convexHull Real (ray n S₁) := hsubsetHull hx'''
  simpa [cone, conv] using hx''''

/-- The convex cone hull of `S₁` lies in `cone S₁`. -/
lemma cone_eq_convexConeGenerated_aux_hull_subset_cone {n : Nat} {S₁ : Set (Fin n → Real)} :
    (ConvexCone.hull Real S₁ : Set (Fin n → Real)) ⊆ cone n S₁ := by
  classical
  let Ccone : ConvexCone Real (Fin n → Real) :=
    { carrier := cone n S₁
      smul_mem' := by
        intro c hc x hx
        exact
          cone_eq_convexConeGenerated_aux_pos_smul_mem_cone (n := n) (S₁ := S₁) (c := c) hc hx
      add_mem' := by
        intro x hx y hy
        have hconv : Convex Real (cone n S₁) := by
          simpa [cone, conv] using (convex_convexHull (𝕜:=Real) (s:=ray n S₁))
        have hmid : midpoint Real x y ∈ cone n S₁ :=
          Convex.midpoint_mem hconv hx hy
        have htwo : (2 : Real) • midpoint Real x y ∈ cone n S₁ :=
          cone_eq_convexConeGenerated_aux_pos_smul_mem_cone (n := n) (S₁ := S₁) (c := 2)
            (by norm_num) hmid
        have hsum : x + y = (2 : Real) • midpoint Real x y := by
          calc
            x + y = midpoint Real x y + midpoint Real x y := by simp
            _ = (2 : Real) • midpoint Real x y := by
                  simpa using (two_smul Real (midpoint Real x y)).symm
        simpa [hsum] using htwo }
  have hSsub : S₁ ⊆ (Ccone : Set (Fin n → Real)) := by
    intro x hx
    have hxray : x ∈ ray n S₁ := by
      have hxraynonneg : x ∈ rayNonneg n S₁ := by
        refine ⟨x, hx, 1, by norm_num, ?_⟩
        simp
      exact (Set.mem_insert_iff).2 (Or.inr hxraynonneg)
    simpa [cone, conv] using (subset_convexHull (𝕜:=Real) (s:=ray n S₁)) hxray
  intro x hx
  exact (ConvexCone.hull_min (s := S₁) (C := Ccone) hSsub) hx

/-- The generated cone is contained in `cone`. -/
lemma cone_eq_convexConeGenerated_aux_convexConeGenerated_subset_cone (n : Nat)
    (S₁ : Set (Fin n → Real)) :
    convexConeGenerated n S₁ ⊆ cone n S₁ := by
  intro x hx
  have hx' : x = 0 ∨ x ∈ (ConvexCone.hull Real S₁ : Set (Fin n → Real)) := by
    simpa [convexConeGenerated, Set.mem_insert_iff] using hx
  cases hx' with
  | inl hx0 =>
      subst hx0
      have h0ray : (0 : Fin n → Real) ∈ ray n S₁ := by
        change (0 : Fin n → Real) ∈ Set.insert 0 (rayNonneg n S₁)
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      simpa [cone, conv] using (subset_convexHull (𝕜:=Real) (s:=ray n S₁)) h0ray
  | inr hxHull =>
      exact cone_eq_convexConeGenerated_aux_hull_subset_cone (n := n) (S₁ := S₁) hxHull

/-- The cone defined as `conv(ray S₁)` agrees with the convex cone generated by `S₁`. -/
theorem cone_eq_convexConeGenerated (n : Nat) (S₁ : Set (Fin n → Real)) :
    cone n S₁ = convexConeGenerated n S₁ := by
  refine subset_antisymm ?_ ?_
  · have hsubset : ray n S₁ ⊆ convexConeGenerated n S₁ :=
      cone_eq_convexConeGenerated_aux_ray_subset_convexConeGenerated n S₁
    have hconv : Convex Real (convexConeGenerated n S₁) :=
      convexConeGenerated_convex n S₁
    have hHull : convexHull Real (ray n S₁) ⊆ convexConeGenerated n S₁ :=
      convexHull_min hsubset hconv
    simpa [cone, conv] using hHull
  · exact cone_eq_convexConeGenerated_aux_convexConeGenerated_subset_cone n S₁

/-- The mixed convex hull is convex. -/
lemma convex_mixedConvexHull {n : Nat} (S₀ S₁ : Set (Fin n → Real)) :
    Convex ℝ (mixedConvexHull (n := n) S₀ S₁) := by
  classical
  unfold mixedConvexHull
  refine convex_sInter ?_
  intro C hC
  have hC' :
      Convex ℝ C ∧ S₀ ⊆ C ∧
        ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ t : Real, 0 ≤ t → x + t • d ∈ C := by
    simpa using hC
  exact hC'.1

/-- Elements of `S₀ + ray S₁` lie in the mixed convex hull. -/
lemma add_ray_subset_mixedConvexHull {n : Nat} (S₀ S₁ : Set (Fin n → Real)) :
    S₀ + ray n S₁ ⊆ mixedConvexHull (n := n) S₀ S₁ := by
  intro x hx
  rcases (Set.mem_add).1 hx with ⟨a, haS₀, r, hr, rfl⟩
  refine (Set.mem_sInter).2 ?_
  intro C hC
  rcases (by simpa using hC) with ⟨_hconv, hS₀C, hrec⟩
  have hr' : r = 0 ∨ r ∈ rayNonneg n S₁ := by
    simpa [ray] using hr
  cases hr' with
  | inl hr0 =>
      subst hr0
      simpa using hS₀C haS₀
  | inr hrRay =>
      rcases hrRay with ⟨d, hdS₁, t, ht, rfl⟩
      exact hrec hdS₁ (hS₀C haS₀) t ht

/-- The generated cone is a convex cone. -/
lemma isConvexCone_convexConeGenerated {n : Nat} (S₁ : Set (Fin n → Real)) :
    IsConvexCone n (convexConeGenerated n S₁) := by
  refine ⟨?_, ?_⟩
  · intro x hx t ht
    have hx' : x = 0 ∨ x ∈ (ConvexCone.hull Real S₁ : Set (Fin n → Real)) := by
      simpa [convexConeGenerated, Set.mem_insert_iff] using hx
    cases hx' with
    | inl hx0 =>
        subst hx0
        have h0 : (0 : Fin n → Real) ∈ convexConeGenerated n S₁ := by
          change (0 : Fin n → Real) ∈
              Set.insert 0 (ConvexCone.hull Real S₁ : Set (Fin n → Real))
          exact (Set.mem_insert_iff).2 (Or.inl rfl)
        simpa using h0
    | inr hxHull =>
        have htx : t • x ∈ (ConvexCone.hull Real S₁ : Set (Fin n → Real)) :=
          (ConvexCone.hull Real S₁).smul_mem ht hxHull
        have : t • x = 0 ∨ t • x ∈ (ConvexCone.hull Real S₁ : Set (Fin n → Real)) :=
          Or.inr htx
        simpa [convexConeGenerated, Set.mem_insert_iff, -smul_eq_zero] using this
  · exact convexConeGenerated_convex n S₁

/-- The set `conv S₀ + cone S₁` satisfies the mixed convex hull properties. -/
lemma conv_add_cone_mem_mixedConvexHull_family {n : Nat} (S₀ S₁ : Set (Fin n → Real)) :
    Convex ℝ (conv S₀ + cone n S₁) ∧
      S₀ ⊆ conv S₀ + cone n S₁ ∧
      ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ conv S₀ + cone n S₁ → ∀ t : Real, 0 ≤ t →
        x + t • d ∈ conv S₀ + cone n S₁ := by
  classical
  have hconvS₀ : Convex ℝ (conv S₀) := by
    simpa [conv] using (convex_convexHull (𝕜:=Real) (s:=S₀))
  have hconvCone : Convex ℝ (cone n S₁) := by
    simpa [cone, conv] using (convex_convexHull (𝕜:=Real) (s:=ray n S₁))
  refine ⟨Convex.add hconvS₀ hconvCone, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ conv S₀ := (subset_convexHull (𝕜:=Real) (s:=S₀)) hx
    have h0ray : (0 : Fin n → Real) ∈ ray n S₁ := by
      change (0 : Fin n → Real) ∈ Set.insert 0 (rayNonneg n S₁)
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
    have h0cone : (0 : Fin n → Real) ∈ cone n S₁ := by
      simpa [cone, conv] using (subset_convexHull (𝕜:=Real) (s:=ray n S₁)) h0ray
    have hxmem : x + 0 ∈ conv S₀ + cone n S₁ := Set.add_mem_add hx' h0cone
    simpa using hxmem
  · intro d hdS₁ x hx t ht
    rcases (Set.mem_add).1 hx with ⟨x0, hx0, u, hu, rfl⟩
    have ht_raynonneg : t • d ∈ rayNonneg n S₁ := by
      exact ⟨d, hdS₁, t, ht, rfl⟩
    have ht_ray : t • d ∈ ray n S₁ := by
      exact (Set.mem_insert_iff).2 (Or.inr ht_raynonneg)
    have ht_cone : t • d ∈ cone n S₁ := by
      simpa [cone, conv] using (subset_convexHull (𝕜:=Real) (s:=ray n S₁)) ht_ray
    have hcone' : IsConvexCone n (cone n S₁) := by
      simpa [cone_eq_convexConeGenerated (n := n) (S₁ := S₁)] using
        (isConvexCone_convexConeGenerated (n := n) (S₁ := S₁))
    have hadd :
        ∀ y ∈ cone n S₁, ∀ z ∈ cone n S₁, y + z ∈ cone n S₁ :=
      isConvexCone_add_closed n (cone n S₁) hcone'
    have hu' : u + t • d ∈ cone n S₁ := hadd u hu (t • d) ht_cone
    have hx' : x0 + (u + t • d) ∈ conv S₀ + cone n S₁ := Set.add_mem_add hx0 hu'
    simpa [add_assoc] using hx'
/-- Proposition 17.0.6 (Representation of the mixed convex hull), LaTeX label
`prop:mixed-representation`. With the notation above, the smallest mixed convex hull exists, and
one has

`mixedConvexHull S₀ S₁ = conv (S₀ + ray n S₁) = conv S₀ + cone n S₁`. -/
theorem mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone {n : Nat} (S₀ S₁ : Set (Fin n → Real)) :
    mixedConvexHull S₀ S₁ = conv (S₀ + ray n S₁) ∧
      conv (S₀ + ray n S₁) = conv S₀ + cone n S₁ := by
  classical
  have hconv_add : conv (S₀ + ray n S₁) = conv S₀ + cone n S₁ := by
    simpa [conv, cone] using
      (convexHull_add (R := Real) (s := S₀) (t := ray n S₁))
  have hsubset1 : conv (S₀ + ray n S₁) ⊆ mixedConvexHull S₀ S₁ := by
    refine convexHull_min ?_ (convex_mixedConvexHull (n := n) S₀ S₁)
    exact add_ray_subset_mixedConvexHull (n := n) S₀ S₁
  have hCstar_mem :
      (conv S₀ + cone n S₁) ∈
        {C : Set (Fin n → Real) |
          Convex ℝ C ∧ S₀ ⊆ C ∧
            ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ t : Real, 0 ≤ t → x + t • d ∈ C} := by
    simpa using (conv_add_cone_mem_mixedConvexHull_family (n := n) S₀ S₁)
  have hsubset2 : mixedConvexHull S₀ S₁ ⊆ conv (S₀ + ray n S₁) := by
    have hsubset2' : mixedConvexHull S₀ S₁ ⊆ conv S₀ + cone n S₁ := by
      simpa [mixedConvexHull] using (Set.sInter_subset_of_mem hCstar_mem)
    simpa [hconv_add] using hsubset2'
  refine ⟨subset_antisymm hsubset2 hsubset1, hconv_add⟩

/-- Definition 17.0.7 (Mixed convex combination), LaTeX label `def:mixed-comb`. Let `S = S₀ ∪ S₁`
be a mixed set of points `S₀ ⊆ ℝⁿ` and directions `S₁ ⊆ ℝⁿ`. A vector `x ∈ ℝⁿ` is a convex
combination of `m` points and directions in `S` if it can be written as

`x = λ₁ • x₁ + ··· + λₖ • xₖ + λₖ₊₁ • xₖ₊₁ + ··· + λₘ • xₘ`,

where `1 ≤ k ≤ m`, one has `x₁, …, xₖ ∈ S₀`, the vectors `xₖ₊₁, …, xₘ` have directions in `S₁`,
all coefficients satisfy `λ i ≥ 0`, and `λ₁ + ··· + λₖ = 1`.

In this formalization, “has direction in `S₁`” is modeled as membership in `ray n S₁`. -/
def IsMixedConvexCombination (n m : Nat) (S₀ S₁ : Set (Fin n → Real)) (x : Fin n → Real) : Prop :=
  ∃ k : Nat, 1 ≤ k ∧ k ≤ m ∧
    ∃ (p : Fin k → Fin n → Real) (d : Fin (m - k) → Fin n → Real)
      (a : Fin k → Real) (b : Fin (m - k) → Real),
      (∀ i, p i ∈ S₀) ∧ (∀ j, d j ∈ ray n S₁) ∧
      (∀ i, 0 ≤ a i) ∧ (∀ j, 0 ≤ b j) ∧
      (∑ i, a i = (1 : Real)) ∧ x = (∑ i, a i • p i) + (∑ j, b j • d j)

/-- Convex weights force at least one summand. -/
lemma one_le_of_IsConvexWeights {m : Nat} {w : Fin m → Real} (hw : IsConvexWeights m w) :
    1 ≤ m := by
  have hm : m ≠ 0 := by
    intro hm0
    subst hm0
    rcases hw with ⟨_, hsum⟩
    simp at hsum
  have hm' : 0 < m := Nat.pos_of_ne_zero hm
  exact (Nat.succ_le_iff).2 hm'

/-- A nonnegative linear combination of rays lies in the cone. -/
lemma sum_smul_mem_cone_of_nonneg_mem_ray {n m : Nat} {S₁ : Set (Fin n → Real)}
    (d : Fin m → Fin n → Real) (b : Fin m → Real)
    (hd : ∀ j, d j ∈ ray n S₁) (hb : ∀ j, 0 ≤ b j) :
    (∑ j, b j • d j) ∈ cone n S₁ := by
  classical
  have hcone : IsConvexCone n (cone n S₁) := by
    simpa [cone_eq_convexConeGenerated (n := n) (S₁ := S₁)] using
      (isConvexCone_convexConeGenerated (n := n) (S₁ := S₁))
  have hadd :
      ∀ x ∈ cone n S₁, ∀ y ∈ cone n S₁, x + y ∈ cone n S₁ :=
    isConvexCone_add_closed n (cone n S₁) hcone
  have h0cone : (0 : Fin n → Real) ∈ cone n S₁ := by
    have h0ray : (0 : Fin n → Real) ∈ ray n S₁ := by
      change (0 : Fin n → Real) ∈ Set.insert 0 (rayNonneg n S₁)
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
    simpa [cone, conv] using (subset_convexHull (𝕜:=Real) (s:=ray n S₁)) h0ray
  have hterm : ∀ j, b j • d j ∈ cone n S₁ := by
    intro j
    have hdcone : d j ∈ cone n S₁ := by
      simpa [cone, conv] using (subset_convexHull (𝕜:=Real) (s:=ray n S₁)) (hd j)
    rcases lt_or_eq_of_le (hb j) with hbpos | hbzero
    · exact hcone.1 (d j) hdcone (b j) hbpos
    · have hbzero' : b j = 0 := by simpa [eq_comm] using hbzero
      simpa [hbzero'] using h0cone
  have hsum :
      ∀ s : Finset (Fin m), Finset.sum s (fun j => b j • d j) ∈ cone n S₁ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using h0cone
    · intro a s ha hs
      have ha' : b a • d a ∈ cone n S₁ := hterm a
      have hs' : Finset.sum s (fun j => b j • d j) ∈ cone n S₁ := hs
      have hsum' :
          b a • d a + Finset.sum s (fun j => b j • d j) ∈ cone n S₁ :=
        hadd (b a • d a) ha' (Finset.sum s (fun j => b j • d j)) hs'
      simpa [Finset.sum_insert ha] using hsum'
  simpa using (hsum Finset.univ)

/-- Membership in the mixed convex hull gives a mixed convex combination. -/
lemma exists_mixedConvexCombination_of_mem_mixedConvexHull {n : Nat}
    {S₀ S₁ : Set (Fin n → Real)} {x : Fin n → Real} :
    x ∈ mixedConvexHull S₀ S₁ → ∃ m : Nat, IsMixedConvexCombination n m S₀ S₁ x := by
  intro hx
  have hrepr := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀ S₁
  have hx' : x ∈ conv S₀ + cone n S₁ := by
    have hx'' : x ∈ conv (S₀ + ray n S₁) := by
      simpa [hrepr.1] using hx
    simpa [hrepr.2] using hx''
  rcases (Set.mem_add).1 hx' with ⟨x0, hx0, u, hu, rfl⟩
  obtain ⟨k, _hk_le, p, a, hpS₀, ha, hx0eq⟩ :=
    caratheodory (n := n) (S := S₀) (x := x0) hx0
  have hu' : u ∈ conv (ray n S₁) := by
    simpa [cone] using hu
  obtain ⟨m2, _hm2_le, d, b, hdS₁, hb, huneq⟩ :=
    caratheodory (n := n) (S := ray n S₁) (x := u) hu'
  have hk_pos : 1 ≤ k := one_le_of_IsConvexWeights (m := k) (w := a) ha
  let m := k + m2
  have hmk : m - k = m2 := by simp [m]
  have hmk' : (Fin (m - k)) = Fin m2 := by
    simpa using congrArg Fin hmk
  let e : Fin (m - k) ≃ Fin m2 := Equiv.cast hmk'
  let d' : Fin (m - k) → Fin n → Real := fun j => d (e j)
  let b' : Fin (m - k) → Real := fun j => b (e j)
  refine ⟨m, ?_⟩
  refine ⟨k, hk_pos, ?_, ?_⟩
  · simp [m]
  · refine ⟨p, d', a, b', ?_⟩
    have hd' : ∀ j : Fin (m - k), d' j ∈ ray n S₁ := by
      intro j
      simpa [d'] using hdS₁ (e j)
    have hb' : ∀ j : Fin (m - k), 0 ≤ b' j := by
      intro j
      simpa [b'] using hb.1 (e j)
    refine ⟨hpS₀, hd', ha.1, hb', ha.2, ?_⟩
    have hx0eq' : x0 = ∑ i, a i • p i := by
      simpa [convexCombination] using hx0eq
    have huneq' : u = ∑ j, b j • d j := by
      simpa [convexCombination] using huneq
    have hsum : x0 + u = (∑ i, a i • p i) + (∑ j, b j • d j) := by
      simp [hx0eq', huneq']
    have hsum' : (∑ j, b' j • d' j) = ∑ j, b j • d j := by
      simpa [b', d'] using (Equiv.sum_comp e (fun j => b j • d j))
    simpa [hsum'] using hsum

/-- A mixed convex combination lies in the mixed convex hull. -/
lemma mem_mixedConvexHull_of_IsMixedConvexCombination {n m : Nat}
    {S₀ S₁ : Set (Fin n → Real)} {x : Fin n → Real} :
    IsMixedConvexCombination n m S₀ S₁ x → x ∈ mixedConvexHull S₀ S₁ := by
  intro hx
  rcases hx with ⟨k, _hk_pos, _hk_le, p, d, a, b, hpS₀, hdS₁, ha, hb, ha_sum, hx_eq⟩
  let x0 : Fin n → Real := ∑ i, a i • p i
  let u : Fin n → Real := ∑ j, b j • d j
  have hx0 : x0 ∈ conv S₀ := by
    refine (mem_convexHull_iff_exists_fin_isConvexCombination n S₀ x0).2 ?_
    refine ⟨k, p, hpS₀, ?_⟩
    have ha' : IsConvexWeights k a := ⟨ha, ha_sum⟩
    have hcomb :
        IsConvexCombination n k p (convexCombination n k p a) :=
      isConvexCombination_of_isConvexWeights n k p a ha'
    simpa [x0, convexCombination] using hcomb
  have hu : u ∈ cone n S₁ := by
    have hu' :=
      sum_smul_mem_cone_of_nonneg_mem_ray (n := n) (m := m - k) (S₁ := S₁) d b hdS₁ hb
    simpa [u] using hu'
  have hx_add : x0 + u ∈ conv S₀ + cone n S₁ := Set.add_mem_add hx0 hu
  have hx_eq' : x = x0 + u := by
    simpa [x0, u] using hx_eq
  have hx_add' : x ∈ conv S₀ + cone n S₁ := by
    simpa [hx_eq'] using hx_add
  have hrepr := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀ S₁
  have hx_conv : x ∈ conv (S₀ + ray n S₁) := by
    simpa [hrepr.2] using hx_add'
  simpa [hrepr.1] using hx_conv

/-- Proposition 17.0.8 (Algebraic characterization of `conv S`), LaTeX label `prop:algebraic-char`.
With the notation above, a vector `x ∈ ℝⁿ` lies in the (mixed) convex hull if and only if `x` is
a mixed convex combination in the sense of Definition 17.0.7. -/
theorem mem_mixedConvexHull_iff_exists_mixedConvexCombination {n : Nat}
    (S₀ S₁ : Set (Fin n → Real)) (x : Fin n → Real) :
    x ∈ mixedConvexHull S₀ S₁ ↔ ∃ m : Nat, IsMixedConvexCombination n m S₀ S₁ x := by
  constructor
  · intro hx
    exact exists_mixedConvexCombination_of_mem_mixedConvexHull (n := n) (S₀ := S₀) (S₁ := S₁)
      (x := x) hx
  · rintro ⟨m, hx⟩
    exact mem_mixedConvexHull_of_IsMixedConvexCombination (n := n) (m := m)
      (S₀ := S₀) (S₁ := S₁) (x := x) hx

/-- Definition 17.0.9 (Lifting data in `ℝ^{n+1}`), LaTeX label `def:lifting`. Let
`H := {(1, x) | x ∈ ℝⁿ} ⊆ ℝ^{n+1}`. -/
def liftingHyperplane (n : Nat) : Set (Fin (n + 1) → Real) :=
  Set.range fun x : Fin n → Real => Fin.cases (1 : Real) x

/-- Definition 17.0.9 (Lifting data in `ℝ^{n+1}`), continued. Given `S₀ ⊆ ℝⁿ` and a choice of
`S₁' ⊆ ℝⁿ` whose set of directions is `S₁`, define

`S' := {(1, x) | x ∈ S₀} ∪ {(0, x) | x ∈ S₁'} ⊆ ℝ^{n+1}`. -/
def liftingSet {n : Nat} (S₀ S₁' : Set (Fin n → Real)) : Set (Fin (n + 1) → Real) :=
  (fun x : Fin n → Real => Fin.cases (1 : Real) x) '' S₀ ∪
    (fun x : Fin n → Real => Fin.cases (0 : Real) x) '' S₁'

/-- Definition 17.0.9 (Lifting data in `ℝ^{n+1}`), continued. With `S'` as above, define
`K := cone(S')`. -/
def liftingCone {n : Nat} (S₀ S₁' : Set (Fin n → Real)) : Set (Fin (n + 1) → Real) :=
  cone (n + 1) (liftingSet (n := n) S₀ S₁')

/-- The lifted point `(1, x)` lies in the lifting hyperplane. -/
lemma lift1_mem_liftingHyperplane {n : Nat} (x : Fin n → Real) :
    (Fin.cases (1 : Real) x) ∈ liftingHyperplane n := by
  exact ⟨x, rfl⟩

/-- Elements of the lifting set lie on the corresponding ray. -/
lemma liftingSet_mem_ray_of_mem {n : Nat} {S₀ S₁' : Set (Fin n → Real)}
    {v : Fin (n + 1) → Real} (hv : v ∈ liftingSet (n := n) S₀ S₁') :
    v ∈ ray (n + 1) (liftingSet (n := n) S₀ S₁') := by
  refine (Set.mem_insert_iff).2 (Or.inr ?_)
  refine ⟨v, hv, 1, by norm_num, ?_⟩
  simp

/-- A lifted direction from `ray S₁'` lies on the ray of the lifting set. -/
lemma lift0_mem_ray_of_mem_ray {n : Nat} {S₀ S₁' : Set (Fin n → Real)}
    {d : Fin n → Real} (hd : d ∈ ray n S₁') :
    (Fin.cases (0 : Real) d) ∈ ray (n + 1) (liftingSet (n := n) S₀ S₁') := by
  have hd' : d = 0 ∨ d ∈ rayNonneg n S₁' := by
    simpa [ray] using hd
  cases hd' with
  | inl hd0 =>
      subst hd0
      refine (Set.mem_insert_iff).2 (Or.inl ?_)
      ext i
      cases i using Fin.cases <;> simp
  | inr hdRay =>
      rcases hdRay with ⟨x, hxS₁, t, ht, rfl⟩
      have hxLift :
          (Fin.cases (0 : Real) x) ∈ liftingSet (n := n) S₀ S₁' := by
        refine Or.inr ?_
        exact ⟨x, hxS₁, rfl⟩
      have hRay :
          (Fin.cases (0 : Real) (t • x)) ∈
            rayNonneg (n + 1) (liftingSet (n := n) S₀ S₁') := by
        refine ⟨Fin.cases (0 : Real) x, hxLift, t, ht, ?_⟩
        ext i
        cases i using Fin.cases <;> simp
      exact (Set.mem_insert_iff).2 (Or.inr hRay)

/-- A mixed convex combination lifts into the lifting cone. -/
lemma lift_mem_liftingCone_of_IsMixedConvexCombination {n m : Nat}
    {S₀ S₁' : Set (Fin n → Real)} {x : Fin n → Real} :
    IsMixedConvexCombination n m S₀ S₁' x →
      (Fin.cases (1 : Real) x) ∈ liftingCone (n := n) S₀ S₁' := by
  intro hx
  rcases hx with ⟨k, _hk_pos, _hk_le, p, d, a, b, hpS₀, hdS₁, ha, hb, ha_sum, hx_eq⟩
  let pLift : Fin k → Fin (n + 1) → Real := fun i => Fin.cases (1 : Real) (p i)
  let dLift : Fin (m - k) → Fin (n + 1) → Real := fun j => Fin.cases (0 : Real) (d j)
  have hpLift :
      ∀ i, pLift i ∈ ray (n + 1) (liftingSet (n := n) S₀ S₁') := by
    intro i
    have hpLift' : pLift i ∈ liftingSet (n := n) S₀ S₁' := by
      refine Or.inl ?_
      exact ⟨p i, hpS₀ i, rfl⟩
    exact liftingSet_mem_ray_of_mem (v := pLift i) hpLift'
  have hdLift :
      ∀ j, dLift j ∈ ray (n + 1) (liftingSet (n := n) S₀ S₁') := by
    intro j
    exact lift0_mem_ray_of_mem_ray (S₀ := S₀) (S₁' := S₁') (d := d j) (hdS₁ j)
  have hu :
      (∑ i, a i • pLift i) ∈ liftingCone (n := n) S₀ S₁' := by
    have hu' :=
      sum_smul_mem_cone_of_nonneg_mem_ray
        (n := n + 1) (m := k) (S₁ := liftingSet (n := n) S₀ S₁') pLift a hpLift ha
    simpa [liftingCone] using hu'
  have hv :
      (∑ j, b j • dLift j) ∈ liftingCone (n := n) S₀ S₁' := by
    have hv' :=
      sum_smul_mem_cone_of_nonneg_mem_ray
        (n := n + 1) (m := m - k) (S₁ := liftingSet (n := n) S₀ S₁') dLift b hdLift hb
    simpa [liftingCone] using hv'
  have hcone :
      IsConvexCone (n + 1) (liftingCone (n := n) S₀ S₁') := by
    simpa [liftingCone, cone_eq_convexConeGenerated (n := n + 1)
      (S₁ := liftingSet (n := n) S₀ S₁')] using
      (isConvexCone_convexConeGenerated (n := n + 1) (S₁ := liftingSet (n := n) S₀ S₁'))
  have hadd :
      ∀ y ∈ liftingCone (n := n) S₀ S₁', ∀ z ∈ liftingCone (n := n) S₀ S₁',
        y + z ∈ liftingCone (n := n) S₀ S₁' :=
    isConvexCone_add_closed (n := n + 1) (K := liftingCone (n := n) S₀ S₁') hcone
  have hsum :
      (∑ i, a i • pLift i) + (∑ j, b j • dLift j) ∈ liftingCone (n := n) S₀ S₁' :=
    hadd _ hu _ hv
  have hx_eq' :
      (Fin.cases (1 : Real) x) =
        (∑ i, a i • pLift i) + (∑ j, b j • dLift j) := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [pLift, dLift, ha_sum]
    | succ j =>
        have hxj :
            x j = (∑ i, a i • p i) j + (∑ j, b j • d j) j := by
          simpa using congrArg (fun f => f j) hx_eq
        simpa [pLift, dLift] using hxj
  rw [hx_eq']
  exact hsum

/-- Elements of a set lie in its generated ray. -/
lemma mem_ray_of_mem {n : Nat} {S : Set (Fin n → Real)} {x : Fin n → Real} (hx : x ∈ S) :
    x ∈ ray n S := by
  refine (Set.mem_insert_iff).2 (Or.inr ?_)
  refine ⟨x, hx, 1, by norm_num, ?_⟩
  simp

/-- Decompose membership in a ray into either `0` or a nonnegative multiple. -/
lemma ray_mem_decompose {n : Nat} {S : Set (Fin n → Real)} {v : Fin n → Real}
    (hv : v ∈ ray n S) :
    v = 0 ∨ ∃ s ∈ S, ∃ t : Real, 0 ≤ t ∧ v = t • s := by
  have hv' : v = 0 ∨ v ∈ rayNonneg n S := by
    simpa [ray] using hv
  cases hv' with
  | inl h0 =>
      exact Or.inl h0
  | inr hvnonneg =>
      rcases hvnonneg with ⟨s, hs, t, ht, rfl⟩
      exact Or.inr ⟨s, hs, t, ht, rfl⟩

/-- Split membership in the lifting set into point-lifts or direction-lifts. -/
lemma liftingSet_mem_cases {n : Nat} {S₀ S₁' : Set (Fin n → Real)}
    {v : Fin (n + 1) → Real} (hv : v ∈ liftingSet (n := n) S₀ S₁') :
    (∃ p ∈ S₀, v = Fin.cases (1 : Real) p) ∨
      (∃ d ∈ S₁', v = Fin.cases (0 : Real) d) := by
  have hv' :
      v ∈ (fun x : Fin n → Real => Fin.cases (1 : Real) x) '' S₀ ∨
        v ∈ (fun x : Fin n → Real => Fin.cases (0 : Real) x) '' S₁' := by
    simpa [liftingSet] using hv
  cases hv' with
  | inl hv0 =>
      rcases hv0 with ⟨p, hpS₀, rfl⟩
      exact Or.inl ⟨p, hpS₀, rfl⟩
  | inr hv1 =>
      rcases hv1 with ⟨d, hdS₁, rfl⟩
      exact Or.inr ⟨d, hdS₁, rfl⟩

/-- Evaluate a lifted vector at coordinate `0`. -/
lemma fin_cases_zero_real {n : Nat} (a : Real) (p : Fin n → Real) :
    (Fin.cases (motive := fun _ : Fin (n + 1) => Real) a p) 0 = a := by
  rfl

/-- Evaluate a lifted vector at a successor coordinate. -/
lemma fin_cases_succ_real {n : Nat} (a : Real) (p : Fin n → Real) (j : Fin n) :
    (Fin.cases (motive := fun _ : Fin (n + 1) => Real) a p) (Fin.succ j) = p j := by
  rfl

/-- Cone membership yields a finite nonnegative sum of lifting-set generators. -/
lemma exists_nonneg_sum_smul_liftingSet_of_lift_mem_liftingCone {n : Nat}
    {S₀ S₁' : Set (Fin n → Real)} {x : Fin n → Real} :
    (Fin.cases (1 : Real) x) ∈ liftingCone (n := n) S₀ S₁' →
      ∃ (m : Nat) (s : Fin m → Fin (n + 1) → Real) (c : Fin m → Real),
        (∀ i, s i ∈ liftingSet (n := n) S₀ S₁') ∧ (∀ i, 0 ≤ c i) ∧
          (Fin.cases (1 : Real) x) = ∑ i, c i • s i := by
  intro hx
  classical
  have hx' :
      (Fin.cases (1 : Real) x) ∈
        conv (ray (n + 1) (liftingSet (n := n) S₀ S₁')) := by
    simpa [liftingCone, cone] using hx
  rcases (mem_convexHull_iff_exists_fin_isConvexCombination (n := n + 1)
      (S := ray (n + 1) (liftingSet (n := n) S₀ S₁'))
      (y := Fin.cases (1 : Real) x)).1 hx' with ⟨m, z, hz, hcomb⟩
  rcases hcomb with ⟨w, hw0, hw1, hsum⟩
  let I : Type := {i : Fin m // z i ≠ 0}
  have hzdecomp :
      ∀ i : I, ∃ s ∈ liftingSet (n := n) S₀ S₁', ∃ t : Real,
        0 ≤ t ∧ z i.1 = t • s := by
    intro i
    have hzray : z i.1 ∈ ray (n + 1) (liftingSet (n := n) S₀ S₁') := hz i.1
    rcases ray_mem_decompose (n := n + 1)
      (S := liftingSet (n := n) S₀ S₁') (v := z i.1) hzray with h0 | hdecomp
    · exfalso
      exact i.2 (by simpa using h0)
    · exact hdecomp
  choose s hs t ht hz_eq using hzdecomp
  have hsum_subtype :
      (Fin.cases (1 : Real) x) = ∑ i : I, w i.1 • z i.1 := by
    have hsum_filter :
        (∑ i, w i • z i) =
          ∑ i ∈ Finset.univ.filter (fun i => z i ≠ 0), w i • z i := by
      have hsum_if :
          (∑ i, w i • z i) = ∑ i, (if z i ≠ 0 then w i • z i else 0) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases h : z i = 0
        · simp [h]
        · simp [h]
      have hsum_filter' :
          ∑ i ∈ Finset.univ.filter (fun i => z i ≠ 0), w i • z i =
            ∑ i, (if z i ≠ 0 then w i • z i else 0) := by
        simpa using
          (Finset.sum_filter (s := (Finset.univ : Finset (Fin m)))
            (f := fun i => w i • z i) (p := fun i => z i ≠ 0))
      calc
        (∑ i, w i • z i) =
            ∑ i, (if z i ≠ 0 then w i • z i else 0) := hsum_if
        _ = ∑ i ∈ Finset.univ.filter (fun i => z i ≠ 0), w i • z i := by
            symm
            exact hsum_filter'
    have hsum_subtype' :
        ∑ i ∈ Finset.univ.filter (fun i => z i ≠ 0), w i • z i =
          ∑ i : I, w i.1 • z i.1 := by
      refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => z i ≠ 0))
        (p := fun i => z i ≠ 0) (f := fun i => w i • z i) ?_)
      intro i
      simp
    calc
      (Fin.cases (1 : Real) x) = ∑ i, w i • z i := hsum
      _ = ∑ i ∈ Finset.univ.filter (fun i => z i ≠ 0), w i • z i := hsum_filter
      _ = ∑ i : I, w i.1 • z i.1 := hsum_subtype'
  have hsum_subtype' :
      (Fin.cases (1 : Real) x) = ∑ i : I, (w i.1 * t i) • s i := by
    calc
      (Fin.cases (1 : Real) x) = ∑ i : I, w i.1 • z i.1 := hsum_subtype
      _ = ∑ i : I, w i.1 • (t i • s i) := by
          simp [hz_eq]
      _ = ∑ i : I, (w i.1 * t i) • s i := by
          simp [smul_smul]
  let m' := Fintype.card I
  let e : I ≃ Fin m' := Fintype.equivFin I
  let s' : Fin m' → Fin (n + 1) → Real := fun j => s (e.symm j)
  let c' : Fin m' → Real := fun j => w (e.symm j).1 * t (e.symm j)
  have hs' : ∀ j, s' j ∈ liftingSet (n := n) S₀ S₁' := by
    intro j
    simpa [s'] using hs (e.symm j)
  have hc' : ∀ j, 0 ≤ c' j := by
    intro j
    have hw' : 0 ≤ w (e.symm j).1 := hw0 (e.symm j).1
    have ht' : 0 ≤ t (e.symm j) := ht (e.symm j)
    exact mul_nonneg hw' ht'
  have hsum' : (Fin.cases (1 : Real) x) = ∑ j, c' j • s' j := by
    have hsum_equiv :
        ∑ j, c' j • s' j = ∑ i : I, (w i.1 * t i) • s i := by
      simpa [s', c'] using
        (Equiv.sum_comp (e.symm) (fun i : I => (w i.1 * t i) • s i))
    calc
      (Fin.cases (1 : Real) x) = ∑ i : I, (w i.1 * t i) • s i := hsum_subtype'
      _ = ∑ j, c' j • s' j := by
          symm
          exact hsum_equiv
  exact ⟨m', s', c', hs', hc', hsum'⟩

/-- Split a lifting-set sum into a mixed convex combination. -/
lemma split_liftingSet_sum_to_IsMixedConvexCombination {n m : Nat}
    {S₀ S₁' : Set (Fin n → Real)} {x : Fin n → Real}
    (s : Fin m → Fin (n + 1) → Real) (c : Fin m → Real)
    (hs : ∀ i, s i ∈ liftingSet (n := n) S₀ S₁') (hc : ∀ i, 0 ≤ c i)
    (hsum : (Fin.cases (1 : Real) x) = ∑ i, c i • s i) :
    ∃ m', IsMixedConvexCombination n m' S₀ S₁' x := by
  classical
  let lift1 : (Fin n → Real) → Fin (n + 1) → Real :=
    fun y => Fin.cases (motive := fun _ : Fin (n + 1) => Real) (1 : Real) y
  let lift0 : (Fin n → Real) → Fin (n + 1) → Real :=
    fun y => Fin.cases (motive := fun _ : Fin (n + 1) => Real) (0 : Real) y
  let isPoint : Fin m → Prop := fun i =>
    ∃ p ∈ S₀, s i = lift1 p
  have hcases :
      ∀ i, isPoint i ∨ ∃ d ∈ S₁', s i = lift0 d := by
    intro i
    simpa [isPoint, lift1, lift0] using
      (liftingSet_mem_cases (n := n) (S₀ := S₀) (S₁' := S₁') (v := s i) (hs i))
  have hdir_of_not_point :
      ∀ i, ¬ isPoint i → ∃ d ∈ S₁', s i = lift0 d := by
    intro i hnot
    have hcases_i := hcases i
    cases hcases_i with
    | inl hpoint => exact (False.elim (hnot hpoint))
    | inr hdir => exact hdir
  let I : Type := {i : Fin m // isPoint i}
  let J : Type := {i : Fin m // ¬ isPoint i}
  have hpoint : ∀ i : I, ∃ p ∈ S₀, s i.1 = lift1 p := by
    intro i
    exact i.2
  choose p hpS₀ hs_p using hpoint
  have hdir : ∀ j : J, ∃ d ∈ S₁', s j.1 = lift0 d := by
    intro j
    exact hdir_of_not_point j.1 j.2
  choose d hdS₁ hs_d using hdir
  have hsum_point_fun :
      ∑ i ∈ Finset.univ.filter isPoint, c i • s i =
        ∑ i : I, c i.1 • s i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter isPoint)
      (p := isPoint) (f := fun i => c i • s i) ?_)
    intro i
    simp
  have hsum_dir_fun :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ isPoint i), c i • s i =
        ∑ j : J, c j.1 • s j.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => ¬ isPoint i))
      (p := fun i => ¬ isPoint i) (f := fun i => c i • s i) ?_)
    intro i
    simp
  have hsum_split :
      ∑ i, c i • s i =
        (∑ i : I, c i.1 • lift1 (p i)) +
        (∑ j : J, c j.1 • lift0 (d j)) := by
    have hsplit' : ∑ i, c i • s i =
        (∑ i ∈ Finset.univ.filter isPoint, c i • s i) +
        (∑ i ∈ Finset.univ.filter (fun i => ¬ isPoint i), c i • s i) := by
      simpa using
        (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
          (p := isPoint) (f := fun i => c i • s i)).symm
    calc
      ∑ i, c i • s i =
          (∑ i ∈ Finset.univ.filter isPoint, c i • s i) +
          (∑ i ∈ Finset.univ.filter (fun i => ¬ isPoint i), c i • s i) := hsplit'
      _ = (∑ i : I, c i.1 • s i.1) + (∑ j : J, c j.1 • s j.1) := by
          simp [hsum_point_fun, hsum_dir_fun]
      _ = (∑ i : I, c i.1 • lift1 (p i)) +
          (∑ j : J, c j.1 • lift0 (d j)) := by
          have hsumI :
              ∑ i : I, c i.1 • s i.1 =
                ∑ i : I, c i.1 • lift1 (p i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hs_p i]
          have hsumJ :
              ∑ j : J, c j.1 • s j.1 =
                ∑ j : J, c j.1 • lift0 (d j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hs_d j]
          simp [hsumI, hsumJ]
  have hsum_point : ∑ i : I, c i.1 = (1 : Real) := by
    have h0 := congrArg (fun f => f 0) hsum
    have h0' : (1 : Real) = (∑ i, c i • s i) 0 := by
      simpa using h0
    have h0_split := congrArg (fun f => f 0) hsum_split
    have hsum_point' : (1 : Real) = ∑ i : I, c i.1 := by
      calc
        (1 : Real) = (∑ i, c i • s i) 0 := h0'
        _ =
            (∑ i : I, c i.1 • lift1 (p i)) 0 +
            (∑ j : J, c j.1 • lift0 (d j)) 0 := by
              simpa using h0_split
        _ = ∑ i : I, c i.1 := by
            simp [lift1, lift0]
    simpa using hsum_point'.symm
  have hx_eq_subtype :
      x = (∑ i : I, c i.1 • p i) + (∑ j : J, c j.1 • d j) := by
    ext j
    have hsum' :
        (Fin.cases (1 : Real) x) =
          (∑ i : I, c i.1 • lift1 (p i)) + (∑ j : J, c j.1 • lift0 (d j)) := by
      simpa [hsum_split] using hsum
    have hsum_succ := congrArg (fun f => f (Fin.succ j)) hsum'
    simpa [lift1, lift0] using hsum_succ
  let k := Fintype.card I
  let l := Fintype.card J
  let eI : I ≃ Fin k := Fintype.equivFin I
  let eJ : J ≃ Fin l := Fintype.equivFin J
  let p' : Fin k → Fin n → Real := fun i => p (eI.symm i)
  let d' : Fin l → Fin n → Real := fun j => d (eJ.symm j)
  let a : Fin k → Real := fun i => c (eI.symm i).1
  let b : Fin l → Real := fun j => c (eJ.symm j).1
  have hp' : ∀ i, p' i ∈ S₀ := by
    intro i
    simpa [p'] using hpS₀ (eI.symm i)
  have hd' : ∀ j, d' j ∈ ray n S₁' := by
    intro j
    have hd' : d (eJ.symm j) ∈ S₁' := hdS₁ (eJ.symm j)
    simpa [d'] using mem_ray_of_mem (n := n) (S := S₁') (x := d (eJ.symm j)) hd'
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    simpa [a] using hc (eI.symm i).1
  have hb : ∀ j, 0 ≤ b j := by
    intro j
    simpa [b] using hc (eJ.symm j).1
  have hsum_a : ∑ i, a i = (1 : Real) := by
    have hsum_a' : ∑ i, a i = ∑ i : I, c i.1 := by
      simpa [a] using (Equiv.sum_comp (eI.symm) (fun i : I => c i.1))
    simpa [hsum_a'] using hsum_point
  have hx_eq :
      x = (∑ i, a i • p' i) + (∑ j, b j • d' j) := by
    have hsum_p :
        ∑ i : I, c i.1 • p i = ∑ i, a i • p' i := by
      symm
      simpa [a, p'] using
        (Equiv.sum_comp (eI.symm) (fun i : I => c i.1 • p i))
    have hsum_d :
        ∑ j : J, c j.1 • d j = ∑ j, b j • d' j := by
      symm
      simpa [b, d'] using
        (Equiv.sum_comp (eJ.symm) (fun j : J => c j.1 • d j))
    calc
      x = (∑ i : I, c i.1 • p i) + (∑ j : J, c j.1 • d j) := hx_eq_subtype
      _ = (∑ i, a i • p' i) + (∑ j, b j • d' j) := by
          simp [hsum_p, hsum_d]
  have ha_weights : IsConvexWeights k a := ⟨ha, hsum_a⟩
  have hk_pos : 1 ≤ k := one_le_of_IsConvexWeights (m := k) (w := a) ha_weights
  refine ⟨k + l, ?_⟩
  refine ⟨k, hk_pos, ?_, ?_⟩
  · exact Nat.le_add_right k l
  ·
    have hm : k + l - k = l := by simp
    have hFin : Fin (k + l - k) = Fin l := by
      simp [hm]
    let e : Fin (k + l - k) ≃ Fin l := Equiv.cast hFin
    let d'' : Fin (k + l - k) → Fin n → Real := fun j => d' (e j)
    let b'' : Fin (k + l - k) → Real := fun j => b (e j)
    have hd'' : ∀ j, d'' j ∈ ray n S₁' := by
      intro j
      simpa [d'', e] using hd' (e j)
    have hb'' : ∀ j, 0 ≤ b'' j := by
      intro j
      simpa [b'', e] using hb (e j)
    have hsum_b : ∑ j, b j • d' j = ∑ j, b'' j • d'' j := by
      symm
      simpa [b'', d''] using (Equiv.sum_comp e (fun j : Fin l => b j • d' j))
    have hx_eq' :
        x = (∑ i, a i • p' i) + (∑ j, b'' j • d'' j) := by
      simpa [hsum_b] using hx_eq
    refine ⟨p', d'', a, b'', ?_⟩
    exact ⟨hp', hd'', ha, hb'', hsum_a, hx_eq'⟩

/-- Lifting cone membership yields a mixed convex combination. -/
lemma exists_IsMixedConvexCombination_of_lift_mem_liftingCone {n : Nat}
    {S₀ S₁' : Set (Fin n → Real)} {x : Fin n → Real} :
    (Fin.cases (1 : Real) x) ∈ liftingCone (n := n) S₀ S₁' →
      ∃ m : Nat, IsMixedConvexCombination n m S₀ S₁' x := by
  intro hx
  obtain ⟨m, s, c, hs, hc, hsum⟩ :=
    exists_nonneg_sum_smul_liftingSet_of_lift_mem_liftingCone
      (n := n) (S₀ := S₀) (S₁' := S₁') (x := x) hx
  exact split_liftingSet_sum_to_IsMixedConvexCombination
    (n := n) (m := m) (S₀ := S₀) (S₁' := S₁') (x := x) s c hs hc hsum

/-- Proposition 17.0.10 (Cone slice representation), LaTeX label `prop:lift-cone`. With the
notation in Definition 17.0.9, the (mixed) convex hull can be identified with the slice `K ∩ H`
via the correspondence `x ↦ (1, x)`. Equivalently, mixed convex combinations correspond to
nonnegative linear combinations

`λ₁ (1, x₁) + ··· + λₖ (1, xₖ) + λₖ₊₁ (0, xₖ₊₁) + ··· + λₘ (0, xₘ)` in `ℝ^{n+1}`

which lie in the hyperplane `H = {(1, x) | x ∈ ℝⁿ}`. -/
theorem mem_mixedConvexHull_iff_lift_mem_liftingCone_inter_liftingHyperplane {n : Nat}
    (S₀ S₁' : Set (Fin n → Real)) (x : Fin n → Real) :
    x ∈ mixedConvexHull S₀ S₁' ↔
      (Fin.cases (1 : Real) x) ∈ (liftingCone (n := n) S₀ S₁' ∩ liftingHyperplane n) := by
  constructor
  · intro hx
    have hx' :
        (Fin.cases (1 : Real) x) ∈ liftingCone (n := n) S₀ S₁' := by
      have hx'' := (mem_mixedConvexHull_iff_exists_mixedConvexCombination (n := n)
        (S₀ := S₀) (S₁ := S₁') (x := x)).1 hx
      rcases hx'' with ⟨m, hmix⟩
      exact lift_mem_liftingCone_of_IsMixedConvexCombination (n := n) (m := m)
        (S₀ := S₀) (S₁' := S₁') (x := x) hmix
    have hxH : (Fin.cases (1 : Real) x) ∈ liftingHyperplane n :=
      lift1_mem_liftingHyperplane (n := n) x
    exact ⟨hx', hxH⟩
  · intro hx
    rcases hx with ⟨hxK, _hxH⟩
    have hx' :
        ∃ m : Nat, IsMixedConvexCombination n m S₀ S₁' x :=
      exists_IsMixedConvexCombination_of_lift_mem_liftingCone (n := n)
        (S₀ := S₀) (S₁' := S₁') (x := x) hxK
    exact (mem_mixedConvexHull_iff_exists_mixedConvexCombination (n := n)
      (S₀ := S₀) (S₁ := S₁') (x := x)).2 hx'

/-- Mixed convex hull with point-set `{0}` agrees with the cone. -/
lemma mixedConvexHull_singleton_zero_eq_cone {n : Nat} (T : Set (Fin n → Real)) :
    mixedConvexHull ({0} : Set (Fin n → Real)) T = cone n T := by
  have hrepr := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) ({0} : Set
    (Fin n → Real)) T
  have hzero : ({0} : Set (Fin n → Real)) + ray n T = ray n T := by
    ext x
    constructor
    · intro hx
      rcases (Set.mem_add).1 hx with ⟨a, ha, b, hb, rfl⟩
      have ha' : a = 0 := by
        simpa using ha
      subst ha'
      simpa using hb
    · intro hx
      refine (Set.mem_add).2 ?_
      exact ⟨0, by simp, x, hx, by simp⟩
  calc
    mixedConvexHull ({0} : Set (Fin n → Real)) T = conv (({0} : Set (Fin n → Real)) + ray n T) :=
      hrepr.1
    _ = conv (ray n T) := by simp [hzero]
    _ = cone n T := rfl


end Section17
end Chap04
