/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Suwan Wu, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section02_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part1

open scoped Pointwise

section Chap03
section Section11

/-- Text 11.0.1: Let `C₁` and `C₂` be non-empty sets in `ℝ^n`. A hyperplane `H` is said to
separate `C₁` and `C₂` if `C₁` is contained in one of the closed half-spaces associated with `H`
and `C₂` lies in the opposite closed half-space. -/
def HyperplaneSeparates (n : Nat) (H C₁ C₂ : Set (Fin n → Real)) : Prop :=
  C₁.Nonempty ∧
    C₂.Nonempty ∧
      ∃ (b : Fin n → Real) (β : Real),
        b ≠ 0 ∧
          H = {x : Fin n → Real | x ⬝ᵥ b = β} ∧
            ((C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ β} ∧ C₂ ⊆ {x : Fin n → Real | β ≤ x ⬝ᵥ b}) ∨
              (C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ β} ∧ C₁ ⊆ {x : Fin n → Real | β ≤ x ⬝ᵥ b}))

/-- Text 11.0.2: A hyperplane `H` is said to separate `C₁` and `C₂` properly if `C₁` and `C₂`
are not both actually contained in `H` itself. -/
def HyperplaneSeparatesProperly (n : Nat) (H C₁ C₂ : Set (Fin n → Real)) : Prop :=
  HyperplaneSeparates n H C₁ C₂ ∧ ¬ (C₁ ⊆ H ∧ C₂ ⊆ H)

/-- Extract the "properness" clause from `HyperplaneSeparatesProperly`: the two sets cannot both
lie entirely in the separating hyperplane. -/
lemma not_both_subset_of_hyperplaneSeparatesProperly {n : Nat}
    {H C₁ C₂ : Set (Fin n → Real)} :
    HyperplaneSeparatesProperly n H C₁ C₂ → ¬ (C₁ ⊆ H ∧ C₂ ⊆ H) := by
  intro h
  exact h.2

/-- Pure-Prop helper: from `¬ (A ⊆ H ∧ B ⊆ H)` we get `A ⊆ H → ¬ B ⊆ H`. -/
lemma subset_left_imp_not_subset_right {α : Type*} {A B H : Set α}
    (hnot : ¬ (A ⊆ H ∧ B ⊆ H)) : (A ⊆ H → ¬ B ⊆ H) := by
  intro hAH hBH
  exact hnot ⟨hAH, hBH⟩

/-- Pure-Prop helper: from `¬ (A ⊆ H ∧ B ⊆ H)` we get `B ⊆ H → ¬ A ⊆ H`. -/
lemma subset_right_imp_not_subset_left {α : Type*} {A B H : Set α}
    (hnot : ¬ (A ⊆ H ∧ B ⊆ H)) : (B ⊆ H → ¬ A ⊆ H) := by
  intro hBH hAH
  exact hnot ⟨hAH, hBH⟩

/-- Text 11.1.1: Proper separation allows that one (but not both) of the sets be contained in the
separating hyperplane itself. -/
theorem hyperplaneSeparatesProperly_imp_atMostOne_subset_hyperplane (n : Nat)
    (H C₁ C₂ : Set (Fin n → Real)) :
    HyperplaneSeparatesProperly n H C₁ C₂ →
      (C₁ ⊆ H → ¬ C₂ ⊆ H) ∧ (C₂ ⊆ H → ¬ C₁ ⊆ H) := by
  intro h
  have hnot : ¬ (C₁ ⊆ H ∧ C₂ ⊆ H) :=
    not_both_subset_of_hyperplaneSeparatesProperly (H := H) (C₁ := C₁) (C₂ := C₂) h
  refine ⟨subset_left_imp_not_subset_right (A := C₁) (B := C₂) (H := H) hnot, ?_⟩
  exact subset_right_imp_not_subset_left (A := C₁) (B := C₂) (H := H) hnot

/-- Text 11.0.3: A hyperplane `H` is said to separate `C₁` and `C₂` strongly if there exists
`ε > 0` such that `C₁ + ε B` is contained in one of the open half-spaces associated with `H`
and `C₂ + ε B` is contained in the opposite open half-space, where `B` is the unit Euclidean
ball `{x | ‖x‖ ≤ 1}`. (Here `Cᵢ + ε B` consists of points `x` such that `‖x - y‖ ≤ ε` for at
least one `y ∈ Cᵢ`.) -/
def HyperplaneSeparatesStrongly (n : Nat) (H C₁ C₂ : Set (Fin n → Real)) : Prop :=
  C₁.Nonempty ∧
    C₂.Nonempty ∧
      ∃ (b : Fin n → Real) (β : Real),
        b ≠ 0 ∧
          H = {x : Fin n → Real | x ⬝ᵥ b = β} ∧
            ∃ ε : Real,
              0 < ε ∧
                let B : Set (Fin n → Real) := {x | ‖x‖ ≤ (1 : Real)}
                ((C₁ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
                      C₂ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) ∨
                  (C₂ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
                    C₁ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}))

/-- The set `C₁` from Text 11.1.2 (a closed convex "hyperbola region"). -/
def C11_1_2_C1 : Set (Fin 2 → Real) :=
  {x | 0 ≤ x 0 ∧ (1 : Real) ≤ x 0 * x 1}

/-- The set `C₂` from Text 11.1.2 (a closed convex ray on the `x`-axis). -/
def C11_1_2_C2 : Set (Fin 2 → Real) :=
  {x | 0 ≤ x 0 ∧ x 1 = 0}

/-- Any point in `C11_1_2_C1` has strictly positive first coordinate. -/
lemma C11_1_2_C1_pos {x : Fin 2 → Real} (hx : x ∈ C11_1_2_C1) : 0 < x 0 := by
  rcases hx with ⟨hx0, hxprod⟩
  have hx0ne : x 0 ≠ 0 := by
    intro h0
    have : (1 : Real) ≤ 0 := by simpa [h0] using hxprod
    linarith
  exact lt_of_le_of_ne hx0 (by simpa [eq_comm] using hx0ne)

/-- Any point in `C11_1_2_C1` satisfies the equivalent inequality `x0⁻¹ ≤ x1`. -/
lemma inv_le_coord1_of_mem_C11_1_2_C1 {x : Fin 2 → Real} (hx : x ∈ C11_1_2_C1) :
    (x 0)⁻¹ ≤ x 1 := by
  have hx0pos : 0 < x 0 := C11_1_2_C1_pos hx
  exact (inv_le_iff_one_le_mul₀' hx0pos).2 hx.2

/-- The sets `C11_1_2_C1` and `C11_1_2_C2` are closed and convex and disjoint. -/
lemma C11_1_2_closed_convex_disjoint :
    IsClosed C11_1_2_C1 ∧
      IsClosed C11_1_2_C2 ∧
        Convex Real C11_1_2_C1 ∧
          Convex Real C11_1_2_C2 ∧ Disjoint C11_1_2_C1 C11_1_2_C2 := by
  constructor
  · -- `C11_1_2_C1` is closed.
    have h₁ : IsClosed {x : Fin 2 → Real | 0 ≤ x 0} := by
      simpa [Set.preimage, Set.Ici] using (isClosed_Ici.preimage (continuous_apply (0 : Fin 2)))
    have h₂ : IsClosed {x : Fin 2 → Real | (1 : Real) ≤ x 0 * x 1} := by
      simpa [Set.preimage, Set.Ici] using
        (isClosed_Ici.preimage ((continuous_apply (0 : Fin 2)).mul (continuous_apply (1 : Fin 2))))
    have : IsClosed ({x : Fin 2 → Real | 0 ≤ x 0} ∩ {x : Fin 2 → Real | (1 : Real) ≤ x 0 * x 1}) :=
      h₁.inter h₂
    simpa [C11_1_2_C1, Set.setOf_and] using this
  constructor
  · -- `C11_1_2_C2` is closed.
    have h₁ : IsClosed {x : Fin 2 → Real | 0 ≤ x 0} := by
      simpa [Set.preimage, Set.Ici] using (isClosed_Ici.preimage (continuous_apply (0 : Fin 2)))
    have h₂ : IsClosed {x : Fin 2 → Real | x 1 = (0 : Real)} := by
      simpa [Set.preimage] using (isClosed_singleton.preimage (continuous_apply (1 : Fin 2)))
    have : IsClosed ({x : Fin 2 → Real | 0 ≤ x 0} ∩ {x : Fin 2 → Real | x 1 = (0 : Real)}) :=
      h₁.inter h₂
    simpa [C11_1_2_C2, Set.setOf_and, eq_comm] using this
  constructor
  · -- `C11_1_2_C1` is convex.
    intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_⟩
    · -- nonnegativity of the first coordinate is preserved.
      have hx0 : 0 ≤ x 0 := hx.1
      have hy0 : 0 ≤ y 0 := hy.1
      have hx0' : 0 ≤ a * x 0 := mul_nonneg ha hx0
      have hy0' : 0 ≤ b * y 0 := mul_nonneg hb hy0
      simpa [C11_1_2_C1, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using add_nonneg hx0' hy0'
    · -- use convexity of `r ↦ r⁻¹` on `(0,∞)`.
      have hx0pos : 0 < x 0 := C11_1_2_C1_pos hx
      have hy0pos : 0 < y 0 := C11_1_2_C1_pos hy
      have hz0pos : 0 < (a • x + b • y) 0 := by
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith [hab, ha0]
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha0, hb1] using hy0pos
        · by_cases hb0 : b = 0
          · have ha1 : a = 1 := by linarith [hab, hb0]
            simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb0, ha1] using hx0pos
          · have ha' : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
            have hb' : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
            have hx0' : 0 < a * x 0 := mul_pos ha' hx0pos
            have hy0' : 0 < b * y 0 := mul_pos hb' hy0pos
            simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using add_pos hx0' hy0'
      have hxinv : (x 0)⁻¹ ≤ x 1 := inv_le_coord1_of_mem_C11_1_2_C1 hx
      have hyinv : (y 0)⁻¹ ≤ y 1 := inv_le_coord1_of_mem_C11_1_2_C1 hy
      have hinv : ((a • x + b • y) 0)⁻¹ ≤ a * (x 0)⁻¹ + b * (y 0)⁻¹ := by
        -- `convexOn_inv_Ioi` supplies the Jensen inequality.
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          (convexOn_inv_Ioi).2 (x := x 0) (y := y 0) hx0pos hy0pos ha hb hab
      have hle : a * (x 0)⁻¹ + b * (y 0)⁻¹ ≤ (a • x + b • y) 1 := by
        have hxinv' : a * (x 0)⁻¹ ≤ a * x 1 := mul_le_mul_of_nonneg_left hxinv ha
        have hyinv' : b * (y 0)⁻¹ ≤ b * y 1 := mul_le_mul_of_nonneg_left hyinv hb
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using add_le_add hxinv' hyinv'
      have hcoord : ((a • x + b • y) 0)⁻¹ ≤ (a • x + b • y) 1 := le_trans hinv hle
      have : (1 : Real) ≤ (a • x + b • y) 0 * (a • x + b • y) 1 :=
        (inv_le_iff_one_le_mul₀' hz0pos).1 hcoord
      simpa [C11_1_2_C1] using this
  constructor
  · -- `C11_1_2_C2` is convex.
    intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_⟩
    · have hx0 : 0 ≤ x 0 := hx.1
      have hy0 : 0 ≤ y 0 := hy.1
      have hx0' : 0 ≤ a * x 0 := mul_nonneg ha hx0
      have hy0' : 0 ≤ b * y 0 := mul_nonneg hb hy0
      simpa [C11_1_2_C2, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using add_nonneg hx0' hy0'
    · -- the second coordinate stays zero.
      have hx1 : x 1 = 0 := hx.2
      have hy1 : y 1 = 0 := hy.2
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx1, hy1]
  · -- `C11_1_2_C1` and `C11_1_2_C2` are disjoint.
    refine Set.disjoint_left.2 ?_
    intro x hx1 hx2
    have hx2' : x 1 = 0 := hx2.2
    have : (1 : Real) ≤ 0 := by simpa [hx2', mul_zero] using hx1.2
    linarith

/-- Any `ε`-thickening of `C11_1_2_C1` and `C11_1_2_C2` intersects (hence no strong separation). -/
lemma C11_1_2_thickenings_intersect :
    ∀ ε : Real,
      ε > 0 →
        let B : Set (Fin 2 → Real) := {x | ‖x‖ ≤ (1 : Real)}
        ∃ z, z ∈ C11_1_2_C1 + (ε • B) ∧ z ∈ C11_1_2_C2 + (ε • B) := by
  intro ε hεpos
  classical
  dsimp
  set B : Set (Fin 2 → Real) := {x | ‖x‖ ≤ (1 : Real)} with hB
  -- explicit witness `z = (ε⁻¹, ε)`.
  let z : Fin 2 → Real := ![ε⁻¹, ε]
  let y : Fin 2 → Real := ![ε⁻¹, (0 : Real)]
  let u : Fin 2 → Real := Pi.single (1 : Fin 2) (1 : Real)
  have huB : u ∈ B := by
    have hunorm : ‖u‖ = (1 : Real) := by
      simpa [u] using
        (Pi.norm_single (ι := Fin 2) (G := fun _ : Fin 2 => Real) (i := (1 : Fin 2))
          (y := (1 : Real)))
    have hunorm_le : ‖u‖ ≤ (1 : Real) := by simp [hunorm]
    simpa [B] using hunorm_le
  have hzC1 : z ∈ C11_1_2_C1 := by
    have hz0pos : 0 < (ε⁻¹ : Real) := inv_pos.2 hεpos
    refine ⟨le_of_lt hz0pos, ?_⟩
    -- `ε⁻¹ * ε = 1`
    have : (1 : Real) ≤ (ε⁻¹ : Real) * ε := by
      simp [inv_mul_cancel₀ (ne_of_gt hεpos)]
    simpa [z] using this
  have hyC2 : y ∈ C11_1_2_C2 := by
    have hy0pos : 0 < (ε⁻¹ : Real) := inv_pos.2 hεpos
    refine ⟨le_of_lt hy0pos, ?_⟩
    simp [y]
  have hz_mem_C1 : z ∈ C11_1_2_C1 + (ε • B) := by
    have h0B : (0 : Fin 2 → Real) ∈ B := by simp [B]
    have h0 : (0 : Fin 2 → Real) ∈ ε • B := by
      refine ⟨0, h0B, by simp⟩
    refine ⟨z, hzC1, 0, h0, by simp⟩
  have hz_mem_C2 : z ∈ C11_1_2_C2 + (ε • B) := by
    have hεu : (ε • u : Fin 2 → Real) ∈ ε • B := by
      exact ⟨u, huB, rfl⟩
    refine ⟨y, hyC2, (ε • u), hεu, ?_⟩
    -- compute `y + ε•u = z`
    ext i
    fin_cases i <;> simp [z, y, u]
  exact ⟨z, hz_mem_C1, hz_mem_C2⟩

/-- The counterexample sets cannot be separated strongly by any hyperplane. -/
lemma C11_1_2_not_hyperplaneSeparatesStrongly :
    ¬ (∃ H, HyperplaneSeparatesStrongly 2 H C11_1_2_C1 C11_1_2_C2) := by
  intro h
  rcases h with ⟨H, hH⟩
  rcases hH with ⟨_, _, b, β, _, _, ε, hεpos, hcases⟩
  set B : Set (Fin 2 → Real) := {x | ‖x‖ ≤ (1 : Real)}
  have hcases' :
      ((C11_1_2_C1 + (ε • B) ⊆ {x : Fin 2 → Real | x ⬝ᵥ b < β} ∧
            C11_1_2_C2 + (ε • B) ⊆ {x : Fin 2 → Real | β < x ⬝ᵥ b}) ∨
        (C11_1_2_C2 + (ε • B) ⊆ {x : Fin 2 → Real | x ⬝ᵥ b < β} ∧
            C11_1_2_C1 + (ε • B) ⊆ {x : Fin 2 → Real | β < x ⬝ᵥ b})) := by
    simpa [B] using hcases
  have hinter :
      ∃ z, z ∈ C11_1_2_C1 + (ε • B) ∧ z ∈ C11_1_2_C2 + (ε • B) := by
    simpa [B] using (C11_1_2_thickenings_intersect (ε := ε) hεpos)
  rcases hinter with ⟨z, hz1, hz2⟩
  cases hcases' with
  | inl hsub =>
      rcases hsub with ⟨hC1, hC2⟩
      have hzlt : z ⬝ᵥ b < β := hC1 hz1
      have hzgt : β < z ⬝ᵥ b := hC2 hz2
      exact (lt_irrefl β) (lt_trans hzgt hzlt)
  | inr hsub =>
      rcases hsub with ⟨hC2, hC1⟩
      have hzlt : z ⬝ᵥ b < β := hC2 hz2
      have hzgt : β < z ⬝ᵥ b := hC1 hz1
      exact (lt_irrefl β) (lt_trans hzgt hzlt)

/-- Text 11.1.2: Not every pair of disjoint closed convex sets can be separated strongly. -/
theorem exists_disjoint_closed_convex_not_hyperplaneSeparatesStrongly :
    ∃ (n : Nat) (C₁ C₂ : Set (Fin n → Real)),
      IsClosed C₁ ∧
        IsClosed C₂ ∧
          Convex Real C₁ ∧
            Convex Real C₂ ∧
              Disjoint C₁ C₂ ∧ ¬ (∃ H, HyperplaneSeparatesStrongly n H C₁ C₂) := by
  refine ⟨2, C11_1_2_C1, C11_1_2_C2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact C11_1_2_closed_convex_disjoint.1
  · exact C11_1_2_closed_convex_disjoint.2.1
  · exact C11_1_2_closed_convex_disjoint.2.2.1
  · exact C11_1_2_closed_convex_disjoint.2.2.2.1
  · exact C11_1_2_closed_convex_disjoint.2.2.2.2
  · exact C11_1_2_not_hyperplaneSeparatesStrongly

/-- Text 11.0.4: Strict separation means that `C₁` and `C₂` are contained in opposing open
half-spaces determined by a hyperplane `H`. -/
def HyperplaneSeparatesStrictly (n : Nat) (H C₁ C₂ : Set (Fin n → Real)) : Prop :=
  C₁.Nonempty ∧
    C₂.Nonempty ∧
      ∃ (b : Fin n → Real) (β : Real),
        b ≠ 0 ∧
          H = {x : Fin n → Real | x ⬝ᵥ b = β} ∧
            ((C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧ C₂ ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) ∨
              (C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧ C₁ ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}))

/-- Put a properly separating hyperplane in a consistent "oriented" form:
`C₁` lies in `{x | β ≤ x ⬝ᵥ b}` and `C₂` lies in `{x | x ⬝ᵥ b ≤ β}`. -/
lemma hyperplaneSeparatesProperly_oriented (n : Nat) (H C₁ C₂ : Set (Fin n → Real)) :
    HyperplaneSeparatesProperly n H C₁ C₂ →
      ∃ (b : Fin n → Real) (β : Real),
        b ≠ 0 ∧
          H = {x : Fin n → Real | x ⬝ᵥ b = β} ∧
            (∀ x ∈ C₁, β ≤ x ⬝ᵥ b) ∧
              (∀ x ∈ C₂, x ⬝ᵥ b ≤ β) ∧ ¬ (C₁ ⊆ H ∧ C₂ ⊆ H) := by
  rintro ⟨hsep, hnot⟩
  rcases hsep with ⟨hC₁, hC₂, b, β, hb0, rfl, hcases⟩
  refine ?_
  -- If the "wrong" half-space orientation occurs, replace `b` by `-b` and `β` by `-β`.
  cases hcases with
  | inl h =>
      rcases h with ⟨hC₁_le, hC₂_ge⟩
      refine ⟨-b, -β, ?_, ?_, ?_, ?_, hnot⟩
      · simpa using neg_ne_zero.mpr hb0
      · ext x
        simp
      · intro x hx
        have : x ⬝ᵥ b ≤ β := hC₁_le hx
        -- `-β ≤ x ⬝ᵥ (-b)` is equivalent to `x ⬝ᵥ b ≤ β`.
        simpa [dotProduct_neg] using (neg_le_neg this)
      · intro x hx
        have : β ≤ x ⬝ᵥ b := hC₂_ge hx
        -- `x ⬝ᵥ (-b) ≤ -β` is equivalent to `β ≤ x ⬝ᵥ b`.
        simpa [dotProduct_neg] using (neg_le_neg this)
  | inr h =>
      rcases h with ⟨hC₂_le, hC₁_ge⟩
      refine ⟨b, β, hb0, rfl, ?_, ?_, hnot⟩
      · intro x hx
        exact hC₁_ge hx
      · intro x hx
        exact hC₂_le hx

/-- If `C₁` lies in `{x | β ≤ x ⬝ᵥ b}` and `C₂` lies in `{x | x ⬝ᵥ b ≤ β}`, then the extended
infimum of `x ⬝ᵥ b` over `C₁` is at least the extended supremum over `C₂`. -/
lemma sInf_ge_sSup_of_pointwise_bounds_EReal {n : Nat} {C₁ C₂ : Set (Fin n → Real)}
    (b : Fin n → Real) (β : Real)
    (hC₁ : ∀ x ∈ C₁, β ≤ x ⬝ᵥ b) (hC₂ : ∀ x ∈ C₂, x ⬝ᵥ b ≤ β) :
    sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) ≥
      sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂) := by
  -- Show `sSup ≤ β ≤ sInf`.
  have hSup : sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂) ≤ (β : EReal) := by
    refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (EReal.coe_le_coe_iff.2 (hC₂ x hx))
  have hInf : (β : EReal) ≤ sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) := by
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (EReal.coe_le_coe_iff.2 (hC₁ x hx))
  exact le_trans hSup hInf

/-- Properness forces strict separation between the extended `sSup` on `C₁` and extended `sInf`
on `C₂` under the same half-space inclusions. -/
lemma sSup_gt_sInf_of_not_both_subset_levelset_EReal {n : Nat} {C₁ C₂ : Set (Fin n → Real)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty) (b : Fin n → Real) (β : Real)
    (hC₁ : ∀ x ∈ C₁, β ≤ x ⬝ᵥ b) (hC₂ : ∀ x ∈ C₂, x ⬝ᵥ b ≤ β)
    (hnot : ¬ (C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} ∧ C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β})) :
    sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) >
      sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂) := by
  classical
  let f : (Fin n → Real) → EReal := fun x => ((x ⬝ᵥ b : Real) : EReal)
  have hC₂_le_β : sInf (f '' C₂) ≤ (β : EReal) := by
    rcases hC₂ne with ⟨x₀, hx₀⟩
    have hx₀mem : f x₀ ∈ f '' C₂ := ⟨x₀, hx₀, rfl⟩
    have hx₀le : f x₀ ≤ (β : EReal) := EReal.coe_le_coe_iff.2 (hC₂ x₀ hx₀)
    exact le_trans (sInf_le hx₀mem) hx₀le
  have hβ_le_C₁ : (β : EReal) ≤ sSup (f '' C₁) := by
    rcases hC₁ne with ⟨x₀, hx₀⟩
    have hx₀mem : f x₀ ∈ f '' C₁ := ⟨x₀, hx₀, rfl⟩
    have hβle : (β : EReal) ≤ f x₀ := EReal.coe_le_coe_iff.2 (hC₁ x₀ hx₀)
    exact le_trans hβle (le_sSup hx₀mem)
  by_cases hC₁H : C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β}
  · have hC₂H : ¬ C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} := by
      intro hC₂H
      exact hnot ⟨hC₁H, hC₂H⟩
    rcases (Set.not_subset.mp hC₂H) with ⟨y, hyC₂, hyH⟩
    have hyne : y ⬝ᵥ b ≠ β := by simpa using hyH
    have hlt : y ⬝ᵥ b < β :=
      lt_of_le_of_ne (hC₂ y hyC₂) (by simpa [eq_comm] using hyne)
    have hlt' : f y < (β : EReal) := by
      simpa [f] using (EReal.coe_lt_coe_iff.2 hlt)
    have hyMem : f y ∈ f '' C₂ := ⟨y, hyC₂, rfl⟩
    have : sInf (f '' C₂) < sSup (f '' C₁) :=
      lt_of_lt_of_le (lt_of_le_of_lt (sInf_le hyMem) hlt') hβ_le_C₁
    simpa [gt_iff_lt] using this
  · rcases (Set.not_subset.mp hC₁H) with ⟨x, hxC₁, hxH⟩
    have hxne : x ⬝ᵥ b ≠ β := by simpa using hxH
    have hlt : β < x ⬝ᵥ b :=
      lt_of_le_of_ne (hC₁ x hxC₁) (by simpa using hxne.symm)
    have hlt' : (β : EReal) < f x := by
      simpa [f] using (EReal.coe_lt_coe_iff.2 hlt)
    have hxMem : f x ∈ f '' C₁ := ⟨x, hxC₁, rfl⟩
    have hltSup : (β : EReal) < sSup (f '' C₁) :=
      lt_of_lt_of_le hlt' (le_sSup hxMem)
    have : sInf (f '' C₂) < sSup (f '' C₁) :=
      lt_of_le_of_lt hC₂_le_β hltSup
    simpa [gt_iff_lt] using this

/-- Build a properly separating hyperplane from `EReal` inf/sup inequalities (Theorem 11.1). -/
lemma exists_hyperplaneSeparatesProperly_of_EReal_inf_sup_conditions (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ : C₁.Nonempty) (hC₂ : C₂.Nonempty) (b : Fin n → Real)
    (ha :
      sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) ≥
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂))
    (hb :
      sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) >
        sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂)) :
    ∃ H, HyperplaneSeparatesProperly n H C₁ C₂ := by
  classical
  let f : (Fin n → Real) → EReal := fun x => ((x ⬝ᵥ b : Real) : EReal)
  let S₁ : Set EReal := f '' C₁
  let S₂ : Set EReal := f '' C₂
  have hS₂_not_bot : sSup S₂ ≠ (⊥ : EReal) := by
    rcases hC₂ with ⟨x₀, hx₀⟩
    have hx₀mem : f x₀ ∈ S₂ := ⟨x₀, hx₀, rfl⟩
    have hx₀le : f x₀ ≤ sSup S₂ := le_sSup hx₀mem
    have hbotlt : (⊥ : EReal) < f x₀ := by
      simp [f]
    have : (⊥ : EReal) < sSup S₂ := lt_of_lt_of_le hbotlt hx₀le
    exact ne_of_gt ((gt_iff_lt).2 this)
  have hS₂_not_top : sSup S₂ ≠ (⊤ : EReal) := by
    rcases hC₁ with ⟨x₀, hx₀⟩
    have hx₀mem : f x₀ ∈ S₁ := ⟨x₀, hx₀, rfl⟩
    have hle₁ : sSup S₂ ≤ sInf S₁ := by simpa [S₁, S₂, f, ge_iff_le] using ha
    have hle₂ : sInf S₁ ≤ f x₀ := sInf_le hx₀mem
    have hle : sSup S₂ ≤ f x₀ := le_trans hle₁ hle₂
    have hltTop : sSup S₂ < ⊤ := lt_of_le_of_lt hle (by simp [f])
    exact ne_of_lt hltTop
  -- Define `β` as the real number corresponding to `sSup S₂`.
  lift sSup S₂ to Real using ⟨hS₂_not_top, hS₂_not_bot⟩ with β hβ
  have hβE : (β : EReal) = sSup S₂ := by simpa using hβ
  have hb0 : b ≠ 0 := by
    intro hb0
    -- With `b = 0`, dot products are constant, so the strict inequality `hb` is impossible.
    have hS₁ : sSup S₁ = (0 : EReal) := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        simp [f, hb0]
      · rcases hC₁ with ⟨x₀, hx₀⟩
        have hx₀mem : f x₀ ∈ S₁ := ⟨x₀, hx₀, rfl⟩
        have : (0 : EReal) ≤ sSup S₁ := by simpa [S₁, f, hb0] using (le_sSup hx₀mem)
        exact this
    have hS₂' : sInf S₂ = (0 : EReal) := by
      apply le_antisymm
      · rcases hC₂ with ⟨x₀, hx₀⟩
        have hx₀mem : f x₀ ∈ S₂ := ⟨x₀, hx₀, rfl⟩
        have : sInf S₂ ≤ (0 : EReal) := by simpa [S₂, f, hb0] using (sInf_le hx₀mem)
        exact this
      · refine le_sInf ?_
        rintro _ ⟨x, hx, rfl⟩
        simp [f, hb0]
    have : ¬ (sSup S₁ > sInf S₂) := by
      simp [hS₁, hS₂']
    exact this (by simpa [S₁, S₂] using hb)
  refine ⟨{x : Fin n → Real | x ⬝ᵥ b = β}, ?_⟩
  refine ⟨?_, ?_⟩
  · -- `HyperplaneSeparates`
    refine ⟨hC₁, hC₂, b, β, hb0, rfl, ?_⟩
    refine Or.inr ?_
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxmem : f x ∈ S₂ := ⟨x, hx, rfl⟩
      have : f x ≤ (β : EReal) := by
        -- `f x ≤ sSup S₂ = β`
        simpa [hβE] using (le_sSup hxmem)
      exact (EReal.coe_le_coe_iff.1 this)
    · intro x hx
      have hxmem : f x ∈ S₁ := ⟨x, hx, rfl⟩
      have hle₁ : (β : EReal) ≤ sInf S₁ := by
        -- `β = sSup S₂ ≤ sInf S₁`
        simpa [hβE] using (show sSup S₂ ≤ sInf S₁ from (by simpa [S₁, S₂, f, ge_iff_le] using ha))
      have hle₂ : sInf S₁ ≤ f x := sInf_le hxmem
      have : (β : EReal) ≤ f x := le_trans hle₁ hle₂
      exact (EReal.coe_le_coe_iff.1 this)
  · -- `¬ (C₁ ⊆ H ∧ C₂ ⊆ H)` using the strict inequality `hb`
    intro hsub
    rcases hsub with ⟨hC₁H, hC₂H⟩
    have hS₁eq : sSup S₁ = (β : EReal) := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        have : x ⬝ᵥ b = β := hC₁H hx
        simp [f, this]
      · rcases hC₁ with ⟨x₀, hx₀⟩
        have hx₀mem : f x₀ ∈ S₁ := ⟨x₀, hx₀, rfl⟩
        have hβle : (β : EReal) ≤ sSup S₁ := by
          have : f x₀ ≤ sSup S₁ := le_sSup hx₀mem
          have hx₀eq : x₀ ⬝ᵥ b = β := hC₁H hx₀
          simpa [f, hx₀eq] using this
        exact hβle
    have hS₂eq : sInf S₂ = (β : EReal) := by
      apply le_antisymm
      · rcases hC₂ with ⟨x₀, hx₀⟩
        have hx₀mem : f x₀ ∈ S₂ := ⟨x₀, hx₀, rfl⟩
        have hle : sInf S₂ ≤ (β : EReal) := by
          have : sInf S₂ ≤ f x₀ := sInf_le hx₀mem
          have hx₀eq : x₀ ⬝ᵥ b = β := hC₂H hx₀
          simpa [f, hx₀eq] using this
        exact hle
      · refine le_sInf ?_
        rintro _ ⟨x, hx, rfl⟩
        have : x ⬝ᵥ b = β := hC₂H hx
        simp [f, this]
    have : ¬ (sSup S₁ > sInf S₂) := by
      simp [hS₁eq, hS₂eq]
    exact this (by simpa [S₁, S₂] using hb)

/-- Theorem 11.1: Let `C₁` and `C₂` be non-empty sets in `ℝ^n`.

There exists a hyperplane separating `C₁` and `C₂` properly if and only if there exists a
vector `b` such that:

(a) `inf {⟪x, b⟫ | x ∈ C₁} ≥ sup {⟪x, b⟫ | x ∈ C₂}`,
(b) `sup {⟪x, b⟫ | x ∈ C₁} > inf {⟪x, b⟫ | x ∈ C₂}`.

There exists a hyperplane separating `C₁` and `C₂` strongly if and only if there exists a
vector `b` such that:

(c) `inf {⟪x, b⟫ | x ∈ C₁} > sup {⟪x, b⟫ | x ∈ C₂}`. -/
theorem exists_hyperplaneSeparatesProperly_iff (n : Nat) (C₁ C₂ : Set (Fin n → Real))
    (hC₁ : C₁.Nonempty) (hC₂ : C₂.Nonempty) :
    (∃ H, HyperplaneSeparatesProperly n H C₁ C₂) ↔
      ∃ b : Fin n → Real,
        sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) ≥
            sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂) ∧
          sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) >
            sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂) := by
  constructor
  · rintro ⟨H, hsep⟩
    rcases hyperplaneSeparatesProperly_oriented n H C₁ C₂ hsep with
      ⟨b, β, hb0, hH, hC₁β, hC₂β, hnot⟩
    refine ⟨b, ?_, ?_⟩
    · exact sInf_ge_sSup_of_pointwise_bounds_EReal b β hC₁β hC₂β
    · have : sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) >
          sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂) := by
        -- Convert properness into strict inequality on `sSup/sInf`.
        -- Use `hnot`, rewritten via `hH`, to match the expected level set.
        have hnot' : ¬ (C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} ∧ C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β}) := by
          simpa [hH] using hnot
        exact
          sSup_gt_sInf_of_not_both_subset_levelset_EReal (hC₁ne := hC₁) (hC₂ne := hC₂) b β
            hC₁β hC₂β hnot'
      exact this
  · rintro ⟨b, ha, hb⟩
    exact exists_hyperplaneSeparatesProperly_of_EReal_inf_sup_conditions n C₁ C₂ hC₁ hC₂ b ha hb

/-- Theorem 11.1 (strong separation): Let `C₁` and `C₂` be non-empty sets in `ℝ^n`. There exists
a hyperplane separating `C₁` and `C₂` strongly if and only if there exists a vector `b` such that
`inf {⟪x, b⟫ | x ∈ C₁} > sup {⟪x, b⟫ | x ∈ C₂}`. -/
theorem exists_hyperplaneSeparatesStrongly_iff (n : Nat) (C₁ C₂ : Set (Fin n → Real))
    (hC₁ : C₁.Nonempty) (hC₂ : C₂.Nonempty) :
    (∃ H, HyperplaneSeparatesStrongly n H C₁ C₂) ↔
      ∃ b : Fin n → Real,
        sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₁) >
          sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal)) '' C₂) := by
  classical
  constructor
  · rintro ⟨H, hsep⟩
    rcases hsep with ⟨_, _, b, β, hb0, _, ε, hεpos, hcases⟩
    let B : Set (Fin n → Real) := {x | ‖x‖ ≤ (1 : Real)}
    have hcases' :
        ((C₁ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
              C₂ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) ∨
          (C₂ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
              C₁ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b})) := by
      simpa [B] using hcases
    have hOriented :
        ∃ (b' : Fin n → Real) (β' : Real),
          b' ≠ 0 ∧
            C₂ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b' < β'} ∧
              C₁ + (ε • B) ⊆ {x : Fin n → Real | β' < x ⬝ᵥ b'} := by
      cases hcases' with
      | inl h =>
          rcases h with ⟨hC₁lt, hC₂gt⟩
          refine ⟨-b, -β, neg_ne_zero.mpr hb0, ?_, ?_⟩
          · intro z hz
            have hz' : (β : Real) < z ⬝ᵥ b := hC₂gt hz
            have : z ⬝ᵥ (-b) < (-β : Real) := by
              have : -(z ⬝ᵥ b) < (-β : Real) := neg_lt_neg hz'
              simpa [dotProduct_neg] using this
            exact this
          · intro z hz
            have hz' : z ⬝ᵥ b < (β : Real) := hC₁lt hz
            have : (-β : Real) < z ⬝ᵥ (-b) := by
              have : (-β : Real) < -(z ⬝ᵥ b) := neg_lt_neg hz'
              simpa [dotProduct_neg] using this
            exact this
      | inr h =>
          rcases h with ⟨hC₂lt, hC₁gt⟩
          exact ⟨b, β, hb0, hC₂lt, hC₁gt⟩
    rcases hOriented with ⟨b', β', hb'0, hC₂lt, hC₁gt⟩
    rcases Function.ne_iff.mp hb'0 with ⟨j, hj⟩
    let a : Real := if 0 ≤ b' j then 1 else -1
    let v : Fin n → Real := Pi.single j a
    have hvB : v ∈ B := by
      have ha : ‖a‖ ≤ (1 : Real) := by
        by_cases h : 0 ≤ b' j <;> simp [a, h]
      have hvnorm : ‖v‖ = ‖a‖ := by
        simpa [v] using
          (Pi.norm_single (ι := Fin n) (G := fun _ : Fin n => Real) (i := j) (y := a))
      simpa [B, hvnorm] using ha
    have hvdot : v ⬝ᵥ b' = |b' j| := by
      have : v ⬝ᵥ b' = a * b' j := by simp [v]
      by_cases h : 0 ≤ b' j
      · have ha : a = 1 := by simp [a, h]
        simp [this, ha, abs_of_nonneg h]
      · have hneg : b' j < 0 := lt_of_not_ge h
        have ha : a = -1 := by simp [a, h]
        simp [this, ha, abs_of_neg hneg]
    let m : Real := ε * |b' j|
    have hmpos : 0 < m := by
      exact mul_pos hεpos (abs_pos.2 hj)
    have hC₁_strict : ∀ x ∈ C₁, β' + m < x ⬝ᵥ b' := by
      intro x hx
      have hnegvB : (-v) ∈ B := by simpa [B, norm_neg] using hvB
      have hmem_neg : (-(ε • v) : Fin n → Real) ∈ ε • B := by
        refine ⟨-v, hnegvB, by simp [smul_neg]⟩
      have hmem : x + (-(ε • v) : Fin n → Real) ∈ C₁ + (ε • B) := by
        exact ⟨x, hx, -(ε • v), hmem_neg, rfl⟩
      have hz : (β' : Real) < (x + (-(ε • v) : Fin n → Real)) ⬝ᵥ b' := hC₁gt hmem
      have hz' : (β' : Real) < x ⬝ᵥ b' - m := by
        simpa [m, dotProduct_add, smul_dotProduct, hvdot, sub_eq_add_neg] using hz
      linarith
    have hC₂_strict : ∀ y ∈ C₂, y ⬝ᵥ b' < β' - m := by
      intro y hy
      have hmem_pos : (ε • v : Fin n → Real) ∈ ε • B := ⟨v, hvB, rfl⟩
      have hmem : y + (ε • v : Fin n → Real) ∈ C₂ + (ε • B) := by
        exact ⟨y, hy, (ε • v), hmem_pos, rfl⟩
      have hz : (y + (ε • v : Fin n → Real)) ⬝ᵥ b' < (β' : Real) := hC₂lt hmem
      have hz' : y ⬝ᵥ b' + m < (β' : Real) := by
        simpa [m, dotProduct_add, smul_dotProduct, hvdot] using hz
      linarith
    have hInf :
        ((β' + m : Real) : EReal) ≤
          sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b' : Real) : EReal)) '' C₁) := by
      refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      exact EReal.coe_le_coe_iff.2 (le_of_lt (hC₁_strict x hx))
    have hSup :
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b' : Real) : EReal)) '' C₂) ≤
          ((β' - m : Real) : EReal) := by
      refine sSup_le ?_
      rintro _ ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe_iff.2 (le_of_lt (hC₂_strict y hy))
    have hmid : ((β' - m : Real) : EReal) < ((β' + m : Real) : EReal) := by
      exact EReal.coe_lt_coe_iff.2 (by linarith [hmpos])
    have : sSup ((fun x : Fin n → Real => ((x ⬝ᵥ b' : Real) : EReal)) '' C₂) <
        sInf ((fun x : Fin n → Real => ((x ⬝ᵥ b' : Real) : EReal)) '' C₁) :=
      lt_of_lt_of_le (lt_of_le_of_lt hSup hmid) hInf
    exact ⟨b', by simpa [gt_iff_lt] using this⟩
  · rintro ⟨b, hab⟩
    let f : (Fin n → Real) → EReal := fun x => ((x ⬝ᵥ b : Real) : EReal)
    let S₁ : Set EReal := f '' C₁
    let S₂ : Set EReal := f '' C₂
    have hab' : sSup S₂ < sInf S₁ := (gt_iff_lt).1 hab
    have hb0 : b ≠ 0 := by
      intro hb0
      have hS₁ : S₁ = {(0 : EReal)} := by
        simpa [S₁, f, hb0] using (hC₁.image_const (0 : EReal))
      have hS₂ : S₂ = {(0 : EReal)} := by
        simpa [S₂, f, hb0] using (hC₂.image_const (0 : EReal))
      have habS : sInf S₁ > sSup S₂ := by
        simpa [S₁, S₂, f] using hab
      have habS' := habS
      simp [hS₁, hS₂] at habS'
    rcases hC₁ with ⟨x₀, hx₀⟩
    rcases hC₂ with ⟨y₀, hy₀⟩
    have hS₂_not_bot : sSup S₂ ≠ (⊥ : EReal) := by
      have hyMem : f y₀ ∈ S₂ := ⟨y₀, hy₀, rfl⟩
      have hbotlt : (⊥ : EReal) < f y₀ := by simp [f]
      have : (⊥ : EReal) < sSup S₂ := lt_of_lt_of_le hbotlt (le_sSup hyMem)
      exact ne_of_gt ((gt_iff_lt).2 this)
    have hS₁_not_top : sInf S₁ ≠ (⊤ : EReal) := by
      have hxMem : f x₀ ∈ S₁ := ⟨x₀, hx₀, rfl⟩
      have : sInf S₁ ≤ f x₀ := sInf_le hxMem
      have : sInf S₁ < ⊤ := lt_of_le_of_lt this (by simp [f])
      exact ne_of_lt this
    have hS₂_not_top : sSup S₂ ≠ (⊤ : EReal) := by
      intro htop
      have hab'' := hab'
      simp [htop] at hab''
    have hS₁_not_bot : sInf S₁ ≠ (⊥ : EReal) := by
      have : (⊥ : EReal) < sSup S₂ := by
        -- from nonemptiness of `C₂`
        have hyMem : f y₀ ∈ S₂ := ⟨y₀, hy₀, rfl⟩
        exact lt_of_lt_of_le (by simp [f]) (le_sSup hyMem)
      have : (⊥ : EReal) < sInf S₁ := lt_trans this hab'
      exact ne_of_gt ((gt_iff_lt).2 this)
    lift sSup S₂ to Real using ⟨hS₂_not_top, hS₂_not_bot⟩ with α₂ hα₂
    lift sInf S₁ to Real using ⟨hS₁_not_top, hS₁_not_bot⟩ with α₁ hα₁
    have hα₂E : (α₂ : EReal) = sSup S₂ := by simpa using hα₂
    have hα₁E : (α₁ : EReal) = sInf S₁ := by simpa using hα₁
    have hαlt : α₂ < α₁ := by
      have : (α₂ : EReal) < (α₁ : EReal) := by
        simpa [hα₂E, hα₁E] using hab'
      exact EReal.coe_lt_coe_iff.1 this
    let β : Real := (α₁ + α₂) / 2
    let B : Set (Fin n → Real) := {x | ‖x‖ ≤ (1 : Real)}
    let M : Real := ∑ i : Fin n, |b i|
    let K : Real := M + 1
    let δ : Real := (α₁ - α₂) / 4
    let ε : Real := δ / K
    have hKpos : 0 < K := by
      have hMnonneg : 0 ≤ M := by
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith [hMnonneg]
    have hδpos : 0 < δ := by
      have : 0 < α₁ - α₂ := sub_pos.2 hαlt
      exact div_pos this (by positivity)
    have hεpos : 0 < ε := by
      exact div_pos hδpos hKpos
    have hMK : M ≤ K := by linarith
    have abs_dotProduct_le (v : Fin n → Real) (hv : ‖v‖ ≤ (1 : Real)) : |v ⬝ᵥ b| ≤ M := by
      classical
      have hv' : ∀ i : Fin n, |v i| ≤ (1 : Real) := by
        have hv'' :
            ∀ i : Fin n, ‖v i‖ ≤ (1 : Real) :=
          (pi_norm_le_iff_of_nonneg (x := v) (r := (1 : Real)) (by positivity)).1 hv
        intro i
        simpa [Real.norm_eq_abs] using hv'' i
      have hsum :
          |∑ i : Fin n, v i * b i| ≤ ∑ i : Fin n, |v i * b i| := by
        simpa using (Finset.abs_sum_le_sum_abs (f := fun i : Fin n => v i * b i) Finset.univ)
      calc
        |v ⬝ᵥ b| = |∑ i : Fin n, v i * b i| := by simp [dotProduct]
        _ ≤ ∑ i : Fin n, |v i * b i| := hsum
        _ = ∑ i : Fin n, |v i| * |b i| := by simp [abs_mul]
        _ ≤ ∑ i : Fin n, |b i| := by
            refine Finset.sum_le_sum ?_
            intro i _
            have : |v i| * |b i| ≤ (1 : Real) * |b i| :=
              mul_le_mul_of_nonneg_right (hv' i) (abs_nonneg (b i))
            simpa [one_mul] using this
    have hεK : ε * K = δ := by
      have hKne : K ≠ 0 := ne_of_gt hKpos
      -- `ε = δ / K`.
      simp [ε, div_eq_mul_inv, hKne]
    have hεM : ε * M ≤ δ := by
      have hεnonneg : 0 ≤ ε := le_of_lt hεpos
      have : ε * M ≤ ε * K := mul_le_mul_of_nonneg_left hMK hεnonneg
      simpa [hεK] using this
    have hx_ge (x : Fin n → Real) (hx : x ∈ C₁) : α₁ ≤ x ⬝ᵥ b := by
      have hxMem : f x ∈ S₁ := ⟨x, hx, rfl⟩
      have : sInf S₁ ≤ f x := sInf_le hxMem
      have : (α₁ : EReal) ≤ ((x ⬝ᵥ b : Real) : EReal) := by simpa [f, hα₁E] using this
      exact EReal.coe_le_coe_iff.1 this
    have hy_le (y : Fin n → Real) (hy : y ∈ C₂) : y ⬝ᵥ b ≤ α₂ := by
      have hyMem : f y ∈ S₂ := ⟨y, hy, rfl⟩
      have : f y ≤ sSup S₂ := le_sSup hyMem
      have : ((y ⬝ᵥ b : Real) : EReal) ≤ (α₂ : EReal) := by simpa [f, hα₂E] using this
      exact EReal.coe_le_coe_iff.1 this
    have hC₁β : C₁ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b} := by
      intro z hz
      rcases hz with ⟨x, hx, u, hu, rfl⟩
      rcases hu with ⟨v, hvB, rfl⟩
      have hvnorm : ‖v‖ ≤ (1 : Real) := by simpa [B] using hvB
      have hvb : |v ⬝ᵥ b| ≤ M := abs_dotProduct_le v hvnorm
      have habs : |(ε • v : Fin n → Real) ⬝ᵥ b| ≤ δ := by
        have : |(ε • v : Fin n → Real) ⬝ᵥ b| = ε * |v ⬝ᵥ b| := by
          simp [smul_dotProduct, abs_of_pos hεpos, abs_mul]
        have : |(ε • v : Fin n → Real) ⬝ᵥ b| ≤ ε * M := by
          have hεnonneg : 0 ≤ ε := le_of_lt hεpos
          exact this.le.trans (mul_le_mul_of_nonneg_left hvb hεnonneg)
        exact this.trans hεM
      have hpert : -(δ : Real) ≤ (ε • v : Fin n → Real) ⬝ᵥ b :=
        (abs_le.mp habs).1
      have hβlt : β < α₁ - δ := by
        simp [β, δ]
        linarith [hαlt]
      have : β < x ⬝ᵥ b + (ε • v : Fin n → Real) ⬝ᵥ b := by
        have hxge : α₁ ≤ x ⬝ᵥ b := hx_ge x hx
        have : α₁ - δ ≤ x ⬝ᵥ b + (ε • v : Fin n → Real) ⬝ᵥ b := by linarith
        exact lt_of_lt_of_le hβlt this
      simpa [dotProduct_add] using this
    have hC₂β : C₂ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} := by
      intro z hz
      rcases hz with ⟨y, hy, u, hu, rfl⟩
      rcases hu with ⟨v, hvB, rfl⟩
      have hvnorm : ‖v‖ ≤ (1 : Real) := by simpa [B] using hvB
      have hvb : |v ⬝ᵥ b| ≤ M := abs_dotProduct_le v hvnorm
      have habs : |(ε • v : Fin n → Real) ⬝ᵥ b| ≤ δ := by
        have : |(ε • v : Fin n → Real) ⬝ᵥ b| = ε * |v ⬝ᵥ b| := by
          simp [smul_dotProduct, abs_of_pos hεpos, abs_mul]
        have : |(ε • v : Fin n → Real) ⬝ᵥ b| ≤ ε * M := by
          have hεnonneg : 0 ≤ ε := le_of_lt hεpos
          exact this.le.trans (mul_le_mul_of_nonneg_left hvb hεnonneg)
        exact this.trans hεM
      have hpert : (ε • v : Fin n → Real) ⬝ᵥ b ≤ δ :=
        (abs_le.mp habs).2
      have hβgt : α₂ + δ < β := by
        simp [β, δ]
        linarith [hαlt]
      have : y ⬝ᵥ b + (ε • v : Fin n → Real) ⬝ᵥ b < β := by
        have hyle : y ⬝ᵥ b ≤ α₂ := hy_le y hy
        have : y ⬝ᵥ b + (ε • v : Fin n → Real) ⬝ᵥ b ≤ α₂ + δ := by linarith
        exact lt_of_le_of_lt this hβgt
      simpa [dotProduct_add] using this
    refine ⟨{x : Fin n → Real | x ⬝ᵥ b = β}, ?_⟩
    refine ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, b, β, hb0, rfl, ε, hεpos, ?_⟩
    simpa [B] using Or.inr ⟨hC₂β, hC₁β⟩

/-- The quotient map `mkQ` collapses an affine subspace to a singleton in the quotient. -/
lemma image_mkQ_affineSubspace_eq_singleton {n : Nat} (M : AffineSubspace ℝ (Fin n → ℝ))
    {m0 : Fin n → ℝ} (hm0 : m0 ∈ M) :
    (M.direction.mkQ '' (M : Set (Fin n → ℝ))) = {M.direction.mkQ m0} := by
  classical
  ext q
  constructor
  · rintro ⟨m, hmM, rfl⟩
    have hsub : m - m0 ∈ M.direction := by
      simpa [vsub_eq_sub] using (AffineSubspace.vsub_mem_direction hmM hm0)
    have hEq :
        (Submodule.Quotient.mk m : (Fin n → ℝ) ⧸ M.direction) = Submodule.Quotient.mk m0 :=
      (Submodule.Quotient.eq (p := M.direction)).2 hsub
    have : M.direction.mkQ m = M.direction.mkQ m0 := by
      simpa [Submodule.mkQ_apply] using hEq
    simp [this]
  · intro hq
    have : q = M.direction.mkQ m0 := by simpa using hq
    subst this
    exact ⟨m0, hm0, rfl⟩

/-- Disjointness forces the distinguished quotient point `mkQ m0` (with `m0 ∈ M`) to lie outside
`mkQ '' C`. -/
lemma quotient_point_not_mem_image_of_disjoint {n : Nat} {C : Set (Fin n → ℝ)}
    (M : AffineSubspace ℝ (Fin n → ℝ)) {m0 : Fin n → ℝ} (hm0 : m0 ∈ M)
    (hCM : Disjoint C (M : Set (Fin n → ℝ))) :
    M.direction.mkQ m0 ∉ (M.direction.mkQ '' C) := by
  classical
  intro hmem
  rcases hmem with ⟨c, hcC, hcEq⟩
  have hsub : c - m0 ∈ M.direction := by
    have hcEq' :
        (Submodule.Quotient.mk c : (Fin n → ℝ) ⧸ M.direction) = Submodule.Quotient.mk m0 := by
      simpa [Submodule.mkQ_apply] using hcEq
    exact (Submodule.Quotient.eq (p := M.direction)).1 hcEq'
  have hcM : c ∈ M := by
    -- membership in an affine subspace is characterized by `vsub` membership in the direction
    have : c -ᵥ m0 ∈ M.direction := by simpa [vsub_eq_sub] using hsub
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hm0 c).1 this
  exact (Set.disjoint_left.1 hCM) hcC hcM

/-- If `x₀` lies outside the affine span of a nonempty set `S`, there is a continuous linear
functional which is constant on `affineSpan ℝ S` and strictly separates `x₀` from `S`. -/
lemma exists_strictSep_point_of_not_mem_affineSpan {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsModuleTopology ℝ E] {S : Set E} (hS : S.Nonempty) {x0 : E}
    (hx0 : x0 ∉ affineSpan ℝ S) : ∃ f : StrongDual ℝ E, ∀ x ∈ S, f x < f x0 := by
  classical
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd ℝ E
  obtain ⟨p, hpS⟩ := hS
  let A : AffineSubspace ℝ E := affineSpan ℝ S
  have hpA : p ∈ A := subset_affineSpan ℝ S hpS
  have hvnot : x0 -ᵥ p ∉ A.direction := by
    intro hv
    exact hx0 <| (AffineSubspace.vsub_right_mem_direction_iff_mem hpA x0).1 hv
  obtain ⟨l, hlv, hker⟩ := Submodule.exists_le_ker_of_notMem (p := A.direction) hvnot
  let f0 : StrongDual ℝ E :=
    { toLinearMap := l
      cont := IsModuleTopology.continuous_of_linearMap (R := ℝ) (A := E) (B := ℝ) l }
  have hdiffne : f0 (x0 - p) ≠ 0 := by
    simpa [f0, vsub_eq_sub] using hlv
  let f : StrongDual ℝ E := if f0 (x0 - p) < 0 then -f0 else f0
  refine ⟨f, ?_⟩
  intro x hxS
  have hxA : x ∈ A := subset_affineSpan ℝ S hxS
  have hxsub : x - p ∈ A.direction := by
    simpa [vsub_eq_sub] using (AffineSubspace.vsub_mem_direction hxA hpA)
  have hxker' : l (x - p) = 0 := by
    have : x - p ∈ LinearMap.ker l := hker hxsub
    simpa using this
  have hxEq : f0 x = f0 p := by
    have : l x - l p = 0 := by simpa [LinearMap.map_sub] using hxker'
    have : l x = l p := sub_eq_zero.mp this
    simpa [f0] using this
  have hx0decomp : f0 x0 = f0 (x0 - p) + f0 p := by
    nth_rewrite 1 [← sub_add_cancel x0 p]
    simp
  by_cases hneg : f0 (x0 - p) < 0
  · -- If the difference is negative, negate to make it positive.
    have hx0lt : f0 x0 < f0 x := by
      have : f0 x0 < f0 p := by linarith [hx0decomp, hneg]
      simpa [hxEq] using this
    -- `(-f0) x < (-f0) x0` is equivalent to `f0 x0 < f0 x`.
    have : (-f0) x < (-f0) x0 := by simpa using (neg_lt_neg hx0lt)
    have hf : f = -f0 := by
      unfold f
      exact if_pos hneg
    simpa [hf] using this
  · have hpos : 0 < f0 (x0 - p) :=
      lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hdiffne)
    have hlt : f0 x < f0 x0 := by
      have : f0 p < f0 x0 := by linarith [hx0decomp, hpos]
      simpa [hxEq] using this
    have hf : f = f0 := by
      unfold f
      exact if_neg hneg
    simpa [hf] using hlt

/-- If `C` is relatively open in its affine span, then translating by a point `c0 ∈ C` yields an
open subset of the direction submodule `(affineSpan ℝ C).direction`. -/
lemma isOpen_translate_in_direction_of_relOpen {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsModuleTopology ℝ E] {C : Set E}
    (hCrelopen : ∃ U : Set E, IsOpen U ∧ C = U ∩ (affineSpan ℝ C : Set E)) {c0 : E} (hc0 : c0 ∈ C) :
    IsOpen {v : (affineSpan ℝ C).direction | ((v : E) + c0) ∈ C} := by
  classical
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd ℝ E
  rcases hCrelopen with ⟨U, hUopen, hCeq⟩
  have hc0A : c0 ∈ (affineSpan ℝ C : Set E) := subset_affineSpan ℝ C hc0
  have hEq :
      {v : (affineSpan ℝ C).direction | ((v : E) + c0) ∈ C} =
        {v : (affineSpan ℝ C).direction | ((v : E) + c0) ∈ U} := by
    ext v
    constructor
    · intro hvC
      have hxEq :
          ((v : E) + c0 ∈ C) ↔ ((v : E) + c0 ∈ U ∩ (affineSpan ℝ C : Set E)) :=
        Iff.of_eq (congrArg (fun s : Set E => ((v : E) + c0) ∈ s) hCeq)
      exact (hxEq.1 hvC).1
    · intro hvU
      have hvA : (v : E) + c0 ∈ (affineSpan ℝ C : Set E) := by
        have : (v : E) +ᵥ c0 ∈ affineSpan ℝ C :=
          AffineSubspace.vadd_mem_of_mem_direction (s := affineSpan ℝ C) v.2 hc0A
        simpa [vadd_eq_add] using this
      have hxEq :
          ((v : E) + c0 ∈ C) ↔ ((v : E) + c0 ∈ U ∩ (affineSpan ℝ C : Set E)) :=
        Iff.of_eq (congrArg (fun s : Set E => ((v : E) + c0) ∈ s) hCeq)
      exact hxEq.2 ⟨hvU, hvA⟩
  have hcont : Continuous fun v : (affineSpan ℝ C).direction => ((v : E) + c0) := by
    simpa using (continuous_subtype_val.add continuous_const)
  simpa [hEq] using (hUopen.preimage hcont)

/-- If `O` is open in the direction submodule `V0`, then its image in the mapped direction
`Submodule.map π V0` is open. This is the key topological step in the hard case of Theorem 11.2. -/
lemma isOpen_image_direction_mkQ_of_isOpen {n : Nat} (C : Set (Fin n → ℝ))
    (D : Submodule ℝ (Fin n → ℝ)) :
    let Q := (Fin n → ℝ) ⧸ D
    let π : (Fin n → ℝ) →ₗ[ℝ] Q := D.mkQ
    let V0 : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ C).direction
    let f0 : V0 →ₗ[ℝ] Q := π.comp V0.subtype
    let V : Submodule ℝ Q := Submodule.map π V0
    ∀ O : Set V0, IsOpen O →
      IsOpen ((fun v : V0 => (⟨f0 v, by exact ⟨(v : Fin n → ℝ), v.2, rfl⟩⟩ : V)) '' O) := by
  intro Q π V0 f0 V O hO
  classical
  -- Ensure the quotient space `Q` is Hausdorff by using that `D` is closed (finite-dimensional).
  have hDclosed : IsClosed (D : Set (Fin n → ℝ)) := by
    haveI : FiniteDimensional ℝ D := by infer_instance
    exact Submodule.closed_of_finiteDimensional (s := D)
  letI : IsClosed (D : Set (Fin n → ℝ)) := hDclosed
  haveI : T3Space Q := by infer_instance
  haveI : T2Space Q := by infer_instance
  haveI : T2Space V := by infer_instance
  let g : V0 →ₗ[ℝ] V :=
    { toFun := fun v => ⟨f0 v, by exact ⟨(v : Fin n → ℝ), v.2, rfl⟩⟩
      map_add' := by
        intro x y
        ext
        simp [f0]
      map_smul' := by
        intro r x
        ext
        simp [f0] }
  have hgSurj : Function.Surjective g := by
    rintro ⟨y, hyV⟩
    rcases hyV with ⟨x, hxV0, rfl⟩
    refine ⟨⟨x, hxV0⟩, ?_⟩
    ext
    rfl
  -- Pass to the quotient by the kernel, then use the (continuous) isomorphism theorem.
  let K : Submodule ℝ V0 := LinearMap.ker g
  haveI : ContinuousAdd V0 := by infer_instance
  haveI : FiniteDimensional ℝ V0 := by infer_instance
  haveI : T2Space V0 := by infer_instance
  have hgcont : Continuous (g : V0 → V) := g.continuous_of_finiteDimensional
  have hKclosed : IsClosed (K : Set V0) :=
    by
      -- `K = g ⁻¹' {0}` and `{0}` is closed in a `T1` space.
      simpa [K, LinearMap.mem_ker] using (isClosed_singleton.preimage hgcont)
  letI : IsClosed (K : Set V0) := hKclosed
  haveI : T3Space (V0 ⧸ K) := by infer_instance
  haveI : T2Space (V0 ⧸ K) := by infer_instance
  have hmkQopen : IsOpen (K.mkQ '' O) := (Submodule.isOpenMap_mkQ (S := K)) O hO
  let e : (V0 ⧸ K) ≃ₗ[ℝ] V := g.quotKerEquivOfSurjective hgSurj
  let eCL : (V0 ⧸ K) ≃L[ℝ] V := e.toContinuousLinearEquiv
  have heOpenMap : IsOpenMap (eCL : (V0 ⧸ K) → V) := eCL.toHomeomorph.isOpenMap
  have hcomp : ∀ x : V0, (eCL : (V0 ⧸ K) → V) (K.mkQ x) = g x := by
    intro x
    -- Unfold `eCL` to the underlying linear equivalence, then use the isomorphism theorem simp lemma.
    change (e : (V0 ⧸ K) → V) (K.mkQ x) = g x
    -- `K.mkQ x` is definitionally `Submodule.Quotient.mk x`.
    simp [Submodule.mkQ_apply, e, K, g, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have himage : g '' O = (eCL : (V0 ⧸ K) → V) '' (K.mkQ '' O) := by
    ext y
    constructor
    · rintro ⟨x, hxO, rfl⟩
      refine ⟨K.mkQ x, ⟨x, hxO, rfl⟩, ?_⟩
      exact hcomp x
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨x, hxO, rfl⟩
      refine ⟨x, hxO, ?_⟩
      exact (hcomp x).symm
  -- `eCL` is an open map, so the image is open.
  have hopen : IsOpen ((eCL : (V0 ⧸ K) → V) '' (K.mkQ '' O)) := heOpenMap (K.mkQ '' O) hmkQopen
  have hopen' : IsOpen (g '' O) := by simpa [himage] using hopen
  simpa [g] using hopen'

end Section11
end Chap03
