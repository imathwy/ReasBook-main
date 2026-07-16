import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped Rockafellar

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]

local notation "E" => ι → 𝕜

local instance : HasPairing E E 𝕜 where
  pairing x y := ∑ i, x i * y i

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item computes the support function of the explicit coordinate set
  `D = {y | ∑ i, |y i| ≤ 1}` and identifies it with the maximum absolute value of the
  coordinates.
- `core/canonical`: the owner abstractions are the chapter support function `δᵛ(x | C)`,
  the source-facing coordinate `ℓ¹` unit ball
  `coordinateL1Ball = {y | ∑ i, |y i| ≤ 1}`, and the coordinate `ℓ∞` owner `linftyNorm`
  defined intrinsically as the finite maximum `maxᵢ |x i|`.
  The pairing layer is explicit and model-independent:
  `⟪x, y⟫ₚ = ∑ i, x i * y i`, so the support-function statement is proved directly from the
  coordinate formula.
- Layer target: `core/canonical`; the main entry is the pointwise owner theorem
  `supportFunction_coordinateL1Ball_eq_linftyNorm`.

Domain-style sampling used here:
- the project owner `supportFunction` and its notation/specification theorem `supportFunction_def`;
- the coordinate pairing owner `⟪x, y⟫ₚ = ∑ i, x i * y i`;
- the coordinate-set owner `coordinateL1Ball` and coordinate-max owner `linftyNorm`.
-/

/-- The coordinate `ℓ¹` unit ball `D = {y | ∑ i, |y i| ≤ 1}` on a finite coordinate family. -/
def coordinateL1Ball {ι : Type*} [Fintype ι] {𝕜 : Type*}
    [AddCommGroup 𝕜] [LinearOrder 𝕜] [One 𝕜] :
    Set (ι → 𝕜) :=
  {y : ι → 𝕜 | ∑ i, |y i| ≤ 1}

@[simp] theorem mem_coordinateL1Ball {ι : Type*} [Fintype ι] {𝕜 : Type*}
    [AddCommGroup 𝕜] [LinearOrder 𝕜] [One 𝕜] (y : ι → 𝕜) :
    y ∈ coordinateL1Ball ↔ ∑ i, |y i| ≤ 1 :=
  Iff.rfl

/-- Canonical coordinate `ℓ∞` owner used in Text 5.5.0.5:
the finite maximum `maxᵢ |x i|` on a finite coordinate family. -/
def linftyNorm {ι : Type*} [Fintype ι] {𝕜 : Type*} [AddGroup 𝕜] [LinearOrder 𝕜]
    (x : ι → 𝕜) : 𝕜 :=
  if hι : Fintype.card ι = 0 then
    0
  else
    letI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.pos_iff_ne_zero.mpr hι)
    Finset.univ.sup' Finset.univ_nonempty fun i : ι ↦ |x i|

@[simp] theorem linftyNorm_eq_sup'_univ_abs {ι : Type*} [Fintype ι] {𝕜 : Type*}
    [AddGroup 𝕜] [LinearOrder 𝕜] [Nonempty ι] (x : ι → 𝕜) :
    linftyNorm x = Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ |x i|) := by
  have hcard : Fintype.card ι ≠ 0 := by
    exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance)
  simp [linftyNorm, hcard]

/-- Upper bound used in the support-function computation for the coordinate `ℓ¹` ball:
`⟪x, y⟫ ≤ ‖x‖_∞` whenever `∑ i, |y i| ≤ 1`. -/
private theorem pairing_le_linftyNorm_of_mem_coordinateL1Ball
    [Nonempty ι] (x y : E) (hy : y ∈ coordinateL1Ball) :
    (⟪x, y⟫ₚ : 𝕜) ≤ linftyNorm x := by
  have hsum_le_one : ∑ i, |y i| ≤ 1 := hy
  have hxi : ∀ i, |x i| ≤ linftyNorm x := by
    intro i
    rw [linftyNorm_eq_sup'_univ_abs x]
    exact Finset.le_sup' (fun j : ι ↦ |x j|) (Finset.mem_univ i)
  have hterm : ∀ i, |x i * y i| ≤ linftyNorm x * |y i| := by
    intro i
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hxi i) (abs_nonneg (y i))
  have hlin_nonneg : 0 ≤ linftyNorm x := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact le_trans (abs_nonneg (x i)) (hxi i)
  calc
    (⟪x, y⟫ₚ : 𝕜) = ∑ i, x i * y i := rfl
    _ ≤ |∑ i, x i * y i| := le_abs_self _
    _ ≤ ∑ i, |x i * y i| := by
      simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : ι ↦ x i * y i))
    _ ≤ ∑ i, linftyNorm x * |y i| := Finset.sum_le_sum (fun i _ ↦ hterm i)
    _ = linftyNorm x * ∑ i, |y i| := by rw [Finset.mul_sum]
    _ ≤ linftyNorm x * 1 := by
      exact mul_le_mul_of_nonneg_left hsum_le_one hlin_nonneg
    _ = linftyNorm x := by simp

/-- Canonical owner-side theorem for Text 5.5.0.5: the support function of the coordinate
`ℓ¹` unit ball is the coordinate `ℓ∞` norm. -/
theorem supportFunction_coordinateL1Ball_eq_linftyNorm (x : E) :
    δᵛ(x | (coordinateL1Ball : Set E)) = ((linftyNorm x : 𝕜) : WithTopBot 𝕜) := by
  classical
  by_cases hι : IsEmpty ι
  · have hx0 : x = (0 : E) := Subsingleton.elim _ _
    subst hx0
    have hlin0 : linftyNorm (0 : E) = 0 := by
      simp [linftyNorm]
    rw [supportFunction_def, hlin0]
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro y
      have hy_le : (∑ i, (0 : E) i * (y : E) i) ≤ 0 := by
        simp
      change
        (((∑ i, (0 : E) i * (y : E) i : 𝕜) : WithTopBot 𝕜) ≤
          (0 : WithTopBot 𝕜))
      exact_mod_cast hy_le
    · refine le_iSup_of_le ⟨(0 : E), by simp [coordinateL1Ball]⟩ ?_
      have h0_le : (0 : 𝕜) ≤ (∑ i, (0 : E) i * (0 : E) i) := by
        simp
      change
        ((0 : WithTopBot 𝕜) ≤
          ((∑ i, (0 : E) i * (0 : E) i : 𝕜) : WithTopBot 𝕜))
      exact_mod_cast h0_le
  · have hnonempty : Nonempty ι := not_isEmpty_iff.mp hι
    letI : Nonempty ι := hnonempty
    obtain ⟨i, -, hi_sup⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : ι ↦ |x j|)
    have hi_sup : linftyNorm x = |x i| := by
      rw [linftyNorm_eq_sup'_univ_abs x]
      exact hi_sup
    rw [supportFunction_def]
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro y
      change
        (((⟪x, (y : E)⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤
          ((linftyNorm x : 𝕜) : WithTopBot 𝕜))
      exact_mod_cast pairing_le_linftyNorm_of_mem_coordinateL1Ball x y.1 y.2
    · rw [hi_sup]
      let t : 𝕜 := if 0 ≤ x i then (1 : 𝕜) else -1
      let y0 : E := fun j ↦ if j = i then t else 0
      have hy0 : y0 ∈ coordinateL1Ball := by
        change (∑ j, |y0 j|) ≤ 1
        have hsum : (∑ j, |y0 j|) = |t| := by
          have hif : ∀ j : ι, |(if j = i then t else 0 : 𝕜)| = (if j = i then |t| else 0) := by
            intro j
            by_cases h : j = i <;> simp [h]
          calc
            (∑ j, |y0 j|) = ∑ j, |(if j = i then t else 0 : 𝕜)| := by
              simp [y0]
            _ = ∑ j, (if j = i then |t| else 0) := by
              exact Finset.sum_congr rfl (fun j _ ↦ hif j)
            _ = |t| := by
              simp [Finset.sum_ite_eq', Finset.mem_univ]
        have ht_abs : |t| = (1 : 𝕜) := by
          by_cases hnonneg : 0 ≤ x i <;> simp [t, hnonneg]
        calc
          (∑ j, |y0 j|) = |t| := hsum
          _ = (1 : 𝕜) := ht_abs
          _ ≤ 1 := le_rfl
      refine le_iSup_of_le ⟨y0, hy0⟩ ?_
      have hmul : x i * t = |x i| := by
        by_cases hnonneg : 0 ≤ x i
        · simp [t, hnonneg, abs_of_nonneg]
        · have hneg : x i < 0 := lt_of_not_ge hnonneg
          simp [t, hnonneg, abs_of_neg hneg]
      have hpair : (⟪x, y0⟫ₚ : 𝕜) = |x i| := by
        have hif : ∀ j : ι, x j * y0 j = (if j = i then x i * t else 0) := by
          intro j
          by_cases h : j = i <;> simp [y0, h, t]
        calc
          (⟪x, y0⟫ₚ : 𝕜) = ∑ j, x j * y0 j := rfl
          _ = ∑ j, (if j = i then x i * t else 0) := by
            exact Finset.sum_congr rfl (fun j _ ↦ hif j)
          _ = x i * t := by
            simp [Finset.sum_ite_eq', Finset.mem_univ]
          _ = |x i| := hmul
      have hle : |x i| ≤ (⟪x, y0⟫ₚ : 𝕜) := by
        simp [hpair]
      change
        (((|x i| : 𝕜) : WithTopBot 𝕜) ≤
          (((⟪x, y0⟫ₚ : 𝕜) : WithTopBot 𝕜)))
      exact_mod_cast hle

/-- Function-valued bridge form of `supportFunction_coordinateL1Ball_eq_linftyNorm`. -/
theorem supportFunction_coordinateL1Ball_eq_linftyNorm_fun :
    (δᵛ(· | (coordinateL1Ball : Set E)) : E → WithTopBot 𝕜) =
      fun x ↦ ((linftyNorm x : 𝕜) : WithTopBot 𝕜) := by
  funext x
  exact supportFunction_coordinateL1Ball_eq_linftyNorm x

-- Proof sketch: combine `supportFunction_coordinateL1Ball_eq_linftyNorm` with the finite
-- coordinate-maximum formula `linftyNorm_eq_sup'_univ_abs`.
/-- Text 5.5.0.5: the support function of the coordinate `ℓ¹` unit ball
`{y | ∑ i, |y i| ≤ 1}` is the finite coordinate maximum `max_i |x i|`. -/
theorem supportFunction_coordinateL1Ball_eq_sup'_univ_abs [Nonempty ι] (x : E) :
    δᵛ(x | (coordinateL1Ball : Set E)) =
      (((Finset.univ.sup' Finset.univ_nonempty fun i : ι ↦ (|x i| : 𝕜)) : 𝕜) :
        WithTopBot 𝕜) := by
  rw [supportFunction_coordinateL1Ball_eq_linftyNorm x]
  exact congrArg (fun r : 𝕜 ↦ (r : WithTopBot 𝕜)) (linftyNorm_eq_sup'_univ_abs x)

end
