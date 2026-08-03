import Mathlib
import BauschkeLean.Chap08.Proposition_8_6
import BauschkeLean.Chap09.Remark_9_37
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap13.Proposition_13_30
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap19.Definition_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ERealFunction InnerProductSpace

noncomputable section

universe u v

namespace ContinuousLinearMap

section HilbertFamily

variable {I : Type v}
variable {H : Type u} {K : I → Type u}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, NormedSpace ℝ (K i)]

section Finite

variable [Fintype I]

/-- The canonical `lp`-valued operator attached to a finite family `(Lᵢ)`. This is the standard
bridge from the coordinatewise `ContinuousLinearMap.pi` into the `lp` owner. -/
abbrev toLpOperator (L : ∀ i, H →L[ℝ] K i) : H →L[ℝ] lp K 2 :=
    (((PiLp.continuousLinearEquiv 2 ℝ K).symm.trans
        ((lpPiLpₗᵢ K ℝ).symm.toContinuousLinearEquiv)).toContinuousLinearMap).comp
      (ContinuousLinearMap.pi L)

/-- The `i`th coordinate of the canonical finite-family operator `toLpOperator L` is `Lᵢ x`. -/
@[simp] theorem toLpOperator_apply
    (L : ∀ i, H →L[ℝ] K i) (x : H) (i : I) :
    toLpOperator L x i = L i x := by
  change ((lpPiLpₗᵢ K ℝ).symm (WithLp.toLp 2 fun j ↦ L j x)) i = L i x
  rw [coe_lpPiLpₗᵢ_symm (WithLp.toLp 2 fun j ↦ L j x)]

end Finite

end HilbertFamily

end ContinuousLinearMap

namespace ERealFunction

open ContinuousLinearMap

section Basic

variable {I : Type v}
variable {H : Type u} {K : I → Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]

-- Proof sketch: `h x` lies in `]-∞,+∞]`, and subtracting the finite linear term `⟪x, z⟫`
-- preserves the strict inequality above `⊥`.
/-- The linear tilt `x ↦ h(x) - ⟪x, z⟫` stays in `]-∞,+∞]`. -/
theorem linearTilt_value_mem_Ioi_bot
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (x : H) :
    (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) ∈ Set.Ioi (⊥ : EReal) := by
  -- Rewrite subtraction as addition and use that adding a finite real term cannot create `⊥`.
  rw [sub_eq_add_neg]
  have hne :
      (h x : EReal) + -(((⟪x, z⟫_ℝ : ℝ) : EReal)) ≠ ⊥ := by
    exact (EReal.add_ne_bot_iff.2) ⟨ne_of_gt (h x).2, by simp⟩
  exact lt_of_le_of_ne bot_le hne.symm

/-- The source-facing linear tilt `x ↦ h(x) - ⟪x, z⟫` from Example 19.3. -/
def linearTilt
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨(h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal),
      linearTilt_value_mem_Ioi_bot z h x⟩

/-- Evaluating `linearTilt z h` gives `h(x) - ⟪x, z⟫`. -/
@[simp] theorem linearTilt_apply
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (x : H) :
    (linearTilt z h x : EReal) =
      (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) :=
  rfl

-- Proof sketch: each coordinate term `gᵢ(yᵢ - rᵢ)` lies in `]-∞,+∞]`, and the Hilbert direct sum
-- of such values again stays strictly above `⊥`.
/-- The shifted Hilbert sum `y ↦ ⨁ i, gᵢ(yᵢ - rᵢ)` stays in `]-∞,+∞]`. -/
theorem shiftedHilbertSum_value_mem_Ioi_bot
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (y : lp K 2) :
    (⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) y ∈ Set.Ioi (⊥ : EReal) := by
  classical
  by_cases hI : Finite I
  · let _ : Fintype I := Fintype.ofFinite I
    -- In the finite branch, the Hilbert sum is the ordinary finite coordinate sum.
    simpa [hilbertSumFunction, hI] using
      fintype_sum_mem_Ioi_bot (fun i ↦ g i (y i - r i))
  · -- In the infinite branch, the supremum is bounded below by the empty partial sum `0`.
    have hzero_mem :
        (0 : EReal) ∈
          Set.range
            (fun J : Finset I ↦
              J.sum (fun i ↦ (g i (y i - r i) : EReal))) := by
      exact ⟨∅, by simp⟩
    have hzero_le :
        (0 : EReal) ≤
          sSup
            (Set.range
              (fun J : Finset I ↦
                J.sum (fun i ↦ (g i (y i - r i) : EReal)))) := by
      exact le_sSup hzero_mem
    -- The empty partial sum already sits strictly above `⊥`, so the supremum does as well.
    simpa [hilbertSumFunction, hI] using
      (lt_of_lt_of_le (show (⊥ : EReal) < 0 by simp) hzero_le)

/-- The source-facing separable penalty `y ↦ ⨁ i, gᵢ(yᵢ - rᵢ)` from Example 19.3. -/
def shiftedHilbertSum
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) :
    lp K 2 → Set.Ioi (⊥ : EReal) :=
  fun y ↦
    ⟨(⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) y,
      shiftedHilbertSum_value_mem_Ioi_bot r g y⟩

/-- Evaluating `shiftedHilbertSum r g` gives the Hilbert-sum formula
`⨁ i, gᵢ(yᵢ - rᵢ)`. -/
@[simp] theorem shiftedHilbertSum_apply
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (y : lp K 2) :
    (shiftedHilbertSum r g y : EReal) =
      (⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) y :=
  rfl

/-- Helper for Example 19 3: the explicit perturbation
`(x, y) ↦ h(x) - ⟪x, z⟫ + ⨁ i, gᵢ((Lx + y)ᵢ - rᵢ)`. -/
private abbrev linearTiltShiftedHilbertSumPerturbation
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] lp K 2) :
    H × lp K 2 → Set.Ioi (⊥ : EReal) :=
  ((linearTilt z h) ∘ Prod.fst) + (shiftedHilbertSum r g ∘ fun p ↦ L p.1 + p.2)

section FiniteFamilyBridge

variable [Fintype I]

/-- Helper for Example 19 3: over a finite index set, `shiftedHilbertSum` is the ordinary
coordinate sum `∑ i, gᵢ(yᵢ - rᵢ)`. -/
@[simp] theorem shiftedHilbertSum_apply_eq_sum_of_fintype
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (y : lp K 2) :
    (shiftedHilbertSum r g y : EReal) = ∑ i, (g i (y i - r i) : EReal) := by
  have huniv :
      (@Finset.univ I inferInstance) = (@Finset.univ I (Fintype.ofFinite I)) := by
    ext i
    simp
  have hsum :
      (let _ : Fintype I := Fintype.ofFinite I
       ∑ i, (g i (y i - r i) : EReal)) =
        ∑ i, (g i (y i - r i) : EReal) := by
    simpa using
      congrArg
        (fun s : Finset I ↦ s.sum (fun i ↦ (g i (y i - r i) : EReal)))
        huniv.symm
  -- Collapse the Hilbert-sum owner to its finite-coordinate branch.
  rw [shiftedHilbertSum_apply, hilbertSumFunction_apply_of_finite
    (f := fun i yi ↦ (g i (yi - r i) : EReal)) (x := y)]
  exact hsum

-- Proof sketch: rewrite the canonical direct-sum operator `toLpOperator L` coordinatewise and
-- use the finite-branch formula for `⨁ i`.
/-- Finite-index specialization of
`compositePerturbationFunction_linearTilt_shiftedHilbertSum_apply`: for a finite family
`(Lᵢ)`, the perturbation value is `h(x) - ⟪x, z⟫ + ∑ᵢ gᵢ(Lᵢ x + yᵢ - rᵢ)`. -/
@[simp] theorem compositePerturbationFunction_linearTilt_shiftedHilbertSum_family_apply_eq_sum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : ∀ i, H →L[ℝ] K i) (x : H) (y : lp K 2) :
    (linearTiltShiftedHilbertSumPerturbation z h r g (toLpOperator L) (x, y) : EReal) =
      (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
        ∑ i, (g i (L i x + y i - r i) : EReal) := by
  -- Evaluate the perturbation at `(x, y)` before rewriting the finite Hilbert sum.
  change (linearTilt z h x : EReal) + (shiftedHilbertSum r g (toLpOperator L x + y) : EReal) =
    (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
      ∑ i, (g i (L i x + y i - r i) : EReal)
  rw [linearTilt_apply, shiftedHilbertSum_apply_eq_sum_of_fintype]
  -- Rewrite the finite coordinate sum using the canonical coordinate formula for `toLpOperator`.
  refine congrArg (fun t : EReal ↦
    (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) + t) ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hcoord : ((toLpOperator L x + y) i : K i) = L i x + y i := by
    change (toLpOperator L x) i + y i = L i x + y i
    rw [ContinuousLinearMap.toLpOperator_apply]
  change (g i (((toLpOperator L x + y) i : K i) - r i) : EReal) =
    (g i (L i x + y i - r i) : EReal)
  exact congrArg (fun t : K i ↦ (g i (t - r i) : EReal)) hcoord

-- Proof sketch: evaluate the perturbation at the zero fiber and use the source-facing family
-- formula above.
/-- Finite-index specialization of
`perturbationPrimalObjective_compositePerturbationFunction_linearTilt_shiftedHilbertSum`: the
primal objective is
`x ↦ h(x) - ⟪x, z⟫ + ∑ᵢ gᵢ(Lᵢ x - rᵢ)`. -/
theorem perturbationPrimalObjective_linearTilt_shiftedHilbertSum_family_eq_sum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : ∀ i, H →L[ℝ] K i) :
    perturbationPrimalObjective
        (linearTiltShiftedHilbertSumPerturbation z h r g (toLpOperator L)) =
      fun x : H ↦
        (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
          ∑ i, (g i (L i x - r i) : EReal) := by
  funext x
  -- Evaluate the perturbation objective on the zero perturbation fiber.
  rw [perturbationPrimalObjective_apply]
  -- Route correction: close the finite primal formula by specializing the family perturbation
  -- rewrite at `y = 0`, rather than unfolding the perturbation recursively.
  calc
    (linearTiltShiftedHilbertSumPerturbation z h r g (toLpOperator L) (x, 0) : EReal) =
        (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
          ∑ i, (g i (L i x + (0 : lp K 2) i - r i) : EReal) := by
            simpa using
              compositePerturbationFunction_linearTilt_shiftedHilbertSum_family_apply_eq_sum
                (z := z) (h := h) (r := r) (g := g) (L := L) x 0
    _ =
        (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
          ∑ i, (g i (L i x - r i) : EReal) := by
            refine congrArg (fun t : EReal ↦
              (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) + t) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hzero : (((0 : lp K 2) i : K i)) = 0 := rfl
            change (g i (L i x + (((0 : lp K 2) i : K i)) - r i) : EReal) =
              (g i (L i x - r i) : EReal)
            rw [hzero]
            simp

end FiniteFamilyBridge

-- Proof sketch: specialize the canonical owner `compositePerturbationFunction` from
-- Proposition 19.20 to `f = linearTilt z h` and `g = shiftedHilbertSum r g`, then unfold the two
-- source-facing component functions.
/-- Helper for Example 19 3: the textbook perturbation is the specialization of the canonical composite
perturbation to `f = h - ⟪·, z⟫` and `g = ⨁ i, gᵢ(· - rᵢ)`. -/
@[simp] theorem compositePerturbationFunction_linearTilt_shiftedHilbertSum_apply
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] lp K 2) (x : H) (y : lp K 2) :
    (linearTiltShiftedHilbertSumPerturbation z h r g L (x, y) : EReal) =
      (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
        (⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) (L x + y) := by
  -- Unfold the two source-facing building blocks of the perturbation.
  simp [linearTiltShiftedHilbertSumPerturbation, linearTilt_apply, shiftedHilbertSum_apply]

-- Proof sketch: specialize Proposition 19.20 (2) to the linear tilt and shifted Hilbert sum, and
-- then unfold the source-facing component functions.
/-- Helper for Example 19 3: the primal objective of the canonical composite perturbation
specialized to `h - ⟪·, z⟫` and `⨁ i, gᵢ(· - rᵢ)` is exactly the textbook objective
`x ↦ h(x) - ⟪x, z⟫ + ⨁ i gᵢ((Lx)ᵢ - rᵢ)`. -/
theorem perturbationPrimalObjective_compositePerturbationFunction_linearTilt_shiftedHilbertSum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] lp K 2) :
    perturbationPrimalObjective
        (linearTiltShiftedHilbertSumPerturbation z h r g L) =
      fun x : H ↦
        (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
          (⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) (L x) := by
  funext x
  -- Evaluate the perturbation objective on the zero perturbation fiber.
  rw [perturbationPrimalObjective_apply]
  -- The source-facing perturbation formula at `y = 0` is exactly the textbook primal objective.
  simpa using
    compositePerturbationFunction_linearTilt_shiftedHilbertSum_apply
      (z := z) (h := h) (r := r) (g := g) (L := L) x 0

end Basic

end ERealFunction

namespace ContinuousLinearMap

section DualFormula

variable {I : Type v}
variable {H : Type u} {K : I → Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

section FiniteFamilyBridge

variable [Fintype I]

/-- For a finite family, the adjoint of `toLpOperator L` is the ordinary sum
`v ↦ ∑ᵢ Lᵢ^* vᵢ`. -/
@[simp] theorem toLpOperator_adjoint_apply_eq_sum
    (L : ∀ i, H →L[ℝ] K i) (v : lp K 2) :
    (toLpOperator L).adjoint v = ∑ i, (L i).adjoint (v i) := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, inner_sum]
  calc
    ⟪toLpOperator L x, v⟫_ℝ = ∑ i, ⟪L i x, v i⟫_ℝ := by
      calc
        ⟪toLpOperator L x, v⟫_ℝ
            = ⟪lpPiLpₗᵢ K ℝ (toLpOperator L x), lpPiLpₗᵢ K ℝ v⟫_ℝ := by
                exact ((lpPiLpₗᵢ K ℝ).inner_map_map (toLpOperator L x) v).symm
        _ = ∑ i, ⟪(lpPiLpₗᵢ K ℝ (toLpOperator L x)) i, (lpPiLpₗᵢ K ℝ v) i⟫_ℝ := by
              rw [PiLp.inner_apply]
        _ = ∑ i, ⟪L i x, v i⟫_ℝ := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [ContinuousLinearMap.toLpOperator_apply, coe_lpPiLpₗᵢ]
    _ = ∑ i, ⟪x, (L i).adjoint (v i)⟫_ℝ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using (ContinuousLinearMap.adjoint_inner_right (A := L i) x (v i)).symm

end FiniteFamilyBridge

end DualFormula

end ContinuousLinearMap

namespace ERealFunction

open ContinuousLinearMap

section DualFormula

variable {I : Type v}
variable {H : Type u} {K : I → Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- Helper for Example 19 3: the conjugate of the linear tilt `x ↦ h(x) - ⟪x, z⟫` is the
translated conjugate `u ↦ h^*(u + z)`. -/
theorem linearTilt_asEReal_conjugate_apply
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (u : H) :
    (linearTilt z h).asEReal∗ u = h.asEReal∗ (u + z) := by
  -- Apply the translate-plus-inner conjugation formula with zero translation and zero constant.
  simpa [linearTilt, Function.asEReal_apply, translate_apply, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm, inner_neg_right] using
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := h.asEReal) (y := (0 : H)) (v := -z) (β := 0))
      u

/-- Helper for Example 19 3: a single shifted coordinate `yi ↦ gᵢ(yi - rᵢ)` has conjugate
`vi ↦ gᵢ^*(vi) + ⟪vi, rᵢ⟫`. -/
theorem shifted_coordinate_asEReal_conjugate_apply
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (i : I) (vi : K i) :
    ((fun yi : K i ↦ g i (yi - r i)).asEReal∗ vi) =
      (g i).asEReal∗ vi + ((⟪vi, r i⟫_ℝ : ℝ) : EReal) := by
  -- Each coordinate is a pure translate, so Proposition 13.23 applies directly.
  simpa [Function.asEReal_apply, translate_apply, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm, real_inner_comm] using
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := (g i).asEReal) (y := r i) (v := (0 : K i)) (β := 0))
      vi

/-- Helper for Example 19 3: after coercion to `EReal`, the finite shifted Hilbert sum agrees
with the direct-sum owner built from the shifted coordinate family. -/
theorem shiftedHilbertSum_asEReal_eq_directSumFunction_shifted
    [Fintype I] (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) :
    (shiftedHilbertSum r g).asEReal =
      (directSumFunction (fun i yi ↦ g i (yi - r i))).asEReal := by
  funext y
  -- Rewrite both owners to the same finite coordinate sum.
  rw [Function.asEReal_apply, Function.asEReal_apply]
  rw [shiftedHilbertSum_apply_eq_sum_of_fintype, directSumFunction_apply]

/-- Helper for Example 19 3: a nonempty finite sum of the constant value `⊥` is `⊥`. -/
private theorem finset_sum_const_bot_of_nonempty
    (s : Finset I) (hs : s.Nonempty) :
    s.sum (fun _ : I ↦ (⊥ : EReal)) = ⊥ := by
  classical
  rcases hs with ⟨i, hi⟩
  rw [← Finset.insert_erase hi, Finset.sum_insert (Finset.notMem_erase i s)]
  simp

/-- Helper for Example 19 3: over an infinite index set, the naive arbitrary-index shifted
Hilbert-sum conjugate formula is false. For the constant-`⊤` family at `0`, the left-hand side is
`⊥` while the right-hand side is `0`. -/
theorem shiftedHilbertSum_asEReal_conjugate_counterexample_of_infinite
    [Infinite I] :
    let g : ∀ i, K i → Set.Ioi (⊥ : EReal) := fun _ _ ↦ ⟨(⊤ : EReal), by simp⟩
    (shiftedHilbertSum (0 : lp K 2) g).asEReal∗ (0 : lp K 2) ≠
      (⨁ i, fun vi ↦ (g i).asEReal∗ vi + ((⟪vi, (0 : lp K 2) i⟫_ℝ : ℝ) : EReal))
        (0 : lp K 2) := by
  classical
  let g : ∀ i, K i → Set.Ioi (⊥ : EReal) := fun _ _ ↦ ⟨(⊤ : EReal), by simp⟩
  have hshifted_top : ∀ y : lp K 2, (shiftedHilbertSum (0 : lp K 2) g y : EReal) = ⊤ := by
    intro y
    rw [shiftedHilbertSum_apply]
    simp only [hilbertSumFunction_apply_of_infinite]
    let i0 : I := Classical.choice (inferInstance : Nonempty I)
    have htop_mem :
        (⊤ : EReal) ∈
          Set.range
            (fun J : Finset I ↦
              J.sum (fun i ↦ (g i (y i - (0 : lp K 2) i) : EReal))) := by
      refine ⟨{i0}, ?_⟩
      simp [g]
    exact le_antisymm le_top (le_sSup htop_mem)
  have hleft :
      (shiftedHilbertSum (0 : lp K 2) g).asEReal∗ (0 : lp K 2) = ⊥ := by
    -- The shifted Hilbert sum is pointwise `⊤`, so every affine defect at the origin is `⊥`.
    rw [conjugate_apply]
    refine le_antisymm ?_ bot_le
    refine iSup_le fun y => ?_
    rw [Function.asEReal_apply, hshifted_top y]
    simp
  have hcoord_bot : ∀ i : I, (g i).asEReal∗ (0 : K i) = ⊥ := by
    intro i
    -- Each coordinate function is constantly `⊤`, so its conjugate at `0` is `⊥`.
    rw [conjugate_apply]
    refine le_antisymm ?_ bot_le
    refine iSup_le fun y => ?_
    simp [Function.asEReal_apply, g]
  have hright :
      (⨁ i, fun vi ↦ (g i).asEReal∗ vi + ((⟪vi, (0 : lp K 2) i⟫_ℝ : ℝ) : EReal))
          (0 : lp K 2) = 0 := by
    -- The empty partial sum contributes `0`, and every nonempty partial sum collapses to `⊥`.
    rw [hilbertSumFunction_apply_of_infinite]
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro _ ⟨J, rfl⟩
      by_cases hJ : J.Nonempty
      · have hsum_bot :
          J.sum (fun i ↦ (g i).asEReal∗ ((0 : lp K 2) i) +
            ((⟪((0 : lp K 2) i), (0 : lp K 2) i⟫_ℝ : ℝ) : EReal)) = ⊥ := by
            calc
              J.sum (fun i ↦ (g i).asEReal∗ ((0 : lp K 2) i) +
                  ((⟪((0 : lp K 2) i), (0 : lp K 2) i⟫_ℝ : ℝ) : EReal)) =
                  J.sum (fun _ : I ↦ (⊥ : EReal)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    change (g i).asEReal∗ (0 : K i) +
                        ((⟪(0 : K i), (0 : K i)⟫_ℝ : ℝ) : EReal) = ⊥
                    rw [hcoord_bot i]
                    simp
              _ = ⊥ := finset_sum_const_bot_of_nonempty (s := J) hJ
        exact hsum_bot.le.trans bot_le
      · rw [Finset.not_nonempty_iff_eq_empty.mp hJ]
        simp
    · exact le_sSup ⟨∅, by simp⟩
  change (shiftedHilbertSum (0 : lp K 2) g).asEReal∗ (0 : lp K 2) ≠
      (⨁ i, fun vi ↦ (g i).asEReal∗ vi + ((⟪vi, (0 : lp K 2) i⟫_ℝ : ℝ) : EReal))
        (0 : lp K 2)
  rw [hleft, hright]
  simp

-- Proof sketch: specialize Proposition 19.20 (3) to `f = linearTilt z h` and
-- `g = shiftedHilbertSum r g`, then rewrite the linear-tilt conjugate as
-- `u ↦ h^*(u + z)` via `linearTilt_asEReal_conjugate_apply`.
/-- Example 19.3, bundled dual surface: the dual objective associated with the perturbation
specialized to `h - ⟪·, z⟫` and `⨁ i, gᵢ(· - rᵢ)` is
`v ↦ h^*(z - L^* v) + (shiftedHilbertSum r g)^*(v)`, written with the canonical
`EReal` conjugate owner. -/
theorem perturbationDualObjective_linearTilt_shiftedHilbertSum_bundled
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] lp K 2) :
    perturbationDualObjective
        (linearTiltShiftedHilbertSumPerturbation z h r g L) =
      fun v : lp K 2 ↦
        h.asEReal∗ (z - L.adjoint v) + (shiftedHilbertSum r g).asEReal∗ v := by
  have hdual_owner :
      perturbationDualObjective
          (linearTiltShiftedHilbertSumPerturbation z h r g L) =
        compositeDualObjective (linearTilt z h) (shiftedHilbertSum r g) L := by
    funext v
    have hsplit :
        ∀ x : H, ∀ w : lp K 2,
          (((⟪w - L x, v⟫_ℝ : ℝ) : EReal) -
              ((linearTilt z h x : EReal) + (shiftedHilbertSum r g w : EReal))) =
            ((((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) - (linearTilt z h x : EReal)) +
              (((⟪w, v⟫_ℝ : ℝ) : EReal) - (shiftedHilbertSum r g w : EReal))) := by
      intro x w
      have hlinear_bot : (linearTilt z h x : EReal) ≠ ⊥ := ne_of_gt (linearTilt z h x).2
      have hsum_bot : (shiftedHilbertSum r g w : EReal) ≠ ⊥ := ne_of_gt (shiftedHilbertSum r g w).2
      have hadj : ⟪x, -(L.adjoint v)⟫_ℝ = -⟪L x, v⟫_ℝ := by
        simpa [inner_neg_right] using
          congrArg Neg.neg (ContinuousLinearMap.adjoint_inner_right (A := L) x v)
      have hinner :
          (((⟪w - L x, v⟫_ℝ : ℝ) : EReal)) =
            (((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) +
              ((⟪w, v⟫_ℝ : ℝ) : EReal)) := by
        have hreal :
            ⟪w - L x, v⟫_ℝ = ⟪x, -(L.adjoint v)⟫_ℝ + ⟪w, v⟫_ℝ := by
          calc
            ⟪w - L x, v⟫_ℝ = ⟪w, v⟫_ℝ - ⟪L x, v⟫_ℝ := by
              simp [inner_sub_left]
            _ = ⟪w, v⟫_ℝ + ⟪x, -(L.adjoint v)⟫_ℝ := by
              rw [sub_eq_add_neg, hadj]
            _ = ⟪x, -(L.adjoint v)⟫_ℝ + ⟪w, v⟫_ℝ := by
              simp [add_comm]
        rw [hreal, EReal.coe_add]
      rw [hinner, sub_eq_add_neg, EReal.neg_add (.inl hlinear_bot) (.inr hsum_bot),
        sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
      let a : EReal := (((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal))
      let b : EReal := (((⟪w, v⟫_ℝ : ℝ) : EReal))
      let c : EReal := -((linearTilt z h x : EReal))
      let d : EReal := -((shiftedHilbertSum r g w : EReal))
      change a + b + (c + d) = a + c + (b + d)
      calc
        a + b + (c + d) = a + (b + (c + d)) := by rw [add_assoc]
        _ = a + (c + (b + d)) := by
              refine congrArg (fun t : EReal ↦ a + t) ?_
              calc
                b + (c + d) = (b + c) + d := by rw [← add_assoc]
                _ = (c + b) + d := by rw [add_comm b c]
                _ = c + (b + d) := by rw [add_assoc]
        _ = a + c + (b + d) := by rw [add_assoc]
    rw [perturbationDualObjective_apply, compositeDualObjective_apply, conjugate_apply,
      conjugate_apply]
    calc
      (⨆ p : H × lp K 2,
          (((⟪p.2, v⟫_ℝ : ℝ) : EReal) -
            (linearTiltShiftedHilbertSumPerturbation z h r g L p : EReal))) =
          ⨆ x : H, ⨆ y : lp K 2,
            (((⟪y, v⟫_ℝ : ℝ) : EReal) -
              (linearTiltShiftedHilbertSumPerturbation z h r g L (x, y) : EReal)) := by
            rw [iSup_prod']
      _ = ⨆ x : H, ⨆ y : lp K 2,
            (((⟪y, v⟫_ℝ : ℝ) : EReal) -
              ((linearTilt z h x : EReal) +
                (shiftedHilbertSum r g (L x + y) : EReal))) := by
            refine iSup_congr fun x => ?_
            refine iSup_congr fun y => ?_
            rfl
      _ = ⨆ x : H, ⨆ w : lp K 2,
            (((⟪w - L x, v⟫_ℝ : ℝ) : EReal) -
              ((linearTilt z h x : EReal) + (shiftedHilbertSum r g w : EReal))) := by
            refine iSup_congr fun x => ?_
            exact
              ((Equiv.addRight (-(L x))).surjective.iSup_congr (Equiv.addRight (-(L x)))
                fun w => by
                  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]).symm
      _ = ⨆ x : H, ⨆ w : lp K 2,
            ((((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) - (linearTilt z h x : EReal)) +
              (((⟪w, v⟫_ℝ : ℝ) : EReal) - (shiftedHilbertSum r g w : EReal))) := by
            refine iSup_congr fun x => ?_
            refine iSup_congr fun w => ?_
            simpa using hsplit x w
      _ = (⨆ x : H, (((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) - (linearTilt z h x : EReal))) +
            (⨆ w : lp K 2, (((⟪w, v⟫_ℝ : ℝ) : EReal) - (shiftedHilbertSum r g w : EReal))) := by
            exact iSup_iSup_add_eq_add_iSup _ _
  -- Route correction: pass through the canonical composite dual owner, then rewrite only the
  -- linear-tilt conjugate back to the source-facing `h^*(z - L^* v)` surface.
  funext v
  have hdual_owner_v :
      perturbationDualObjective
          (linearTiltShiftedHilbertSumPerturbation z h r g L) v =
        compositeDualObjective (linearTilt z h) (shiftedHilbertSum r g) L v :=
    congrFun hdual_owner v
  rw [hdual_owner_v, compositeDualObjective_apply]
  calc
    (linearTilt z h).asEReal∗ (-(L.adjoint v)) + (shiftedHilbertSum r g).asEReal∗ v =
        h.asEReal∗ (-(L.adjoint v) + z) + (shiftedHilbertSum r g).asEReal∗ v := by
          rw [linearTilt_asEReal_conjugate_apply]
    _ = h.asEReal∗ (z - L.adjoint v) + (shiftedHilbertSum r g).asEReal∗ v := by
          refine congrArg (fun t : EReal ↦ t + (shiftedHilbertSum r g).asEReal∗ v) ?_
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = h.asEReal∗ (z - L.adjoint v) + (shiftedHilbertSum r g).asEReal∗ v := by
          rfl

section FiniteFamilyBridge

variable [Fintype I]

/-- Helper for Example 19 3: in the finite branch, the conjugate of the shifted Hilbert sum is
the coordinate sum of the translated coordinate conjugates. -/
theorem shiftedHilbertSum_asEReal_conjugate_eq_sum_of_fintype
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (v : lp K 2) :
    (shiftedHilbertSum r g).asEReal∗ v =
      ∑ i, ((g i).asEReal∗ (v i) + ((⟪v i, r i⟫_ℝ : ℝ) : EReal)) := by
  let shifted : ∀ i, K i → Set.Ioi (⊥ : EReal) := fun i yi ↦ g i (yi - r i)
  have hshift :
      (shiftedHilbertSum r g).asEReal = (directSumFunction shifted).asEReal := by
    simpa [shifted] using shiftedHilbertSum_asEReal_eq_directSumFunction_shifted (r := r) (g := g)
  -- Rewrite to the finite direct-sum owner, then split the conjugate coordinatewise.
  rw [hshift]
  calc
    (directSumFunction shifted).asEReal∗ v = ∑ i, (shifted i).asEReal∗ (v i) := by
      simpa [shifted] using
        congrFun (conjugate_directSumFunction_eq_sum_conjugate shifted) v
    _ = ∑ i, ((g i).asEReal∗ (v i) + ((⟪v i, r i⟫_ℝ : ℝ) : EReal)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      -- Each coordinate is the translate `yi ↦ gᵢ(yi - rᵢ)`, so Proposition 13.23 applies.
      simpa [shifted] using shifted_coordinate_asEReal_conjugate_apply (r := r) (g := g) i (v i)

-- Semantic recall: verified candidates are `ContinuousLinearMap.adjoint` for the bundled adjoint
-- and the local finite-family bridge `toLpOperator`; the coordinate-sum formula stays a companion.
-- Proof sketch: specialize the bundled dual formula to the canonical finite-family operator
-- `toLpOperator L`.
/-- Finite-family companion to Example 19.3: the dual objective associated with the perturbation
specialized to `h - ⟪·, z⟫` and `⨁ i, gᵢ(· - rᵢ)` is
`v ↦ h^*(z - (toLpOperator L)^* v) + (shiftedHilbertSum r g)^*(v)`, again written with the
canonical `EReal` conjugate owner. -/
theorem perturbationDualObjective_linearTilt_shiftedHilbertSum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : ∀ i, H →L[ℝ] K i) :
    perturbationDualObjective
        (linearTiltShiftedHilbertSumPerturbation z h r g (toLpOperator L)) =
      fun v : lp K 2 ↦
        h.asEReal∗ (z - (toLpOperator L).adjoint v) +
          (shiftedHilbertSum r g).asEReal∗ v := by
  -- Specialize the bundled owner theorem to the canonical finite-family operator.
  simpa using
    perturbationDualObjective_linearTilt_shiftedHilbertSum_bundled
      (z := z) (h := h) (r := r) (g := g) (L := toLpOperator L)

-- Proof sketch: specialize the canonical dual formula to the canonical finite-family operator
-- `toLpOperator L`, then use the finite-branch formulas for the adjoint and the Hilbert sum.
/-- Finite-index specialization of Example 19.3: the dual of
`x ↦ h(x) - ⟪x, z⟫ + ∑ i, gᵢ(Lᵢ x - rᵢ)` is
`v ↦ h^*(z - ∑ᵢ Lᵢ^* vᵢ) + ∑ᵢ (gᵢ^*(vᵢ) + ⟪vᵢ, rᵢ⟫)`, written with the canonical `EReal`
conjugate owner. -/
theorem perturbationDualObjective_linearTilt_shiftedHilbertSum_family_eq_sum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : ∀ i, H →L[ℝ] K i) :
    perturbationDualObjective
        (linearTiltShiftedHilbertSumPerturbation z h r g (toLpOperator L)) =
      fun v : lp K 2 ↦
        h.asEReal∗ (z - ∑ i, (L i).adjoint (v i)) +
          ∑ i, ((g i).asEReal∗ (v i) + ((⟪v i, r i⟫_ℝ : ℝ) : EReal)) := by
  rw [perturbationDualObjective_linearTilt_shiftedHilbertSum
    (z := z) (h := h) (r := r) (g := g) (L := L)]
  funext v
  rw [ContinuousLinearMap.toLpOperator_adjoint_apply_eq_sum,
    shiftedHilbertSum_asEReal_conjugate_eq_sum_of_fintype]

end FiniteFamilyBridge

end DualFormula

end ERealFunction
