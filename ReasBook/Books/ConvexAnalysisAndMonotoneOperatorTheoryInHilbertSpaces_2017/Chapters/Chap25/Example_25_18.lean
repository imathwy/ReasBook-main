import BauschkeLean.Chap25.Proposition_25_16

open scoped InnerProductSpace

noncomputable section

universe u

namespace ContinuousLinearMap

section RealHilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: the cyclic right-shift operator on the finite Hilbert product.
- `core/canonical`: the Chapter 25 owner
  `SetValuedOperator.IsThreeStarMonotone` on the associated singleton-valued operator.
- `bridge/view`: the canonical finite-Hilbert-sum bridge `lpPiLpₗᵢ` into mathlib's `PiLp` owner,
  together with the `PiLp` reindexing equivalence `LinearIsometryEquiv.piLpCongrLeft`; the
  deleted coordinate-model transport was only a duplicate view of this owner-level API. -/

/-- The cyclic right-shift operator on `H^N`, transported to the canonical finite Hilbert-sum
model `lp (fun _ : Fin N ↦ H) 2`. In coordinates it is
`x ↦ fun i ↦ x ((finRotate N).symm i)`, i.e. `(x₁, …, x_N) ↦ (x_N, x₁, …, x_{N-1})`. -/
def cyclicRightShift (N : ℕ+) :
    lp (fun _ : Fin N ↦ H) 2 →L[ℝ] lp (fun _ : Fin N ↦ H) 2 :=
  (((lpPiLpₗᵢ (fun _ : Fin N ↦ H) ℝ).trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ H (finRotate N))).trans
    (lpPiLpₗᵢ (fun _ : Fin N ↦ H) ℝ).symm).toLinearIsometry.toContinuousLinearMap

/-- Helper for Example 25.18: the reflector of `(1 / 2) • (Id - R)` is exactly `-R`. -/
lemma reflected_half_id_sub_cyclicRightShift_eq_neg (N : ℕ+) :
    let E := lp (fun _ : Fin N ↦ H) 2
    let A : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - cyclicRightShift N
    reflectedMap (Set.univ : Set E)
      (fun x : (Set.univ : Set E) ↦ (1 / 2 : ℝ) • A x) =
      fun x : (Set.univ : Set E) ↦ -cyclicRightShift N x := by
  let E := lp (fun _ : Fin N ↦ H) 2
  let A : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - cyclicRightShift N
  ext x i
  -- Normalizing the reflector identifies the source map `2 * ((1 / 2) * (Id - R)) - Id`.
  have hsmul : (2 : ℝ) • ((1 / 2 : ℝ) • A x) = A x := by
    rw [smul_smul]
    norm_num
  calc
    reflectedMap (Set.univ : Set E) (fun x : (Set.univ : Set E) ↦ (1 / 2 : ℝ) • A x) x i
        = ((2 : ℝ) • ((1 / 2 : ℝ) • A x) - (x : E)) i := by
            simp [reflectedMap]
    _ = (-cyclicRightShift N x) i := by
      rw [hsmul]
      simp [A]

/-- Helper for Example 25.18: the negated cyclic right-shift is nonexpansive because the shift
itself is an isometry of the finite Hilbert sum. -/
lemma neg_cyclicRightShift_lipschitzWith_one (N : ℕ+) :
    let E := lp (fun _ : Fin N ↦ H) 2
    LipschitzWith 1 (fun x : E ↦ -cyclicRightShift N x) := by
  let E := lp (fun _ : Fin N ↦ H) 2
  let e : E ≃ₗᵢ[ℝ] E :=
    ((lpPiLpₗᵢ (fun _ : Fin N ↦ H) ℝ).trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ H (finRotate N))).trans
      (lpPiLpₗᵢ (fun _ : Fin N ↦ H) ℝ).symm
  -- The cyclic shift is transported from the reindexing isometry `e`, and negation preserves
  -- distances.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  calc
    dist (-cyclicRightShift N x) (-cyclicRightShift N y)
        = dist (cyclicRightShift N x) (cyclicRightShift N y) := by simp
    _ = dist x y := by
      simpa [cyclicRightShift] using e.dist_map x y
    _ ≤ 1 * dist x y := by
      exact le_of_eq (by simp)

/-- Helper for Example 25.18: Proposition 4.4 turns nonexpansiveness of the reflector into firm
nonexpansiveness of `(1 / 2) • (Id - R)`. -/
lemma half_id_sub_cyclicRightShift_firmlyNonexpansiveOn (N : ℕ+) :
    let E := lp (fun _ : Fin N ↦ H) 2
    let A : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - cyclicRightShift N
    FirmlyNonexpansiveOn (Set.univ : Set E)
      (fun x : Set.univ ↦ (1 / 2 : ℝ) • A x) := by
  let E := lp (fun _ : Fin N ↦ H) 2
  let A : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - cyclicRightShift N
  have hReflectEq :
      reflectedMap (Set.univ : Set E) (fun x : Set.univ ↦ (1 / 2 : ℝ) • A x) =
        fun x : (Set.univ : Set E) ↦ -cyclicRightShift N x := by
    -- This is the source proof's key identity `2((1 / 2)(Id - R)) - Id = -R`.
    simpa [A] using reflected_half_id_sub_cyclicRightShift_eq_neg (H := H) N
  have hLip : LipschitzWith 1 (fun x : E ↦ -cyclicRightShift N x) := by
    -- The right-shift is an isometry, hence the reflected map is nonexpansive.
    simpa using neg_cyclicRightShift_lipschitzWith_one (H := H) N
  -- Proposition 4.4 now upgrades nonexpansiveness of the reflector to firm nonexpansiveness.
  refine (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn (Set.univ : Set E)
    (fun x : Set.univ ↦ (1 / 2 : ℝ) • A x)).1 ?_
  intro x y
  rw [hReflectEq]
  -- First record the reflected map estimate in distance form, then return to norms.
  have hdist :
      dist (-cyclicRightShift N (x : E)) (-cyclicRightShift N (y : E)) ≤ dist (x : E) (y : E) := by
    simpa using hLip.dist_le_mul (x : E) (y : E)
  simpa [dist_eq_norm] using hdist

/-- Helper for Example 25.18: firm nonexpansiveness of `(1 / 2) • (Id - R)` rewrites to
`1 / 2`-cocoercivity of `Id - R`. -/
lemma id_sub_cyclicRightShift_cocoerciveOn_half (N : ℕ+) :
    let E := lp (fun _ : Fin N ↦ H) 2
    let A : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - cyclicRightShift N
    CocoerciveOn (1 / 2 : ℝ) (Set.univ : Set E) (fun x : Set.univ ↦ A x) := by
  let E := lp (fun _ : Fin N ↦ H) 2
  let A : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - cyclicRightShift N
  have hFirm :
      FirmlyNonexpansiveOn (Set.univ : Set E)
        (fun x : Set.univ ↦ (1 / 2 : ℝ) • A x) := by
    -- This is exactly the firm nonexpansive stage obtained from the reflector route.
    simpa [A] using half_id_sub_cyclicRightShift_firmlyNonexpansiveOn (H := H) N
  refine ⟨by norm_num, ?_⟩
  intro x y
  have hxy := hFirm x y
  have hnorm :
      ‖(1 / 2 : ℝ) • A x - (1 / 2 : ℝ) • A y‖ ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) * ‖A x - A y‖ ^ (2 : ℕ)) := by
    -- Pull the common scalar out of the difference and simplify the resulting norm square.
    calc
      ‖(1 / 2 : ℝ) • A x - (1 / 2 : ℝ) • A y‖ ^ (2 : ℕ)
          = ‖(1 / 2 : ℝ) • (A x - A y)‖ ^ (2 : ℕ) := by rw [smul_sub]
      _ = ((1 / 2 : ℝ) * ‖A x - A y‖) ^ (2 : ℕ) := by
            simp [norm_smul]
      _ = (1 / 2 : ℝ) * ((1 / 2 : ℝ) * ‖A x - A y‖ ^ (2 : ℕ)) := by
            ring
  have hinner :
      inner ℝ ((x : E) - y) ((1 / 2 : ℝ) • A x - (1 / 2 : ℝ) • A y) =
        (1 / 2 : ℝ) * inner ℝ ((x : E) - y) (A x - A y) := by
    -- The right-hand side scales linearly in the second argument.
    rw [← smul_sub, real_inner_smul_right]
  rw [hnorm, hinner] at hxy
  nlinarith

/-- Example 25.18: if `N` is a strictly positive integer and `R : H^N → H^N` is the cyclic
right-shift operator, then `Id - R` is `3*` monotone. -/
theorem id_sub_cyclicRightShift_isThreeStarMonotone [CompleteSpace H] (N : ℕ+) :
    let E := lp (fun _ : Fin N ↦ H) 2
    (ContinuousLinearMap.id ℝ E - cyclicRightShift N).toSetValuedOperator.IsThreeStarMonotone :=
      by
  let E := lp (fun _ : Fin N ↦ H) 2
  let A : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - cyclicRightShift N
  have hCoco : CocoerciveOn (1 / 2 : ℝ) (Set.univ : Set E) (fun x : Set.univ ↦ A x) := by
    -- The source route has already produced the required `1 / 2`-cocoercivity of `Id - R`.
    simpa [A] using id_sub_cyclicRightShift_cocoerciveOn_half (H := H) N
  -- Proposition 25.16 upgrades whole-space cocoercivity to `3*` monotonicity.
  exact isThreeStarMonotone_of_cocoerciveOn_univ A hCoco

end RealHilbert

end ContinuousLinearMap
