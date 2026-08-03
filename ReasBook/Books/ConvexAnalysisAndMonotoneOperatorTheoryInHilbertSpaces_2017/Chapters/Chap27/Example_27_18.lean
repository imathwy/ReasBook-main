import Mathlib
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Example_6_25
import BauschkeLean.Chap27.Proposition_27_14
import BauschkeLean.Chap27.Proposition_27_17

open Set
open ContinuousLinearMap
open scoped InnerProductSpace
open scoped Pointwise

noncomputable section

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Example 27.18 is the matrix/orthant KKT criterion for the constraint
  `A x ∈ [0,+∞[^M`.
- `core/canonical`: the owner abstractions are `PolarSubgradientWitness`,
  `mem_argmin_coneConstraintObjective_iff_exists_polar_subgradient`, and the affine-objective
  bridge `mem_argmin_affineObjective_of_eq_and_neg_adjoint_mem_subdifferential`.
- `bridge/view`: this file keeps the textbook matrix specialization and rewrites the polar-cone
  multiplier from Proposition 27.17 into the nonnegative-orthant multiplier via orthant
  self-duality.
-/

section MatrixConeConstraints

/-- For the Euclidean nonnegative orthant, the Proposition 27.17 witness for `-vbar` is exactly
the textbook nonnegative multiplier system. -/
theorem polarSubgradientWitness_matrix_nonnegativeOrthant_iff
    {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ)
    {f : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)}
    {xbar : EuclideanSpace ℝ (Fin N)} {vbar : EuclideanSpace ℝ (Fin M)} :
    PolarSubgradientWitness f ({x : EuclideanSpace ℝ (Fin M) | ∀ i, 0 ≤ x i})
        A.toEuclideanLin.toContinuousLinearMap xbar (-vbar) ↔
      vbar ∈ ({x : EuclideanSpace ℝ (Fin M) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin M))) ∧
        (A.toEuclideanLin.toContinuousLinearMap).adjoint vbar ∈ (∂ f) xbar ∧
          ⟪xbar, (A.toEuclideanLin.toContinuousLinearMap).adjoint vbar⟫_ℝ = 0 := by
  let K : Set (EuclideanSpace ℝ (Fin M)) := {x | ∀ i, 0 ≤ x i}
  let L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin M) :=
    A.toEuclideanLin.toContinuousLinearMap
  have hself : K.IsSelfDual := by
    change
      ({x : EuclideanSpace ℝ (Fin M) | ∀ i, 0 ≤ x i} :
        Set (EuclideanSpace ℝ (Fin M))).IsSelfDual
    exact euclideanPositiveOrthant_isSelfDual M
  have hself' : K = Kᵒ⊕ := Set.isSelfDual_iff.mp hself
  constructor
  · intro hvbar
    have hvdual : vbar ∈ Kᵒ⊕ := (mem_dualCone_iff).2 hvbar.mem_polarCone
    have hvK : vbar ∈ K := by
      rw [hself']
      exact hvdual
    refine ⟨hvK, ?_, ?_⟩
    · simpa [L] using hvbar.mem_subdifferential
    · simpa [L] using hvbar.complementary_slackness_adjoint
  · rintro ⟨hvbar, hsub, hinner⟩
    have hvdual : vbar ∈ Kᵒ⊕ := by
      rw [← hself']
      exact hvbar
    refine ⟨(mem_dualCone_iff).1 hvdual, by simpa [L] using hsub, ?_⟩
    have hinner' : ⟪xbar, L.adjoint (-vbar)⟫_ℝ = 0 := by
      simpa [L] using hinner
    calc
      ⟪L xbar, -vbar⟫_ℝ = ⟪xbar, L.adjoint (-vbar)⟫_ℝ := by
        rw [L.adjoint_inner_right]
      _ = 0 := hinner'

/-- Example 27.18 (1): for the matrix inequality constraint `A x ∈ [0,+∞[^M`, a point `xbar`
solves the constrained minimization problem if and only if it is feasible and admits a
nonnegative multiplier `vbar` with `Aᵀ vbar ∈ ∂ f xbar` and complementary slackness. -/
theorem mem_argminOn_matrix_preimage_nonnegativeOrthant_iff_exists_nonnegative_transpose_subgradient
    {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ)
    {f : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hri :
      (({x : EuclideanSpace ℝ (Fin M) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin M))) ∩
        Set.relativeInterior
          (A.toEuclideanLin.toContinuousLinearMap '' effectiveDomain f)).Nonempty)
    {xbar : EuclideanSpace ℝ (Fin N)} :
    xbar ∈ Argmin[A.toEuclideanLin.toContinuousLinearMap ⁻¹'
      ({x : EuclideanSpace ℝ (Fin M) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin M)))]
      f.asEReal ↔
      A.toEuclideanLin.toContinuousLinearMap xbar ∈
        ({x : EuclideanSpace ℝ (Fin M) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin M))) ∧
        ∃ vbar : EuclideanSpace ℝ (Fin M),
          vbar ∈ ({x : EuclideanSpace ℝ (Fin M) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin M))) ∧
            (A.toEuclideanLin.toContinuousLinearMap).adjoint vbar ∈ (∂ f) xbar ∧
            ⟪xbar, (A.toEuclideanLin.toContinuousLinearMap).adjoint vbar⟫_ℝ = 0 := by
  let K : Set (EuclideanSpace ℝ (Fin M)) := {x | ∀ i, 0 ≤ x i}
  let L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin M) :=
    A.toEuclideanLin.toContinuousLinearMap
  have hK_nonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    simp [K]
  have hK_closed : IsClosed K := by
    have hclosed : IsClosed (⋂ i : Fin M, {x : EuclideanSpace ℝ (Fin M) | 0 ≤ x i}) := by
      refine isClosed_iInter fun i ↦ ?_
      simpa using isClosed_le continuous_const (EuclideanSpace.proj i).continuous
    convert hclosed using 1
    ext x
    simp [K]
  have hK_convex : Convex ℝ K := by
    intro x hx y hy a b ha hb hab i
    simpa [smul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  have hK_cone : IsCone K := by
    rw [isCone_iff]
    ext x
    constructor
    · intro hx
      exact Set.mem_smul.mpr ⟨1, by norm_num, x, hx, by simp⟩
    · rintro ⟨t, ht, y, hy, rfl⟩
      intro i
      exact mul_nonneg (le_of_lt ht) (hy i)
  have hpolyK : K.IsPolyhedral := by
    classical
    let t : Finset (((EuclideanSpace ℝ (Fin M) →L[ℝ] ℝ) × ℝ)) :=
      Finset.univ.image fun i : Fin M ↦
        (-(EuclideanSpace.proj i : EuclideanSpace ℝ (Fin M) →L[ℝ] ℝ), (0 : ℝ))
    refine ⟨t, ?_⟩
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter, Set.mem_closedHalfspace_iff]
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
      simpa using hx i
    · intro hx
      simp only [Set.mem_iInter, Set.mem_closedHalfspace_iff] at hx
      intro i
      have hproj :
          (-(EuclideanSpace.proj i : EuclideanSpace ℝ (Fin M) →L[ℝ] ℝ), (0 : ℝ)) ∈ t :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hx' := hx (-(EuclideanSpace.proj i : EuclideanSpace ℝ (Fin M) →L[ℝ] ℝ), (0 : ℝ))
        hproj
      simpa using hx'
  have hqual : ConeConstraintRegularity f K L :=
    .finite_dimensional_polyhedral_ri (by infer_instance) hpolyK (by simpa [K, L] using hri)
  have hbot : ∀ x ∉ L ⁻¹' K, f.asEReal x ≠ ⊥ := by
    intro x hx
    exact ne_of_gt (f x).2
  have hargminOn :
      Argmin[L ⁻¹' K] f.asEReal = (L ⁻¹' K) ∩ Argmin (compositePrimalObjective f (ι[K]) L) := by
    simpa [compositePrimalObjective, primalObjective] using
      argminOn_eq_inter_argmin_add_indicator f.asEReal (L ⁻¹' K) hbot
  have howner :
      xbar ∈ Argmin (compositePrimalObjective f (ι[K]) L) ↔
        L xbar ∈ K ∧ ∃ vbar : EuclideanSpace ℝ (Fin M), PolarSubgradientWitness f K L xbar vbar :=
    mem_argmin_coneConstraintObjective_iff_exists_polar_subgradient
      hf hK_nonempty hK_closed hK_convex hK_cone hqual
  rw [hargminOn, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, hxobj⟩
    rcases howner.mp hxobj with ⟨hxK, vbar, hvbar⟩
    refine ⟨hxK, -vbar, ?_⟩
    have hbridge :
        PolarSubgradientWitness f K L xbar (-(-vbar)) ↔
          -vbar ∈ K ∧
            L.adjoint (-vbar) ∈ (∂ f) xbar ∧
              ⟪xbar, L.adjoint (-vbar)⟫_ℝ = 0 :=
      polarSubgradientWitness_matrix_nonnegativeOrthant_iff A
    simpa [K, L] using hbridge.1 (by simpa using hvbar)
  · rintro ⟨hxK, vbar, hvbar, hsub, hinner⟩
    have hbridge :
        PolarSubgradientWitness f K L xbar (-vbar) ↔
          vbar ∈ K ∧
            L.adjoint vbar ∈ (∂ f) xbar ∧
              ⟪xbar, L.adjoint vbar⟫_ℝ = 0 :=
      polarSubgradientWitness_matrix_nonnegativeOrthant_iff A
    have hw : PolarSubgradientWitness f K L xbar (-vbar) :=
      hbridge.2 ⟨hvbar, hsub, hinner⟩
    refine ⟨hxK, howner.mpr ?_⟩
    exact ⟨hxK, -vbar, hw⟩

/-- Example 27.18 (2): every vector `vbar` satisfying the subgradient condition
`Aᵀ vbar ∈ ∂ f xbar` makes `xbar` a minimizer of the affine objective
`x ↦ f x - ⟪x, Aᵀ vbar⟫`. -/
theorem mem_argmin_affineObjective_of_matrix_adjoint_mem_subdifferential
    {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ)
    {f : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)}
    {xbar : EuclideanSpace ℝ (Fin N)} {vbar : EuclideanSpace ℝ (Fin M)}
    (hsub : (A.toEuclideanLin.toContinuousLinearMap).adjoint vbar ∈ (∂ f) xbar) :
    xbar ∈ Argmin (fun x : EuclideanSpace ℝ (Fin N) ↦
      (f x : EReal) -
        (⟪x, (A.toEuclideanLin.toContinuousLinearMap).adjoint vbar⟫_ℝ : EReal)) := by
  let L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin M) :=
    A.toEuclideanLin.toContinuousLinearMap
  have harg :
      xbar ∈ Argmin (fun x : EuclideanSpace ℝ (Fin N) ↦
        (f x : EReal) + (⟪x, L.adjoint (-vbar)⟫_ℝ : EReal)) :=
    mem_argmin_affineObjective_of_eq_and_neg_adjoint_mem_subdifferential L rfl
      (by simpa [L] using hsub)
  simpa [L, sub_eq_add_neg] using harg

end MatrixConeConstraints

end ERealFunction
