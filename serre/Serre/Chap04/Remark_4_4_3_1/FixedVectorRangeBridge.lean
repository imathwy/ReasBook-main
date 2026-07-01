import Serre.Chap04.Remark_4_4_3_1.DefectRecovery

open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule

noncomputable section

universe u v

namespace Representation

open Remark_4_4_3_1

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

/-- Helper for Remark 4-4.3-1: if the recovered dual vanishes, then the chosen fixed vector image
of `D` is orthogonal to every fixed vector coming from a matrix-coefficient image. This isolates
the remaining source step to a compact-coordinate spanning statement inside the `σ`-isotypic
block. -/
theorem matrixCoefficient_codRestrict_fixedVector_orthogonal_image_of_dualRecovery_zero
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hΨD :
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0)
    (x : W) :
    inner ℂ
      ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
        (G := G) σ hσ) (J x) (chosen_irreducible_vector (G := G) σ))
      (D (chosen_irreducible_vector (G := G) σ)) = 0 := by
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  have hx₀_ne : x₀ ≠ 0 := by
    simpa [x₀] using chosen_irreducible_vector_ne_zero (G := G) σ
  rcases hJ_pos x₀ hx₀_ne with ⟨r₀, hr₀, hr₀J⟩
  have hpair :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) (J x))).comp D) = 0 := by
    exact
      (matrixCoefficient_codRestrict_pairings_zero_of_dualRecovery_zero
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (D := D) hΨD).2 (J x)
  have hden_ne : J x₀ x₀ ≠ 0 := by
    rw [hr₀J]
    exact_mod_cast (ne_of_gt hr₀)
  rw [scalar_of_intertwining_end_comp_eq_inner_fixed_vector
    (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
    (S := (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
      (G := G) σ hσ) (J x)) (T := D)] at hpair
  exact (div_eq_zero_iff.mp hpair).resolve_right hden_ne

/-- Helper for Remark 4-4.3-1: the vanished recovery functional already forces orthogonality
against the whole coefficient-image range after evaluating intertwiners at the chosen source
vector. This packages the analytic part of the kernel bridge into a single range-level statement,
so the only remaining blocker is the source-faithful spanning theorem for that evaluated range. -/
theorem matrixCoefficient_codRestrict_fixedVector_orthogonal_range_of_dualRecovery_zero
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hΨD :
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hT :
      T ∈ LinearMap.range
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ)) :
    inner ℂ
      (T (chosen_irreducible_vector (G := G) σ))
      (D (chosen_irreducible_vector (G := G) σ)) = 0 := by
  rcases hT with ⟨ℓ, rfl⟩
  let x : W := J.symm ℓ
  have horth :=
    matrixCoefficient_codRestrict_fixedVector_orthogonal_image_of_dualRecovery_zero
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (D := D) hΨD x
  simpa [x] using horth

/-- Helper for Remark 4-4.3-1: evaluation of the coefficient-image family at the distinguished
source vector. This is the first-coordinate bridge used in the compact reconstruction step. -/
noncomputable def matrixCoefficient_codRestrict_evalAtChosenLinear
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] :
    Module.Dual ℂ W →ₗ[ℂ]
      (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
  (LinearMap.applyₗ (R := ℂ) (M := W)
    (M₂ := (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (chosen_irreducible_vector (G := G) σ)).comp
    ((Representation.IntertwiningMap.toLinearMapl
      (ρ := σ)
      (σ := (l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)).comp
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ))

@[simp] theorem matrixCoefficient_codRestrict_evalAtChosenLinear_apply
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] (ℓ : Module.Dual ℂ W) :
    matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ ℓ =
      (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
        (G := G) σ hσ ℓ) (chosen_irreducible_vector (G := G) σ) :=
  rfl

/-- Helper for Remark 4-4.3-1: the chosen-vector evaluation of the coefficient family is already
injective. This is the compact analogue of Proposition 8's distinguished first-coordinate copy
`V_{i,1}` inside the `σ`-isotypic block. -/
theorem matrixCoefficient_codRestrict_evalAtChosenLinear_injective
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] :
    Function.Injective
      (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ) := by
  intro ℓ₁ ℓ₂ hEval
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  have hEval_sub :
      matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ (ℓ₁ - ℓ₂) = 0 := by
    rw [LinearMap.map_sub, hEval, sub_self]
  have hDx₀ :
      (Φ (ℓ₁ - ℓ₂)) (chosen_irreducible_vector (G := G) σ) = 0 := by
    simpa [matrixCoefficient_codRestrict_evalAtChosenLinear, Φ] using hEval_sub
  have hPhi_zero : Φ (ℓ₁ - ℓ₂) = 0 := by
    exact
      intertwiningMap_zero_of_apply_chosen_irreducible_vector_zero
        (G := G) (σ := σ)
        (((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
        (Φ (ℓ₁ - ℓ₂)) hDx₀
  have hdiff :
      ℓ₁ - ℓ₂ = 0 := by
    apply (matrixCoefficientIntertwining_l2Regular_codRestrictLinear_injective
      (G := G) σ hσ)
    simpa using hPhi_zero
  exact sub_eq_zero.mp hdiff

/-- Helper for Remark 4-4.3-1: once `D x₀` is known to lie in the evaluated coefficient-image
range, the previously isolated orthogonality statement forces `D x₀ = 0`. This reduces the
kernel bridge to a single evaluated-range existence statement. -/
theorem matrixCoefficient_codRestrict_fixedVector_zero_of_exists_range_preimage
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hΨD :
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0)
    (hpreimage :
      ∃ T : σ.IntertwiningMap
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
        T ∈ LinearMap.range
            (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ∧
          T (chosen_irreducible_vector (G := G) σ) =
            D (chosen_irreducible_vector (G := G) σ)) :
    D (chosen_irreducible_vector (G := G) σ) = 0 := by
  rcases hpreimage with ⟨T, hT_range, hTx₀⟩
  have horth :
      inner ℂ
        (T (chosen_irreducible_vector (G := G) σ))
        (D (chosen_irreducible_vector (G := G) σ)) = 0 := by
    exact
      matrixCoefficient_codRestrict_fixedVector_orthogonal_range_of_dualRecovery_zero
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (D := D) hΨD T hT_range
  have hself :
      inner ℂ
        (D (chosen_irreducible_vector (G := G) σ))
        (D (chosen_irreducible_vector (G := G) σ)) = 0 := by
    simpa [hTx₀] using horth
  exact inner_self_eq_zero.mp hself

/-- Helper for Remark 4-4.3-1: the fixed-vector value of any intertwiner admits an orthogonal
decomposition into an evaluated coefficient part and a residual orthogonal to the entire
evaluated coefficient range. This shrinks the remaining Proposition 8 blocker to showing that the
orthogonal residual itself must vanish. -/
theorem matrixCoefficient_codRestrict_exists_range_preimage_with_orthogonal_residual
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    ∃ T : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
      T ∈ LinearMap.range
          (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ∧
        ∀ U : σ.IntertwiningMap
            ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
          U ∈ LinearMap.range
              (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
                (G := G) σ hσ) →
            inner ℂ
              (U (chosen_irreducible_vector (G := G) σ))
              ((D - T) (chosen_irreducible_vector (G := G) σ)) = 0 := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let E := matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  let K :
      Submodule ℂ ((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule) :=
    LinearMap.range E
  let y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule := D x₀
  letI : FiniteDimensional ℂ K := inferInstance
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K
  letI : K.HasOrthogonalProjection := inferInstance
  rcases K.exists_add_mem_mem_orthogonal y with ⟨z, hzK, r, hrK, hyr⟩
  rcases hzK with ⟨ℓ, hℓ⟩
  let T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) := Φ ℓ
  refine ⟨T, ⟨ℓ, rfl⟩, ?_⟩
  intro U hU
  rcases hU with ⟨η, rfl⟩
  have hη_mem : (Φ η) x₀ ∈ K := ⟨η, rfl⟩
  have horth : inner ℂ ((Φ η) x₀) r = 0 :=
    Submodule.inner_right_of_mem_orthogonal hη_mem hrK
  have hT_eval : T x₀ = z := by
    change (Φ ℓ) x₀ = z
    simpa [E] using hℓ
  have hres : (D - T) x₀ = r := by
    change D x₀ - T x₀ = r
    calc
      D x₀ - T x₀ = y - z := by
        rw [hT_eval]
      _ = r := by
        rw [hyr]
        simp
  rw [hres]
  exact horth

/-- Helper for Remark 4-4.3-1: the evaluated-range existence statement is equivalent to first
showing that the chosen-vector image already lies in the range of the evaluation map. -/
theorem matrixCoefficient_codRestrict_exists_range_preimage_of_fixedVector_iff_mem_evalRange
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    (∃ T : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
      T ∈ LinearMap.range
          (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ∧
        T (chosen_irreducible_vector (G := G) σ) =
          D (chosen_irreducible_vector (G := G) σ)) ↔
      D (chosen_irreducible_vector (G := G) σ) ∈
        LinearMap.range
          (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ) := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let E := matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  constructor
  · rintro ⟨T, hT_range, hTx₀⟩
    rcases hT_range with ⟨ℓ, rfl⟩
    refine ⟨ℓ, ?_⟩
    simpa [E, Φ, x₀] using hTx₀
  · rintro ⟨ℓ, hℓ⟩
    refine ⟨Φ ℓ, ⟨ℓ, rfl⟩, ?_⟩
    simpa [E, Φ, x₀] using hℓ

end PeterWeyl

end Representation
