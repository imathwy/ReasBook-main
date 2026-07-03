import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_6_3
import LinearRepresentations_Serre_1977.Chap04.Remark_4_4_3_1.RegularIsotypicModel

open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule

noncomputable section

universe u v

namespace Representation

namespace Remark_4_4_3_1

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

/-- Helper for Remark 4-4.3-1: if the invariant Hermitian form is positive on the fixed source
vector, the Schur scalar is the normalized `J`-coefficient of that vector's image. -/
theorem scalar_of_intertwining_end_eq_div_apply_fixed_vector
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (f : σ.IntertwiningMap σ) :
    scalar_of_intertwining_end (G := G) σ f =
      J (chosen_irreducible_vector (G := G) σ) (f (chosen_irreducible_vector (G := G) σ)) /
        J (chosen_irreducible_vector (G := G) σ) (chosen_irreducible_vector (G := G) σ) := by
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  have hx₀_ne : x₀ ≠ 0 := by
    simpa [x₀] using chosen_irreducible_vector_ne_zero (G := G) σ
  rcases hJ_pos x₀ hx₀_ne with ⟨r, hr, hrJ⟩
  have hJx₀_ne : J x₀ x₀ ≠ 0 := by
    rw [hrJ]
    exact_mod_cast (ne_of_gt hr)
  have hx₀ :=
    congrArg (fun F : σ.IntertwiningMap σ ↦ F x₀)
      (scalar_of_intertwining_end_smul_id (G := G) σ f)
  have hJx₀ :=
    congrArg (fun z : W ↦ J x₀ z) hx₀
  have hmul :
      scalar_of_intertwining_end (G := G) σ f * J x₀ x₀ =
        J x₀ (f x₀) := by
    simpa [x₀, smul_eq_mul] using hJx₀
  -- Normalize by the positive scalar `J x₀ x₀` to recover the Schur coefficient from `f x₀`.
  simpa [x₀] using (eq_div_iff hJx₀_ne).2 hmul

/-- Helper for Remark 4-4.3-1: positivity of `J` turns the adjoint-test scalar into the
normalized inner product of the two intertwiner images of the fixed source vector. -/
theorem scalar_of_intertwining_end_comp_eq_inner_fixed_vector
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (S T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S).comp T) =
    inner ℂ
      (S (chosen_irreducible_vector (G := G) σ))
      (T (chosen_irreducible_vector (G := G) σ)) /
        J (chosen_irreducible_vector (G := G) σ) (chosen_irreducible_vector (G := G) σ) := by
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  -- Route correction: use the positive `J`-normalization at the fixed source vector so the
  -- self-test scalar becomes a genuine norm term on `D x₀`.
  rw [scalar_of_intertwining_end_eq_div_apply_fixed_vector
    (G := G) (σ := σ) (J := J) (hJ_pos := hJ_pos)]
  rw [Representation.IntertwiningMap.comp_apply]
  calc
    J x₀ ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S) (T x₀)) /
        J x₀ x₀
      =
        star (J ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S) (T x₀)) x₀) /
          J x₀ x₀ := by
            congr 1
            simpa using
              (hJ_herm
                ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S) (T x₀))
                x₀).symm
    _ = star (inner ℂ (T x₀) (S x₀)) / J x₀ x₀ := by
          congr 1
          rw [intertwiningMap_toDualAdjointMap_apply
            (G := G) (σ := σ) (J := J) (hJ := hJ) (T := S) (v := T x₀) (x := x₀)]
    _ = inner ℂ (S x₀) (T x₀) / J x₀ x₀ := by
          simp
    _ =
        inner ℂ
          (S (chosen_irreducible_vector (G := G) σ))
          (T (chosen_irreducible_vector (G := G) σ)) /
            J (chosen_irreducible_vector (G := G) σ) (chosen_irreducible_vector (G := G) σ) := by
              simp [x₀]

/-- Helper for Remark 4-4.3-1: after normalizing by the positive scalar `J x₀ x₀`, swapping the
two test intertwiners conjugates the extracted Schur scalar. -/
theorem scalar_of_intertwining_end_comp_swap_fixed_vector
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (S T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S).comp T)) =
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp S) := by
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  have hx₀_ne : x₀ ≠ 0 := by
    simpa [x₀] using chosen_irreducible_vector_ne_zero (G := G) σ
  rcases hJ_pos x₀ hx₀_ne with ⟨r, hr, hrJ⟩
  -- Rewrite both test scalars using the same positive normalizing constant `J x₀ x₀`.
  rw [scalar_of_intertwining_end_comp_eq_inner_fixed_vector
    (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
    (S := S) (T := T)]
  rw [scalar_of_intertwining_end_comp_eq_inner_fixed_vector
    (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
    (S := T) (T := S)]
  rw [hrJ]
  -- Conjugating the numerator swaps the inner-product arguments, while the denominator is real.
  simp

/-- Helper for Remark 4-4.3-1: when the test intertwiner itself comes from a matrix coefficient,
the recovery pairing is the conjugate of the expected dual evaluation. -/
theorem matrixCoefficient_codRestrict_pairing_eval_on_image_star
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (ℓ : Module.Dual ℂ W) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
          ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ) ℓ)).comp T) =
      star
        (ℓ (J.symm
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T))) := by
  let x : W := J.symm ℓ
  have hswap :=
    scalar_of_intertwining_end_comp_swap_fixed_vector
      (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (S := T)
      (T := (matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ) ℓ)
  have hrecover :
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T x =
        star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp
              ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ) ℓ))) := by
    simpa [x] using
      matrixCoefficient_codRestrict_dualRecovery_apply
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ) (T := T) (x := x)
  have hx :
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T x =
        star
          (ℓ (J.symm
            ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T))) := by
    -- The Hermitian symmetry of `J` swaps the two recovered dual vectors after conjugation.
    calc
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T x
        = star
            (star
              ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T x)) := by
                simp
      _ = star
            (ℓ (J.symm
              ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T))) := by
                congr 1
                simpa [x] using
                  (hJ_herm
                    (J.symm
                      ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T))
                    x)
  -- Combine the swapped scalar identity with the explicit recovery formula at `x = J.symm ℓ`.
  calc
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ) ℓ)).comp T)
      =
        star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp
              ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ) ℓ))) := by
              simpa using hswap.symm
    _ =
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T x := by
              exact hrecover.symm
    _ =
        star
          (ℓ (J.symm
            ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T))) := by
              exact hx

/-- Helper for Remark 4-4.3-1: the recovered scalar pairing can be rewritten as the ordinary
test pairing against the matrix-coefficient image of the recovered dual. -/
theorem matrixCoefficient_codRestrict_recovered_pairing_eq_image_pairing
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (S T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ T)
        (J.symm
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ S))) =
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ)
              ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) S))).comp T) := by
  -- First swap the two recovered dual evaluations by Hermitian symmetry.
  calc
    (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ T)
        (J.symm
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ S))) =
      star
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ S)
          (J.symm
            ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ T)))) := by
              simpa using
                (matrixCoefficient_codRestrict_dualRecovery_swap_star
                  (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm)
                  (S := S) (T := T)).symm
    -- Then identify the conjugated recovered evaluation with the source test pairing on the image.
    _ =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
              ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
                (G := G) σ hσ)
                ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) S))).comp T) := by
              simpa using
                (matrixCoefficient_codRestrict_pairing_eval_on_image_star
                  (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
                  (hJ_herm := hJ_herm) (hJ_pos := hJ_pos) (T := T)
                  (ℓ := (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) S)).symm

/-- Helper for Remark 4-4.3-1: exact recovery on coefficient images already kills the full
reconstruction defect for those image intertwiners. -/
theorem matrixCoefficient_codRestrict_image_recovery_defect_zero_of_on_image
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hrecover :
      ∀ ℓ : Module.Dual ℂ W,
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ) = ℓ)
    (ℓ : Module.Dual ℂ W) :
    (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
          ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ℓ))) -
      (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
        (G := G) σ hσ) ℓ) = 0 := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  -- Push the assumed exactness `Ψ (Φ ℓ) = ℓ` back across the image map `Φ`.
  have himage : Φ (Ψ (Φ ℓ)) = Φ ℓ := by
    exact congrArg Φ (hrecover ℓ)
  exact sub_eq_zero.mpr himage

/-- Helper for Remark 4-4.3-1: exact recovery on coefficient images forces the image-case defect
to vanish on the chosen irreducible vector. -/
theorem matrixCoefficient_codRestrict_image_defect_x0_zero_of_on_image
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hrecover :
      ∀ ℓ : Module.Dual ℂ W,
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ) = ℓ)
    (ℓ : Module.Dual ℂ W) :
    (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
          ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ℓ))) -
      (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
        (G := G) σ hσ) ℓ) (chosen_irreducible_vector (G := G) σ) = 0 := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  -- Evaluate the already vanished image-case defect on the fixed source vector.
  have hzero :
      (Φ (Ψ (Φ ℓ)) - Φ ℓ) = 0 := by
    simpa [Φ, Ψ] using
      matrixCoefficient_codRestrict_image_recovery_defect_zero_of_on_image
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hrecover := hrecover) (ℓ := ℓ)
  have happly := congrArg
    (fun F :
      σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) ↦
        F (chosen_irreducible_vector (G := G) σ)) hzero
  simpa [Φ, Ψ] using happly

/-- Helper for Remark 4-4.3-1: once a defect intertwiner vanishes on the fixed source vector,
every Schur pairing against that defect vanishes as well. -/
theorem matrixCoefficient_codRestrict_pairing_zero_of_apply_chosen_irreducible_vector_zero
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (S D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hDx₀ : D (chosen_irreducible_vector (G := G) σ) = 0) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S).comp D) = 0 := by
  -- Rewrite the Schur scalar as the normalized inner product against `D x₀`.
  rw [scalar_of_intertwining_end_comp_eq_inner_fixed_vector
    (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
    (S := S) (T := D)]
  -- The fixed-vector hypothesis makes the numerator vanish.
  simp [hDx₀]

/-- Helper for Remark 4-4.3-1: if the reconstruction defect already vanishes on the chosen
irreducible source vector, then its self-test scalar vanishes immediately. This reduces the final
analytic frontier to the source-faithful fixed-vector statement `D x₀ = 0`. -/
theorem matrixCoefficient_codRestrict_self_test_zero_of_apply_chosen_irreducible_vector_zero
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hDx₀ : D (chosen_irreducible_vector (G := G) σ) = 0) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) = 0 := by
  -- Reuse the generic pairing vanishing lemma with the same defect in both slots.
  simpa using
    matrixCoefficient_codRestrict_pairing_zero_of_apply_chosen_irreducible_vector_zero
      (G := G) (σ := σ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (S := D) (D := D) hDx₀

/-- Helper for Remark 4-4.3-1: once coefficient images are recovered exactly, the global defect
`Φ (Ψ T) - T` is orthogonal to every matrix-coefficient image. -/
theorem matrixCoefficient_codRestrict_defect_pairing_zero_of_on_image
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (hrecover :
      ∀ ℓ : Module.Dual ℂ W,
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ) = ℓ)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (ℓ : Module.Dual ℂ W) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
          ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ℓ)).comp
        (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)) = 0 := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  have himage : Ψ (Φ (Ψ T)) = Ψ T := by
    exact hrecover (Ψ T)
  have hnegcomp :
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ (Φ ℓ)).comp (-T)) =
        -((intertwiningMap_toDualAdjointMap (G := G) σ J hJ (Φ ℓ)).comp T) := by
    apply Representation.IntertwiningMap.ext
    ext x
    simp
  -- Expand the defect linearly, then rewrite both image pairings by the same recovered dual.
  calc
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ (Φ ℓ)).comp (Φ (Ψ T) - T))
      =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ (Φ ℓ)).comp (Φ (Ψ T))) -
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ (Φ ℓ)).comp T) := by
            rw [sub_eq_add_neg, Representation.IntertwiningMap.add_comp, map_add, hnegcomp]
            simpa [sub_eq_add_neg]
    _ =
        star (ℓ (J.symm (Ψ T))) - star (ℓ (J.symm (Ψ T))) := by
          rw [matrixCoefficient_codRestrict_pairing_eval_on_image_star
            (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
            (hJ_herm := hJ_herm) (hJ_pos := hJ_pos) (T := Φ (Ψ T)) (ℓ := ℓ)]
          rw [himage]
          rw [matrixCoefficient_codRestrict_pairing_eval_on_image_star
            (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
            (hJ_herm := hJ_herm) (hJ_pos := hJ_pos) (T := T) (ℓ := ℓ)]
    _ = 0 := by simp

/-- Helper for Remark 4-4.3-1: if every coefficient-image pairing against `D` vanishes, then the
analytic recovery functional attached to `D` is already zero. -/
theorem matrixCoefficient_codRestrict_dualRecovery_zero_of_all_image_pairings
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hpair :
      ∀ ℓ : Module.Dual ℂ W,
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
              ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
                (G := G) σ hσ) ℓ)).comp D) = 0) :
    (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0 := by
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let x : W := J.symm (Ψ D)
  have hx_pairing_right :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) (Ψ D))).comp D) = 0 :=
    hpair (Ψ D)
  have hx_pairing :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp
          ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) (Ψ D))) = 0 := by
    have hswap :=
      scalar_of_intertwining_end_comp_swap_fixed_vector
        (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm)
        (hJ_pos := hJ_pos)
        (S := (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ) (Ψ D))
        (T := D)
    rw [← hswap]
    simpa using hx_pairing_right
  have hx_eval : (Ψ D) x = 0 := by
    -- Evaluate the vanishing pairing on the `J`-representative of the recovered functional.
    rw [← matrixCoefficient_codRestrict_pairing_eval_on_image_exact
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm)
      (T := D) (ℓ := Ψ D)]
    exact hx_pairing
  have hx_zero : x = 0 := by
    by_contra hx_ne
    rcases hJ_pos x hx_ne with ⟨r, hr, hrJ⟩
    -- Positivity of `J` forbids a nonzero vector whose `J`-norm vanishes.
    rw [show (Ψ D) x = J x x by simp [x], hrJ] at hx_eval
    exact hr.ne' (Complex.ofReal_eq_zero.mp hx_eval)
  -- Move the vanishing `J`-representative back across the conjugate-dual equivalence.
  have hΨ_zero := congrArg J hx_zero
  simpa [x, Ψ] using hΨ_zero

/-- Helper for Remark 4-4.3-1: once coefficient images are recovered exactly, the global defect
`Φ (Ψ T) - T` has vanishing analytic recovery functional. -/
theorem matrixCoefficient_codRestrict_defect_dualRecovery_zero_of_on_image
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (hrecover :
      ∀ ℓ : Module.Dual ℂ W,
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ) = ℓ)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
      (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T) = 0 := by
  -- Specialize the general vanishing-of-recovery criterion to the reconstruction defect.
  apply matrixCoefficient_codRestrict_dualRecovery_zero_of_all_image_pairings
    (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
    (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
  intro ℓ
  simpa using
    matrixCoefficient_codRestrict_defect_pairing_zero_of_on_image
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (hrecover := hrecover) (T := T) (ℓ := ℓ)

/-- Helper for Remark 4-4.3-1: once the analytic recovery functional of `D` vanishes, every
coefficient-image pairing with `D` vanishes in both slot orders. This isolates the remaining
source blocker to the kernel statement `Ψ D = 0 → D x₀ = 0`. -/
theorem matrixCoefficient_codRestrict_pairings_zero_of_dualRecovery_zero
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hΨD :
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0) :
    (∀ ℓ : Module.Dual ℂ W,
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp
          ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ℓ)) = 0) ∧
      ∀ ℓ : Module.Dual ℂ W,
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
              ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
                (G := G) σ hσ) ℓ)).comp D) = 0 := by
  constructor
  · intro ℓ
    -- Evaluate the left-slot pairing through the exact recovery formula and collapse it with
    -- the vanishing recovered functional `Ψ D = 0`.
    rw [matrixCoefficient_codRestrict_pairing_eval_on_image_exact
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (T := D) (ℓ := ℓ)]
    simp [hΨD]
  · intro ℓ
    have hleft :
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ)) = 0 := by
      rw [matrixCoefficient_codRestrict_pairing_eval_on_image_exact
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (T := D) (ℓ := ℓ)]
      simp [hΨD]
    have hswap :=
      scalar_of_intertwining_end_comp_swap_fixed_vector
        (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm)
        (hJ_pos := hJ_pos) (S := D)
        (T := (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ) ℓ)
    -- Hermitian symmetry turns the already vanished left-slot pairing into the right-slot one.
    rw [← hswap]
    simpa [hleft]

/-- Helper for Remark 4-4.3-1: to prove a codomain intertwiner is zero, it is enough to show that
its value on the chosen irreducible source vector vanishes. The generic self-test then turns that
single fixed-vector vanishing into the full zero conclusion. -/
theorem intertwiningMap_zero_of_apply_chosen_irreducible_vector_zero
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (τ : Representation ℂ G V)
    (T : σ.IntertwiningMap τ)
    (hTx₀ : T (chosen_irreducible_vector (G := G) σ) = 0) :
    T = 0 := by
  -- Route correction: this step is purely representation-theoretic. An intertwiner out of an
  -- irreducible source is injective or zero, so killing the chosen nonzero source vector forces
  -- the zero case immediately.
  rcases Representation.IsIrreducible.injective_or_eq_zero (ρ := σ) (σ := τ) T with hT_inj | hT_zero
  · have hx₀_zero : chosen_irreducible_vector (G := G) σ = 0 := by
      apply hT_inj
      simpa using hTx₀
    exact (chosen_irreducible_vector_ne_zero (G := G) σ hx₀_zero).elim
  · exact hT_zero

/-- Helper for Remark 4-4.3-1: to prove a codomain intertwiner is zero, it is enough to show that
its value on the chosen irreducible source vector vanishes. The current codomain-specialized
version is now just the pure irreducibility criterion above. -/
theorem matrixCoefficient_codRestrict_zero_of_apply_chosen_irreducible_vector_zero
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hDx₀ : D (chosen_irreducible_vector (G := G) σ) = 0) :
    D = 0 := by
  let _ := hJ
  let _ := hJ_herm
  let _ := hJ_pos
  -- The source-faithful content here is only irreducibility of the source representation.
  exact
    intertwiningMap_zero_of_apply_chosen_irreducible_vector_zero
      (G := G) (σ := σ)
      (((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
      D hDx₀

/-- Helper for Remark 4-4.3-1: if the Schur self-test scalar of a codomain intertwiner vanishes,
then the intertwiner already vanishes on the chosen irreducible source vector. This isolates the
final analytic blocker to a single self-pairing identity. -/
theorem
    matrixCoefficient_codRestrict_apply_chosen_irreducible_vector_zero_of_self_test_zero
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hself :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) = 0) :
    D (chosen_irreducible_vector (G := G) σ) = 0 := by
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  have hx₀_ne : x₀ ≠ 0 := by
    simpa [x₀] using chosen_irreducible_vector_ne_zero (G := G) σ
  rcases hJ_pos x₀ hx₀_ne with ⟨r, hr, hrJ⟩
  -- Rewrite the self-test scalar as the normalized norm of `D x₀`.
  rw [scalar_of_intertwining_end_comp_eq_inner_fixed_vector
    (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
    (S := D) (T := D)] at hself
  have hden_ne : (J x₀ x₀) ≠ 0 := by
    rw [hrJ]
    exact_mod_cast (ne_of_gt hr)
  have hinner_zero : inner ℂ (D x₀) (D x₀) = 0 := by
    exact (div_eq_zero_iff.mp hself).resolve_right hden_ne
  -- Positive-definiteness of the ambient Hilbert norm forces the fixed vector image to vanish.
  have hDx₀_zero : D x₀ = 0 := inner_self_eq_zero.mp hinner_zero
  simpa [x₀] using hDx₀_zero

/-- Helper for Remark 4-4.3-1: once the reconstruction defect is known to vanish on the chosen
irreducible source vector for every test intertwiner, the generic self-test already upgrades that
pointwise vanishing to the full right-inverse identity `Φ.comp Ψ = id`. -/
theorem
    matrixCoefficientIntertwining_l2Regular_codRestrict_rightInverse_of_defect_apply_chosen_irreducible_vector_zero
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (hdefect :
      ∀ T : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
        (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
            ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
          (chosen_irreducible_vector (G := G) σ) = 0) :
    (matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ).comp
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) =
      LinearMap.id := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  -- Close the reconstruction identity pointwise by applying the fixed-vector zero criterion to
  -- the defect `D := Φ (Ψ T) - T`.
  apply LinearMap.ext
  intro T
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  have hDx₀ : D (chosen_irreducible_vector (G := G) σ) = 0 := by
    simpa [D, Φ, Ψ] using hdefect T
  have hDzero :
      D = 0 :=
    matrixCoefficient_codRestrict_zero_of_apply_chosen_irreducible_vector_zero
      (G := G) (σ := σ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (D := D) hDx₀
  have hsub : Φ (Ψ T) - T = 0 := by
    simpa [D, Φ, Ψ] using hDzero
  exact sub_eq_zero.mp hsub

/-- Helper for Remark 4-4.3-1: the only remaining Peter-Weyl input is that the reconstruction
defect `Φ (Ψ T) - T` already vanishes on the chosen irreducible source vector. Once this
source-faithful image-exactness step is supplied, the previous helper closes the right inverse
formally. -/
theorem
    matrixCoefficient_codRestrict_defect_apply_chosen_irreducible_vector_zero_of_on_image_and_bridge
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (hrecover :
      ∀ ℓ : Module.Dual ℂ W,
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ) = ℓ)
    (hbridge :
      ∀ D : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0 →
        (∀ ℓ : Module.Dual ℂ W,
          scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
                ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
                  (G := G) σ hσ) ℓ)).comp D) = 0) →
        D (chosen_irreducible_vector (G := G) σ) = 0)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
      (chosen_irreducible_vector (G := G) σ) = 0 := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  have hΨD : Ψ D = 0 := by
    -- The same exactness package kills the analytic recovery functional of the defect.
    simpa [D, Φ, Ψ] using
      matrixCoefficient_codRestrict_defect_dualRecovery_zero_of_on_image
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (hrecover := hrecover) (T := T)
  have hpair :
      ∀ ℓ : Module.Dual ℂ W,
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ (Φ ℓ)).comp D) = 0 := by
    intro ℓ
    -- Once `Ψ D = 0` is known, the right-slot vanishing against every coefficient image is
    -- formal; the extra pairing hypothesis in the old bridge is redundant.
    exact
      (matrixCoefficient_codRestrict_pairings_zero_of_dualRecovery_zero
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (D := D) hΨD).2 ℓ
  -- Only the final bridge from zero image pairings plus `Ψ D = 0` to `D x₀ = 0` remains.
  simpa [D, Φ, Ψ] using hbridge D hΨD hpair

/-- Helper for Remark 4-4.3-1: after exact recovery on coefficient images is available, the
remaining source-faithful bridge can be reduced to the smaller kernel statement
`Ψ D = 0 → D x₀ = 0`. The extra coefficient-pairing vanishing in the older bridge is now a
formal consequence of `Ψ D = 0`. -/
theorem
    matrixCoefficient_codRestrict_defect_apply_chosen_irreducible_vector_zero_of_on_image_and_kernel_bridge
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (hrecover :
      ∀ ℓ : Module.Dual ℂ W,
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ) = ℓ)
    (hkernel :
      ∀ D : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0 →
        D (chosen_irreducible_vector (G := G) σ) = 0)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
      (chosen_irreducible_vector (G := G) σ) = 0 := by
  -- Route correction: the old bridge asked for both `Ψ D = 0` and vanishing coefficient-image
  -- pairings. The new pairing lemma shows those pairings already follow from `Ψ D = 0`.
  refine
    matrixCoefficient_codRestrict_defect_apply_chosen_irreducible_vector_zero_of_on_image_and_bridge
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (hrecover := hrecover)
      (hbridge := fun D hΨD _ ↦ hkernel D hΨD)
      (T := T)

/-- Helper for Remark 4-4.3-1: once exact recovery on coefficient images and the kernel bridge
`Ψ D = 0 → D x₀ = 0` are both available, the defect self-test scalar vanishes formally. This
packages the old defect chain into the precise two source-faithful inputs still missing. -/
theorem matrixCoefficient_codRestrict_defect_self_test_zero_of_on_image_and_kernel_bridge
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (hrecover :
      ∀ ℓ : Module.Dual ℂ W,
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ) = ℓ)
    (hkernel :
      ∀ D : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0 →
        D (chosen_irreducible_vector (G := G) σ) = 0)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    let D :
        σ.IntertwiningMap
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
      (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) = 0 := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  -- Route correction: exact recovery on coefficient images plus the kernel bridge first kill
  -- `D x₀`, and the fixed-vector criterion then turns that into the desired self-test vanishing.
  have hDx₀ :
      D (chosen_irreducible_vector (G := G) σ) = 0 := by
    simpa [D, Φ, Ψ] using
      matrixCoefficient_codRestrict_defect_apply_chosen_irreducible_vector_zero_of_on_image_and_kernel_bridge
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (hrecover := hrecover) (hkernel := hkernel) (T := T)
  have hself :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) = 0 := by
    exact
      matrixCoefficient_codRestrict_self_test_zero_of_apply_chosen_irreducible_vector_zero
        (G := G) (σ := σ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (D := D) hDx₀
  simpa [D, Φ, Ψ] using hself

/-- Helper for Remark 4-4.3-1: once exact recovery on coefficient images and the kernel bridge
`Ψ D = 0 → D x₀ = 0` are supplied, the analytic recovery map is already a genuine right inverse
to the corestricted matrix-coefficient map. This packages the proved suffix of the source route so
that the remaining blocker is exactly the two missing source inputs. -/
theorem
    matrixCoefficientIntertwining_l2Regular_codRestrict_rightInverse_of_on_image_and_kernel_bridge
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (hrecover :
      ∀ ℓ : Module.Dual ℂ W,
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ) ℓ) = ℓ)
    (hkernel :
      ∀ D : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0 →
        D (chosen_irreducible_vector (G := G) σ) = 0) :
    (matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ).comp
        (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) =
      LinearMap.id := by
  -- Route correction: stop reopening the old defect chain. The proved suffix now shows that
  -- on-image exactness plus the kernel bridge already force the reconstruction identity `Φ ∘ Ψ = id`.
  exact
    matrixCoefficientIntertwining_l2Regular_codRestrict_rightInverse_of_defect_apply_chosen_irreducible_vector_zero
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (hdefect := fun T ↦
        matrixCoefficient_codRestrict_defect_apply_chosen_irreducible_vector_zero_of_on_image_and_kernel_bridge
          (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
          (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
          (hrecover := hrecover) (hkernel := hkernel) (T := T))


end PeterWeyl

end Remark_4_4_3_1

end Representation
