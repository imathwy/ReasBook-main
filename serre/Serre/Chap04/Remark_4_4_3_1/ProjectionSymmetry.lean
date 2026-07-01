import Mathlib
import Serre.Chap02.Exercise_2_2_6_3
import Serre.Chap04.Remark_4_4_3_1.DefectRecovery

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

/-- Helper for Remark 4-4.3-1: the only remaining Peter-Weyl input is that the reconstruction
defect `Φ (Ψ T) - T` already vanishes on the chosen irreducible source vector. Once this
source-faithful image-exactness step is supplied, the previous helper closes the right inverse
formally. -/
theorem matrixCoefficient_codRestrict_projection_pairing_eq
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (S T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S).comp
        (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ).comp
          (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)) T)) =
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ
            (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ).comp
              (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ)) S)).comp T) := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  -- The source test pairing sees the analytic projection `Φ ∘ Ψ` symmetrically in the two slots.
  calc
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S).comp ((Φ.comp Ψ) T))
      = Ψ T (J.symm (Ψ S)) := by
          simpa [Φ, Ψ] using
            matrixCoefficient_codRestrict_recovery_represents_testPairing
              (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
              (hJ_herm := hJ_herm) (S := S) (T := T)
    _ =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ ((Φ.comp Ψ) S)).comp T) := by
            simpa [Φ, Ψ] using
              matrixCoefficient_codRestrict_recovered_pairing_eq_image_pairing
                (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
                (hJ_herm := hJ_herm) (hJ_pos := hJ_pos) (S := S) (T := T)

/-- Helper for Remark 4-4.3-1: once coefficient images are recovered exactly, the recovered
projection `Φ (Ψ T)` is already orthogonal to the reconstruction defect `D := Φ (Ψ T) - T` in the
source test pairing. This packages the previously local `Ψ D = 0` collapse as a reusable step. -/
theorem matrixCoefficient_codRestrict_defect_projection_pairing_zero_of_on_image
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
    let D :
        σ.IntertwiningMap
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
      (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp
        ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
          (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T))) = 0 := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  have hΨD : Ψ D = 0 := by
    -- Exact recovery on coefficient images annihilates the analytic recovery of the defect.
    simpa [D, Φ, Ψ] using
      matrixCoefficient_codRestrict_defect_dualRecovery_zero_of_on_image
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (hrecover := hrecover) (T := T)
  have hPD : Φ (Ψ D) = 0 := by
    simpa [hΨD] using congrArg Φ hΨD
  have hproj :=
    matrixCoefficient_codRestrict_projection_pairing_eq
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos) (S := D) (T := T)
  -- Rewrite the projection pairing through the symmetry identity, then collapse it using `Ψ D = 0`.
  have hproj' :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp (Φ (Ψ T))) =
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ 0).comp T) := by
          simpa [Φ, Ψ, hPD] using hproj
  have hcomp_zero :
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ 0).comp T) = 0 := by
    -- The zero test intertwiner has zero adjoint, so the composite vanishes pointwise.
    apply Representation.IntertwiningMap.ext
    ext x
    simp
  have hzero' :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ 0).comp T) = 0 := by
          rw [hcomp_zero]
          simp
  exact hproj'.trans hzero'

/-- Helper for Remark 4-4.3-1: once coefficient images are recovered exactly, the defect
self-test scalar is already the negative of the remaining mixed pairing against `T`. This isolates
the final blocker to a single mixed-term normalization. -/
theorem matrixCoefficient_codRestrict_defect_self_test_eq_neg_right_pairing_of_on_image
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
    let D :
        σ.IntertwiningMap
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
      (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  have hprojection_zero :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp (Φ (Ψ T))) = 0 := by
    -- Reuse the isolated projection-orthogonality lemma instead of reopening the `Ψ D = 0` bridge.
    simpa [D, Φ, Ψ] using
      matrixCoefficient_codRestrict_defect_projection_pairing_zero_of_on_image
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (hrecover := hrecover) (T := T)
  -- Expand the second slot of the self-test scalar across the defect `D = Φ (Ψ T) - T`.
  calc
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D)
      =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp (Φ (Ψ T))) -
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
            have hcomp_defect :
                ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
                  ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp
                    (Φ (Ψ T) - T)) := by
              rfl
            rw [hcomp_defect]
            have hnegcomp :
                ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp (-T)) =
                  -((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
              apply Representation.IntertwiningMap.ext
              ext x
              simp
            rw [sub_eq_add_neg, Representation.IntertwiningMap.add_comp, map_add, hnegcomp]
            simp [sub_eq_add_neg]
    _ = 0 -
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
            rw [hprojection_zero]
    _ =
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
            simp

/-- Helper for Remark 4-4.3-1: once coefficient images are recovered exactly, the defect
self-test scalar is also the negative of the mixed pairing with the slots swapped. This is the
conjugate form of the same remaining normalization problem. -/
theorem matrixCoefficient_codRestrict_defect_self_test_eq_neg_left_pairing_of_on_image
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
    let D :
        σ.IntertwiningMap
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
      (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp D) := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  have hright :=
    matrixCoefficient_codRestrict_defect_self_test_eq_neg_right_pairing_of_on_image
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (hrecover := hrecover) (T := T)
  -- Hermitian symmetry converts the right mixed pairing into the left mixed pairing.
  calc
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D)
      =
        star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D)) := by
              simpa using
                (scalar_of_intertwining_end_comp_swap_fixed_vector
                  (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm)
                  (hJ_pos := hJ_pos) (S := D) (T := D)).symm
    _ =
        star
          (-scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T)) := by
              rw [show
                scalar_of_intertwining_end (G := G) σ
                  ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
                    -scalar_of_intertwining_end (G := G) σ
                      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) by
                        simpa [D, Φ, Ψ] using hright]
    _ =
        -star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T)) := by
              simp
    _ =
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp D) := by
            congr 1
            simpa using
              (scalar_of_intertwining_end_comp_swap_fixed_vector
                (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm)
                (hJ_pos := hJ_pos) (S := D) (T := T))

/-- Helper for Remark 4-4.3-1: once coefficient images are recovered exactly, the remaining
right mixed pairing is already fixed by complex conjugation. This isolates the unresolved source
step to proving that this real scalar actually vanishes. -/
theorem matrixCoefficient_codRestrict_defect_right_pairing_star_eq_self_of_on_image
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
    let D :
        σ.IntertwiningMap
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
      (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
    star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T)) =
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  have hleft :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
      -scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp D) := by
    -- The left-slot version of the defect identity rewrites the self-test through the swapped
    -- mixed pairing.
    simpa [D, Φ, Ψ] using
      matrixCoefficient_codRestrict_defect_self_test_eq_neg_left_pairing_of_on_image
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (hrecover := hrecover) (T := T)
  have hright :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
      -scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
    -- The right-slot version is the source-facing reduction already established above.
    simpa [D, Φ, Ψ] using
      matrixCoefficient_codRestrict_defect_self_test_eq_neg_right_pairing_of_on_image
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (hrecover := hrecover) (T := T)
  have hswap :
      star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T)) =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp D) := by
    -- Hermitian symmetry swaps the two mixed pairings after complex conjugation.
    simpa using
      (scalar_of_intertwining_end_comp_swap_fixed_vector
        (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm)
        (hJ_pos := hJ_pos) (S := D) (T := T))
  have hpair_eq :
      scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp D) =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
    have hleft' :
        -scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
          scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp D) := by
      rw [hleft]
      simp
    have hright' :
        -scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
          scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
      rw [hright]
      simp
    -- Both mixed pairings are the negative of the same self-test scalar, so they agree.
    calc
      scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp D)
        =
          -scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) := by
              simpa using hleft'.symm
      _ =
          scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
              simpa using hright'
  -- Combine the swap-conjugation law with the equality of the two mixed pairings.
  calc
    star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T))
      =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp D) := by
            exact hswap
    _ =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
            exact hpair_eq

/-- Helper for Remark 4-4.3-1: the remaining Peter-Weyl blocker is now isolated as the vanishing
of the defect self-test scalar. The proved projection-symmetry lemmas reduce this to exact
on-image recovery plus a final mixed-pairing normalization. -/
theorem
    matrixCoefficient_codRestrict_defect_self_test_zero_of_on_image_and_right_pairing_zero
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
    (hmixed :
      let D :
          σ.IntertwiningMap
            ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
        (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
            ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) = 0) :
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
  -- The proved right-pairing identity collapses the defect self-test to the single mixed term.
  have hself :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
      -scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
    simpa [D, Φ, Ψ] using
      matrixCoefficient_codRestrict_defect_self_test_eq_neg_right_pairing_of_on_image
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (hrecover := hrecover) (T := T)
  have hmixed' :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) = 0 := by
    simpa [D, Φ, Ψ] using hmixed
  -- Once the mixed term vanishes, the defect self-test scalar vanishes as well.
  change scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) = 0
  rw [hself, hmixed']
  simp

/-- Helper for Remark 4-4.3-1: once coefficient images are recovered exactly, the defect
self-test scalar vanishes if and only if the remaining right mixed pairing vanishes. This
packages the last analytic frontier as a single mixed-pairing statement. -/
theorem
    matrixCoefficient_codRestrict_defect_right_pairing_zero_iff_self_test_zero_of_on_image
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
    let D :
        σ.IntertwiningMap
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
      (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) = 0 ↔
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) = 0 := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  constructor
  · intro hmixed
    -- Route correction: the previously isolated reduction theorem turns the mixed-pairing
    -- vanishing into the defect self-test vanishing without reopening the stronger bridge.
    have hself :
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) = 0 := by
      exact
        matrixCoefficient_codRestrict_defect_self_test_zero_of_on_image_and_right_pairing_zero
          (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
          (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
          (hrecover := hrecover) (T := T) (by simpa [D, Φ, Ψ] using hmixed)
    simpa [D, Φ, Ψ] using hself
  · intro hself
    -- Rewrite the self-test scalar as the negative of the right mixed pairing and simplify.
    have hself_eq :
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
      simpa [D, Φ, Ψ] using
        matrixCoefficient_codRestrict_defect_self_test_eq_neg_right_pairing_of_on_image
          (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
          (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
          (hrecover := hrecover) (T := T)
    have hneg_zero :
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) = 0 := by
      exact Eq.trans hself_eq.symm hself
    exact neg_eq_zero.mp hneg_zero

/-- Helper for Remark 4-4.3-1: once coefficient images are recovered exactly, the remaining right
mixed pairing is already a nonpositive real scalar. The only unresolved source step is to show
that this real scalar actually vanishes. -/
theorem
    matrixCoefficient_codRestrict_defect_right_pairing_eq_neg_nonneg_real_of_on_image
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
    let D :
        σ.IntertwiningMap
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
      (((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) - T)
    ∃ r : ℝ,
      0 ≤ r ∧
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) = -(r : ℂ) := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    Φ (Ψ T) - T
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  have hx₀_ne : x₀ ≠ 0 := by
    simpa [x₀] using chosen_irreducible_vector_ne_zero (G := G) σ
  rcases hJ_pos x₀ hx₀_ne with ⟨r₀, hr₀, hr₀J⟩
  have hself_eq :
      scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) := by
    -- Reuse the on-image defect identity to rewrite the mixed term as the negative self-test.
    simpa [D, Φ, Ψ] using
      matrixCoefficient_codRestrict_defect_self_test_eq_neg_right_pairing_of_on_image
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (hrecover := hrecover) (T := T)
  have hself_real :
      scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) =
        (((‖D x₀‖ ^ 2) / r₀ : ℝ) : ℂ) := by
    -- Rewrite the self-test scalar as the normalized squared norm of `D x₀`.
    have hnorm :
        inner ℂ (D x₀) (D x₀) = (((‖D x₀‖ ^ 2) : ℝ) : ℂ) := by
      simpa using (inner_self_eq_norm_sq_to_K (D x₀))
    rw [scalar_of_intertwining_end_comp_eq_inner_fixed_vector
      (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (S := D) (T := D)]
    rw [hr₀J, hnorm]
    simpa using (Complex.ofReal_div (‖D x₀‖ ^ 2) r₀).symm
  refine ⟨(‖D x₀‖ ^ 2) / r₀, div_nonneg (sq_nonneg ‖D x₀‖) hr₀.le, ?_⟩
  -- Convert the mixed pairing into the negative of the nonnegative self-test scalar.
  have hright :
      scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T) =
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) := by
    rw [hself_eq]
    simp
  calc
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp T)
      =
        -scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ D).comp D) := hright
    _ = -((((‖D x₀‖ ^ 2) / r₀ : ℝ) : ℂ)) := by rw [hself_real]

/-- Helper for Remark 4-4.3-1: if the recovered dual vanishes, then the chosen fixed vector image
of `D` is orthogonal to every fixed vector coming from a matrix-coefficient image. This isolates
the remaining source step to a compact-coordinate spanning statement inside the `σ`-isotypic
block. -/
theorem
    matrixCoefficient_codRestrict_fixedVector_orthogonal_image_of_dualRecovery_zero
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
    -- The analytic kernel condition `Ψ D = 0` already kills every right-slot pairing with a
    -- matrix-coefficient image.
    exact
      (matrixCoefficient_codRestrict_pairings_zero_of_dualRecovery_zero
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (D := D) hΨD).2 (J x)
  have hden_ne : J x₀ x₀ ≠ 0 := by
    rw [hr₀J]
    exact_mod_cast (ne_of_gt hr₀)
  -- Rewrite the vanished pairing as the normalized inner product at the chosen source vector.
  rw [scalar_of_intertwining_end_comp_eq_inner_fixed_vector
    (G := G) (σ := σ) (J := J) (hJ := hJ) (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
    (S := (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
      (G := G) σ hσ) (J x)) (T := D)] at hpair
  exact (div_eq_zero_iff.mp hpair).resolve_right hden_ne

/-- Helper for Remark 4-4.3-1: the vanished recovery functional already forces orthogonality
against the whole coefficient-image range after evaluating intertwiners at the chosen source
vector. This packages the analytic part of the kernel bridge into a single range-level statement,
so the only remaining blocker is the source-faithful spanning theorem for that evaluated range. -/
theorem
    matrixCoefficient_codRestrict_fixedVector_orthogonal_range_of_dualRecovery_zero
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
  -- Move a general coefficient-image intertwiner back to the `J x` model used above.
  have horth :=
    matrixCoefficient_codRestrict_fixedVector_orthogonal_image_of_dualRecovery_zero
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (D := D) hΨD x
  simpa [x] using horth

/-- Helper for Remark 4-4.3-1: once `D x₀` is known to lie in the evaluated coefficient-image
range, the previously isolated orthogonality statement forces `D x₀ = 0`. This reduces the
kernel bridge to a single evaluated-range existence statement. -/
noncomputable def matrixCoefficient_codRestrict_evalAtChosenLinear
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] :
    Module.Dual ℂ W →ₗ[ℂ]
      (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule where
  toFun ℓ :=
    (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
      (G := G) σ hσ ℓ) (chosen_irreducible_vector (G := G) σ)
  map_add' ℓ₁ ℓ₂ := by
    -- Evaluate the coefficient family after using its linearity in the dual variable.
    simp [matrixCoefficientIntertwining_l2Regular_codRestrictLinear]
  map_smul' a ℓ := by
    -- The same evaluation is compatible with scalar multiplication.
    simp [matrixCoefficientIntertwining_l2Regular_codRestrictLinear]

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
    -- The evaluated column map agrees with evaluation of `Φ` at the chosen source vector.
    simpa [matrixCoefficient_codRestrict_evalAtChosenLinear, Φ] using hEval_sub
  have hPhi_zero : Φ (ℓ₁ - ℓ₂) = 0 := by
    -- Vanishing on the chosen nonzero vector forces the entire intertwiner to vanish.
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
    -- Reuse the range-level orthogonality statement at the specific preimage witnessing `D x₀`.
    exact
      matrixCoefficient_codRestrict_fixedVector_orthogonal_range_of_dualRecovery_zero
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (D := D) hΨD T hT_range
  have hself :
      inner ℂ
        (D (chosen_irreducible_vector (G := G) σ))
        (D (chosen_irreducible_vector (G := G) σ)) = 0 := by
    -- Substitute the preimage equality so the orthogonality becomes a self-inner-product.
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
  -- Project `D x₀` orthogonally onto the distinguished evaluated coefficient copy.
  have hproj_mem :
      (((K.orthogonalProjection y : K) :
        (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)) ∈ K := by
    simpa using (K.orthogonalProjection y).2
  rcases hproj_mem with ⟨ℓ, hℓ⟩
  let T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) := Φ ℓ
  refine ⟨T, ⟨ℓ, rfl⟩, ?_⟩
  intro U hU
  rcases hU with ⟨η, rfl⟩
  have hη_mem : (Φ η) x₀ ∈ K := by
    exact ⟨η, rfl⟩
  have horth_right :
      inner ℂ
        (y - (((K.orthogonalProjection y : K) :
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)))
        ((Φ η) x₀) = 0 := by
    -- The orthogonal projection leaves a residual orthogonal to every evaluated coefficient
    -- vector.
    exact Submodule.orthogonalProjectionFn_inner_eq_zero (K := K) y ((Φ η) x₀) hη_mem
  have horth :
      inner ℂ
        ((Φ η) x₀)
        (y - (((K.orthogonalProjection y : K) :
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule))) = 0 := by
    simpa [inner_eq_zero_symm] using horth_right
  -- Rewrite the orthogonal projection term back as the chosen coefficient-image preimage `T`.
  simpa [T, Φ, E, K, x₀, y, hℓ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using horth


end PeterWeyl

end Remark_4_4_3_1

end Representation
