import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_4

noncomputable section

open Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-- Helper for Exercise 18-18.6-3: the source-faithful degree-`4` slot is the augmentation
constituent of the natural action of `A₅` on five letters. -/
abbrev a5_augmentation_representation :
    Representation 𝔽₄ A5
      (permutationAugmentationSubrepresentation 𝔽₄ A5 (Fin 5)).toSubmodule :=
  permutationAugmentationRepresentation 𝔽₄ A5 (Fin 5)

/-- Helper for Exercise 18-18.6-3: the bundled degree-`4` slot over `𝔽₄`. -/
abbrev a5_augmentation_fdRep : FDRep 𝔽₄ A5 :=
  FDRep.of a5_augmentation_representation

/-- Helper for Exercise 18-18.6-3: the augmentation slot for the natural action of `A₅` on five
letters has degree `4`. -/
lemma a5_augmentation_representation_finrank :
    Module.finrank 𝔽₄
      (permutationAugmentationSubrepresentation 𝔽₄ A5 (Fin 5)).toSubmodule = 4 := by
  let ε : (Fin 5 →₀ 𝔽₄) →ₗ[𝔽₄] 𝔽₄ := permutationAugmentationLinearMap 𝔽₄ (Fin 5)
  have hrange : LinearMap.range ε = ⊤ := by
    -- The augmentation map is onto because a single basis vector already maps to any scalar.
    rw [LinearMap.range_eq_top]
    intro q
    refine ⟨Finsupp.single 0 q, ?_⟩
    simp [ε, permutationAugmentationLinearMap]
  have hsplit := LinearMap.finrank_range_add_finrank_ker ε
  have hrange_finrank : Module.finrank 𝔽₄ (LinearMap.range ε) = 1 := by
    -- The codomain is one-dimensional, so the surjective range has finrank `1`.
    rw [hrange]
    simp
  have hdomain_finrank : Module.finrank 𝔽₄ (Fin 5 →₀ 𝔽₄) = 5 := by
    -- The permutation module on five letters has the expected basis of point masses.
    simp
  have hker_finrank : Module.finrank 𝔽₄ (LinearMap.ker ε) = 4 := by
    -- Rank-nullity computes the kernel dimension once the range has been identified.
    linarith [hsplit, hrange_finrank, hdomain_finrank]
  -- The augmentation representation is definitionally the kernel of the augmentation map.
  simpa [ε, permutationAugmentationSubrepresentation, permutationAugmentation] using hker_finrank

/-- Helper for Exercise 18-18.6-3: the bundled augmentation slot has finrank `4`. -/
lemma a5_augmentation_fdRep_finrank :
    Module.finrank 𝔽₄ a5_augmentation_fdRep.V = 4 := by
  -- Unbundle the finite-dimensional representation back to its augmentation carrier.
  simpa [a5_augmentation_fdRep, a5_augmentation_representation] using
    a5_augmentation_representation_finrank
