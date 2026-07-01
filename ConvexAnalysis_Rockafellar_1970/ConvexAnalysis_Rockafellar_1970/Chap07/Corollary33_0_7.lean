import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem33_0_6

noncomputable section

open Matrix
open scoped Rockafellar

section BilinearKernel

variable {𝕜 : Type*} {U : Type*} {X : Type*} {L : Type*}
variable [CommSemiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid L] [PartialOrder L] [Module 𝕜 L]

namespace IsBilinearMap

/-- A bilinear kernel is concave-convex on any convex product domain. -/
theorem isConcaveConvexOn
    {K : U → X → L} (hK : IsBilinearMap 𝕜 K)
    {C : Set U} {D : Set X}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    SaddleFunction.IsConcaveConvexOn 𝕜 C D K := by
  rw [SaddleFunction.isConcaveConvexOn_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa using
      (hK.toLinearMap.flip x).concaveOn hC
  · intro u hu
    simpa using
      (hK.toLinearMap u).convexOn hD

/-- A bilinear kernel is concave-convex in the whole-space Chapter 33 owner. -/
theorem isConcaveConvex
    {K : U → X → L} (hK : IsBilinearMap 𝕜 K) :
    SaddleFunction.IsConcaveConvex 𝕜 K := by
  simpa [SaddleFunction.IsConcaveConvex] using
    hK.isConcaveConvexOn (C := Set.univ) (D := Set.univ) convex_univ convex_univ

/-- A bilinear kernel is convex-concave on any convex product domain. -/
theorem isConvexConcaveOn
    {K : U → X → L} (hK : IsBilinearMap 𝕜 K)
    {C : Set U} {D : Set X}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    SaddleFunction.IsConvexConcaveOn 𝕜 C D K := by
  rw [SaddleFunction.isConvexConcaveOn_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa using
      (hK.toLinearMap.flip x).convexOn hC
  · intro u hu
    simpa using
      (hK.toLinearMap u).concaveOn hD

/-- A bilinear kernel is convex-concave in the whole-space Chapter 33 owner. -/
theorem isConvexConcave
    {K : U → X → L} (hK : IsBilinearMap 𝕜 K) :
    SaddleFunction.IsConvexConcave 𝕜 K := by
  simpa [SaddleFunction.IsConvexConcave] using
    hK.isConvexConcaveOn (C := Set.univ) (D := Set.univ) convex_univ convex_univ

end IsBilinearMap

end BilinearKernel

section PairingKernel

variable {𝕜 : Type*} {U : Type*} {X : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [HasLinearPairing U X 𝕜]

namespace HasLinearPairing

/-- The intrinsic pairing kernel is bilinear. -/
theorem isBilinearMap_pairing :
    IsBilinearMap 𝕜 (fun u : U => fun x : X => (⟪u, x⟫ₚ : 𝕜)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u₁ u₂ x
    simp
  · intro c u x
    simp
  · intro u x₁ x₂
    simp
  · intro c u x
    simp

variable [PartialOrder 𝕜]

/-- The intrinsic pairing kernel is concave-convex on any convex product domain. -/
theorem isConcaveConvexOn_pairing
    {C : Set U} {D : Set X}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    SaddleFunction.IsConcaveConvexOn 𝕜 C D (fun u : U => fun x : X => (⟪u, x⟫ₚ : 𝕜)) :=
  isBilinearMap_pairing.isConcaveConvexOn hC hD

/-- The intrinsic pairing kernel is concave-convex in the whole-space Chapter 33 owner. -/
theorem isConcaveConvex_pairing :
    SaddleFunction.IsConcaveConvex 𝕜 (fun u : U => fun x : X => (⟪u, x⟫ₚ : 𝕜)) := by
  simpa [SaddleFunction.IsConcaveConvex] using
    isConcaveConvexOn_pairing (𝕜 := 𝕜) (U := U) (X := X)
      (C := Set.univ) (D := Set.univ) convex_univ convex_univ

/-- The intrinsic pairing kernel is convex-concave on any convex product domain. -/
theorem isConvexConcaveOn_pairing
    {C : Set U} {D : Set X}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    SaddleFunction.IsConvexConcaveOn 𝕜 C D (fun u : U => fun x : X => (⟪u, x⟫ₚ : 𝕜)) :=
  isBilinearMap_pairing.isConvexConcaveOn hC hD

/-- The intrinsic pairing kernel is convex-concave in the whole-space Chapter 33 owner. -/
theorem isConvexConcave_pairing :
    SaddleFunction.IsConvexConcave 𝕜 (fun u : U => fun x : X => (⟪u, x⟫ₚ : 𝕜)) := by
  simpa [SaddleFunction.IsConvexConcave] using
    isConvexConcaveOn_pairing (𝕜 := 𝕜) (U := U) (X := X)
      (C := Set.univ) (D := Set.univ) convex_univ convex_univ

/-- Corollary33.0.7 (canonical pairing-owner form): every intrinsic linear pairing kernel is both
concave-convex and convex-concave. -/
theorem isConcaveConvex_and_isConvexConcave :
    SaddleFunction.IsConcaveConvex 𝕜 (fun u : U => fun x : X => (⟪u, x⟫ₚ : 𝕜)) ∧
      SaddleFunction.IsConvexConcave 𝕜 (fun u : U => fun x : X => (⟪u, x⟫ₚ : 𝕜)) :=
  ⟨isConcaveConvex_pairing (𝕜 := 𝕜) (U := U) (X := X),
    isConvexConcave_pairing (𝕜 := 𝕜) (U := U) (X := X)⟩

end HasLinearPairing

end PairingKernel

section DualKernel

variable {𝕜 : Type*} {U : Type*} {X : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

namespace LinearMap

/-- The evaluation kernel of a dual-valued linear map is bilinear. -/
theorem isBilinearMap_dualKernel
    (A : U →ₗ[𝕜] Module.Dual 𝕜 X) :
    IsBilinearMap 𝕜 (fun u xStar ↦ A u xStar) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u₁ u₂ xStar
    simp
  · intro c u xStar
    simp
  · intro u xStar₁ xStar₂
    simp
  · intro c u xStar
    simp

/-- An intrinsic dual-kernel induced by a linear map is concave-convex. -/
theorem isConcaveConvexOn_dualKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] Module.Dual 𝕜 X)
    {C : Set U} {D : Set X}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    SaddleFunction.IsConcaveConvexOn 𝕜 C D
      (fun u xStar ↦ A u xStar) := by
  letI : HasLinearPairing U X 𝕜 := ⟨A⟩
  simpa using
    (HasLinearPairing.isConcaveConvexOn_pairing
      (𝕜 := 𝕜) (U := U) (X := X) hC hD)

/-- An intrinsic dual-kernel induced by a linear map is concave-convex. -/
theorem isConcaveConvex_dualKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] Module.Dual 𝕜 X) :
    SaddleFunction.IsConcaveConvex 𝕜
      (fun u xStar ↦ A u xStar) := by
  letI : HasLinearPairing U X 𝕜 := ⟨A⟩
  simpa using
    (HasLinearPairing.isConcaveConvex_pairing (𝕜 := 𝕜) (U := U) (X := X))

/-- An intrinsic dual-kernel induced by a linear map is convex-concave. -/
theorem isConvexConcaveOn_dualKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] Module.Dual 𝕜 X)
    {C : Set U} {D : Set X}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    SaddleFunction.IsConvexConcaveOn 𝕜 C D
      (fun u xStar ↦ A u xStar) := by
  letI : HasLinearPairing U X 𝕜 := ⟨A⟩
  simpa using
    (HasLinearPairing.isConvexConcaveOn_pairing
      (𝕜 := 𝕜) (U := U) (X := X) hC hD)

/-- An intrinsic dual-kernel induced by a linear map is convex-concave. -/
theorem isConvexConcave_dualKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] Module.Dual 𝕜 X) :
    SaddleFunction.IsConvexConcave 𝕜
      (fun u xStar ↦ A u xStar) := by
  letI : HasLinearPairing U X 𝕜 := ⟨A⟩
  simpa using
    (HasLinearPairing.isConvexConcave_pairing (𝕜 := 𝕜) (U := U) (X := X))

/-- The dual-kernel induced by a linear map is both concave-convex and convex-concave. -/
theorem isConcaveConvex_and_isConvexConcave_dualKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] Module.Dual 𝕜 X) :
    SaddleFunction.IsConcaveConvex 𝕜
        (fun u xStar ↦ A u xStar) ∧
      SaddleFunction.IsConvexConcave 𝕜
        (fun u xStar ↦ A u xStar) := by
  letI : HasLinearPairing U X 𝕜 := ⟨A⟩
  simpa using
    (HasLinearPairing.isConcaveConvex_and_isConvexConcave (𝕜 := 𝕜) (U := U) (X := X))

/-- Corollary33.0.7 (canonical dual-owner form): a linear-map-induced dual kernel is both
concave-convex and convex-concave. -/
theorem isConcaveConvex_and_isConvexConcave
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] Module.Dual 𝕜 X) :
    SaddleFunction.IsConcaveConvex 𝕜
        (fun u xStar ↦ A u xStar) ∧
      SaddleFunction.IsConvexConcave 𝕜
        (fun u xStar ↦ A u xStar) :=
  A.isConcaveConvex_and_isConvexConcave_dualKernel

end LinearMap

end DualKernel

section DotProductBridge

variable {𝕜 : Type*} {U n : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [Fintype n]

namespace LinearMap

/-- A finite-coordinate dot-product kernel induced by a linear map is concave-convex. -/
theorem isConcaveConvexOn_dotProductKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] (n → 𝕜))
    {C : Set U} {D : Set (n → 𝕜)}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    SaddleFunction.IsConcaveConvexOn 𝕜 C D
      (fun u xStar ↦ (A u) ⬝ᵥ xStar) :=
  IsBilinearMap.isConcaveConvexOn (hK := A.isBilinearMap_dotProduct) hC hD

/-- A finite-coordinate dot-product kernel induced by a linear map is concave-convex. -/
theorem isConcaveConvex_dotProductKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] (n → 𝕜)) :
    SaddleFunction.IsConcaveConvex 𝕜
      (fun u xStar ↦ (A u) ⬝ᵥ xStar) := by
  simpa [SaddleFunction.IsConcaveConvex] using
    A.isConcaveConvexOn_dotProductKernel
      (C := Set.univ) (D := Set.univ) convex_univ convex_univ

/-- A finite-coordinate dot-product kernel induced by a linear map is convex-concave. -/
theorem isConvexConcaveOn_dotProductKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] (n → 𝕜))
    {C : Set U} {D : Set (n → 𝕜)}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    SaddleFunction.IsConvexConcaveOn 𝕜 C D
      (fun u xStar ↦ (A u) ⬝ᵥ xStar) :=
  IsBilinearMap.isConvexConcaveOn (hK := A.isBilinearMap_dotProduct) hC hD

/-- A finite-coordinate dot-product kernel induced by a linear map is convex-concave. -/
theorem isConvexConcave_dotProductKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] (n → 𝕜)) :
    SaddleFunction.IsConvexConcave 𝕜
      (fun u xStar ↦ (A u) ⬝ᵥ xStar) := by
  simpa [SaddleFunction.IsConvexConcave] using
    A.isConvexConcaveOn_dotProductKernel
      (C := Set.univ) (D := Set.univ) convex_univ convex_univ

/-- Finite-coordinate bridge form of Corollary33.0.7: a dot-product kernel induced by a linear
map is both concave-convex and convex-concave. -/
theorem isConcaveConvex_and_isConvexConcave_dotProductKernel
    [PartialOrder 𝕜]
    (A : U →ₗ[𝕜] (n → 𝕜)) :
    SaddleFunction.IsConcaveConvex 𝕜
        (fun u xStar ↦ (A u) ⬝ᵥ xStar) ∧
      SaddleFunction.IsConvexConcave 𝕜
        (fun u xStar ↦ (A u) ⬝ᵥ xStar) :=
  ⟨A.isConcaveConvex_dotProductKernel, A.isConvexConcave_dotProductKernel⟩

end LinearMap

end DotProductBridge
