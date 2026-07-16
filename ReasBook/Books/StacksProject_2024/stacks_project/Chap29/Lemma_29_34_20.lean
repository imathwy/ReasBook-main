import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_139_4
import StacksProject_2024.stacks_project.Chap29.Lemma_29_34_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: the pointwise smooth owner and affine-open restriction surface were verified
-- from the local project files `Lemma_29_34_11` and `Lemma_10_139_4`.

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)

abbrev affineSectionRingMap
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : S.Opens)) :
    Γ(S, U) →+* Γ(X, V) :=
  (f.appLE (U : S.Opens) (V : X.Opens) e).hom

abbrev affineSectionRetraction
    {X S : Scheme.{u}} (σ : S ⟶ X) (U : S.affineOpens) (V : X.affineOpens)
    (eσ : (U : S.Opens) ≤ σ ⁻¹ᵁ (V : X.Opens)) :
    Γ(X, V) →+* Γ(S, U) :=
  (σ.appLE (V : X.Opens) (U : S.Opens) eσ).hom

/-- The affine-ring retraction property attached to a section on affine neighborhoods. -/
def AffineSectionRetractionProperty
    {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (U : S.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : S.Opens))
    (eσ : (U : S.Opens) ≤ σ ⁻¹ᵁ (V : X.Opens)) : Prop :=
  Function.LeftInverse (affineSectionRetraction σ U V eσ) (affineSectionRingMap f U V e)

/-- The conormal freeness conclusion of Lemma 29.34.20 on affine neighborhoods. -/
def AffineSectionCotangentFree
    {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (U : S.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : S.Opens))
    (eσ : (U : S.Opens) ≤ σ ⁻¹ᵁ (V : X.Opens)) : Prop :=
  let A := Γ(S, U)
  let B := Γ(X, V)
  let _ : Algebra A B := (affineSectionRingMap f U V e).toAlgebra
  Module.Free A (RingHom.ker (affineSectionRetraction σ U V eσ)).Cotangent

/-- The formal-power-series completion conclusion of Lemma 29.34.20 on affine neighborhoods. -/
def AffineSectionCompletionPowerSeries
    {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (U : S.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : S.Opens))
    (eσ : (U : S.Opens) ≤ σ ⁻¹ᵁ (V : X.Opens)) : Prop :=
  let A := Γ(S, U)
  let B := Γ(X, V)
  let _ : Algebra A B := (affineSectionRingMap f U V e).toAlgebra
  ∃ d : ℕ,
    Nonempty
      ((AdicCompletion (RingHom.ker (affineSectionRetraction σ U V eσ)) B) ≃ₐ[A]
        MvPowerSeries (Fin d) A)

/-- Lemma 29.34.20: if `σ : S ⟶ X` is a section of `f : X ⟶ S` and `f` is smooth at the point
`x = σ s`, then after shrinking to affine neighborhoods `U` of `s` and `V` of `x` with
`f(V) ⊆ U` and `σ(U) ⊆ V`, the restricted morphism `V.toScheme ⟶ U.toScheme` is smooth and the
induced map on affine coordinate rings is a retraction. This is the source-facing affine
neighborhood owner underlying the conormal and completion consequences from Chapter 10. -/
@[stacks 05D9]
theorem exists_affineOpenNeighborhood_restrict_smooth_with_section
    [LocallyOfFinitePresentation f] (hσ : σ ≫ f = 𝟙 S)
    (s : S) (hsmooth : f.SmoothAt (σ s)) :
    ∃ U : S.affineOpens, s ∈ (U : S.Opens) ∧
      ∃ V : X.affineOpens, σ s ∈ (V : X.Opens) ∧
        ∃ e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : S.Opens),
          ∃ eσ : (U : S.Opens) ≤ σ ⁻¹ᵁ (V : X.Opens),
            Smooth (f.resLE (U : S.Opens) (V : X.Opens) e) ∧
              AffineSectionRetractionProperty f σ U V e eσ := sorry

/-- Lemma 29.34.20: on affine neighborhoods around a smooth section point, the restricted section
ring map has free conormal module and its adic completion is a finite-variable formal power series
ring. The theorem is stated through the Chapter 10 smooth-section API attached to the restricted
`appTop` maps. -/
@[stacks 05D9]
theorem exists_affineOpenNeighborhood_section_cotangent_free_and_completion
    [LocallyOfFinitePresentation f] (hσ : σ ≫ f = 𝟙 S)
    (s : S) (hsmooth : f.SmoothAt (σ s)) :
    ∃ U : S.affineOpens, s ∈ (U : S.Opens) ∧
      ∃ V : X.affineOpens, σ s ∈ (V : X.Opens) ∧
        ∃ e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : S.Opens),
          ∃ eσ : (U : S.Opens) ≤ σ ⁻¹ᵁ (V : X.Opens),
            Smooth (f.resLE (U : S.Opens) (V : X.Opens) e) ∧
              AffineSectionRetractionProperty f σ U V e eσ ∧
              AffineSectionCotangentFree f σ U V e eσ ∧
              AffineSectionCompletionPowerSeries f σ U V e eσ := sorry

/-- Lemma 29.34.20, restated using the smooth locus owner from mathlib. -/
@[stacks 05D9]
theorem exists_affineOpenNeighborhood_section_cotangent_free_and_completion_of_mem_smoothLocus
    [LocallyOfFinitePresentation f] (hσ : σ ≫ f = 𝟙 S)
    (s : S) (hsmooth : σ s ∈ f.smoothLocus) :
    ∃ U : S.affineOpens, s ∈ (U : S.Opens) ∧
      ∃ V : X.affineOpens, σ s ∈ (V : X.Opens) ∧
        ∃ e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : S.Opens),
          ∃ eσ : (U : S.Opens) ≤ σ ⁻¹ᵁ (V : X.Opens),
            Smooth (f.resLE (U : S.Opens) (V : X.Opens) e) ∧
              AffineSectionRetractionProperty f σ U V e eσ ∧
              AffineSectionCotangentFree f σ U V e eσ ∧
              AffineSectionCompletionPowerSeries f σ U V e eσ := by
  rw [← f.smoothAt_iff_mem_smoothLocus (σ s)] at hsmooth
  exact exists_affineOpenNeighborhood_section_cotangent_free_and_completion f σ hσ s hsmooth

end AlgebraicGeometry
