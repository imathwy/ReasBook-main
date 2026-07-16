import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_6
import StacksProject_2024.stacks_project.Chap20.Remark_20_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling:
- primary domain: chosen injective-resolution comparison squares for derived pushforward on ringed
  spaces;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `CochainComplex.InjectiveResolution`,
  `comparisonTop`;
-- source/core/bridge triage:
  `source-facing`: the specific square from Remark 20.14.2 with top edge induced by `φ` and `I.ι`,
    vertical edges `J.ι` and `J'.ι`, and a bottom edge `β` whose existence makes the square
    commute;
  `core/canonical`: `CategoryTheory.CommSq`;
  `bridge/view`: `comparisonTop`, the canonical project name for that explicit top horizontal map.
- primitive data: `φ`, `I`, `J`, `J'`, and the termwise-monomorphism hypothesis on `J.ι`;
- derived API: the existence of a bottom comparison morphism `β` making the chosen-resolution
  square commute.

This item is therefore a source-facing specialization of the canonical owner `CommSq`, reusing the
project bridge `comparisonTop` from `Remark_20_14_2` and the Chapter 13 strict lifting theorem
rather than restating the square as a vacuous type-formation check.
-/

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable (𝒢 : RingedSpace.Modules Y) (ℱ : RingedSpace.Modules X)
variable (φ : 𝒢 ⟶ (f _*).obj ℱ)

local notation "CpxY" => CochainComplex (RingedSpace.Modules Y) ℤ

variable (I : CochainComplex.InjectiveResolution
  ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ))
variable (J : CochainComplex.InjectiveResolution
  ((CochainComplex.singleFunctor (RingedSpace.Modules Y) 0).obj 𝒢))
variable (J' : CochainComplex.InjectiveResolution
  (((f _*).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (I : CochainComplex (RingedSpace.Modules X) ℤ)))

/-- 20.14.2.1: if the chosen injective resolution `J` of `𝒢[0]` has termwise
monomorphic augmentation, then there exists a comparison morphism `β : J ⟶ J'` making the
chosen-resolution square from Remark 20.14.2 commute. -/
@[stacks 01FC]
theorem exists_comparisonTop_commSq
    (hJmono : ∀ n : ℤ, Mono (J.ι.f n)) :
    ∃ β,
      CommSq (comparisonTop f 𝒢 ℱ φ I) J.ι J'.ι β := by
  -- Factor the chosen top map through `J.ι` using the strict lifting theorem.
  obtain ⟨β, hβ⟩ :
      ∃ β : (J : CpxY) ⟶ (J' : CpxY),
        J.ι ≫ β = comparisonTop f 𝒢 ℱ φ I ≫ J'.ι :=
    CochainComplex.exists_strict_lift_to_boundedBelow_injective_of_termwiseMono
      (α := J.ι)
      (I := (J' : CochainComplex.InjectivePlus (RingedSpace.Modules Y)))
      (γ := comparisonTop f 𝒢 ℱ φ I ≫ J'.ι)
      hJmono
  exact ⟨β, CommSq.mk hβ.symm⟩

/-- The comparison morphism from 20.14.2.1 can be chosen so that the top edge factors through the
augmentation maps exactly. -/
theorem exists_comparisonTop_fac
    (hJmono : ∀ n : ℤ, Mono (J.ι.f n)) :
    ∃ β,
      comparisonTop f 𝒢 ℱ φ I ≫ J'.ι = J.ι ≫ β := by
  -- Read off the commuting equation from the square witness.
  obtain ⟨β, hsq⟩ := exists_comparisonTop_commSq
    (f := f) (𝒢 := 𝒢) (ℱ := ℱ) (φ := φ) (I := I) (J := J) (J' := J') hJmono
  exact ⟨β, hsq.w⟩

end

end AlgebraicGeometry.RingedSpace
