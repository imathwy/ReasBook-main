import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.LeftExact
import StacksProject_2024.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.Chap07.Lemma_7_17_6

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace Sheaf

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}

/-- Helper for Lemma 7.41.1: the singleton coproduct desc map built from identity morphisms is an
isomorphism. -/
private theorem singleton_sigma_desc_identity_isIso
    {A : Sheaf J (Type w)} :
    IsIso (Limits.Sigma.desc (fun _ : PUnit ↦ 𝟙 A)) := by
  -- The singleton coproduct injection is a two-sided inverse to the desc of identities.
  refine ⟨⟨Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit, ?_, ?_⟩⟩
  · -- Compare the two endomorphisms of the singleton coproduct after the unique injection.
    apply Limits.Sigma.hom_ext
    intro i
    cases i
    simp [Category.assoc]
  · -- The other composite is exactly the singleton `Sigma.ι_desc` identity.
    simpa using Limits.Sigma.ι_desc (fun _ : PUnit ↦ 𝟙 A) PUnit.unit

/-- Helper for Lemma 7.41.1: for a singleton source family, the associated sigma-desc map is
locally surjective exactly when the unique component map is locally surjective. -/
theorem isLocallySurjective_singleton_sigma_desc_iff
    {A Z : Sheaf J (Type w)} (φ : A ⟶ Z) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun _ : PUnit ↦ φ)) ↔
      Sheaf.IsLocallySurjective φ := by
  -- Read both local-surjectivity statements as epimorphism assertions and compare them through
  -- the singleton coproduct equivalence.
  let e : (∐ fun _ : PUnit ↦ A) ⟶ A := Limits.Sigma.desc (fun _ : PUnit ↦ 𝟙 A)
  letI : IsIso e := singleton_sigma_desc_identity_isIso (J := J) (A := A)
  have hcomp : e ≫ φ = Limits.Sigma.desc (fun _ : PUnit ↦ φ) := by
    -- Check the factorization componentwise on the unique summand.
    apply Limits.Sigma.hom_ext
    intro i
    cases i
    simp [e]
  rw [Sheaf.isLocallySurjective_iff_epi, Sheaf.isLocallySurjective_iff_epi]
  constructor
  · intro hdesc
    -- Rewrite the singleton sigma-desc as an isomorphic source change of `φ`.
    have hcomp_epi : Epi (e ≫ φ) := by
      simpa [hcomp] using hdesc
    exact (epi_comp_iff_of_epi e φ).1 hcomp_epi
  · intro hφ
    -- Compose `φ` with the singleton coproduct equivalence to recover the sigma-desc.
    have hcomp_epi : Epi (e ≫ φ) := (epi_comp_iff_of_epi e φ).2 hφ
    simpa [hcomp] using hcomp_epi

end

end Sheaf

namespace MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : MorphismOfTopoiIn J K)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Surjections onto inverse images lift along a surjective cover in the target topos. -/
def surjectionLiftingAlongInverseImage : Prop :=
  ∀ {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ f⁻¹.obj 𝒢),
    Sheaf.IsLocallySurjective φ →
      ∃ (𝒢' : Sheaf J (Type w)) (π : 𝒢' ⟶ 𝒢),
        Sheaf.IsLocallySurjective π ∧
          ∃ ι : (f⁻¹).obj 𝒢' ⟶ ℱ,
            ι ≫ φ = (f⁻¹).map π

/-- Helper for Lemma 7.41.1: pullbacks of locally surjective morphisms of sheaves of sets are
again locally surjective. -/
theorem sheaf_pullback_snd_isLocallySurjective
    {A B Z : Sheaf J (Type w)} (φ : A ⟶ Z) (q : B ⟶ Z)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Sheaf.IsLocallySurjective (pullback.snd φ q) := by
  -- Route correction: reuse the compiled sigma-desc pullback theorem through a singleton family
  -- instead of reconstructing a pointwise pullback witness in this file.
  have hsingleton :
      Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun _ : PUnit ↦ φ)) := by
    exact (Sheaf.isLocallySurjective_singleton_sigma_desc_iff (J := J) (φ := φ)).2 hφ
  have hpull :
      Sheaf.IsLocallySurjective
        (Limits.Sigma.desc (fun _ : PUnit ↦ pullback.snd φ q)) := by
    simpa using
      CategoryTheory.Sheaf.isLocallySurjective_sigma_desc_pullback_snd
        (J := J) (q := q) (X := fun _ : PUnit ↦ A) (fun _ : PUnit ↦ φ) hsingleton
  exact
    (Sheaf.isLocallySurjective_singleton_sigma_desc_iff
      (J := J) (φ := pullback.snd φ q)).1 hpull

end

end MorphismOfTopoiIn

end CategoryTheory
