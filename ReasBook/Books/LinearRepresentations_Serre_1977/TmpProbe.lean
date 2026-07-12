import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_3.Index
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2

noncomputable section
open CategoryTheory
open scoped Representation
universe u
namespace Representation

section
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]
local notation "k" => IsLocalRing.ResidueField A

example [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ s : R₀[K'](G) →+ finiteProjectiveGroupAlgebraGrothendieckGroup k G,
      Function.LeftInverse s
        ((finiteRepGrothendieckScalarExtensionHom K K' G).comp
          (projectiveGrothendieckScalarExtensionHom A K)) := by
  letI : Algebra A K' := (algebraMap K K').comp (algebraMap A K) |>.toAlgebra
  haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq' rfl
  letI : HasEnoughRootsOfUnity K' (Monoid.exponent G) :=
    ProjectiveScalarExtensionSplitInjective.hasEnoughRootsOfUnity_extension_local
      (K := K) (L := K') (G := G)
  obtain ⟨s, hs⟩ :=
    projectiveGrothendieckScalarExtensionHom_split_injective (A := A) (K := K') (G := G)
  refine ⟨s, ?_⟩
  intro x
  exact hs x

end
end Representation
