import StacksProject_2024.Chap22.Definition_22_26_3
import StacksProject_2024.Chap22.PropertyI

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory
open scoped ZeroObject

noncomputable section

universe u v w

namespace DGModuleContext

section

variable {R : Type u} [CommRing R]
variable (𝒜 : DGModuleContext.{v, w})
variable [DifferentialGradedCategory R 𝒜.moduleCat]
variable [Limits.HasZeroObject 𝒜.moduleCat]
variable [Limits.HasZeroMorphisms (K R 𝒜.moduleCat)]

local notation "Kdg" => K R 𝒜.moduleCat

-- This file keeps the Chapter 22 source-facing property `(I)` hypothesis explicit. In this
-- generic dg-module context acyclicity is still expressed by the quasi-isomorphism `0 ⟶ N`,
-- rather than by a separate chapter owner.

/-- Lemma 22.21.2: if `I` is a differential graded module with property `(I)`, then every
morphism from an acyclic differential graded module `N` to `I` in the homotopy category
`K(Mod_(A,d))` is zero. Here acyclicity is represented by the zero-to-`N` quasi-isomorphism in
the ambient differential graded module context. -/
@[stacks 09KS]
theorem homotopyCategoryHom_eq_zero_of_acyclic_of_hasPropertyI
    {N I : 𝒜.moduleCat}
    (hI : HasPropertyI 𝒜 I)
    (hN : 𝒜.quasiIso (0 : (0 : 𝒜.moduleCat) ⟶ N))
    (f : (⟨N⟩ : Kdg) ⟶ (⟨I⟩ : Kdg)) :
    f = 0 := sorry

/-- Under property `(I)`, morphisms in `K(Mod_(A,d))` from an acyclic differential graded module
to `I` form a subsingleton. This companion instance lets downstream arguments use typeclass
inference for uniqueness of such morphisms. -/
instance instSubsingletonHomOfAcyclicOfHasPropertyI
    {N I : 𝒜.moduleCat}
    [hI : Fact (HasPropertyI 𝒜 I)]
    [hN : Fact (𝒜.quasiIso (0 : (0 : 𝒜.moduleCat) ⟶ N))] :
    Subsingleton ((⟨N⟩ : Kdg) ⟶ (⟨I⟩ : Kdg)) where
  allEq f g := by
    rw [homotopyCategoryHom_eq_zero_of_acyclic_of_hasPropertyI 𝒜 hI.1 hN.1 f,
      homotopyCategoryHom_eq_zero_of_acyclic_of_hasPropertyI 𝒜 hI.1 hN.1 g]

end

end DGModuleContext
