import StacksProject_2024.stacks_project.Chap12.Lemma_12_29_1
import StacksProject_2024.stacks_project.Chap17.Lemma_17_6_1
import StacksProject_2024.stacks_project.Chap17.Lemma_17_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat
open scoped ClosedSubsetSectionsWithSupport

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

local instance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  HasSheafify.isRightAdjoint

/- 
Domain-style sampling for Lemma 20.21.1:
- primary domain: adjunctions, preservation of monomorphisms, and preservation of injective
  objects for abelian sheaves on a closed subset;
- sampled owner declarations:
  `Functor.preservesMonomorphisms_of_adjunction`,
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`,
  `Functor.PreservesInjectiveObjects`,
  `closedSubset_pushforwardSectionsWithSupportAdjunction`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical sections-with-
  support functor `𝓗[hZ]`, derived from the adjunction
  `Sheaf.pushforward AddCommGrpCat (X.closedSubsetInclusion Z) ⊣ 𝓗[hZ]`;
- primitive data: the closed subset `Z ⊆ X`, the pullback/pushforward adjunction, and the
  closed-subset pushforward/sections-with-support adjunction;
- derived API: preservation of injective objects by `𝓗[hZ]`, and the objectwise injectivity of
  `(𝓗[hZ]).obj ℐ` for injective `ℐ`.

Source/core/bridge triage:
- `source-facing`: the textbook claim that sections with support in a closed subset send injective
  abelian sheaves to injective abelian sheaves on the closed subset;
- `core/canonical`: `Functor.PreservesInjectiveObjects`;
- `bridge/view`: the specialization below from the closed-subset pushforward adjunction and the
  fact that pushforward preserves monomorphisms as a right adjoint. -/

/-- Helper for Lemma 20.21.1: the closed-subset sections-with-support functor preserves injective
objects because it is right adjoint to the exact pushforward along the closed immersion. -/
private theorem closedSubsetSectionsWithSupport_preservesInjectiveObjects
    (hZ : IsClosed Z) : (𝓗[hZ]).PreservesInjectiveObjects := by
  -- Proof comment: use the closed-immersion adjunction `i_* ⊣ 𝓗_Z` and let the imported
  -- pushforward API supply preservation of monomorphisms for `i_*`.
  let _ : (Sheaf.pushforward AddCommGrpCat.{u} (X.closedSubsetInclusion Z)).PreservesMonomorphisms :=
    by infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (closedSubset_pushforwardSectionsWithSupportAdjunction hZ)

/-- Lemma 20.21.1: if `i : Z ↪ X` is the inclusion of a closed subset and `ℐ` is an injective
abelian sheaf on `X`, then the sheaf `𝓗[hZ](ℐ)`, formalized as `(𝓗[hZ]).obj ℐ`, is an injective
abelian sheaf on `Z`. -/
@[stacks 0A3A]
theorem closedSubsetSectionsWithSupport_injective_of_injective
    (hZ : IsClosed Z) (ℐ : X.Sheaf AddCommGrpCat.{u}) (hℐ : Injective ℐ) :
    Injective ((𝓗[hZ]).obj ℐ) := by
  let _ : (𝓗[hZ]).PreservesInjectiveObjects :=
    closedSubsetSectionsWithSupport_preservesInjectiveObjects hZ
  -- Proof comment: once the functor-level witness is fixed, specialize it to the injective sheaf
  -- `ℐ` instead of re-running adjunction or instance search inside the final step.
  simpa using (𝓗[hZ]).injective_obj_of_injective hℐ

end
