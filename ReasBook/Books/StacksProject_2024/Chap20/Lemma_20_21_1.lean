import Mathlib
import StacksProject_2024.Chap12.Lemma_12_29_1
import StacksProject_2024.Chap17.Lemma_17_6_1
import StacksProject_2024.Chap17.Lemma_17_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat
open scoped ClosedSubsetSectionsWithSupport

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

/- 
Domain-style sampling for Lemma 20.21.1:
- primary domain: adjunctions, exact functors, and preservation of injective objects for abelian
  sheaves on a closed subset;
- sampled owner declarations:
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`,
  `Functor.PreservesInjectiveObjects`,
  `closedSubset_pushforwardSectionsWithSupportAdjunction`,
  `closedSubsetAbelianSheafPushforward_exact`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical sections-with-
  support functor `𝓗[hZ]`, derived from the adjunction
  `Sheaf.pushforward AddCommGrpCat (X.closedSubsetInclusion Z) ⊣ 𝓗[hZ]`;
- primitive data: the closed subset `Z ⊆ X` and the closed-subset adjunction/exactness results
  already established upstream;
- derived API: preservation of injective objects by `𝓗[hZ]`, and the objectwise injectivity of
  `(𝓗[hZ]).obj ℐ` for injective `ℐ`.

Source/core/bridge triage:
- `source-facing`: the textbook claim that sections with support in a closed subset send injective
  abelian sheaves to injective abelian sheaves on the closed subset;
- `core/canonical`: `Functor.PreservesInjectiveObjects`;
- `bridge/view`: the specialization below from the closed-subset pushforward adjunction and its
  exactness. -/

instance closedSubsetSectionsWithSupport_preservesInjectiveObjects
    (hZ : IsClosed Z) :
    (𝓗[hZ]).PreservesInjectiveObjects := by
  exact (CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint
    (closedSubset_pushforwardSectionsWithSupportAdjunction hZ)
    (closedSubsetAbelianSheafPushforward_exact hZ) :
      (𝓗[hZ]).PreservesInjectiveObjects)

-- Proof sketch: the closed-subset pushforward functor is exact by Lemma `17.6.1`, and
-- `𝓗[hZ]` is its right adjoint by Lemma `17.6.3`. Apply
-- Homology, Lemma `12.29.1`, to conclude that this right adjoint preserves injective objects.
/-- Lemma 20.21.1: if `i : Z → X` is the inclusion of a closed subset and `\mathcal I` is an
injective abelian sheaf on `X`, then the sheaf `\mathcal H_Z(\mathcal I)` of sections with support
in `Z`, formalized as `(𝓗[hZ]).obj ℐ`, is an injective
abelian sheaf on `Z`. -/
theorem closedSubsetSectionsWithSupport_injective_of_injective
    (hZ : IsClosed Z) (ℐ : X.Sheaf AddCommGrpCat.{u}) (hℐ : Injective ℐ) :
    Injective ((𝓗[hZ]).obj ℐ) :=
  (𝓗[hZ]).injective_obj_of_injective hℐ

end
