import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_project.Chap15.Definition_15_67_1
import stacks_project.Chap15.Lemma_15_99_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedInternalHom

/- Domain-style sampling for 15.99.2:
- primary domain: isomorphism criteria for the tensor-right/internal-Hom comparison in `D(R)`,
  propagated along truncation triangles;
- sampled owner declarations:
  `CategoryTheory.derivedInternalHom_tensor_right_comparison`,
  `CategoryTheory.derivedInternalHomTensorRightComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension`,
  `CategoryTheory.HasFiniteTorDimension`,
  `DerivedCategory.TStructure.t.truncLE`;
- best owner abstraction:
  `source-facing`: the textbook isomorphism criterion for the canonical comparison morphism from
    Lemma `15.74.3`, now reduced through the owner-level criterion of Lemma `15.99.1`;
  `core/canonical`: the chosen monoidal-closed owner `H : MonoidalClosed DMod`, the comparison
    morphism `derivedInternalHom_tensor_right_comparison H K L M`, the source-facing notation
    `RHom[H](L, M)`, and the Chapter 15 owners `HasFiniteInjectiveDimension`,
    `HasFiniteTorDimension`, and `X.IsPseudoCoherent`;
  `bridge/view`: the lower truncations `τ_{\le n} K` used to reduce to Lemma `15.99.1`.
- primitive vs. derived:
  the primitive inputs are the owner `H`, the finite-injective-dimension hypotheses on `L` and
  `M`, the finite-tor-dimension hypothesis on `RHom[H](L, M)`, and the pseudo-coherence of the
  lower truncations of `K`; the bounded-below hypothesis needed to invoke Lemma `15.99.1` is
  derived locally from the injective-amplitude witness inside `hL`, so there is no need for an
  additional public bridge declaration here.
-/

/-- Lemma 15.99.2: the tensor-right comparison map
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} K \to
R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)` is an isomorphism when `L` and `M` have finite
injective dimension, `R\mathrm{Hom}_R(L, M)` has finite tor dimension, and every lower truncation
`τ_{\le n} K` is pseudo-coherent. -/
theorem derivedInternalHomTensorRightComparison_hom_isIso_of_finiteInjectiveDimension_of_finiteTorDimension_of_truncLE_isPseudoCoherent
    (H : RHomPkg)
    (K L M : DMod)
    (hL : HasFiniteInjectiveDimension L)
    (hM : HasFiniteInjectiveDimension M)
    (hLM : HasFiniteTorDimension (RHom[H](L, M)))
    (hτK : ∀ n : ℤ, ((t.truncLE n).obj K).IsPseudoCoherent) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := by
  have hLge : ∃ n : ℤ, L.IsGE n := by
    sorry
  sorry

end

end CategoryTheory
