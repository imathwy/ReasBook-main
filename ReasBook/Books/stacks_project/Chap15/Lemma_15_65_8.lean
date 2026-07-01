import Mathlib
import stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ObjectProperty.IsStableUnderRetracts

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.8:
- primary domain: pseudo-coherence as an object property on `D(R)`, together with the generic
  retract/direct-summand API for additive categories;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the `core/canonical` layer is the object property
  `fun K : DMod ↦ K.IsMPseudoCoherent m` and its pseudo-coherent analogue; the source-facing
  biproduct statements are thin `bridge/view` specializations of the generic direct-summand API;
- primitive vs. derived:
  primitive data are the owner predicates `K.IsMPseudoCoherent m` and `K.IsPseudoCoherent`;
  derived API is retract stability and the left/right biproduct consequences.
-/

/-- `m`-pseudo-coherent objects of `D(R)` are stable under retracts/direct summands. -/
-- Proof sketch: if `K` is a retract of `L`, then `L ≅ K ⊞ K'` for some complement `K'`. Apply
-- the biproduct argument from the Stacks proof, using the distinguished triangle attached to the
-- projection `K ⊞ K' ⟶ K` together with Lemmas `15.65.2` and `15.65.7`.
instance isMPseudoCoherent_isStableUnderRetracts (m : ℤ) :
    ObjectProperty.IsStableUnderRetracts (fun K : DMod ↦ K.IsMPseudoCoherent m) where
  of_retract h hK := by
    sorry

/-- Pseudo-coherent objects of `D(R)` are stable under retracts/direct summands. -/
-- Proof sketch: combine Lemma `15.65.5`, which characterizes pseudo-coherence by
-- `m`-pseudo-coherence for every `m`, with the retract-stability instance above applied degreewise.
instance isPseudoCoherent_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (fun K : DMod ↦ K.IsPseudoCoherent) where
  of_retract h hK := by
    sorry

/-- Lemma 15.65.8 (1): if `K ⊞ L` is `m`-pseudo-coherent in `D(R)`, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_left_of_biprod
    (K L : DMod) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m :=
  of_biprod_left (fun X : DMod ↦ X.IsMPseudoCoherent m) hKL

/-- Lemma 15.65.8 (2): if `K ⊞ L` is `m`-pseudo-coherent in `D(R)`, then `L` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_right_of_biprod
    (K L : DMod) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m :=
  of_biprod_right (fun X : DMod ↦ X.IsMPseudoCoherent m) hKL

/-- Lemma 15.65.8 (3): if `K ⊞ L` is pseudo-coherent in `D(R)`, then `K` is pseudo-coherent. -/
theorem isPseudoCoherent_left_of_biprod
    (K L : DMod)
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent :=
  of_biprod_left (fun X : DMod ↦ X.IsPseudoCoherent) hKL

/-- Lemma 15.65.8 (4): if `K ⊞ L` is pseudo-coherent in `D(R)`, then `L` is pseudo-coherent. -/
theorem isPseudoCoherent_right_of_biprod
    (K L : DMod)
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    L.IsPseudoCoherent :=
  of_biprod_right (fun X : DMod ↦ X.IsPseudoCoherent) hKL

end

end CategoryTheory
