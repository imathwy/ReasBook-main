import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_12
import StacksProject_2024.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R' R : Type u} [CommRing R'] [CommRing R] [Algebra R' R]

local notation "DModRPrime" => DerivedCategory (ModuleCat R')

/- Domain-style sampling for Lemma 15.76.4:
- primary domain: derived scalar extension on module derived categories and reflection of
  pseudo-coherence across nilpotent thickenings;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebra_isPseudoCoherent`,
  `exists_boundedAbove_projective_representative_lifting_mod_nilpotent`,
  `DerivedCategory.IsPseudoCoherent`;
- best owner abstraction: the core/canonical owner is the derived scalar-extension functor
  `derivedTensorWithAlgebra R' R : D(R') ⥤ D(R)`, used on objects through the notation
  `K' ⊗[R']^L[R]`;
- primitive vs. derived:
  primitive data are the surjectivity and nilpotence hypotheses on `R' → R` and the object
  `K' : D(R')`;
  the pseudo-coherence equivalence is derived API over the existing owner and predicate;
- source/core/bridge triage:
  `source-facing`: pseudo-coherence is equivalent before and after base change along a nilpotent
  surjection;
  `core/canonical`: `derivedTensorWithAlgebra` and `DerivedCategory.IsPseudoCoherent`;
  `bridge/view`: the notation `K' ⊗[R']^L[R]` for applying the owner functor to `K'`.
- layer: this theorem is source-facing over canonical owners, so the public statement should use
  the existing notation layer rather than a raw functor application term. -/

-- Proof sketch: the implication `K'.IsPseudoCoherent → (K' ⊗[R']^L[R]).IsPseudoCoherent` is the
-- canonical preservation theorem `derivedTensorWithAlgebra_isPseudoCoherent` from Lemma
-- `15.65.12`. For the converse, choose a bounded-above finite-free representative of the base
-- change, lift it through Lemma `15.76.3` to a bounded-above projective representative over `R'`,
-- and then use Nakayama along the surjection with nilpotent kernel to show the lifted terms are
-- finite free.
/-- Lemma 15.76.4: for a surjective ring map `R' → R` with nilpotent kernel, an object `K'` of
`D(R')` is pseudo-coherent if and only if its derived base change
`K' \otimes_{R'}^{\mathbf L} R` is pseudo-coherent in `D(R)`. -/
@[stacks 0H76]
theorem isPseudoCoherent_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (K' : DModRPrime) :
    (K' ⊗[R']^L[R]).IsPseudoCoherent ↔
      K'.IsPseudoCoherent := by
  constructor
  · intro hK
    sorry
  · intro hK
    simpa using derivedTensorWithAlgebra_isPseudoCoherent K' hK

end

end CategoryTheory
