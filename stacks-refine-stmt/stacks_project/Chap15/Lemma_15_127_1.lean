import stacks_project.Chap15.Lemma_15_59_15
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.127.1:
- primary domain: the symmetric monoidal structure on `D(R)` together with the source-facing
  derived tensor product notation `⊗[R]^L`;
- sampled owner declarations:
  the anonymous `MonoidalCategory DMod` and `SymmetricCategory DMod` instances from Lemma
  `15.59.14`,
  `derivedCategory_tensorObj_iso_derivedTensorProduct`,
  `derivedTensorProduct_associator`,
  `derivedTensorProduct_comm`;
- best owner abstraction:
  `source-facing`: the tensor surface `⊗[R]^L` and its associativity/commutativity constraints;
  `core/canonical`: the ambient `MonoidalCategory DMod` and `SymmetricCategory DMod` instances;
  `bridge/view`: the comparison isomorphism identifying the owner tensor `K ⊗ L` with
  `K ⊗[R]^L L`;
- primitive vs. derived:
  the monoidal and symmetric structures on `D(R)` are the owner data; the comparison with
  `⊗[R]^L` and the displayed associator/commutor are derived API transported from that owner;
- layer: this file is a recall-only `core/canonical` item, so its main entry should recall the
  ambient monoidal and symmetric owners on `D(R)`, with the source-facing associator and
  commutor kept as companions.
-/

/- Lemma 15.127.1: the derived category `D(R)` carries the canonical monoidal structure obtained
by localizing tensor product on complexes. -/
#synth MonoidalCategory DMod

/- The same localized tensor product makes `D(R)` into a symmetric monoidal category. -/
#synth SymmetricCategory DMod

/- The owner tensor on `D(R)` is identified with the source-facing derived tensor product
notation `⊗[R]^L`. -/
section

variable [∀ (K₁ K₂ : CochainComplex (ModuleCat R) ℤ),
  CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat R))]

recall derivedCategory_tensorObj_iso_derivedTensorProduct
    (K L : DMod) :
    K ⊗ L ≅ K ⊗[R]^L L

/- The associativity constraint for `⊗[R]^L` is transported from the ambient monoidal owner on
`D(R)`. -/
recall derivedTensorProduct_associator
    (K L M : DMod) :
    ((K ⊗[R]^L L) ⊗[R]^L M) ≅ (K ⊗[R]^L (L ⊗[R]^L M))

end

end

section

/- The commutativity constraint for `⊗[R]^L` is transported from the ambient symmetric-monoidal
owner on `D(R)`. -/
#check derivedTensorProduct_comm

end

end CategoryTheory
