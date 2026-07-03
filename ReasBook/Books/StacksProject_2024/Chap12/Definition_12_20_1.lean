import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Domain-style sampling for Definition 12.20.1:
- primary domain: spectral sequences in an abelian category, specialized here to one-object page
  complexes;
- sampled core/canonical declarations:
  `CategoryTheory.SpectralSequence`,
  `CategoryTheory.SpectralSequence.Hom`,
  `SpectralSequence.pageFunctor`,
  `SpectralSequence.pageHomologyNatIso`,
  `ExactCouple.associatedSpectralSequence`;
- best owner abstraction: the category
  `SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1`;
- primitive data:
  object level: the pages `E.page r` and the homology-to-next-page isomorphisms
    `E.iso r r' PUnit.unit`;
  morphism level: the pagewise maps of `CategoryTheory.SpectralSequence.Hom` commuting with those
    homology identifications;
- derived API: the textbook page objects and differentials obtained by evaluating each page at
  `PUnit.unit`, the transition `H(E_r) ≅ E_{r+1}` recovered from
  `SpectralSequence.pageHomologyNatIso`, and the arrow notation supplied by the canonical category
  structure;
- source/core/bridge triage:
  `source-facing`: a spectral sequence whose pages are one-object homological complexes, together
    with morphisms of such spectral sequences;
  `core/canonical`: `SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1`;
  `bridge/view`: evaluation at `PUnit.unit` and the recalled page/homology functorial API.

No local wrapper is needed here: the textbook definition is exactly this specialization of the
mathlib owner object. -/
/- Definition 12.20.1 is a core/canonical recall item in the spectral-sequence domain: a spectral
sequence in an abelian category with one-object pages is exactly the owner type
`SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1`, and a morphism of such spectral
sequences is exactly the owner structure `CategoryTheory.SpectralSequence.Hom`. -/
#check (SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1)

/- Companion recall: the canonical morphism owner for these spectral sequences is the pagewise
homological-complex map structure `CategoryTheory.SpectralSequence.Hom`. -/
recall CategoryTheory.SpectralSequence.Hom

variable (E E' : SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1)

/- Companion recall: these objects already form the canonical category whose arrows are the
recalled morphisms above. -/
#check (inferInstance : Category (SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1))

/- Companion recall: the textbook morphisms are therefore the ordinary arrows `E ⟶ E'` in that
canonical category. -/
#check (E ⟶ E')

/- Companion recall: the page family is accessed through the canonical owner functor. -/
recall SpectralSequence.pageFunctor

/- Companion recall: the identification `H(E_r) ≅ E_{r+1}` is the canonical owner natural
isomorphism; specializing at `PUnit.unit` recovers the textbook transition. -/
recall SpectralSequence.pageHomologyNatIso

end CategoryTheory
