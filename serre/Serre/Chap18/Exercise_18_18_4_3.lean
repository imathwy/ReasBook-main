import Serre.Chap18.Theorem_18_18_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for this item:
* primary domain: modular representation theory of finite groups, specifically the interaction
  between Serre's `x ↦ x'` operation, the decomposition homomorphism
  `d : R₀[K](G) → R₀[k](G)`, and its additive sections.
* relevant owner declarations inspected in this domain:
  `Representation.virtualModularCharacter`,
  `Representation.pRegularComponentVirtualCharacter`,
  `Representation.finiteRepGrothendieckCharacter`,
  `Representation.exists_decompositionHom_section_of_pRegularComponent_virtualModularCharacter`.
* best owner abstraction: the section statement already belongs to the upstream theorem
  `Representation.exists_decompositionHom_section_of_pRegularComponent_virtualModularCharacter`;
  this exercise does not define a new object, map, or property.
* primitive data vs. derived API:
  the primitive data are already carried upstream by `decompositionHom`,
  `finiteRepGrothendieckCharacter`, and the source-facing `x ↦ x'` bridge;
  the present exercise contributes only the proof-note observation that the same section theorem
  holds without any largeness hypothesis on `K`.

Source/core/bridge triage:
* source-facing: Exercise `18-18.4-3` is a proof note about the existing section statement.
* core/canonical: the owner theorem is
  `Representation.exists_decompositionHom_section_of_pRegularComponent_virtualModularCharacter`.
* bridge/view: Exercise `18-18.4-2` provides an alternative route through the power operation,
  but no additional public owner.

This item should therefore stay as a direct recall of the canonical theorem rather than a
duplicate wrapper declaration. -/
recall Representation.exists_decompositionHom_section_of_pRegularComponent_virtualModularCharacter
