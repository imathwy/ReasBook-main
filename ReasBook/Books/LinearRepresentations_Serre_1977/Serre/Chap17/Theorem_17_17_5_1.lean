import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 17-17.5-1: Serre's image criterion for
`e : P_k(G) → R_K(G)` is the existing range theorem
`Representation.mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular`.

Domain-style sampling for this item:
* primary domain: modular representation theory of finite groups, at the Grothendieck-group and
  ordinary-character interface for Serre's projective scalar-extension map;
* relevant owner declarations inspected in this domain:
  `Representation.projectiveGrothendieckScalarExtensionHom`,
  `Representation.finiteRepGrothendieckCharacter`,
  `Representation.projectiveGrothendieckScalarExtensionHom_split_injective`,
  `Representation.mem_projectiveGrothendieckScalarExtension_range_iff_
    character_eq_zero_on_pSingular`.

Primitive data vs derived API:
* primitive data: the chapter owner map `projectiveGrothendieckScalarExtensionHom`;
* derived API: the range criterion expressed by vanishing of the ordinary Grothendieck character on
  `p`-singular elements.

Source/core/bridge triage:
* source-facing: Theorem `17-17.5-1`, which restates the image criterion for Serre's map
  `e : P_k(G) → R_K(G)`;
* core/canonical: the Chapter `16` owner theorem
  `Representation.mem_projectiveGrothendieckScalarExtension_range_iff_
    character_eq_zero_on_pSingular`;
* bridge/view: this file contributes no new owner or wrapper, so it should remain a direct recall
  of that canonical theorem rather than a parallel local alias. -/
recall
  Representation.mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
