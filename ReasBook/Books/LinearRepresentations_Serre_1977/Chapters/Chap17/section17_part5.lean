import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_17_17_4_1 (from Chap17) -/
open scoped Representation

namespace Representation

/- Domain-style sampling for Theorem 17-17.4-1:
* primary domain: modular representation theory of finite groups, centered on the Cartan
  homomorphism and its cokernel.
* inspected owner declarations in this domain:
  `cartanHom`,
  `cartanCokernel`,
  `cartanHom_surjective_on_p_part_multiples`,
  `cartanHom_cokernel_annihilated_by_p_part`.
* best owner abstraction: the Cartan owner map `cartanHom k G` together with its derived quotient
  owner `cartanCokernel k G`.
* source/core/bridge triage:
  source-facing: Theorem `17-17.4-1` is the quotient-level annihilation statement for the Cartan
    cokernel;
  core/canonical: the theorem owner is already the Chapter `16` declaration
    `cartanHom_cokernel_annihilated_by_p_part`;
  bridge/view: none.

Primitive data belongs to the Chapter `16` Cartan owners, so this Chapter `17` file should be a
direct recall of the existing quotient theorem rather than a second local proof-shaped copy.
-/
recall cartanHom_cokernel_annihilated_by_p_part

end Representation

/-! ### Theorem_17_17_5_1 (from Chap17) -/
/- Domain-style sampling for this item:
* primary domain: modular representation theory of finite groups, at the Grothendieck-group and
  ordinary-character interface for LinearRepresentations_Serre_1977's projective scalar-extension map;
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
* source-facing: Theorem `17-17.5-1`, which restates the image criterion for LinearRepresentations_Serre_1977's map
  `e : P_k(G) → R_K(G)`;
* core/canonical: the Chapter `16` owner theorem
  `Representation.mem_projectiveGrothendieckScalarExtension_range_iff_
    character_eq_zero_on_pSingular`;
* bridge/view: this file contributes no new owner or wrapper, so it should remain a direct recall
  of that canonical theorem rather than a parallel local alias. -/
recall
  Representation.mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
