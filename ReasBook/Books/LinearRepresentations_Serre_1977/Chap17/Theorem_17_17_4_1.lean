import Serre.Chap16.Theorem_16_16_1_5

-- Declarations for this item will be appended below by the statement pipeline.

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
