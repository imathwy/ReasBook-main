import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped Representation

universe u

namespace Representation

section ProjectiveGrothendieckGroup

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/- Domain-style sampling:
* Primary domain: Grothendieck groups of finite projective group-algebra modules and their
  classification up to isomorphism.
* Relevant owner-level declarations inspected in this domain:
  `FiniteProjectiveGroupAlgebraModule`,
  `finiteProjectiveGroupAlgebraGrothendieckClass`,
  `finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso`, and
  `finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv`.
* Core/canonical owner abstraction: `FiniteProjectiveGroupAlgebraModule k G`.
* Primitive data: objects of the canonical owner category.
* Derived API: their classes in `P₀[k](G)` and the linear/representation bridge maps.
Corollary 14-14.3-4 is exactly the owner-level classification statement, so the file reuses the
canonical owner theorem directly rather than keeping a separate `toRep`-bridge duplicate. -/

/- Corollary 14-14.3-4 is the field specialization of the canonical owner theorem
`finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso`; the file records that
specialization directly rather than introducing a duplicate local theorem. -/
#check
  (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso :
    ∀ P Q : FiniteProjectiveGroupAlgebraModule k G, [P]ₚ₀ = [Q]ₚ₀ ↔ Nonempty (P ≅ Q))

end ProjectiveGrothendieckGroup

end Representation
