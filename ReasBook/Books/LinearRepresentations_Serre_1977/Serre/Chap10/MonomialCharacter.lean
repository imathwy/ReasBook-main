import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

open scoped Representation SubgroupInduction

section

variable {G : Type} [Group G] [Finite G]

/- Domain-style sampling for this owner:
* primary domain: ordinary character theory of finite groups, with monomiality expressed by
  induction from a one-dimensional subgroup character;
* relevant owner declarations inspected in this domain:
  `Representation.IsMonomial`,
  `Representation.character`,
  `MonoidHom.toRepresentation`,
  the scoped induction notation `Ind[H](...)`;
* best owner abstraction: monomiality of an ordinary complex character is a property of the
  character itself, so the public owner lives at the character level rather than as an ad hoc
  existential surface in downstream files;
* source/core/bridge triage:
  - source-facing: a character `χ : G → ℂ` is induced from a linear character of a subgroup;
  - core/canonical: `Representation.IsMonomialCharacter`;
  - bridge/view: the representation-level predicate `Representation.IsMonomial` maps to this owner
    in the heavier Chapter 10 theorem file.

Primitive data versus derived API:
* primitive data: a subgroup `H ≤ G` and a linear character `α : H →* ℂˣ`;
* derived API: the proposition that the ambient character `χ` is monomial.
-/

/-- A complex character of a finite group is monomial if it is induced from a one-dimensional
complex representation of a subgroup. -/
def IsMonomialCharacter (χ : G → ℂ) : Prop :=
  ∃ H : Subgroup G, ∃ α : H →* ℂˣ, Ind[H](α.toRepresentation.character) = χ

/-- The character induced from a one-dimensional complex representation of a subgroup is
monomial. -/
theorem isMonomialCharacter_of_induced (H : Subgroup G) (α : H →* ℂˣ) :
    IsMonomialCharacter (Ind[H](α.toRepresentation.character)) :=
  ⟨H, α, rfl⟩

end

end Representation
