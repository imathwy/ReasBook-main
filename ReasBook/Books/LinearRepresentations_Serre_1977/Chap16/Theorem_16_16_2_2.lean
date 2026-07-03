import Mathlib
import Serre.Chap12.Proposition_12_12_1_3
import Serre.Chap15.Definition_15_15_3_1
import Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import Serre.Chap16.Theorem_16_16_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open scoped Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G

/- Domain-style sampling for Theorem 16-16.2-2:
* primary domain: modular representation theory on Grothendieck groups, combining Serre's
  projective scalar-extension map over a finite extension field with ordinary characters;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckCharacter`,
  `IsValuedInBaseField`;
* best owner abstraction: the existing Chapter `15` and `16` scalar-extension owners on
  Grothendieck groups, namely
  `(finiteRepGrothendieckScalarExtensionHom K K' G).comp
    (projectiveGrothendieckScalarExtensionHom A K)`,
  together with the Chapter `16` character bridge and the Chapter `12` `K`-valuedness predicate
  on class functions;
* source/core/bridge triage:
  source-facing: the image criterion over the finite extension `K' / K`;
  core/canonical: `projectiveGrothendieckScalarExtensionHom A K`,
    `finiteRepGrothendieckScalarExtensionHom K K' G`,
    `finiteRepGrothendieckCharacter K' G`, and `IsValuedInBaseField K`;
  bridge/view: this theorem, which characterizes the range of the canonical composite of those
    scalar-extension owners by a base-field-valuedness condition plus vanishing on `p`-singular
    elements.

Primitive data vs derived API:
* primitive data: the canonical composite
  `(finiteRepGrothendieckScalarExtensionHom K K' G).comp
    (projectiveGrothendieckScalarExtensionHom A K)`;
* derived API: the character-theoretic criterion for membership in its range.
This file should therefore reuse those upstream owners directly and avoid introducing a parallel
public map declaration for their composite.
-/

-- Proof sketch: if `x` lies in the image of the finite-extension scalar-extension map
-- `P_k(G) → R_K'(G)`, then it comes by extension of scalars from a projective class over `K`, so
-- its ordinary character is the scalar extension of a `K`-valued character, so it is
-- `Representation.IsValuedInBaseField K`; Theorem `16-16.2-1` gives vanishing on `p`-singular
-- elements. Conversely, if the character of `x` is `K`-valued and vanishes on `p`-singular
-- elements, descend `x` to a class in `R_K(G)` and apply Theorem `16-16.2-1`, then re-extend
-- scalars to recover `x`.
/-- Theorem 16-16.2-2: for a finite extension `K' / K`, an element of `R_K'(G)` lies in the image
of the projective scalar-extension homomorphism `e : P_k(G) → R_K'(G)` exactly when its ordinary
character is `K`-valued and vanishes on every `p`-singular element of `G`. Here
`k = IsLocalRing.ResidueField A`. -/
theorem
    mem_projectiveScalarExtensionOverExtension_range_iff_valuedInBaseField_zero_on_pSingular
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : R₀[K'](G)) :
    x ∈ ((finiteRepGrothendieckScalarExtensionHom K K' G).comp
      (projectiveGrothendieckScalarExtensionHom A K) : P_k(G) →+ R₀[K'](G)).range ↔
      IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x) ∧
      ∀ g : G, ¬ IsPRegular p g → finiteRepGrothendieckCharacter K' G x g = 0 := sorry

end

end Representation
