import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
* primary domain: Pontryagin duality for finite abelian groups via additive characters.
* sampled owner declarations in this domain:
  `AddChar.doubleDualEmb`,
  `AddChar.doubleDualEquiv`,
  `AddChar.doubleDualEmb_injective`,
  `AddChar.card_eq`.
* best owner abstraction: the existing `AddChar` double-dual API from mathlib, already reused by
  the chapter-level file `LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_1_5`.

Primitive data versus derived API:
* primitive owner data: the canonical evaluation morphism into the double dual.
* derived API: the finite-group double-dual equivalence, its injectivity consequence, and the
  cardinality equality for the dual group.

Source/core/bridge triage:
* `source-facing`: Exercise `3-3.1-5` as a recall of the canonical double-dual statements for
  finite abelian groups.
* `core/canonical`: the `AddChar` owner declarations listed above, as surfaced in
  `LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_1_5`.
* `bridge/view`: this item file is only a thin recall layer reusing the chapter-level owner file
  rather than restating the same recalls from scratch.
-/

/- The evaluation map `x ↦ (χ ↦ χ x)` into the dual of the dual is the canonical double-dual
embedding. -/
recall AddChar.doubleDualEmb

/- Exercise 3-3.1-5: using Theorem 3-3.1-1 to identify the irreducible complex characters of the
finite abelian group `G` with the complex characters `AddChar (Additive G) ℂ`, Pontryagin duality
gives the canonical double-dual isomorphism `Additive G ≃+ AddChar (AddChar (Additive G) ℂ) ℂ`. -/
recall AddChar.doubleDualEquiv

/- The canonical evaluation homomorphism into the double dual is injective. -/
recall AddChar.doubleDualEmb_injective

/- The dual group of a finite abelian group has the same cardinality as the group itself. -/
recall AddChar.card_eq
