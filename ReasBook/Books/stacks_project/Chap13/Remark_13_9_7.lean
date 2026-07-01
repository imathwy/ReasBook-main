import Mathlib.Algebra.Homology.Factorizations.CM5b
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory
open CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable (K L : CochainComplex C ℤ)

/- Domain-style sampling for Remark 13.9.7:
- primary domain: CM5b factorization of morphisms of cochain complexes, viewed through homotopy
  equivalences of mapping-cone-based factorization objects;
- sampled canonical declarations:
  `HomotopyEquiv`,
  `HomotopyEquiv.homotopyHomInvId`,
  `cm5b.p`,
  `cm5b.homotopyEquiv`;
- source/core/bridge triage:
  `core/canonical`: `HomotopyEquiv`,
  `bridge/view`: `cm5b.homotopyEquiv K L` and its field
    `(cm5b.homotopyEquiv K L).homotopyHomInvId`.

The primitive data are already owned by `HomotopyEquiv`: the two comparison morphisms and the two
homotopies from their composites to the identities. The CM5b construction in mathlib packages the
relevant factorization object and the projection `cm5b.p` into the canonical homotopy equivalence
`cm5b.homotopyEquiv`, so this remark should recall that owner rather than introduce a parallel
chapter-local wrapper for the same homotopy. -/

/- Remark 13.9.7: the elementwise computation of the proof above is the explicit verification that,
for the standard CM5b factorization `mappingCone (𝟙 (cm5b.I K)) ⊞ L`, the projection-section
composite is homotopic to the identity on the factorization object, equivalently
`id - π ≫ s = d h + h d`. This is the canonical owner `cm5b.homotopyEquiv`, whose relevant
component is the field `homotopyHomInvId`. -/
recall cm5b.homotopyEquiv

/- Companion check: the homotopy asserted in the remark is exactly the `homotopyHomInvId` field of
the canonical CM5b homotopy equivalence. -/
#check (cm5b.homotopyEquiv K L).homotopyHomInvId
