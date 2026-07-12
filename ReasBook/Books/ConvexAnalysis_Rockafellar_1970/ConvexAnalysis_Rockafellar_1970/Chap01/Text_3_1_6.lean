import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.6 records the basic algebraic identities for pointwise addition of
  sets and for pointwise scalar multiplication of sets.
- `core/canonical`: the owner abstractions are the pointwise additive semigroup/commutative
  semigroup structures on sets, the pointwise scalar-tower owner on sets for iterated scaling, and
  the pointwise distributive scalar action on sets.
- `bridge/view`: the textbook equalities are exactly the generic algebraic laws `add_comm`,
  `add_assoc`, `smul_assoc`, and `smul_add` read through the owner declarations
  `Set.addCommSemigroup`, `Set.addSemigroup`, `Set.isScalarTower`, and
  `Set.distribSMulSet`.
- Primitive data vs derived API: the primitive data are just the underlying sets and scalars; the
  displayed equalities are derived consequences of the owner structures and should reuse those
  owners directly.
- Domain-style sampling: this item aligns with `Set.addCommSemigroup`, `Set.addSemigroup`,
  `Set.isScalarTower`, and `Set.distribSMulSet`.
- Layer target: `core/canonical`; each clause is exact owner reuse, so the public surface keeps
  direct `recall` of the pointwise-set owner declarations.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the codomain at generic `Set` owners; the identities are pure
  pointwise-set algebra and do not need concrete codomains like `ℝ` or `EReal`.
- Scalar/ambient-structure check: keep only the weak canonical layers already used by the owners:
  `AddSemigroup`/`AddCommSemigroup`, `SMul`/`IsScalarTower`, and `DistribSMul` with
  `AddZeroClass`.
- Owner check: keep intrinsic pointwise owners `Set.addCommSemigroup`, `Set.addSemigroup`,
  `Set.isScalarTower`, and `Set.distribSMulSet`, not local wrapper owners.
- Topology check: this item has no ambient/intrinsic topology content, so no topology-layer change.
- Owner-name/notation check: keep short canonical `Set` owners and use textbook-primary notation
  `+` and `•` on source-facing surfaces.
-/

/- Text 3.1.6 (1): pointwise addition of sets is commutative; this is the commutativity field of
the canonical owner declaration `Set.addCommSemigroup`. -/
recall Set.addCommSemigroup

/- Text 3.1.6 (2): pointwise addition of sets is associative; this is already present at the
weaker canonical owner declaration `Set.addSemigroup`. -/
recall Set.addSemigroup

/- Text 3.1.6 (3): scaling a set first by `λ₂` and then by `λ₁` is the same as
scaling it once by `λ₁ * λ₂`; this is the scalar-associativity field of the weaker
owner declaration `Set.isScalarTower`. -/
recall Set.isScalarTower

/- Text 3.1.6 (4): scalar multiplication distributes over pointwise addition of sets; this is the
distributivity field of the owner declaration `Set.distribSMulSet`. -/
recall Set.distribSMulSet
