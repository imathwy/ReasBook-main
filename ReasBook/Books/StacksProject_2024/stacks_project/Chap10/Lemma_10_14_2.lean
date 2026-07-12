import Mathlib
import Mathlib.Tactic.Recall

open scoped TensorProduct

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling:
- primary domain: finiteness conditions for modules and algebras under tensor-product base change;
- sampled owner declarations:
  `Module.Finite.base_change`,
  the tensor-product base-change instance for `Module.FinitePresentation`,
  `Algebra.FiniteType.baseChange`,
  `Algebra.FinitePresentation.baseChange`;
- best owner abstraction: the canonical finiteness owners `Module.Finite`,
  `Module.FinitePresentation`, `Algebra.FiniteType`, and `Algebra.FinitePresentation`;
- primitive data: the ring maps `R → S`, `R → R'`, and the original finiteness hypotheses on `M`
  or `S`;
- derived API: the four textbook finiteness statements after base change.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma 10.14.2;
- `core/canonical`: the owner declarations listed above;
- `bridge/view`: the tensor-product models `S' = S ⊗[R] R'` and `M' = S' ⊗[S] M`, together with
  the tensor-symmetry identification relating the textbook order of factors to the owner
  orientation used by mathlib.
-/

section ModuleBaseChange

variable {R S R' M : Type u} [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R'] [AddCommGroup M] [Module S M]
local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- Lemma 10.14.2 (1): if `M` is a finite `S`-module, then after base change along `R → R'`,
`M'` is finite over `S'`. This is the canonical theorem `Module.Finite.base_change`, applied to
the `S`-algebra `S'`. -/
recall Module.Finite.base_change

/- Lemma 10.14.2 (2): if `M` is a finitely presented `S`-module, then after base change along
`R → R'`, `M'` is finitely presented over `S'`. Mathlib exposes this as the canonical
tensor-product base-change instance for finitely presented modules. -/
variable [Module.FinitePresentation S M]

#check (inferInstance : Module.FinitePresentation S' M')

end ModuleBaseChange

section AlgebraBaseChange

variable {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R']
local notation "S'" => S ⊗[R] R'

/- Lemma 10.14.2 (3): if `R → S` is of finite type, then the standard base change
`R' → R' ⊗[R] S` is of finite type; via `Algebra.TensorProduct.comm R' S`, this is the textbook
base change `R' → S'`. This is the canonical theorem `Algebra.FiniteType.baseChange`. -/
recall Algebra.FiniteType.baseChange

/- Lemma 10.14.2 (4): if `R → S` is of finite presentation, then the standard base change
`R' → R' ⊗[R] S` is of finite presentation; via `Algebra.TensorProduct.comm R' S`, this is the
textbook base change `R' → S'`. This is the canonical theorem
`Algebra.FinitePresentation.baseChange`. -/
recall Algebra.FinitePresentation.baseChange

end AlgebraBaseChange
