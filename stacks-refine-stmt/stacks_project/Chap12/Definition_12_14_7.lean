import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: shifts of cochain complexes in a preadditive category;
- sampled owner declarations:
  `CochainComplex.shiftFunctor`,
  `CochainComplex.shiftFunctor_obj_X'`,
  `CochainComplex.shiftFunctor_obj_d'`,
  `CochainComplex.shiftFunctor_map_f'`.

Source/core/bridge triage:
- `core/canonical`: `CochainComplex.shiftFunctor`;
- `source-facing`: the shifted cochain complex `A⟦k⟧`;
- `bridge/view`: the degreewise object, differential, and morphism formulas supplied by the
  sampled companion lemmas.

Primitive data are only the owner functor. The formulas
`(A⟦k⟧).X n = A.X (n + k)`, `d = (-1)^k • A.d (n + k) (n + k + 1)`, and
`((shiftFunctor _ k).map f).f n = f.f (n + k)` are derived API, so this file should remain a
canonical recall item rather than reintroducing a parallel local shift definition.

Definition 12.14.7: the source-facing shift construction on cochain complexes is the canonical
owner functor `CochainComplex.shiftFunctor`. -/
recall CochainComplex.shiftFunctor
