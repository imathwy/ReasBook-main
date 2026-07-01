import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain-style sampling for towers of field extensions:
- primary domain: finite chains of field extensions;
- sampled owner declarations:
  `Algebra F E` from Definition 9.6.2,
  `IsScalarTower`,
  `rank_mul_rank`,
  `Algebra.IsSeparable.trans`;
- best owner abstraction: a finite tower is source-facing primitive data consisting of the
  successive field extensions `E_{i + 1} / E_i`, so the public entry should remain the direct
  family of adjacent `Algebra` structures indexed by `Fin n`;
- primitive data: the family of fields `E : Fin (n + 1) → Type u` and the consecutive algebra
  structures;
- derived API: once one focuses on a fixed three-stage subtower and equips the composite stage
  with its algebra structure, `IsScalarTower` and downstream tower lemmas become the canonical
  compatibility layer.

Layer triage:
- `source-facing`: the finite tower `E_n / E_{n - 1} / ... / E_0`;
- `core/canonical`: `Algebra F E` for each adjacent extension;
- `bridge/view`: `IsScalarTower` and the standard transitivity lemmas for a chosen triple.
-/

section

variable {n : ℕ} (E : Fin (n + 1) → Type u)
variable [∀ i : Fin (n + 1), Field (E i)]

/- Definition 9.6.3: building on Definition 9.6.2, a tower of fields
`E_n / E_{n - 1} / ... / E_0` is expressed in Lean by a family of fields
`E : Fin (n + 1) → Type u` together with the canonical extension structure on each consecutive
pair. The source-facing primitive data are exactly these successive `Algebra` structures;
`IsScalarTower` is the canonical derived compatibility notion for a fixed three-stage subtower,
not the owner abstraction for the whole finite chain. -/
#check (∀ i : Fin n, Algebra (E i.castSucc) (E i.succ))

end
