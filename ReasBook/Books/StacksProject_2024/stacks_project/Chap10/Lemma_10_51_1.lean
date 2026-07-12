import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain triage: this item is in the commutative algebra of Noetherian modules.
- `source-facing`: finite presentation of finite modules, finiteness of submodules, and the
  ascending chain condition on submodules.
- `core/canonical`: the owner predicate `IsNoetherian R M`, together with mathlib's canonical
  bridges `Module.finitePresentation_of_finite`,
  `isNoetherian_of_submodule_of_noetherian`, and
  `monotone_stabilizes_iff_noetherian`.
- `bridge/view`: the source-facing finiteness statement for a submodule is the derived instance
  `Module.Finite R N`, not extra primitive data; the ACC clause is the specialized forward
  implication of `monotone_stabilizes_iff_noetherian`, not the equivalence itself.
Primitive data are just the ambient ring, module, and chosen submodule. -/

/- Lemma 10.51.1 (1): over a Noetherian ring, every finite `R`-module is finitely presented.
This is exactly the canonical theorem `Module.finitePresentation_of_finite`. -/
section FiniteOverNoetherianRing

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

recall Module.finitePresentation_of_finite

variable (N : Submodule R M)

/- Lemma 10.51.1 (2): every submodule of a finite `R`-module is finite over a Noetherian ring.
The owner theorem is `isNoetherian_of_submodule_of_noetherian`, and the source-facing finiteness
statement is the derived instance `Module.Finite R N`. -/
recall isNoetherian_of_submodule_of_noetherian
#check (inferInstance : Module.Finite R N)

end FiniteOverNoetherianRing

section NoetherianModule

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/- Lemma 10.51.1 (3): a Noetherian module satisfies the ascending chain condition on submodules.
This is the source-facing ACC consequence of the owner equivalence
`monotone_stabilizes_iff_noetherian`. -/
theorem submodule_monotone_stabilizes (f : ℕ →o Submodule R M) :
    ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian R M› f

end NoetherianModule
