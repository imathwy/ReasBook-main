import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [IsNoetherianRing S]
variable {R' : Type w} [CommRing R'] [Algebra R R'] [Algebra.FiniteType R R']
local notation "S'" => S ⊗[R] R'
attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- Domain triage: this lemma lies in commutative algebra of finite-type base change and
-- Noetherianity. The owner abstraction is the `S`-algebra `S'`, obtained from
-- `Algebra.FiniteType.baseChange`; its Noetherianity is then a derived instance from
-- `Algebra.FiniteType.isNoetherianRing`. The displayed tensor order `R' ⊗[R] S` is only the
-- source-facing bridge/view, recovered from the owner object by `Algebra.TensorProduct.comm`.
/-- Lemma 10.31.7: if `R → R'` is of finite type and `S` is a Noetherian `R`-algebra, then the
base-changed ring `R' ⊗[R] S` is Noetherian. -/
@[stacks 0CY6]
theorem isNoetherianRing_baseChange :
    IsNoetherianRing (R' ⊗[R] S) := by
  let _ : Algebra.FiniteType S S' := inferInstance
  let _ : IsNoetherianRing S' := Algebra.FiniteType.isNoetherianRing S S'
  simpa using
    (isNoetherianRing_of_ringEquiv S' (Algebra.TensorProduct.comm R S R').toRingEquiv :
      IsNoetherianRing (R' ⊗[R] S))

end
