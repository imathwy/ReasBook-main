import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Algebra.FiniteType R S]

/-
Lemma 10.51.7 (Artin-Tate) is a `bridge/view` item in the finite-type / finite-module algebra-tower
domain. The owner abstraction is `fg_of_fg_of_fg`, and the textbook finite-type formulation for an
intermediate `R`-subalgebra is the derived bridge below via `Subalgebra.fg_iff_finiteType`.
-/
recall fg_of_fg_of_fg

/-- Lemma 10.51.7 (Artin-Tate): if `T` is an `R`-subalgebra of a finite type `R`-algebra `S` and
`S` is finite as a `T`-module, then `T` is finite type over the Noetherian ring `R`. -/
@[stacks 00IS]
theorem Subalgebra.finiteType_of_finite (T : Subalgebra R S) [Module.Finite T S] :
    Algebra.FiniteType R T := by
  exact (Subalgebra.fg_iff_finiteType T).mp <|
    (T.fg_top).mp <|
      fg_of_fg_of_fg R T S Algebra.FiniteType.out Module.Finite.fg_top Subtype.val_injective

end
