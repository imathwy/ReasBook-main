import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

/- Lemma 10.14.4 is a `core/canonical` recall item in the change-of-rings domain. Its owner
abstraction is the mathlib adjunction `ModuleCat.restrictCoextendScalarsAdj`; the textbook
statement that `ModuleCat.restrictScalars f` is left adjoint to `ModuleCat.coextendScalars f` is
exactly this canonical declaration. -/
recall ModuleCat.restrictCoextendScalarsAdj

/- Companion check: for an `S`-module `N` and an `R`-module `M`, the textbook bijection
`Hom_R(N, M) ≃ Hom_S(N, Hom_R(S, M))` is the canonical equivalence
`(ModuleCat.restrictCoextendScalarsAdj f).homEquiv N M`. -/
#check (ModuleCat.restrictCoextendScalarsAdj f).homEquiv
