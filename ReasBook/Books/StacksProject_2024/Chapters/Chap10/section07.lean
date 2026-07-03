import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_7_1 (from Chap10) -/
/- Definition 10.7.1: a ring map `φ : R → S` is finite exactly in the canonical sense of
`RingHom.Finite`, namely when the target ring is finite as a module over the source ring. -/
recall RingHom.Finite

/- Companion recall: for an `R`-algebra `S`, finiteness of the canonical map `algebraMap R S`
is exactly the module-finiteness statement `Module.Finite R S`. -/
recall RingHom.finite_algebraMap

/-! ### Lemma_10_7_2 (from Chap10) -/
universe u v w

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommSemiring R] [Semiring S] [Algebra R S]
variable [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite R S]

namespace Module.Finite

/-- Lemma 10.7.2: for a finite ring map `R → S` and an `S`-module `M`, finiteness of `M` as an
`R`-module is equivalent to finiteness of `M` as an `S`-module. -/
theorem iff_of_finite :
    Module.Finite R M ↔ Module.Finite S M :=
  ⟨fun _ ↦ of_restrictScalars_finite R S M, fun _ ↦ trans S M⟩

end Module.Finite

/-! ### Lemma_10_7_3 (from Chap10) -/
/- Lemma 10.7.3: the composite of two finite ring maps is finite. This is exactly the canonical
mathlib theorem `RingHom.Finite.comp`. -/
recall RingHom.Finite.comp

/-! ### Lemma_10_7_4 (from Chap10) -/
/- Lemma 10.7.4 (1): a finite ring map `φ : R → S` is of finite type. This is exactly the
canonical mathlib theorem `RingHom.Finite.to_finiteType`. -/
recall RingHom.Finite.to_finiteType

/- Lemma 10.7.4 (2), owner abstraction: if an `R`-algebra `S` is finitely presented as an
`R`-module, then `S` is finitely presented as an `R`-algebra. -/
recall Algebra.FinitePresentation.of_finitePresentation

/- Lemma 10.7.4 (2), `bridge/view` layer: the ring-map formulation is obtained from the owner
abstraction `Algebra.FinitePresentation` via the canonical equivalence for `algebraMap`. -/
recall RingHom.finitePresentation_algebraMap
