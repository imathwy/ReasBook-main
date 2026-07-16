import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Smooth R S]

/- Domain-style sampling:
- primary domain: infinitesimal lifting for smooth algebras across quotient maps by locally
  nilpotent ideals;
- sampled owner declarations: the chapter owner `Ideal.IsLocallyNilpotent`, together with
  mathlib's `Algebra.FormallySmooth.exists_lift` and the owner field
  `Algebra.Smooth.formallySmooth`;
- best owner abstraction: `Smooth R S` is the source-facing ambient owner, while local nilpotence
  should be expressed through `Ideal.IsLocallyNilpotent` rather than restating the containment
  `I ≤ nilradical A`.

Source/core/bridge triage:
- `source-facing`: the theorem below, which matches Lemma `10.138.17`;
- `core/canonical`: `Algebra.FormallySmooth.exists_lift`;
- `bridge/view`: the reduction from a locally nilpotent ideal to a nilpotent ideal inside a
  finite type subalgebra used in the proof sketch.
-/

-- Proof sketch: smoothness gives formal smoothness together with finite presentation. Descend the
-- given map `S → A ⧸ I` and finitely many chosen lifts of generators to a finite type
-- `ℤ`-subalgebra `A₀ ⊆ A`; then `I ∩ A₀` is nilpotent because `A₀` is Noetherian, so the
-- infinitesimal lifting theorem for formally smooth algebras applies to produce a lift into `A₀`,
-- hence into `A`.
/-- Lemma 10.138.17: if `R → S` is smooth and `I` is a locally nilpotent ideal of the
`R`-algebra `A`, then every commutative square
`S → A ⧸ I ← A` over `R` admits a lift `S → A`. In canonical form, the locally nilpotent
hypothesis is expressed by the chapter owner `I.IsLocallyNilpotent`. -/
theorem smooth_exists_lift_of_quotient_by_locally_nilpotent
    (I : Ideal A) (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := sorry

end

end Algebra
