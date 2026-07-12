import Mathlib.RingTheory.FiniteType
import StacksProject_2024.Chap10.Lemma_10_6_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules over finite type algebras;
- sampled owner declarations:
  `Module.FinitePresentation`,
  `Algebra.FiniteType.iff_quotient_mvPolynomial''`,
  `Algebra.FiniteType.of_surjective`,
  `Module.FinitePresentation.of_restrictScalars_finiteType`;
- best owner abstraction: the source-facing predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of the `R`-algebra `A` together with
  finite presentation of `M` over that presentation ring;
- derived API: finite type of `A` over `R`, and ordinary finite presentation of `M` over `A`
  via restriction-of-scalars along a finite type algebra.

Source/core/bridge triage:
- `source-facing`: `Module.FinitePresentationRelativeTo R A M`;
- `core/canonical`: `Module.FinitePresentation` and `Algebra.FiniteType`;
- `bridge/view`: `Module.finitePresentation_of_finitePresentationRelativeTo`, which applies the
  canonical finite-type scalar-restriction theorem to one source-facing witness.

The owner predicate is the right public abstraction here, so this file should keep that owner and
derive its ordinary finite-presentation consequence through the canonical chapter-10 bridge,
rather than introducing a parallel wrapper around `Module.FinitePresentation`. -/

variable (R : Type u) (A : Type v) (M : Type w)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

/-- Definition 15.81.2: an `A`-module is finitely presented relative to `R` if it is finitely
presented over one polynomial presentation of the finite type `R`-algebra `A`. -/
@[stacks 05GZ]
def Module.FinitePresentationRelativeTo : Prop :=
  ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
    Function.Surjective α ∧
      let _ : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
      Module.FinitePresentation (MvPolynomial (Fin n) R) M

/-- A module finitely presented relative to `R` can exist only over a finite type `R`-algebra. -/
theorem Module.FinitePresentationRelativeTo.finiteType
    (h : Module.FinitePresentationRelativeTo R A M) :
    Algebra.FiniteType R A := by
  rcases h with ⟨n, α, hα, -⟩
  exact (Algebra.FiniteType.iff_quotient_mvPolynomial'').2 ⟨n, α, hα⟩

-- Proof sketch: choose a surjective polynomial presentation from
-- `Module.FinitePresentationRelativeTo R A M` and descend finite presentation along the
-- quotient map `MvPolynomial (Fin n) R →ₐ[R] A`, exactly as in Lemma 15.81.1.
/-- A module that is finitely presented relative to `R` is finitely presented as an `A`-module. -/
theorem Module.finitePresentation_of_finitePresentationRelativeTo
    (h : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentation A M := by
  rcases h with ⟨n, α, hα, hM⟩
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  letI : Algebra.FiniteType P A := by
    have hα' : Function.Surjective (algebraMap P A) := by
      change Function.Surjective α
      simpa using hα
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.FiniteType.of_surjective (algebraMap P A) hα'
  letI : Module.FinitePresentation P M := by
    simpa [P] using hM
  exact Module.FinitePresentation.of_restrictScalars_finiteType P

end
