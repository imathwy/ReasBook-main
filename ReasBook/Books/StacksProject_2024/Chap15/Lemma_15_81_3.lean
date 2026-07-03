import stacks_project.Chap10.Lemma_10_36_23
import stacks_project.Chap15.Lemma_15_81_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules under restriction of scalars along a
  finite algebra map;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `iff_overAnyFinitelyPresentedCover`,
  `Module.FinitePresentation.iff_of_finite_finitePresentation`,
  `Module.Finite.exists_free_surjective`,
  `Algebra.FinitePresentation.out`;
- best owner abstraction: the source-facing owner predicate
  `Module.FinitePresentationRelativeTo`;
- primitive data: a finite type `R`-algebra `A`, a finite `A`-algebra `B`, and a `B`-module `M`
  together with its canonical restricted `A`-module structure expressed by `[Module A M]` and
  `[IsScalarTower A B M]`;
- derived API: the comparison of the source-facing owner over `A` and over `B`, obtained by
  passing through finite free algebra covers and the canonical finite scalar-change equivalence for
  ordinary finite presentation.

Source/core/bridge triage:
- `source-facing`: Lemma `15.81.3`, which compares relative finite presentation for a `B`-module
  and its restriction of scalars to `A`;
- `core/canonical`: `Module.FinitePresentationRelativeTo R A _` and
  `Module.FinitePresentationRelativeTo R B _`;
- `bridge/view`: `iff_overAnyFinitelyPresentedCover`,
  `Module.FinitePresentation.iff_of_finite_finitePresentation`,
  `Module.Finite.exists_free_surjective`, and `Algebra.FinitePresentation.out`. -/

variable {R : Type u} {A : Type v} {B : Type w} {M : Type x}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable [Algebra.FiniteType R A]
variable [Module.Finite A B]

namespace Module

open Module.FinitePresentation

-- Proof sketch: for the forward direction, start from one polynomial presentation of `A`
-- witnessing `FinitePresentationRelativeTo R A M`. Restrict scalars along that presentation to
-- make `B` finite over the polynomial ring, choose a finite free cover `B' → B`, and then pass
-- from finite presentation over the polynomial ring to finite presentation over `B'` via the
-- canonical finite scalar-change equivalence. Finally, expand the finitely presented algebra `B'`
-- over `R` into one polynomial presentation of `B`. For the backward direction, start from a
-- polynomial presentation `P → A` coming from `Algebra.FiniteType R A`; then `B` is finite over
-- `P`, so a finite free cover `B' → B` over `P` lets the hypothesis on `B` descend back to
-- finite presentation over `P`, yielding the required witness for `A`. The ambient
-- `Algebra.FiniteType R A` hypothesis is genuine here because the backward implication needs such
-- a polynomial presentation of `A`.
/-- Lemma 15.81.3: for a finite map `A → B` of finite type `R`-algebras and a `B`-module `M`,
if the `A`-module structure on `M` is the canonical restriction of scalars along `A → B`, then
`M` is finitely presented relative to `R` as an `A`-module if and only if it is finitely presented
relative to `R` as a `B`-module. -/
theorem finitePresentationRelativeTo_iff_of_finite :
    FinitePresentationRelativeTo R A M ↔ FinitePresentationRelativeTo R B M := by
  constructor
  · intro hM
    rcases hM with ⟨n, α, hα, hPM⟩
    let P := MvPolynomial (Fin n) R
    letI : Algebra P A := α.toAlgebra
    letI : Module P A := Module.compHom A α.toRingHom
    letI : Module P M := Module.compHom M α.toRingHom
    letI : Algebra P B := ((algebraMap A B).comp α).toAlgebra
    letI : IsScalarTower R P B := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R B r = algebraMap A B (α (algebraMap R P r))
      rw [α.commutes, IsScalarTower.algebraMap_apply R A B r]
    letI : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' rfl
    letI : Module.Finite P A :=
      Module.Finite.of_surjective (Algebra.linearMap P A) hα
    letI : Module.Finite P B := Module.Finite.trans A B
    obtain ⟨B', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective P B
    letI : Algebra R B' := ((algebraMap P B').comp (algebraMap R P)).toAlgebra
    letI : IsScalarTower R P B' := IsScalarTower.of_algebraMap_eq' rfl
    letI : Module B' M := Module.compHom M f.toRingHom
    letI : IsScalarTower P B' M := IsScalarTower.of_algebraMap_smul fun p m ↦ by
      change f (algebraMap P B' p) • m = p • m
      rw [f.commutes]
      change algebraMap A B (α p) • m = α p • m
      simpa using (IsScalarTower.algebraMap_smul (α p) m)
    have hB'M : Module.FinitePresentation B' M :=
      iff_of_finite_finitePresentation.mp hPM
    letI : Algebra.FinitePresentation R B' := Algebra.FinitePresentation.trans R P B'
    obtain ⟨m, β, hβ, hkerβ⟩ := (inferInstance : Algebra.FinitePresentation R B').out
    letI : Algebra (MvPolynomial (Fin m) R) B' := β.toRingHom.toAlgebra
    letI : Module (MvPolynomial (Fin m) R) B' := Module.compHom B' β.toRingHom
    letI : Module (MvPolynomial (Fin m) R) M :=
      Module.compHom M ((f.restrictScalars R).comp β).toRingHom
    letI : IsScalarTower (MvPolynomial (Fin m) R) B' M :=
      IsScalarTower.of_compHom (MvPolynomial (Fin m) R) B' M
    letI : Module.FinitePresentation (MvPolynomial (Fin m) R) B' :=
      Module.finitePresentation_of_surjective (Algebra.linearMap (MvPolynomial (Fin m) R) B')
        hβ (by simpa using hkerβ)
    have hQM : Module.FinitePresentation (MvPolynomial (Fin m) R) M :=
      Module.FinitePresentation.trans (MvPolynomial (Fin m) R) M B'
    have hcomp : Function.Surjective ((f.restrictScalars R).comp β) := by
      intro b
      rcases hf b with ⟨b', rfl⟩
      rcases hβ b' with ⟨q, rfl⟩
      exact ⟨q, rfl⟩
    refine ⟨m, (f.restrictScalars R).comp β, hcomp, ?_⟩
    simpa using hQM
  · intro hM
    obtain ⟨n, α, hα⟩ :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
    let P := MvPolynomial (Fin n) R
    letI : Algebra P A := α.toAlgebra
    letI : Module P A := Module.compHom A α.toRingHom
    letI : Module P M := Module.compHom M α.toRingHom
    letI : Algebra P B := ((algebraMap A B).comp α).toAlgebra
    letI : IsScalarTower R P B := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R B r = algebraMap A B (α (algebraMap R P r))
      rw [α.commutes, IsScalarTower.algebraMap_apply R A B r]
    letI : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' rfl
    letI : Module.Finite P A :=
      Module.Finite.of_surjective (Algebra.linearMap P A) hα
    letI : Module.Finite P B := Module.Finite.trans A B
    letI : Algebra.FiniteType R B := Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R P) (inferInstance : Algebra.FiniteType P B)
    obtain ⟨B', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective P B
    letI : Algebra R B' := ((algebraMap P B').comp (algebraMap R P)).toAlgebra
    letI : IsScalarTower R P B' := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.FinitePresentation R B' := Algebra.FinitePresentation.trans R P B'
    letI : Module B' M := Module.compHom M f.toRingHom
    have hB'M : Module.FinitePresentation B' M := by
      simpa using hM.overAnyFinitelyPresentedCover B' (f.restrictScalars R) hf
    letI : IsScalarTower P B' M := IsScalarTower.of_algebraMap_smul fun p m ↦ by
      change f (algebraMap P B' p) • m = p • m
      rw [f.commutes]
      change algebraMap A B (α p) • m = α p • m
      simpa using (IsScalarTower.algebraMap_smul (α p) m)
    have hPM : Module.FinitePresentation P M :=
      iff_of_finite_finitePresentation.mpr hB'M
    refine ⟨n, α, hα, ?_⟩
    simpa using hPM

end Module

end
