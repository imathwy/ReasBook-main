import Mathlib
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_81_1 (from Chap15) -/
universe u v w x

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules over a finite type algebra;
- sampled owner declarations:
  `Module.FinitePresentation`,
  `Algebra.FinitePresentation`,
  `Module.FinitePresentationRelativeTo`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`;
- best owner abstraction: the source-facing owner predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of the finite type `R`-algebra `A`,
  together with finite presentation of `M` over that presentation ring;
- derived API: the presentation-independent reformulations using every polynomial presentation and
  every finitely presented cover of `A`, which belong on the theorem surface rather than as
  separate public predicate owners.

Source/core/bridge triage:
- `source-facing`: `Module.FinitePresentationRelativeTo R A M` together with the theorem below
  comparing it with the other two formulations in the Stacks lemma;
- `core/canonical`: `Module.FinitePresentation` and `Algebra.FinitePresentation`;
- `bridge/view`: the two equivalence theorems comparing the owner with the universal polynomial and
  finitely presented cover formulations.

The first clause of the textbook equivalence is exactly the existing owner
`Module.FinitePresentationRelativeTo R A M`, so the local duplicate wrapper should be removed
rather than preserved under a second name. -/

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

section FiniteType

variable [Algebra.FiniteType R A]

namespace Module.FinitePresentationRelativeTo

-- Proof sketch: compare any two polynomial presentations of `A` by adjoining both sets of
-- variables and applying the stability of finite presentation under finite type scalar restriction
-- and quotient maps from Algebra, Lemmas `10.6.4` and `10.36.23`; then pass between polynomial
-- presentations and arbitrary finitely presented covers using a quotient presentation
-- `A' ≅ R[x_1, ..., x_n] / (f_1, ..., f_m)`.
/-- Lemma 15.81.1: for a finite type ring map `R → A` and an `A`-module `M`, the following are
equivalent: `M` is finitely presented over some polynomial presentation of `A`; `M` is finitely
presented over every polynomial presentation of `A`. -/
theorem iff_overEveryPolynomialPresentation :
    Module.FinitePresentationRelativeTo R A M ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          Module.FinitePresentation P M := sorry

/-- Lemma 15.81.1, cover formulation: for a finite type ring map `R → A` and an `A`-module `M`,
`M` is finitely presented over some polynomial presentation of `A` if and only if for every
surjection `A' → A` with `A'` a finitely presented `R`-algebra, `M` is finitely presented as an
`A'`-module. -/
theorem iff_overAnyFinitelyPresentedCover :
    Module.FinitePresentationRelativeTo R A M ↔
      ∀ (A' : Type x) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
        (f : A' →ₐ[R] A) (_ : Function.Surjective f),
          let _ : Module A' M := Module.compHom M f.toRingHom
          Module.FinitePresentation A' M := sorry

end Module.FinitePresentationRelativeTo

end FiniteType

namespace Module.FinitePresentationRelativeTo

/-- If `M` is finitely presented relative to `R`, then for every surjective polynomial
presentation `P → A`, the transported `P`-module structure on `M` is finitely presented. -/
theorem overPolynomialPresentation (hM : Module.FinitePresentationRelativeTo R A M)
    (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α) :
    let P := MvPolynomial (Fin n) R
    let _ : Module P M := Module.compHom M α.toRingHom
    Module.FinitePresentation P M := by
  letI : Algebra.FiniteType R A := hM.finiteType
  have hiff :
      Module.FinitePresentationRelativeTo R A M ↔
        ∀ n : ℕ,
          let P := MvPolynomial (Fin n) R
          ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
            let _ : Module P M := Module.compHom M α.toRingHom
            Module.FinitePresentation P M := iff_overEveryPolynomialPresentation
  simpa using
    hiff.mp hM n α hα

/-- If `M` is finitely presented relative to `R`, then for every surjective map `A' → A` from a
finitely presented `R`-algebra `A'`, the transported `A'`-module structure on `M` is finitely
presented. -/
theorem overAnyFinitelyPresentedCover (hM : Module.FinitePresentationRelativeTo R A M)
    (A' : Type x) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
    (f : A' →ₐ[R] A) (hf : Function.Surjective f) :
    let _ : Module A' M := Module.compHom M f.toRingHom
    Module.FinitePresentation A' M := by
  letI : Algebra.FiniteType R A := hM.finiteType
  have hiff :
      Module.FinitePresentationRelativeTo R A M ↔
        ∀ (A' : Type x) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
          (f : A' →ₐ[R] A) (_ : Function.Surjective f),
            let _ : Module A' M := Module.compHom M f.toRingHom
            Module.FinitePresentation A' M := iff_overAnyFinitelyPresentedCover
  simpa using
    hiff.mp hM A' f hf

end Module.FinitePresentationRelativeTo

/- If `M` is finitely presented relative to `R` as an `A`-module, then it is finitely presented as
an `A`-module; this is the canonical owner theorem from `Definition_15.81.2`. -/
#check Module.finitePresentation_of_finitePresentationRelativeTo

end

/-! ### Definition_15_81_2 (from Chap15) -/
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

/-! ### Lemma_15_81_3 (from Chap15) -/
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

/-! ### Lemma_15_81_4 (from Chap15) -/
universe u v w

section

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: relative finite presentation of modules under localization;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentation`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `LocalizedModule.Away`,
  `IsLocalization.Away.finitePresentation`;
- best owner abstraction: the source-facing predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of the ambient algebra together with
  finite presentation of the induced module over that polynomial ring;
- derived API: localization statements and ordinary finite presentation over the target algebra.

Source/core/bridge triage:
- `source-facing`: the localization theorem below for relative finite presentation;
- `core/canonical`: `Module.FinitePresentation`;
- `bridge/view`: passage from the localized source-facing owner over `Localization.Away f` to the
  localized target owner over `R`.

The raw existential in the original statement is exactly the primitive data already owned by
`Module.FinitePresentationRelativeTo`, so the theorem should use that owner directly rather than
repeat the witness package locally. -/

variable {R : Type u} [CommRing R]
variable {f : R}
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra (Localization.Away f) A]
variable [IsScalarTower R (Localization.Away f) A]
variable {g : A}
variable {M : Type w} [AddCommGroup M] [Module A M]

-- Proof sketch: choose a polynomial presentation of `A` over `Localization.Away f`, rewrite
-- `Localization.Away f` as an `R`-algebra obtained by adjoining an inverse to `f`, then localize
-- the presentation further at `g` by adjoining an inverse to `g`; this gives a polynomial
-- presentation of `LocalizedModule.Away g M` over `R`.
/-- Lemma 15.81.4: if `M` is finitely presented relative to the localized base
`Localization.Away f` as an `A`-module, then the localized module `Away g M` is
finitely presented relative to `R` as a `Localization.Away g`-module. -/
theorem Module.finitePresentationRelativeTo_localizationAway_from_localizedBase
    (hM : Module.FinitePresentationRelativeTo (Localization.Away f) A M) :
    Module.FinitePresentationRelativeTo R (Localization.Away g) (Away g M) := sorry

end

/-! ### Lemma_15_81_5 (from Chap15) -/
universe u v w x

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules under scalar base change;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentationRelativeTo.overPolynomialPresentation`,
  `Module.FinitePresentation`,
  the tensor-base-change instance for `Module.FinitePresentation`;
- best owner abstraction: the source-facing predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of `A` over `R` together with finite
  presentation of `M` over that presentation ring;
- derived API: presentation-independent finite presentation over any chosen polynomial
  presentation of `A`, the tensor-base-change instance for `Module.FinitePresentation`, the
  canonical `R'`-algebra structure on `A ⊗[R] R'`, and the relative finite-presentation
  statement for the base-changed module.

Source/core/bridge triage:
- `source-facing`: the theorem below about relative finite presentation after the base change
  `R → R'`;
- `core/canonical`: `Module.FinitePresentation` and `Algebra.FiniteType`;
- `bridge/view`: `MvPolynomial.algebraTensorAlgEquiv` and the standard tensor base-change
  equivalences identifying the presentation ring and module after scalar extension, together with
  the canonical right-action `R'`-algebra structure on `A ⊗[R] R'`.

The owner is already the correct source-facing predicate, so the main theorem should live on the
`Module` namespace and reuse the chapter owner API
`Module.FinitePresentationRelativeTo.overPolynomialPresentation` beneath that owner rather than
unpack one particular witness and duplicate that bridge locally. -/

variable {R : Type u} {A : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [AddCommGroup M] [Module A M]

-- Proof sketch: choose any polynomial presentation `P → A` coming from the finite-type algebra
-- structure implicit in `hM`, obtain `Module.FinitePresentation P M` from the canonical owner API
-- `hM.overPolynomialPresentation`, base-change `P` to `R'`, rewrite that base change as a
-- polynomial ring over `R'`, and then apply the standard tensor-base-change stability of
-- `Module.FinitePresentation` to the induced presentation of `((A ⊗[R] R') ⊗[A] M)`.
/-- Lemma 15.81.5: if `M` is finitely presented relative to `R`, then for any base change
`R → R'` the base-changed `(A ⊗[R] R')`-module `((A ⊗[R] R') ⊗[A] M)`, canonically identified
with `M ⊗[R] R'`, is finitely presented relative to `R'`; the needed `R'`-algebra structure on
`A ⊗[R] R'` is the canonical tensor-product one, and the finite-type hypothesis on `R → A` is
already implicit in `Module.FinitePresentationRelativeTo R A M`. -/
theorem Module.finitePresentationRelativeTo_baseChange
    (hM : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentationRelativeTo R' (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := by
  sorry

end

/-! ### Lemma_15_81_6 (from Chap15) -/
open scoped TensorProduct

universe u v w x

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules over finite type / finitely presented
  algebra maps;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`,
  `Module.FinitePresentation.trans`,
  the tensor-product base-change instance for `Module.FinitePresentation`;
- best owner abstraction: the source-facing owner predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: a single surjective polynomial presentation of `A` over `R` over which `M` is
  finitely presented;
- derived API: finite type of `A` over `R`, ordinary finite-presentation consequences, the
  algebra finite-presentation restriction-of-scalars bridge, transitivity of module finite
  presentation, and tensor-product base change for finitely presented modules.

Source/core/bridge triage:
- `source-facing`: `Module.FinitePresentationRelativeTo R A M`;
- `core/canonical`: `Module.FinitePresentation`, `Algebra.FinitePresentation`, and the canonical
  base-change / scalar-restriction theorems for finitely presented modules;
- `bridge/view`: the theorem below, which upgrades the source-facing relative statement along a
  finitely presented algebra map using those canonical owners. -/

variable {R : Type u} {A : Type v} {A' : Type w} {M : Type x}
variable [CommRing R] [CommRing A] [CommRing A']
variable [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
variable [AddCommGroup M] [Module A M]
variable [Algebra.FinitePresentation A A']

-- Proof sketch: start from the owner predicate
-- `Module.FinitePresentationRelativeTo R A M`, derive the finite-type `R`-algebra structure on
-- `A` from that witness, then compare the chosen polynomial presentation with a finitely
-- presented polynomial presentation of `A'` over `A`. The module-theoretic input should stay on
-- the canonical owners `Module.FinitePresentation` and `Algebra.FinitePresentation`, using the
-- standard tensor-product finite-presentation instance and the scalar-restriction/transitivity
-- bridges from Chapter 10 rather than any parallel local wrapper. The only new mathematical
-- content here is the source-facing relative reformulation over `R`, not a new owner for finite
-- presentation.
/-- Lemma 15.81.6: let `M` be an `A`-module finitely presented relative to `R`, and let
`A → A'` be a ring map of finite presentation. Then the base-changed `A'`-module `A' ⊗[A] M`,
canonically identified with the textbook module `M ⊗[A] A'`, is finitely presented relative to
`R`. -/
theorem Module.finitePresentationRelativeTo_baseChange_of_finitePresentation
    (hM : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentationRelativeTo R A' (A' ⊗[A] M) := sorry

end

/-! ### Lemma_15_81_7 (from Chap15) -/
universe u v w x

section

/-
Domain-style sampling:
- primary domain: relative finite presentation of modules over a tower of algebras;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `Algebra.FinitePresentation.trans`,
  `Algebra.FinitePresentation.mvPolynomial_of_finitePresentation`;
- best owner abstraction: the source-facing predicate `Module.FinitePresentationRelativeTo`;
- primitive data: a polynomial presentation of the target algebra over the intermediate algebra
  together with finite presentation of the module over that polynomial ring;
- derived API: transitivity along a finitely presented intermediate algebra.

Source/core/bridge triage:
- `source-facing`: the transitivity statement for relative finite presentation in the algebra tower
  `R → A → B`;
- `core/canonical`: `Module.FinitePresentationRelativeTo` and `Algebra.FinitePresentation`;
- `bridge/view`: the theorem below, which upgrades relative finite presentation from base `A` to
  base `R` using finite presentation of the intermediate algebra.

The finite-type hypotheses from the textbook are redundant on the public Lean surface here:
`Algebra.FinitePresentation R A` already implies `Algebra.FiniteType R A`, and
`Module.FinitePresentationRelativeTo A B M` already packages a surjective polynomial presentation
of `B` over `A`. -/
variable {R : Type u} {A : Type v} {B : Type w} {M : Type x}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [AddCommGroup M] [Module B M]

-- Proof sketch: choose a surjective polynomial presentation of `B` over `A` witnessing that `M`
-- is finitely presented relative to `A`, then present `A` itself as a finitely presented
-- `R`-algebra. Compose these presentations to obtain a surjective polynomial presentation of `B`
-- over `R`, and rewrite the resulting module presentation by adjoining the finitely many
-- relations cutting out `A` over `R`.
/-- Lemma 15.81.7: if `R → A → B` is a tower of ring maps, `M` is a `B`-module finitely
presented relative to `A`, and `A` is finitely presented over `R`, then `M` is finitely
presented relative to `R`. -/
theorem Module.finitePresentationRelativeTo_trans [Algebra.FinitePresentation R A]
    (hM : Module.FinitePresentationRelativeTo A B M) :
    Module.FinitePresentationRelativeTo R B M := by
  rcases hM with ⟨n, α, hα, hM⟩
  let P := MvPolynomial (Fin n) A
  letI : Module P M := Module.compHom M α.toRingHom
  have hP : Algebra.FinitePresentation R P := by
    simpa [P] using (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (Fin n))
  letI : Algebra.FinitePresentation R P := hP
  obtain ⟨m, β, hβ, hkerβ⟩ := (inferInstance : Algebra.FinitePresentation R P).out
  let Q := MvPolynomial (Fin m) R
  letI : Algebra Q P := β.toRingHom.toAlgebra
  letI : Module Q P := Module.compHom P β.toRingHom
  have hQP : Module.FinitePresentation Q P := by
    refine Module.finitePresentation_of_surjective (Algebra.linearMap Q P) hβ ?_
    simpa using hkerβ
  letI : Module.FinitePresentation Q P := hQP
  letI : Module Q M := Module.compHom M ((α.restrictScalars R).comp β).toRingHom
  letI : IsScalarTower Q P M := IsScalarTower.of_compHom Q P M
  have hαR : Function.Surjective (α.restrictScalars R) := by
    simpa using hα
  have hcomp : Function.Surjective ((α.restrictScalars R).comp β) := by
    intro b
    rcases hαR b with ⟨p, rfl⟩
    rcases hβ p with ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  refine ⟨m, (α.restrictScalars R).comp β, hcomp, ?_⟩
  exact (Module.FinitePresentation.trans Q M P : Module.FinitePresentation Q M)

end

/-! ### Lemma_15_81_8 (from Chap15) -/
universe u v w

section

open scoped TensorProduct

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: relative finite presentation of modules and locality on a finite principal-open
  cover;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentationRelativeTo.iff_overAnyFinitelyPresentedCover`,
  `Module.finitePresentationRelativeTo_baseChange_of_finitePresentation`,
  `module_finitePresentation_of_localizationAway`;
- best owner abstraction: the source-facing owner predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: a finitely presented `R`-algebra cover of `A` together with a finite
  presentation of `M` after restricting scalars to that cover;
- derived API: localization and descent lemmas that turn that owner data into ordinary finite
  presentation on local charts and back.

Source/core/bridge triage:
- `source-facing`: the locality theorem below for `Module.FinitePresentationRelativeTo`;
- `core/canonical`: `Module.FinitePresentation` and the principal-open descent theorem
  `module_finitePresentation_of_localizationAway`;
- `bridge/view`: Lemma `15.81.1`, which converts between the relative owner and finite
  presentation over finitely presented covers of `A`.

The public API should stay centered on `Module.FinitePresentationRelativeTo`; the ordinary
finite-presentation theorem is auxiliary descent data, not a second owner for this notion. -/

-- Proof sketch: for `→`, a source-facing relative presentation already implies
-- `Algebra.FiniteType R A`; localize that presentation and apply the chapter's
-- finite-presentation base-change theorem
-- `Module.finitePresentationRelativeTo_baseChange_of_finitePresentation`, then identify the
-- resulting tensor product with `LocalizedModule.Away` via `LocalizedModule.equivTensorProduct`.
-- For `←`, each local hypothesis implies `Algebra.FiniteType R (Localization.Away f.1)`, so
-- `Algebra.FiniteType.of_span_eq_top_source hs` recovers `Algebra.FiniteType R A`. Then choose a
-- finitely presented cover of `A`; the local hypotheses and Lemma `15.81.1` make each induced
-- localized module finitely presented over the corresponding localized cover, Lemma `10.23.2`
-- descends finite presentation over that cover, and Lemma `15.81.1` packages the result back
-- into `FinitePresentationRelativeTo`, with the ordinary finite-presentation descent step routed
-- through the chapter's principal-open locality theorem
-- `module_finitePresentation_of_localizationAway`.

namespace Module.FinitePresentationRelativeTo

/-- Lemma 15.81.8: for an `R`-algebra `A`, an `A`-module `M`, and finitely many elements of `A`
generating the unit ideal, `M` is finitely presented relative to `R` if and only if each
principal localization `M_f` is finitely presented relative to `R`; the localized hypotheses
already force `A` to be finite type over `R`. -/
theorem iff_localizationAway_unitIdeal
    (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤) :
    FinitePresentationRelativeTo R A M ↔
      ∀ f : s, FinitePresentationRelativeTo R (Localization.Away f.1) (Away f.1 M) := by
  sorry

end Module.FinitePresentationRelativeTo

end

/-! ### Lemma_15_81_9 (from Chap15) -/
universe u v w x y

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules over a finite type algebra in short exact
  sequences;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentationRelativeTo.iff_overEveryPolynomialPresentation`,
  `Module.finitePresentation_of_exact`,
  `Module.finitePresentation_of_surjective_of_exact`;
- best owner abstraction: the source-facing predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation `P → A` together with ordinary finite
  presentation / finite generation after restricting scalars to `P`;
- derived API: exact-sequence closure statements for relative finite presentation, obtained by
  transporting all three modules to the same polynomial presentation and then invoking the core
  exact-sequence theorems for `Module.FinitePresentation`.

Source/core/bridge triage:
- `source-facing`: the two exact-sequence theorems below for
  `Module.FinitePresentationRelativeTo R A _`;
- `core/canonical`: `Module.FinitePresentation`, `Module.Finite`, and the exact-sequence lemmas of
  Lemma `10.5.3`;
- `bridge/view`: Lemma `15.81.1` in the owner theorem
  `Module.FinitePresentationRelativeTo.iff_overEveryPolynomialPresentation`, which moves relative
  finite presentation to any chosen polynomial presentation of `A`.

The owner is already correct, so the refinement should stay at the relative owner and delete any
temptation to build a second presentation wrapper. The only data that must remain primitive is the
single witness `P → A`; exactness consequences are derived from the canonical core theorems after
restriction of scalars. -/

variable {R : Type u} {A : Type v}
variable {M' : Type w} {M : Type x} {M'' : Type y}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M'] [Module A M']
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup M''] [Module A M'']

namespace Module

section

-- Proof sketch: by Lemma `15.81.1`, it is enough to work over an arbitrary surjective polynomial
-- presentation `P → A`. Over that chosen `P`, the relative finite presentation hypotheses for
-- `M'` and `M''` become ordinary finite presentation, so Lemma `10.5.3 (1)` applies directly to
-- the restricted short exact sequence.
/-- Lemma 15.81.9 (1): for a finite type ring map `R → A` and a short exact sequence
`0 → M' → M → M'' → 0` of `A`-modules, if `M'` and `M''` are finitely presented relative to `R`,
then `M` is finitely presented relative to `R`. -/
theorem finitePresentationRelativeTo_of_exact
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM' : FinitePresentationRelativeTo R A M') (hM'' : FinitePresentationRelativeTo R A M'') :
    FinitePresentationRelativeTo R A M := by
  letI : Algebra.FiniteType R A := hM'.finiteType
  have hiff :
      FinitePresentationRelativeTo R A M ↔
        ∀ n : ℕ,
          let P := MvPolynomial (Fin n) R
          ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
            let _ : Module P M := Module.compHom M α.toRingHom
            Module.FinitePresentation P M :=
    FinitePresentationRelativeTo.iff_overEveryPolynomialPresentation
  refine hiff.2 ?_
  intro n
  dsimp
  intro α hα
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Module P M' := Module.compHom M' α.toRingHom
  letI : Module P M := Module.compHom M α.toRingHom
  letI : Module P M'' := Module.compHom M'' α.toRingHom
  letI : IsScalarTower P A M' := IsScalarTower.of_compHom P A M'
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  letI : IsScalarTower P A M'' := IsScalarTower.of_compHom P A M''
  letI : Module.FinitePresentation P M' := by
    simpa [P] using hM'.overPolynomialPresentation n α hα
  letI : Module.FinitePresentation P M'' := by
    simpa [P] using hM''.overPolynomialPresentation n α hα
  have hfgP : Function.Exact (f.restrictScalars P) (g.restrictScalars P) := by
    simpa using hfg
  exact finitePresentation_of_exact
    (f.restrictScalars P) (g.restrictScalars P)
    (by simpa using hf) (by simpa using hg) hfgP

end

-- Proof sketch: again use Lemma `15.81.1` to reduce to an arbitrary polynomial presentation
-- `P → A`. The middle term becomes finitely presented over `P`, while finiteness of `M'` over `A`
-- restricts to finiteness over `P` because `A` is finite type over `P`. Lemma `10.5.3 (2)` then
-- gives finite presentation of the quotient over `P`.
/-- Lemma 15.81.9 (2): for a finite type ring map `R → A` and a short exact sequence
`0 → M' → M → M'' → 0` of `A`-modules, if `M'` is a finite `A`-module and `M` is finitely
presented relative to `R`, then `M''` is finitely presented relative to `R`. -/
theorem finitePresentationRelativeTo_of_surjective_of_exact
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'')
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM'_finite : Module.Finite A M') (hM : FinitePresentationRelativeTo R A M) :
    FinitePresentationRelativeTo R A M'' := by
  letI : Algebra.FiniteType R A := hM.finiteType
  have hiff :
      FinitePresentationRelativeTo R A M'' ↔
        ∀ n : ℕ,
          let P := MvPolynomial (Fin n) R
          ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
            let _ : Module P M'' := Module.compHom M'' α.toRingHom
            Module.FinitePresentation P M'' :=
    FinitePresentationRelativeTo.iff_overEveryPolynomialPresentation
  refine hiff.2 ?_
  intro n
  dsimp
  intro α hα
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Algebra.FiniteType P A := by
    rw [← RingHom.finiteType_algebraMap]
    simpa [P] using RingHom.FiniteType.of_surjective (algebraMap P A) hα
  letI : Module P M' := Module.compHom M' α.toRingHom
  letI : Module P M := Module.compHom M α.toRingHom
  letI : Module P M'' := Module.compHom M'' α.toRingHom
  letI : IsScalarTower P A M' := IsScalarTower.of_compHom P A M'
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  letI : IsScalarTower P A M'' := IsScalarTower.of_compHom P A M''
  letI : Module.FinitePresentation P M := by
    simpa [P] using hM.overPolynomialPresentation n α hα
  letI : Module.Finite A M' := hM'_finite
  letI : Module.Finite P A := by
    simpa [AlgHom.Finite, RingHom.Finite] using AlgHom.Finite.of_surjective α hα
  letI : Module.Finite P M' := Module.Finite.trans A M'
  have hfgP : Function.Exact (f.restrictScalars P) (g.restrictScalars P) := by
    simpa using hfg
  exact finitePresentation_of_surjective_of_exact
    (f.restrictScalars P) (g.restrictScalars P) (by simpa using hg) hfgP

end Module

end

/-! ### Lemma_15_81_10 (from Chap15) -/
universe u v w x

section

/-
Domain-style sampling:
- primary domain: relative finite presentation of modules over a finite type algebra;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `Module.finitePresentation_of_split_exact`,
  `Module.FinitePresentation.prod`;
- best owner abstraction: the source-facing predicate `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of `A` over `R` together with finite
  presentation of the relevant module over that polynomial ring;
- derived API: stability of relative finite presentation under the split projections onto the two
  direct summands of a product.

Source/core/bridge triage:
- `source-facing`: the statement that relative finite presentation of `M × M'` forces the same
  property for both summands;
- `core/canonical`: `Module.FinitePresentationRelativeTo` and mathlib's split-exact theorem
  `Module.finitePresentation_of_split_exact`;
- `bridge/view`: the proof below unpacks one witness for the source-facing owner and applies the
  core split-exact result over that witness ring before repackaging the same presentation. -/
variable {R : Type u} {A : Type v} {M : Type w} {M' : Type x}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup M'] [Module A M']

namespace Module

-- Proof sketch: choose a surjective polynomial presentation of `A` over `R` witnessing that
-- `M × M'` is relatively finitely presented. Over the polynomial ring, finite presentation is
-- stable under split direct summands, so apply the projections `M × M' → M` and `M × M' → M'`
-- together with their standard sections, then repackage the same presentation witness.
/-- Lemma 15.81.10: if `M × M'` is finitely presented relative to `R` as an `A`-module, then both
`M` and `M'` are finitely presented relative to `R`. -/
theorem finitePresentationRelativeTo_summands_of_prod
    (h : Module.FinitePresentationRelativeTo R A (M × M')) :
    Module.FinitePresentationRelativeTo R A M ∧ Module.FinitePresentationRelativeTo R A M' := by
  rcases h with ⟨n, α, hα, hprod⟩
  let P := MvPolynomial (Fin n) R
  letI : Module P M := Module.compHom M α.toRingHom
  letI : Module P M' := Module.compHom M' α.toRingHom
  letI : Module P (M × M') := Module.compHom (M × M') α.toRingHom
  letI : Module.FinitePresentation P (M × M') := hprod
  constructor <;> refine ⟨n, α, hα, ?_⟩
  · exact Module.finitePresentation_of_split_exact
      (LinearMap.inl P M M') (LinearMap.snd P M M') (LinearMap.inr P M M')
      rfl LinearMap.inl_injective Function.Exact.inl_snd
  · exact Module.finitePresentation_of_split_exact
      (LinearMap.inr P M M') (LinearMap.fst P M M') (LinearMap.inl P M M')
      rfl LinearMap.inr_injective Function.Exact.inr_fst

-- Proof sketch: apply `finitePresentationRelativeTo_summands_of_prod` to `M × M'` and take the
-- first projection of the resulting conjunction.
/-- If `M × M'` is finitely presented relative to `R`, then `M` is finitely presented relative to
`R`. -/
theorem finitePresentationRelativeTo_left_of_prod
    (h : Module.FinitePresentationRelativeTo R A (M × M')) :
    Module.FinitePresentationRelativeTo R A M :=
  (finitePresentationRelativeTo_summands_of_prod h).1

-- Proof sketch: apply `finitePresentationRelativeTo_summands_of_prod` to `M × M'` and take the
-- second projection of the resulting conjunction.
/-- If `M × M'` is finitely presented relative to `R`, then `M'` is finitely presented relative to
`R`. -/
theorem finitePresentationRelativeTo_right_of_prod
    (h : Module.FinitePresentationRelativeTo R A (M × M')) :
    Module.FinitePresentationRelativeTo R A M' :=
  (finitePresentationRelativeTo_summands_of_prod h).2

end Module

end
