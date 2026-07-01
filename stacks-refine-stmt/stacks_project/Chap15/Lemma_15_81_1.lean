import stacks_project.Chap15.Definition_15_81_2

-- Declarations for this item will be appended below by the statement pipeline.

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
