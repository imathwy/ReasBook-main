import StacksProject_2024.stacks_project.Chap10.Lemma_10_5_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_81_1

-- Declarations for this item will be appended below by the statement pipeline.

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
