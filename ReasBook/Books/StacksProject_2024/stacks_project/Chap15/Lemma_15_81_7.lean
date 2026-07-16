import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_81_2

-- Declarations for this item will be appended below by the statement pipeline.

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
