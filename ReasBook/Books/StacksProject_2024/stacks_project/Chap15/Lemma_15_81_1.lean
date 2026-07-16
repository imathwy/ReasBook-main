import StacksProject_2024.stacks_project.Chap10.Lemma_10_36_23
import StacksProject_2024.stacks_project.Chap15.Definition_15_81_2

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
          Module.FinitePresentation P M := by
  constructor
  · intro hM
    rcases hM with ⟨n₀, α₀, hα₀, hP₀M⟩
    intro n₁
    let P₁ := MvPolynomial (Fin n₁) R
    change ∀ (α₁ : P₁ →ₐ[R] A), Function.Surjective α₁ →
      let _ : Module P₁ M := Module.compHom M α₁.toRingHom
      Module.FinitePresentation P₁ M
    intro α₁ hα₁
    let P₀ := MvPolynomial (Fin n₀) R
    classical
    -- Choose lifts of the variables of the witness presentation through the new surjection.
    let lifts : Fin n₀ → P₁ := fun i ↦ Classical.choose (hα₁ (α₀ (MvPolynomial.X i)))
    have hlifts : ∀ i : Fin n₀, α₁ (lifts i) = α₀ (MvPolynomial.X i) := fun i ↦
      Classical.choose_spec (hα₁ (α₀ (MvPolynomial.X i)))
    let β : P₀ →ₐ[R] P₁ := MvPolynomial.aeval lifts
    have hcomp : α₁.comp β = α₀ := by
      -- The comparison map is determined by its values on the polynomial variables.
      apply MvPolynomial.algHom_ext
      intro i
      simp [β, hlifts i]
    letI : Algebra P₀ P₁ := β.toAlgebra
    letI : Module P₀ M := Module.compHom M α₀.toRingHom
    letI : Module P₁ M := Module.compHom M α₁.toRingHom
    letI : IsScalarTower R P₀ P₁ := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R P₁ r = β (algebraMap R P₀ r)
      exact (β.commutes r).symm
    letI : IsScalarTower P₀ P₁ M := IsScalarTower.of_algebraMap_smul fun p m ↦ by
      -- The transported `P₀`-action agrees with the original witness action on `M`.
      change α₁ (β p) • m = α₀ p • m
      simpa using congrArg (fun x : A ↦ x • m) (AlgHom.congr_fun hcomp p)
    letI : Algebra.FiniteType P₀ P₁ := Algebra.FiniteType.of_restrictScalars_finiteType R P₀ P₁
    letI : Module.FinitePresentation P₀ M := by
      simpa [P₀] using hP₀M
    -- Finite presentation ascends along the finite type comparison map `P₀ → P₁`.
    simpa [P₁] using
      (Module.FinitePresentation.of_restrictScalars_finiteType P₀ : Module.FinitePresentation P₁ M)
  · intro h
    -- Any one surjective polynomial presentation of the finite type algebra `A` gives a witness.
    obtain ⟨n, α, hα⟩ :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
    refine ⟨n, α, hα, ?_⟩
    simpa using h n α hα

/-- Helper for Lemma 15.81.1: lifting a polynomial presentation along `ULift` preserves
surjectivity. -/
lemma ulift_mvPolynomial_presentation_surjective
    {n : ℕ} {α : MvPolynomial (Fin n) R →ₐ[R] A} (hα : Function.Surjective α) :
    Function.Surjective
      (α.comp
        (ULift.algEquiv : ULift.{x} (MvPolynomial (Fin n) R) ≃ₐ[R] MvPolynomial (Fin n) R).toAlgHom) := by
  -- Lift a preimage through the original surjective polynomial presentation.
  intro a
  rcases hα a with ⟨p, rfl⟩
  exact ⟨ULift.up p, rfl⟩

/-- Helper for Lemma 15.81.1: the `ULift` of a finite-variable polynomial ring is still a
finitely presented `R`-algebra. -/
lemma ulift_mvPolynomial_finitePresentation_over_base (n : ℕ) :
    Algebra.FinitePresentation R (ULift.{x} (MvPolynomial (Fin n) R)) := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra.FinitePresentation R P := by
    -- The original polynomial ring is finitely presented over the base ring.
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := R) (A := R) (Fin n))
  let g : P →ₐ[P] ULift.{x} P := Algebra.ofId P (ULift.{x} P)
  have hg : Function.Surjective g := by
    -- Every lifted polynomial has an obvious preimage given by `down`.
    intro q
    refine ⟨q.down, ?_⟩
    cases q
    rfl
  have hginj : Function.Injective g := by
    -- The map is just `ULift.up`, so `down` recovers the source element.
    intro p q hpq
    exact congrArg ULift.down hpq
  have hgker : (RingHom.ker g.toRingHom).FG := by
    -- The kernel is trivial because the `ULift` map is injective.
    have hker_eq : RingHom.ker g.toRingHom = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot g.toRingHom).mp hginj
    rw [hker_eq]
    exact Submodule.fg_bot
  letI : Algebra.FinitePresentation P (ULift.{x} P) :=
    Algebra.FinitePresentation.of_surjective (f := g) hg hgker
  -- Compose finite presentation along `R → P → ULift P`.
  exact Algebra.FinitePresentation.trans R P (ULift.{x} P)

/-- Helper for Lemma 15.81.1: finite presentation over a polynomial presentation is equivalent to
finite presentation over its `ULift` presentation. -/
lemma finitePresentation_iff_ulift_mvPolynomial_presentation
    (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    let P := MvPolynomial (Fin n) R
    let αup : ULift.{x} P →ₐ[R] A :=
      α.comp (ULift.algEquiv : ULift.{x} P ≃ₐ[R] P).toAlgHom
    let _ : Module P M := Module.compHom M α.toRingHom
    let _ : Module (ULift.{x} P) M := Module.compHom M αup.toRingHom
    Module.FinitePresentation P M ↔ Module.FinitePresentation (ULift.{x} P) M := by
  let P := MvPolynomial (Fin n) R
  let αup : ULift.{x} P →ₐ[R] A :=
    α.comp (ULift.algEquiv : ULift.{x} P ≃ₐ[R] P).toAlgHom
  let moduleP : Module P M := Module.compHom M α.toRingHom
  let moduleUp : Module (ULift.{x} P) M := Module.compHom M αup.toRingHom
  let tower : IsScalarTower P (ULift.{x} P) M := IsScalarTower.of_algebraMap_smul fun p m ↦ by
    -- The lifted action agrees with the original action because `αup` extends `α`.
    change αup (algebraMap P (ULift.{x} P) p) • m = α p • m
    rfl
  let finiteUp : Module.Finite P (ULift.{x} P) := by
    have hsurj : Function.Surjective (algebraMap P (ULift.{x} P)) := by
      -- Every lifted polynomial comes from its `down` representative.
      intro q
      refine ⟨q.down, ?_⟩
      cases q
      rfl
    exact Module.Finite.of_surjective (Algebra.linearMap P (ULift.{x} P)) hsurj
  let g : P →ₐ[P] ULift.{x} P := Algebra.ofId P (ULift.{x} P)
  let algFpUp : Algebra.FinitePresentation P (ULift.{x} P) := by
    have hg : Function.Surjective g := by
      -- The algebra map onto the `ULift` is surjective by `down`.
      intro q
      refine ⟨q.down, ?_⟩
      cases q
      rfl
    have hginj : Function.Injective g := by
      -- Injectivity follows because `down` is a left inverse.
      intro p q hpq
      exact congrArg ULift.down hpq
    have hgker : (RingHom.ker g.toRingHom).FG := by
      -- Again the kernel is zero, so it is finitely generated.
      have hker_eq : RingHom.ker g.toRingHom = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot g.toRingHom).mp hginj
      rw [hker_eq]
      exact Submodule.fg_bot
    exact Algebra.FinitePresentation.of_surjective (f := g) hg hgker
  letI : Module P M := moduleP
  letI : Module (ULift.{x} P) M := moduleUp
  -- Compare the two module structures using the finite, finitely presented algebra map `P → ULift P`.
  have hiff : Module.FinitePresentation P M ↔ Module.FinitePresentation (ULift.{x} P) M :=
    @Module.FinitePresentation.iff_of_finite_finitePresentation P (ULift.{x} P) M
      inferInstance inferInstance inferInstance inferInstance moduleUp moduleP tower finiteUp algFpUp
  exact hiff

/-- Lemma 15.81.1, cover formulation: for a finite type ring map `R → A` and an `A`-module `M`,
`M` is finitely presented over some polynomial presentation of `A` if and only if for every
surjection `A' → A` with `A'` a finitely presented `R`-algebra, `M` is finitely presented as an
`A'`-module. -/
theorem iff_overAnyFinitelyPresentedCover :
    Module.FinitePresentationRelativeTo R A M ↔
      ∀ (A' : Type (max u x)) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
        (f : A' →ₐ[R] A) (_ : Function.Surjective f),
          let _ : Module A' M := Module.compHom M f.toRingHom
          Module.FinitePresentation A' M := by
  constructor
  · intro hM A' _ _ _
    change ∀ (f : A' →ₐ[R] A), Function.Surjective f →
      let _ : Module A' M := Module.compHom M f.toRingHom
      Module.FinitePresentation A' M
    intro f hf
    obtain ⟨n, β, hβ, hkerβ⟩ := Algebra.FinitePresentation.out (R := R) (A := A')
    let Q := MvPolynomial (Fin n) R
    let γ : Q →ₐ[R] A := f.comp β
    have hγ : Function.Surjective γ := by
      intro a
      rcases hf a with ⟨a', rfl⟩
      rcases hβ a' with ⟨q, rfl⟩
      exact ⟨q, rfl⟩
    letI : Algebra Q A' := β.toAlgebra
    letI : Module A' M := Module.compHom M f.toRingHom
    letI : Module Q M := Module.compHom M γ.toRingHom
    letI : IsScalarTower Q A' M := IsScalarTower.of_algebraMap_smul fun q m ↦ by
      -- The `Q`-action on `M` is exactly the one obtained by composing through `A'`.
      change f (β q) • m = γ q • m
      rfl
    letI : Module.Finite Q A' := Module.Finite.of_surjective (Algebra.linearMap Q A') hβ
    letI : Algebra.FinitePresentation Q A' := by
      let g : Q →ₐ[Q] A' := Algebra.ofId Q A'
      have hg : Function.Surjective g := by
        simpa [g] using hβ
      have hgker : (RingHom.ker g.toRingHom).FG := by
        simpa [g] using hkerβ
      exact Algebra.FinitePresentation.of_surjective (f := g) hg hgker
    have hQM : Module.FinitePresentation Q M := by
      -- First move to the polynomial presentation of the cover, then descend to `A'`.
      simpa [Q, γ] using
        (iff_overEveryPolynomialPresentation.mp hM n γ hγ)
    exact Module.FinitePresentation.iff_of_finite_finitePresentation.mp hQM
  · intro h
    -- Route correction: the reverse direction must pass through `ULift P` so the quantified cover
    -- lives in the universe `Type (max u x)`, then descend back to `P`.
    obtain ⟨n, α, hα⟩ :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
    let P := MvPolynomial (Fin n) R
    let αup : ULift.{x} P →ₐ[R] A :=
      α.comp (ULift.algEquiv : ULift.{x} P ≃ₐ[R] P).toAlgHom
    have hαup : Function.Surjective αup :=
      ulift_mvPolynomial_presentation_surjective (R := R) (A := A) hα
    letI : Algebra.FinitePresentation R (ULift.{x} P) :=
      ulift_mvPolynomial_finitePresentation_over_base (R := R) n
    letI : Module P M := Module.compHom M α.toRingHom
    letI : Module (ULift.{x} P) M := Module.compHom M αup.toRingHom
    have hUp : Module.FinitePresentation (ULift.{x} P) M := by
      -- Apply the cover hypothesis to the same-universe `ULift` presentation.
      simpa [P, αup] using h (ULift.{x} P) αup hαup
    have hP : Module.FinitePresentation P M := by
      -- Descend finite presentation across the finite finitely presented map `P → ULift P`.
      exact (finitePresentation_iff_ulift_mvPolynomial_presentation
        (R := R) (A := A) (M := M) n α).2 hUp
    -- Package the original polynomial presentation together with the descended witness.
    refine ⟨n, α, hα, ?_⟩
    simpa [P] using hP

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
    (A' : Type (max u x)) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
    (f : A' →ₐ[R] A) (hf : Function.Surjective f) :
    let _ : Module A' M := Module.compHom M f.toRingHom
    Module.FinitePresentation A' M := by
  letI : Algebra.FiniteType R A := hM.finiteType
  have hiff :
      Module.FinitePresentationRelativeTo R A M ↔
        ∀ (A' : Type (max u x)) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
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
