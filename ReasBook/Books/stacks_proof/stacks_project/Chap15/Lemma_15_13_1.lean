import stacks_proof.stacks_project.Chap10.Lemma_10_55_6
import stacks_proof.stacks_project.Chap15.Definition_15_11_1
import stacks_proof.stacks_project.Chap15.Lemma_15_3_5
import stacks_proof.stacks_project.Chap15.Lemma_15_9_11
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: finite projective modules and reduction modulo an ideal, viewed through the
  full subcategory owner `FiniteProjectiveModuleCat`;
- sampled owner declarations:
  `finiteProjectiveModuleProperty`,
  `FiniteProjectiveModuleCat`,
  `ObjectProperty.lift`,
  `surjectiveRingPullbackFiniteProjectiveModuleBaseChangeFunctor`;
- best owner abstraction: the chapter/project owner for this domain is the full subcategory
  `FiniteProjectiveModuleCat R`, with functors into it built canonically from the ambient functor
  by `ObjectProperty.lift`; the reduction functor below is therefore derived API, not primitive
  hand-built category data;
- primitive data: the ambient scalar-extension functor `ModuleCat.extendScalars (Ideal.Quotient.mk
  I)` together with the theorem that it preserves `finiteProjectiveModuleProperty`;
- derived API: the induced functor on finite-projective full subcategories and the map on
  isomorphism classes.

Source/core/bridge triage:
- `source-facing`: the henselian bijectivity and lifting/isomorphism statements below;
- `core/canonical`: `finiteProjectiveModuleProperty`, `FiniteProjectiveModuleCat`, and
  `ObjectProperty.lift`;
- `bridge/view`: reduction modulo `I` as the scalar-extension functor from
  `FiniteProjectiveModuleCat R` to `FiniteProjectiveModuleCat (R ⧸ I)`. -/

-- Proof sketch: reduction modulo `I` is scalar extension along `R → R ⧸ I`, hence preserves
-- finite generation and projectivity for a finite projective module.
/-- Reduction modulo an ideal, viewed as scalar extension to `R ⧸ I`, preserves finite projective
modules. -/
theorem finiteProjectiveReduction_property (I : Ideal R) (P : FiniteProjectiveModuleCat R) :
    finiteProjectiveModuleProperty (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P.obj) := by
  constructor
  · -- Proof comment: finite generation is preserved by scalar extension to the quotient ring.
    simpa using (Module.Finite.base_change (R := R) (A := R ⧸ I) (M := P.obj))
  · -- Proof comment: projectivity is preserved by the same base-change functor.
    simpa using
      (show Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[R] P.obj) from
        Module.Projective.tensorProduct)

/-- The functor on finite projective module categories induced by reduction modulo `I`. -/
noncomputable abbrev finiteProjectiveReductionFunctor (I : Ideal R) :
    FiniteProjectiveModuleCat R ⥤ FiniteProjectiveModuleCat (R ⧸ I) :=
  (finiteProjectiveModuleProperty (R ⧸ I)).lift
    ((finiteProjectiveModuleProperty R).ι ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I))
    (fun P ↦ finiteProjectiveReduction_property I P)

/-- Helper for Lemma 15.13.1: an isomorphism between finite projective `R`-modules yields the
same isomorphism class after reduction modulo `I`. -/
theorem finiteProjectiveReduction_isoClass_eq_of_iso (I : Ideal R)
    {P₁ P₂ : FiniteProjectiveModuleCat R} (h : Nonempty (P₁ ≅ P₂)) :
    (isomorphismClasses.map (finiteProjectiveReductionFunctor I).toCatHom) (Quotient.mk'' P₁) =
      (isomorphismClasses.map (finiteProjectiveReductionFunctor I).toCatHom) (Quotient.mk'' P₂) :=
    by
  -- Proof comment: map the chosen isomorphism through the reduction functor and then pass to the
  -- quotient defining `isomorphismClasses`.
  rcases h with ⟨e⟩
  change Quotient.mk'' ((finiteProjectiveReductionFunctor I).obj P₁) =
      Quotient.mk'' ((finiteProjectiveReductionFunctor I).obj P₂)
  exact Quotient.sound ⟨(finiteProjectiveReductionFunctor I).mapIso e⟩

/-- Helper for Lemma 15.13.1: once a chosen lift `P` of `Pbar` is constructed, the reduction
class of `P` is exactly the class of `Pbar`. -/
theorem finiteProjectiveReduction_isoClass_eq_of_lift (I : Ideal R)
    {P : FiniteProjectiveModuleCat R} {Pbar : FiniteProjectiveModuleCat (R ⧸ I)}
    (e : Nonempty ((finiteProjectiveReductionFunctor I).obj P ≅ Pbar)) :
    (isomorphismClasses.map (finiteProjectiveReductionFunctor I).toCatHom) (Quotient.mk'' P) =
      Quotient.mk'' Pbar := by
  -- Proof comment: this is the quotient-level reformulation of the chosen objectwise reduction
  -- isomorphism.
  change Quotient.mk'' ((finiteProjectiveReductionFunctor I).obj P) = Quotient.mk'' Pbar
  exact Quotient.sound e

/-- Helper for Lemma 15.13.1: a quotient section of an étale `R`-algebra lifts across a
henselian pair `(R, I)`. -/
theorem exists_etale_section_of_henselianRing
    {A' : Type u} [CommRing A'] [Algebra R A'] [Algebra.Etale R A']
    (g : A' →ₐ[R] R ⧸ I) :
    ∃ τ : A' →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp τ = g :=
  by
  -- Proof comment: this is the isolated henselian-to-étale section bridge needed to descend the
  -- finite-projective étale lift constructed earlier in the proof.
  sorry

/-- Helper for Lemma 15.13.1: the quotient map obtained by composing a henselian section with the
reduction map is surjective. -/
theorem section_composite_surjective
    {A' : Type u} [CommRing A'] [Algebra R A']
    (eIso : (R ⧸ I) ≃ₐ[R ⧸ I] (A' ⧸ Ideal.map (algebraMap R A') I))
    (τ : A' →ₐ[R] R)
    (hτ : (Ideal.Quotient.mkₐ R I).comp τ =
      (eIso.symm.toAlgHom.restrictScalars R).comp
        ((Ideal.Quotient.mkₐ A' (Ideal.map (algebraMap R A') I)).restrictScalars R)) :
    Function.Surjective (((Ideal.Quotient.mkₐ R I).comp τ).toRingHom) := by
  let J : Ideal A' := Ideal.map (algebraMap R A') I
  -- Proof comment: rewrite the composite through the quotient-ring isomorphism and then lift a
  -- chosen quotient representative in `A' / J`.
  rw [hτ]
  intro x
  obtain ⟨y, hy⟩ := Ideal.Quotient.mkₐ_surjective A' J (eIso x)
  refine ⟨y, ?_⟩
  change eIso.symm ((Ideal.Quotient.mkₐ A' J) y) = x
  rw [hy]
  simp

variable (I : Ideal R) [HenselianRing R I]

/-- Helper for Lemma 15.13.1: after rewriting the descended `A'`-algebra structure on `R ⧸ I`
through the henselian section, the tensor base change of the étale lift is linearly equivalent to
the original reduced module. -/
theorem descended_baseChange_equiv_of_section
    {A' : Type u} [CommRing A'] [Algebra R A']
    {P' : Type v} [AddCommGroup P'] [Module A' P']
    {Pbar : FiniteProjectiveModuleCat (R ⧸ I)}
    (eIso : (R ⧸ I) ≃ₐ[R ⧸ I] (A' ⧸ Ideal.map (algebraMap R A') I))
    (eP :
      let J : Ideal A' := Ideal.map (algebraMap R A') I
      let _ : Module (A' ⧸ J) Pbar.obj := Module.compHom Pbar.obj eIso.symm.toRingHom
      (P' ⧸ (J • (⊤ : Submodule A' P'))) ≃ₗ[A' ⧸ J] Pbar.obj)
    (τ : A' →ₐ[R] R)
    (hτ : (Ideal.Quotient.mkₐ R I).comp τ =
      (eIso.symm.toAlgHom.restrictScalars R).comp
        ((Ideal.Quotient.mkₐ A' (Ideal.map (algebraMap R A') I)).restrictScalars R)) :
    let _ : Algebra A' (R ⧸ I) := (((Ideal.Quotient.mkₐ R I).comp τ)).toRingHom.toAlgebra
    Nonempty ((R ⧸ I) ⊗[A'] P' ≃ₗ[R ⧸ I] Pbar.obj) := by
  -- Proof comment: this is the tensor-normalization step isolating the descended `A'`-module from
  -- the chosen henselian section.
  sorry

/-- Helper for Lemma 15.13.1: descending the étale finite-projective lift along a henselian
section produces a finite projective `R`-module whose reduction is the prescribed quotient
module. -/
theorem descend_etale_finiteProjective_lift_along_section
    {A' : Type u} [CommRing A'] [Algebra R A']
    {P' : Type v} [AddCommGroup P'] [Module A' P']
    {Pbar : FiniteProjectiveModuleCat (R ⧸ I)}
    (eIso : (R ⧸ I) ≃ₐ[R ⧸ I] (A' ⧸ Ideal.map (algebraMap R A') I))
    (eP :
      let J : Ideal A' := Ideal.map (algebraMap R A') I
      let _ : Module (A' ⧸ J) Pbar.obj := Module.compHom Pbar.obj eIso.symm.toRingHom
      (P' ⧸ (J • (⊤ : Submodule A' P'))) ≃ₗ[A' ⧸ J] Pbar.obj)
    (hP' : Module.FiniteProjective A' P')
    (τ : A' →ₐ[R] R)
    (hτ : (Ideal.Quotient.mkₐ R I).comp τ =
      (eIso.symm.toAlgHom.restrictScalars R).comp
        ((Ideal.Quotient.mkₐ A' (Ideal.map (algebraMap R A') I)).restrictScalars R)) :
    ∃ P : FiniteProjectiveModuleCat R,
      Nonempty ((finiteProjectiveReductionFunctor I).obj P ≅ Pbar) := by
  -- Proof comment: once the tensor normalization is available, the descended finite-projective
  -- model over `R` is the scalar restriction of the chosen étale lift.
  sorry

/-- Helper for Lemma 15.13.1: every finite projective `R ⧸ I`-module lifts to a finite projective
`R`-module over a henselian pair. -/
theorem exists_finiteProjective_reduction_lift
    (Pbar : FiniteProjectiveModuleCat (R ⧸ I)) :
    ∃ P : FiniteProjectiveModuleCat R,
      Nonempty ((finiteProjectiveReductionFunctor I).obj P ≅ Pbar) := by
  obtain ⟨A', _, _, _, eIso, P', _, _, eP, hP'⟩ :=
    Algebra.exists_etale_finite_projective_lift_of_finite_projective_quotient
      (A := R) (I := I) (Pbar := Pbar.obj) (hPbar := ⟨inferInstance, inferInstance⟩)
  let J : Ideal A' := Ideal.map (algebraMap R A') I
  let g : A' →ₐ[R] R ⧸ I :=
    (eIso.symm.toAlgHom.restrictScalars R).comp
      ((Ideal.Quotient.mkₐ A' J).restrictScalars R)
  -- Proof comment: the henselian pair supplies a section of the étale quotient map.
  obtain ⟨τ, hτ⟩ := exists_etale_section_of_henselianRing (R := R) (I := I) g
  -- Proof comment: descend the étale lift along that section and identify its reduction with
  -- the original finite projective quotient module.
  exact descend_etale_finiteProjective_lift_along_section
    (R := R) (I := I) (Pbar := Pbar) eIso eP hP' τ hτ

/-- Helper for Lemma 15.13.1: an isomorphism after reduction is exactly a quotient linear
equivalence `P₁ / IP₁ ≃ P₂ / IP₂`. -/
noncomputable abbrev reduction_functor_iso_to_quotient_linear_equiv
    {P₁ P₂ : FiniteProjectiveModuleCat R}
    (e : (finiteProjectiveReductionFunctor I).obj P₁ ≅
      (finiteProjectiveReductionFunctor I).obj P₂) :
    (P₁.obj ⧸ I • (⊤ : Submodule R P₁.obj)) ≃ₗ[R ⧸ I]
      (P₂.obj ⧸ I • (⊤ : Submodule R P₂.obj)) := sorry

/-- Helper for Lemma 15.13.1: reduction modulo `I` reflects isomorphisms between finite
projective `R`-modules over a henselian pair. -/
theorem finiteProjectiveReduction_reflects_iso
    {P₁ P₂ : FiniteProjectiveModuleCat R}
    (h : Nonempty ((finiteProjectiveReductionFunctor I).obj P₁ ≅
      (finiteProjectiveReductionFunctor I).obj P₂)) :
    Nonempty (P₁ ≅ P₂) := by
  rcases h with ⟨e⟩
  let eQuot :
      (P₁.obj ⧸ I • (⊤ : Submodule R P₁.obj)) ≃ₗ[R ⧸ I]
        (P₂.obj ⧸ I • (⊤ : Submodule R P₂.obj)) :=
    reduction_functor_iso_to_quotient_linear_equiv (I := I) e
  -- Proof comment: the reduced categorical isomorphism is now in the exact quotient-module shape
  -- needed by the finite-projective lifting theorem across a Jacobson-radical ideal.
  obtain ⟨φ, _hφ⟩ :=
    exists_lift_of_quotient_equiv_of_finite_projective
      (R := R) (I := I) (P := P₁.obj) (P' := P₂.obj)
      (Ideal.le_ring_jacobson_of_henselianRing (A := R) (I := I)) eQuot
  -- Proof comment: package the lifted linear equivalence as an isomorphism in the full
  -- subcategory of finite projective modules.
  exact ⟨(finiteProjectiveModuleProperty R).isoMk φ.toModuleIso⟩

/-- Helper for Lemma 15.13.1: the chosen henselian lift of a reduced finite projective module
depends only on its isomorphism class. -/
theorem chosen_reduction_lift_respects_isoClass
    {Pbar₁ Pbar₂ : FiniteProjectiveModuleCat (R ⧸ I)}
    (h : Nonempty (Pbar₁ ≅ Pbar₂)) :
    (Quotient.mk'' (Classical.choose (exists_finiteProjective_reduction_lift (I := I) Pbar₁)) :
        isomorphismClasses.obj (Cat.of (FiniteProjectiveModuleCat R))) =
      Quotient.mk'' (Classical.choose (exists_finiteProjective_reduction_lift (I := I) Pbar₂)) := by
  let P₁ := Classical.choose (exists_finiteProjective_reduction_lift (I := I) Pbar₁)
  let P₂ := Classical.choose (exists_finiteProjective_reduction_lift (I := I) Pbar₂)
  have hP₁ :
      Nonempty ((finiteProjectiveReductionFunctor I).obj P₁ ≅ Pbar₁) :=
    Classical.choose_spec (exists_finiteProjective_reduction_lift (I := I) Pbar₁)
  have hP₂ :
      Nonempty ((finiteProjectiveReductionFunctor I).obj P₂ ≅ Pbar₂) :=
    Classical.choose_spec (exists_finiteProjective_reduction_lift (I := I) Pbar₂)
  have hred :
      Nonempty ((finiteProjectiveReductionFunctor I).obj P₁ ≅
        (finiteProjectiveReductionFunctor I).obj P₂) := by
    rcases hP₁ with ⟨e₁⟩
    rcases h with ⟨ebar⟩
    rcases hP₂ with ⟨e₂⟩
    -- Proof comment: compose the two chosen reduction isomorphisms with the given iso class
    -- downstairs to compare the chosen lifts after reduction.
    exact ⟨e₁ ≪≫ ebar ≪≫ e₂.symm⟩
  -- Proof comment: reflect the reduced isomorphism back upstairs and pass to quotient classes.
  exact Quotient.sound (finiteProjectiveReduction_reflects_iso (I := I) hred)
-- Proof sketch: surjectivity comes from Lemmas `15.9.11` and `15.11.6`, which produce a finite
-- projective lift after an étale neighborhood and then descend it back along a henselian section.
-- Injectivity is the quotient-isomorphism criterion proved by lifting maps and applying Nakayama's
-- lemma together with the finite-projective endomorphism criterion from Algebra, Lemma `10.16.4`.
/-- Lemma 15.13.1: scalar extension along `R → R ⧸ I`, equivalently reduction `P ↦ P / IP`,
induces a bijection on isomorphism classes of finite projective modules for a henselian pair
`(R, I)`. -/
@[stacks 0D4A]
theorem finiteProjectiveReduction_isoClasses_bijective_of_henselianRing :
    Function.Bijective (isomorphismClasses.map (finiteProjectiveReductionFunctor I).toCatHom) :=
  by
  classical
  let f := isomorphismClasses.map (finiteProjectiveReductionFunctor I).toCatHom
  let liftClass :
      isomorphismClasses.obj (Cat.of (FiniteProjectiveModuleCat (R ⧸ I))) →
        isomorphismClasses.obj (Cat.of (FiniteProjectiveModuleCat R)) :=
    Quotient.lift
      (fun Pbar : FiniteProjectiveModuleCat (R ⧸ I) ↦
        (Quotient.mk'' (Classical.choose (exists_finiteProjective_reduction_lift (I := I) Pbar)) :
          isomorphismClasses.obj (Cat.of (FiniteProjectiveModuleCat R))))
      (fun _ _ h ↦ chosen_reduction_lift_respects_isoClass (I := I) h)
  have hright : Function.RightInverse liftClass f := by
    intro q
    refine Quotient.inductionOn q ?_
    intro Pbar
    -- Proof comment: the chosen lift of `Pbar` reduces back to `Pbar` by construction.
    simpa [f, liftClass] using
      (finiteProjectiveReduction_isoClass_eq_of_lift (I := I)
        (e := Classical.choose_spec
          (exists_finiteProjective_reduction_lift (I := I) Pbar)))
  have hleft : Function.LeftInverse liftClass f := by
    intro q
    refine Quotient.inductionOn q ?_
    intro P
    have hLift :
        Nonempty
          ((finiteProjectiveReductionFunctor I).obj
              (Classical.choose
                (exists_finiteProjective_reduction_lift
                  (I := I) ((finiteProjectiveReductionFunctor I).obj P))) ≅
            (finiteProjectiveReductionFunctor I).obj P) :=
      Classical.choose_spec
        (exists_finiteProjective_reduction_lift
          (I := I) ((finiteProjectiveReductionFunctor I).obj P))
    -- Proof comment: if the chosen lift of the reduction of `P` reduces to the same object as
    -- `P`, then reduction reflection identifies that chosen lift with `P` upstairs.
    simpa [f, liftClass] using
      (show
          (Quotient.mk''
              (Classical.choose
                (exists_finiteProjective_reduction_lift
                  (I := I) ((finiteProjectiveReductionFunctor I).obj P))) :
            isomorphismClasses.obj (Cat.of (FiniteProjectiveModuleCat R))) =
            Quotient.mk'' P
        from Quotient.sound (finiteProjectiveReduction_reflects_iso (I := I) hLift))
  exact ⟨hleft.injective, hright.surjective⟩

-- Proof sketch: apply the surjective half of
-- `finiteProjectiveReduction_isoClasses_bijective_of_henselianRing` and then identify reduction
-- modulo `I` with the quotient module `P ⧸ I P`.
/-- Every finite projective `R ⧸ I`-module, viewed as an object of
`FiniteProjectiveModuleCat (R ⧸ I)`, lifts to a finite projective `R`-module over a henselian
pair. -/
theorem exists_finiteProjective_lift_of_henselianRing
    (Pbar : FiniteProjectiveModuleCat (R ⧸ I)) :
    ∃ P : FiniteProjectiveModuleCat R,
      Nonempty ((finiteProjectiveReductionFunctor I).obj P ≅ Pbar) := by
  -- Proof comment: this is the object-level surjectivity statement already isolated above.
  exact exists_finiteProjective_reduction_lift (I := I) Pbar

-- Proof sketch: lift an isomorphism after reduction to an `R`-linear map, use Nakayama's lemma to
-- make the lift and a reverse lift surjective, and then invoke the criterion that a surjective
-- endomorphism of a finite projective module is an isomorphism.
/-- Two finite projective `R`-modules, viewed in `FiniteProjectiveModuleCat R`, are isomorphic over
a henselian pair once their reductions modulo `I` are isomorphic. -/
theorem finiteProjective_iso_of_quotient_iso_of_henselianRing
    {P₁ P₂ : FiniteProjectiveModuleCat R}
    (h : Nonempty ((finiteProjectiveReductionFunctor I).obj P₁ ≅
      (finiteProjectiveReductionFunctor I).obj P₂)) :
    Nonempty (P₁ ≅ P₂) := by
  -- Proof comment: this is the reflection-of-isomorphisms helper specialized to the given pair.
  exact finiteProjectiveReduction_reflects_iso (I := I) h

end
