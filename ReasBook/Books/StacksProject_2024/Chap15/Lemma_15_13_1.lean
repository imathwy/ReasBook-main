import StacksProject_2024.Chap10.Lemma_10_55_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

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
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P.obj) := sorry

/-- The functor on finite projective module categories induced by reduction modulo `I`. -/
noncomputable abbrev finiteProjectiveReductionFunctor (I : Ideal R) :
    FiniteProjectiveModuleCat R ⥤ FiniteProjectiveModuleCat (R ⧸ I) :=
  (finiteProjectiveModuleProperty (R ⧸ I)).lift
    ((finiteProjectiveModuleProperty R).ι ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I))
    (fun P ↦ finiteProjectiveReduction_property I P)

variable (I : Ideal R) [HenselianRing R I]

-- Proof sketch: surjectivity comes from Lemmas `15.9.11` and `15.11.6`, which produce a finite
-- projective lift after an étale neighborhood and then descend it back along a henselian section.
-- Injectivity is the quotient-isomorphism criterion proved by lifting maps and applying Nakayama's
-- lemma together with the finite-projective endomorphism criterion from Algebra, Lemma `10.16.4`.
/-- Lemma 15.13.1: scalar extension along `R → R ⧸ I`, equivalently reduction `P ↦ P / IP`,
induces a bijection on isomorphism classes of finite projective modules for a henselian pair
`(R, I)`. -/
theorem finiteProjectiveReduction_isoClasses_bijective_of_henselianRing :
    Function.Bijective (isomorphismClasses.map (finiteProjectiveReductionFunctor I).toCatHom) :=
  sorry

-- Proof sketch: apply the surjective half of
-- `finiteProjectiveReduction_isoClasses_bijective_of_henselianRing` and then identify reduction
-- modulo `I` with the quotient module `P ⧸ I P`.
/-- Every finite projective `R ⧸ I`-module, viewed as an object of
`FiniteProjectiveModuleCat (R ⧸ I)`, lifts to a finite projective `R`-module over a henselian
pair. -/
theorem exists_finiteProjective_lift_of_henselianRing
    (Pbar : FiniteProjectiveModuleCat (R ⧸ I)) :
    ∃ P : FiniteProjectiveModuleCat R,
      Nonempty ((finiteProjectiveReductionFunctor I).obj P ≅ Pbar) := sorry

-- Proof sketch: lift an isomorphism after reduction to an `R`-linear map, use Nakayama's lemma to
-- make the lift and a reverse lift surjective, and then invoke the criterion that a surjective
-- endomorphism of a finite projective module is an isomorphism.
/-- Two finite projective `R`-modules, viewed in `FiniteProjectiveModuleCat R`, are isomorphic over
a henselian pair once their reductions modulo `I` are isomorphic. -/
theorem finiteProjective_iso_of_quotient_iso_of_henselianRing
    {P₁ P₂ : FiniteProjectiveModuleCat R}
    (h : Nonempty ((finiteProjectiveReductionFunctor I).obj P₁ ≅
      (finiteProjectiveReductionFunctor I).obj P₂)) :
    Nonempty (P₁ ≅ P₂) := sorry

end
