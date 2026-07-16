import Mathlib
import stacks_proof.stacks_project.Chap18.Definition_18_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped RelativeDerivation
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type u)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.35.2:
- primary domain: naive cotangent complexes of presentations `\mathcal A[E] \to \mathcal B` of
  sheaves of `\mathcal A`-algebras on a fixed site, compared in the derived category of
  `\mathcal B`-module sheaves;
- sampled owner declarations:
  `Sheaf.composeAndSheafify J CommRingCat.free`,
  `Sheaf.adjunction J CommRingCat.adj`,
  `presentationMapOf`,
  `Under`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `DerivedCategory.Q.obj`;
- best owner abstraction: the source-facing primitive data are a sheaf of sets `E` together with a
  map `α : E ⟶ \mathcal B` of underlying sheaves of sets; this induces the presentation
  morphism `presentationMapOf A B E α : A[E] \to B`, whose two-term
  complex is the correct presentationwise input to `presentationNaiveCotangent`;
- derived API: the resulting comparison morphism in `D(\mathcal B)` from the chosen presentation
  to the canonical presentation `\mathcal A[\mathcal B] \to \mathcal B`.

Source/core/bridge triage:
- `source-facing`: the comparison in `D(\mathcal B)` between the naive cotangent complexes of the
  chosen presentation `\mathcal A[E] \to \mathcal B` and the canonical presentation
  `\mathcal A[\mathcal B] \to \mathcal B`;
- `core/canonical`: `presentationMapOf`, `presentationNaiveCotangent`, and `naiveCotangent`;
- `bridge/view`: the localization functor `DerivedCategory.Q`.

This file should therefore keep the source presentation data visible, and expose an actual
comparison morphism in `D(\mathcal B)` rather than only the proposition that two objects are
isomorphic. -/

section

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]
variable [HasBinaryCoproducts (Sheaf J (Type u))]
variable {A : Sheaf J CommRingCat.{u}} {B : Under A}

local notation "ModB" => SheafOfModules (ringSheaf J B.right)
local notation "DModB" => DerivedCategory ModB

local instance : HasDerivedCategory ModB :=
  HasDerivedCategory.standard ModB

private abbrev cotangentSingle₀ : CochainComplex ModB ℤ :=
  (HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj (Ω(B.hom))

private abbrev presentationCotangentSingle
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    CochainComplex ModB ℤ :=
  (HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj
    (Ω(presentationBaseOf A E ≫ presentationMapOf A B E α))

private abbrev naiveCotangentSingle : CochainComplex ModB ℤ :=
  (HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj
    (Ω(presentationBase A B ≫ presentationMap A B))

/-- The naive cotangent complex attached to a presentation of `B` by a sheaf of sets
`α : E ⟶ presentationVariables B`, i.e. to the induced presentation morphism
`presentationMapOf A B E α : A[E] ⟶ B`. -/
abbrev presentationNaiveCotangentOf
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    CochainComplex ModB ℤ :=
  presentationNaiveCotangent
    (presentationBaseOf A E)
    (presentationMapOf A B E α)

/-- Helper for Lemma 18.35.2: the degree `0` term of the chosen-presentation naive cotangent
complex is the corresponding tensor term of relative differentials. -/
private theorem presentationNaiveCotangentOf_X_zero
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    (presentationNaiveCotangentOf E α).X 0 =
      conormalTensorTerm (presentationBaseOf A E) (presentationMapOf A B E α) := by
  rfl

omit [HasWeakSheafify J (Type u)] in
private theorem presentationNaiveCotangent_target_eq
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    Ω(presentationBaseOf A E ≫ presentationMapOf A B E α) = Ω(B.hom) :=
  by
    -- Proof comment: `presentationMapOf` is the `.right` component of a morphism in `Under A`,
    -- so its defining commutativity square already identifies the composite with `B.hom`.
    exact congrArg (fun f ↦ Ω(f)) <|
      Under.w
        ((((Under.costarAdjForget A).homEquiv
            (presentationFreeSheaf E) B).symm
            (((Sheaf.adjunction J CommRingCat.adj).homEquiv E B.right).symm α)))

omit [HasWeakSheafify J (Type u)] in
private theorem naiveCotangent_target_eq :
    Ω(presentationBase A B ≫ presentationMap A B) = Ω(B.hom) :=
  by
    -- Proof comment: the canonical presentation is the chosen-presentation construction with
    -- generators `presentationVariables B` and the identity generator map.
    simpa [presentationBase, presentationMap] using
      presentationNaiveCotangent_target_eq
        (A := A) (B := B) (E := presentationVariables B) (α := 𝟙 _)

private theorem presentationCotangentSingle_eq
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    presentationCotangentSingle E α = cotangentSingle₀ :=
  congrArg ((HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj)
    (presentationNaiveCotangent_target_eq E α)

private theorem naiveCotangentSingle_eq :
    (naiveCotangentSingle : CochainComplex ModB ℤ) = cotangentSingle₀ :=
  congrArg ((HomologicalComplex.single ModB (ComplexShape.up ℤ) 0).obj)
    naiveCotangent_target_eq

-- Proof sketch: compare the chosen presentation `\mathcal A[E] \to \mathcal B` with the
-- canonical one `\mathcal A[\mathcal B] \to \mathcal B` through the refinement
-- `\mathcal A[E \amalg \mathcal B] \to \mathcal B` coming from the map
-- `coprod.desc α (𝟙 _) : E ⨿ presentationVariables B ⟶ presentationVariables B`. The two induced
-- maps to the refinement are
-- quasi-isomorphisms by the same site-level conormal exactness argument as in Lemma `18.33.8`,
-- together with the presentation-independence argument from Chapter `10`. Passing to
-- `DerivedCategory.Q` produces the comparison morphism in `D(B)`.
private noncomputable def presentationNaiveCotangentToCotangent
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    : presentationNaiveCotangentOf E α ⟶ presentationCotangentSingle E α :=
  HomologicalComplex.mkHomToSingle
    (show (presentationNaiveCotangentOf E α).X 0 ⟶
        Ω(presentationBaseOf A E ≫ presentationMapOf A B E α) from by
      rw [presentationNaiveCotangentOf_X_zero]
      exact conormalToDifferentials (presentationBaseOf A E) (presentationMapOf A B E α))
    (fun i hi ↦ by
      have hi₀ : i + 1 = 0 := by
        simpa [ComplexShape.up, ComplexShape.Rel] using hi
      have hi' : i = -1 := by omega
      subst hi'
      simpa [presentationNaiveCotangentOf] using
        conormal_comp_zero (presentationBaseOf A E) (presentationMapOf A B E α)
    )

private noncomputable def naiveCotangentToCotangent :
    naiveCotangent A B ⟶ naiveCotangentSingle :=
  HomologicalComplex.mkHomToSingle
    (show (naiveCotangent A B).X 0 ⟶ Ω(presentationBase A B ≫ presentationMap A B) from by
      rw [naiveCotangent_X_zero]
      exact conormalToDifferentials (presentationBase A B) (presentationMap A B))
    (fun i hi ↦ by
      have hi₀ : i + 1 = 0 := by
        simpa [ComplexShape.up, ComplexShape.Rel] using hi
      have hi' : i = -1 := by omega
      subst hi'
      simpa [naiveCotangent] using
        conormal_comp_zero (presentationBase A B) (presentationMap A B)
    )

private noncomputable def presentationCotangentSingleIso
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    presentationCotangentSingle E α ≅ cotangentSingle₀ :=
  eqToIso (presentationCotangentSingle_eq E α)

private noncomputable def naiveCotangentSingleIso :
    (naiveCotangentSingle : CochainComplex ModB ℤ) ≅ cotangentSingle₀ :=
  eqToIso naiveCotangentSingle_eq

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
/-- Helper for Lemma 18.35.2: the free commutative-ring map adjoint to `α` factors through the
presentation morphism via the unit of `Under.costarAdjForget`. -/
private theorem freeMap_eq_underUnit_comp_presentationMapOf
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E B.right).symm α =
      ((Under.costarAdjForget A).unit.app (presentationFreeSheaf E)) ≫
        presentationMapOf A B E α := by
  -- Proof comment: this is the unit identity for the adjunction
  -- `Under.costarAdjForget A`, specialized to the presentation morphism produced from `α`.
  let u := ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E B.right).symm α
  have hu₁ :
      u = ((Under.costarAdjForget A).homEquiv (presentationFreeSheaf E) B)
        (((Under.costarAdjForget A).homEquiv (presentationFreeSheaf E) B).symm u) := by
    rw [Equiv.apply_symm_apply]
  have hu₂ :
      ((Under.costarAdjForget A).homEquiv (presentationFreeSheaf E) B)
        (((Under.costarAdjForget A).homEquiv (presentationFreeSheaf E) B).symm u) =
          ((Under.costarAdjForget A).unit.app (presentationFreeSheaf E)) ≫
            presentationMapOf A B E α := by
    -- Proof comment: `presentationMapOf` is definitionally the `.right` component of the
    -- transposed morphism in `Under A`.
    dsimp [u]
    simpa [presentationMapOf] using
      (Adjunction.homEquiv_unit (adj := Under.costarAdjForget A)
        (X := presentationFreeSheaf E) (Y := B)
        (f := (((Under.costarAdjForget A).homEquiv (presentationFreeSheaf E) B).symm
          (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E B.right).symm α))))
  exact hu₁.trans hu₂

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
/-- Helper for Lemma 18.35.2: the generator map `α` is obtained by evaluating the presentation
map on the bracket sections coming from the two adjunction units. -/
private theorem generatorMap_eq_unit_comp_forget_map
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    α =
      ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app E) ≫
        (sheafCompose J (CategoryTheory.forget CommRingCat)).map
          (((Under.costarAdjForget A).unit.app (presentationFreeSheaf E)) ≫
            presentationMapOf A B E α) := by
  -- Proof comment: first rewrite `α` by the unit identity for the free-ring/sheaf adjunction,
  -- then substitute the factorization of the free map through `presentationMapOf`.
  calc
    α = ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E B.right)
        (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E B.right).symm α) := by
          rw [Equiv.apply_symm_apply]
    _ = ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app E) ≫
        (sheafCompose J (CategoryTheory.forget CommRingCat)).map
          (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E B.right).symm α) := by
          simpa using
            (Adjunction.homEquiv_unit
              (adj := CategoryTheory.Sheaf.adjunction J CommRingCat.adj)
              (X := E) (Y := B.right)
              (f := (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E B.right).symm
                α)))
    _ = ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app E) ≫
        (sheafCompose J (CategoryTheory.forget CommRingCat)).map
          (((Under.costarAdjForget A).unit.app (presentationFreeSheaf E)) ≫
            presentationMapOf A B E α) := by
          exact congrArg
            (fun f ↦ ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app E) ≫
              (sheafCompose J (CategoryTheory.forget CommRingCat)).map f)
            (freeMap_eq_underUnit_comp_presentationMapOf (A := A) (B := B) E α)

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
/-- Helper for Lemma 18.35.2: the chosen presentation map sends the bracket generator attached to
`e` to the corresponding section `α(e)`. -/
private theorem presentationMapOf_on_generator
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (U : Cᵒᵖ)
    (e : E.1.obj U) :
    (((presentationMapOf A B E α).hom.app U).hom
      ((((Under.costarAdjForget A).unit.app (presentationFreeSheaf E)).hom.app U).hom
        (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app E).hom.app U e))) =
      α.hom.app U e := by
  -- Proof comment: evaluate the sheaf-level generator formula at `U` and the element `e`.
  have h := congrFun
    (congrArg (fun η : E ⟶ presentationVariables B ↦ η.hom.app U)
      (generatorMap_eq_unit_comp_forget_map (A := A) (B := B) E α))
    e
  simpa [Functor.map_comp, Category.assoc] using h.symm

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
/-- Helper for Lemma 18.35.2: local surjectivity of the generator map induces local surjectivity
of the corresponding presentation morphism. -/
private theorem presentationMapOf_isLocallySurjective
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hα : Sheaf.IsLocallySurjective α) :
    Sheaf.IsLocallySurjective (presentationMapOf A B E α) :=
  by
    -- Proof comment: a local preimage for `b` along `α` yields a local preimage along the
    -- presentation map by taking the corresponding bracket generator in the free algebra.
    change Presheaf.IsLocallySurjective J (presentationMapOf A B E α).hom
    change Presheaf.IsLocallySurjective J α.hom at hα
    refine Presheaf.IsLocallySurjective.mk ?_
    intro U b
    refine J.superset_covering ?_ (hα.imageSieve_mem (U := U) b)
    intro Y g hg
    rw [Presheaf.imageSieve_apply] at hg ⊢
    rcases hg with ⟨e, he⟩
    refine ⟨
      ((((Under.costarAdjForget A).unit.app (presentationFreeSheaf E)).hom.app (Opposite.op Y)).hom
        (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app E).hom.app
          (Opposite.op Y) e)),
      ?_⟩
    have he' : α.hom.app (Opposite.op Y) e = B.right.1.map g.op b := by
      simpa [presentationVariables] using he
    -- Proof comment: the presentation map evaluates this bracket generator to `α(e)`, which is
    -- exactly the restriction of `b` along `g` by the image-sieve witness.
    have hgen :
        (((presentationMapOf A B E α).hom.app (Opposite.op Y)).hom
          ((((Under.costarAdjForget A).unit.app (presentationFreeSheaf E)).hom.app
              (Opposite.op Y)).hom
            (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app E).hom.app
              (Opposite.op Y) e))) =
          α.hom.app (Opposite.op Y) e := by
      simpa using
        presentationMapOf_on_generator
          (A := A) (B := B) (E := E) (α := α) (Opposite.op Y) e
    exact hgen.trans he'

omit [HasWeakSheafify J (Type u)]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.35.2: the canonical presentation map is sectionwise surjective. -/
private theorem presentationMap_sectionwiseSurjective
    (U : Cᵒᵖ) :
    Function.Surjective (((presentationMap A B).hom.app U).hom) := by
  -- Proof comment: every section of `B` is one of the canonical generators of `A[B]`, and the
  -- presentation map evaluates that generator back to the original section.
  intro b
  refine ⟨
    ((((Under.costarAdjForget A).unit.app
        (presentationFreeSheaf (presentationVariables B))).hom.app U).hom
      (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app
          (presentationVariables B)).hom.app U b)),
    ?_⟩
  simpa using
    presentationMapOf_on_generator
      (A := A) (B := B) (E := presentationVariables B) (α := 𝟙 _)
      U b

/-- Helper for Lemma 18.35.2: the canonical generators of `A[E]` are the images of the original
generators of `E` under the two adjunction units. -/
private abbrev presentationGeneratorInclusion
    (E : Sheaf J (Type u)) :
    E ⟶ presentationVariables (Under.mk (presentationBaseOf A E)) :=
  ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).unit.app E) ≫
    (sheafCompose J (CategoryTheory.forget CommRingCat)).map
      ((Under.costarAdjForget A).unit.app (presentationFreeSheaf E))

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
/-- Helper for Lemma 18.35.2: the free map adjoint to the canonical generator inclusion is the
unit of the free-ring adjunction, followed by the `Under` unit. -/
private theorem presentationGeneratorInclusion_freeMap
    (E : Sheaf J (Type u)) :
    ((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E
        (presentationSheafOf A E)).symm
        (presentationGeneratorInclusion (A := A) E) =
      ((Under.costarAdjForget A).unit.app (presentationFreeSheaf E)) := by
  -- Proof comment: `presentationGeneratorInclusion` is defined by the two adjunction units, so
  -- transposing it across the free-ring/sheaf adjunction recovers the free-ring unit.
  rw [Equiv.symm_apply_eq]
  simpa [presentationGeneratorInclusion] using
    (Adjunction.homEquiv_unit
      (adj := CategoryTheory.Sheaf.adjunction J CommRingCat.adj)
      (X := E)
      (Y := presentationSheafOf A E)
      (f := ((Under.costarAdjForget A).unit.app (presentationFreeSheaf E))))

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] in
/-- Helper for Lemma 18.35.2: the presentation morphism induced by the canonical generator
inclusion is the identity on `A[E]`. -/
private theorem presentationMapOf_presentationGeneratorInclusion
    (E : Sheaf J (Type u)) :
    presentationMapOf A (Under.mk (presentationBaseOf A E)) E
        (presentationGeneratorInclusion (A := A) E) =
      𝟙 (presentationSheafOf A E) := by
  -- Proof comment: after rewriting the defining free map by
  -- `presentationGeneratorInclusion_freeMap`, the `Under`-adjunction triangle identity turns the
  -- induced presentation morphism into the identity on `A[E]`.
  have hUnder :
      ((Under.costarAdjForget A).homEquiv
          (presentationFreeSheaf E)
          (Under.mk (presentationBaseOf A E))).symm
        (((CategoryTheory.Sheaf.adjunction J CommRingCat.adj).homEquiv E
            (presentationSheafOf A E)).symm
          (presentationGeneratorInclusion (A := A) E)) =
        𝟙 ((Under.costar A).obj (presentationFreeSheaf E)) := by
    rw [presentationGeneratorInclusion_freeMap]
    simpa using
      (Adjunction.homEquiv_symm_unit
        (adj := Under.costarAdjForget A)
        (X := presentationFreeSheaf E))
  simpa [presentationMapOf, presentationSheafOf] using
    congrArg (fun f ↦ f.right) hUnder

/-- Helper for Lemma 18.35.2: exactness of the conormal sequence identifies the presentationwise
naive cotangent complex with the degree-zero cotangent single complex in the derived category. -/
private theorem presentationNaiveCotangentToCotangent_isIso_of_exact
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hExact :
      (ShortComplex.mk
        (conormalMap (presentationBaseOf A E) (presentationMapOf A B E α))
        (conormalToDifferentials (presentationBaseOf A E) (presentationMapOf A B E α))
        (conormal_comp_zero (presentationBaseOf A E) (presentationMapOf A B E α))).Exact)
    [Epi (conormalToDifferentials (presentationBaseOf A E) (presentationMapOf A B E α))] :
    IsIso (DerivedCategory.Q.map (presentationNaiveCotangentToCotangent (A := A) (B := B) E α)) := by
  -- Proof comment: apply the Chapter 18 derived comparison criterion for two-term complexes with
  -- exact degree `0` window and vanishing higher cohomology.
  have hExact₀ :
      (ShortComplex.mk
        ((presentationNaiveCotangentOf E α).d (-1) 0)
        ((presentationNaiveCotangentToCotangent (A := A) (B := B) E α).f 0)
        (by simpa using
          ((presentationNaiveCotangentToCotangent (A := A) (B := B) E α).comm (-1) 0))).Exact := by
    simpa [presentationNaiveCotangentOf, presentationNaiveCotangent_X_negOne,
      presentationNaiveCotangentOf_X_zero, presentationNaiveCotangentToCotangent]
      using hExact
  have hExactSucc (n : ℕ) :
      (presentationNaiveCotangentOf E α).ExactAt (n + 1) := by
    -- Proof comment: the source complex vanishes in strictly positive degrees.
    apply (presentationNaiveCotangentOf E α).exactAt_of_isLE 0 (n + 1)
    omega
  have hQuasi : QuasiIso (presentationNaiveCotangentToCotangent (A := A) (B := B) E α) := by
    rw [quasiIso_iff]
    intro i
    cases' Int.eq_zero_or_eq_natSucc_or_eq_negSucc i with hi hi
    · subst hi
      rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp [ComplexShape.up, ComplexShape.up'])
        (by simp [ComplexShape.up, ComplexShape.up'])]
      refine (ShortComplex.quasiIso_iff_of_zeros' _ ?_ ?_ ?_).2 ?_
      · simp [presentationNaiveCotangentToCotangent, presentationNaiveCotangentOf]
      · simp [presentationNaiveCotangentToCotangent]
      · simp [presentationCotangentSingle]
      · simpa [presentationNaiveCotangentOf_X_zero] using And.intro hExact inferInstance
    · rcases hi with ⟨n, rfl⟩
      exact (quasiIsoAt_iff_exactAt'
        (presentationNaiveCotangentToCotangent (A := A) (B := B) E α)
        (n + 1)
        (CochainComplex.exactAt_succ_single_obj (Ω(B.hom)) n)).2
        (by simpa using hExactSucc n)
    · rcases hi with ⟨n, rfl⟩
      have hSource :
          (presentationNaiveCotangentOf E α).ExactAt (Int.negSucc (n + 1)) := by
        apply (presentationNaiveCotangentOf E α).exactAt_of_isGE (-1) (Int.negSucc (n + 1))
        omega
      have hTarget :
          (presentationCotangentSingle E α).ExactAt (Int.negSucc (n + 1)) := by
        simpa [presentationCotangentSingle_eq (A := A) (B := B) E α] using
          HomologicalComplex.exactAt_single_obj (C := ModB) (c := ComplexShape.up ℤ) (j := 0)
            (A := Ω(B.hom)) (Int.negSucc (n + 1)) (by omega)
      exact (quasiIsoAt_iff_exactAt'
        (presentationNaiveCotangentToCotangent (A := A) (B := B) E α)
        (Int.negSucc (n + 1))
        hTarget).2 hSource
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso ModB
    (presentationNaiveCotangentToCotangent (A := A) (B := B) E α)).2 hQuasi

/-- Helper for Lemma 18.35.2: the canonical naive cotangent augmentation is invertible in the
derived category. -/
private theorem naiveCotangentToCotangent_isIso :
    IsIso (DerivedCategory.Q.map (naiveCotangentToCotangent (A := A) (B := B))) := by
  -- Proof comment: specialize the exactness criterion to the canonical presentation map.
  have hcanonicalExact :
      (ShortComplex.mk
        (conormalMap (presentationBase A B) (presentationMap A B))
        (conormalToDifferentials (presentationBase A B) (presentationMap A B))
        (conormal_comp_zero (presentationBase A B) (presentationMap A B))).Exact ∧
        Epi (conormalToDifferentials (presentationBase A B) (presentationMap A B)) :=
    conormalSequence_exact_of_sectionwiseSurjective
      (presentationBase A B) (presentationMap A B)
      (presentationMap_sectionwiseSurjective (A := A) (B := B))
  exact presentationNaiveCotangentToCotangent_isIso_of_exact
    (A := A) (B := B) (E := presentationVariables B) (α := 𝟙 _)
    hcanonicalExact.1

/-- Lemma 18.35.2: let
`α : E ⟶ presentationVariables B`
be a locally surjective map of sheaves of sets, so that the
induced map `presentationMapOf A B E α : A[E] ⟶ B` is a chosen presentation of `B` over
`A`. Then there is a canonical comparison morphism in `D(B)` from the naive cotangent
complex of that chosen presentation to the canonical naive cotangent complex
`NL_{B/A}`. -/
@[stacks 08TY]
noncomputable abbrev presentationNaiveCotangentComparison
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B) :
    ((DerivedCategory.Q.obj (presentationNaiveCotangentOf E α)) : DModB) ⟶
      ((DerivedCategory.Q.obj (naiveCotangent A B)) : DModB) :=
  -- Route correction: compare both naive cotangent complexes through the common single complex
  -- `Ω(B.hom)[0]` and invert the canonical augmentation.
  DerivedCategory.Q.map (presentationNaiveCotangentToCotangent (A := A) (B := B) E α) ≫
    (presentationCotangentSingleIso (A := A) (B := B) E α).hom ≫
    (naiveCotangentSingleIso (A := A) (B := B)).inv ≫
    inv (DerivedCategory.Q.map (naiveCotangentToCotangent (A := A) (B := B)))

private instance presentationNaiveCotangentComparison_isIso_inst
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hα : Sheaf.IsLocallySurjective α) :
    IsIso (presentationNaiveCotangentComparison E α) := by
  -- Proof comment: the chosen augmentation is a derived isomorphism by the conormal exact
  -- sequence, and the remaining factors are fixed transport isomorphisms.
  have hchosenExact :
      (ShortComplex.mk
        (conormalMap (presentationBaseOf A E) (presentationMapOf A B E α))
        (conormalToDifferentials (presentationBaseOf A E) (presentationMapOf A B E α))
        (conormal_comp_zero (presentationBaseOf A E) (presentationMapOf A B E α))).Exact ∧
        Epi (conormalToDifferentials (presentationBaseOf A E) (presentationMapOf A B E α)) :=
    conormalSequence_exact
      (presentationBaseOf A E) (presentationMapOf A B E α)
      (presentationMapOf_isLocallySurjective (A := A) (B := B) E α hα)
  letI :
      IsIso (DerivedCategory.Q.map (presentationNaiveCotangentToCotangent (A := A) (B := B) E α)) :=
    presentationNaiveCotangentToCotangent_isIso_of_exact
      (A := A) (B := B) (E := E) (α := α) hchosenExact.1
  letI := naiveCotangentToCotangent_isIso (A := A) (B := B)
  dsimp [presentationNaiveCotangentComparison]
  infer_instance

/-- The comparison morphism of Lemma 18.35.2 is an isomorphism in `D(B)`. -/
theorem presentationNaiveCotangentComparison_isIso
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hα : Sheaf.IsLocallySurjective α) :
    IsIso (presentationNaiveCotangentComparison E α) := by
  exact presentationNaiveCotangentComparison_isIso_inst E α hα

/-- The chosen-presentation naive cotangent complex and the canonical naive cotangent complex are
canonically isomorphic in `D(B)`. -/
theorem presentationNaiveCotangent_iso
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables B)
    (hα : Sheaf.IsLocallySurjective α) :
    IsIsomorphic
      ((DerivedCategory.Q.obj (presentationNaiveCotangentOf E α)) : DModB)
      ((DerivedCategory.Q.obj (naiveCotangent A B)) : DModB) := by
  letI := presentationNaiveCotangentComparison_isIso E α hα
  exact ⟨asIso (presentationNaiveCotangentComparison E α)⟩

end

end
