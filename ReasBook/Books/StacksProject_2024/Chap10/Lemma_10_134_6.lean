import stacks_project.Chap10.Definition_10_134_1

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent

universe u

noncomputable section

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: surjective algebra maps and the naive cotangent complex;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the chapter owner `NL_{B⁄A}`;
  - `Algebra.H1Cotangent`, the canonical owner `H¹(L_{B/A})`;
  - `Generators.naiveCotangentChainHomotopyEquiv`, the presentation-independence bridge from a
    chosen presentation back to `NL_{B⁄A}`;
  - `Extension.ofSurjective`, the surjective presentation whose cotangent is the conormal module
    `I / I²`.
* best owner abstraction: the public source-facing statements belong on the canonical algebra
  owners `NL_{B⁄A}` and `H1Cotangent A B`; the surjective extension is only the bridge/view
  exposing the target conormal module `I / I²`.
* primitive data vs. derived API:
  - primitive data: the surjective algebra map `A → B`;
  - derived API: the surjective presentation `Extension.ofSurjective (Algebra.ofId A B) h`, the
    canonical empty-generator presentation `Generators.ofSurjectiveAlgebraMap h`, and the
    comparison equivalences between them.
* layer triage:
  - `source-facing`: `NL_{B⁄A}` and `H¹(L_{B/A})`;
  - `core/canonical`: `Algebra.naiveCotangent A B` and `Algebra.H1Cotangent A B`;
  - `bridge/view`: the surjective presentation and its conormal module
    `(Extension.ofSurjective (Algebra.ofId A B) h).Cotangent`.
-/
-- Semantic recall note: the MCP tool `lean_leansearch` was unavailable in this environment, so
-- the owner/API choice was verified by local repository search against `Definition_10_134_1` and
-- `Lemma_10_134_2`.

private abbrev LiftCotangent (P : Extension A B) :=
  ULift P.Cotangent

private noncomputable abbrev liftCotangentEquiv
    (P : Extension A B) :
    LiftCotangent P ≃ₗ[B] P.Cotangent :=
  ULift.moduleEquiv

private noncomputable def liftCotangentMap
    {P Q : Extension A B} (f : P.Hom Q) :
    LiftCotangent P →ₗ[B] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ
    Cotangent.map f ∘ₗ (liftCotangentEquiv P).toLinearMap

private noncomputable def liftCotangentHomotopyMap
    {P Q : Extension A B} (f g : P.Hom Q) :
    P.CotangentSpace →ₗ[B] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ f.sub g

private theorem liftCotangentMap_id
    (P : Extension A B) :
    liftCotangentMap (.id P) = LinearMap.id := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap]

private theorem liftCotangentMap_comp
    {P Q T : Extension A B} (f : P.Hom Q) (g : Q.Hom T) :
    liftCotangentMap (g.comp f) =
      (liftCotangentMap g).restrictScalars B ∘ₗ liftCotangentMap f := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap, Cotangent.map_comp, LinearMap.comp_assoc]

private theorem naiveCotangent_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_rel21 : (ComplexShape.down ℕ).Rel 2 1 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_not_rel0 (j : ℕ) : ¬ (ComplexShape.down ℕ).Rel 0 j := by
  simp [ComplexShape.down]

private noncomputable def naiveCotangentChainComplexXIsoPUnit
    (P : Extension A B) (i : ℕ) :
    P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of B PUnit := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, zero_comp⟩
  simpa [naiveCotangentChainComplex] using
    (ChainComplex.mk'XIso
      (ModuleCat.of B P.CotangentSpace)
      (ModuleCat.of B (LiftCotangent P))
      (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftCotangentEquiv P).toLinearMap))
      succZero i)

private theorem naiveCotangentChainComplex_eq_zero_of_succ_succ
    (P : Extension A B) (i : ℕ)
    (x : P.naiveCotangentChainComplex.X (i + 2)) :
    x = 0 := by
  let e := naiveCotangentChainComplexXIsoPUnit P i
  have h : e.hom.hom x = e.hom.hom 0 := by
    cases e.hom.hom x
    rfl
  apply_fun e.inv.hom at h
  simpa using h

private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension A B) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [naiveCotangentChainComplex_eq_zero_of_succ_succ P i x,
    naiveCotangentChainComplex_eq_zero_of_succ_succ P i y]

private theorem naiveCotangentChainMap_id
    (P : Extension A B) :
    Extension.naiveCotangentChainMap (.id P) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ModuleCat.ofHom (CotangentSpace.map (.id P)) =
        ModuleCat.ofHom (LinearMap.id : P.CotangentSpace →ₗ[B] P.CotangentSpace)
      congr
      exact CotangentSpace.map_id
  | succ i =>
      cases i with
      | zero =>
          ext x
          rcases x with ⟨x⟩
          change (ULift.up (Cotangent.map (.id P) x) : LiftCotangent P) = ULift.up x
          congr 1
          simp
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ P i
          ext x
          exact Subsingleton.elim _ _

private theorem naiveCotangentChainMap_comp
    {P Q T : Extension A B} (f : P.Hom Q) (g : Q.Hom T) :
    Extension.naiveCotangentChainMap (g.comp f) =
      Extension.naiveCotangentChainMap f ≫ Extension.naiveCotangentChainMap g := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ModuleCat.ofHom (CotangentSpace.map (g.comp f)) =
        ModuleCat.ofHom ((CotangentSpace.map g).restrictScalars B ∘ₗ CotangentSpace.map f)
      congr
      exact CotangentSpace.map_comp f g
  | succ i =>
      cases i with
      | zero =>
          ext x
          rcases x with ⟨x⟩
          change (ULift.up (Cotangent.map (g.comp f) x) : LiftCotangent T) =
            ULift.up (Cotangent.map g (Cotangent.map f x))
          simp [Cotangent.map_comp]
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ T i
          ext x
          exact Subsingleton.elim _ _

private noncomputable def naiveCotangentChainHomotopyHom
    {P Q : Extension A B} (f g : P.Hom Q)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    P.naiveCotangentChainComplex.X i ⟶ Q.naiveCotangentChainComplex.X j := by
  rcases i with _ | i
  · rcases j with _ | j
    · exact 0
    · cases j with
      | zero =>
          exact ModuleCat.ofHom (liftCotangentHomotopyMap f g)
      | succ j =>
          exact 0
  · exact 0

private theorem naiveCotangentChainMap_sub_eq_nullHomotopicMap
    {P Q : Extension A B} (f g : P.Hom Q) :
    Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g =
      Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g) := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 0 =
        (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g)).f 0
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left naiveCotangent_rel10
        naiveCotangent_not_rel0 (naiveCotangentChainHomotopyHom f g)]
      ext x
      simpa [Extension.naiveCotangentChainMap, naiveCotangentChainHomotopyHom,
        naiveCotangentChainComplex, liftCotangentHomotopyMap, LinearMap.comp_assoc] using
        LinearMap.congr_fun (Extension.CotangentSpace.map_sub_map f g) x
  | succ i =>
      cases i with
      | zero =>
          change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 1 =
            (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g)).f 1
          rw [Homotopy.nullHomotopicMap'_f naiveCotangent_rel21 naiveCotangent_rel10
            (naiveCotangentChainHomotopyHom f g)]
          ext x
          rcases x with ⟨x⟩
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            (ModuleCat.Hom.hom
                (P.naiveCotangentChainComplex.d 1 0 ≫
                  naiveCotangentChainHomotopyHom f g 0 1 naiveCotangent_rel10 +
                naiveCotangentChainHomotopyHom f g 1 2 naiveCotangent_rel21 ≫
                  Q.naiveCotangentChainComplex.d 2 1))
              { down := x }
          rw [naiveCotangentChainComplex_d_succ_succ Q 0, naiveCotangentChainComplex_d_1_0 P]
          simp [naiveCotangentChainHomotopyHom, liftCotangentHomotopyMap]
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            ULift.up ((f.sub g) (P.cotangentComplex x))
          rw [LinearMap.congr_fun (Extension.Cotangent.map_sub_map f g) x]
          rfl
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ Q i
          ext x
          exact Subsingleton.elim _ _

private noncomputable def naiveCotangentChainMapHomotopy
    {P Q : Extension A B} (f g : P.Hom Q) :
    Homotopy (Extension.naiveCotangentChainMap f) (Extension.naiveCotangentChainMap g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (naiveCotangentChainMap_sub_eq_nullHomotopicMap f g)).trans
      (Homotopy.nullHomotopy' (naiveCotangentChainHomotopyHom f g)))

private noncomputable def generators_naiveCotangentChainHomotopyEquiv
    {ι ι' : Type u} (P : Generators A B ι) (Q : Generators A B ι') :
    HomotopyEquiv P.toExtension.naiveCotangentChainComplex Q.toExtension.naiveCotangentChainComplex where
  hom := Extension.naiveCotangentChainMap (Generators.defaultHom P Q).toExtensionHom
  inv := Extension.naiveCotangentChainMap (Generators.defaultHom Q P).toExtensionHom
  homotopyHomInvId := by
    let f := (Generators.defaultHom P Q).toExtensionHom
    let g := (Generators.defaultHom Q P).toExtensionHom
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp f g).symm).trans
        ((naiveCotangentChainMapHomotopy (g.comp f) (.id P.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id P.toExtension)))
  homotopyInvHomId := by
    let f := (Generators.defaultHom P Q).toExtensionHom
    let g := (Generators.defaultHom Q P).toExtensionHom
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp g f).symm).trans
        ((naiveCotangentChainMapHomotopy (f.comp g) (.id Q.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id Q.toExtension)))

private abbrev surjectivePresentation
    (h : Function.Surjective (algebraMap A B)) :
    Extension A B :=
  Extension.ofSurjective (Algebra.ofId A B) h

private abbrev surjectiveGenerators
    (h : Function.Surjective (algebraMap A B)) :
    Generators A B PEmpty.{u + 1} :=
  Generators.ofSurjectiveAlgebraMap h

private noncomputable def surjectiveGeneratorsToPresentation
    (h : Function.Surjective (algebraMap A B)) :
    (surjectiveGenerators h).toExtension.Hom (surjectivePresentation h) := by
  let e : (surjectiveGenerators h).Ring →ₐ[A] (surjectivePresentation h).Ring :=
    (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).toAlgHom
  refine Extension.Hom.ofAlgHom e ?_
  have hsigma :
      (Algebra.ofId A B).comp e =
        IsScalarTower.toAlgHom A (surjectiveGenerators h).Ring B := by
    ext i
    exact PEmpty.elim i
  simpa [surjectivePresentation] using hsigma

private noncomputable def surjectivePresentationToGenerators
    (h : Function.Surjective (algebraMap A B)) :
    (surjectivePresentation h).Hom (surjectiveGenerators h).toExtension := by
  let e : (surjectivePresentation h).Ring →ₐ[A] (surjectiveGenerators h).Ring :=
    (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).symm.toAlgHom
  refine Extension.Hom.ofAlgHom e ?_
  have hsigma :
      (IsScalarTower.toAlgHom A (surjectiveGenerators h).Ring B).comp e =
        Algebra.ofId A B := by
    ext
  simpa [surjectivePresentation] using hsigma

private theorem surjectiveGenerators_presentation_comp_id
    (h : Function.Surjective (algebraMap A B)) :
    (surjectivePresentationToGenerators h).comp (surjectiveGeneratorsToPresentation h) =
      .id (surjectiveGenerators h).toExtension := by
  ext x
  change
    (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).symm
      ((MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}) x) = x
  exact (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).symm_apply_apply x

private theorem surjectivePresentation_generators_comp_id
    (h : Function.Surjective (algebraMap A B)) :
    (surjectiveGeneratorsToPresentation h).comp (surjectivePresentationToGenerators h) =
      .id (surjectivePresentation h) := by
  ext x
  change
    (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1})
      ((MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).symm x) = x
  exact (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).apply_symm_apply x

private noncomputable def surjectiveGeneratorsCotangentEquiv
    (h : Function.Surjective (algebraMap A B)) :
    (surjectiveGenerators h).toExtension.Cotangent ≃ₗ[B] (surjectivePresentation h).Cotangent where
  toFun := Cotangent.map (surjectiveGeneratorsToPresentation h)
  invFun := Cotangent.map (surjectivePresentationToGenerators h)
  left_inv x := by
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    rw [Cotangent.map_mk, Cotangent.map_mk]
    congr 1
    apply Subtype.ext
    exact (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).symm_apply_apply x.1
  right_inv x := by
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    rw [Cotangent.map_mk, Cotangent.map_mk]
    congr 1
    apply Subtype.ext
    exact (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).apply_symm_apply x.1
  map_add' := (Cotangent.map (surjectiveGeneratorsToPresentation h)).map_add
  map_smul' := (Cotangent.map (surjectiveGeneratorsToPresentation h)).map_smul

private noncomputable def surjectiveGeneratorsCotangentSpaceEquiv
    (h : Function.Surjective (algebraMap A B)) :
    (surjectiveGenerators h).toExtension.CotangentSpace ≃ₗ[B]
      (surjectivePresentation h).CotangentSpace where
  toFun := CotangentSpace.map (surjectiveGeneratorsToPresentation h)
  invFun := CotangentSpace.map (surjectivePresentationToGenerators h)
  left_inv x := by
    let f := surjectiveGeneratorsToPresentation h
    let g := surjectivePresentationToGenerators h
    have hcomp := (CotangentSpace.map_comp_apply f g x).symm
    rw [surjectiveGenerators_presentation_comp_id h, CotangentSpace.map_id] at hcomp
    simpa using hcomp
  right_inv x := by
    let f := surjectivePresentationToGenerators h
    let g := surjectiveGeneratorsToPresentation h
    have hcomp := (CotangentSpace.map_comp_apply f g x).symm
    rw [surjectivePresentation_generators_comp_id h, CotangentSpace.map_id] at hcomp
    simpa using hcomp
  map_add' := (CotangentSpace.map (surjectiveGeneratorsToPresentation h)).map_add
  map_smul' := (CotangentSpace.map (surjectiveGeneratorsToPresentation h)).map_smul

private lemma surjectivePresentation_cotangentSpace_subsingleton
    (h : Function.Surjective (algebraMap A B)) :
    Subsingleton (surjectivePresentation h).CotangentSpace := by
  let P : Extension A B := surjectivePresentation h
  have hP : P.Ring = A := rfl
  letI : Subsingleton (KaehlerDifferential A P.Ring) := by
    cases hP
    change Subsingleton (KaehlerDifferential A A)
    exact KaehlerDifferential.subsingleton_of_surjective A A fun x ↦ ⟨x, rfl⟩
  letI : Subsingleton P.CotangentSpace := inferInstance
  infer_instance

private lemma surjectiveGenerators_cotangentSpace_subsingleton
    (h : Function.Surjective (algebraMap A B)) :
    Subsingleton (surjectiveGenerators h).toExtension.CotangentSpace := by
  letI : Subsingleton (surjectivePresentation h).CotangentSpace :=
    surjectivePresentation_cotangentSpace_subsingleton h
  exact (surjectiveGeneratorsCotangentSpaceEquiv h).injective.subsingleton

private theorem cotangentComplex_eq_zero_of_subsingleton_cotangentSpace
    (P : Extension A B) [Subsingleton P.CotangentSpace] :
    P.cotangentComplex = 0 := by
  ext x
  exact Subsingleton.elim _ _

private theorem h1Cotangentι_bijective_of_subsingleton_cotangentSpace
    (P : Extension A B) [Subsingleton P.CotangentSpace] :
    Function.Bijective P.h1Cotangentι := by
  refine ⟨P.h1Cotangentι_injective, ?_⟩
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  simp [cotangentComplex_eq_zero_of_subsingleton_cotangentSpace P]

private noncomputable def naiveCotangentChainComplex_homotopyEquiv_single₁_cotangent_of_subsingleton
    (P : Extension A B) [Subsingleton P.CotangentSpace] :
    HomotopyEquiv
      P.naiveCotangentChainComplex
      ((HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of B P.Cotangent)) := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, zero_comp⟩
  let C := P.naiveCotangentChainComplex
  let D := (HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).obj
    (ModuleCat.of B P.Cotangent)
  let e : ∀ n : ℕ, C.X n ≅ D.X n
    | 0 => by
        simpa [C, D, naiveCotangentChainComplex] using
          ((ModuleCat.isZero_of_subsingleton
              (ModuleCat.of B P.CotangentSpace)).isoZero ≪≫
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 1
              (ModuleCat.of B P.Cotangent) 0 (by decide)).isoZero.symm)
    | 1 => by
        simpa [C, D, naiveCotangentChainComplex] using
          (ULift.moduleEquiv : ULift P.Cotangent ≃ₗ[B] P.Cotangent).toModuleIso
    | n + 2 => by
        have hs : (succZero (C.d (n + 1) n)).1 = ModuleCat.of B PUnit := rfl
        have hX :
            C.X (n + 2) ≅ (succZero (C.d (n + 1) n)).1 := by
          simpa [C, naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of B P.CotangentSpace)
              (ModuleCat.of B (ULift P.Cotangent))
              (ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
              succZero n)
        simpa [D] using
          (hX ≪≫ eqToIso hs ≪≫
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of B PUnit)).isoZero ≪≫
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 1
              (ModuleCat.of B P.Cotangent) (n + 2) (by simp)).isoZero.symm)
  exact HomotopyEquiv.ofIso <|
    HomologicalComplex.Hom.isoOfComponents e <| by
      intro i j hij
      subst i
      cases j with
      | zero =>
          have hcot :
              ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) = 0 := by
            rw [cotangentComplex_eq_zero_of_subsingleton_cotangentSpace P]
            rfl
          have hC : C.d 1 0 = 0 := by
            simpa [C] using (naiveCotangentChainComplex_d_1_0 P).trans hcot
          have hD : D.d 1 0 = 0 := by
            simp [D]
          change (e 1).hom ≫ D.d 1 0 = C.d 1 0 ≫ (e 0).hom
          rw [hC, hD]
          simp
      | succ j =>
          have hC : C.d (j + 2) (j + 1) = 0 := by
            simpa [C] using naiveCotangentChainComplex_d_succ_succ P j
          have hD : D.d (j + 2) (j + 1) = 0 := by
            simp [D]
          change (e (j + 2)).hom ≫ D.d (j + 2) (j + 1) =
            C.d (j + 2) (j + 1) ≫ (e (j + 1)).hom
          rw [hC, hD]
          simp

private noncomputable def surjectiveGenerators_h1Cotangent_equiv_cotangent
    (h : Function.Surjective (algebraMap A B)) :
    (surjectiveGenerators h).toExtension.H1Cotangent ≃ₗ[B]
      (surjectiveGenerators h).toExtension.Cotangent := by
  let P := (surjectiveGenerators h).toExtension
  letI : Subsingleton P.CotangentSpace := surjectiveGenerators_cotangentSpace_subsingleton h
  exact LinearEquiv.ofBijective P.h1Cotangentι
    (h1Cotangentι_bijective_of_subsingleton_cotangentSpace P)

private noncomputable def surjectiveGenerators_naiveCotangentChainComplex_homotopyEquiv_single₁_cotangent
    (h : Function.Surjective (algebraMap A B)) :
    HomotopyEquiv
      (surjectiveGenerators h).toExtension.naiveCotangentChainComplex
      ((HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of B (surjectivePresentation h).Cotangent)) := by
  let P := surjectiveGenerators h
  letI : Subsingleton P.toExtension.CotangentSpace := surjectiveGenerators_cotangentSpace_subsingleton h
  exact
    (naiveCotangentChainComplex_homotopyEquiv_single₁_cotangent_of_subsingleton
      P.toExtension).trans <|
      HomotopyEquiv.ofIso <|
        (HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).mapIso
          (surjectiveGeneratorsCotangentEquiv h).toModuleIso

/-- Lemma 10.134.6 (1): for a surjective ring map `A → B` with kernel `I`, the naive cotangent
complex `NL_{B/A}` is homotopy equivalent to the chain complex `(I / I² → 0)` concentrated in
degree `1`, represented here as the single complex on
`(Extension.ofSurjective (Algebra.ofId A B) h).Cotangent`. -/
noncomputable def surjective_algebra_naiveCotangent_homotopyEquiv_single₁_cotangent
    (h : Function.Surjective (algebraMap A B)) :
    HomotopyEquiv
      (Algebra.naiveCotangent A B)
      ((HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent)) :=
  (generators_naiveCotangentChainHomotopyEquiv (Generators.self A B) (surjectiveGenerators h)).trans
    (surjectiveGenerators_naiveCotangentChainComplex_homotopyEquiv_single₁_cotangent h)

/-- Lemma 10.134.6 (2): for a surjective ring map `A → B` with kernel `I`, the canonical first
cotangent homology `H₁(L_{B/A})` identifies with the conormal module `I / I²`. -/
noncomputable def surjective_algebra_h1Cotangent_equiv_cotangent
    (h : Function.Surjective (algebraMap A B)) :
    H1Cotangent A B ≃ₗ[B] (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent := by
  let P := surjectiveGenerators h
  let eH1 : H1Cotangent A B ≃ₗ[B] P.toExtension.H1Cotangent := P.equivH1Cotangent.symm
  let eCot :
      P.toExtension.H1Cotangent ≃ₗ[B] (surjectivePresentation h).Cotangent :=
    (surjectiveGenerators_h1Cotangent_equiv_cotangent h).trans
      (surjectiveGeneratorsCotangentEquiv h)
  simpa [surjectivePresentation] using eH1.trans eCot

end
