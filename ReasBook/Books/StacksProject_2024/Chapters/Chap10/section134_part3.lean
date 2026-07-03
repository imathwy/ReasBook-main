import Mathlib
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_134_6 (from Chap10) -/
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

/-! ### Lemma_10_134_7 (from Chap10) -/
open Algebra
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
* primary domain: the Jacobi-Zariski exact sequence for a tower `A → B → C`, specialized to the
  surjective case `A → C`;
* sampled owner declarations:
  - `Algebra.H1Cotangent.exact_map_δ`, the owner exactness of
    `H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A]`;
  - `Algebra.H1Cotangent.exact_δ_mapBaseChange`, the next owner exactness
    `H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A]`;
  - `KaehlerDifferential.subsingleton_of_surjective`, the canonical vanishing of `Ω[C⁄A]` for a
    surjective map `A → C`;
  - `surjective_algebra_h1Cotangent_equiv_cotangent`, the previous chapter bridge identifying the
    surjective `H¹` terms with conormal modules.
* best owner abstraction: the public source-facing statement should stay on the canonical owner
  maps `H1Cotangent.map` and `H1Cotangent.δ`; the conormal-module formulation is only the
  bridge/view supplied by the surjective comparison from Lemma `10.134.6`.
* primitive data vs. derived API:
  - primitive data: a tower `A → B → C` and the surjectivity hypothesis on `A → C`;
  - derived API: exactness of `H1Cotangent.map`, `H1Cotangent.δ`, and the surjectivity of `δ`
    forced by the vanishing of `Ω[C⁄A]`.
* layer triage:
  - `source-facing`: the surjective Jacobi-Zariski conormal sequence;
  - `core/canonical`: `H1Cotangent.exact_map_δ`, `H1Cotangent.exact_δ_mapBaseChange`, and
    `KaehlerDifferential.subsingleton_of_surjective`;
  - `bridge/view`: the conormal-module interpretation via
    `surjective_algebra_h1Cotangent_equiv_cotangent`.
-/
-- Proof sketch: start from the Jacobi-Zariski exactness
-- `H1Cotangent.exact_map_δ` for `A → B → C`. If `A → C` is surjective, then `Ω[C⁄A] = 0`, so the
-- next map in the Jacobi-Zariski sequence is zero and `δ` is therefore surjective. By the
-- surjective-case description of Lemma `10.134.6`, the two `H1Cotangent` terms identify with the
-- conormal modules `I / I²` and `J / J²`.
/-- Lemma 10.134.7: if `A → C` is surjective, then the Jacobi-Zariski segment
`H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A]`
is exact and the second map is surjective. Via the canonical identifications for surjective maps,
this is the exact sequence
`I / I² → J / J² → Ω[B⁄A] ⊗[B] B / J → 0`,
where `I = ker(A → C)` and `J = ker(B → C)`. -/
theorem surjective_jacobi_zariski_conormal_sequence
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Exact (H1Cotangent.map A B C C) (H1Cotangent.δ A B C) ∧
      Function.Surjective (H1Cotangent.δ A B C) := by
  refine ⟨H1Cotangent.exact_map_δ A B C, ?_⟩
  letI : Subsingleton Ω[C⁄A] := KaehlerDifferential.subsingleton_of_surjective A C hAC
  have hExact :
      Function.Exact (H1Cotangent.δ A B C) (KaehlerDifferential.mapBaseChange A B C) :=
    H1Cotangent.exact_δ_mapBaseChange A B C
  have hZero : KaehlerDifferential.mapBaseChange A B C = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hKer : LinearMap.ker (KaehlerDifferential.mapBaseChange A B C) = ⊤ := by
    rw [hZero, LinearMap.ker_zero]
  rw [← LinearMap.range_eq_top]
  rw [← Function.Exact.linearMap_ker_eq hExact]
  exact hKer

end

/-! ### Lemma_10_134_8_Flat_base_change (from Chap10) -/
open scoped NaiveCotangent TensorProduct
open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {R : Type u} {S : Type u} {R' : Type u}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] TensorProduct.leftAlgebra
attribute [local instance] TensorProduct.rightAlgebra

local notation:max "NL_{" S "⁄" R "}↾[" T "]" =>
  Algebra.Extension.naiveCotangentChainComplexRestrictScalars
    (Generators.toExtension (Generators.self R S)) T

/- Domain triage:
* primary domain: flat base change for naive cotangent complexes of commutative algebras;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the source-facing owner `NL_{S⁄R}`;
  - `Algebra.Extension.naiveCotangentChainComplex`, the presentation-level owner for the
    underived two-term complex;
  - `Algebra.Extension.naiveCotangentChainComplexRestrictScalars`, the canonical bridge/view for
    viewing that owner over a smaller base ring;
  - `Algebra.Extension.tensorCotangentSpace` and `Algebra.Extension.tensorCotangentOfFlat`, the
    degree-`0` and degree-`1` flat base-change isomorphisms.
* best owner abstraction: the main source-facing statement should expose the canonical comparison
  from the scalar extension of `NL_{S⁄R}` as an `R`-linear complex to the restricted target owner
  `NL_{R' ⊗[R] S⁄R'}` as an `R'`-linear complex.
* primitive data vs. derived API:
  - primitive data: the owner complexes `NL_{S⁄R}` and
    `Algebra.Extension.naiveCotangentChainComplex` for the base-changed extension;
  - derived API: the tensor-model normalization of degree `1`, the comparison chain map, and the
    induced chain-complex isomorphism / homotopy equivalence.
* layer triage:
  - `source-facing`: flat base change for `NL_{S⁄R}`;
  - `core/canonical`: `NL_{S⁄R}` and `(P.baseChange : Extension R' (R' ⊗[R] S))
      .naiveCotangentChainComplexRestrictScalars R'`;
  - `bridge/view`: the private tensor model with degree `1` written as `R' ⊗[R] P.Cotangent`.
-/

private abbrev LiftCotangent (P : Extension R S) :=
  ULift.{u, u} P.Cotangent

private noncomputable abbrev liftCotangentEquiv (P : Extension R S) :
    LiftCotangent P ≃ₗ[S] P.Cotangent :=
  ULift.moduleEquiv

private noncomputable def restrictCotangentSpaceEquiv (P : Extension R S) :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S P.CotangentSpace)) ≃ₗ[R]
      P.CotangentSpace :=
  { __ := AddEquiv.refl _
    map_smul' := fun _ _ ↦ by simp }

private noncomputable abbrev scalarExtendedNaiveCotangentChainComplex
    (T : Type u) [CommRing T] [Algebra R T] (P : Extension R S) :
    ChainComplex (ModuleCat T) ℕ :=
  ((ModuleCat.extendScalars (algebraMap R T)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (P.naiveCotangentChainComplexRestrictScalars R)

private noncomputable def tensorNaiveCotangentChainComplex
    (T : Type u) [CommRing T] [Algebra R T] (P : Extension R S) :
    ChainComplex (ModuleCat T) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of T (T ⊗[R] P.CotangentSpace))
    (ModuleCat.of T (T ⊗[R] P.Cotangent))
    (ModuleCat.ofHom (LinearMap.baseChange T (P.cotangentComplex.restrictScalars R)))
    (fun {_ _} _ ↦ ⟨ModuleCat.of T PUnit, 0, zero_comp⟩)

private noncomputable abbrev baseChangedExtension
    (T : Type u) [CommRing T] [Algebra R T] (P : Extension R S) :
    Extension T (T ⊗[R] S) := by
  let Q : Extension T (T ⊗[R] S) := P.baseChange
  exact Q

private noncomputable abbrev baseChangedNaiveCotangentChainComplex
    (T : Type u) [CommRing T] [Algebra R T] (P : Extension R S) :
    ChainComplex (ModuleCat T) ℕ := by
  let Q : Extension T (T ⊗[R] S) := baseChangedExtension T P
  exact Q.naiveCotangentChainComplexRestrictScalars T

private noncomputable abbrev selfBaseChangedExtension :
    Extension R' (R' ⊗[R] S) := by
  let Q : Extension R' (R' ⊗[R] S) := (Generators.self R S).toExtension.baseChange
  exact Q

private noncomputable abbrev selfBaseChangedGenerators :
    Generators R' (R' ⊗[R] S) S := by
  let Q : Generators R' (R' ⊗[R] S) S := (Generators.self R S).baseChange R'
  exact Q

private theorem baseChangedExtension_algebraMap_smul_cotangent
    (P : Extension R S) :
    ∀ t : R', ∀ x : (baseChangedExtension R' P).Cotangent,
      (algebraMap R' (R' ⊗[R] S) t) • x = t • x := by
  intro t x
  rfl

private theorem baseChangedExtension_algebraMap_smul_cotangentSpace
    (P : Extension R S) :
    ∀ t : R', ∀ x : (baseChangedExtension R' P).CotangentSpace,
      (algebraMap R' (R' ⊗[R] S) t) • x = t • x := by
  intro t x
  dsimp [Extension.CotangentSpace] at x ⊢
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s y =>
      simp [TensorProduct.smul_tmul', Algebra.smul_def]

private instance baseChangedExtensionCotangentIsScalarTower
    (P : Extension R S) :
    IsScalarTower R' (R' ⊗[R] S) (baseChangedExtension R' P).Cotangent :=
  IsScalarTower.of_algebraMap_smul
    (baseChangedExtension_algebraMap_smul_cotangent P)

private instance baseChangedExtensionCotangentSpaceIsScalarTower
    (P : Extension R S) :
    IsScalarTower R' (R' ⊗[R] S) (baseChangedExtension R' P).CotangentSpace :=
  IsScalarTower.of_algebraMap_smul
    (baseChangedExtension_algebraMap_smul_cotangentSpace P)

private instance baseChangedExtensionLiftCotangentIsScalarTower
    (P : Extension R S) :
    IsScalarTower R' (R' ⊗[R] S) (LiftCotangent (baseChangedExtension R' P)) :=
  IsScalarTower.of_algebraMap_smul fun t x ↦ by
    change ULift.up ((algebraMap R' (R' ⊗[R] S) t) • x.down) = ULift.up (t • x.down)
    simpa using baseChangedExtension_algebraMap_smul_cotangent P t x.down

private noncomputable def restrictScalarsSelfEquiv
    (T : Type u) [CommRing T] [Algebra R T] :
    ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) ≃ₗ[T] T :=
  { __ := AddEquiv.refl T
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower
    (T : Type u) [CommRing T] [Algebra R T] :
    IsScalarTower R T
      ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    rfl

private noncomputable def scalarExtendedPUnitIso
    (T : Type u) [CommRing T] [Algebra R T] :
    (ModuleCat.extendScalars (algebraMap R T)).obj (ModuleCat.of R PUnit) ≅
      ModuleCat.of T PUnit := by
  let e₁ :
      (ModuleCat.extendScalars (algebraMap R T)).obj (ModuleCat.of R PUnit) ≅
        ModuleCat.of T (T ⊗[R] PUnit) := by
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        (restrictScalarsSelfEquiv T)
        (LinearEquiv.refl R PUnit)).toModuleIso
  letI : Subsingleton (T ⊗[R] PUnit) := inferInstance
  let e₂ : ModuleCat.of T (T ⊗[R] PUnit) ≅ ModuleCat.of T PUnit :=
    (LinearEquiv.ofSubsingleton _ _).toModuleIso
  exact e₁ ≪≫ e₂

private noncomputable def restrictOfIso
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M) ≅ ModuleCat.of A M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) ≃ₗ[A] M from
      { __ := AddEquiv.refl _
        map_smul' := fun _ _ ↦ by simp }).toModuleIso

private theorem tensorNaiveCotangentChainComplex_d_eq_zero
    (P : Extension R S) (n : ℕ) :
    ((tensorNaiveCotangentChainComplex R' P : ChainComplex (ModuleCat R') ℕ)).d (n + 2) (n + 1) = 0 := by
  rw [tensorNaiveCotangentChainComplex, ChainComplex.mk'_d]
  simp

private theorem scalarExtendedNaiveCotangentChainComplex_d_eq_zero
    (P : Extension R S) (n : ℕ) :
    (scalarExtendedNaiveCotangentChainComplex R' P).d (n + 2) (n + 1) = 0 := by
  -- The scalar-extended complex is the image of the restricted two-term complex, so its higher
  -- differentials are the image of zero.
  rw [scalarExtendedNaiveCotangentChainComplex,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    Extension.naiveCotangentChainComplexRestrictScalars_d_succ_succ P R n]
  simpa using
    CategoryTheory.Functor.map_zero (ModuleCat.extendScalars (algebraMap R R'))
      ((P.naiveCotangentChainComplexRestrictScalars R).X (n + 2))
      ((P.naiveCotangentChainComplexRestrictScalars R).X (n + 1))

private theorem baseChangedNaiveCotangentChainComplex_d_eq_zero
    (P : Extension R S) (n : ℕ) :
    (baseChangedNaiveCotangentChainComplex R' P).d (n + 2) (n + 1) = 0 := by
  -- The base-changed presentation is also a two-term naive cotangent complex after restriction.
  let Q : Extension R' (R' ⊗[R] S) := baseChangedExtension R' P
  simpa [baseChangedNaiveCotangentChainComplex, baseChangedExtension, Q] using
    Extension.naiveCotangentChainComplexRestrictScalars_d_succ_succ Q R' n

private noncomputable def scalarExtendedNaiveCotangentChainComplexXIso
    (P : Extension R S) :
    ∀ n : ℕ,
      (scalarExtendedNaiveCotangentChainComplex R' P).X n ≅
        (tensorNaiveCotangentChainComplex R' P).X n
  | 0 => by
      let e :
          ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ⊗[R]
              ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S P.CotangentSpace))
            ≃ₗ[R'] R' ⊗[R] P.CotangentSpace :=
        TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv R')
          (restrictCotangentSpaceEquiv P)
      simpa [scalarExtendedNaiveCotangentChainComplex, tensorNaiveCotangentChainComplex,
        Extension.naiveCotangentChainComplexRestrictScalars, Extension.naiveCotangentChainComplex,
        ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using e.toModuleIso
  | 1 => by
      let e :
          ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ⊗[R]
              LiftCotangent P ≃ₗ[R'] R' ⊗[R] P.Cotangent :=
        TensorProduct.AlgebraTensorModule.congr
          (restrictScalarsSelfEquiv R')
          ((liftCotangentEquiv P).restrictScalars R)
      simpa [scalarExtendedNaiveCotangentChainComplex, tensorNaiveCotangentChainComplex,
        Extension.naiveCotangentChainComplexRestrictScalars, Extension.naiveCotangentChainComplex,
        ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using e.toModuleIso
  | n + 2 => by
      let succZeroR :
          ∀ {X₀ X₁ : ModuleCat.{u} R} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat.{u} R) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of.{u} R PUnit, 0, zero_comp⟩
      let succZeroR' :
          ∀ {X₀ X₁ : ModuleCat R'} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat R') (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of R' PUnit, 0, zero_comp⟩
      have hsrc :
          (scalarExtendedNaiveCotangentChainComplex R' P).X (n + 2) ≅
            ModuleCat.of R' PUnit := by
        let hX :
            (scalarExtendedNaiveCotangentChainComplex R' P).X (n + 2) =
              (ModuleCat.extendScalars (algebraMap R R')).obj
                ((P.naiveCotangentChainComplexRestrictScalars R).X (n + 2)) :=
          CategoryTheory.Functor.mapHomologicalComplex_obj_X
            (ModuleCat.extendScalars (algebraMap R R')) (ComplexShape.down ℕ)
            (P.naiveCotangentChainComplexRestrictScalars R) (n + 2)
        have hmkS : P.naiveCotangentChainComplex.X (n + 2) ≅ ModuleCat.of S PUnit := by
          simpa [Extension.naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of S P.CotangentSpace)
              (ModuleCat.of S (LiftCotangent P))
              (ModuleCat.ofHom (P.cotangentComplex.comp (liftCotangentEquiv P).toLinearMap))
              (fun {_ _} _ ↦ ⟨ModuleCat.of S PUnit, 0, zero_comp⟩) n)
        have hmk : (P.naiveCotangentChainComplexRestrictScalars R).X (n + 2) ≅
            ModuleCat.of R PUnit := by
          simpa [Extension.naiveCotangentChainComplexRestrictScalars] using
            (ModuleCat.restrictScalars (algebraMap R S)).mapIso hmkS ≪≫
              restrictOfIso PUnit
        simpa [scalarExtendedNaiveCotangentChainComplex] using
          eqToIso hX ≪≫ (ModuleCat.extendScalars (algebraMap R R')).mapIso hmk ≪≫
            scalarExtendedPUnitIso R'
      have htrg :
          (tensorNaiveCotangentChainComplex R' P).X (n + 2) ≅
            ModuleCat.of R' PUnit := by
        simpa [tensorNaiveCotangentChainComplex] using
          (ChainComplex.mk'XIso
            (ModuleCat.of R' (R' ⊗[R] P.CotangentSpace))
            (ModuleCat.of R' (R' ⊗[R] P.Cotangent))
            (ModuleCat.ofHom (LinearMap.baseChange R' (P.cotangentComplex.restrictScalars R)))
            succZeroR' n)
      exact hsrc ≪≫ htrg.symm

private theorem scalarExtendedNaiveCotangentChainComplexXIso_comm
    (P : Extension R S) :
    ∀ i j (_ : (ComplexShape.down ℕ).Rel i j),
      (scalarExtendedNaiveCotangentChainComplexXIso P i).hom ≫
          (tensorNaiveCotangentChainComplex R' P).d i j =
        (scalarExtendedNaiveCotangentChainComplex R' P).d i j ≫
          (scalarExtendedNaiveCotangentChainComplexXIso P j).hom := by
  -- Only the degree `1 → 0` differential is nontrivial; every higher differential vanishes.
  intro i j hij
  subst i
  cases j with
  | zero =>
      ext x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · have hL :
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                  (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
              0 = 0 := by
            rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.map_zero, LinearMap.map_zero]
        have hR :
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                  (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
              0 = 0 := by
            rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.map_zero, LinearMap.map_zero]
        exact hL.trans hR.symm
      · intro t x
        rcases x with ⟨x⟩
        change
          (LinearMap.baseChange R' (P.cotangentComplex.restrictScalars R))
              ((TensorProduct.AlgebraTensorModule.congr
                  (restrictScalarsSelfEquiv R')
                  ((liftCotangentEquiv P).restrictScalars R))
                (t ⊗ₜ[R] ULift.up x)) =
            (LinearMap.baseChange R'
              ((P.cotangentComplex.comp (liftCotangentEquiv P).toLinearMap).restrictScalars R))
              (t ⊗ₜ[R] ULift.up x)
        rfl
      · intro x y hx hy
        calc
          (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                  (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
              (x + y) =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                  (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
                x +
              (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                  (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
                y := by
                  simpa using
                    (LinearMap.map_add
                      (ModuleCat.Hom.hom
                        ((scalarExtendedNaiveCotangentChainComplexXIso P (0 + 1)).hom ≫
                          (tensorNaiveCotangentChainComplex R' P).d (0 + 1) 0))
                      x y)
          _ =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                  (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
                x +
              (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                  (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
                y := by rw [hx, hy]
          _ =
            (ModuleCat.Hom.hom
                ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                  (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
              (x + y) := by
                simpa using
                  (LinearMap.map_add
                    (ModuleCat.Hom.hom
                      ((scalarExtendedNaiveCotangentChainComplex R' P).d (0 + 1) 0 ≫
                        (scalarExtendedNaiveCotangentChainComplexXIso P 0).hom))
                    x y).symm
  | succ j =>
      rw [show (tensorNaiveCotangentChainComplex R' P).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using tensorNaiveCotangentChainComplex_d_eq_zero (P := P) j,
        show (scalarExtendedNaiveCotangentChainComplex R' P).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using scalarExtendedNaiveCotangentChainComplex_d_eq_zero
              (P := P) j]
      ext x
      have hL :
          (ModuleCat.Hom.hom
              ((scalarExtendedNaiveCotangentChainComplexXIso P (j + 2)).hom ≫
                (0 : (tensorNaiveCotangentChainComplex R' P).X (j + 2) ⟶
                  (tensorNaiveCotangentChainComplex R' P).X (j + 1))))
            x = 0 := by
        rfl
      have hR :
          (ModuleCat.Hom.hom
              ((0 : (scalarExtendedNaiveCotangentChainComplex R' P).X (j + 2) ⟶
                (scalarExtendedNaiveCotangentChainComplex R' P).X (j + 1)) ≫
                (scalarExtendedNaiveCotangentChainComplexXIso P (j + 1)).hom))
            x = 0 := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]
        change (ModuleCat.Hom.hom (scalarExtendedNaiveCotangentChainComplexXIso P (j + 1)).hom) 0 = 0
        simpa using
          (LinearMap.map_zero
            (ModuleCat.Hom.hom (scalarExtendedNaiveCotangentChainComplexXIso P (j + 1)).hom))
      simpa [Nat.add_assoc] using hL.trans hR.symm

private noncomputable def scalarExtendedNaiveCotangentChainComplexIso
    (P : Extension R S) :
    scalarExtendedNaiveCotangentChainComplex R' P ≅
      tensorNaiveCotangentChainComplex R' P :=
  HomologicalComplex.Hom.isoOfComponents
    (scalarExtendedNaiveCotangentChainComplexXIso P)
    (scalarExtendedNaiveCotangentChainComplexXIso_comm P)

private theorem tensorCotangent_baseChangeCotangentComplex_apply
    (P : Extension R S) [Module.Flat R R'] (x : R' ⊗[R] P.Cotangent) :
    (baseChangedExtension R' P).cotangentComplex (P.tensorCotangentOfFlat R' x) =
      (P.tensorCotangentSpace R')
        (LinearMap.baseChange R' (P.cotangentComplex.restrictScalars R) x) := by
  -- The base-change isomorphisms identify the conormal differential on pure tensors and hence
  -- on the whole tensor product by linearity.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Both comparison maps are linear, so they agree on the zero tensor.
    exact (LinearMap.map_zero _).trans (LinearEquiv.map_zero _).symm
  · intro t y
    rw [Extension.tensorCotangentOfFlat_tmul, LinearMap.baseChange_tmul,
      Extension.tensorCotangentSpace_tmul,
      ← baseChangedExtension_algebraMap_smul_cotangent P t
          (Cotangent.map (P.toBaseChange R') y)]
    have hs :
        (algebraMap R' (R' ⊗[R] S) t) •
            CotangentSpace.map (P.toBaseChange R') (P.cotangentComplex y) =
          t • CotangentSpace.map (P.toBaseChange R') (P.cotangentComplex y) :=
      baseChangedExtension_algebraMap_smul_cotangentSpace P t
        (CotangentSpace.map (P.toBaseChange R') (P.cotangentComplex y))
    rw [map_smul, ← Extension.CotangentSpace.map_cotangentComplex (P.toBaseChange R') y]
    simpa using hs
  · intro x y hx hy
    simp [map_add, hx, hy]

private noncomputable def tensorNaiveCotangentChainComplexXIso
    (P : Extension R S) [Module.Flat R R'] :
    ∀ n : ℕ,
      (tensorNaiveCotangentChainComplex R' P).X n ≅
        (baseChangedNaiveCotangentChainComplex R' P).X n
  | 0 => by
      let Q := baseChangedExtension R' P
      simpa [tensorNaiveCotangentChainComplex, baseChangedNaiveCotangentChainComplex,
        baseChangedExtension, Extension.naiveCotangentChainComplexRestrictScalars,
        Extension.naiveCotangentChainComplex] using
        (P.tensorCotangentSpace R').toModuleIso ≪≫
          (restrictOfIso Q.CotangentSpace).symm
  | 1 => by
      let Q := baseChangedExtension R' P
      simpa [tensorNaiveCotangentChainComplex, baseChangedNaiveCotangentChainComplex,
        baseChangedExtension, Extension.naiveCotangentChainComplexRestrictScalars,
        Extension.naiveCotangentChainComplex] using
        ((P.tensorCotangentOfFlat R').toModuleIso ≪≫
          (restrictOfIso Q.Cotangent).symm ≪≫
          (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))).mapIso
            ((liftCotangentEquiv Q).symm.toModuleIso))
  | n + 2 => by
      let succZero :
          ∀ {X₀ X₁ : ModuleCat R'} (f : X₁ ⟶ X₀),
            Σ' (X₂ : ModuleCat R') (d : X₂ ⟶ X₁), d ≫ f = 0 :=
        fun {_ _} _ ↦ ⟨ModuleCat.of R' PUnit, 0, zero_comp⟩
      have htensor :
          (tensorNaiveCotangentChainComplex R' P).X (n + 2) ≅
            ModuleCat.of R' PUnit := by
        simpa [tensorNaiveCotangentChainComplex] using
          (ChainComplex.mk'XIso
            (ModuleCat.of R' (R' ⊗[R] P.CotangentSpace))
            (ModuleCat.of R' (R' ⊗[R] P.Cotangent))
            (ModuleCat.ofHom (LinearMap.baseChange R' (P.cotangentComplex.restrictScalars R)))
            succZero n)
      have hbase :
          (baseChangedNaiveCotangentChainComplex R' P).X (n + 2) ≅
            ModuleCat.of R' PUnit := by
        let Q := baseChangedExtension R' P
        let succZeroQ :
            ∀ {X₀ X₁ : ModuleCat (R' ⊗[R] S)} (f : X₁ ⟶ X₀),
              Σ' (X₂ : ModuleCat (R' ⊗[R] S)) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
          fun {_ _} _ ↦ ⟨ModuleCat.of (R' ⊗[R] S) PUnit, 0, zero_comp⟩
        let hX :
            (baseChangedNaiveCotangentChainComplex R' P).X (n + 2) =
              (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))).obj
                (Q.naiveCotangentChainComplex.X (n + 2)) :=
          CategoryTheory.Functor.mapHomologicalComplex_obj_X
            (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))) (ComplexShape.down ℕ)
            Q.naiveCotangentChainComplex (n + 2)
        have hmk : Q.naiveCotangentChainComplex.X (n + 2) ≅
            ModuleCat.of (R' ⊗[R] S) PUnit := by
          simpa [Extension.naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of (R' ⊗[R] S) Q.CotangentSpace)
              (ModuleCat.of (R' ⊗[R] S) (LiftCotangent Q))
              (ModuleCat.ofHom (Q.cotangentComplex.comp (liftCotangentEquiv Q).toLinearMap))
              succZeroQ n)
        simpa [baseChangedNaiveCotangentChainComplex] using
          eqToIso hX ≪≫ (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))).mapIso hmk ≪≫
            restrictOfIso PUnit
      exact htensor ≪≫ hbase.symm

private theorem tensorNaiveCotangentChainComplexXIso_comm
    (P : Extension R S) [Module.Flat R R'] :
    ∀ i j (_ : (ComplexShape.down ℕ).Rel i j),
      (tensorNaiveCotangentChainComplexXIso P i).hom ≫
          (baseChangedNaiveCotangentChainComplex R' P).d i j =
        (tensorNaiveCotangentChainComplex R' P).d i j ≫
          (tensorNaiveCotangentChainComplexXIso P j).hom := by
  -- Route correction: the only nontrivial square is again `1 → 0`; higher squares collapse
  -- immediately because both complexes are two-term.
  intro i j hij
  subst i
  cases j with
  | zero =>
      ext x
      simpa [tensorNaiveCotangentChainComplex, baseChangedNaiveCotangentChainComplex,
        baseChangedExtension, Extension.naiveCotangentChainComplexRestrictScalars,
        Extension.naiveCotangentChainComplex, LinearMap.comp_assoc] using
        tensorCotangent_baseChangeCotangentComplex_apply (P := P) (R' := R') x
  | succ j =>
      rw [show (baseChangedNaiveCotangentChainComplex R' P).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using baseChangedNaiveCotangentChainComplex_d_eq_zero
              (P := P) j,
        show (tensorNaiveCotangentChainComplex R' P).d (j + 1 + 1) (j + 1) = 0 by
            simpa [Nat.add_assoc] using tensorNaiveCotangentChainComplex_d_eq_zero (P := P) j]
      ext x
      have hL :
          (ModuleCat.Hom.hom
              ((tensorNaiveCotangentChainComplexXIso P (j + 2)).hom ≫
                (0 : (baseChangedNaiveCotangentChainComplex R' P).X (j + 2) ⟶
                  (baseChangedNaiveCotangentChainComplex R' P).X (j + 1))))
            x = 0 := by
        rfl
      have hR :
          (ModuleCat.Hom.hom
              ((0 : (tensorNaiveCotangentChainComplex R' P).X (j + 2) ⟶
                (tensorNaiveCotangentChainComplex R' P).X (j + 1)) ≫
                (tensorNaiveCotangentChainComplexXIso P (j + 1)).hom))
            x = 0 := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply]
        change (ModuleCat.Hom.hom (tensorNaiveCotangentChainComplexXIso P (j + 1)).hom) 0 = 0
        simpa using
          (LinearMap.map_zero
            (ModuleCat.Hom.hom (tensorNaiveCotangentChainComplexXIso P (j + 1)).hom))
      simpa [Nat.add_assoc] using hL.trans hR.symm

private noncomputable def tensorNaiveCotangentChainComplexIso
    (P : Extension R S) [Module.Flat R R'] :
    tensorNaiveCotangentChainComplex R' P ≅
      baseChangedNaiveCotangentChainComplex R' P :=
  HomologicalComplex.Hom.isoOfComponents
    (tensorNaiveCotangentChainComplexXIso P)
    (tensorNaiveCotangentChainComplexXIso_comm P)

private noncomputable def naiveCotangent_tensor_comparison_to_baseChangePresentation_iso
    [Module.Flat R R'] :
    (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (NL_{S⁄R}↾[R])) ≅
      (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
       E.naiveCotangentChainComplexRestrictScalars R') := by
  let P : Extension R S := (Generators.self R S).toExtension
  let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
  simpa [scalarExtendedNaiveCotangentChainComplex, baseChangedNaiveCotangentChainComplex,
    baseChangedExtension, Algebra.naiveCotangent, E] using
    scalarExtendedNaiveCotangentChainComplexIso P ≪≫
      tensorNaiveCotangentChainComplexIso P

private noncomputable def baseChangeExtensionToPresentationHomotopyEquiv [Module.Flat R R'] :
    HomotopyEquiv
      (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
       E.naiveCotangentChainComplexRestrictScalars R')
      (let P' : Generators R' (R' ⊗[R] S) S := selfBaseChangedGenerators
       P'.toExtension.naiveCotangentChainComplexRestrictScalars R') := by
  let F :=
    (ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))).mapHomologicalComplex (ComplexShape.down ℕ)
  let P := Generators.self R S
  let P' : Generators R' (R' ⊗[R] S) S := selfBaseChangedGenerators
  refine
    { hom := F.map (Extension.naiveCotangentChainMap (P.baseChangeFromBaseChange R'))
      inv := F.map (Extension.naiveCotangentChainMap (P.baseChangeToBaseChange R'))
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · -- The two presentation maps are inverse on the source base-changed polynomial ring.
    have hfg :
        (P.baseChangeToBaseChange R').comp (P.baseChangeFromBaseChange R') =
          .id (P.toExtension.baseChange (T := R')) := by
      ext x
      change
        (MvPolynomial.algebraTensorAlgEquiv (σ := S) R R').symm
            ((MvPolynomial.algebraTensorAlgEquiv (σ := S) R R') x) = x
      exact (MvPolynomial.algebraTensorAlgEquiv (σ := S) R R').symm_apply_apply x
    exact Homotopy.ofEq <| by
      rw [← F.map_comp,
        ← Extension.naiveCotangentChainMap_comp (P.baseChangeFromBaseChange R')
          (P.baseChangeToBaseChange R'),
        hfg, Extension.naiveCotangentChainMap_id, F.map_id]
  · -- The reverse composition is the identity on the target base-changed presentation.
    have hgf :
        (P.baseChangeFromBaseChange R').comp (P.baseChangeToBaseChange R') =
          .id P'.toExtension := by
      ext x
      change
        (MvPolynomial.algebraTensorAlgEquiv (σ := S) R R')
            ((MvPolynomial.algebraTensorAlgEquiv (σ := S) R R').symm x) = x
      exact (MvPolynomial.algebraTensorAlgEquiv (σ := S) R R').apply_symm_apply x
    exact Homotopy.ofEq <| by
      rw [← F.map_comp,
        ← Extension.naiveCotangentChainMap_comp (P.baseChangeToBaseChange R')
          (P.baseChangeFromBaseChange R'),
        hgf, Extension.naiveCotangentChainMap_id, F.map_id]

private noncomputable def baseChangePresentationToOwnerHomotopyEquiv [Module.Flat R R'] :
    HomotopyEquiv
      (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
       E.naiveCotangentChainComplexRestrictScalars R')
      NL_{R' ⊗[R] S⁄R'}↾[R'] := by
  let G := ModuleCat.restrictScalars (algebraMap R' (R' ⊗[R] S))
  let P' : Generators R' (R' ⊗[R] S) S := selfBaseChangedGenerators
  let e :=
    Generators.naiveCotangentChainHomotopyEquiv
      P'
      (Generators.self R' (R' ⊗[R] S))
  have eRaw :
      HomotopyEquiv
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P'.toExtension.naiveCotangentChainComplex)
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Generators.self R' (R' ⊗[R] S)).toExtension.naiveCotangentChainComplex) :=
    G.mapHomotopyEquiv e
  let e' :
      HomotopyEquiv
        (P'.toExtension.naiveCotangentChainComplexRestrictScalars R')
        ((Generators.self R' (R' ⊗[R] S)).toExtension.naiveCotangentChainComplexRestrictScalars
          R') := by
    simpa [Extension.naiveCotangentChainComplexRestrictScalars] using eRaw
  exact (baseChangeExtensionToPresentationHomotopyEquiv).trans e'

-- Proof sketch: rewrite the scalar extension of `NL_{S⁄R}` as the private tensor model with
-- degree `1` normalized from `R' ⊗[R] ULift(I / I²)` to `R' ⊗[R] (I / I²)`. The flat base-change
-- isomorphisms `tensorCotangentSpace` and `tensorCotangentOfFlat` identify that tensor model with
-- the restricted owner complex `NL_{R' ⊗[R] S⁄R'}`.
/-- Lemma 10.134.8 (Flat base change): if `R → R'` is flat, then the canonical base-change map
from the scalar extension of `NL_{S⁄R}` to `NL_{R' ⊗[R] S⁄R'}`, both viewed as chain complexes of
`R'`-modules, is the owner-level comparison morphism induced by the flat base-change
identifications on the degree `0` and degree `1` terms. -/
noncomputable def naiveCotangent_tensor_comparison_of_flat [Module.Flat R R'] :
    (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (NL_{S⁄R}↾[R])) ⟶
      NL_{R' ⊗[R] S⁄R'}↾[R'] := by
  let e₁ :
      (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (NL_{S⁄R}↾[R])) ≅
        (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
         E.naiveCotangentChainComplexRestrictScalars R') :=
    naiveCotangent_tensor_comparison_to_baseChangePresentation_iso
  let e₂ :
      HomotopyEquiv
        (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
         E.naiveCotangentChainComplexRestrictScalars R')
        NL_{R' ⊗[R] S⁄R'}↾[R'] :=
    baseChangePresentationToOwnerHomotopyEquiv
  exact e₁.hom ≫ e₂.hom

/-- Lemma 10.134.8 (Flat base change): if `R → R'` is flat, then the canonical base-change map
from the scalar extension of `NL_{S⁄R}` to `NL_{R' ⊗[R] S⁄R'}`, both viewed as chain complexes of
`R'`-modules, is a homotopy equivalence. -/
noncomputable def naiveCotangent_tensor_homotopyEquiv_of_flat [Module.Flat R R'] :
    HomotopyEquiv
      (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (NL_{S⁄R}↾[R]))
      NL_{R' ⊗[R] S⁄R'}↾[R'] := by
  let e₁ :
      (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (NL_{S⁄R}↾[R])) ≅
        (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
         E.naiveCotangentChainComplexRestrictScalars R') :=
    naiveCotangent_tensor_comparison_to_baseChangePresentation_iso
  let e₂ :
      HomotopyEquiv
        (let E : Extension R' (R' ⊗[R] S) := selfBaseChangedExtension
         E.naiveCotangentChainComplexRestrictScalars R')
        NL_{R' ⊗[R] S⁄R'}↾[R'] :=
    baseChangePresentationToOwnerHomotopyEquiv
  exact (HomotopyEquiv.ofIso e₁).trans e₂

/- The induced identification on first homology is the canonical owner theorem
`Algebra.tensorH1CotangentOfFlat`. -/
recall Algebra.tensorH1CotangentOfFlat

end
