import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.Equivalence
import StacksProject_2024.Chap13.Lemma_13_6_6
import StacksProject_2024.Chap13.Lemma_13_5_8
import StacksProject_2024.Chap13.Lemma_13_10_6
import StacksProject_2024.Chap13.Lemma_13_11_6
import StacksProject_2024.Chap13.«13_17_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open scoped DerivedCategoryWithCohomologyIn ZeroObject

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace _root_.CategoryTheory.ObjectProperty

section

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsWeakSerreClass]

/-- Helper for Lemma 13.17.4: the quasi-isomorphisms in `K^-(A)` are the morphisms whose images
in `K(A)` are quasi-isomorphisms. -/
abbrev boundedAboveHomotopyQuasiIso :
    MorphismProperty (K⁻(A)) :=
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
    (HomotopyCategory.minus A).ι

/-- Helper for Lemma 13.17.4: the bounded-above acyclic owner on `K^-(A)`. -/
abbrev boundedAboveAcyclicHomotopyProperty : ObjectProperty (K⁻(A)) :=
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (HomotopyCategory.minus A))

/-- Helper for Lemma 13.17.4: the homotopy-to-derived functor on `K^-(A)` lands in `D^-(A)`. -/
theorem qh_obj_mem_t_minus
    (X : K⁻(A)) :
    (t.minus : ObjectProperty (D(A))) (DerivedCategory.Qh.obj X.obj) := by
  let K : CochainComplex A ℤ := X.obj.as
  have hK : CochainComplex.minus A K := by
    simpa [K, HomotopyCategory.minus] using X.property
  rcases hK with ⟨n, hn⟩
  letI : K.IsStrictlyLE n := by
    simpa [K] using hn
  letI : K.IsLE n := inferInstance
  let e : DerivedCategory.Qh.obj X.obj ≅ DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso A).app K
  have hQ : (t.minus : ObjectProperty (D(A))) (DerivedCategory.Q.obj K) := by
    refine ⟨n, ?_⟩
    change (DerivedCategory.Q.obj K).IsLE n
    exact (DerivedCategory.isLE_Q_obj_iff K n).2 inferInstance
  -- Proof comment: compare the bounded-above homotopy object with its chosen cochain
  -- representative in the unbounded derived category and transport the cutoff across the iso.
  exact (t.minus : ObjectProperty (D(A))).prop_of_iso e.symm hQ

/-- Helper for Lemma 13.17.4: the canonical functor `K^-(A) ⟶ D^-(A)`. -/
abbrev mapBoundedAboveHomotopyToDerivedAbove :
    K⁻(A) ⥤ D⁻(A) :=
  (t.minus : ObjectProperty (D(A))).lift
    ((HomotopyCategory.minus A).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_minus

/-- Helper for Lemma 13.17.4: the Verdier morphism property of bounded-above acyclic complexes is
exactly the bounded-above quasi-isomorphism property. -/
theorem boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso :
    (show MorphismProperty (K⁻(A)) from boundedAboveAcyclicHomotopyProperty.trW) =
      (show MorphismProperty (K⁻(A)) from boundedAboveHomotopyQuasiIso) := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedAboveHomotopyQuasiIso, HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]

/-- Helper for Lemma 13.17.4: the bounded-above derived functor inverts bounded-above acyclic
denominators. -/
theorem mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW :
    MorphismProperty.IsInvertedBy
      (show MorphismProperty (K⁻(A)) from boundedAboveAcyclicHomotopyProperty.trW)
      (show K⁻(A) ⥤ D⁻(A) from mapBoundedAboveHomotopyToDerivedAbove) := by
  intro X Y f hf
  let ιminus : D⁻(A) ⥤ D(A) := (t.minus : ObjectProperty (D(A))).ι
  have hQis : boundedAboveHomotopyQuasiIso f := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso] using hf
  have hUnderlying :
      IsIso (((HomotopyCategory.minus A).ι ⋙ DerivedCategory.Qh).map f) := by
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.minus A).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(A) ⥤ D(A))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      ((HomotopyCategory.minus A).ι.map f)
      (by simpa [boundedAboveHomotopyQuasiIso] using hQis)
  have hLifted :
      IsIso (ιminus.map (mapBoundedAboveHomotopyToDerivedAbove.map f)) := by
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(A)))
          ((HomotopyCategory.minus A).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_minus)
        f)).2 hUnderlying
  let _ : IsIso (ιminus.map (mapBoundedAboveHomotopyToDerivedAbove.map f)) := hLifted
  exact isIso_of_fully_faithful ιminus (mapBoundedAboveHomotopyToDerivedAbove.map f)

/- Domain-style sampling for Lemma 13.17.4:
- primary domain: bounded-above derived categories of a Serre full subcategory and the canonical
  comparison with the bounded-above part of `D_{P}(A)`;
- sampled owner declarations:
  `P.ι.mapDerivedCategory`,
  `weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn`,
  `derivedCategoryBoundedAboveCohomologyInProperty`,
  `ObjectProperty.lift`;
- best owner abstraction: the primitive owner is the derived functor
  `P.ι.mapDerivedCategory : D(P.FullSubcategory) ⥤ D(A)` of the inclusion
  `P.ι : P.FullSubcategory ⥤ A`, together with the chapter owner
  `derivedCategoryBoundedAboveCohomologyInProperty P` on `D⁻(A)`;
- primitive-vs-derived split:
  primitive data: the inclusion `P.ι : P.FullSubcategory ⥤ A`, its derived functor
    `P.ι.mapDerivedCategory`, and the owner property
    `derivedCategoryBoundedAboveCohomologyInProperty P` on `D⁻(A)`;
  derived API: the bounded-above landing theorem and the induced lift
    `D⁻(P.FullSubcategory) ⥤ D⁻_{P}`;
- source/core/bridge triage:
  `source-facing`: the bounded-above comparison functor and its equivalence criterion;
  `core/canonical`: `P.ι.mapDerivedCategory`,
    `weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn P`,
    `derivedCategoryBoundedAboveCohomologyInProperty P`, and `ObjectProperty.lift`;
  `bridge/view`: the bounded-above lift of the primitive derived inclusion functor.

The local `Abelian P.FullSubcategory` wrapper was duplicate API: for a weak Serre class, the canonical
mathlib instance on `P.FullSubcategory` is already available and is reused directly here. -/

local instance : PreservesFiniteLimits P.ι :=
  weakSerreSubcategory_inclusion_preservesFiniteLimits P

local instance : PreservesFiniteColimits P.ι :=
  weakSerreSubcategory_inclusion_preservesFiniteColimits P

-- Proof sketch: `13_17_1_1` already proves the cohomology-in-`P` half for
-- `P.ι.mapDerivedCategory`. For bounded-above-ness, represent `X` by a bounded-above cochain
-- complex in `P.FullSubcategory`; applying `P.ι` termwise preserves strict bounded-above support,
-- so the image in `D(A)` still lies in `t.minus`.
/-- The derived functor of the inclusion `P.ι : P.FullSubcategory ⥤ A` preserves
bounded-above-ness. -/
theorem weakSerreSubcategory_mapDerivedCategory_obj_mem_boundedAboveDerivedCategory
    (X : D⁻(P.FullSubcategory)) :
    (t.minus : ObjectProperty (D(A))) ((t.minus.ι ⋙ P.ι.mapDerivedCategory).obj X) := by
  change (t.minus : ObjectProperty (D(A))) ((P.ι.mapDerivedCategory).obj X.obj)
  rcases X.property with ⟨n, hX⟩
  let _ : X.obj.IsLE n := hX
  obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X.obj n
  let e' :
      ((P.ι.mapDerivedCategory).obj X.obj) ≅
        DerivedCategory.Q.obj
          ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (P.ι.mapDerivedCategory).mapIso e ≪≫ (P.ι.mapDerivedCategoryFactors.app K)
  exact ⟨n, t.isLE_of_iso e'.symm n⟩

/-- The bounded-above restriction of the canonical comparison functor
`D⁻(P.FullSubcategory) ⥤ D⁻_{P}`. -/
@[stacks 0FCL]
noncomputable abbrev weakSerreSubcategoryDerivedComparisonFunctorMinus :
    D⁻(P.FullSubcategory) ⥤ D⁻_{P} :=
  (derivedCategoryBoundedAboveCohomologyInProperty P).lift
    ((t.minus : ObjectProperty (D(A))).lift
      (t.minus.ι ⋙ P.ι.mapDerivedCategory)
      (weakSerreSubcategory_mapDerivedCategory_obj_mem_boundedAboveDerivedCategory P))
    (fun X ↦ by
      simpa using
        weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn P
          (((t.minus : ObjectProperty (D(P.FullSubcategory))).ι).obj X))

end

section

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

/-- Helper for Lemma 13.17.4: in the Serre-class section, the inclusion `P.ι` still preserves
finite limits. -/
local instance : PreservesFiniteLimits P.ι :=
  weakSerreSubcategory_inclusion_preservesFiniteLimits P

/-- Helper for Lemma 13.17.4: in the Serre-class section, the inclusion `P.ι` still preserves
finite colimits. -/
local instance : PreservesFiniteColimits P.ι :=
  weakSerreSubcategory_inclusion_preservesFiniteColimits P

/-- Helper for Lemma 13.17.4: once the bounded-above comparison functor is full, faithful, and
essentially surjective, it is an equivalence. -/
private theorem comparisonFunctorMinus_isEquivalence_of_full_faithful_essSurj
    [Functor.Full (weakSerreSubcategoryDerivedComparisonFunctorMinus P)]
    [Functor.Faithful (weakSerreSubcategoryDerivedComparisonFunctorMinus P)]
    (hEss : (weakSerreSubcategoryDerivedComparisonFunctorMinus P).EssSurj) :
    Functor.IsEquivalence (weakSerreSubcategoryDerivedComparisonFunctorMinus P) := by
  -- This is the standard final assembly step once the three source-proof outputs are available.
  letI : (weakSerreSubcategoryDerivedComparisonFunctorMinus P).EssSurj := hEss
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- Helper for Lemma 13.17.4: the canonical bounded-above functor obtained by applying `P.ι`
termwise on homotopy objects and then passing to the bounded-above derived category. -/
private abbrev mapBoundedAboveHomotopyCategoryToDerivedAbove :
    K⁻(P.FullSubcategory) ⥤ D⁻(A) :=
  mapBoundedAboveHomotopyCategory P.ι ⋙ mapBoundedAboveHomotopyToDerivedAbove

/-- Helper for Lemma 13.17.4: forgetting the bounded-above target of the termwise-derived
comparison agrees with the ambient homotopy-to-derived functor. -/
private noncomputable abbrev mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso :
    mapBoundedAboveHomotopyCategoryToDerivedAbove P ⋙
      (t.minus : ObjectProperty (D(A))).ι ≅
    (HomotopyCategory.minus (P.FullSubcategory)).ι ⋙
      (P.ι.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
  -- Proof comment: reassociate the bounded-above source functor, identify the bounded-above
  -- derived target with the ambient homotopy-to-derived functor, and then rewrite the bounded
  -- source inclusion of `K^-(P)` into `K(P)` by the canonical lift comparison.
  exact
    (Functor.associator
      (mapBoundedAboveHomotopyCategory P.ι)
      mapBoundedAboveHomotopyToDerivedAbove
      ((t.minus : ObjectProperty (D(A))).ι)).symm ≪≫
      Functor.isoWhiskerLeft
        (mapBoundedAboveHomotopyCategory P.ι)
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(A)))
          ((HomotopyCategory.minus A).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_minus) ≪≫
      Functor.associator
        (mapBoundedAboveHomotopyCategory P.ι)
        (HomotopyCategory.minus A).ι
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerRight
        ((HomotopyCategory.minus A).liftCompιIso
          ((HomotopyCategory.minus (P.FullSubcategory)).ι ⋙
            P.ι.mapHomotopyCategory (ComplexShape.up ℤ))
          (mapHomotopyCategory_obj_mem_boundedAbove P.ι))
        DerivedCategory.Qh

/-- Helper for Chap13 Lemma 13 17 4: the epi-lift hypothesis already implies that every object of
`A` contains a monomorphic subobject lying in `P`. -/
private theorem exists_property_subobject_of_epi_lift
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f))
    (X : A) :
    ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι := by
  let Y : P.FullSubcategory :=
    ⟨(0 : A), by simpa using ObjectProperty.prop_zero P⟩
  let f : X ⟶ Y.obj := 0
  have hf : Epi f := by
    simpa using (inferInstance : Epi (0 : X ⟶ (0 : A)))
  -- Proof comment: specialize the source hypothesis to the canonical epimorphism `X ⟶ 0`.
  obtain ⟨X', ι, hmono, _⟩ := hP Y f
  exact ⟨X', ι, hmono⟩

/-- Helper for Chap13 Lemma 13 17 4: the bounded-above homotopy objects whose cochain terms all
lie in `P`. -/
private abbrev termwiseObjectProperty
    (P : ObjectProperty A) : ObjectProperty (K⁻(A)) :=
  fun X ↦
    let K : CochainComplex A ℤ := X.obj.as
    ∀ n : ℤ, P (K.X n)

/-- Helper for Chap13 Lemma 13 17 4: a bounded-above homotopy object whose terms lie in `P`
canonically packages into a bounded-above cochain complex in `P.FullSubcategory`. -/
private abbrev toBoundedAboveFullSubcategoryComplex
    {X : K⁻(A)} (hX : termwiseObjectProperty P X) :
    Comp⁻(P.FullSubcategory) := by
  let K : CochainComplex A ℤ := X.obj.as
  let K' : CochainComplex (P.FullSubcategory) ℤ :=
    { X n := ⟨K.X n, hX n⟩
      d i j := ObjectProperty.homMk (K.d i j)
      shape i j hij := by
        simp [K.shape i j hij]
      d_comp_d' i j k hij hjk := by
        ext
        simp [K.d_comp_d' i j k hij hjk] }
  let a : ℤ := ((CochainComplex.minus_iff A K).1 X.property).choose
  let hK : K.IsStrictlyLE a := ((CochainComplex.minus_iff A K).1 X.property).choose_spec
  have hK' : K'.IsStrictlyLE a := by
    rw [CochainComplex.isStrictlyLE_iff] at hK ⊢
    intro n hn
    refine (IsZero.iff_id_eq_zero _).2 ?_
    simpa [K'] using
      congrArg ObjectProperty.homMk ((IsZero.iff_id_eq_zero _).1 (hK n hn))
  -- Proof comment: rebuild the same bounded-above complex inside the full subcategory by
  -- upgrading each term and differential to `P.FullSubcategory`.
  exact ⟨K', (CochainComplex.minus_iff (P.FullSubcategory) K').2 ⟨a, hK'⟩⟩

/-- Helper for Chap13 Lemma 13 17 4: a termwise-`P` bounded-above homotopy object yields the
corresponding bounded-above derived object of `P.FullSubcategory`. -/
private abbrev toBoundedAboveDerivedInFullSubcategory
    {X : K⁻(A)} (hX : termwiseObjectProperty P X) :
    D⁻(P.FullSubcategory) :=
  let K' : Comp⁻(P.FullSubcategory) := toBoundedAboveFullSubcategoryComplex P hX
  mapBoundedAboveHomotopyToDerivedAbove.obj
    ((HomotopyCategory.Minus.quotient (P.FullSubcategory)).obj K')

/-- Helper for Lemma 13.17.4: the bounded-above homotopy objects whose derived image already lies
in `D^-_P(A)`. -/
private abbrev minusCohomologyObjectProperty
    (P : ObjectProperty A) : ObjectProperty (K⁻(A)) :=
  ObjectProperty.inverseImage
    (derivedCategoryBoundedAboveCohomologyInProperty P)
    mapBoundedAboveHomotopyToDerivedAbove

/-- Helper for Lemma 13.17.4: inside the bounded-above homotopy objects whose derived image lies
in `D^-_P(A)`, the source subcategory consists of those objects whose cochain terms are already in
`P`. -/
private abbrev termwiseMinusCohomologyObjectProperty
    (P : ObjectProperty A) :
    ObjectProperty (minusCohomologyObjectProperty P).FullSubcategory :=
  fun X ↦ termwiseObjectProperty P X.obj

/-- Helper for Lemma 13.17.4: the restricted localization system on bounded-above homotopy
objects whose derived image lies in `D^-_P(A)`. -/
  private abbrev minusCohomologyLocalizationSystem
    (P : ObjectProperty A) :
    MorphismProperty (minusCohomologyObjectProperty P).FullSubcategory :=
  boundedAboveAcyclicHomotopyProperty.trW.inverseImage
    (minusCohomologyObjectProperty P).ι

/-- Helper for Lemma 13.17.4: a bounded-above quasi-isomorphism in the minus-cohomology full
subcategory is a denominator for the restricted localization system. -/
private theorem minusCohomologyLocalizationSystem_of_quasiIso
    {X Y : (minusCohomologyObjectProperty P).FullSubcategory}
    (f : X ⟶ Y)
    (hf : boundedAboveHomotopyQuasiIso f.hom) :
    minusCohomologyLocalizationSystem P f := by
  -- Proof comment: the restricted localization system is the pullback of bounded-above acyclic
  -- denominators along the full-subcategory inclusion, so it suffices to rewrite it as `Qis⁻`.
  change boundedAboveAcyclicHomotopyProperty.trW f.hom
  let htrW :
      (show MorphismProperty (K⁻(A)) from boundedAboveAcyclicHomotopyProperty.trW) =
        (show MorphismProperty (K⁻(A)) from boundedAboveHomotopyQuasiIso) :=
    boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
  simpa [htrW] using hf

/-- Helper for Chap13 Lemma 13 17 4: forgetting a bounded-above homotopy object of
`P.FullSubcategory` to `A` preserves the termwise-`P` condition degreewise. -/
private theorem mapBoundedAboveHomotopyCategory_termwiseObjectProperty
    (X : K⁻(P.FullSubcategory)) :
    termwiseObjectProperty P ((mapBoundedAboveHomotopyCategory P.ι).obj X) := by
  let K := X.obj.as
  intro n
  -- Proof comment: the bounded-above forgetful functor is induced termwise from `P.ι`, so the
  -- degree-`n` term is literally the underlying ambient object of the source degree-`n` term.
  simpa [termwiseObjectProperty, Functor.mapHomotopyCategory_obj,
    Functor.mapHomologicalComplex_obj_X] using (K.X n).property

/-- Helper for Chap13 Lemma 13 17 4: the source bounded-above homotopy category of
`P.FullSubcategory` forgets into the bounded-above homotopy full subcategory cut out by the
termwise-`P` condition on `A`. -/
private abbrev termwiseBoundedAboveForgetFunctor :
    K⁻(P.FullSubcategory) ⥤ (termwiseObjectProperty P).FullSubcategory :=
  (termwiseObjectProperty P).lift
    (mapBoundedAboveHomotopyCategory P.ι)
    (mapBoundedAboveHomotopyCategory_termwiseObjectProperty P)

/-- Helper for Chap13 Lemma 13 17 4: every termwise-`P` bounded-above homotopy object comes from
an object of `K^-(P.FullSubcategory)` by forgetting termwise. -/
private theorem termwiseBoundedAboveForgetFunctor_essSurj :
    (termwiseBoundedAboveForgetFunctor P).EssSurj := by
  exact
    Functor.essSurj_of_surj (fun X ↦ by
      let K' : Comp⁻(P.FullSubcategory) := toBoundedAboveFullSubcategoryComplex P X.property
      let Y : K⁻(P.FullSubcategory) :=
        (HomotopyCategory.Minus.quotient (P.FullSubcategory)).obj K'
      -- Proof comment: package the termwise-`P` bounded-above object back into a bounded-above
      -- complex in `P.FullSubcategory`; forgetting it again is definitionally the original object.
      refine ⟨Y, ?_⟩
      cases X
      rfl)

/-- Helper for Chap13 Lemma 13 17 4: applying the inclusion `P.ι` termwise to cochain complexes is
fully faithful. -/
private noncomputable def mapHomologicalComplexFullyFaithful :
    (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).FullyFaithful := by
  let hFF : P.ι.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful P.ι
  refine
    { preimage := fun {K L} f ↦
        { f := fun i ↦ hFF.preimage (f.f i)
          comm' := fun i j hij ↦ by
            -- Proof comment: each differential square in the ambient complex is already
            -- commutative, so fully faithfulness of `P.ι` reflects it back degreewise.
            apply ObjectProperty.hom_ext
            have hi : (hFF.preimage (f.f i)).hom = f.f i := by
              simpa using (hFF.map_preimage (f.f i))
            have hj : (hFF.preimage (f.f j)).hom = f.f j := by
              simpa using (hFF.map_preimage (f.f j))
            simpa [hi, hj] using f.comm i j }
      map_preimage := fun {K L} f ↦ by
        -- Proof comment: after forgetting termwise, the preimaged chain map has exactly the
        -- original ambient components, so extensionality on chain maps closes the goal.
        ext i
        exact hFF.map_preimage (f.f i)
      preimage_map := fun {K L} f ↦ by
        -- Proof comment: componentwise preimages of an already forgotten chain map recover the
        -- original chain map by faithful cancellation.
        ext i
        simpa using congrArg (fun k => k.hom) (hFF.preimage_map (f.f i)) }

/-- Helper for Chap13 Lemma 13 17 4: a homotopy between the termwise images of two chain maps in
`A` already comes from a homotopy before forgetting from `P.FullSubcategory`. -/
private noncomputable def mapHomologicalComplexReflectsHomotopy
    {K L : CochainComplex (P.FullSubcategory) ℤ}
    {f g : K ⟶ L}
    (h :
      Homotopy
        ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
        ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :
    Homotopy f g := by
  let hFF : P.ι.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful P.ι
  refine
    { hom := fun i j ↦ hFF.preimage (h.hom i j)
      zero := fun i j hij ↦ by
        -- Proof comment: the ambient homotopy is zero off the predecessor relation, and the
        -- fully faithful inclusion reflects that vanishing componentwise.
        apply ObjectProperty.hom_ext
        have hij' : (hFF.preimage (h.hom i j)).hom = h.hom i j := by
          simpa using (hFF.map_preimage (h.hom i j))
        simpa [hij'] using h.zero i j hij
      comm := fun i ↦ by
        -- Proof comment: apply `P.ι` to the reflected homotopy equation and simplify the
        -- resulting `dNext` and `prevD` terms using `preimage_comp` and `map_preimage`.
        have hnext :
            (hFF.preimage (h.hom ((ComplexShape.up ℤ).next i) i)).hom =
              h.hom ((ComplexShape.up ℤ).next i) i := by
          simpa using hFF.map_preimage (h.hom ((ComplexShape.up ℤ).next i) i)
        have hprev :
            (hFF.preimage (h.hom i ((ComplexShape.up ℤ).prev i))).hom =
              h.hom i ((ComplexShape.up ℤ).prev i) := by
          simpa using hFF.map_preimage (h.hom i ((ComplexShape.up ℤ).prev i))
        apply ObjectProperty.hom_ext
        change (f.f i).hom =
          (K.d i ((ComplexShape.up ℤ).next i)).hom ≫
              (hFF.preimage (h.hom ((ComplexShape.up ℤ).next i) i)).hom +
            (hFF.preimage (h.hom i ((ComplexShape.up ℤ).prev i))).hom ≫
              (L.d ((ComplexShape.up ℤ).prev i) i).hom +
            (g.f i).hom
        simpa [Category.assoc, hnext, hprev] using h.comm i }

/-- Helper for Chap13 Lemma 13 17 4: the inclusion `P.ι` induces a fully faithful functor on the
ambient homotopy categories. -/
private noncomputable def mapHomotopyCategoryFullyFaithful :
    (P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).FullyFaithful := by
  let hFF :
      (P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).FullyFaithful :=
    mapHomologicalComplexFullyFaithful P
  refine
    { preimage := fun {X Y} f ↦
        let α :
            X.as ⟶ Y.as :=
          hFF.preimage f.out
        -- Proof comment: choose the chain-level representative `f.out` in the ambient homotopy
        -- category and pull it back componentwise through the fully faithful inclusion.
        (HomotopyCategory.quotient (P.FullSubcategory) (ComplexShape.up ℤ)).map α
      map_preimage := fun {X Y} f ↦ by
        -- Proof comment: the ambient image of the chosen preimage representative is still
        -- `f.out`, and quotienting that representative recovers `f`.
        dsimp
        exact
          (congrArg
            (fun α ↦
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α)
            (hFF.map_preimage f.out)).trans
            (HomotopyCategory.quotient_map_out f)
      preimage_map := fun {X Y} f ↦ by
        -- Proof comment: compare the chain representatives of the image and use reflected
        -- homotopies to descend equality from `K(A)` back to `K(P)`.
        rw [← HomotopyCategory.quotient_map_out f]
        let hEq :
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                (((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f).out) =
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map f.out) := by
          have hEq₁ :
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                  (((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f).out) =
                (P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f := by
            simpa using
              (HomotopyCategory.quotient_map_out
                ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f))
          have hEq₂ :
              (P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f =
                (P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
                  ((HomotopyCategory.quotient (P.FullSubcategory) (ComplexShape.up ℤ)).map f.out) := by
            -- Proof comment: after rewriting `f` by its chosen chain representative in the
            -- source homotopy category, the ambient image is definitionally unchanged.
            rw [HomotopyCategory.quotient_map_out]
            rfl
          have hEq₃ :
              (P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
                  ((HomotopyCategory.quotient (P.FullSubcategory) (ComplexShape.up ℤ)).map f.out) =
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                  ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map f.out) := by
            rw [Functor.mapHomotopyCategory_map]
          exact hEq₁.trans (hEq₂.trans hEq₃)
        have hHom :
            Homotopy
              (((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f).out)
              ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map f.out) :=
          HomotopyCategory.homotopyOfEq _ _ hEq
        have hHom' :
            Homotopy
              ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
                (hFF.preimage
                  (((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f).out)))
              ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map f.out) := by
          simpa using hHom
        have hReflected :
            Homotopy
              (hFF.preimage
                (((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f).out))
              f.out :=
          mapHomologicalComplexReflectsHomotopy P hHom'
        simpa using
          HomotopyCategory.eq_of_homotopy _ _ hReflected
    }

/-- Helper for Chap13 Lemma 13 17 4: forgetting bounded-above homotopy objects from
`P.FullSubcategory` to `A` is fully faithful. -/
private noncomputable def mapBoundedAboveHomotopyCategoryFullyFaithful :
    (mapBoundedAboveHomotopyCategory P.ι).FullyFaithful :=
by
  let F := mapBoundedAboveHomotopyCategory P.ι
  let ιminus : K⁻(A) ⥤ K(A) := ObjectProperty.ι (HomotopyCategory.minus A)
  let ιsrc : K⁻(P.FullSubcategory) ⥤ K(P.FullSubcategory) :=
    ObjectProperty.ι (HomotopyCategory.minus (P.FullSubcategory))
  let Famb : K(P.FullSubcategory) ⥤ K(A) :=
    P.ι.mapHomotopyCategory (ComplexShape.up ℤ)
  let H : K⁻(P.FullSubcategory) ⥤ K(A) := ιsrc ⋙ Famb
  let eComp :
      F ⋙ ιminus ≅ H :=
    (HomotopyCategory.minus A).liftCompιIso
      ((HomotopyCategory.minus (P.FullSubcategory)).ι ⋙
        P.ι.mapHomotopyCategory (ComplexShape.up ℤ))
      (mapHomotopyCategory_obj_mem_boundedAbove P.ι)
  let hFFminus : ιminus.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιminus
  let hFFsrc : ιsrc.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιsrc
  let hFFamb : Famb.FullyFaithful := mapHomotopyCategoryFullyFaithful P
  let _ : ιminus.Full := hFFminus.full
  let _ : ιminus.Faithful := hFFminus.faithful
  let _ : ιsrc.Full := hFFsrc.full
  let _ : ιsrc.Faithful := hFFsrc.faithful
  let _ : Famb.Full := hFFamb.full
  let _ : Famb.Faithful := hFFamb.faithful
  let _ : H.Full := inferInstance
  let _ : H.Faithful := inferInstance
  -- Proof comment: cancel the bounded-above inclusion `K^-(A) ↪ K(A)` against the standard
  -- `liftCompιIso` comparison with the ambient homotopy-category functor.
  let _ : F.Full := Functor.Full.of_comp_faithful_iso eComp
  let _ : F.Faithful := Functor.Faithful.of_comp_iso eComp
  exact Functor.FullyFaithful.ofFullyFaithful F

/-- Helper for Chap13 Lemma 13 17 4: the termwise bounded-above source presentation is equivalent
to `K^-(P.FullSubcategory)`. -/
private theorem termwiseBoundedAboveForgetFunctor_isEquivalence :
    Functor.IsEquivalence (termwiseBoundedAboveForgetFunctor P) := by
  let F := termwiseBoundedAboveForgetFunctor P
  let ιterm : (termwiseObjectProperty P).FullSubcategory ⥤ K⁻(A) :=
    (termwiseObjectProperty P).ι
  let H : K⁻(P.FullSubcategory) ⥤ K⁻(A) := mapBoundedAboveHomotopyCategory P.ι
  let eComp :
      F ⋙ ιterm ≅ H :=
    ObjectProperty.liftCompιIso
      (termwiseObjectProperty P)
      (mapBoundedAboveHomotopyCategory P.ι)
      (mapBoundedAboveHomotopyCategory_termwiseObjectProperty P)
  let hFFH : H.FullyFaithful := mapBoundedAboveHomotopyCategoryFullyFaithful P
  let _ : H.Full := hFFH.full
  let _ : H.Faithful := hFFH.faithful
  let _ : F.Full := Functor.Full.of_comp_faithful_iso (F := F) (G := ιterm) (H := H) eComp
  let _ : F.Faithful := Functor.Faithful.of_comp_iso eComp
  let _ : F.EssSurj := termwiseBoundedAboveForgetFunctor_essSurj P
  -- Proof comment: full faithfulness comes from the ambient forgetful functor, and essential
  -- surjectivity was already proved by rebuilding any termwise-`P` object in `P.FullSubcategory`.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- Helper for Chap13 Lemma 13 17 4: a bounded-above homotopy object whose cochain terms already
lie in `P` automatically lies in the bounded-above cohomology-in-`P` owner. -/
private theorem termwiseObjectProperty_mem_minusCohomologyObjectProperty
    (X : (termwiseObjectProperty P).FullSubcategory) :
    minusCohomologyObjectProperty P X.obj := by
  let K' : Comp⁻(P.FullSubcategory) := toBoundedAboveFullSubcategoryComplex P X.property
  let Y : K⁻(P.FullSubcategory) :=
    (HomotopyCategory.Minus.quotient (P.FullSubcategory)).obj K'
  have hDerived :
      derivedCategoryCohomologyInProperty P
        (P.ι.mapDerivedCategory.obj (DerivedCategory.Qh.obj Y.obj)) :=
    weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn P
      (DerivedCategory.Qh.obj Y.obj)
  have hHomotopy :
      derivedCategoryCohomologyInProperty P
        (((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh).obj Y.obj) := by
    let e :
        P.ι.mapDerivedCategory.obj (DerivedCategory.Qh.obj Y.obj) ≅
          (((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh).obj Y.obj) :=
      (P.ι.mapDerivedCategoryFactorsh.app Y.obj)
    -- Proof comment: replace the derived image of the packaged homotopy representative by the
    -- direct homotopy-to-derived image of the same representative.
    exact (derivedCategoryCohomologyInProperty P).prop_of_iso e hDerived
  have hBounded :
      minusCohomologyObjectProperty P
        ((mapBoundedAboveHomotopyCategory P.ι).obj Y) := by
    change derivedCategoryCohomologyInProperty P
      (((t.minus : ObjectProperty (D(A))).ι).obj
        (mapBoundedAboveHomotopyToDerivedAbove.obj
          ((mapBoundedAboveHomotopyCategory P.ι).obj Y)))
    -- Proof comment: the bounded-above comparison isomorphism for `P.ι` identifies this ambient
    -- bounded-above derived object with the homotopy-to-derived image handled above.
    exact
      (derivedCategoryCohomologyInProperty P).prop_of_iso
        ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso P).app Y).symm
        hHomotopy
  have hForget : ((mapBoundedAboveHomotopyCategory P.ι).obj Y) = X.obj := by
    -- Proof comment: forgetting the packaged full-subcategory complex recovers the original
    -- bounded-above homotopy object degreewise.
    cases X
    rfl
  simpa [hForget] using hBounded

/-- Helper for Chap13 Lemma 13 17 4: forgetting a bounded-above homotopy object of
`P.FullSubcategory` to `A` already lands in the bounded-above cohomology-in-`P` full
subcategory. -/
private theorem mapBoundedAboveHomotopyCategory_mem_minusCohomologyObjectProperty
    (X : K⁻(P.FullSubcategory)) :
    minusCohomologyObjectProperty P ((mapBoundedAboveHomotopyCategory P.ι).obj X) := by
  -- Proof comment: after forgetting to `A`, the source object still has all terms in `P`, so the
  -- termwise landing theorem applies directly.
  exact
    termwiseObjectProperty_mem_minusCohomologyObjectProperty P
      ⟨(mapBoundedAboveHomotopyCategory P.ι).obj X,
        mapBoundedAboveHomotopyCategory_termwiseObjectProperty P X⟩

/-- Helper for Chap13 Lemma 13 17 4: the source bounded-above homotopy category of
`P.FullSubcategory` lands in the bounded-above cohomology-in-`P` full subcategory after
forgetting to `A`. -/
private abbrev minusCohomologySourceFunctor :
    K⁻(P.FullSubcategory) ⥤
      (minusCohomologyObjectProperty P).FullSubcategory :=
  (minusCohomologyObjectProperty P).lift
    (mapBoundedAboveHomotopyCategory P.ι)
    (mapBoundedAboveHomotopyCategory_mem_minusCohomologyObjectProperty P)

/-- Helper for Chap13 Lemma 13 17 4: the source bounded-above homotopy category still satisfies
the termwise-`P` condition after landing in the minus-cohomology full subcategory. -/
private theorem minusCohomologySourceFunctor_termwise
    (X : K⁻(P.FullSubcategory)) :
    termwiseMinusCohomologyObjectProperty P
      (minusCohomologySourceFunctor P |>.obj X) := by
  -- Proof comment: this is the same degreewise termwise-`P` statement, now read inside the
  -- target full subcategory.
  exact mapBoundedAboveHomotopyCategory_termwiseObjectProperty P X

/-- Helper for Chap13 Lemma 13 17 4: the source bounded-above homotopy category of
`P.FullSubcategory` lands in the smaller full subcategory cut out simultaneously by the termwise
condition and by `D^-_P(A)`. -/
private abbrev termwiseToMinusCohomologyFunctor :
    (termwiseObjectProperty P).FullSubcategory ⥤
      (termwiseMinusCohomologyObjectProperty P).FullSubcategory :=
  (termwiseMinusCohomologyObjectProperty P).lift
    (ObjectProperty.ιOfLE
      (fun X hX ↦
        termwiseObjectProperty_mem_minusCohomologyObjectProperty P ⟨X, hX⟩))
    (fun X ↦ X.property)

/-- Helper for Chap13 Lemma 13 17 4: forgetting the auxiliary `D^-_P(A)` witness from the
termwise-minus source presentation recovers the plain termwise bounded-above full subcategory. -/
private abbrev termwiseFromMinusCohomologyFunctor :
    (termwiseMinusCohomologyObjectProperty P).FullSubcategory ⥤
      (termwiseObjectProperty P).FullSubcategory :=
  (termwiseObjectProperty P).lift
    ((termwiseMinusCohomologyObjectProperty P).ι ⋙
      (minusCohomologyObjectProperty P).ι)
    (fun X ↦ X.property)

/-- Helper for Chap13 Lemma 13 17 4: the extra minus-cohomology witness on a termwise object is
purely bookkeeping, so the two termwise source presentations are equivalent. -/
private theorem termwiseToMinusCohomologyFunctor_isEquivalence :
    Functor.IsEquivalence (termwiseToMinusCohomologyFunctor P) := by
  let e :
      (termwiseObjectProperty P).FullSubcategory ≌
        (termwiseMinusCohomologyObjectProperty P).FullSubcategory :=
    { functor := termwiseToMinusCohomologyFunctor P
      inverse := termwiseFromMinusCohomologyFunctor P
      unitIso := by
        -- Proof comment: both composites forget back to the same underlying bounded-above
        -- homotopy object, so the unit is the identity after unpacking the witness.
        refine NatIso.ofComponents (fun X ↦ ?_) ?_
        · cases X
          exact Iso.refl _
        · intro X Y f
          cases X
          cases Y
          ext
          simp
      counitIso := by
        -- Proof comment: re-adding and then forgetting the minus-cohomology witness likewise does
        -- not change the underlying object or morphism.
        refine NatIso.ofComponents (fun X ↦ ?_) ?_
        · cases X
          exact Iso.refl _
        · intro X Y f
          cases X
          cases Y
          ext
          simp }
  simpa [e] using e.isEquivalence_functor

/-- Helper for Chap13 Lemma 13 17 4: the source bounded-above homotopy category of
`P.FullSubcategory` lands in the smaller full subcategory cut out simultaneously by the termwise
condition and by `D^-_P(A)`. -/
private abbrev termwiseMinusSourceFunctor :
    K⁻(P.FullSubcategory) ⥤
      (termwiseMinusCohomologyObjectProperty P).FullSubcategory :=
  (termwiseMinusCohomologyObjectProperty P).lift
    (minusCohomologySourceFunctor P)
    (minusCohomologySourceFunctor_termwise P)

/-- Helper for Chap13 Lemma 13 17 4: the actual source functor to the termwise-minus
presentation is the termwise bounded-above forgetful equivalence followed by the bookkeeping
equivalence that records the `D^-_P(A)` witness. -/
private noncomputable abbrev termwiseBoundedAboveForgetFunctorCompTermwiseToMinusIso :
    termwiseBoundedAboveForgetFunctor P ⋙
      termwiseToMinusCohomologyFunctor P ≅
    termwiseMinusSourceFunctor P := by
  -- Proof comment: both functors keep the same underlying bounded-above homotopy object and only
  -- differ by how the full-subcategory witnesses are packaged.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · cases X
    exact Iso.refl _
  · intro X Y f
    cases X
    cases Y
    ext
    simp

/-- Helper for Chap13 Lemma 13 17 4: the source functor to the termwise-minus presentation is an
equivalence of categories. -/
private theorem termwiseMinusSourceFunctor_isEquivalence :
    Functor.IsEquivalence (termwiseMinusSourceFunctor P) := by
  let G := termwiseBoundedAboveForgetFunctor P ⋙ termwiseToMinusCohomologyFunctor P
  let _ : Functor.IsEquivalence (termwiseBoundedAboveForgetFunctor P) :=
    termwiseBoundedAboveForgetFunctor_isEquivalence P
  let _ : Functor.IsEquivalence (termwiseToMinusCohomologyFunctor P) :=
    termwiseToMinusCohomologyFunctor_isEquivalence P
  let _ : Functor.IsEquivalence G := inferInstance
  -- Proof comment: the actual source functor differs from the composite of the two explicit
  -- source-side equivalences only by the bookkeeping NatIso established above.
  exact
    Functor.isEquivalence_of_iso
      (termwiseBoundedAboveForgetFunctorCompTermwiseToMinusIso P)

/-- Helper for Lemma 13.17.4: after forgetting from the termwise source bridge to the ambient
derived category, the result agrees with the bounded-above comparison functor for `P.ι`. -/
private noncomputable abbrev termwiseMinusSourceFunctorCompAmbientDerivedIso :
    termwiseMinusSourceFunctor P ⋙
      (termwiseMinusCohomologyObjectProperty P).ι ⋙
      (minusCohomologyObjectProperty P).ι ⋙
      mapBoundedAboveHomotopyToDerivedAbove ⋙
      ((t.minus : ObjectProperty (D(A))).ι) ≅
    mapBoundedAboveHomotopyToDerivedAbove ⋙
      weakSerreSubcategoryDerivedComparisonFunctorMinus P ⋙
      (derivedCategoryBoundedAboveCohomologyInProperty P).ι ⋙
      ((t.minus : ObjectProperty (D(A))).ι) := by
  let FminusP : K⁻(P.FullSubcategory) ⥤ D⁻(P.FullSubcategory) :=
    mapBoundedAboveHomotopyToDerivedAbove
  let hqMinusP :
      ∀ X : K⁻(P.FullSubcategory),
        (t.minus : ObjectProperty (D(P.FullSubcategory))) (DerivedCategory.Qh.obj X.obj) :=
    qh_obj_mem_t_minus
  let leftToCommon :
      termwiseMinusSourceFunctor P ⋙
          (termwiseMinusCohomologyObjectProperty P).ι ⋙
          (minusCohomologyObjectProperty P).ι ⋙
          mapBoundedAboveHomotopyToDerivedAbove ⋙
          ((t.minus : ObjectProperty (D(A))).ι) ≅
        (HomotopyCategory.minus (P.FullSubcategory)).ι ⋙
          (P.ι.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    (Functor.associator
        (termwiseMinusSourceFunctor P)
        (termwiseMinusCohomologyObjectProperty P).ι
        ((minusCohomologyObjectProperty P).ι ⋙
          mapBoundedAboveHomotopyToDerivedAbove ⋙
          ((t.minus : ObjectProperty (D(A))).ι))).symm ≪≫
      Functor.isoWhiskerRight
        (ObjectProperty.liftCompιIso
          (termwiseMinusCohomologyObjectProperty P)
          (minusCohomologySourceFunctor P)
          (minusCohomologySourceFunctor_termwise P))
        ((minusCohomologyObjectProperty P).ι ⋙
          mapBoundedAboveHomotopyToDerivedAbove ⋙
          ((t.minus : ObjectProperty (D(A))).ι)) ≪≫
      Functor.associator
        (minusCohomologySourceFunctor P)
        (minusCohomologyObjectProperty P).ι
        (mapBoundedAboveHomotopyToDerivedAbove ⋙
          ((t.minus : ObjectProperty (D(A))).ι)) ≪≫
      Functor.isoWhiskerRight
        (ObjectProperty.liftCompιIso
          (minusCohomologyObjectProperty P)
          (mapBoundedAboveHomotopyCategory P.ι)
          (mapBoundedAboveHomotopyCategory_mem_minusCohomologyObjectProperty P))
        (mapBoundedAboveHomotopyToDerivedAbove ⋙
          ((t.minus : ObjectProperty (D(A))).ι)) ≪≫
      (Functor.associator
        (mapBoundedAboveHomotopyCategory P.ι)
        mapBoundedAboveHomotopyToDerivedAbove
        ((t.minus : ObjectProperty (D(A))).ι)).symm ≪≫
      mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso P
  let rightToCommon :
      FminusP ⋙
          weakSerreSubcategoryDerivedComparisonFunctorMinus P ⋙
          (derivedCategoryBoundedAboveCohomologyInProperty P).ι ⋙
          ((t.minus : ObjectProperty (D(A))).ι) ≅
        (HomotopyCategory.minus (P.FullSubcategory)).ι ⋙
          (P.ι.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    (Functor.associator
        (FminusP ⋙
          weakSerreSubcategoryDerivedComparisonFunctorMinus P)
        (derivedCategoryBoundedAboveCohomologyInProperty P).ι
        ((t.minus : ObjectProperty (D(A))).ι)).symm ≪≫
      (Functor.associator
        FminusP
        (weakSerreSubcategoryDerivedComparisonFunctorMinus P)
        ((derivedCategoryBoundedAboveCohomologyInProperty P).ι ⋙
          ((t.minus : ObjectProperty (D(A))).ι))).symm ≪≫
      Functor.isoWhiskerLeft
        FminusP
        (Functor.isoWhiskerRight
          (ObjectProperty.liftCompιIso
            (derivedCategoryBoundedAboveCohomologyInProperty P)
            ((t.minus : ObjectProperty (D(A))).lift
              (t.minus.ι ⋙ P.ι.mapDerivedCategory)
              (weakSerreSubcategory_mapDerivedCategory_obj_mem_boundedAboveDerivedCategory P))
            (fun X ↦ by
              simpa using
                weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn P
                  (((t.minus : ObjectProperty (D(P.FullSubcategory))).ι).obj X)))
          ((t.minus : ObjectProperty (D(A))).ι)) ≪≫
      Functor.isoWhiskerLeft
        FminusP
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(A)))
          (t.minus.ι ⋙ P.ι.mapDerivedCategory)
          (weakSerreSubcategory_mapDerivedCategory_obj_mem_boundedAboveDerivedCategory P)) ≪≫
      Functor.associator
        FminusP
        (t.minus : ObjectProperty (D(P.FullSubcategory))).ι
        P.ι.mapDerivedCategory ≪≫
      Functor.isoWhiskerRight
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(P.FullSubcategory)))
          ((HomotopyCategory.minus (P.FullSubcategory)).ι ⋙ DerivedCategory.Qh)
          hqMinusP)
        P.ι.mapDerivedCategory ≪≫
      (Functor.associator
        (HomotopyCategory.minus (P.FullSubcategory)).ι
        DerivedCategory.Qh
        P.ι.mapDerivedCategory).symm ≪≫
      Functor.isoWhiskerLeft
        (HomotopyCategory.minus (P.FullSubcategory)).ι
        (P.ι.mapDerivedCategoryFactorsh)
  -- Proof comment: both sides identify with the same ambient functor from `K^-(P)` to `D(A)`,
  -- namely the homotopy-to-derived image followed by the ambient inclusion `P.ι`.
  exact leftToCommon ≪≫ rightToCommon.symm

/-- Helper for Chap13 Lemma 13 17 4: the bounded-above homotopy objects of `A` whose derived
image already lies in `D^-_P(A)` map canonically into the bounded-above derived subcategory
`D^-_P(A)`. -/
private abbrev minusCohomologyDerivedFunctor :
    (minusCohomologyObjectProperty P).FullSubcategory ⥤ D⁻_{P} :=
  (derivedCategoryBoundedAboveCohomologyInProperty P).lift
    ((minusCohomologyObjectProperty P).ι ⋙ mapBoundedAboveHomotopyToDerivedAbove)
    (fun X ↦ X.property)

/-- Helper for Chap13 Lemma 13 17 4: forgetting the bounded-above cohomology-in-`P` target of the
restricted derived functor recovers the ambient bounded-above homotopy-to-derived functor. -/
private noncomputable abbrev minusCohomologyDerivedFunctorCompιIso :
    minusCohomologyDerivedFunctor P ⋙
      (derivedCategoryBoundedAboveCohomologyInProperty P).ι ≅
    (minusCohomologyObjectProperty P).ι ⋙
      mapBoundedAboveHomotopyToDerivedAbove := by
  -- Proof comment: this is exactly the defining lift comparison for the restricted target
  -- functor.
  exact
    ObjectProperty.liftCompιIso
      (derivedCategoryBoundedAboveCohomologyInProperty P)
      ((minusCohomologyObjectProperty P).ι ⋙ mapBoundedAboveHomotopyToDerivedAbove)
      (fun X ↦ X.property)

/-- Helper for Chap13 Lemma 13 17 4: after composing with the bounded-above target inclusions, the
source termwise-minus derived functor agrees with the bounded-above comparison functor. -/
private noncomputable abbrev sourceMinusDerivedComparisonIso :
    termwiseMinusSourceFunctor P ⋙
      (termwiseMinusCohomologyObjectProperty P).ι ⋙
      minusCohomologyDerivedFunctor P ≅
    mapBoundedAboveHomotopyToDerivedAbove ⋙
      weakSerreSubcategoryDerivedComparisonFunctorMinus P := by
  let ιminusDerived : D⁻_{P} ⥤ D(A) :=
    (derivedCategoryBoundedAboveCohomologyInProperty P).ι ⋙
      ((t.minus : ObjectProperty (D(A))).ι)
  let eLeft :
      (termwiseMinusSourceFunctor P ⋙
          (termwiseMinusCohomologyObjectProperty P).ι ⋙
          minusCohomologyDerivedFunctor P) ⋙
        ιminusDerived ≅
        termwiseMinusSourceFunctor P ⋙
          (termwiseMinusCohomologyObjectProperty P).ι ⋙
          (minusCohomologyObjectProperty P).ι ⋙
          mapBoundedAboveHomotopyToDerivedAbove ⋙
          ((t.minus : ObjectProperty (D(A))).ι) :=
    (Functor.associator
      (termwiseMinusSourceFunctor P)
      (termwiseMinusCohomologyObjectProperty P).ι
      (minusCohomologyDerivedFunctor P ⋙ ιminusDerived)).symm ≪≫
      Functor.isoWhiskerLeft
        (termwiseMinusSourceFunctor P)
        ((Functor.associator
          (termwiseMinusCohomologyObjectProperty P).ι
          (minusCohomologyDerivedFunctor P)
          ιminusDerived).symm ≪≫
          Functor.isoWhiskerLeft
            (termwiseMinusCohomologyObjectProperty P).ι
            ((Functor.associator
              (minusCohomologyDerivedFunctor P)
              (derivedCategoryBoundedAboveCohomologyInProperty P).ι
              ((t.minus : ObjectProperty (D(A))).ι)).symm ≪≫
              Functor.isoWhiskerRight
                (minusCohomologyDerivedFunctorCompιIso P)
                ((t.minus : ObjectProperty (D(A))).ι) ≪≫
              Functor.associator
                (minusCohomologyObjectProperty P).ι
                mapBoundedAboveHomotopyToDerivedAbove
                ((t.minus : ObjectProperty (D(A))).ι)))
  let eRight :
      (mapBoundedAboveHomotopyToDerivedAbove ⋙
          weakSerreSubcategoryDerivedComparisonFunctorMinus P) ⋙
        ιminusDerived ≅
        mapBoundedAboveHomotopyToDerivedAbove ⋙
          weakSerreSubcategoryDerivedComparisonFunctorMinus P ⋙
          (derivedCategoryBoundedAboveCohomologyInProperty P).ι ⋙
          ((t.minus : ObjectProperty (D(A))).ι) :=
    (Functor.associator
      mapBoundedAboveHomotopyToDerivedAbove
      (weakSerreSubcategoryDerivedComparisonFunctorMinus P)
      ιminusDerived).symm ≪≫
      Functor.isoWhiskerLeft
        mapBoundedAboveHomotopyToDerivedAbove
        (Functor.associator
          (weakSerreSubcategoryDerivedComparisonFunctorMinus P)
          (derivedCategoryBoundedAboveCohomologyInProperty P).ι
          ((t.minus : ObjectProperty (D(A))).ι))
  let hFFminusDerived : ιminusDerived.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιminusDerived
  let _ : ιminusDerived.Full := hFFminusDerived.full
  let _ : ιminusDerived.Faithful := hFFminusDerived.faithful
  -- Proof comment: both comparison functors become the same ambient `K^-(P) ⥤ D(A)` functor
  -- after composing with the fully faithful inclusion `D^-_P(A) ↪ D(A)`.
  exact
    Functor.fullyFaithfulCancelRight ιminusDerived
      (eLeft ≪≫ termwiseMinusSourceFunctorCompAmbientDerivedIso P ≪≫ eRight.symm)

/-- Helper for Chap13 Lemma 13 17 4: the restricted minus-cohomology system is the pullback of the
canonical bounded-above quasi-isomorphism system `Qis⁻(A)`. -/
private theorem minusCohomologyLocalizationSystem_eq_qisInverseImage :
    minusCohomologyLocalizationSystem P =
      (Qis⁻(A)).inverseImage (minusCohomologyObjectProperty P).ι := by
  ext X Y f
  -- Proof comment: the restricted system is defined by pulling back bounded-above acyclic
  -- denominators, and Lemma 13.11.6 identifies those denominators with `Qis⁻`.
  change boundedAboveAcyclicHomotopyProperty.trW f.hom ↔
    Qis⁻(A) f.hom
  let htrW :
      (show MorphismProperty (K⁻(A)) from boundedAboveAcyclicHomotopyProperty.trW) =
        (show MorphismProperty (K⁻(A)) from boundedAboveHomotopyQuasiIso) :=
    boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
  simpa [minusCohomologyLocalizationSystem, boundedAboveHomotopyQuasiIso,
    CategoryTheory.boundedAboveHomotopyQuasiIso, htrW]

/-- Helper for Lemma 13.17.4: the bounded-above cohomology-in-`P` owner is invariant under
bounded-above quasi-isomorphisms. -/
private theorem minusCohomologyObjectProperty_iff_of_quasiIso
    {X Y : K⁻(A)} (s : X ⟶ Y)
    (hs : Qis⁻(A) s) :
    minusCohomologyObjectProperty P X ↔
      minusCohomologyObjectProperty P Y := by
  have hsBounded : boundedAboveHomotopyQuasiIso s := by
    simpa [boundedAboveHomotopyQuasiIso, CategoryTheory.boundedAboveHomotopyQuasiIso] using hs
  have hsTrW : boundedAboveAcyclicHomotopyProperty.trW s := by
    let htrW :
        (show MorphismProperty (K⁻(A)) from boundedAboveAcyclicHomotopyProperty.trW) =
          (show MorphismProperty (K⁻(A)) from boundedAboveHomotopyQuasiIso) :=
      boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
    simpa [htrW] using hsBounded
  have hsIso : IsIso (mapBoundedAboveHomotopyToDerivedAbove.map s) :=
    mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW s hsTrW
  constructor
  · intro hX
    -- Proof comment: transport the bounded-above cohomology-in-`P` condition across the
    -- isomorphism induced by the quasi-isomorphism in the derived category.
    exact
      (derivedCategoryBoundedAboveCohomologyInProperty P).prop_of_iso
        (asIso (mapBoundedAboveHomotopyToDerivedAbove.map s))
        hX
  · intro hY
    -- Proof comment: apply the same transport in the opposite direction.
    exact
      (derivedCategoryBoundedAboveCohomologyInProperty P).prop_of_iso
        (asIso (mapBoundedAboveHomotopyToDerivedAbove.map s)).symm
        hY

/-- Helper for Chap13 Lemma 13 17 4: the bounded-above derived functor restricted to the
minus-cohomology source full subcategory is a localization at the restricted quasi-isomorphism
system. -/
private theorem minusCohomologyDerivedFunctor_isLocalization :
    Functor.IsLocalization
      (minusCohomologyDerivedFunctor P)
      (minusCohomologyLocalizationSystem P) := by
  let G :
      (minusCohomologyObjectProperty P).FullSubcategory ⥤ D⁻_{P} :=
    minusCohomologyDerivedFunctor P
  let ιminus : D⁻_{P} ⥤ D⁻(A) :=
    (derivedCategoryBoundedAboveCohomologyInProperty P).ι
  letI :
      mapBoundedAboveHomotopyToDerivedAbove.IsLocalization (Qis⁻(A)) :=
    mapBoundedAboveHomotopyToDerivedAbove_isLocalization
  letI :
      ((minusCohomologyObjectProperty P).ι ⋙ mapBoundedAboveHomotopyToDerivedAbove).IsLocalization
        (((Qis⁻(A)).inverseImage (minusCohomologyObjectProperty P).ι)) := by
    -- Route correction: the ambient `Qis⁻` localization does restrict directly to the
    -- minus-cohomology full subcategory via `whisker_left`; no separate localization comparison
    -- category is needed here.
    exact
      Functor.IsLocalization.whisker_left
        (W := Qis⁻(A))
        (F := mapBoundedAboveHomotopyToDerivedAbove)
        ((minusCohomologyObjectProperty P).ι)
  letI :
      ((minusCohomologyObjectProperty P).ι ⋙ mapBoundedAboveHomotopyToDerivedAbove).IsLocalization
        (minusCohomologyLocalizationSystem P) := by
    -- Proof comment: rewrite the restricted denominator system into the pullback spelling used by
    -- `whisker_left`.
    simpa [minusCohomologyLocalizationSystem_eq_qisInverseImage P]
  letI :
      (G ⋙ ιminus).IsLocalization
        (minusCohomologyLocalizationSystem P) := by
    -- Proof comment: the lifted minus-cohomology derived functor becomes the restricted ambient
    -- bounded-above derived functor after forgetting the target full subcategory.
    simpa [G, ιminus, minusCohomologyDerivedFunctor] using
      (Functor.IsLocalization.of_iso
        (minusCohomologyDerivedFunctorCompιIso P))
  letI : ιminus.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms
      (derivedCategoryBoundedAboveCohomologyInProperty P).fullyFaithfulι
  -- Proof comment: the target inclusion `D^-_P(A) ↪ D^-(A)` is fully faithful, so localization
  -- descends from the composite back to `minusCohomologyDerivedFunctor`.
  exact Functor.IsLocalization.of_comp G ιminus

/-- Helper for Lemma 13.17.4: the bounded-above cohomology-in-`P` owner is invariant under
bounded-above quasi-isomorphisms in the homotopy category. -/
private theorem minusCohomologyIn_of_quasiIso
    {X Y : K⁻(A)} (s : Y ⟶ X)
    (hs : boundedAboveHomotopyQuasiIso s)
    (hX : minusCohomologyObjectProperty P X) :
    minusCohomologyObjectProperty P Y := by
  -- Proof comment: the bounded-above derived functor sends quasi-isomorphisms to isomorphisms, so
  -- the cohomology-in-`P` condition transports back across `mapBoundedAboveHomotopyToDerivedAbove`.
  have hsTrW : boundedAboveAcyclicHomotopyProperty.trW s := by
    let htrW :
        (show MorphismProperty (K⁻(A)) from boundedAboveAcyclicHomotopyProperty.trW) =
          (show MorphismProperty (K⁻(A)) from boundedAboveHomotopyQuasiIso) :=
      boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
    simpa [htrW] using hs
  let fs : mapBoundedAboveHomotopyToDerivedAbove.obj Y ⟶ mapBoundedAboveHomotopyToDerivedAbove.obj X :=
    mapBoundedAboveHomotopyToDerivedAbove.map s
  have hsIso : IsIso fs :=
    (mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW) s hsTrW
  exact
    (derivedCategoryBoundedAboveCohomologyInProperty P).prop_of_iso
      (asIso fs).symm hX

/-- Helper for Chap13 Lemma 13 17 4: a bounded-above homotopy object whose derived image lies in
`D^-_P(A)` has all cohomology objects of its chosen cochain representative in `P`. -/
private theorem homologyMemOfMinusCohomologyObjectProperty
    (X : K⁻(A))
    (hX : minusCohomologyObjectProperty P X) :
    ∀ i : ℤ, P ((X.obj.as).homology i) := by
  intro i
  let K : CochainComplex A ℤ := X.obj.as
  let eLift :
      ((t.minus : ObjectProperty (D(A))).ι).obj
          (mapBoundedAboveHomotopyToDerivedAbove.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.minus : ObjectProperty (D(A)))
      ((HomotopyCategory.minus A).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_minus).app X
  let eQh :
      DerivedCategory.Qh.obj X.obj ≅
        DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso A).app K
  let eHomology :
      (DerivedCategory.homologyFunctor A i).obj (DerivedCategory.Q.obj K) ≅
        K.homology i :=
    (DerivedCategory.homologyFunctorFactors A i).app K
  have hDerived :
      P
        ((DerivedCategory.homologyFunctor A i).obj
          (((t.minus : ObjectProperty (D(A))).ι).obj
            (mapBoundedAboveHomotopyToDerivedAbove.obj X))) := by
    simpa [minusCohomologyObjectProperty, derivedCategoryBoundedAboveCohomologyInProperty] using hX i
  let eDerived :
      (DerivedCategory.homologyFunctor A i).obj
          (((t.minus : ObjectProperty (D(A))).ι).obj
            (mapBoundedAboveHomotopyToDerivedAbove.obj X)) ≅
        K.homology i :=
    (DerivedCategory.homologyFunctor A i).mapIso (eLift ≪≫ eQh) ≪≫ eHomology
  -- Proof comment: compare the bounded-above derived object with its chosen cochain model and
  -- then commute homology through the quotient functor.
  exact P.prop_of_iso eDerived hDerived

/-- Helper for Lemma 13.17.4: the epi-lift hypothesis produces a `P`-subobject of the cycles in
degree `i` that still surjects onto the degree-`i` homology object. -/
private theorem existsCyclesCoverSurjectingHomology
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f))
    (K : CochainComplex A ℤ)
    (hHomology : ∀ i : ℤ, P (K.homology i))
    (i : ℤ) :
    ∃ (C : P.FullSubcategory) (ι : C.obj ⟶ K.cycles i), Mono ι ∧
      Epi (ι ≫ K.homologyπ i) := by
  let Y : P.FullSubcategory := ⟨K.homology i, hHomology i⟩
  let π : K.cycles i ⟶ Y.obj := K.homologyπ i
  -- Proof comment: apply `hP` to the canonical epimorphism from cycles to homology in degree `i`.
  obtain ⟨C, ι, hmono, hepι⟩ := hP Y π
  exact ⟨C, ι, hmono, hepι⟩

/-- Helper for Lemma 13.17.4: a `P`-subobject of `image(d^i)` lifts to a `P`-subobject of
`K.X i` whose map to the boundary target is still epimorphic. -/
private theorem existsPropertySubobjectOverBoundaryTarget
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f))
    (K : CochainComplex A ℤ) (i : ℤ)
    (T : Subobject ((imageSubobject (K.d i (i + 1)) : A)))
    (hT : P (T : A)) :
    ∃ (E : P.FullSubcategory) (ι : E.obj ⟶ K.X i) (σ : E.obj ⟶ (T : A)),
      Mono ι ∧ Epi σ ∧
        ι ≫ K.d i (i + 1) =
          σ ≫ (show (T : A) ⟶ (imageSubobject (K.d i (i + 1)) : A) from T.arrow) ≫
            (imageSubobject (K.d i (i + 1))).arrow := by
  let e : K.X i ⟶ (imageSubobject (K.d i (i + 1)) : A) :=
    factorThruImageSubobject (K.d i (i + 1))
  let R : A := pullback e T.arrow
  let a : R ⟶ K.X i := pullback.fst e T.arrow
  let π : R ⟶ (T : A) := pullback.snd e T.arrow
  have hπ : Epi π := by
    letI : Epi e := by infer_instance
    simpa [π] using
      (Abelian.epi_snd_of_isLimit (f := e) (g := T.arrow)
        (IsPullback.of_hasPullback e T.arrow).isLimit)
  let Y : P.FullSubcategory := ⟨(T : A), hT⟩
  -- Proof comment: apply the epi-lift hypothesis to the pullback projection onto `T`, then push
  -- the chosen `P`-subobject forward through the left leg of the pullback square.
  obtain ⟨E, j, hj, hσ⟩ := hP Y π
  refine ⟨E, j ≫ a, j ≫ π, ?_, ?_, ?_⟩
  · letI : Mono a := by infer_instance
    infer_instance
  · simpa [π] using hσ
  · -- Proof comment: the pullback condition identifies the two factorizations through
    -- `imageSubobject (K.d i (i + 1))`, and composing with the image arrow recovers `d`.
    have hw :
        j ≫ a ≫ e ≫ (imageSubobject (K.d i (i + 1))).arrow =
          j ≫ π ≫ T.arrow ≫ (imageSubobject (K.d i (i + 1))).arrow := by
      simpa [a, π, Category.assoc] using
        congrArg
          (fun t ↦ j ≫ t ≫ (imageSubobject (K.d i (i + 1))).arrow)
          (IsPullback.of_hasPullback e T.arrow).w
    simpa [e, Category.assoc] using hw

/-- Helper for Chap13 Lemma 13 17 4: if two subobjects of a fixed term lie in `P`, then their
sum subobject also lies in `P`. -/
private theorem prop_sup_of_subobject_mem
    {X : A} (S T : Subobject X)
    (hS : P (S : A)) (hT : P (T : A)) :
    P (((S ⊔ T : Subobject X) : A)) := by
  let f : (S : A) ⊞ (T : A) ⟶ X := biprod.desc S.arrow T.arrow
  have hBiprod : P ((S : A) ⊞ (T : A)) := by
    -- Proof comment: closure under extensions upgrades the two source subobjects to their
    -- biproduct before taking the image of their sum map.
    exact P.prop_biprod hS hT
  have hImage : P (Limits.image f) := by
    -- Proof comment: the image object is a quotient of the biproduct through
    -- `factorThruImage f`, so quotient-closure of the Serre class preserves membership in `P`.
    exact P.prop_of_epi (factorThruImage f) hBiprod
  have hSupEq :
      Subobject.mk (Limits.image.ι f) = (S ⊔ T : Subobject X) := by
    have hMkLe :
        Subobject.mk (Limits.image.ι f) ≤ (S ⊔ T : Subobject X) := by
      let F' : MonoFactorisation f :=
        { I := (S ⊔ T : Subobject X)
          m := (S ⊔ T).arrow
          e := biprod.desc
            (Subobject.ofLE S (S ⊔ T) le_sup_left)
            (Subobject.ofLE T (S ⊔ T) le_sup_right)
          fac := by
            ext
            · simp [f, Subobject.ofLE_arrow]
            · simp [f, Subobject.ofLE_arrow] }
      -- Proof comment: the universal map from the image to the sum subobject shows that the
      -- image subobject of `biprod.desc` is contained in `S ⊔ T`.
      exact Subobject.mk_le_of_comm (Limits.image.lift F') (Limits.image.lift_fac F')
    have hSLe :
        S ≤ Subobject.mk (Limits.image.ι f) := by
      -- Proof comment: the left inclusion factors through the image of the sum map.
      refine Subobject.le_mk_of_comm (biprod.inl ≫ factorThruImage f) ?_
      simp [f, Category.assoc]
    have hTLe :
        T ≤ Subobject.mk (Limits.image.ι f) := by
      -- Proof comment: the right inclusion factors through the same image subobject.
      refine Subobject.le_mk_of_comm (biprod.inr ≫ factorThruImage f) ?_
      simp [f, Category.assoc]
    exact le_antisymm hMkLe (sup_le hSLe hTLe)
  have hSupAsImage :
      P (((Subobject.mk (Limits.image.ι f) : Subobject X) : A)) := by
    -- Proof comment: identify the carrier of the image subobject with the image object itself.
    exact P.prop_of_iso (Subobject.underlyingIso (Limits.image.ι f)).symm hImage
  simpa [hSupEq] using hSupAsImage

/-- Helper for Chap13 Lemma 13 17 4: the source-proof boundary target
`((D^{i + 1} + E^{i + 1}) ∩ image(d^i))` lies in `P` once the two summands do. -/
private theorem descendingBoundaryTarget_mem
    (K : CochainComplex A ℤ) (i : ℤ)
    (DNext ENext : Subobject (K.X (i + 1)))
    (hDNext : P (DNext : A)) (hENext : P (ENext : A)) :
    P ((((DNext ⊔ ENext) ⊓ imageSubobject (K.d i (i + 1)) :
      Subobject (K.X (i + 1))) : A)) := by
  have hSup : P (((DNext ⊔ ENext : Subobject (K.X (i + 1))) : A)) :=
    prop_sup_of_subobject_mem (P := P) DNext ENext hDNext hENext
  -- Proof comment: the boundary target is a subobject of the sum term, so subobject-closure of
  -- the Serre class finishes the source side-condition.
  exact
    P.prop_of_mono
      (Subobject.ofLE
        (((DNext ⊔ ENext) ⊓ imageSubobject (K.d i (i + 1))) : Subobject (K.X (i + 1)))
        (DNext ⊔ ENext) inf_le_left)
      hSup

/-- Helper for Chap13 Lemma 13 17 4: the chain-level representative of a bounded-above
quasi-isomorphism is itself a quasi-isomorphism. -/
private theorem quasiIso_out_of_boundedAbove_quasiIso
    {B : Type u} [Category.{v} B] [Abelian B]
    {X Y : K⁻(B)} (s : X ⟶ Y) (hs : Qis⁻(B) s) :
    QuasiIso (((HomotopyCategory.minus B).ι.map s).out) := by
  have hsAmbient :
      HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
        ((HomotopyCategory.minus B).ι.map s) := hs
  have hsOut :
      HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (((HomotopyCategory.minus B).ι.map s).out)) := by
    simpa [HomotopyCategory.quotient_map_out ((HomotopyCategory.minus B).ι.map s)] using
      hsAmbient
  -- Proof comment: replace the bounded-above homotopy morphism by its chosen chain-level
  -- representative via the quotient presentation of the homotopy category.
  exact
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff
      (f := (((HomotopyCategory.minus B).ι.map s).out))).1 hsOut)

/-- Helper for Chap13 Lemma 13 17 4: after forgetting the bounded-above restriction, the map of
a bounded-above homotopy morphism is the ordinary ambient homotopy-category image. -/
private theorem mapBoundedAboveHomotopyCategory_map_eq
    {X Y : K⁻(P.FullSubcategory)} (s : X ⟶ Y) :
    ((HomotopyCategory.minus A).ι.map ((mapBoundedAboveHomotopyCategory P.ι).map s)) =
      ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.minus (P.FullSubcategory)).ι.map s)) := by
  -- Proof comment: the bounded-above functor is defined by restricting the ambient homotopy
  -- functor along the bounded-above inclusion.
  simp [mapBoundedAboveHomotopyCategory]

/-- Helper for Chap13 Lemma 13 17 4: forgetting a bounded-above homotopy morphism in
`P.FullSubcategory` to `A` preserves and reflects quasi-isomorphisms. -/
private theorem mapBoundedAboveHomotopyCategory_quasiIso_iff
    {X Y : K⁻(P.FullSubcategory)} (s : X ⟶ Y) :
    boundedAboveHomotopyQuasiIso ((mapBoundedAboveHomotopyCategory P.ι).map s) ↔
      Qis⁻(P.FullSubcategory) s := by
  constructor
  · intro hs
    have hsAmbient :
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
          ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((HomotopyCategory.minus (P.FullSubcategory)).ι.map s)) := by
      -- Proof comment: forgetting the bounded-above restriction identifies the ambient morphism
      -- with the ordinary homotopy-category image of `s`.
      simpa [mapBoundedAboveHomotopyCategory_map_eq (P := P) s] using hs
    have hsAmbientOut :
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out))) := by
      -- Proof comment: replace the ambient homotopy morphism by its chosen chain-level
      -- representative before applying the homology-preservation comparison.
      have hmap :
          ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
              ((HomotopyCategory.minus (P.FullSubcategory)).ι.map s)) =
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
              ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
                (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out)) := by
        have hmap₁ :
            ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
                ((HomotopyCategory.minus (P.FullSubcategory)).ι.map s)) =
              ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
                ((HomotopyCategory.quotient (P.FullSubcategory) (ComplexShape.up ℤ)).map
                  (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out))) := by
          rw [HomotopyCategory.quotient_map_out]
          rfl
        have hmap₂ :
            ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
                ((HomotopyCategory.quotient (P.FullSubcategory) (ComplexShape.up ℤ)).map
                  (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out))) =
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
                  (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out)) := by
          rw [Functor.mapHomotopyCategory_map]
        exact hmap₁.trans hmap₂
      exact hmap.symm ▸ hsAmbient
    have hsChain :
        QuasiIso
          ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out)) :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hsAmbientOut
    have hsSourceChain :
        QuasiIso (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out) :=
      (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
        (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out) P.ι).1 hsChain
    have hsSourceOut :
        HomotopyCategory.quasiIso (P.FullSubcategory) (ComplexShape.up ℤ)
          ((HomotopyCategory.quotient (P.FullSubcategory) (ComplexShape.up ℤ)).map
            (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out)) :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hsSourceChain
    -- Proof comment: one final `quotient_map_out` rewrite returns to the bounded-above homotopy
    -- morphism itself.
    simpa [HomotopyCategory.quotient_map_out] using hsSourceOut
  · intro hs
    have hsSourceChain :
        QuasiIso (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out) :=
      quasiIso_out_of_boundedAbove_quasiIso s hs
    have hsAmbientChain :
        QuasiIso
          ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out)) :=
      (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
        (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out) P.ι).2 hsSourceChain
    have hsAmbientOut :
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out))) :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hsAmbientChain
    have hsAmbient :
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
          ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((HomotopyCategory.minus (P.FullSubcategory)).ι.map s)) := by
      -- Proof comment: after pushing the source chain representative through `P.ι`, the ambient
      -- homotopy morphism is again recovered by `quotient_map_out`.
      have hmap :
          ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
              ((HomotopyCategory.minus (P.FullSubcategory)).ι.map s)) =
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
              ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
                (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out)) := by
        have hmap₁ :
            ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
                ((HomotopyCategory.minus (P.FullSubcategory)).ι.map s)) =
              ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
                ((HomotopyCategory.quotient (P.FullSubcategory) (ComplexShape.up ℤ)).map
                  (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out))) := by
          rw [HomotopyCategory.quotient_map_out]
          rfl
        have hmap₂ :
            ((P.ι.mapHomotopyCategory (ComplexShape.up ℤ)).map
                ((HomotopyCategory.quotient (P.FullSubcategory) (ComplexShape.up ℤ)).map
                  (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out))) =
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).map
                  (((HomotopyCategory.minus (P.FullSubcategory)).ι.map s).out)) := by
          rw [Functor.mapHomotopyCategory_map]
        exact hmap₁.trans hmap₂
      exact hmap ▸ hsAmbientOut
    -- Proof comment: rewrite back from the ambient homotopy-category image to the bounded-above
    -- functor spelling used in the statement.
    simpa [mapBoundedAboveHomotopyCategory_map_eq (P := P) s] using hsAmbient

/-- Helper for Chap13 Lemma 13 17 4: under the termwise-minus source equivalence, the restricted
localization system is exactly the usual bounded-above quasi-isomorphism system on `K^-(P)`. -/
private theorem termwiseMinusSourceFunctor_localizationSystem_iff
    {X Y : K⁻(P.FullSubcategory)} (s : X ⟶ Y) :
    fullSubcategoryLocalizationSystem
        (termwiseMinusCohomologyObjectProperty P)
        (minusCohomologyLocalizationSystem P)
        ((termwiseMinusSourceFunctor P).map s) ↔
      Qis⁻(P.FullSubcategory) s := by
  change
    minusCohomologyLocalizationSystem P (((termwiseMinusSourceFunctor P).map s).hom) ↔
      Qis⁻(P.FullSubcategory) s
  let htrW :
      (show MorphismProperty (K⁻(A)) from boundedAboveAcyclicHomotopyProperty.trW) =
        (show MorphismProperty (K⁻(A)) from boundedAboveHomotopyQuasiIso) :=
    boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
  rw [show minusCohomologyLocalizationSystem P =
      boundedAboveHomotopyQuasiIso.inverseImage (minusCohomologyObjectProperty P).ι by
      ext X Y f
      simpa [minusCohomologyLocalizationSystem, htrW]]
  change
    boundedAboveHomotopyQuasiIso ((((termwiseMinusSourceFunctor P).map s).hom).hom) ↔
      Qis⁻(P.FullSubcategory) s
  -- Proof comment: composing the termwise-minus source functor with the two full-subcategory
  -- inclusions forgets exactly to `mapBoundedAboveHomotopyCategory P.ι`.
  simpa [termwiseMinusSourceFunctor, minusCohomologySourceFunctor] using
    (mapBoundedAboveHomotopyCategory_quasiIso_iff (P := P) s)

/-- Helper for Chap13 Lemma 13 17 4: a bounded-above cochain complex whose homology objects lie in
`P` should admit a bounded-above quasi-isomorphic replacement whose terms already lie in `P`. -/
private theorem existsStrictlyLEQuasiIsoWithTermsInOfHomologyMem
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f))
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a)
    (hHomology : ∀ i : ℤ, P (K.homology i)) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      QuasiIso α ∧ Q.IsStrictlyLE a ∧
        (∀ n : ℤ, P (Q.X n)) := by
  -- Route correction: the downstream localization argument only consumes the plain bounded-above
  -- replacement theorem, not the earlier over-strong bookkeeping of prescribed subobjects.
  -- TODO: derive this from the Stacks descending `C^i/D^i/E^i` construction using the epi-lift
  -- hypothesis `hP`. The new closed helpers `prop_sup_of_subobject_mem` and
  -- `descendingBoundaryTarget_mem` isolate the source side-condition; the remaining blocker is the
  -- global descending realization that forces injectivity on cohomology while keeping all terms
  -- in `P`.
  sorry

/-- Helper for Lemma 13.17.4: the remaining source-faithful construction is a bounded-above
quasi-isomorphic replacement by a termwise-`P` complex for any object already lying in
`D^-_P(A)`. -/
private theorem existsTermwisePropertyQuasiIsoOfMinusCohomologyIn
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f))
    (X : K⁻(A))
    (hX : minusCohomologyObjectProperty P X) :
    ∃ (Y : K⁻(A)) (s : Y ⟶ X),
      termwiseObjectProperty P Y ∧ boundedAboveHomotopyQuasiIso s := by
  let K : CochainComplex A ℤ := X.obj.as
  obtain ⟨a, hK⟩ := (CochainComplex.minus_iff A K).1 X.property
  have hHomology : ∀ i : ℤ, P (K.homology i) := by
    simpa [K] using
      homologyMemOfMinusCohomologyObjectProperty P X hX
  obtain ⟨Q, α, hα⟩ :=
    existsStrictlyLEQuasiIsoWithTermsInOfHomologyMem P hP a K hK hHomology
  rcases hα with ⟨hαQuasiIso, hQStrictlyLE, hQTermMem⟩
  let Xc : Comp⁻(A) := ⟨K, X.property⟩
  have hXeq : (HomotopyCategory.Minus.quotient A).obj Xc = X := by
    cases X
    rfl
  let Qminus : Comp⁻(A) := ⟨Q, (CochainComplex.minus_iff A Q).2 ⟨a, hQStrictlyLE⟩⟩
  let Y : K⁻(A) := (HomotopyCategory.Minus.quotient A).obj Qminus
  let α' : Qminus ⟶ Xc := ⟨α⟩
  let s : Y ⟶ X := by
    simpa [Y, hXeq] using (HomotopyCategory.Minus.quotient A).map α'
  refine ⟨Y, s, ?_, ?_⟩
  · -- Proof comment: the bounded-above replacement theorem already records the termwise `P`
    -- condition on `Q`, so the packaged homotopy object inherits it degreewise.
    intro n
    simpa [termwiseObjectProperty, Y, Qminus] using hQTermMem n
  · -- Proof comment: passage to the bounded-above homotopy category preserves the
    -- quasi-isomorphism class of the comparison map.
    change HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((ObjectProperty.ι (HomotopyCategory.minus A)).map s)
    simpa [s, Y, hXeq] using
      (show HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
        (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hαQuasiIso)

/-- Helper for Lemma 13.17.4: once the bounded-above replacement theorem is available, the
localized inclusion of termwise-`P` objects covers the full bounded-above homotopy subcategory
cut out by `D^-_P(A)`. -/
private theorem termwisePropertyLocalizationCover
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    ∀ X : (minusCohomologyObjectProperty P).FullSubcategory,
      ∃ (Y :
          (termwiseMinusCohomologyObjectProperty P).FullSubcategory)
        (s : (termwiseMinusCohomologyObjectProperty P).ι.obj Y ⟶ X),
        minusCohomologyLocalizationSystem P s := by
  intro X
  obtain ⟨Y, s, hYterm, hs⟩ :=
    existsTermwisePropertyQuasiIsoOfMinusCohomologyIn P hP X.obj X.property
  have hYminus :
      minusCohomologyObjectProperty P Y :=
    minusCohomologyIn_of_quasiIso P s hs X.property
  let Yminus : (minusCohomologyObjectProperty P).FullSubcategory := ⟨Y, hYminus⟩
  let Yterm :
      (termwiseMinusCohomologyObjectProperty P).FullSubcategory := ⟨Yminus, hYterm⟩
  let s' : Yminus ⟶ X := ObjectProperty.homMk s
  refine ⟨Yterm, s', ?_⟩
  -- Proof comment: the replacement morphism is a bounded-above quasi-isomorphism, hence a
  -- denominator in the restricted localization system.
  exact
    minusCohomologyLocalizationSystem_of_quasiIso P s' hs

/-- Helper for Lemma 13.17.4: on the minus-cohomology full subcategory, the restricted
localization system is exactly the pullback of bounded-above quasi-isomorphisms. -/
private theorem minusCohomologyLocalizationSystem_eq_quasiIsoInverseImage :
    minusCohomologyLocalizationSystem P =
      boundedAboveHomotopyQuasiIso.inverseImage
        (minusCohomologyObjectProperty P).ι := by
  -- Proof comment: first rewrite the restricted system to the chapter owner `Qis⁻(A)`, then
  -- unfold the local alias `boundedAboveHomotopyQuasiIso`.
  simpa [boundedAboveHomotopyQuasiIso, CategoryTheory.boundedAboveHomotopyQuasiIso] using
    minusCohomologyLocalizationSystem_eq_qisInverseImage P

/-- Helper for Lemma 13.17.4: once the bounded-above replacement theorem is available, the
localized inclusion of termwise-`P` objects into the full bounded-above homotopy subcategory
cut out by `D^-_P(A)` is an equivalence. -/
private theorem boundedAboveAcyclicHomotopyPropertyIsStableUnderRetracts :
    (Ac⁻(A)).IsStableUnderRetracts := by
  -- Proof comment: bounded-above acyclic complexes are exactly the kernel of the bounded-above
  -- homotopy-to-derived functor, and kernels of exact functors are retract-stable.
  let Fminus : K⁻(A) ⥤ D⁻(A) := mapBoundedAboveHomotopyToDerivedAbove
  have hkernel :
      Functor.kernel Fminus = Ac⁻(A) := by
    simpa [Fminus] using
      (show Functor.kernel Fminus = Ac⁻(A) from
        CategoryTheory.kernel_mapBoundedAboveHomotopyToDerivedAbove_eq_acyclic)
  rw [← hkernel]
  infer_instance

/-- Helper for Lemma 13.17.4: the bounded-above quasi-isomorphisms form a saturated
multiplicative system. -/
private theorem boundedAboveQuasiIso_isSaturated :
    IsSaturatedMultiplicativeSystem (Qis⁻(A)) := by
  let _ : (Ac⁻(A)).IsStableUnderRetracts :=
    boundedAboveAcyclicHomotopyPropertyIsStableUnderRetracts
  -- Proof comment: chapter 13.11.6 identifies `Qis⁻` with the canonical `trW` owner of bounded-
  -- above acyclic complexes, so saturation comes from the general `trW` theorem.
  simpa [CategoryTheory.boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso A] using
    (inferInstance : IsSaturatedMultiplicativeSystem ((Ac⁻(A)).trW))

/-- Helper for Lemma 13.17.4: the bounded-above quasi-isomorphisms are compatible with the
triangulated structure on `K^-(A)`. -/
private theorem boundedAboveQuasiIso_isCompatibleWithTriangulation :
    (Qis⁻(A)).IsCompatibleWithTriangulation := by
  -- Proof comment: `Qis⁻` is the `trW` owner of the bounded-above acyclic triangulated
  -- subcategory, so compatibility is inherited from the canonical `trW` instance.
  simpa [CategoryTheory.boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso A] using
    (inferInstance : ((Ac⁻(A)).trW).IsCompatibleWithTriangulation)

/-- Helper for Lemma 13.17.4: the canonical pullback of `Qis⁻` to the minus-cohomology full
subcategory is saturated. -/
private theorem minusCohomologyQuasiIsoInverseImage_isSaturated :
    IsSaturatedMultiplicativeSystem
      ((Qis⁻(A)).inverseImage
        (minusCohomologyObjectProperty P).ι) := by
  let _ : IsSaturatedMultiplicativeSystem (Qis⁻(A)) :=
    boundedAboveQuasiIso_isSaturated
  let _ : (Qis⁻(A)).IsCompatibleWithTriangulation :=
    boundedAboveQuasiIso_isCompatibleWithTriangulation
  let _ : HasZeroObject (minusCohomologyObjectProperty P).FullSubcategory :=
    inferInstance
  let F :
      (minusCohomologyObjectProperty P).FullSubcategory ⥤
        (Qis⁻(A)).Localization :=
    (minusCohomologyObjectProperty P).ι ⋙ (Qis⁻(A)).Q
  have hEq :
      ((Qis⁻(A)).inverseImage
          (minusCohomologyObjectProperty P).ι) =
        (isomorphisms (Qis⁻(A)).Localization).inverseImage F := by
    -- Proof comment: this is exactly the canonical restricted localization system attached to the
    -- inclusion of the minus-cohomology full subcategory into `K⁻(A)`.
    simpa [F, fullSubcategoryLocalizationSystem] using
      (fullSubcategoryLocalizationSystem_eq_inverseImage_isomorphisms_of_localized_inclusion
        (minusCohomologyObjectProperty P) (Qis⁻(A)))
  -- Proof comment: once rewritten in inverse-image-of-isomorphisms form, saturation is the exact
  -- functor theorem from Lemma 13.5.4 applied to the localized inclusion functor.
  simpa [hEq] using
    (inverseImage_isomorphisms_of_exactFunctor_isSaturatedMultiplicativeSystem
      F)

/-- Helper for Lemma 13.17.4: once the bounded-above replacement theorem is available, the
localized inclusion of termwise-`P` objects into the full bounded-above homotopy subcategory
cut out by `D^-_P(A)` is an equivalence. -/
private theorem termwisePropertyLocalizationIsEquivalence
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    Functor.IsEquivalence
      (fullSubcategoryLocalizationFunctor
        (termwiseMinusCohomologyObjectProperty P)
        (minusCohomologyLocalizationSystem P)) := by
  have hSystem :
      minusCohomologyLocalizationSystem P =
        (Qis⁻(A)).inverseImage (minusCohomologyObjectProperty P).ι := by
    -- Proof comment: the local bounded-above quasi-isomorphism alias is just the chapter-level
    -- owner `Qis⁻(A)`, so the restricted system is the canonical pullback of `Qis⁻`.
    calc
      minusCohomologyLocalizationSystem P =
          boundedAboveHomotopyQuasiIso.inverseImage
            (minusCohomologyObjectProperty P).ι :=
        minusCohomologyLocalizationSystem_eq_quasiIsoInverseImage P
      _ = ((Qis⁻(A)).inverseImage
            (minusCohomologyObjectProperty P).ι) := by
        ext X Y f
        simp [boundedAboveHomotopyQuasiIso, CategoryTheory.boundedAboveHomotopyQuasiIso]
  let _ : IsSaturatedMultiplicativeSystem
      (minusCohomologyLocalizationSystem P) := by
    -- Proof comment: transport the saturation of the canonical pullback system back to the local
    -- spelling used in this file.
    simpa [hSystem] using
      (minusCohomologyQuasiIsoInverseImage_isSaturated P)
  -- Proof comment: Lemma 13.5.8 now applies directly to the termwise full subcategory cover
  -- produced by the bounded-above replacement theorem.
  exact
    fullSubcategoryLocalization_inclusion_isEquivalence
      (termwiseMinusCohomologyObjectProperty P)
      (minusCohomologyLocalizationSystem P)
      (termwisePropertyLocalizationCover P hP)

/-- Helper for Chap13 Lemma 13 17 4: after localizing the termwise-minus source presentation,
one may pass directly to `D^-_P(A)` via the restricted derived functor. -/
private theorem termwiseMinusDerivedFunctor_isLocalization
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    Functor.IsLocalization
      ((termwiseMinusCohomologyObjectProperty P).ι ⋙
        minusCohomologyDerivedFunctor P)
      (fullSubcategoryLocalizationSystem
        (termwiseMinusCohomologyObjectProperty P)
        (minusCohomologyLocalizationSystem P)) := by
  let Wterm :
      MorphismProperty ((termwiseMinusCohomologyObjectProperty P).FullSubcategory) :=
    fullSubcategoryLocalizationSystem
      (termwiseMinusCohomologyObjectProperty P)
      (minusCohomologyLocalizationSystem P)
  let Wminus :
      MorphismProperty ((minusCohomologyObjectProperty P).FullSubcategory) :=
    minusCohomologyLocalizationSystem P
  let Qterm :
      (termwiseMinusCohomologyObjectProperty P).FullSubcategory ⥤
        Wterm.Localization :=
    Wterm.Q
  let Eterm :
      Wterm.Localization ⥤ Wminus.Localization :=
    fullSubcategoryLocalizationFunctor
      (termwiseMinusCohomologyObjectProperty P)
      (minusCohomologyLocalizationSystem P)
  letI : (minusCohomologyDerivedFunctor P).IsLocalization Wminus :=
    minusCohomologyDerivedFunctor_isLocalization P
  let Eminus :
      Wminus.Localization ≌ D⁻_{P} :=
    Localization.uniq Wminus.Q (minusCohomologyDerivedFunctor P) Wminus
  letI : Functor.IsEquivalence Eterm :=
    termwisePropertyLocalizationIsEquivalence P hP
  let _ : Eminus.functor.IsEquivalence :=
    Equivalence.isEquivalence_functor Eminus
  have hInv :
      Wterm.IsInvertedBy
        ((termwiseMinusCohomologyObjectProperty P).ι ⋙ Wminus.Q) := by
    intro X Y f hf
    exact Localization.inverts Wminus.Q Wminus f.hom hf
  have hComp :
      Qterm ⋙ Eterm ⋙ Eminus.functor ≅
        ((termwiseMinusCohomologyObjectProperty P).ι ⋙
          minusCohomologyDerivedFunctor P) := by
    -- Proof comment: first identify the localized termwise inclusion with the restricted source
    -- inclusion into `Wminus.Localization`, then postcompose with the unique comparison functor
    -- from that localization model to `D^-_P(A)`.
    calc
      Qterm ⋙ Eterm ⋙ Eminus.functor ≅
          (Qterm ⋙ Eterm) ⋙ Eminus.functor :=
        (Functor.associator _ _ _).symm
      _ ≅
          (((termwiseMinusCohomologyObjectProperty P).ι ⋙ Wminus.Q) ⋙
            Eminus.functor) :=
        Functor.isoWhiskerRight
          (Localization.fac
            ((termwiseMinusCohomologyObjectProperty P).ι ⋙ Wminus.Q)
            hInv Qterm)
          Eminus.functor
      _ ≅
          (termwiseMinusCohomologyObjectProperty P).ι ⋙
            (Wminus.Q ⋙ Eminus.functor) :=
        Functor.associator _ _ _
      _ ≅
          (termwiseMinusCohomologyObjectProperty P).ι ⋙
            minusCohomologyDerivedFunctor P :=
        Functor.isoWhiskerLeft
          (termwiseMinusCohomologyObjectProperty P).ι
          (by
            simpa [Eminus] using
              (Localization.compUniqFunctor
                Wminus.Q
                (minusCohomologyDerivedFunctor P)
                Wminus))
  letI : Qterm.IsLocalization Wterm := inferInstance
  letI : (Qterm ⋙ Eterm ⋙ Eminus.functor).IsLocalization Wterm := inferInstance
  -- Proof comment: the canonical localization model `Wterm.Q` differs from the target functor
  -- only by equivalence transport on the two localization stages.
  simpa [Qterm, Wterm] using
    (Functor.IsLocalization.of_iso (W := Wterm) hComp)

/-- Helper for Lemma 13.17.4: once the direct bounded-above replacement theorem is proved, only
the formal localization comparison with the source termwise full subcategory remains. -/
private theorem comparisonFunctorMinus_isEquivalence_of_epi_lift_blocker
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    Functor.IsEquivalence (weakSerreSubcategoryDerivedComparisonFunctorMinus P) := by
  let Fterm :
      (termwiseMinusCohomologyObjectProperty P).FullSubcategory ⥤ D⁻_{P} :=
    (termwiseMinusCohomologyObjectProperty P).ι ⋙ minusCohomologyDerivedFunctor P
  let Gsrc : K⁻(P.FullSubcategory) ⥤ D⁻(P.FullSubcategory) :=
    mapBoundedAboveHomotopyToDerivedAbove
  let H : D⁻(P.FullSubcategory) ⥤ D⁻_{P} :=
    weakSerreSubcategoryDerivedComparisonFunctorMinus P
  let Gcomp : K⁻(P.FullSubcategory) ⥤ D⁻_{P} := Gsrc ⋙ H
  let Wterm :
      MorphismProperty ((termwiseMinusCohomologyObjectProperty P).FullSubcategory) :=
    fullSubcategoryLocalizationSystem
      (termwiseMinusCohomologyObjectProperty P)
      (minusCohomologyLocalizationSystem P)
  let Wsrc : MorphismProperty (K⁻(P.FullSubcategory)) := Qis⁻(P.FullSubcategory)
  letI : Fterm.IsLocalization Wterm :=
    termwiseMinusDerivedFunctor_isLocalization P hP
  letI : Gsrc.IsLocalization Wsrc :=
    mapBoundedAboveHomotopyToDerivedAbove_isLocalization
  letI : Functor.IsEquivalence (termwiseMinusSourceFunctor P) :=
    termwiseMinusSourceFunctor_isEquivalence P
  let Esrc :
      (termwiseMinusCohomologyObjectProperty P).FullSubcategory ≌
        K⁻(P.FullSubcategory) :=
    (termwiseMinusSourceFunctor P).asEquivalence.symm
  have hWterm :
      Wterm ≤ Wsrc.isoClosure.inverseImage Esrc.functor := by
    have hInvEq :
        Wterm.inverseImage (termwiseMinusSourceFunctor P) = Wsrc := by
      ext X Y f
      simpa [Wterm] using
        (termwiseMinusSourceFunctor_localizationSystem_iff (P := P) f)
    have hMapEq :
        Wsrc.map (termwiseMinusSourceFunctor P) = Wterm := by
      calc
        Wsrc.map (termwiseMinusSourceFunctor P) =
            (Wterm.inverseImage (termwiseMinusSourceFunctor P)).map
              (termwiseMinusSourceFunctor P) := by
                rw [hInvEq.symm]
        _ = Wterm := by
              simpa using
                (MorphismProperty.map_inverseImage_eq_of_isEquivalence
                  Wterm (termwiseMinusSourceFunctor P))
    have hSourceEq :
        Wsrc.inverseImage Esrc.functor =
          Wsrc.map (termwiseMinusSourceFunctor P) := by
      simpa [Esrc] using
        (MorphismProperty.inverseImage_equivalence_functor_eq_map_inverse
          (Q := Wsrc) (termwiseMinusSourceFunctor P).asEquivalence)
    calc
      Wterm ≤ Wsrc.inverseImage Esrc.functor := by
        simpa [hSourceEq] using le_of_eq hMapEq.symm
      _ ≤ Wsrc.isoClosure.inverseImage Esrc.functor := by
        intro X Y f hf
        exact Wsrc.le_isoClosure _ hf
  have hWsrcInv : Wsrc.IsInvertedBy Gcomp := by
    intro X Y f hf
    have hfIso : IsIso (Gsrc.map f) :=
      Localization.inverts Gsrc Wsrc f hf
    let _ : IsIso (Gsrc.map f) := hfIso
    change IsIso (H.map (Gsrc.map f))
    infer_instance
  have hIsoTerm :
      Esrc.functor ⋙ Gcomp ≅ Fterm := by
    -- Proof comment: rewrite the source comparison through the inverse of the source-side
    -- equivalence and collapse the adjacent equivalence pair back to the identity.
    calc
      Esrc.functor ⋙ Gcomp ≅
          Esrc.functor ⋙ (termwiseMinusSourceFunctor P ⋙ Fterm) := by
            exact Functor.isoWhiskerLeft Esrc.functor
              (sourceMinusDerivedComparisonIso P).symm
      _ ≅ (Esrc.functor ⋙ termwiseMinusSourceFunctor P) ⋙ Fterm :=
            (Functor.associator _ _ _).symm
      _ ≅ 𝟭 _ ⋙ Fterm :=
            Functor.isoWhiskerRight Esrc.unitIso.symm Fterm
      _ ≅ Fterm := Functor.leftUnitor _
  have hCompLoc : Gcomp.IsLocalization Wsrc := by
    -- Proof comment: transport the termwise localization model back across the source
    -- equivalence `K^-(P) ≌ termwiseMinus`.
    exact
      Functor.IsLocalization.of_equivalence_source
        Fterm Wterm Gcomp Wsrc Esrc hWterm hWsrcInv hIsoTerm
  let Euniq : D⁻(P.FullSubcategory) ≌ D⁻_{P} :=
    Localization.uniq Gsrc Gcomp Wsrc
  have hH :
      H ≅ Euniq.functor := by
    -- Proof comment: `H` and the localization-uniqueness functor `Euniq.functor` are two lifts
    -- of the same composite `K^-(P) ⥤ D^-_P(A)` through the source localization `Gsrc`.
    exact
      Localization.liftNatIso
        Gsrc Wsrc
        (Gsrc ⋙ H) (Gsrc ⋙ Euniq.functor)
        H Euniq.functor
        (Localization.compUniqFunctor Gsrc Gcomp Wsrc).symm
  let _ : Euniq.functor.IsEquivalence := Equivalence.isEquivalence_functor Euniq
  exact Functor.isEquivalence_of_iso hH.symm

/-- Helper for Lemma 13.17.4: the source-proof replacement claim implies essential surjectivity of
the bounded-above comparison functor. -/
private theorem comparisonFunctorMinus_essSurj_of_epi_lift
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    (weakSerreSubcategoryDerivedComparisonFunctorMinus P).EssSurj := by
  -- Once the comparison functor is known to be an equivalence, essential surjectivity is formal.
  letI : Functor.IsEquivalence (weakSerreSubcategoryDerivedComparisonFunctorMinus P) :=
    comparisonFunctorMinus_isEquivalence_of_epi_lift_blocker P hP
  infer_instance

/-- Helper for Lemma 13.17.4: the source-proof roof argument yields fullness of the bounded-above
comparison functor. -/
private theorem comparisonFunctorMinus_full_of_epi_lift
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    Functor.Full (weakSerreSubcategoryDerivedComparisonFunctorMinus P) := by
  -- Once the comparison functor is known to be an equivalence, fullness is formal.
  letI : Functor.IsEquivalence (weakSerreSubcategoryDerivedComparisonFunctorMinus P) :=
    comparisonFunctorMinus_isEquivalence_of_epi_lift_blocker P hP
  infer_instance

/-- Helper for Lemma 13.17.4: the source-proof homotopy argument yields faithfulness of the
bounded-above comparison functor. -/
private theorem comparisonFunctorMinus_faithful_of_epi_lift
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    Functor.Faithful (weakSerreSubcategoryDerivedComparisonFunctorMinus P) := by
  -- Once the comparison functor is known to be an equivalence, faithfulness is formal.
  letI : Functor.IsEquivalence (weakSerreSubcategoryDerivedComparisonFunctorMinus P) :=
    comparisonFunctorMinus_isEquivalence_of_epi_lift_blocker P hP
  infer_instance

-- Proof sketch: the hypothesis lets one replace a bounded-above complex in `A` with cohomology in
-- `P` by a quasi-isomorphic bounded-above subcomplex whose terms lie in `P.FullSubcategory`.
-- This gives essential surjectivity of the comparison functor, and the same replacement applied to
-- mapping cones and homotopies yields faithfulness and fullness.
/-- Lemma 13.17.4: let `P` be a Serre subcategory of an abelian category `A`. Assume that for
every epimorphism `f : X ⟶ Y` with `Y` an object of `P.FullSubcategory`, there exist an object
`X'` of `P.FullSubcategory`, a monomorphism `ι : X' ⟶ X`, and an epimorphism `X' ⟶ Y` given by
`ι ≫ f`. Then the canonical comparison functor `D^-(P) ⟶ D^-_P(A)` is an equivalence. -/
@[stacks 0FCL]
theorem serreSubcategoryDerivedComparisonFunctorMinus_isEquivalence_of_epi_lift
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    Functor.IsEquivalence (weakSerreSubcategoryDerivedComparisonFunctorMinus P) := by
  -- Route correction: the file now records the single structural blocker directly. The formal
  -- consequences `EssSurj`, `Full`, and `Faithful` are derived above from this same blocker.
  exact comparisonFunctorMinus_isEquivalence_of_epi_lift_blocker P hP

end

end _root_.CategoryTheory.ObjectProperty
