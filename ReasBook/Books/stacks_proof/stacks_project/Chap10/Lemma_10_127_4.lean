import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u v w

section

variable {R : Type u} [CommRing R]
variable {Λ : Type v} [CommRing Λ] [Algebra R Λ]

/-- The canonical diagram of selected `R`-algebras over `Λ`, viewed in `CommAlgCat R`. -/
abbrev selectedAlgebrasOverTargetDiagram
    (P : ObjectProperty (Over (CommAlgCat.of R Λ))) :
    P.FullSubcategory ⥤ CommAlgCat.{v} R :=
  ObjectProperty.ι P ⋙
    (Over.forget (CommAlgCat.of R Λ) : Over (CommAlgCat.of R Λ) ⥤ CommAlgCat.{v} R)

/-- The canonical cocone from the selected `R`-algebras over `Λ` to `Λ`. -/
abbrev selectedAlgebrasOverTargetCocone
    (P : ObjectProperty (Over (CommAlgCat.of R Λ))) :
    Cocone (selectedAlgebrasOverTargetDiagram P) :=
  (Over.forgetCocone (CommAlgCat.of R Λ)).whisker (ObjectProperty.ι P)

/-- Helper for Chap10 Lemma 10 127 4: the selected cocone component at a stage is its structure
map to `Λ`. -/
private lemma selectedAlgebrasOverTargetCocone_ι_app
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (A : P.FullSubcategory) :
    (selectedAlgebrasOverTargetCocone P).ι.app A = A.obj.hom := rfl

/-
Domain sampling:
* Primary domain: filtered colimit presentations inside the over category
  `Over (CommAlgCat.of R Λ)`.
* Core/canonical declarations inspected:
  - `ObjectProperty.ι`
  - `Over.forget`
  - `Over.forgetCocone`
  - `ObjectProperty.initial_ι`
* Owner abstraction: the ambient owner is the canonical over-category diagram
  `ObjectProperty.ι P ⋙ Over.forget (CommAlgCat.of R Λ)` together with its canonical cocone
  `(Over.forgetCocone (CommAlgCat.of R Λ)).whisker (ObjectProperty.ι P)`.
* Layer triage:
  - `source-facing`: the factorization criterion for selected finitely presented stages;
  - `core/canonical`: `ObjectProperty.ι`, `Over.forget`, and `Over.forgetCocone`;
  - `bridge/view`: the finite-presentation hypothesis selecting which over-objects participate.
* Primitive vs. derived:
  - primitive data: the object property `P`;
  - derived API: the induced diagram to `CommAlgCat R` and its canonical cocone to `Λ`.
-/

/-- Helper for Lemma 10.127.4: the full subcategory of over-objects whose source algebra is
finitely presented over `R`. -/
private abbrev finitelyPresentedOverTargetProperty :
    ObjectProperty (Over (CommAlgCat.of R Λ)) :=
  fun A : Over (CommAlgCat.of R Λ) ↦ Algebra.FinitePresentation R A.left

/-- Helper for Chap10 Lemma 10 127 4: the object property on `Over (CommAlgCat.of R A)` selecting
the finitely presented `R`-algebras over `A`. -/
private abbrev finitelyPresentedAlgebrasOverProperty
    (A : Type v) [CommRing A] [Algebra R A] :
    ObjectProperty (Over (CommAlgCat.of R A)) :=
  fun B : Over (CommAlgCat.of R A) ↦ Algebra.FinitePresentation R B.left

/-- Helper for Lemma 10.127.4: a commutative factorization of the structure maps packages into a
morphism in the over category. -/
private lemma over_hom_of_factorization
    {A B : Over (CommAlgCat.of R Λ)}
    (u : A.left ⟶ B.left) (hu : u ≫ B.hom = A.hom) :
    Nonempty (A ⟶ B) := by
  -- Proof comment: `Over.homMk` is the canonical constructor for morphisms in the slice category.
  exact ⟨Over.homMk u hu⟩

/-- Helper for Chap10 Lemma 10 127 4: forgetting an over-morphism recovers the corresponding
factorization equation on the underlying algebra maps. -/
private lemma factorization_eq_of_over_hom
    {A B : Over (CommAlgCat.of R Λ)} (f : A ⟶ B) :
    f.left ≫ B.hom = A.hom := by
  -- Proof comment: this is exactly the defining commutative triangle recorded by `Over.w`.
  simpa using Over.w f

/-- Helper for Chap10 Lemma 10 127 4: the right component of an under-morphism respects the
structure maps from the base ring. -/
private lemma underRight_hom_commutes
    {A B : Under (CommRingCat.of R)} (m : A ⟶ B) (r : R) :
    m.right.hom (A.hom.hom r) = B.hom.hom r := by
  -- Proof comment: move the defining triangle identity of the under-morphism down to elements.
  have h : A.hom ≫ m.right = B.hom := by
    simpa using m.w.symm
  simpa [CommRingCat.comp_apply] using
    congrArg (fun φ : CommRingCat.of R ⟶ B.right ↦ φ.hom r) h

/-- Helper for Chap10 Lemma 10 127 4: the right component preserves the chosen ambient
`R`-algebra maps when they are the displayed under-structure maps. -/
private lemma underRightAlgHom_commutes
    {A B : Under (CommRingCat.of R)}
    [Algebra R A.right] [Algebra R B.right]
    (hA : algebraMap R A.right = A.hom.hom)
    (hB : algebraMap R B.right = B.hom.hom)
    (m : A ⟶ B) (r : R) :
    m.right.hom (algebraMap R A.right r) = algebraMap R B.right r := by
  -- Proof comment: rewrite both ambient algebra maps to the maps displayed by the under-category.
  simpa [hA, hB] using underRight_hom_commutes m r

/-- Helper for Chap10 Lemma 10 127 4: an under-morphism is an algebra homomorphism for any
ambient algebra structures whose algebra maps are the displayed under-structure maps. -/
private abbrev underRightAlgHom
    {A B : Under (CommRingCat.of R)}
    [Algebra R A.right] [Algebra R B.right]
    (hA : algebraMap R A.right = A.hom.hom)
    (hB : algebraMap R B.right = B.hom.hom)
    (m : A ⟶ B) : A.right →ₐ[R] B.right where
  __ := m.right.hom
  commutes' := underRightAlgHom_commutes hA hB m

/-- Helper for Chap10 Lemma 10 127 4: over the terminal object
`Over.mk (𝟙 (CommAlgCat.of R Λ))`, the costructured-arrow category of `P.ι` is equivalent to
`P.FullSubcategory`. -/
private noncomputable def terminalCostructuredArrowEquivalence
    (P : ObjectProperty (Over (CommAlgCat.of R Λ))) :
    P.FullSubcategory ≌ CostructuredArrow P.ι (Over.mk (𝟙 (CommAlgCat.of R Λ))) where
  functor :=
    { obj := fun A ↦ CostructuredArrow.mk (Over.mkIdTerminal.from A.obj)
      map := fun f ↦
        -- Proof comment: morphisms between the left objects automatically define morphisms in the
        -- costructured-arrow category because the target object is terminal.
        CostructuredArrow.homMk f }
  inverse :=
    { obj := fun A ↦ A.left
      map := fun f ↦
        -- Proof comment: forgetting the unique map to the terminal object recovers the original
        -- morphism in the full subcategory.
        ObjectProperty.homMk f.left.hom }
  unitIso :=
    NatIso.ofComponents (fun A ↦ Iso.refl A) (fun f ↦ by
      -- Proof comment: on the selected full subcategory, both composites act by the identity.
      ext
      rfl)
  counitIso :=
    NatIso.ofComponents
      (fun A ↦ by
        -- Proof comment: the left object is unchanged, and the arrow to the terminal object is
        -- unique, so the counit is the identity on the source algebra.
        refine CostructuredArrow.isoMk (Iso.refl _) ?_
        exact IsTerminal.hom_ext Over.mkIdTerminal _ _)
      (fun f ↦ by
        ext
        rfl)

/-- Helper for Chap10 Lemma 10 127 4: after viewing both the base ring and the algebra in any
ambient universe containing them, a finitely presented commutative `R`-algebra is finitely
presentable as an object of `CommAlgCat R`. -/
private lemma commAlgCat_sameUniverse_isFinitelyPresentable_of_finitePresentation
    {R' : Type w} [CommRing R'] (A : CommAlgCat.{w} R') (hA : Algebra.FinitePresentation R' A) :
    IsFinitelyPresentable.{w} A := by
  let E := commAlgCatEquivUnder (CommRingCat.of R')
  let _ : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  have hUnder :
      IsFinitelyPresentable.{w} (E.functor.obj A) := by
    -- Proof comment: the owner theorem on `Under (CommRingCat.of R)` packages finite
    -- presentation of `algebraMap R A` as finite presentability of the corresponding under-object.
    simpa [E, CategoryTheory.MorphismProperty.isFinitelyPresentable,
      RingHom.finitePresentation_algebraMap] using
      (CommRingCat.isFinitelyPresentable_hom
        (CommRingCat.ofHom (algebraMap R' A))
        ((RingHom.finitePresentation_algebraMap).mpr hA))
  -- Proof comment: equivalences reflect finite presentability, so we move the under-category
  -- result back across `commAlgCatEquivUnder`.
  simpa using
    (CategoryTheory.isCardinalPresentable_iff_of_isEquivalence
      A Cardinal.aleph0 E.functor).mp hUnder

/-- Helper for Chap10 Lemma 10 127 4: lifting only the carrier universe of an `R`-algebra gives a
same-category object of `CommAlgCat R` in the ambient universe `max u v`. -/
private abbrev carrierLiftedCommAlgCatObject
    (A : CommAlgCat.{v} R) :
    CommAlgCat.{max u v} R :=
  (CommAlgCat.uliftFunctor.{u, v} R).obj A

/-- Helper for Chap10 Lemma 10 127 4: finite presentation survives the carrier `ULift`. -/
private lemma carrierLiftedFinitePresentation
    {A : Type v} [CommRing A] [Algebra R A]
    (hA : Algebra.FinitePresentation R A) :
    Algebra.FinitePresentation R (ULift.{u} A) := by
  letI : Algebra.FinitePresentation R A := hA
  -- Proof comment: the carrier-only `ULift` is canonically equivalent to the original algebra.
  simpa [RingHom.finitePresentation_algebraMap] using
    (Algebra.FinitePresentation.equiv
      ((ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).symm) :
        Algebra.FinitePresentation R (ULift.{u} A))

/-- Helper for Chap10 Lemma 10 127 4: an `R`-algebra map lifts functorially to the carrier
`ULift`. -/
private abbrev liftCarrierAlgHom
    {A : Type u} [CommRing A] [Algebra R A]
    {B : Type v} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) :
    ULift.{v} A →ₐ[R] ULift.{u} B :=
  ((ULift.algEquiv : ULift.{u} B ≃ₐ[R] B).symm.toAlgHom).comp
    (f.comp (ULift.algEquiv : ULift.{v} A ≃ₐ[R] A).toAlgHom)

/-- Helper for Chap10 Lemma 10 127 4: an `R`-algebra map between lifted carriers descends back to
the original carriers. -/
private abbrev descendCarrierAlgHom
    {A : Type u} [CommRing A] [Algebra R A]
    {B : Type v} [CommRing B] [Algebra R B]
    (f : ULift.{v} A →ₐ[R] ULift.{u} B) :
    A →ₐ[R] B :=
  ((ULift.algEquiv : ULift.{u} B ≃ₐ[R] B).toAlgHom).comp
    (f.comp (ULift.algEquiv : ULift.{v} A ≃ₐ[R] A).symm.toAlgHom)

/-- Helper for Chap10 Lemma 10 127 4: descending the lifted map recovers the original algebra
homomorphism. -/
private lemma descendCarrierAlgHom_liftCarrierAlgHom
    {A : Type u} [CommRing A] [Algebra R A]
    {B : Type v} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) :
    descendCarrierAlgHom (liftCarrierAlgHom f) = f := by
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 127 4: after lifting both the base ring and the algebra carrier,
`ULift A` carries the canonical `ULift R`-algebra structure used in the same-universe reduction.
-/
private abbrev uliftBaseUliftAlgebra (A : Type v) [CommRing A] [Algebra R A] :
    Algebra (ULift.{v} R) (ULift.{u} A) := by
  letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
  exact @ULift.algebra (ULift.{v} R) A _ _ inferInstance

/-- Helper for Chap10 Lemma 10 127 4: restricting scalars along `R → ULift R` turns a
`ULift R`-algebra object into the corresponding `R`-algebra object on the same carrier. -/
private abbrev restrictBaseObject
    (A : CommAlgCat.{max u v} (ULift.{v} R)) : CommAlgCat.{max u v} R :=
  letI : Algebra R A := Algebra.restrictScalars R (ULift.{v} R) A
  CommAlgCat.of R A

/-- Helper for Chap10 Lemma 10 127 4: extending scalars along the surjective map
`R → ULift R` turns an `R`-algebra object into the corresponding `ULift R`-algebra object on the
same carrier. -/
private abbrev extendBaseObject
    (A : CommAlgCat.{max u v} R) : CommAlgCat.{max u v} (ULift.{v} R) :=
  letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
  CommAlgCat.of (ULift.{v} R) A

/-- Helper for Chap10 Lemma 10 127 4: changing the base ring along `R ≃ ULift R` gives an
equivalence on the ambient mixed-universe commutative-algebra categories. -/
private lemma uliftAlgebraMap_surjective :
    Function.Surjective (algebraMap R (ULift.{v} R)) := by
  -- Proof comment: every lifted scalar is represented by its underlying scalar downstairs.
  intro x
  exact ⟨x.down, rfl⟩

/-- Helper for Chap10 Lemma 10 127 4: changing the base ring along `R ≃ ULift R` gives an
equivalence on the ambient mixed-universe commutative-algebra categories. -/
private noncomputable def commAlgCatBaseUliftEquivalence :
    CommAlgCat.{max u v} R ≌ CommAlgCat.{max u v} (ULift.{v} R) where
  functor :=
    { obj := fun A ↦ extendBaseObject A
      map := fun {A B} f ↦
        -- Proof comment: surjectivity of `R → ULift R` upgrades any `R`-algebra map to the
        -- corresponding `ULift R`-algebra map on the same carrier.
        letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
        letI : Algebra (ULift.{v} R) B := ULift.algebra' R B
        CommAlgCat.ofHom <|
          { toRingHom := f.hom
            commutes' := by
              intro r
              simpa using f.hom.commutes r.down } }
  inverse :=
    { obj := fun A ↦ restrictBaseObject A
      map := fun {A B} f ↦
        -- Proof comment: restricting scalars forgets the lifted base-ring structure.
        letI : Algebra R A := Algebra.restrictScalars R (ULift.{v} R) A
        letI : Algebra R B := Algebra.restrictScalars R (ULift.{v} R) B
        CommAlgCat.ofHom <|
          { toRingHom := f.hom
            commutes' := by
              intro r
              change f.hom ((algebraMap (ULift.{v} R) A) (ULift.up r)) =
                (algebraMap (ULift.{v} R) B) (ULift.up r)
              exact f.hom.commutes (ULift.up r) } }
  unitIso :=
    NatIso.ofComponents
      (fun A ↦
        -- Proof comment: extending then restricting scalars leaves the original `R`-algebra
        -- object unchanged.
        CommAlgCat.isoMk <|
          { toRingEquiv := RingEquiv.refl A
            commutes' := by
              intro r
              rfl })
      (fun f ↦ by
        ext x
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun A ↦
        -- Proof comment: on the `ULift R` side, the inverse comparison is the identity ring
        -- equivalence upgraded by `extendScalarsOfSurjective`.
        CommAlgCat.isoMk <|
          { toRingEquiv := RingEquiv.refl A
            commutes' := by
              intro r
              rfl })
      (fun f ↦ by
        ext x
        rfl)

/-- Helper for Chap10 Lemma 10 127 4: a factorization equality in the base-lifted algebra category
descends back to the original `R`-algebra category via the inverse equivalence. -/
private lemma baseUliftEquivalence_descends_factorization
    {A B C : CommAlgCat.{max u v} R}
    (q : commAlgCatBaseUliftEquivalence.functor.obj A ⟶
      commAlgCatBaseUliftEquivalence.functor.obj B)
    (f : B ⟶ C) (g : A ⟶ C)
    (hq : q ≫ commAlgCatBaseUliftEquivalence.functor.map f =
      commAlgCatBaseUliftEquivalence.functor.map g) :
    (commAlgCatBaseUliftEquivalence.inverse.map q) ≫ f = g := by
  -- Proof comment: apply the inverse functor to the lifted factorization equation and simplify
  -- using functoriality of the explicit base-change equivalence.
  simpa [Functor.map_comp, commAlgCatBaseUliftEquivalence] using
    congrArg commAlgCatBaseUliftEquivalence.inverse.map hq

/-- Helper for Chap10 Lemma 10 127 4: finite presentation survives the explicit universe lift
`R → ULift R`, `A → ULift A`. -/
private lemma uliftAlgebraMapFinitePresentation
    {A : Type v} [CommRing A] [Algebra R A]
    (hA : Algebra.FinitePresentation R A) :
    (RingHom.ulift (algebraMap R A) : ULift.{v} R →+* ULift.{u} A).FinitePresentation := by
  have hAuR : (algebraMap R (ULift.{u} A)).FinitePresentation := by
    letI : Algebra R (ULift.{u} A) := ULift.algebra
    letI : Algebra.FinitePresentation R A := hA
    -- Proof comment: first lift only the target algebra, using `ULift.algEquiv` to keep the
    -- source ring fixed.
    simpa [RingHom.finitePresentation_algebraMap] using
      (Algebra.FinitePresentation.equiv
        ((ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).symm) :
          Algebra.FinitePresentation R (ULift.{u} A))
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := uliftBaseUliftAlgebra A
  letI : IsScalarTower R (ULift.{v} R) (ULift.{u} A) := ULift.isScalarTower'
  let fR : R →+* ULift.{v} R :=
    (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom
  have hfR : fR.FinitePresentation :=
    RingHom.FinitePresentation.of_bijective
      (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).bijective
  have hAlgMap : (algebraMap (ULift.{v} R) (ULift.{u} A)).FinitePresentation := by
    -- Proof comment: after rewriting the original algebra map as a composite through
    -- `R ≃ ULift R`, the owner theorem `of_comp_finiteType` descends finite presentation to the
    -- lifted base ring.
    rw [show algebraMap R (ULift.{u} A) = (algebraMap (ULift.{v} R) (ULift.{u} A)).comp fR by
      ext x
      rfl] at hAuR
    exact RingHom.FinitePresentation.of_comp_finiteType fR hAuR
      (RingHom.FiniteType.of_finitePresentation hfR)
  change (algebraMap (ULift.{v} R) (ULift.{u} A)).FinitePresentation
  exact hAlgMap

/-- Helper for Chap10 Lemma 10 127 4: after changing only the base ring along `R ≃ ULift R`,
the bundled base-lifted object is still finitely presented over the lifted base ring. -/
private lemma extendBaseObject_finitePresentation
    (A : CommAlgCat.{max u v} R) (hA : Algebra.FinitePresentation R A) :
    Algebra.FinitePresentation (ULift.{v} R) (extendBaseObject A) := by
  letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
  letI : IsScalarTower R (ULift.{v} R) A := ULift.isScalarTower'
  let fR : R →+* ULift.{v} R :=
    (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom
  have hfR : fR.FinitePresentation :=
    RingHom.FinitePresentation.of_bijective
      (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).bijective
  have hAR : (algebraMap R A).FinitePresentation := by
    exact (RingHom.finitePresentation_algebraMap :
      (algebraMap R A).FinitePresentation ↔ Algebra.FinitePresentation R A).mpr hA
  -- Proof comment: rewrite the original algebra map through `R ≃ ULift R` and descend
  -- finite presentation along the finite type base change.
  rw [show algebraMap R A = (algebraMap (ULift.{v} R) A).comp fR by
    ext x
    rfl] at hAR
  exact (RingHom.finitePresentation_algebraMap :
    (algebraMap (ULift.{v} R) A).FinitePresentation ↔
      Algebra.FinitePresentation (ULift.{v} R) A).mp <|
        RingHom.FinitePresentation.of_comp_finiteType fR hAR
          (RingHom.FiniteType.of_finitePresentation hfR)

/-- Helper for Chap10 Lemma 10 127 4: after changing only the base ring along `R ≃ ULift R`,
the same carrier is still finitely presentable in `CommAlgCat`. -/
private lemma extendBaseObject_isFinitelyPresentable_of_finitePresentation
    (A : CommAlgCat.{max u v} R) (hA : Algebra.FinitePresentation R A) :
    IsFinitelyPresentable.{max u v} (extendBaseObject A) := by
  have hA' :
      Algebra.FinitePresentation (ULift.{v} R) (extendBaseObject A) :=
    extendBaseObject_finitePresentation (R := R) A hA
  exact commAlgCat_sameUniverse_isFinitelyPresentable_of_finitePresentation
    (extendBaseObject A) hA'

/-- Helper for Chap10 Lemma 10 127 4: restricting scalars along `R → ULift R` on the original
carrier universe gives an object of `CommAlgCat.{v} R`. -/
private abbrev restrictBaseObjectSmall
    (A : CommAlgCat.{v} (ULift.{v} R)) : CommAlgCat.{v} R :=
  letI : Algebra R A := Algebra.restrictScalars R (ULift.{v} R) A
  CommAlgCat.of R A

/-- Helper for Chap10 Lemma 10 127 4: extending scalars along `R → ULift R` on the original
carrier universe gives an object of `CommAlgCat.{v} (ULift R)`. -/
private abbrev extendBaseObjectSmall
    (A : CommAlgCat.{v} R) : CommAlgCat.{v} (ULift.{v} R) :=
  letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
  CommAlgCat.of (ULift.{v} R) A

/-- Helper for Chap10 Lemma 10 127 4: changing the base ring along `R ≃ ULift R` is an
equivalence on `CommAlgCat` without changing the carrier universe. -/
private noncomputable def commAlgCatSmallBaseUliftEquivalence :
    CommAlgCat.{v} R ≌ CommAlgCat.{v} (ULift.{v} R) where
  functor :=
    { obj := fun A ↦ extendBaseObjectSmall (R := R) A
      map := fun {A B} f ↦
        -- Proof comment: surjectivity of `R → ULift R` upgrades any `R`-algebra map to the
        -- corresponding `ULift R`-algebra map on the same carrier.
        letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
        letI : Algebra (ULift.{v} R) B := ULift.algebra' R B
        CommAlgCat.ofHom <|
          { toRingHom := f.hom
            commutes' := by
              intro r
              simpa using f.hom.commutes r.down } }
  inverse :=
    { obj := fun A ↦ restrictBaseObjectSmall (R := R) A
      map := fun {A B} f ↦
        -- Proof comment: restricting scalars forgets the lifted base-ring structure.
        letI : Algebra R A := Algebra.restrictScalars R (ULift.{v} R) A
        letI : Algebra R B := Algebra.restrictScalars R (ULift.{v} R) B
        CommAlgCat.ofHom <|
          { toRingHom := f.hom
            commutes' := by
              intro r
              change f.hom ((algebraMap (ULift.{v} R) A) (ULift.up r)) =
                (algebraMap (ULift.{v} R) B) (ULift.up r)
              exact f.hom.commutes (ULift.up r) } }
  unitIso :=
    NatIso.ofComponents
      (fun A ↦
        -- Proof comment: extending then restricting scalars leaves the original `R`-algebra
        -- object unchanged.
        CommAlgCat.isoMk <|
          { toRingEquiv := RingEquiv.refl A
            commutes' := by
              intro r
              rfl })
      (fun f ↦ by
        ext x
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun A ↦
        -- Proof comment: on the `ULift R` side, the comparison is again the identity ring
        -- equivalence on the underlying carrier.
        CommAlgCat.isoMk <|
          { toRingEquiv := RingEquiv.refl A
            commutes' := by
              intro r
              rfl })
      (fun f ↦ by
        ext x
        rfl)

/-- Helper for Chap10 Lemma 10 127 4: finite presentation survives the small-universe base change
`R → ULift R`. -/
private lemma extendBaseObjectSmall_finitePresentation
    (A : CommAlgCat.{v} R) (hA : Algebra.FinitePresentation R A) :
    Algebra.FinitePresentation (ULift.{v} R) (extendBaseObjectSmall (R := R) A) := by
  letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
  letI : IsScalarTower R (ULift.{v} R) A := ULift.isScalarTower'
  let fR : R →+* ULift.{v} R :=
    (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom
  have hfR : fR.FinitePresentation :=
    RingHom.FinitePresentation.of_bijective
      (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).bijective
  have hAR : (algebraMap R A).FinitePresentation := by
    exact (RingHom.finitePresentation_algebraMap :
      (algebraMap R A).FinitePresentation ↔ Algebra.FinitePresentation R A).mpr hA
  -- Proof comment: rewrite the original algebra map through `R ≃ ULift R` and descend finite
  -- presentation along the finite type base change.
  rw [show algebraMap R A = (algebraMap (ULift.{v} R) A).comp fR by
    ext x
    rfl] at hAR
  exact (RingHom.finitePresentation_algebraMap :
    (algebraMap (ULift.{v} R) A).FinitePresentation ↔
      Algebra.FinitePresentation (ULift.{v} R) A).mp <|
        RingHom.FinitePresentation.of_comp_finiteType fR hAR
          (RingHom.FiniteType.of_finitePresentation hfR)

/-- Helper for Chap10 Lemma 10 127 4: finite presentation makes the represented functor of a
mixed-universe `R`-algebra preserve filtered colimits. -/
private lemma commAlgCat_mixedUniverse_preservesFilteredColimits_coyoneda_of_finitePresentation
    (A : CommAlgCat.{max u v} R) (hA : Algebra.FinitePresentation R A) :
    PreservesFilteredColimits (coyoneda.obj (Opposite.op A)) := by
  let _ : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  have hBaseChanged :
      IsFinitelyPresentable.{max u v}
        (commAlgCatBaseUliftEquivalence.functor.obj A) := by
    -- Proof comment: change only the base ring along `R ≃ ULift R`, where the same-universe
    -- finite-presentation bridge applies directly.
    simpa [commAlgCatBaseUliftEquivalence, extendBaseObject] using
      extendBaseObject_isFinitelyPresentable_of_finitePresentation A hA
  have hPresentable : IsFinitelyPresentable.{max u v} A := by
    -- Proof comment: the explicit base-change equivalence reflects finite presentability back to
    -- the original mixed-universe commutative-algebra category.
    simpa using
      (CategoryTheory.isCardinalPresentable_iff_of_isEquivalence
        A Cardinal.aleph0 commAlgCatBaseUliftEquivalence.functor).mp hBaseChanged
  -- Proof comment: once the object is known to be finitely presentable, the represented functor
  -- preserves filtered colimits in every indexing size.
  exact (isFinitelyPresentable_iff_preservesFilteredColimits).1 hPresentable

/-- Helper for Chap10 Lemma 10 127 4: if `A` is finitely presented over `R`, then the explicit
lifted algebra map `ULift.{v} R →+* ULift.{v} A` is finitely presented. -/
private lemma carrierAndBaseLiftedAlgebraMapFinitePresentation
    {A : Type u} [CommRing A] [Algebra R A]
    (hA : Algebra.FinitePresentation R A) :
    (RingHom.ulift (algebraMap R A) : ULift.{v} R →+* ULift.{v} A).FinitePresentation := by
  have hAuR : (algebraMap R (ULift.{v} A)).FinitePresentation := by
    letI : Algebra R (ULift.{v} A) := ULift.algebra
    letI : Algebra.FinitePresentation R A := hA
    -- Proof comment: first lift only the carrier of `A`, keeping the base ring fixed.
    simpa [RingHom.finitePresentation_algebraMap] using
      (Algebra.FinitePresentation.equiv
        ((ULift.algEquiv : ULift.{v} A ≃ₐ[R] A).symm) :
          Algebra.FinitePresentation R (ULift.{v} A))
  letI : Algebra (ULift.{v} R) (ULift.{v} A) := by
    letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
    exact @ULift.algebra (ULift.{v} R) A _ _ inferInstance
  letI : IsScalarTower R (ULift.{v} R) (ULift.{v} A) := ULift.isScalarTower'
  let fR : R →+* ULift.{v} R :=
    (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom
  have hfR : fR.FinitePresentation :=
    RingHom.FinitePresentation.of_bijective
      (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).bijective
  have hAlgMap : (algebraMap (ULift.{v} R) (ULift.{v} A)).FinitePresentation := by
    -- Proof comment: rewriting the lifted algebra map through `R ≃ ULift R` lets the owner
    -- theorem descend finite presentation along the finite type base change.
    rw [show algebraMap R (ULift.{v} A) = (algebraMap (ULift.{v} R) (ULift.{v} A)).comp fR by
      ext x
      rfl] at hAuR
    exact RingHom.FinitePresentation.of_comp_finiteType fR hAuR
      (RingHom.FiniteType.of_finitePresentation hfR)
  exact hAlgMap

/-- Helper for Chap10 Lemma 10 127 4: package the same-universe `ULift` model of an
`R`-algebra as an object of `CommAlgCat (ULift R)`. -/
private abbrev liftedCommAlgCatObject
    (A : Type v) [CommRing A] [Algebra R A] :
    CommAlgCat.{max u v} (ULift.{v} R) :=
  letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := @ULift.algebra (ULift.{v} R) A _ _ inferInstance
  CommAlgCat.of (ULift.{v} R) (ULift.{u} A)

/-- Helper for Chap10 Lemma 10 127 4: after lifting both the base ring and the carrier universe,
finite presentation gives a same-universe finitely presentable commutative algebra object. -/
private lemma liftedCommAlgCat_isFinitelyPresentable_of_finitePresentation
    {A : Type v} [CommRing A] [Algebra R A]
    (hA : Algebra.FinitePresentation R A) :
    IsFinitelyPresentable.{max u v}
      ((liftedCommAlgCatObject A : CommAlgCat.{max u v} (ULift.{v} R))) := by
  letI : Algebra (ULift.{v} R) A := ULift.algebra' R A
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := @ULift.algebra (ULift.{v} R) A _ _ inferInstance
  have hLifted : Algebra.FinitePresentation (ULift.{v} R) (ULift.{u} A) := by
    -- Proof comment: the explicit lifted algebra map is finitely presented by the direct
    -- base-and-carrier `ULift` transport lemma.
    exact (RingHom.finitePresentation_algebraMap :
      (algebraMap (ULift.{v} R) (ULift.{u} A)).FinitePresentation ↔
        Algebra.FinitePresentation (ULift.{v} R) (ULift.{u} A)).mp <|
          uliftAlgebraMapFinitePresentation hA
  -- Proof comment: now the base ring and carrier live in the same universe, so the standard
  -- `CommRingCat.isFinitelyPresentable_hom` bridge applies directly.
  exact commAlgCat_sameUniverse_isFinitelyPresentable_of_finitePresentation
    (liftedCommAlgCatObject A : CommAlgCat.{max u v} (ULift.{v} R)) hLifted

/-- Helper for Chap10 Lemma 10 127 4: algebraic finite presentation implies categorical finite
presentability for the carrier-lifted object in the ambient mixed-universe category
`CommAlgCat R`. -/
private lemma carrierLiftedCommAlgCat_isFinitelyPresentable_of_finitePresentation
    (A : CommAlgCat.{v} R) (hA : Algebra.FinitePresentation R A) :
    IsFinitelyPresentable.{max u v} (carrierLiftedCommAlgCatObject A) := by
  let _ : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  have hLifted :
      IsFinitelyPresentable.{max u v} (liftedCommAlgCatObject A) :=
    liftedCommAlgCat_isFinitelyPresentable_of_finitePresentation hA
  have hExtended :
      IsFinitelyPresentable.{max u v}
        (extendBaseObject (carrierLiftedCommAlgCatObject A)) := by
    -- Proof comment: first compare the equivalence image with the explicit same-universe lifted
    -- model where finite presentability was already proved.
    letI : Algebra (ULift.{v} R) ↑(carrierLiftedCommAlgCatObject A) :=
      @ULift.algebra (ULift.{v} R) A _ _ (ULift.algebra' R A)
    -- Proof comment: with the lifted base-ring action fixed explicitly, this is exactly the
    -- same object as `liftedCommAlgCatObject A`.
    change IsFinitelyPresentable.{max u v} (liftedCommAlgCatObject A)
    exact hLifted
  have hBaseChanged :
      IsFinitelyPresentable.{max u v}
        (commAlgCatBaseUliftEquivalence.functor.obj
          (carrierLiftedCommAlgCatObject A)) := by
    simpa [commAlgCatBaseUliftEquivalence] using hExtended
  -- Proof comment: equivalences reflect finite presentability, so we descend from the lifted
  -- base ring back to the original base ring on the carrier-lifted object.
  simpa using
    (CategoryTheory.isCardinalPresentable_iff_of_isEquivalence
      (carrierLiftedCommAlgCatObject A)
      Cardinal.aleph0
      commAlgCatBaseUliftEquivalence.functor).mp hBaseChanged

/-- Helper for Chap10 Lemma 10 127 4: the carrier-`ULift` functor on `CommAlgCat R` is fully
faithful, so morphisms between lifted objects identify with morphisms downstairs. -/
private noncomputable def uliftFunctorHomEquiv
    (A B : CommAlgCat.{v} R) :
    ((CommAlgCat.uliftFunctor R).obj A ⟶ (CommAlgCat.uliftFunctor R).obj B) ≃ (A ⟶ B) where
  toFun f :=
    CommAlgCat.ofHom <|
      ((ULift.algEquiv : ULift.{u} B ≃ₐ[R] B).toAlgHom).comp
        (f.hom.comp (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).symm.toAlgHom)
  invFun f :=
    CommAlgCat.ofHom <|
      ((ULift.algEquiv : ULift.{u} B ≃ₐ[R] B).symm.toAlgHom).comp
        (f.hom.comp (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A).toAlgHom)
  left_inv f := by
    ext x
    rfl
  right_inv f := by
    ext x
    rfl

/-- Helper for Chap10 Lemma 10 127 4: descending the image of a morphism under
`CommAlgCat.uliftFunctor` recovers the original morphism. -/
private lemma uliftFunctorHomEquiv_map
    (A B : CommAlgCat.{v} R) (f : A ⟶ B) :
    uliftFunctorHomEquiv A B ((CommAlgCat.uliftFunctor R).map f) = f := by
  -- Proof comment: `uliftFunctorHomEquiv` is defined by composing with `ULift.algEquiv` in both
  -- directions, so it is inverse to `CommAlgCat.uliftFunctor.map` on morphisms.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 127 4: descending a composite with a lifted morphism turns it into
the corresponding composite downstairs. -/
private lemma uliftFunctorHomEquiv_comp_map
    (A B C : CommAlgCat.{v} R)
    (f : (CommAlgCat.uliftFunctor R).obj A ⟶ (CommAlgCat.uliftFunctor R).obj B)
    (g : B ⟶ C) :
    uliftFunctorHomEquiv A C (f ≫ (CommAlgCat.uliftFunctor R).map g) =
      uliftFunctorHomEquiv A B f ≫ g := by
  -- Proof comment: after unfolding the lifted composition, both sides act identically on
  -- elements of the source algebra.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 127 4: after forgetting to `Type`, the carrier-`ULift` functor on
`CommAlgCat R` is literally the usual `CategoryTheory.uliftFunctor`. -/
private noncomputable def commAlgCatUliftFunctorForgetIso :
    CommAlgCat.uliftFunctor.{u, v} R ⋙ forget (CommAlgCat.{max u v} R) ≅
      forget (CommAlgCat.{v} R) ⋙ CategoryTheory.uliftFunctor.{u, v} :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) fun f ↦ by
    -- Proof comment: both composites act by the same underlying function on each element.
    ext x
    rfl

/-- Helper for Chap10 Lemma 10 127 4: descending the lifted selected cocone component recovers
the original structure map to `Λ`. -/
private lemma uliftFunctorHomEquiv_selectedAlgebrasOverTargetCocone_ι_app
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (B : P.FullSubcategory) :
    uliftFunctorHomEquiv B.obj.left (CommAlgCat.of R Λ)
        (((CommAlgCat.uliftFunctor R).mapCocone (selectedAlgebrasOverTargetCocone P)).ι.app B) =
      B.obj.hom := by
  -- Proof comment: the mapped cocone component is just the lifted structure map to `Λ`.
  simpa [selectedAlgebrasOverTargetCocone_ι_app] using
    uliftFunctorHomEquiv_map B.obj.left (CommAlgCat.of R Λ) B.obj.hom

/-- Helper for Chap10 Lemma 10 127 4: if a filtered cocone in the slice category is colimiting
after forgetting, then every map from a finitely presentable source object factors through one
slice stage. -/
private lemma overForget_exists_hom_of_isColimit
    {J : Type w} [Category.{w} J] [IsFiltered J]
    {D : J ⥤ Over (CommAlgCat.of R Λ)} {c : Cocone D}
    (hForget : IsColimit ((Over.forget (CommAlgCat.of R Λ)).mapCocone c))
    {A : Over (CommAlgCat.of R Λ)}
    [IsFinitelyPresentable.{w} A.left] (f : A ⟶ c.pt) :
    ∃ (j : J) (g : A ⟶ D.obj j), g ≫ c.ι.app j = f := by
  obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hForget f.left
  have hgOver : g ≫ (D.obj j).hom = A.hom := by
    -- Proof comment: the forgotten factorization commutes with the slice structure maps because
    -- both the cocone leg and `f` already commute over `Λ`.
    have hgComp : g ≫ (c.ι.app j).left ≫ c.pt.hom = f.left ≫ c.pt.hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ c.pt.hom) hg
    have hStage :
        g ≫ (D.obj j).hom = g ≫ (c.ι.app j).left ≫ c.pt.hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ g ≫ k) (Over.w (c.ι.app j)).symm
    have hTarget : g ≫ (c.ι.app j).left ≫ c.pt.hom = A.hom := by
      exact hgComp.trans (by simpa using Over.w f)
    exact hStage.trans hTarget
  refine ⟨j, Over.homMk g hgOver, ?_⟩
  apply Over.OverMorphism.ext
  exact hg

/-- Helper for Chap10 Lemma 10 127 4: equality of two maps into a filtered slice colimit can be
checked after forgetting to the ambient commutative-algebra category. -/
private lemma overForget_exists_eq_of_isColimit
    {J : Type w} [Category.{w} J] [IsFiltered J]
    {D : J ⥤ Over (CommAlgCat.of R Λ)} {c : Cocone D}
    (hForget : IsColimit ((Over.forget (CommAlgCat.of R Λ)).mapCocone c))
    {A : Over (CommAlgCat.of R Λ)}
    [IsFinitelyPresentable.{w} A.left]
    {i j : J} (f : A ⟶ D.obj i) (g : A ⟶ D.obj j)
    (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v := by
  obtain ⟨k, u, v, huv⟩ :=
    IsFinitelyPresentable.exists_eq_of_isColimit hForget f.left g.left
      (congrArg (fun m ↦ m.left) h)
  refine ⟨k, u, v, ?_⟩
  apply Over.OverMorphism.ext
  exact huv

/-- Helper for Lemma 10.127.4: every finitely presented stage factors through itself, so the
ambient factorization condition is automatic for the full finitely presented over-category. -/
private lemma finitelyPresentedOverTarget_selfFactorization
    (A : Over (CommAlgCat.of R Λ))
    (hA : Algebra.FinitePresentation R A.left) :
    ∃ B : finitelyPresentedOverTargetProperty.FullSubcategory,
      Nonempty (A ⟶ B.obj) := by
  -- Proof comment: the object already lies in the selected full subcategory, and the identity
  -- morphism provides the required factorization.
  exact ⟨⟨A, hA⟩, ⟨𝟙 A⟩⟩

/-- Helper for Chap10 Lemma 10 127 4: a filtered selected stage category is also
`ℵ₀`-filtered in the larger object universe needed by the presentability API. -/
private lemma selectedAlgebrasOverTarget_isCardinalFiltered_aleph0
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    [IsFiltered P.FullSubcategory] [Fact Cardinal.aleph0.IsRegular] :
    IsCardinalFiltered P.FullSubcategory (Cardinal.aleph0 : Cardinal.{max u (v + 1)}) := by
  simpa using
    ((CategoryTheory.isCardinalFiltered_aleph0_iff P.FullSubcategory).2 inferInstance)

/-- Helper for Chap10 Lemma 10 127 4: the carrier-`ULift` of a finitely presented source algebra
is `ℵ₀`-presentable in the ambient mixed-universe category. -/
private lemma carrierLiftedCommAlgCat_isCardinalPresentable_aleph0_of_finitePresentation
    (A : CommAlgCat.{v} R) [Fact Cardinal.aleph0.IsRegular]
    (hA : Algebra.FinitePresentation R A) :
    IsCardinalPresentable.{max u v}
      ((CommAlgCat.uliftFunctor.{u, v} R).obj A) Cardinal.aleph0 := by
  -- Proof comment: finite presentability already upgraded the lifted carrier to a finitely
  -- presentable object, and `IsFinitelyPresentable` is definitionally `ℵ₀`-presentability.
  simpa [IsFinitelyPresentable, carrierLiftedCommAlgCatObject] using
    carrierLiftedCommAlgCat_isFinitelyPresentable_of_finitePresentation A hA

/-- Helper for Chap10 Lemma 10 127 4: descending a composite with a lifted selected cocone leg
recovers the corresponding composite downstairs. -/
private lemma uliftFunctorHomEquiv_comp_selectedAlgebrasOverTargetCocone_ι_app
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (A : Over (CommAlgCat.of R Λ))
    (B : P.FullSubcategory)
    (pLifted :
      (CommAlgCat.uliftFunctor.{u, v} R).obj A.left ⟶
        (CommAlgCat.uliftFunctor.{u, v} R).obj B.obj.left) :
    uliftFunctorHomEquiv A.left (CommAlgCat.of R Λ)
        (pLifted ≫
          (((CommAlgCat.uliftFunctor R).mapCocone
            (selectedAlgebrasOverTargetCocone P)).ι.app B)) =
      uliftFunctorHomEquiv A.left B.obj.left pLifted ≫ B.obj.hom := by
  -- Proof comment: descending through the lifted cocone leg amounts to composing the descended
  -- map with the original structure morphism to `Λ`.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 127 4: once the lifted selected cocone is known to be colimiting,
finite presentability of `A.left` yields a factorization through one selected stage. -/
private lemma descendedFactorization_of_liftedMap
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (A : Over (CommAlgCat.of R Λ))
    (B : P.FullSubcategory)
    (pLifted :
      (CommAlgCat.uliftFunctor.{u, v} R).obj A.left ⟶
        (CommAlgCat.uliftFunctor.{u, v} R).obj B.obj.left)
    (hpLifted :
      pLifted ≫
          (((CommAlgCat.uliftFunctor R).mapCocone
            (selectedAlgebrasOverTargetCocone P)).ι.app B) =
        (CommAlgCat.uliftFunctor R).map A.hom) :
    ∃ p : A.left ⟶ B.obj.left, p ≫ B.obj.hom = A.hom := by
  refine ⟨uliftFunctorHomEquiv A.left B.obj.left pLifted, ?_⟩
  have hpDescended :=
    congrArg (uliftFunctorHomEquiv A.left (CommAlgCat.of R Λ)) hpLifted
  have hmap :
      uliftFunctorHomEquiv A.left (CommAlgCat.of R Λ)
          ((CommAlgCat.uliftFunctor R).map A.hom) = A.hom := by
    simpa using uliftFunctorHomEquiv_map A.left (CommAlgCat.of R Λ) A.hom
  -- Proof comment: the explicit `ULift` descent turns the lifted triangle back into the original
  -- factorization in `CommAlgCat R`.
  exact
    (uliftFunctorHomEquiv_comp_selectedAlgebrasOverTargetCocone_ι_app P A B pLifted).symm.trans
      (hpDescended.trans hmap)

/-- Helper for Chap10 Lemma 10 127 4: the selected ambient cocone lifts to the slice cocone whose
point is the terminal over-object `Over.mk (𝟙 (CommAlgCat.of R Λ))`. -/
private abbrev selectedAlgebrasOverTargetTerminalCocone
    (P : ObjectProperty (Over (CommAlgCat.of R Λ))) :
    Cocone (ObjectProperty.ι P) :=
  Over.liftCocone (selectedAlgebrasOverTargetCocone P) (𝟙 (CommAlgCat.of R Λ))

/-- Helper for Chap10 Lemma 10 127 4: if the selected ambient cocone is colimiting in
`CommAlgCat R`, then its lifted terminal slice cocone is colimiting in `Over (CommAlgCat.of R Λ)`.
-/
private noncomputable def selectedAlgebrasOverTargetTerminalCoconeIsColimit
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hc : IsColimit (selectedAlgebrasOverTargetCocone P)) :
    IsColimit (selectedAlgebrasOverTargetTerminalCocone P) := by
  -- Proof comment: colimits in an over-category are created by the forgetful functor.
  simpa [selectedAlgebrasOverTargetTerminalCocone, selectedAlgebrasOverTargetDiagram,
    selectedAlgebrasOverTargetCocone] using
    Over.isColimitLiftCocone (selectedAlgebrasOverTargetCocone P)
      (𝟙 (CommAlgCat.of R Λ)) hc

/-- Helper for Chap10 Lemma 10 127 4: forgetting the terminal slice lift of the selected cocone is
definitionally the original ambient cocone. -/
private lemma selectedAlgebrasOverTargetTerminalCocone_forget_eq
    (P : ObjectProperty (Over (CommAlgCat.of R Λ))) :
    (Over.forget (CommAlgCat.of R Λ)).mapCocone
      (selectedAlgebrasOverTargetTerminalCocone P) =
        selectedAlgebrasOverTargetCocone P := rfl

/-- Helper for Chap10 Lemma 10 127 4: forgetting the terminal slice lift of the selected cocone
recovers the original ambient cocone, so any ambient colimit proof can be reused after a `simpa`.
-/
private noncomputable def selectedAlgebrasOverTargetTerminalCocone_forget_isColimit
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hc : IsColimit (selectedAlgebrasOverTargetCocone P)) :
    IsColimit ((Over.forget (CommAlgCat.of R Λ)).mapCocone
      (selectedAlgebrasOverTargetTerminalCocone P)) := by
  -- Proof comment: `Over.liftCocone` only adds the terminal structure map, so forgetting that
  -- lift returns the original cocone definitionally.
  simpa [selectedAlgebrasOverTargetTerminalCocone_forget_eq (R := R) (Λ := Λ) P] using hc

/-- Helper for Chap10 Lemma 10 127 4: once a morphism into a selected stage is recovered in the
terminal slice cocone, forgetting it yields the required factorization through that stage. -/
private lemma factorization_eq_of_selected_stage_over_hom
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    {A : Over (CommAlgCat.of R Λ)} {B : P.FullSubcategory}
    (g : A ⟶ B.obj) :
    g.left ≫ B.obj.hom = A.hom := by
  -- Proof comment: this is just the defining commutative triangle of the over-morphism `g`.
  simpa using factorization_eq_of_over_hom g

/-- Helper for Chap10 Lemma 10 127 4: a selected filtered colimit presentation of `Λ` forces every
finitely presented source algebra over `Λ` to factor through one selected stage. -/
private lemma finitelyPresentableOverTarget_liftedFactorization
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hcolim : IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P)))
    (A : Over (CommAlgCat.of R Λ))
    (hA : Algebra.FinitePresentation R A.left) :
    ∃ (B : P.FullSubcategory),
      ∃ p : A.left ⟶ B.obj.left,
        p ≫ B.obj.hom = A.hom := by
  -- Route correction: the attempted direct factorization through
  -- `IsCardinalPresentable.exists_hom_of_isColimit` isolates one remaining owner-level gap.
  -- The new small-universe base-change helpers above show how finite presentation transports
  -- across `R ≃ ULift R`, but this file still lacks the final bridge from that transport to an
  -- `ℵ₀`-presentability instance for `A.left : CommAlgCat.{v} R`.
  -- TODO: package that bridge, then apply `IsCardinalPresentable.exists_hom_of_isColimit`
  -- directly to `selectedAlgebrasOverTargetCocone P` and rewrite the resulting cocone leg with
  -- `selectedAlgebrasOverTargetCocone_ι_app`.
  sorry

/-- Helper for Lemma 10.127.4: the forward implication reduces to factoring a map from a finitely
presented `R`-algebra through a colimit stage. -/
private lemma finitely_presentable_over_target_factors_through_selected_stage
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hcolim : IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P)))
    (A : Over (CommAlgCat.of R Λ))
    (hA : Algebra.FinitePresentation R A.left) :
    ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj) := by
  obtain ⟨B, p, hp⟩ :=
    finitelyPresentableOverTarget_liftedFactorization P hcolim A hA
  exact ⟨B, over_hom_of_factorization p hp⟩

/-- Helper for Lemma 10.127.4: the canonical cocone of all finitely presented `R`-algebras over
`Λ` is the ambient filtered colimit presentation needed for the backward implication. -/
private lemma finitely_presented_stages_over_target_isFilteredColimit :
    IsFiltered
        ((finitelyPresentedOverTargetProperty : ObjectProperty
          (Over (CommAlgCat.of R Λ))).FullSubcategory) ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone
        (finitelyPresentedOverTargetProperty : ObjectProperty
          (Over (CommAlgCat.of R Λ))))) := by
  -- Route correction: the forward bridge
  -- `Algebra.FinitePresentation R A.left → IsFinitelyPresentable A` is now proved above, so the
  -- only remaining blocker is the converse bridge
  -- `IsFinitelyPresentable A → Algebra.FinitePresentation R A.left`.
  -- TODO: prove that converse by extracting a retract of `A` through a finitely presented stage
  -- in a same-universe filtered presentation over `A.left`, then identify
  -- `finitelyPresentedOverTargetProperty` with `ObjectProperty.isFinitelyPresentable` on the
  -- slice and transport the canonical dense costructured-arrow colimit through
  -- `terminalCostructuredArrowEquivalence`.
  sorry

/-- Helper for Lemma 10.127.4: once the ambient finitely presented over-category is filtered, the
factorization hypothesis makes the selected inclusion final. -/
private lemma selected_stages_final_in_finitely_presented_stages
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hPfp : ∀ A : Over (CommAlgCat.of R Λ), P A → Algebra.FinitePresentation R A.left)
    (hfactor :
      ∀ (A : Over (CommAlgCat.of R Λ)) (_ : Algebra.FinitePresentation R A.left),
        ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj))
    [IsFiltered ((finitelyPresentedOverTargetProperty : ObjectProperty
      (Over (CommAlgCat.of R Λ))).FullSubcategory)] :
    let Q : ObjectProperty (Over (CommAlgCat.of R Λ)) := finitelyPresentedOverTargetProperty
    let incl : P.FullSubcategory ⥤ Q.FullSubcategory :=
      ObjectProperty.ιOfLE (fun A hPA ↦ hPfp A hPA)
    incl.Final ∧ IsFiltered P.FullSubcategory := by
  let Q : ObjectProperty (Over (CommAlgCat.of R Λ)) := finitelyPresentedOverTargetProperty
  let incl : P.FullSubcategory ⥤ Q.FullSubcategory :=
    ObjectProperty.ιOfLE (fun A hPA ↦ hPfp A hPA)
  have hExists : ∀ A : Q.FullSubcategory, ∃ B : P.FullSubcategory, Nonempty (A ⟶ incl.obj B) := by
    intro A
    rcases hfactor A.obj A.property with ⟨B, ⟨f⟩⟩
    -- Proof comment: morphisms in a full subcategory are just the underlying over-category maps.
    exact ⟨B, ⟨ObjectProperty.homMk f⟩⟩
  -- Proof comment: Lemma 4.19.3 is exactly the generic owner theorem for fully faithful
  -- inclusions into a filtered category.
  exact ⟨Functor.final_of_exists_of_isFiltered_of_fullyFaithful incl hExists,
    IsFiltered.of_exists_of_isFiltered_of_fullyFaithful incl hExists⟩

/-- Helper for Lemma 10.127.4: after identifying the selected stages as a final subcategory of all
finitely presented stages, the ambient colimit presentation transfers to the selected diagram. -/
private lemma selected_stages_isFilteredColimit_of_factorization
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hPfp : ∀ A : Over (CommAlgCat.of R Λ), P A → Algebra.FinitePresentation R A.left)
    (hfactor :
      ∀ (A : Over (CommAlgCat.of R Λ)) (_ : Algebra.FinitePresentation R A.left),
        ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj)) :
    IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P)) := by
  let Q : ObjectProperty (Over (CommAlgCat.of R Λ)) := finitelyPresentedOverTargetProperty
  let incl : P.FullSubcategory ⥤ Q.FullSubcategory :=
    ObjectProperty.ιOfLE (fun A hPA ↦ hPfp A hPA)
  have hQcolim :
      IsFiltered Q.FullSubcategory ∧
        Nonempty (IsColimit (selectedAlgebrasOverTargetCocone Q)) :=
    finitely_presented_stages_over_target_isFilteredColimit
  obtain ⟨hFilteredQ, ⟨hcQ⟩⟩ := hQcolim
  let _ : IsFiltered Q.FullSubcategory := hFilteredQ
  obtain ⟨hFinal, hFilteredP⟩ :=
    selected_stages_final_in_finitely_presented_stages P hPfp hfactor
  have hcPWhisker :
      IsColimit ((selectedAlgebrasOverTargetCocone Q).whisker incl) := by
    -- Proof comment: finality of the inclusion lets us restrict the ambient colimit cocone to the
    -- selected full subcategory.
    exact (Functor.Final.isColimitWhiskerEquiv incl
      (selectedAlgebrasOverTargetCocone Q)).symm hcQ
  constructor
  · exact hFilteredP
  · refine ⟨?_⟩
    -- Proof comment: after unfolding the selected diagram and cocone owners, the restricted
    -- cocone is definitionally the canonical cocone for `P`.
    simpa [Q, incl, selectedAlgebrasOverTargetCocone, selectedAlgebrasOverTargetDiagram] using
      hcPWhisker

-- Proof sketch: for `(→)`, a map from a finitely presented `R`-algebra into the filtered colimit
-- `Λ` factors through some selected stage by the finite-presentation factorization property. For
-- `(←)`, compare the selected full subcategory with the filtered category of all finitely
-- presented `R`-algebras over `Λ`; the factorization hypothesis makes the inclusion cofinal, so
-- the canonical colimit over all finitely presented stages restricts to a filtered colimit over
-- the selected ones.
/-- Chap10 Lemma 10 127 4: if every selected `R`-algebra over `Λ` is finitely presented over
`R`, then `Λ` is a filtered colimit of selected stages exactly when every finitely presented
`R`-algebra mapping to `Λ` factors through one of the selected stages. -/
@[stacks 07C3]
theorem selectedAlgebrasOverTarget_isFilteredColimit_iff_factorization
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hPfp : ∀ A : Over (CommAlgCat.of R Λ), P A → Algebra.FinitePresentation R A.left) :
    (IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P))) ↔
      ∀ (A : Over (CommAlgCat.of R Λ)) (hA : Algebra.FinitePresentation R A.left),
        ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj) := by
  constructor
  · intro hcolim A hA
    -- Proof comment: finite presentability of the source algebra lets the map into `Λ` descend to
    -- one stage of the selected filtered colimit.
    exact finitely_presentable_over_target_factors_through_selected_stage P hcolim A hA
  · intro hfactor
    -- Proof comment: once every finitely presented over-object factors through a selected stage,
    -- the selected inclusion is final in the ambient finitely presented presentation.
    exact selected_stages_isFilteredColimit_of_factorization P hPfp hfactor

end
