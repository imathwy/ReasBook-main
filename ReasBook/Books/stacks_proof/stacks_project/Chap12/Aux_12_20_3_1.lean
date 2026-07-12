import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

/-- The ambient category used for the fixed-shift viewpoint. It is definitionally the same as the
original category; the name records that we are viewing objects together with a chosen shift. -/
def ShiftedCategory (_ : A ⥤ A) : Type u := A

instance (T : A ⥤ A) : Category (ShiftedCategory T) :=
  inferInstanceAs (Category A)

instance (T : A ⥤ A) [HasZeroMorphisms A] : HasZeroMorphisms (ShiftedCategory T) :=
  inferInstanceAs (HasZeroMorphisms A)

instance (T : A ⥤ A) [Abelian A] : Abelian (ShiftedCategory T) :=
  inferInstanceAs (Abelian A)

section EquivalenceHelpers

/-- The morphism `T⁻¹ E ⟶ E` induced by `d : E ⟶ T(E)`. -/
noncomputable abbrev shiftedPreviousDifferential (T : A ⥤ A) [Functor.IsEquivalence T]
    {E : A} (d : E ⟶ T.obj E) : T.inv.obj E ⟶ E :=
  T.inv.map d ≫ T.asEquivalence.unitInv.app E

/-- A map commuting with shifted differentials also commutes with the translated previous
 differential. -/
theorem shiftedPreviousDifferential_naturality (T : A ⥤ A) [Functor.IsEquivalence T]
    {E₁ E₂ : A} {d₁ : E₁ ⟶ T.obj E₁} {d₂ : E₂ ⟶ T.obj E₂}
    (f : E₁ ⟶ E₂) (h : f ≫ d₂ = d₁ ≫ T.map f) :
    T.inv.map f ≫ shiftedPreviousDifferential T d₂ =
      shiftedPreviousDifferential T d₁ ≫ f := by
  have hunit :
      T.inv.map (T.map f) =
        T.asEquivalence.unitInv.app E₁ ≫ f ≫ T.asEquivalence.unit.app E₂ := by
    -- Express `T.inv.map (T.map f)` through the unit comparison by canceling on the right.
    apply (cancel_mono (T.asEquivalence.unitInv.app E₂)).1
    simpa [Category.assoc] using T.asEquivalence.unitInv_naturality (f := f)
  have h1 :
      T.inv.map f ≫ shiftedPreviousDifferential T d₂ =
        T.inv.map (f ≫ d₂) ≫ T.asEquivalence.unitInv.app E₂ := by
    simp [shiftedPreviousDifferential, Functor.map_comp, Category.assoc]
  have h2 :
      T.inv.map (f ≫ d₂) ≫ T.asEquivalence.unitInv.app E₂ =
        T.inv.map d₁ ≫ T.inv.map (T.map f) ≫ T.asEquivalence.unitInv.app E₂ := by
    rw [h, Functor.map_comp]
    simp [Category.assoc]
  have h3 :
      T.inv.map d₁ ≫ T.inv.map (T.map f) ≫ T.asEquivalence.unitInv.app E₂ =
        T.inv.map d₁ ≫
          ((T.asEquivalence.unitInv.app E₁ ≫ f ≫ T.asEquivalence.unit.app E₂) ≫
            T.asEquivalence.unitInv.app E₂) := by
    rw [hunit]
    rfl
  have h4 :
      T.inv.map d₁ ≫
          ((T.asEquivalence.unitInv.app E₁ ≫ f ≫ T.asEquivalence.unit.app E₂) ≫
            T.asEquivalence.unitInv.app E₂) =
        shiftedPreviousDifferential T d₁ ≫ f := by
    -- The inserted `unit ≫ unitInv` pair collapses to the identity on `E₂`.
    simpa [shiftedPreviousDifferential, Category.assoc] using
      congrArg
        (fun m ↦ T.inv.map d₁ ≫ T.asEquivalence.unitInv.app E₁ ≫ f ≫ m)
        (T.asEquivalence.unitIso.hom_inv_id_app E₂)
  exact h1.trans (h2.trans (h3.trans h4))

end EquivalenceHelpers

section ShiftedDifferentialObject

variable [Abelian A]

/-- The translated previous differential composes with `d` to zero. -/
theorem shiftedPreviousDifferential_comp_d (T : A ⥤ A) [Functor.IsEquivalence T]
    {E : A} (d : E ⟶ T.obj E) (hd : d ≫ T.map d = 0) :
    shiftedPreviousDifferential T d ≫ d = 0 := by
  apply (cancel_mono (T.asEquivalence.unit.app (T.obj E))).1
  have hd' := congrArg (T.inv.map) hd
  simpa [shiftedPreviousDifferential, Functor.map_comp, Category.assoc] using hd'

/-- Mapping the translated previous differential through the equivalence collapses to the
original differential after the counit comparison. -/
theorem mapShiftedPreviousDifferential (T : A ⥤ A) [Functor.IsEquivalence T]
    {E : A} (d : E ⟶ T.obj E) :
    T.map (shiftedPreviousDifferential T d) = T.asEquivalence.counit.app E ≫ d := by
  apply (cancel_epi (T.asEquivalence.counitInv.app E)).1
  have hmap :
      T.map (shiftedPreviousDifferential T d) =
        T.map (T.inv.map d) ≫ T.map (T.asEquivalence.unitInv.app E) := by
    -- Unfold only the translated previous differential before mapping it through `T`.
    simp [shiftedPreviousDifferential, Functor.map_comp]
  have hfun :=
      congrArg
        (fun m ↦ T.asEquivalence.counitInv.app E ≫ m ≫
          T.map (T.asEquivalence.unitInv.app E))
        (T.asEquivalence.fun_inv_map (X := E) (Y := T.obj E) d)
  have htail :=
      congrArg
        (fun m ↦ T.asEquivalence.counitInv.app E ≫
          T.asEquivalence.counit.app E ≫ d ≫
            T.asEquivalence.counitInv.app (T.obj E) ≫ m)
        (T.asEquivalence.counit_app_functor E).symm
  have hcancel_tail :=
      congrArg
        (fun m ↦ T.asEquivalence.counitInv.app E ≫
          T.asEquivalence.counit.app E ≫ d ≫ m)
        (T.asEquivalence.counitIso.inv_hom_id_app (T.obj E))
  have hhead :=
      congrArg (fun m ↦ m ≫ d) (T.asEquivalence.counitIso.inv_hom_id_app E)
  have htriangle :
      T.asEquivalence.counitInv.app E ≫ T.map (shiftedPreviousDifferential T d) = d := by
    have hpre :
        T.asEquivalence.counitInv.app E ≫ T.map (shiftedPreviousDifferential T d) =
          T.asEquivalence.counitInv.app E ≫
            (T.map (T.inv.map d) ≫ T.map (T.asEquivalence.unitInv.app E)) := by
      exact congrArg (fun m ↦ T.asEquivalence.counitInv.app E ≫ m) hmap
    have hstep1 :
        T.asEquivalence.counitInv.app E ≫
            (T.map (T.inv.map d) ≫ T.map (T.asEquivalence.unitInv.app E)) =
          T.asEquivalence.counitInv.app E ≫
            (T.asEquivalence.counit.app E ≫ d ≫
              T.asEquivalence.counitInv.app (T.obj E)) ≫
                T.map (T.asEquivalence.unitInv.app E) := by
      -- Replace `T.map (T.inv.map d)` by its counit-normalized form.
      simpa [Category.assoc] using hfun
    have hstep2a :
        T.asEquivalence.counitInv.app E ≫
            (T.asEquivalence.counit.app E ≫ d ≫
              T.asEquivalence.counitInv.app (T.obj E)) ≫
                T.map (T.asEquivalence.unitInv.app E) =
          T.asEquivalence.counitInv.app E ≫
            T.asEquivalence.counit.app E ≫
              d ≫ T.asEquivalence.counitInv.app (T.obj E) ≫
                T.asEquivalence.counit.app (T.obj E) := by
      -- Rewrite the final mapped unit comparison as the counit on `T.obj E`.
      simpa [Category.assoc] using htail
    have hstep2b :
        T.asEquivalence.counitInv.app E ≫
            T.asEquivalence.counit.app E ≫
              d ≫ T.asEquivalence.counitInv.app (T.obj E) ≫
                T.asEquivalence.counit.app (T.obj E) =
          T.asEquivalence.counitInv.app E ≫
            T.asEquivalence.counit.app E ≫ d := by
      -- Collapse the tail counit-inverse/counit pair.
      simpa [Category.assoc] using hcancel_tail
    have hstep3 :
        T.asEquivalence.counitInv.app E ≫
            T.asEquivalence.counit.app E ≫ d = d := by
      -- Collapse the head counit-inverse/counit pair.
      simpa [Category.assoc] using hhead
    exact hpre.trans (hstep1.trans (hstep2a.trans (hstep2b.trans hstep3)))
  -- Compare after precomposing by the counit inverse, where both sides become `d`.
  exact htriangle.trans (by simpa [Category.assoc] using hhead.symm)

/-- The induced short complex `T⁻¹E ⟶ E ⟶ TE` attached to `d : E ⟶ T(E)`. -/
noncomputable abbrev shiftedPageShortComplex (T : A ⥤ A) [Functor.IsEquivalence T]
    {E : A} (d : E ⟶ T.obj E) (hd : d ≫ T.map d = 0) : ShortComplex A :=
  ShortComplex.mk
    (shiftedPreviousDifferential T d)
    d
    (shiftedPreviousDifferential_comp_d T d hd)

/-- A page endowed with a shifted differential `d : E ⟶ T(E)` squaring to zero. -/
structure ShiftedDifferentialObject (T : A ⥤ A) [Functor.IsEquivalence T] where
  obj : A
  d : obj ⟶ T.obj obj
  d_squared : d ≫ T.map d = 0

namespace ShiftedDifferentialObject

variable {T : A ⥤ A} [Functor.IsEquivalence T]

/-- The short complex `T⁻¹X ⟶ X ⟶ TX` attached to a shifted differential object. -/
noncomputable abbrev shortComplex (X : ShiftedDifferentialObject T) : ShortComplex A :=
  shiftedPageShortComplex T X.d X.d_squared

/-- The homology object `Ker(d) / Im(T⁻¹ d)` of a shifted differential object. -/
noncomputable abbrev homology (X : ShiftedDifferentialObject T) : A :=
  X.shortComplex.homology

/-- The kernel subobject of `d` maps canonically to the cycles object of the associated short
complex. -/
noncomputable def kernelSubobjectToCycles (X : ShiftedDifferentialObject T) :
    (kernelSubobject X.d : A) ⟶ X.shortComplex.cycles :=
  X.shortComplex.liftCycles (kernelSubobject X.d).arrow (by
    simpa [shortComplex] using kernelSubobject_arrow_comp X.d)

/-- Helper for Chap12 Aux 12 20 3 1: the translated differential on the previous page still
 squares to zero after transporting back along the counit inverse. -/
private theorem previousPage_d_squared (X : ShiftedDifferentialObject T) :
    (shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) ≫
      T.map (shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) = 0 := by
  have htriangle :
      T.asEquivalence.counitInv.app X.obj ≫ T.map (shiftedPreviousDifferential T X.d) = X.d := by
    have hmap :
        T.map (shiftedPreviousDifferential T X.d) =
          T.map (T.inv.map X.d) ≫ T.map (T.asEquivalence.unitInv.app X.obj) := by
      -- Unfold only the translated previous differential before mapping it through `T`.
      simp [shiftedPreviousDifferential, Functor.map_comp]
    have h1 :
        T.asEquivalence.counitInv.app X.obj ≫ T.map (shiftedPreviousDifferential T X.d) =
          T.asEquivalence.counitInv.app X.obj ≫
            (T.map (T.inv.map X.d) ≫ T.map (T.asEquivalence.unitInv.app X.obj)) := by
      exact congrArg (fun m ↦ T.asEquivalence.counitInv.app X.obj ≫ m) hmap
    have h2 :
        T.asEquivalence.counitInv.app X.obj ≫
            (T.map (T.inv.map X.d) ≫ T.map (T.asEquivalence.unitInv.app X.obj)) =
          T.asEquivalence.counitInv.app X.obj ≫
            (T.asEquivalence.counit.app X.obj ≫ X.d ≫
              T.asEquivalence.counitInv.app (T.obj X.obj)) ≫
                T.map (T.asEquivalence.unitInv.app X.obj) := by
      -- Replace `T.map (T.inv.map X.d)` by its counit-normalized form.
      simpa [Category.assoc] using
        congrArg
          (fun m ↦ T.asEquivalence.counitInv.app X.obj ≫
            m ≫ T.map (T.asEquivalence.unitInv.app X.obj))
          (T.asEquivalence.fun_inv_map (X := X.obj) (Y := T.obj X.obj) X.d)
    have h3 :
        T.asEquivalence.counitInv.app X.obj ≫
            (T.asEquivalence.counit.app X.obj ≫ X.d ≫
              T.asEquivalence.counitInv.app (T.obj X.obj)) ≫
                T.map (T.asEquivalence.unitInv.app X.obj) =
          T.asEquivalence.counitInv.app X.obj ≫
            T.asEquivalence.counit.app X.obj ≫ X.d ≫
              T.asEquivalence.counitInv.app (T.obj X.obj) ≫
                T.asEquivalence.counit.app (T.obj X.obj) := by
      -- Rewrite the mapped unit comparison as the counit on `T.obj X.obj`.
      simpa [Category.assoc] using
        congrArg
          (fun m ↦ T.asEquivalence.counitInv.app X.obj ≫
            T.asEquivalence.counit.app X.obj ≫ X.d ≫
              T.asEquivalence.counitInv.app (T.obj X.obj) ≫ m)
          (T.asEquivalence.counit_app_functor X.obj).symm
    have h4 :
        T.asEquivalence.counitInv.app X.obj ≫
            T.asEquivalence.counit.app X.obj ≫ X.d ≫
              T.asEquivalence.counitInv.app (T.obj X.obj) ≫
                T.asEquivalence.counit.app (T.obj X.obj) =
          T.asEquivalence.counitInv.app X.obj ≫
            T.asEquivalence.counit.app X.obj ≫ X.d := by
      -- Collapse the tail counit-inverse/counit pair.
      simpa [Category.assoc] using
        congrArg
          (fun m ↦ T.asEquivalence.counitInv.app X.obj ≫
            T.asEquivalence.counit.app X.obj ≫ X.d ≫ m)
          (T.asEquivalence.counitIso.inv_hom_id_app (T.obj X.obj))
    have h5 :
        T.asEquivalence.counitInv.app X.obj ≫
            T.asEquivalence.counit.app X.obj ≫ X.d = X.d := by
      -- Collapse the head counit-inverse/counit pair.
      simpa [Category.assoc] using
        congrArg (fun m ↦ m ≫ X.d) (T.asEquivalence.counitIso.inv_hom_id_app X.obj)
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hmap :
      shiftedPreviousDifferential T X.d ≫
          T.asEquivalence.counitInv.app X.obj ≫
            T.map (shiftedPreviousDifferential T X.d) =
        shiftedPreviousDifferential T X.d ≫ X.d := by
    -- Apply the counit-normalized comparison inside the left factor.
    exact congrArg (fun m ↦ shiftedPreviousDifferential T X.d ≫ m) htriangle
  -- Normalize the mapped translated differential and reduce to `shiftedPreviousDifferential_comp_d`.
  calc
    (shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) ≫
        T.map (shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) =
      shiftedPreviousDifferential T X.d ≫
        T.asEquivalence.counitInv.app X.obj ≫
          T.map (shiftedPreviousDifferential T X.d) ≫
            T.map (T.asEquivalence.counitInv.app X.obj) := by
          rw [Functor.map_comp]
          simp [Category.assoc]
    _ = shiftedPreviousDifferential T X.d ≫
          X.d ≫ T.map (T.asEquivalence.counitInv.app X.obj) := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ m ≫ T.map (T.asEquivalence.counitInv.app X.obj)) hmap
    _ = 0 := by
          rw [← Category.assoc, shiftedPreviousDifferential_comp_d T X.d X.d_squared]
          exact zero_comp

/-- The source-facing previous page `T⁻¹X`, whose differential is the translated previous
differential `T⁻¹ d`. -/
def previousPage (X : ShiftedDifferentialObject T) : ShiftedDifferentialObject T where
  obj := T.inv.obj X.obj
  d := shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj
  d_squared := previousPage_d_squared X

/-- Helper for Chap12 Aux 12 20 3 1: the first differential in the mapped previous-page short
complex matches the original first differential through the counit comparisons. -/
private theorem previousPageMapShortComplexIso_comm₁₂ (X : ShiftedDifferentialObject T) :
    (T.asEquivalence.counitIso.app (T.inv.obj X.obj)).hom ≫ X.shortComplex.f =
      (X.previousPage.shortComplex.map T).f ≫ (T.asEquivalence.counitIso.app X.obj).hom := by
  have hmap :
      (X.previousPage.shortComplex.map T).f =
        (T.asEquivalence.counitIso.app (T.inv.obj X.obj)).hom ≫
          (shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) := by
    -- Rewrite the mapped previous-page differential via `mapShiftedPreviousDifferential`.
    simpa [previousPage, shortComplex, shiftedPageShortComplex, Category.assoc] using
      mapShiftedPreviousDifferential T X.previousPage.d
  have hcollapse :
      ((T.asEquivalence.counitIso.app (T.inv.obj X.obj)).hom ≫
          shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) ≫
            (T.asEquivalence.counitIso.app X.obj).hom =
        (T.asEquivalence.counitIso.app (T.inv.obj X.obj)).hom ≫ X.shortComplex.f := by
    -- The only remaining transport is the counit-inverse/counit cancellation on `X.obj`.
    simpa [shortComplex, shiftedPageShortComplex, shiftedPreviousDifferential, Category.assoc] using
      congrArg
        (fun m ↦ (T.asEquivalence.counitIso.app (T.inv.obj X.obj)).hom ≫
          T.inv.map X.d ≫ T.asEquivalence.unitInv.app X.obj ≫ m)
        (T.asEquivalence.counitIso.inv_hom_id_app X.obj)
  -- After the previous-page differential is normalized, only the counit cancellation remains.
  rw [hmap]
  exact hcollapse.symm

/-- Helper for Chap12 Aux 12 20 3 1: the second differential in the mapped previous-page short
complex matches the original differential through the counit comparisons. -/
private theorem previousPageMapShortComplexIso_comm₂₃ (X : ShiftedDifferentialObject T) :
    (T.asEquivalence.counitIso.app X.obj).hom ≫ X.shortComplex.g =
      (X.previousPage.shortComplex.map T).g ≫ (T.mapIso (T.asEquivalence.counitIso.app X.obj)).hom := by
  have hmap :
      (X.previousPage.shortComplex.map T).g =
        T.map (shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) := by
    rfl
  have hcollapse :
      T.map (shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) ≫
          (T.mapIso (T.asEquivalence.counitIso.app X.obj)).hom =
        T.map (shiftedPreviousDifferential T X.d) := by
    -- Push the right comparison inside `T.map` and cancel the mapped counit pair there.
    calc
      T.map (shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj) ≫
          (T.mapIso (T.asEquivalence.counitIso.app X.obj)).hom =
        T.map (shiftedPreviousDifferential T X.d) ≫
          T.map (T.asEquivalence.counitInv.app X.obj ≫
            (T.asEquivalence.counitIso.app X.obj).hom) := by
              rw [Functor.map_comp]
              simp [Category.assoc]
      _ = T.map (shiftedPreviousDifferential T X.d) := by
            have htail :
                T.map (T.asEquivalence.counitInv.app X.obj) ≫
                    T.map (T.asEquivalence.counitIso.hom.app X.obj) =
                  𝟙 (T.obj X.obj) := by
              simpa [Functor.map_comp] using
                congrArg (fun m ↦ T.map m) (T.asEquivalence.counitIso.inv_hom_id_app X.obj)
            have htail'' :
                T.map (T.inv.map X.d) ≫ T.map (T.asEquivalence.unitInv.app X.obj) ≫
                    T.map (T.asEquivalence.counitInv.app X.obj ≫
                      (T.asEquivalence.counitIso.app X.obj).hom) =
                  T.map (T.inv.map X.d) ≫ T.map (T.asEquivalence.unitInv.app X.obj) := by
              simpa [Category.assoc] using
                congrArg
                  (fun m ↦ T.map (T.inv.map X.d) ≫
                    T.map (T.asEquivalence.unitInv.app X.obj) ≫ m)
                  htail
            have htail''' :
                T.map (shiftedPreviousDifferential T X.d) ≫
                    T.map (T.asEquivalence.counitInv.app X.obj ≫
                      (T.asEquivalence.counitIso.app X.obj).hom) =
                  T.map (shiftedPreviousDifferential T X.d) := by
              rw [shiftedPreviousDifferential, Functor.map_comp]
              repeat rw [Category.assoc]
              exact htail''
            exact htail'''
  -- Normalize the mapped previous-page differential, then cancel the mapped counit pair.
  rw [hmap]
  exact (mapShiftedPreviousDifferential T X.d).symm.trans hcollapse.symm

/-- Helper for Chap12 Aux 12 20 3 1: mapping the previous-page short complex through `T`
recovers the original short complex via the counit comparisons. -/
noncomputable def previousPageMapShortComplexIso (X : ShiftedDifferentialObject T) :
    X.previousPage.shortComplex.map T ≅ X.shortComplex :=
  ShortComplex.isoMk
    (T.asEquivalence.counitIso.app (T.inv.obj X.obj))
    (T.asEquivalence.counitIso.app X.obj)
    (T.mapIso (T.asEquivalence.counitIso.app X.obj))
    (previousPageMapShortComplexIso_comm₁₂ X)
    (previousPageMapShortComplexIso_comm₂₃ X)

/-- The homology of the previous page is canonically the translated homology `T⁻¹ H(X)`. -/
noncomputable def previousPage_homologyIso (X : ShiftedDifferentialObject T) :
    X.previousPage.homology ≅ T.inv.obj X.homology := by
  -- First transport mapped previous-page homology back to `X.homology`, then apply the unit iso.
  refine T.asEquivalence.unitIso.app X.previousPage.homology ≪≫ ?_
  refine T.inv.mapIso ((X.previousPage.shortComplex.mapHomologyIso T).symm ≪≫ ?_)
  -- The short-complex comparison supplies the remaining homology transport.
  exact ShortComplex.homologyMapIso (previousPageMapShortComplexIso X)

/-- The kernel of the previous-page differential maps canonically to the translated homology
`T⁻¹ H(X)`. -/
noncomputable def previousPageCyclesToHomology (X : ShiftedDifferentialObject T) :
    (kernelSubobject X.previousPage.d : A) ⟶ T.inv.obj X.homology :=
  X.previousPage.kernelSubobjectToCycles ≫
    X.previousPage.shortComplex.homologyπ ≫
      X.previousPage_homologyIso.hom

/-- Pull a subobject of the translated homology `T⁻¹ H(X)` back to the corresponding subobject of
the previous page `T⁻¹ X`. -/
noncomputable def pullbackToPreviousPage (X : ShiftedDifferentialObject T)
    (Z : Subobject (T.inv.obj X.homology)) :
    Subobject X.previousPage.obj :=
  (Subobject.map (kernelSubobject X.previousPage.d).arrow).obj
    ((Subobject.pullback X.previousPageCyclesToHomology).obj Z)

/-- Morphisms of shifted differential objects. -/
@[ext]
structure Hom (X Y : ShiftedDifferentialObject T) where
  hom : X.obj ⟶ Y.obj
  comm : hom ≫ Y.d = X.d ≫ T.map hom

instance : Category (ShiftedDifferentialObject T) where
  Hom X Y := Hom X Y
  id X :=
    { hom := 𝟙 X.obj
      comm := by simp }
  comp := fun {X Y Z} φ ψ =>
    { hom := φ.hom ≫ ψ.hom
      comm := by
        calc
          (φ.hom ≫ ψ.hom) ≫ Z.d = φ.hom ≫ (ψ.hom ≫ Z.d) := by simp [Category.assoc]
          _ = φ.hom ≫ (Y.d ≫ T.map ψ.hom) := by rw [ψ.comm]
          _ = (φ.hom ≫ Y.d) ≫ T.map ψ.hom := by simp [Category.assoc]
          _ = (X.d ≫ T.map φ.hom) ≫ T.map ψ.hom := by rw [φ.comm]
          _ = X.d ≫ (T.map φ.hom ≫ T.map ψ.hom) := by simp [Category.assoc]
          _ = X.d ≫ T.map (φ.hom ≫ ψ.hom) := by rw [Functor.map_comp]
      }

/-- The induced map of short complexes attached to a morphism of shifted differential objects. -/
noncomputable abbrev shortComplexMap {X Y : ShiftedDifferentialObject T} (φ : X ⟶ Y) :
    X.shortComplex ⟶ Y.shortComplex :=
  ShortComplex.homMk
    (T.inv.map φ.hom)
    φ.hom
    (T.map φ.hom)
    (by
      simpa [shortComplex] using
        shiftedPreviousDifferential_naturality T φ.hom φ.comm)
    (by simpa [shortComplex] using φ.comm)

/-- A morphism of shifted differential objects induces a morphism on homology. -/
noncomputable abbrev homologyMap {X Y : ShiftedDifferentialObject T} (φ : X ⟶ Y) :
    X.homology ⟶ Y.homology :=
  ShortComplex.homologyMap (shortComplexMap φ)

end ShiftedDifferentialObject

section ShiftFunctorPages

variable [HasShift A ℤ]

namespace ShiftedDifferentialObject

/-- For the unit shift `X ⟶ X⟦1⟧`, the induced differential on the `n`-th shifted component. -/
noncomputable def iteratedShiftPageDifferential
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    X.obj⟦n⟧ ⟶ X.obj⟦n + 1⟧ :=
  (show X.obj⟦n⟧ ⟶ (shiftFunctor A (1 : ℤ) ⋙ shiftFunctor A n).obj X.obj from X.d⟦n⟧') ≫
    (shiftFunctorComm A (1 : ℤ) n).hom.app X.obj ≫
    (shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj

/-- Helper for Chap12 Aux 12 20 3 1: the fixed unit-shift datum packages to a standard
`DifferentialObject ℤ A`. -/
private theorem iteratedShiftPageDifferential_toDifferentialObject_dSquared
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) :
    X.d ≫ X.d⟦(1 : ℤ)⟧' = 0 := by
  -- The shifted-differential hypothesis already has the standard differential-object shape.
  simpa using X.d_squared

/-- Helper for Chap12 Aux 12 20 3 1: the fixed unit-shift datum viewed as a
`DifferentialObject ℤ A`. -/
private def iteratedShiftPageDifferential_toDifferentialObject
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) : DifferentialObject ℤ A :=
  { obj := X.obj
    d := X.d
    d_squared := iteratedShiftPageDifferential_toDifferentialObject_dSquared X }

/-- Helper for Chap12 Aux 12 20 3 1: postcomposing the normalized page differential with the
`shiftFunctorAdd` comparison recovers the raw shifted differential. -/
private theorem iteratedShiftPageDifferential_comp_shiftFunctorAdd_hom
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    iteratedShiftPageDifferential X n ≫ (shiftFunctorAdd A n (1 : ℤ)).hom.app X.obj =
      (show X.obj⟦n⟧ ⟶ ((shiftFunctor A n ⋙ shiftFunctor A (1 : ℤ)).obj X.obj) from
        X.d⟦n⟧' ≫ (shiftFunctorComm A (1 : ℤ) n).hom.app X.obj) := by
  let raw : X.obj⟦n⟧ ⟶ ((shiftFunctor A n ⋙ shiftFunctor A (1 : ℤ)).obj X.obj) :=
    X.d⟦n⟧' ≫ (shiftFunctorComm A (1 : ℤ) n).hom.app X.obj
  -- The terminal `shiftFunctorAdd` inverse is only bookkeeping for the target index `n + 1`.
  simpa [raw, iteratedShiftPageDifferential, Category.assoc] using
    congrArg (fun m ↦ raw ≫ m) ((shiftFunctorAdd A n (1 : ℤ)).inv_hom_id_app X.obj)

/-- Successive differentials in the canonical shifted page complex compose to zero. -/
theorem iteratedShiftPageDifferential_sq
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    iteratedShiftPageDifferential X n ≫ iteratedShiftPageDifferential X (n + 1) = 0 := by
  let D : DifferentialObject ℤ A := iteratedShiftPageDifferential_toDifferentialObject X
  let rawN : X.obj⟦n⟧ ⟶ ((shiftFunctor A n ⋙ shiftFunctor A (1 : ℤ)).obj X.obj) :=
    X.d⟦n⟧' ≫ (shiftFunctorComm A (1 : ℤ) n).hom.app X.obj
  let rawNext : X.obj⟦n + 1⟧ ⟶ ((shiftFunctor A (n + 1) ⋙ shiftFunctor A (1 : ℤ)).obj X.obj) :=
    X.d⟦n + 1⟧' ≫ (shiftFunctorComm A (1 : ℤ) (n + 1)).hom.app X.obj
  have hraw : rawN ≫ (shiftFunctor A (1 : ℤ)).map rawN = 0 := by
    -- First forget the `shiftFunctorAdd` bookkeeping and reuse the square-zero proof of the
    -- shifted differential object inside mathlib.
    simpa [D, rawN, iteratedShiftPageDifferential_toDifferentialObject, Functor.map_comp,
      Category.assoc] using ((DifferentialObject.shiftFunctor A n).obj D).d_squared
  have htransport :
      (shiftFunctor A (1 : ℤ)).map rawN ≫
        (shiftFunctor A (1 : ℤ)).map ((shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj) =
      (shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj ≫ rawNext := by
    -- The `DifferentialObject.shiftFunctorAdd` comparison transports the raw differential from
    -- degree `n` to the normalized target `n + 1`.
    simpa [D, rawN, rawNext, iteratedShiftPageDifferential_toDifferentialObject,
      Functor.map_comp, Category.assoc] using
      (((DifferentialObject.shiftFunctorAdd A n (1 : ℤ)).inv.app D).comm)
  have htransport' :
      rawN ≫ (shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj ≫ rawNext ≫
          (shiftFunctorAdd A (n + 1) (1 : ℤ)).inv.app X.obj =
        rawN ≫ ((shiftFunctor A (1 : ℤ)).map rawN ≫
            (shiftFunctor A (1 : ℤ)).map ((shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj)) ≫
          (shiftFunctorAdd A (n + 1) (1 : ℤ)).inv.app X.obj := by
    -- Rewrite the second normalized differential in terms of the shifted raw differential.
    simpa [Category.assoc] using
      congrArg
        (fun m ↦ rawN ≫ m ≫ (shiftFunctorAdd A (n + 1) (1 : ℤ)).inv.app X.obj)
        htransport.symm
  have hraw' :
      rawN ≫ ((shiftFunctor A (1 : ℤ)).map rawN ≫
          (shiftFunctor A (1 : ℤ)).map ((shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj)) ≫
        (shiftFunctorAdd A (n + 1) (1 : ℤ)).inv.app X.obj = 0 := by
    -- Once everything is written in the raw shifted spelling, the square-zero relation kills the
    -- composite and the remaining transport factors compose with zero.
    calc
      rawN ≫ ((shiftFunctor A (1 : ℤ)).map rawN ≫
          (shiftFunctor A (1 : ℤ)).map ((shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj)) ≫
          (shiftFunctorAdd A (n + 1) (1 : ℤ)).inv.app X.obj =
        (rawN ≫ (shiftFunctor A (1 : ℤ)).map rawN) ≫
          (shiftFunctor A (1 : ℤ)).map ((shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj) ≫
            (shiftFunctorAdd A (n + 1) (1 : ℤ)).inv.app X.obj := by
              simp [Category.assoc]
      _ = 0 := by
            rw [hraw]
            -- The raw differential square has already vanished, so only the zero tail remains.
            rw [zero_comp]
  -- Put the normalized differentials back together and finish from the transported raw square.
  calc
    iteratedShiftPageDifferential X n ≫ iteratedShiftPageDifferential X (n + 1) =
      rawN ≫ (shiftFunctorAdd A n (1 : ℤ)).inv.app X.obj ≫ rawNext ≫
        (shiftFunctorAdd A (n + 1) (1 : ℤ)).inv.app X.obj := by
          simp [rawN, rawNext, iteratedShiftPageDifferential, Category.assoc]
    _ = 0 := by
          rw [htransport']
          exact hraw'

/-- The canonical cochain complex attached to a shifted differential object for the unit shift. -/
noncomputable def iteratedShiftPageComplex
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) :
    CochainComplex A ℤ :=
  CochainComplex.of
    (fun n : ℤ => X.obj⟦n⟧)
    (iteratedShiftPageDifferential X)
    (iteratedShiftPageDifferential_sq X)

@[simp]
theorem iteratedShiftPageComplex_X
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (iteratedShiftPageComplex X).X n = X.obj⟦n⟧ :=
  rfl

/-- Helper for Chap12 Aux 12 20 3 1: the inverse equivalence chosen by
`Iso.isoInverseOfIsoFunctor` is the natural isomorphism from `⟦-1⟧` to the abstract inverse
functor of `⟦1⟧`. -/
private noncomputable abbrev unitShiftInverseNatIso :
    shiftFunctor A (-1 : ℤ) ≅ (shiftFunctor A (1 : ℤ)).inv :=
  Iso.isoInverseOfIsoFunctor
    (G := shiftEquiv A (1 : ℤ))
    (G' := (shiftFunctor A (1 : ℤ)).asEquivalence)
    (Iso.refl _)

/-- Helper for Chap12 Aux 12 20 3 1: the chosen inverse to the unit shift is canonically
identified with the concrete `(-1)`-shift. -/
private noncomputable def unitShiftInverseIso (X : A) :
    ((shiftFunctor A (-1 : ℤ)).obj X) ≅ ((shiftFunctor A (1 : ℤ)).inv.obj X) :=
  (unitShiftInverseNatIso (A := A)).app X

/-- Helper for Chap12 Aux 12 20 3 1: the first object of the shifted-page short complex is the
`n`-shift of the previous page. -/
private noncomputable abbrev shiftedPageFirstObjectIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    X.obj⟦n - 1⟧ ≅ ((shiftFunctor A n).obj ((shiftFunctor A (1 : ℤ)).inv.obj X.obj)) := by
  exact shiftAdd X.obj n (-1 : ℤ) ≪≫
    shiftComm X.obj n (-1 : ℤ) ≪≫
      (shiftFunctor A n).mapIso (unitShiftInverseIso (A := A) X.obj)

/-- Helper for Chap12 Aux 12 20 3 1: the third object of the shifted page complex matches the
shifted target object of the source-facing short complex. -/
private noncomputable abbrev shiftedPageThirdObjectIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    X.obj⟦n + 1⟧ ≅ ((shiftFunctor A n).obj ((shiftFunctor A (1 : ℤ)).obj X.obj)) :=
  by
    exact (shiftAdd X.obj n (1 : ℤ)) ≪≫ (shiftComm X.obj (1 : ℤ) n).symm

/-- Helper for Chap12 Aux 12 20 3 1: the third-object transport cancels with its inverse. -/
private theorem shiftedPageThirdObjectIso_hom_inv
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (shiftedPageThirdObjectIso (A := A) X n).hom ≫
      (shiftedPageThirdObjectIso (A := A) X n).inv = 𝟙 _ := by
  -- Proof comment: this is the standard right-cancellation identity for the endpoint transport.
  simpa using (shiftedPageThirdObjectIso (A := A) X n).hom_inv_id

omit [Abelian A] in
/-- Helper for Chap12 Aux 12 20 3 1: the comparison between the concrete `(-1)`-shift and the
abstract inverse functor is natural in the underlying object. -/
private theorem unitShiftInverseIso_naturality {X Y : A} (f : X ⟶ Y) :
    (unitShiftInverseIso (A := A) X).hom ≫ (shiftFunctor A (1 : ℤ)).inv.map f =
      f⟦(-1 : ℤ)⟧' ≫ (unitShiftInverseIso (A := A) Y).hom := by
  -- Proof comment: this is exactly naturality of the functor isomorphism
  -- `shiftFunctor (-1) ≅ (shiftFunctor 1).inv`.
  change
    ((unitShiftInverseNatIso (A := A)).hom.app X) ≫ (shiftFunctor A (1 : ℤ)).inv.map f =
      f⟦(-1 : ℤ)⟧' ≫ ((unitShiftInverseNatIso (A := A)).hom.app Y)
  simpa using
    (NatTrans.naturality ((unitShiftInverseNatIso (A := A)).hom) f).symm

omit [Abelian A] in
/-- Helper for Chap12 Aux 12 20 3 1: expose the chosen inverse-shift comparison in the
owner-level `unit ≫ inv.map(counit)` normal form. -/
private theorem unitShiftInverseIso_hom_eq_unit_comp_invMapCounit (X : A) :
    (unitShiftInverseIso (A := A) ((shiftFunctor A (1 : ℤ)).obj X)).hom =
      (shiftFunctor A (1 : ℤ)).asEquivalence.unit.app
          ((shiftFunctor A (-1 : ℤ)).obj ((shiftFunctor A (1 : ℤ)).obj X)) ≫
        (shiftFunctor A (1 : ℤ)).asEquivalence.inverse.map
          ((shiftFunctorCompIsoId A (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).hom.app
            ((shiftFunctor A (1 : ℤ)).obj X)) := by
  -- Route correction: expose the owner-level `unit ≫ inv.map(counit)` spelling once so later
  -- proofs can use the triangle identity instead of reopening `Functor.inv_fun_map`.
  simpa [unitShiftInverseIso, unitShiftInverseNatIso, shiftEquiv, shiftEquiv', Category.assoc]

omit [Abelian A] in
/-- Helper for Chap12 Aux 12 20 3 1: the abstract inverse-functor endpoint comparison matches the
canonical shift-cancellation map. -/
private theorem unitShiftInverseIso_hom_unitInv (X : A) :
    (unitShiftInverseIso (A := A) ((shiftFunctor A (1 : ℤ)).obj X)).hom ≫
      (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X =
        (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X := by
  -- Route correction: rewrite the chosen inverse comparison once, then collapse the endpoint by
  -- the unit naturality square and the shifted `shiftFunctorCompIsoId` formula instead of
  -- reopening the unstable inverse-functor-map tail.
  rw [unitShiftInverseIso_hom_eq_unit_comp_invMapCounit (A := A) X]
  have hshift :
      (shiftFunctorCompIsoId A (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).hom.app
          ((shiftFunctor A (1 : ℤ)).obj X) =
        ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X)⟦
          (1 : ℤ)⟧' := by
    -- Rewrite the shifted counit to the canonical `shiftFunctorCompIsoId` spelling once.
    simpa using
      (shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app (C := A) (n := (1 : ℤ)) (X := X)).symm
  have hunit :
      (shiftFunctor A (1 : ℤ)).asEquivalence.unit.app
          ((shiftFunctor A (-1 : ℤ)).obj ((shiftFunctor A (1 : ℤ)).obj X)) ≫
        (shiftFunctor A (1 : ℤ)).asEquivalence.inverse.map
          ((shiftFunctorCompIsoId A (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).hom.app
            ((shiftFunctor A (1 : ℤ)).obj X)) =
      (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X ≫
        (shiftFunctor A (1 : ℤ)).asEquivalence.unit.app X := by
    -- Naturality of the unit moves the canonical `shiftFunctorCompIsoId` map across the abstract
    -- inverse-functor comparison.
    simpa [Functor.comp_map, hshift] using
      (NatTrans.naturality (shiftFunctor A (1 : ℤ)).asEquivalence.unit
        ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X)).symm
  calc
    ((shiftFunctor A (1 : ℤ)).asEquivalence.unit.app
          ((shiftFunctor A (-1 : ℤ)).obj ((shiftFunctor A (1 : ℤ)).obj X)) ≫
        (shiftFunctor A (1 : ℤ)).asEquivalence.inverse.map
          ((shiftFunctorCompIsoId A (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).hom.app
            ((shiftFunctor A (1 : ℤ)).obj X))) ≫
        (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X =
      ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X ≫
          (shiftFunctor A (1 : ℤ)).asEquivalence.unit.app X) ≫
        (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X := by
          simpa [Category.assoc] using
            congrArg
              (fun m ↦ m ≫ (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X)
              hunit
    _ =
      (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X ≫
        ((shiftFunctor A (1 : ℤ)).asEquivalence.unit.app X ≫
          (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X) := by
            simp [Category.assoc]
    _ = (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X := by
          simpa [Category.assoc] using
            congrArg
              (fun m ↦
                (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X ≫
                  m)
              ((shiftFunctor A (1 : ℤ)).asEquivalence.unitIso.hom_inv_id_app X)

omit [Abelian A] in
/-- Helper for Chap12 Aux 12 20 3 1: whiskering the concrete inverse-shift identification by
`⟦1⟧` and then applying the unit is exactly the standard shift-cancellation isomorphism. -/
private theorem unitShiftInverseNatIso_comp_unitIsoSymm :
    Functor.isoWhiskerLeft (shiftFunctor A (1 : ℤ)) (unitShiftInverseNatIso (A := A)) ≪≫
      (shiftFunctor A (1 : ℤ)).asEquivalence.unitIso.symm =
        shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ)) := by
  -- Proof comment: after the owner-level bridge is proved once, the natural-iso equality is just
  -- componentwise extensionality.
  ext X
  simpa [unitShiftInverseIso] using unitShiftInverseIso_hom_unitInv (A := A) X

/-- Helper for Chap12 Aux 12 20 3 1: the translated previous differential becomes the concrete
`(-1)`-shifted differential after identifying the abstract inverse functor with `⟦-1⟧`. -/
private theorem unitShiftInverseIso_hom_shiftedPreviousDifferential
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) :
    (unitShiftInverseIso (A := A) X.obj).hom ≫
      shiftedPreviousDifferential (shiftFunctor A (1 : ℤ)) X.d =
        X.d⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X.obj := by
  -- Proof comment: first expand the translated previous differential, then use naturality to move
  -- the concrete `(-1)`-shift comparison across `X.d`, and finally collapse the endpoint by the
  -- component theorem above.
  calc
    (unitShiftInverseIso (A := A) X.obj).hom ≫
        shiftedPreviousDifferential (shiftFunctor A (1 : ℤ)) X.d =
      (unitShiftInverseIso (A := A) X.obj).hom ≫
        (shiftFunctor A (1 : ℤ)).inv.map X.d ≫
          (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X.obj := by
            simp [shiftedPreviousDifferential]
    _ =
      ((unitShiftInverseIso (A := A) X.obj).hom ≫
          (shiftFunctor A (1 : ℤ)).inv.map X.d) ≫
        (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X.obj := by
          simp [Category.assoc]
    _ =
      (X.d⟦(-1 : ℤ)⟧' ≫
          (unitShiftInverseIso (A := A) ((shiftFunctor A (1 : ℤ)).obj X.obj)).hom) ≫
        (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X.obj := by
          exact congrArg
            (fun m ↦ m ≫ (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X.obj)
            (unitShiftInverseIso_naturality (A := A) (f := X.d))
    _ = X.d⟦(-1 : ℤ)⟧' ≫
          (unitShiftInverseIso (A := A) ((shiftFunctor A (1 : ℤ)).obj X.obj)).hom ≫
            (shiftFunctor A (1 : ℤ)).asEquivalence.unitInv.app X.obj := by
          simp [Category.assoc]
    _ = X.d⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X.obj := by
            simpa [Category.assoc] using
              congrArg
                (fun m ↦ X.d⟦(-1 : ℤ)⟧' ≫ m)
                (unitShiftInverseIso_hom_unitInv (A := A) X.obj)

omit [Abelian A] in
/-- Helper for Chap12 Aux 12 20 3 1: the pure shift tail carrying
`E⟦1⟧⟦n - 1⟧` to `E⟦n - 1⟧⟦1⟧` is the standard `shiftFunctorComm` comparison. -/
private theorem shiftedPageFirstTailComparison (E : A) (n : ℤ) :
    (shiftAdd (X := E⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
        (shiftComm (X := E⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
          ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app E)⟦n⟧' ≫
            (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n (sub_add_cancel n 1)).hom.app E =
      (shiftFunctorComm A (1 : ℤ) (n - 1)).hom.app E := by
  -- Proof comment: rewrite the target `shiftFunctorComm` by `shiftFunctorAdd'`, then compare the
  -- `1 + (-1) + n` transport with the `1 + (n - 1)` transport via one associativity identity.
  rw [shiftFunctorComm_eq A (1 : ℤ) (n - 1) n (by omega)]
  rw [Iso.trans_hom]
  suffices
      hpre :
        (shiftAdd (X := E⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
            (shiftComm (X := E⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
              ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ)
                (add_neg_cancel (1 : ℤ))).hom.app E)⟦n⟧' =
          (shiftFunctorAdd' A (1 : ℤ) (n - 1) n (by omega)).inv.app E by
    simpa [Category.assoc] using
      congrArg
        (fun m ↦ m ≫ (shiftFunctorAdd' A (n - 1) (1 : ℤ) n (sub_add_cancel n 1)).hom.app E)
        hpre
  change
    (shiftAdd (X := E⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
        (shiftFunctorComm A n (-1 : ℤ)).hom.app (E⟦(1 : ℤ)⟧) ≫
          ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ)
            (add_neg_cancel (1 : ℤ))).hom.app E)⟦n⟧' =
      (shiftFunctorAdd' A (1 : ℤ) (n + (-1 : ℤ)) n (by omega)).inv.app E
  rw [shiftFunctorComm_eq A n (-1 : ℤ) (n + (-1 : ℤ)) rfl]
  rw [Iso.trans_hom]
  have hassoc :
      ((shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0 (add_neg_cancel (1 : ℤ))).inv.app E)⟦n⟧' ≫
          (shiftFunctorAdd' A 0 n n (zero_add n)).inv.app E =
        (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).inv.app (E⟦(1 : ℤ)⟧) ≫
          (shiftFunctorAdd' A (1 : ℤ) (n + (-1 : ℤ)) n (by omega)).inv.app E := by
    -- Proof comment: this is the one associativity identity comparing
    -- `(1 + (-1)) + n` with `1 + ((-1) + n)`.
    simpa using
      (shiftFunctorAdd'_assoc_inv_app (C := A) (a₁ := (1 : ℤ)) (a₂ := (-1 : ℤ))
        (a₃ := n) (a₁₂ := 0) (a₂₃ := n + (-1 : ℤ)) (a₁₂₃ := n)
        (h₁₂ := add_neg_cancel (1 : ℤ)) (h₂₃ := by omega) (h₁₂₃ := by omega) E)
  have hcomp :=
      congrArg
        (fun m ↦
          (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫ m)
        hassoc
  have hfront :
      (shiftFunctorAdd A n (-1 : ℤ)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (shiftFunctorAdd A n (-1 : ℤ)).inv.app (E⟦(1 : ℤ)⟧) ≫
            ((shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
              (shiftFunctor A n).map
                ((shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0
                  (add_neg_cancel (1 : ℤ))).inv.app E) ≫
              (shiftFunctor A n).map ((shiftFunctorZero A ℤ).hom.app E)) =
        (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (shiftFunctor A n).map
            ((shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0
              (add_neg_cancel (1 : ℤ))).inv.app E) ≫
          (shiftFunctor A n).map ((shiftFunctorZero A ℤ).hom.app E) := by
    -- Proof comment: the initial `shiftAdd ≫ shiftAdd⁻¹` pair cancels before the associativity
    -- comparison is used.
    simpa [Category.assoc] using
      congrArg
        (fun m ↦
          m ≫
            ((shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
              (shiftFunctor A n).map
                ((shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0
                  (add_neg_cancel (1 : ℤ))).inv.app E) ≫
              (shiftFunctor A n).map ((shiftFunctorZero A ℤ).hom.app E)))
        ((shiftFunctorAdd A n (-1 : ℤ)).hom_inv_id_app (E⟦(1 : ℤ)⟧))
  have hback :
      (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).inv.app (E⟦(1 : ℤ)⟧) ≫
            (shiftFunctorAdd' A (1 : ℤ) (n + (-1 : ℤ)) n (by omega)).inv.app E =
        (shiftFunctorAdd' A (1 : ℤ) (n + (-1 : ℤ)) n (by omega)).inv.app E := by
    -- Proof comment: the final `shiftFunctorAdd'` transport cancels against its inverse.
    simpa [Category.assoc] using
      congrArg
        (fun m ↦ m ≫ (shiftFunctorAdd' A (1 : ℤ) (n + (-1 : ℤ)) n (by omega)).inv.app E)
        ((shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom_inv_id_app (E⟦(1 : ℤ)⟧))
  have hstep1 :
      (shiftFunctorAdd A n (-1 : ℤ)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (shiftFunctorAdd A n (-1 : ℤ)).inv.app (E⟦(1 : ℤ)⟧) ≫
            (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
              (shiftFunctor A n).map
                ((shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0
                  (add_neg_cancel (1 : ℤ))).inv.app E) ≫
              (shiftFunctor A n).map ((shiftFunctorZero A ℤ).hom.app E) =
        (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (((shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0
              (add_neg_cancel (1 : ℤ))).inv.app E)⟦n⟧' ≫
            (shiftFunctorAdd' A 0 n n (zero_add n)).inv.app E) := by
    simpa [Category.assoc, shiftFunctorAdd'_zero_add_inv_app, Functor.map_comp] using hfront
  have hstep2 :
      (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (((shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0
              (add_neg_cancel (1 : ℤ))).inv.app E)⟦n⟧' ≫
            (shiftFunctorAdd' A 0 n n (zero_add n)).inv.app E) =
        (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0 (add_neg_cancel (1 : ℤ))).inv.app E⟦n⟧' ≫
            (shiftFunctorAdd' A 0 n n (zero_add n)).inv.app E := by
    simp
  have hstep3 :
      (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (shiftFunctorAdd' A (1 : ℤ) (-1 : ℤ) 0 (add_neg_cancel (1 : ℤ))).inv.app E⟦n⟧' ≫
            (shiftFunctorAdd' A 0 n n (zero_add n)).inv.app E =
        (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).hom.app (E⟦(1 : ℤ)⟧) ≫
          (shiftFunctorAdd' A (-1 : ℤ) n (n + (-1 : ℤ)) (by omega)).inv.app (E⟦(1 : ℤ)⟧) ≫
            (shiftFunctorAdd' A (1 : ℤ) (n + (-1 : ℤ)) n (by omega)).inv.app E := by
    simpa [Category.assoc] using hcomp
  simpa [shiftAdd, shiftFunctorCompIsoId, shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, shiftFunctorAdd'_zero_add_inv_app,
    Category.assoc] using
    hstep1.trans (hstep2.trans (hstep3.trans hback))

/-- Helper for Chap12 Aux 12 20 3 1: after postcomposing with the `shiftFunctorAdd`
comparison, the shifted previous differential becomes the raw shifted differential. -/
private theorem shiftedPreviousDifferential_shift_comp_shiftFunctorAdd_hom
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (shiftedPageFirstObjectIso (A := A) X n).hom ≫
      (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).f) ≫
        (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n (sub_add_cancel n 1)).hom.app X.obj =
      X.d⟦n - 1⟧' ≫ (shiftFunctorComm A (1 : ℤ) (n - 1)).hom.app X.obj := by
  have hshifted :
      (shiftAdd X.obj n (-1 : ℤ)).hom ≫
          (shiftComm X.obj n (-1 : ℤ)).hom ≫
            ((unitShiftInverseIso (A := A) X.obj).hom ≫
                shiftedPreviousDifferential (shiftFunctor A (1 : ℤ)) X.d)⟦n⟧' ≫
              (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                (sub_add_cancel n 1)).hom.app X.obj =
        (shiftAdd X.obj n (-1 : ℤ)).hom ≫
          (shiftComm X.obj n (-1 : ℤ)).hom ≫
            (X.d⟦(-1 : ℤ)⟧' ≫
                (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                  X.obj)⟦n⟧' ≫
              (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                (sub_add_cancel n 1)).hom.app X.obj := by
    -- Shift the base `(-1)`-normalized comparison to degree `n`.
    simpa [Functor.map_comp, Category.assoc] using
      congrArg
        (fun m ↦ (shiftAdd X.obj n (-1 : ℤ)).hom ≫
            (shiftComm X.obj n (-1 : ℤ)).hom ≫ m⟦n⟧' ≫
              (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                (sub_add_cancel n 1)).hom.app X.obj)
        (unitShiftInverseIso_hom_shiftedPreviousDifferential (A := A) X)
  have hmain :
      (shiftedPageFirstObjectIso (A := A) X n).hom ≫
          (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).f) ≫
            (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
              (sub_add_cancel n 1)).hom.app X.obj =
        (shiftAdd X.obj n (-1 : ℤ)).hom ≫
          (shiftComm X.obj n (-1 : ℤ)).hom ≫
            (X.d⟦(-1 : ℤ)⟧' ≫
                (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                  X.obj)⟦n⟧' ≫
              (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                (sub_add_cancel n 1)).hom.app X.obj := by
    simpa [shiftedPageFirstObjectIso, shortComplex, shiftedPageShortComplex,
      Functor.map_comp, Category.assoc] using hshifted
  have htail :
      (shiftAdd X.obj n (-1 : ℤ)).hom ≫
          (shiftComm X.obj n (-1 : ℤ)).hom ≫
            (X.d⟦(-1 : ℤ)⟧' ≫
                (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                  X.obj)⟦n⟧' ≫
              (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                (sub_add_cancel n 1)).hom.app X.obj =
        X.d⟦n - 1⟧' ≫ (shiftFunctorComm A (1 : ℤ) (n - 1)).hom.app X.obj := by
    -- Proof comment: move the shifted differential across `shiftComm`, then use `shift_shift'`
    -- to pass through the front `shiftAdd` transport, and finally apply the pure tail lemma.
    have hcomm :
        (shiftComm X.obj n (-1 : ℤ)).hom ≫ (X.d⟦(-1 : ℤ)⟧')⟦n⟧' =
          X.d⟦n⟧'⟦(-1 : ℤ)⟧' ≫
            (shiftComm (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom := by
      simpa using
        (shiftComm_hom_comp (C := A) (X := X.obj) (Y := X.obj⟦(1 : ℤ)⟧) (f := X.d)
          (i := n) (j := (-1 : ℤ)))
    have hshift :
        (shiftAdd X.obj n (-1 : ℤ)).hom ≫ X.d⟦n⟧'⟦(-1 : ℤ)⟧' =
          X.d⟦n + (-1 : ℤ)⟧' ≫ (shiftAdd (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom := by
      have hcancel :
          (shiftAdd X.obj n (-1 : ℤ)).hom ≫
              (shiftAdd X.obj n (-1 : ℤ)).inv ≫
                X.d⟦n + (-1 : ℤ)⟧' ≫
                  (shiftAdd (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom =
            X.d⟦n + (-1 : ℤ)⟧' ≫ (shiftAdd (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom := by
        simpa [Category.assoc] using
          congrArg
            (fun m ↦ m ≫ X.d⟦n + (-1 : ℤ)⟧' ≫
              (shiftAdd (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom)
            ((shiftAdd X.obj n (-1 : ℤ)).hom_inv_id)
      calc
        (shiftAdd X.obj n (-1 : ℤ)).hom ≫ X.d⟦n⟧'⟦(-1 : ℤ)⟧' =
          (shiftAdd X.obj n (-1 : ℤ)).hom ≫
            ((shiftAdd X.obj n (-1 : ℤ)).inv ≫ X.d⟦n + (-1 : ℤ)⟧' ≫
              (shiftAdd (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom) := by
                rw [shift_shift' (X := X.obj) (Y := X.obj⟦(1 : ℤ)⟧) (f := X.d) (i := n)
                  (j := (-1 : ℤ))]
        _ = X.d⟦n + (-1 : ℤ)⟧' ≫ (shiftAdd (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom := by
              exact hcancel
    calc
      (shiftAdd X.obj n (-1 : ℤ)).hom ≫
          (shiftComm X.obj n (-1 : ℤ)).hom ≫
            (X.d⟦(-1 : ℤ)⟧' ≫
                (shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                  X.obj)⟦n⟧' ≫
              (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                (sub_add_cancel n 1)).hom.app X.obj =
        (shiftAdd X.obj n (-1 : ℤ)).hom ≫
          (shiftComm X.obj n (-1 : ℤ)).hom ≫
            (X.d⟦(-1 : ℤ)⟧')⟦n⟧' ≫
              ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                X.obj)⟦n⟧' ≫
                (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                  (sub_add_cancel n 1)).hom.app X.obj := by
              simp [Functor.map_comp, Category.assoc]
      _ =
        (shiftAdd X.obj n (-1 : ℤ)).hom ≫
          X.d⟦n⟧'⟦(-1 : ℤ)⟧' ≫
            (shiftComm (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
              ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                X.obj)⟦n⟧' ≫
                (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                  (sub_add_cancel n 1)).hom.app X.obj := by
              simpa [Category.assoc] using
                congrArg
                  (fun m ↦ (shiftAdd X.obj n (-1 : ℤ)).hom ≫ m ≫
                    ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                      X.obj)⟦n⟧' ≫
                    (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                      (sub_add_cancel n 1)).hom.app X.obj)
                  hcomm
      _ =
        X.d⟦n - 1⟧' ≫
          (shiftAdd (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
            (shiftComm (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
              ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                X.obj)⟦n⟧' ≫
                (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                  (sub_add_cancel n 1)).hom.app X.obj := by
              simpa [sub_eq_add_neg, Category.assoc] using
                congrArg
                  (fun m ↦ m ≫ (shiftComm (X := X.obj⟦(1 : ℤ)⟧) n (-1 : ℤ)).hom ≫
                    ((shiftFunctorCompIsoId A (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
                      X.obj)⟦n⟧' ≫
                    (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
                      (sub_add_cancel n 1)).hom.app X.obj)
                  hshift
      _ =
        X.d⟦n - 1⟧' ≫ (shiftFunctorComm A (1 : ℤ) (n - 1)).hom.app X.obj := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ X.d⟦n - 1⟧' ≫ m)
              (shiftedPageFirstTailComparison (A := A) X.obj n)
  -- Proof comment: the first-object comparison was already normalized in `hmain`, so only the
  -- tail comparison remains.
  exact hmain.trans htail

/-- Helper for Chap12 Aux 12 20 3 1: after normalizing the first shifted object, the mapped
previous differential is exactly the first differential of the iterated shifted page complex. -/
private theorem iteratedShiftPageComplex_d_eq_iteratedShiftPageDifferential
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (iteratedShiftPageComplex X).d n (n + 1) =
      (show X.obj⟦n⟧ ⟶ X.obj⟦n + 1⟧ from iteratedShiftPageDifferential X n) := by
  -- Proof comment: `iteratedShiftPageComplex` is defined by `CochainComplex.of`, so its
  -- degree-`n` differential is exactly the page differential used to build it.
  simpa [iteratedShiftPageComplex] using
    (CochainComplex.of_d (X := fun m : ℤ ↦ X.obj⟦m⟧)
      (d := iteratedShiftPageDifferential X) (sq := iteratedShiftPageDifferential_sq X) (j := n))

/-- Helper for Chap12 Aux 12 20 3 1: after normalizing the first shifted object, the mapped
previous differential is exactly the first differential of the iterated shifted page complex. -/
private theorem iteratedShiftPageComplexFirstDifferential_transport_comp_shiftFunctorAdd_hom
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (iteratedShiftPageComplex X).d (n - 1) ((n - 1) + 1) ≫
      (CategoryTheory.shiftFunctorAdd A (n - 1) (1 : ℤ)).hom.app X.obj =
        X.d⟦n - 1⟧' ≫ (shiftFunctorComm A (1 : ℤ) (n - 1)).hom.app X.obj := by
  -- Route correction: rewrite the `CochainComplex.of` first differential only after
  -- postcomposing by the canonical `shiftFunctorAdd` comparison, so the bare `CochainComplex.of`
  -- differential stays in its natural codomain spelling `((n - 1) + 1)`.
  have hd :
      (iteratedShiftPageComplex X).d (n - 1) ((n - 1) + 1) =
        (show X.obj⟦n - 1⟧ ⟶ X.obj⟦(n - 1) + 1⟧ from
          iteratedShiftPageDifferential X (n - 1)) := by
    simpa using
      (iteratedShiftPageComplex_d_eq_iteratedShiftPageDifferential (A := A) X (n - 1))
  calc
    (iteratedShiftPageComplex X).d (n - 1) ((n - 1) + 1) ≫
        (CategoryTheory.shiftFunctorAdd A (n - 1) (1 : ℤ)).hom.app X.obj =
      iteratedShiftPageDifferential X (n - 1) ≫
        (CategoryTheory.shiftFunctorAdd A (n - 1) (1 : ℤ)).hom.app X.obj := by
            simpa using
              congrArg
                (fun m ↦ m ≫
                  (CategoryTheory.shiftFunctorAdd A (n - 1) (1 : ℤ)).hom.app X.obj)
                hd
    _ = X.d⟦n - 1⟧' ≫ (shiftFunctorComm A (1 : ℤ) (n - 1)).hom.app X.obj := by
          -- This is exactly the normalization already recorded for the page differential.
          simpa [Category.assoc] using
            iteratedShiftPageDifferential_comp_shiftFunctorAdd_hom (A := A) X (n - 1)

/-- Helper for Chap12 Aux 12 20 3 1: the first differential of the iterated shifted page complex
matches the raw shifted differential once both are postcomposed by the same `shiftFunctorAdd'`
comparison. -/
private theorem iteratedShiftPageComplexFirstDifferential_comp_shiftFunctorAdd_hom
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (iteratedShiftPageComplex X).d (n - 1) n ≫
      (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n (sub_add_cancel n 1)).hom.app X.obj =
        X.d⟦n - 1⟧' ≫ (shiftFunctorComm A (1 : ℤ) (n - 1)).hom.app X.obj := by
  -- Proof comment: expand `shiftFunctorAdd'` once to expose the single arithmetic cast
  -- `X.obj⟦n⟧ ⟶ X.obj⟦(n - 1) + 1⟧`, then collapse that cast against the complex differential.
  have hrel_cast : (ComplexShape.up ℤ).Rel (n - 1) n := by
    simpa using (ComplexShape.up_mk (n - 1) n (sub_add_cancel n 1))
  have hrel_succ : (ComplexShape.up ℤ).Rel (n - 1) ((n - 1) + 1) := by
    simpa using (ComplexShape.up_mk (n - 1) ((n - 1) + 1) rfl)
  have hXcast :
      (iteratedShiftPageComplex X).X n =
        (iteratedShiftPageComplex X).X ((n - 1) + 1) := by
    exact congrArg
      (fun m ↦ (iteratedShiftPageComplex X).X m)
      ((ComplexShape.up ℤ).next_eq hrel_cast hrel_succ)
  have hcast :
      (iteratedShiftPageComplex X).d (n - 1) n ≫
          eqToHom hXcast =
        (iteratedShiftPageComplex X).d (n - 1) ((n - 1) + 1) := by
    simpa [iteratedShiftPageComplex_X] using
      (HomologicalComplex.d_comp_eqToHom (C := iteratedShiftPageComplex X)
        (rij := hrel_succ) (rij' := hrel_cast))
  calc
    (iteratedShiftPageComplex X).d (n - 1) n ≫
        (CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n
          (sub_add_cancel n 1)).hom.app X.obj =
      ((iteratedShiftPageComplex X).d (n - 1) n ≫
          eqToHom hXcast) ≫
        (CategoryTheory.shiftFunctorAdd A (n - 1) (1 : ℤ)).hom.app X.obj := by
          simpa [CategoryTheory.shiftFunctorAdd', Category.assoc, iteratedShiftPageComplex_X]
    _ = (iteratedShiftPageComplex X).d (n - 1) ((n - 1) + 1) ≫
          (CategoryTheory.shiftFunctorAdd A (n - 1) (1 : ℤ)).hom.app X.obj := by
            simpa [Category.assoc] using
              congrArg
                (fun m ↦ m ≫
                  (CategoryTheory.shiftFunctorAdd A (n - 1) (1 : ℤ)).hom.app X.obj)
                hcast
    _ = X.d⟦n - 1⟧' ≫ (shiftFunctorComm A (1 : ℤ) (n - 1)).hom.app X.obj := by
          exact
            iteratedShiftPageComplexFirstDifferential_transport_comp_shiftFunctorAdd_hom
              (A := A) X n

/-- Helper for Chap12 Aux 12 20 3 1: after normalizing the first shifted object, the mapped
previous differential is exactly the first differential of the iterated shifted page complex. -/
private theorem shiftedPreviousDifferential_shift_eq_iteratedShiftPageDifferential
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (shiftedPageFirstObjectIso (A := A) X n).hom ≫
      (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).f) =
        (iteratedShiftPageComplex X).d (n - 1) n := by
  -- Route correction: normalize the mapped previous differential through the first-object bridge
  -- once, compare both sides after postcomposition by the same `shiftFunctorAdd'` component,
  -- and then cancel that common isomorphism.
  apply (cancel_mono
    ((CategoryTheory.shiftFunctorAdd' A (n - 1) (1 : ℤ) n (sub_add_cancel n 1)).hom.app X.obj)).1
  simpa [Category.assoc] using
    (shiftedPreviousDifferential_shift_comp_shiftFunctorAdd_hom (A := A) X n).trans
      (iteratedShiftPageComplexFirstDifferential_comp_shiftFunctorAdd_hom
        (A := A) X n).symm

/-- Helper for Chap12 Aux 12 20 3 1: the degree `n` short complex can be written with explicit
indices `(n - 1, n, n + 1)`. -/
private theorem iteratedShiftPageComplex_prev_eq (n : ℤ) :
    (ComplexShape.up ℤ).prev n = n - 1 := by
  apply ComplexShape.prev_eq'
  simpa using (ComplexShape.up_mk (n - 1) n (sub_add_cancel n 1))

/-- Helper for Chap12 Aux 12 20 3 1: the degree `n` short complex can be written with explicit
indices `(n - 1, n, n + 1)`. -/
private theorem iteratedShiftPageComplex_next_eq (n : ℤ) :
    (ComplexShape.up ℤ).next n = n + 1 := by
  apply ComplexShape.next_eq'
  simpa using (ComplexShape.up_mk n (n + 1) rfl)

/-- Helper for Chap12 Aux 12 20 3 1: the first square of the shifted-page short-complex
comparison is exactly the normalized previous-differential identity. -/
private theorem iteratedShiftPageComplexShortComplexIso_comm₁₂
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (shiftedPageFirstObjectIso (A := A) X n).hom ≫
      (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).f) =
        ((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).f := by
  -- Proof comment: the first map of `(iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)` is
  -- `(iteratedShiftPageComplex X).d (n - 1) n`.
  simpa using
    shiftedPreviousDifferential_shift_eq_iteratedShiftPageDifferential (A := A) X n

/-- Helper for Chap12 Aux 12 20 3 1: the second square of the shifted-page short-complex
comparison identifies the normalized page differential with the shifted source differential. -/
private theorem iteratedShiftPageComplexShortComplexIso_comm₂₃
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).g) =
      ((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).g ≫
        (shiftedPageThirdObjectIso (A := A) X n).hom := by
  have hg :
      ((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).g =
        (show X.obj⟦n⟧ ⟶ X.obj⟦n + 1⟧ from iteratedShiftPageDifferential X n) := by
    -- Proof comment: the second map of `K.sc' (n - 1) n (n + 1)` is `K.d n (n + 1)`.
    simpa using
      iteratedShiftPageComplex_d_eq_iteratedShiftPageDifferential (A := A) X n
  -- Proof comment: cancel the inverse of the third-object transport; this reduces the square to
  -- the defining formula for `iteratedShiftPageDifferential`.
  apply (cancel_mono ((shiftedPageThirdObjectIso (A := A) X n).inv)).1
  have hcollapse :
      (((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).g ≫
          (shiftedPageThirdObjectIso (A := A) X n).hom) ≫
            (shiftedPageThirdObjectIso (A := A) X n).inv =
        ((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).g := by
    -- Proof comment: the third-object transport is an isomorphism, so `hom ≫ inv` collapses.
    simpa [Category.assoc] using
      congrArg
        (fun m ↦ ((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).g ≫ m)
        (shiftedPageThirdObjectIso_hom_inv (A := A) X n)
  have hleft :
      (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).g) ≫
        (shiftedPageThirdObjectIso (A := A) X n).inv =
      ((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).g := by
    rw [hg]
    have hcomm :
        (shiftFunctorComm A n (1 : ℤ)).inv.app X.obj =
          (shiftFunctorComm A (1 : ℤ) n).hom.app X.obj := by
      -- Proof comment: the commutation isomorphism is symmetric in the two shift indices.
      simpa using
        congrArg (fun e ↦ e.hom.app X.obj) (shiftFunctorComm_symm A n (1 : ℤ))
    simp [shiftedPageThirdObjectIso, shortComplex, shiftedPageShortComplex,
      iteratedShiftPageDifferential, hcomm]
  exact hleft.trans hcollapse.symm

/-- Helper for Chap12 Aux 12 20 3 1: the first square of the explicit `(n - 1, n, n + 1)` short
complex has the exact `ShortComplex.isoMk` shape. -/
private theorem iteratedShiftPageComplexShortComplexIso_comm₁₂_isoMk
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (shiftedPageFirstObjectIso (A := A) X n).hom ≫
      (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).f) =
        ((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).f ≫
          (Iso.refl (((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).X₂)).hom := by
  -- Proof comment: this is the same first-square identity, rewritten in the exact shape expected
  -- by `ShortComplex.isoMk`.
  simpa using iteratedShiftPageComplexShortComplexIso_comm₁₂ (A := A) X n

/-- Helper for Chap12 Aux 12 20 3 1: the second square of the explicit `(n - 1, n, n + 1)` short
complex has the exact `ShortComplex.isoMk` shape. -/
private theorem iteratedShiftPageComplexShortComplexIso_comm₂₃_isoMk
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (Iso.refl (((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).X₂)).hom ≫
        (((shiftFunctor A n).mapShortComplex.obj X.shortComplex).g) =
      ((iteratedShiftPageComplex X).sc' (n - 1) n (n + 1)).g ≫
        (shiftedPageThirdObjectIso (A := A) X n).hom := by
  -- Proof comment: this is the same second-square identity, rewritten in the exact shape expected
  -- by `ShortComplex.isoMk`.
  simpa using iteratedShiftPageComplexShortComplexIso_comm₂₃ (A := A) X n

/-- Helper for Chap12 Aux 12 20 3 1: the shifted short complex of the iterated page complex is
canonically identified with the shifted source-facing short complex. -/
private noncomputable def iteratedShiftPageComplexShortComplexIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    ((iteratedShiftPageComplex X)⟦n⟧).sc (0 : ℤ) ≅
      ((shiftFunctor A n).mapShortComplex.obj X.shortComplex) :=
  -- Proof comment: first use the canonical shift/short-complex comparison to move from
  -- `((iteratedShiftPageComplex X)⟦n⟧).sc 0` to `(iteratedShiftPageComplex X).sc n`, then replace
  -- the two endpoint objects by the source-facing shifted page objects.
  (CochainComplex.shiftShortComplexFunctorIso A n (0 : ℤ) n (add_zero n)).app
      (iteratedShiftPageComplex X) ≪≫
    (iteratedShiftPageComplex X).isoSc' (n - 1) n (n + 1)
      (iteratedShiftPageComplex_prev_eq n) (iteratedShiftPageComplex_next_eq n) ≪≫
    ShortComplex.isoMk
      (shiftedPageFirstObjectIso (A := A) X n)
      (Iso.refl _)
      (shiftedPageThirdObjectIso (A := A) X n)
      (iteratedShiftPageComplexShortComplexIso_comm₁₂_isoMk (A := A) X n)
      (iteratedShiftPageComplexShortComplexIso_comm₂₃_isoMk (A := A) X n)

/-- Chap12 Aux 12 20 3 1: the `n`-th homology of the canonical shifted page complex is the `n`-fold shift of the
source-facing homology object. -/
noncomputable def iteratedShiftPageComplexHomologyIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    (iteratedShiftPageComplex X).homology n ≅ X.homology⟦n⟧ := by
  refine (((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (0 : ℤ)).shiftIso
      n (0 : ℤ) n (by simp)).app (iteratedShiftPageComplex X)).symm ≪≫ ?_
  refine ShortComplex.homologyMapIso (iteratedShiftPageComplexShortComplexIso X n) ≪≫ ?_
  simpa [homology, shortComplex] using X.shortComplex.mapHomologyIso (shiftFunctor A n)

end ShiftedDifferentialObject

end ShiftFunctorPages

end ShiftedDifferentialObject

end CategoryTheory
