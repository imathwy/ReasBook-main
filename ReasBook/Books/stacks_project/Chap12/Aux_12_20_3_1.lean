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
  sorry

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

/-- The source-facing previous page `T⁻¹X`, whose differential is the translated previous
differential `T⁻¹ d`. -/
def previousPage (X : ShiftedDifferentialObject T) : ShiftedDifferentialObject T where
  obj := T.inv.obj X.obj
  d := shiftedPreviousDifferential T X.d ≫ T.asEquivalence.counitInv.app X.obj
  d_squared := by
    sorry

/-- The homology of the previous page is canonically the translated homology `T⁻¹ H(X)`. -/
noncomputable def previousPage_homologyIso (X : ShiftedDifferentialObject T) :
    X.previousPage.homology ≅ T.inv.obj X.homology := by
  sorry

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
        change (φ.hom ≫ ψ.hom) ≫ Z.d = X.d ≫ T.map (φ.hom ≫ ψ.hom)
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

/-- Successive differentials in the canonical shifted page complex compose to zero. -/
theorem iteratedShiftPageDifferential_sq
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    iteratedShiftPageDifferential X n ≫ iteratedShiftPageDifferential X (n + 1) = 0 := by
  sorry

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

/-- The degree-zero short complex of the shifted page complex is the shift of the source-facing
page short complex. -/
private noncomputable def iteratedShiftPageComplexShortComplexIso
    (X : ShiftedDifferentialObject (shiftFunctor A (1 : ℤ))) (n : ℤ) :
    ((iteratedShiftPageComplex X)⟦n⟧).sc (0 : ℤ) ≅
      ((shiftFunctor A n).mapShortComplex.obj X.shortComplex) := by
  refine (CochainComplex.shiftShortComplexFunctorIso A n (0 : ℤ) n (by simp)).app
      (iteratedShiftPageComplex X) ≪≫ ?_
  sorry

/-- The `n`-th homology of the canonical shifted page complex is the `n`-fold shift of the
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
