import Mathlib
import stacks_project.Chap12.Aux_12_20_3_1

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Remark 12.20.3 (Variant): a spectral sequence relative to translation autoequivalences `T_r`
on an abelian category consists of pages `E_r`, differentials `d_r : E_r ⟶ T_r(E_r)` with
`T_r(d_r) ∘ d_r = 0`, and identifications of `E_{r+1}` with the homology
`Ker(d_r) / Im(T_r⁻¹ d_r)` of the induced short complex `T_r⁻¹ E_r ⟶ E_r ⟶ T_r E_r`. -/
structure ShiftedSpectralSequence (T : ℕ+ → (A ≌ A)) where
  /-- The `r`-th page, viewed as a shifted differential object. -/
  page (r : ℕ+) : ShiftedDifferentialObject (T r).functor
  /-- The homology of the `r`-th page identifies with the underlying object of the next page. -/
  iso (r : ℕ+) : (page r).homology ≅ (page (r + 1)).obj

namespace ShiftedSpectralSequence

variable {T : ℕ+ → (A ≌ A)}

/-- The positive page index corresponding to the textbook page number `n + 1`. -/
private def pageIndex (n : ℕ) : ℕ+ :=
  ⟨n + 1, Nat.succ_pos _⟩

/-- The cycle subobject on the textbook page `E_{n+1}`. -/
private abbrev pageCyclesSubobject (S : ShiftedSpectralSequence T) (n : ℕ) :
    Subobject ((S.page (pageIndex n)).obj) :=
  kernelSubobject (S.page (pageIndex n)).d

/-- The boundary subobject on the textbook page `E_{n+1}`. -/
private abbrev pageBoundariesSubobject (S : ShiftedSpectralSequence T) (n : ℕ) :
    Subobject ((S.page (pageIndex n)).obj) :=
  imageSubobject
    (shiftedPreviousDifferential (T (pageIndex n)).functor (S.page (pageIndex n)).d)

/-- Internal recursive presentation of the eventual cycles `Z_r` inside `E₁`, together with the
canonical map from `Z_r` to the page object `E_r`. -/
private structure StageData (S : ShiftedSpectralSequence T) (n : ℕ) where
  /-- The subobject of `E₁` representing `Z_{n + 1}`. -/
  cycle : Subobject ((S.page 1).obj)
  /-- The canonical map `Z_{n + 1} ⟶ E_{n + 1}`. -/
  toPage : (cycle : A) ⟶ (S.page (pageIndex n)).obj

/-- The recursive cycle presentation underlying the filtration `Z_r ⊆ E₁`. -/
private def stageData (S : ShiftedSpectralSequence T) : (n : ℕ) → StageData S n
  | 0 =>
      { cycle := ⊤
        toPage := (⊤ : Subobject ((S.page 1).obj)).arrow }
  | n + 1 =>
      let prev := stageData S n
      let pulledCycles : Subobject (prev.cycle : A) :=
        (Subobject.pullback prev.toPage).obj (pageCyclesSubobject S n)
      let nextCycle : Subobject ((S.page 1).obj) :=
        (Subobject.map prev.cycle.arrow).obj pulledCycles
      { cycle := nextCycle
        toPage :=
          (Subobject.isoOfEq _ _
            (by
              simpa [Subobject.mk_arrow] using
                (Subobject.map_mk pulledCycles.arrow prev.cycle.arrow))).hom ≫
            (Subobject.underlyingIso (pulledCycles.arrow ≫ prev.cycle.arrow)).hom ≫
            Subobject.pullbackπ prev.toPage (pageCyclesSubobject S n) ≫
              (S.page (pageIndex n)).kernelSubobjectToCycles ≫
                (S.page (pageIndex n)).shortComplex.homologyπ ≫
                  (S.iso (pageIndex n)).hom }

/-- The subobject `Z_{n + 1} ⊆ E₁` in the internal recursive presentation. -/
private abbrev stageCycle (S : ShiftedSpectralSequence T) (n : ℕ) :
    Subobject ((S.page 1).obj) :=
  (stageData S n).cycle

/-- The canonical map `Z_{n + 1} ⟶ E_{n + 1}` in the internal recursive presentation. -/
private abbrev stageToPage (S : ShiftedSpectralSequence T) (n : ℕ) :
    (stageCycle S n : A) ⟶ (S.page (pageIndex n)).obj :=
  (stageData S n).toPage

/-- The recursively defined subobject `Z_r ⊆ E₁` attached to a shifted spectral sequence. -/
def cycle (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject ((S.page 1).obj) :=
  stageCycle S r.natPred

/-- The recursively defined subobject `B_r ⊆ E₁` attached to a shifted spectral sequence. -/
private def boundaryAux (S : ShiftedSpectralSequence T) : ℕ → Subobject ((S.page 1).obj)
  | 0 => ⊥
  | n + 1 =>
      let prevCycle := stageCycle S n
      let pulledBoundaries : Subobject (prevCycle : A) :=
        (Subobject.pullback (stageToPage S n)).obj (pageBoundariesSubobject S n)
      (Subobject.map prevCycle.arrow).obj pulledBoundaries

/-- The recursively defined subobject `B_r ⊆ E₁` attached to a shifted spectral sequence. -/
def boundary (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject ((S.page 1).obj) :=
  S.boundaryAux r.natPred

/-- The recursively defined boundaries form subobjects of the corresponding cycles. -/
theorem boundary_le_cycle (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.boundary r ≤ S.cycle r := sorry

/-- The positive page index `r.natPred + 1` is `r`. -/
private theorem pageIndex_natPred (r : ℕ+) : pageIndex r.natPred = r := by
  apply PNat.eq
  exact r.natPred_add_one

/-- The canonical map `Z_r ⟶ E_r`. -/
def cycleToPage (S : ShiftedSpectralSequence T) (r : ℕ+) :
    (S.cycle r : A) ⟶ (S.page r).obj :=
  let pageIso : (S.page (pageIndex r.natPred)).obj ≅ (S.page r).obj :=
    eqToIso (by simpa using congrArg (fun s ↦ (S.page s).obj) (pageIndex_natPred r))
  stageToPage S r.natPred ≫ pageIso.hom

/-- The recursive map `Z_r ⟶ E_r` kills the boundary subobject `B_r ⊆ Z_r`. -/
theorem boundaryToPage_zero (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject.ofLE (S.boundary r) (S.cycle r) (S.boundary_le_cycle r) ≫
      S.cycleToPage r =
    0 := sorry

/-- The canonical morphism from the quotient `Z_r / B_r` to the page object `E_r`. -/
def pageQuotientToPageObject (S : ShiftedSpectralSequence T) (r : ℕ+) :
    cokernel (Subobject.ofLE (S.boundary r) (S.cycle r) (S.boundary_le_cycle r)) ⟶
      (S.page r).obj :=
  cokernel.desc _ (S.cycleToPage r) (S.boundaryToPage_zero r)

/-- The canonical quotient map `Z_r / B_r ⟶ E_r` is an isomorphism. -/
theorem pageQuotientToPageObject_isIso (S : ShiftedSpectralSequence T) (r : ℕ+) :
    IsIso (S.pageQuotientToPageObject r) := sorry

section ShiftFunctorBridge

open ShiftedDifferentialObject

variable [HasShift A ℤ]
variable (S : ShiftedSpectralSequence (fun _ : ℕ+ ↦ (shiftFunctor A (1 : ℤ)).asEquivalence))

/-- Convert a positive page index written as an integer into the corresponding `ℕ+` index. -/
private def pageNumber (r : ℤ) (hr : 1 ≤ r) : ℕ+ :=
  ⟨Int.toNat r, by omega⟩

/-- The page-number coercion is compatible with successor. -/
private theorem pageNumber_succ (r : ℤ) (hr : 1 ≤ r) :
    pageNumber (r + 1) (by omega) = pageNumber r hr + 1 := by
  apply PNat.eq
  have hr0 : 0 ≤ r := by omega
  rw [pageNumber, pageNumber]
  simp
  omega

/-- For the fixed shift `X ↦ X⟦1⟧`, the shifted spectral-sequence presentation canonically gives a
`mathlib` spectral sequence: each page is the cochain complex of iterated shifts of the
corresponding `ShiftedDifferentialObject`, and the page-to-page isomorphism is induced from the
specified homology identification `S.iso`. -/
noncomputable def toSpectralSequence :
    SpectralSequence A (fun _ : ℤ ↦ ComplexShape.up ℤ) 1 where
  page r hr :=
    iteratedShiftPageComplex (S.page (pageNumber r hr))
  iso r r' pq hrr' hr := by
    subst hrr'
    rw [pageNumber_succ]
    simpa using
      (ShiftedDifferentialObject.iteratedShiftPageComplexHomologyIso
          (S.page (pageNumber r hr)) pq ≪≫
        (shiftFunctor A pq).mapIso (S.iso (pageNumber r hr)))

/-- On the canonical bridge, the degree-zero component of the `r`-th mathlib page is the
source-facing `E_r` object. -/
noncomputable abbrev toSpectralSequencePageZeroIso (r : ℕ+) :
    ((S.toSpectralSequence.page (r : ℤ) (by exact_mod_cast r.2)).X (0 : ℤ)) ≅ (S.page r).obj :=
  by
    simpa [toSpectralSequence, pageNumber, iteratedShiftPageComplex] using
      (shiftZero (ℤ) (S.page r).obj)

end ShiftFunctorBridge

end ShiftedSpectralSequence

end CategoryTheory
