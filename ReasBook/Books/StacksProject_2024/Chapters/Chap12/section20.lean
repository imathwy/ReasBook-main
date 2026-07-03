import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_20_1 (from Chap12) -/
universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Domain-style sampling for Definition 12.20.1:
- primary domain: spectral sequences in an abelian category, specialized here to one-object page
  complexes;
- sampled core/canonical declarations:
  `CategoryTheory.SpectralSequence`,
  `CategoryTheory.SpectralSequence.Hom`,
  `SpectralSequence.pageFunctor`,
  `SpectralSequence.pageHomologyNatIso`,
  `ExactCouple.associatedSpectralSequence`;
- best owner abstraction: the category
  `SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1`;
- primitive data:
  object level: the pages `E.page r` and the homology-to-next-page isomorphisms
    `E.iso r r' PUnit.unit`;
  morphism level: the pagewise maps of `CategoryTheory.SpectralSequence.Hom` commuting with those
    homology identifications;
- derived API: the textbook page objects and differentials obtained by evaluating each page at
  `PUnit.unit`, the transition `H(E_r) ≅ E_{r+1}` recovered from
  `SpectralSequence.pageHomologyNatIso`, and the arrow notation supplied by the canonical category
  structure;
- source/core/bridge triage:
  `source-facing`: a spectral sequence whose pages are one-object homological complexes, together
    with morphisms of such spectral sequences;
  `core/canonical`: `SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1`;
  `bridge/view`: evaluation at `PUnit.unit` and the recalled page/homology functorial API.

No local wrapper is needed here: the textbook definition is exactly this specialization of the
mathlib owner object. -/
/- Definition 12.20.1 is a core/canonical recall item in the spectral-sequence domain: a spectral
sequence in an abelian category with one-object pages is exactly the owner type
`SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1`, and a morphism of such spectral
sequences is exactly the owner structure `CategoryTheory.SpectralSequence.Hom`. -/
#check (SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1)

/- Companion recall: the canonical morphism owner for these spectral sequences is the pagewise
homological-complex map structure `CategoryTheory.SpectralSequence.Hom`. -/
recall CategoryTheory.SpectralSequence.Hom

variable (E E' : SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1)

/- Companion recall: these objects already form the canonical category whose arrows are the
recalled morphisms above. -/
#check (inferInstance : Category (SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1))

/- Companion recall: the textbook morphisms are therefore the ordinary arrows `E ⟶ E'` in that
canonical category. -/
#check (E ⟶ E')

/- Companion recall: the page family is accessed through the canonical owner functor. -/
recall SpectralSequence.pageFunctor

/- Companion recall: the identification `H(E_r) ≅ E_{r+1}` is the canonical owner natural
isomorphism; specializing at `PUnit.unit` recovers the textbook transition. -/
recall SpectralSequence.pageHomologyNatIso

end CategoryTheory

/-! ### Definition_12_20_2 (from Chap12) -/
/-
Domain-style sampling for Definition 12.20.2:
- primary domain: spectral sequences in an abelian category;
- sampled core/canonical declarations:
  `CategoryTheory.SpectralSequence`,
  `SpectralSequence.pageXIsoOfEq`,
  `ExactCouple.associatedSpectralSequence`,
  `ShiftedSpectralSequence.toSpectralSequence`;
- best owner abstraction: `SpectralSequence C c 1`;
- primitive data: the owner pages `E.page r` and the owner isomorphisms identifying the homology
  of page `r` with page `r + 1`;
- source-facing derived API in this file: the recursive cycle pieces `Z_r`, boundary pieces `B_r`,
  their limiting objects `Z_∞`, `B_∞`, the quotient `E_∞`, and the degeneration predicate;
- source/core/bridge triage:
  `source-facing`: `cycle`, `boundary`, `cycleInfinity`, `boundaryInfinity`, `infinityPage`,
  `degeneratesAt`;
  `core/canonical`: `SpectralSequence C c 1`;
  `bridge/view`: later chapter files that specialize these owner-derived constructions to exact
  couples, differential objects, or cohomological spectral sequences.

The source-facing recursive objects are kept public, but the internal recursion is expressed
directly through the stage subobjects and their canonical maps rather than through an internal
wrapper package.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

/-- The `n`-th zero-based page, so `pageComplex E n` is the textbook page `E_{n+1}`. -/
private abbrev pageComplex (E : SpectralSequence C c 1) (n : ℕ) :
    HomologicalComplex C (c (Nat.succ n : ℤ)) :=
  E.page (Nat.succ n : ℤ)

/-- The textbook page `E_r` for a positive page index `r`. -/
private abbrev positivePage (E : SpectralSequence C c 1) (r : ℕ+) :
    HomologicalComplex C (c (r : ℤ)) :=
  E.page (r : ℤ) (by exact_mod_cast r.2)

/-- The entry `E_r^{pq}` on a positive page. -/
abbrev pageObject (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) : C :=
  (E.positivePage r).X pq

/-- Textbook notation for the page entry `E_r^{pq}`. -/
scoped notation:max E "⟦" r "," pq "⟧" => SpectralSequence.pageObject E pq r

open scoped SpectralSequence

/-- The cycles subobject at the entry `pq` on the `r`-th page. -/
private abbrev pageCyclesSubobject
    (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    Subobject ((E.pageComplex n).X pq) :=
  kernelSubobject ((E.pageComplex n).dFrom pq)

/-- The boundaries subobject at the entry `pq` on the `r`-th page. -/
private abbrev pageBoundariesSubobject
    (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    Subobject ((E.pageComplex n).X pq) :=
  imageSubobject ((E.pageComplex n).dTo pq)

/-- The canonical morphism from the kernel subobject of `dFrom pq` to the cycles object. -/
private noncomputable def kernelSubobjectToCycles
    {κ' : Type*} {c' : ComplexShape κ'} (K : HomologicalComplex C c') (pq : κ') :
    (kernelSubobject (K.dFrom pq) : C) ⟶ K.cycles pq :=
  K.liftCycles (kernelSubobject (K.dFrom pq)).arrow (c'.next pq) rfl
    (kernelSubobject_arrow_comp (K.dFrom pq))

/-- Internal recursive presentation of the eventual cycles `Z_r^{pq}` inside `E₁^{pq}`, together
with the canonical map from `Z_r^{pq}` to the page entry `E_r^{pq}`. -/
private structure StageData (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) where
  /-- The subobject of `E₁^{pq}` representing `Z_{n + 1}^{pq}`. -/
  cycle : Subobject (E⟦1, pq⟧)
  /-- The canonical map `Z_{n + 1}^{pq} ⟶ E_{n + 1}^{pq}`. -/
  toPage : (cycle : C) ⟶ (E.pageComplex n).X pq

/-- The recursive cycle presentation underlying the filtration `Z_r^{pq} ⊆ E₁^{pq}`. -/
private def stageData (E : SpectralSequence C c 1) (pq : κ) :
    (n : ℕ) → StageData E pq n
  | 0 =>
      { cycle := ⊤
        toPage := (⊤ : Subobject (E⟦1, pq⟧)).arrow }
  | n + 1 =>
      let prev := stageData E pq n
      let pulledCycles : Subobject (prev.cycle : C) :=
        (Subobject.pullback prev.toPage).obj (E.pageCyclesSubobject pq n)
      let nextCycle : Subobject (E⟦1, pq⟧) :=
        (Subobject.map prev.cycle.arrow).obj pulledCycles
      { cycle := nextCycle
        toPage :=
          (Subobject.isoOfEq _ _
            (by
              simpa [Subobject.mk_arrow] using
                (Subobject.map_mk pulledCycles.arrow prev.cycle.arrow))).hom ≫
            (Subobject.underlyingIso (pulledCycles.arrow ≫ prev.cycle.arrow)).hom ≫
            Subobject.pullbackπ prev.toPage (E.pageCyclesSubobject pq n) ≫
              kernelSubobjectToCycles (E.pageComplex n) pq ≫
                (E.pageComplex n).homologyπ pq ≫
                  (E.iso (Nat.succ n : ℤ) (Nat.succ (Nat.succ n) : ℤ) pq).hom }

/-- The subobject `Z_{n + 1}^{pq} ⊆ E₁^{pq}` in the internal recursive presentation. -/
private abbrev stageCycle (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    Subobject (E⟦1, pq⟧) :=
  (stageData E pq n).cycle

/-- The canonical map `Z_{n + 1}^{pq} ⟶ E_{n + 1}^{pq}` in the internal recursive presentation. -/
private abbrev stageToPage (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    (stageCycle E pq n : C) ⟶ (E.pageComplex n).X pq :=
  (stageData E pq n).toPage

/-- The recursively defined subobject `Z_r^{pq} ⊆ E₁^{pq}` attached to a spectral sequence. -/
def cycle (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject (E⟦1, pq⟧) :=
  stageCycle E pq r.natPred

/-- The recursively defined subobject `B_r^{pq} ⊆ E₁^{pq}` attached to a spectral sequence. -/
private def boundaryAux (E : SpectralSequence C c 1) (pq : κ) :
    ℕ → Subobject (E⟦1, pq⟧)
  | 0 => ⊥
  | n + 1 =>
      let prevCycle := stageCycle E pq n
      let pulledBoundaries : Subobject (prevCycle : C) :=
        (Subobject.pullback (stageToPage E pq n)).obj (E.pageBoundariesSubobject pq n)
      (Subobject.map prevCycle.arrow).obj pulledBoundaries

/-- The recursively defined subobject `B_r^{pq} ⊆ E₁^{pq}` attached to a spectral sequence. -/
def boundary (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject (E⟦1, pq⟧) :=
  E.boundaryAux pq r.natPred

-- Proof sketch: for each page, `im(d_r)` is contained in `ker(d_r)` because `d_r ≫ d_r = 0`;
-- pulling back along the recursive map `Z_r ⟶ E_r` and then mapping into `E_1` preserves that
-- containment.
/-- The recursively defined boundaries form subobjects of the corresponding cycles. -/
theorem boundary_le_cycle (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.boundary pq r ≤ E.cycle pq r := sorry

/-- The positive page index `r.natPred + 1` is `r`. -/
private theorem succ_natPred_eq (r : ℕ+) : (Nat.succ r.natPred : ℤ) = (r : ℤ) := by
  exact_mod_cast r.natPred_add_one

/-- The canonical map `Z_r^{pq} ⟶ E_r^{pq}`. -/
def cycleToPage (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.cycle pq r : C) ⟶ E⟦r, pq⟧ :=
  let pageIso :
      (E.pageComplex r.natPred).X pq ≅ E⟦r, pq⟧ :=
    E.pageXIsoOfEq pq (Nat.succ r.natPred : ℤ) (r : ℤ) (succ_natPred_eq r)
  stageToPage E pq r.natPred ≫ pageIso.hom

-- Proof sketch: the recursive map `Z_r ⟶ E_r` identifies `B_r` with the pullback of
-- `im(d_r) ⊆ E_r` and `Z_r` with the pullback of `ker(d_r) ⊆ E_r`; the homology quotient
-- `ker(d_r) / im(d_r)` is the next page, and the spectral-sequence structure identifies that
-- homology with `E_{r+1}`.
/-- The recursive map `Z_r^{pq} ⟶ E_r^{pq}` kills the boundary subobject
`B_r^{pq} ⊆ Z_r^{pq}`. -/
theorem boundaryToPage_zero (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject.ofLE (E.boundary pq r) (E.cycle pq r) (E.boundary_le_cycle pq r) ≫
      E.cycleToPage pq r = 0 := sorry

/-- The canonical morphism from the quotient `Z_r^{pq} / B_r^{pq}` to the page entry
`E_r^{pq}`. -/
def pageQuotientToPage (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    cokernel (Subobject.ofLE (E.boundary pq r) (E.cycle pq r) (E.boundary_le_cycle pq r)) ⟶
      E⟦r, pq⟧ :=
  cokernel.desc _ (E.cycleToPage pq r) (E.boundaryToPage_zero pq r)

-- Proof sketch: the recursive presentation of `Z_r` and `B_r` matches the usual cycles and
-- boundaries on page `E_r`; the quotient map above is therefore the canonical identification of
-- `Z_r / B_r` with that page.
/-- The canonical quotient map `Z_r^{pq} / B_r^{pq} ⟶ E_r^{pq}` is an isomorphism. -/
theorem pageQuotientToPage_isIso (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    IsIso (E.pageQuotientToPage pq r) := sorry

section InfinityPage

variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasCoproducts C]
  [InitialMonoClass C]

/-- The eventual cycles subobject `Z_∞^{pq} = ⋂_r Z_r^{pq}` inside `E₁^{pq}`. -/
def cycleInfinity (E : SpectralSequence C c 1) (pq : κ) :
    Subobject (E⟦1, pq⟧) :=
  ⨅ r : ℕ+, E.cycle pq r

/-- The eventual boundaries subobject `B_∞^{pq} = ⋃_r B_r^{pq}` inside `E₁^{pq}`. -/
def boundaryInfinity (E : SpectralSequence C c 1) (pq : κ) :
    Subobject (E⟦1, pq⟧) :=
  ⨆ r : ℕ+, E.boundary pq r

-- Proof sketch: each `B_r` lies in `Z_r`; taking the supremum over the boundaries and the infimum
-- over the cycles preserves the eventual containment `B_∞ ≤ Z_∞`.
/-- The eventual boundaries are contained in the eventual cycles. -/
theorem boundaryInfinity_le_cycleInfinity (E : SpectralSequence C c 1) (pq : κ) :
    E.boundaryInfinity pq ≤ E.cycleInfinity pq := sorry

/-- Definition 12.20.2: if the eventual intersection `Z_∞ = ⋂_r Z_r` and eventual union
`B_∞ = ⋃_r B_r` exist as subobjects of `E₁`, then each entry `E_∞^{pq}` is the quotient
`Z_∞^{pq} / B_∞^{pq}`. -/
def infinityPage (E : SpectralSequence C c 1) (pq : κ) : C :=
  cokernel
    (Subobject.ofLE
      (E.boundaryInfinity pq)
      (E.cycleInfinity pq)
      (E.boundaryInfinity_le_cycleInfinity pq))

-- Proof sketch: unfold `infinityPage`; it is defined to be the cokernel of the inclusion
-- `B_∞ ↪ Z_∞` supplied by `boundaryInfinity_le_cycleInfinity`.
/-- The limit object `E_∞` is the cokernel of the inclusion `B_∞ ⟶ Z_∞`. -/
theorem infinityPage_def (E : SpectralSequence C c 1) (pq : κ) :
    E.infinityPage pq =
      cokernel
        (Subobject.ofLE
          (E.boundaryInfinity pq)
          (E.cycleInfinity pq)
          (E.boundaryInfinity_le_cycleInfinity pq)) :=
  rfl

end InfinityPage

/-- The spectral sequence degenerates at `E_r` if all differentials `d_r, d_{r+1}, ...` vanish. -/
def degeneratesAt (E : SpectralSequence C c 1) (r : ℕ+) : Prop :=
  ∀ (pq : κ) (s : ℕ+), r ≤ s →
    (E.positivePage s).dFrom pq = 0

end SpectralSequence
end CategoryTheory

/-! ### Remark_12_20_3_Variant (from Chap12) -/
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
