import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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

-- Proof sketch: `cycle` is defined by one step of `stageData`; for the successor page, unfold
-- that single recursive step and rewrite the private `stageToPage` term to the public
-- `cycleToPage` by removing the tautological page-index transport.
/-- The successor cycle piece is obtained by pulling back the page-`r` cycles along
`cycleToPage : Z_r^{pq} ⟶ E_r^{pq}` and mapping the result back into `E₁^{pq}`. -/
theorem cycle_succ_eq_map_pullback_kernel
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.cycle pq (r + 1) =
      (Subobject.map (E.cycle pq r).arrow).obj
        ((Subobject.pullback (E.cycleToPage pq r)).obj
          (kernelSubobject ((E.page (r : ℤ) (by exact_mod_cast r.2)).dFrom pq))) := by
  -- TODO: unfold one step of `stageData` and transport the pullback across the equality
  -- isomorphism inside `cycleToPage`.
  sorry

-- Proof sketch: `boundary` is defined by one step of `boundaryAux`; for the successor page,
-- unfold that step and rewrite the private `stageToPage` term to the public `cycleToPage`.
/-- The successor boundary piece is obtained by pulling back the page-`r` boundaries along
`cycleToPage : Z_r^{pq} ⟶ E_r^{pq}` and mapping the result back into `E₁^{pq}`. -/
theorem boundary_succ_eq_map_pullback_image
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.boundary pq (r + 1) =
      (Subobject.map (E.cycle pq r).arrow).obj
        ((Subobject.pullback (E.cycleToPage pq r)).obj
          (imageSubobject ((E.page (r : ℤ) (by exact_mod_cast r.2)).dTo pq))) := by
  -- TODO: unfold one step of `boundaryAux` and transport the pullback across the equality
  -- isomorphism inside `cycleToPage`.
  sorry

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
