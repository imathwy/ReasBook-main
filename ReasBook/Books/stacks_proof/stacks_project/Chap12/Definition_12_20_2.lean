import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.StacksAttribute

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
@[stacks 011O]
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

/-- Helper for Chap12 Definition 12 20 2: the cycles object maps back to the kernel subobject of
the outgoing page differential. -/
private noncomputable def cyclesToKernelSubobject
    {κ' : Type*} {c' : ComplexShape κ'} (K : HomologicalComplex C c') (pq : κ') :
    K.cycles pq ⟶ (kernelSubobject (K.dFrom pq) : C) :=
  factorThruKernelSubobject (K.dFrom pq) (K.iCycles pq)
    (K.iCycles_d pq (c'.next pq))

/-- Helper for Definition 12.20.2: composing `kernelSubobjectToCycles` with the cycles inclusion
recovers the kernel-subobject arrow. -/
private theorem kernelSubobjectToCycles_iCycles
    {κ' : Type*} {c' : ComplexShape κ'} (K : HomologicalComplex C c') (pq : κ') :
    kernelSubobjectToCycles K pq ≫ K.iCycles pq = (kernelSubobject (K.dFrom pq)).arrow := by
  -- Proof comment: `kernelSubobjectToCycles` is defined by `liftCycles`, so composing with the
  -- cycles inclusion gives back the original kernel-subobject arrow.
  dsimp [kernelSubobjectToCycles]
  simpa using K.liftCycles_i (kernelSubobject (K.dFrom pq)).arrow (c'.next pq) rfl
    (kernelSubobject_arrow_comp (K.dFrom pq))

/-- Helper for Definition 12.20.2: the reverse comparison from cycles to the kernel subobject has
the expected underlying arrow into the page object. -/
private theorem cyclesToKernelSubobject_arrow
    {κ' : Type*} {c' : ComplexShape κ'} (K : HomologicalComplex C c') (pq : κ') :
    cyclesToKernelSubobject K pq ≫ (kernelSubobject (K.dFrom pq)).arrow = K.iCycles pq := by
  -- Proof comment: this is the universal-property computation for
  -- `factorThruKernelSubobject`.
  dsimp [cyclesToKernelSubobject]
  simpa using
    (factorThruKernelSubobject_comp_arrow (K.dFrom pq) (K.iCycles pq)
      (K.iCycles_d pq (c'.next pq)))

/-- Helper for Definition 12.20.2: the comparison between the kernel subobject of `dFrom pq` and
the cycles object is an isomorphism. -/
private theorem isIsoKernelSubobjectToCycles
    {κ' : Type*} {c' : ComplexShape κ'} (K : HomologicalComplex C c') (pq : κ') :
    IsIso (kernelSubobjectToCycles K pq) := by
  -- Proof comment: the two comparison maps are inverse because both become the same mono into the
  -- ambient page object after composing with the corresponding inclusion.
  refine ⟨⟨cyclesToKernelSubobject K pq, ?_, ?_⟩⟩
  · apply (cancel_mono ((kernelSubobject (K.dFrom pq)).arrow)).1
    rw [Category.assoc, cyclesToKernelSubobject_arrow, kernelSubobjectToCycles_iCycles]
    simp
  · apply (cancel_mono (K.iCycles pq)).1
    rw [Category.assoc, kernelSubobjectToCycles_iCycles, cyclesToKernelSubobject_arrow]
    simp

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
@[stacks 011O]
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
@[stacks 011O]
def boundary (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject (E⟦1, pq⟧) :=
  E.boundaryAux pq r.natPred

/-- Helper for Definition 12.20.2: the page-level boundaries lie in the page-level cycles because
the page differential squares to zero. -/
private theorem pageBoundary_le_pageCycle
    (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    E.pageBoundariesSubobject pq n ≤ E.pageCyclesSubobject pq n := by
  -- Proof comment: the incoming and outgoing page differentials compose to zero on every page.
  exact image_le_kernel _ _ ((E.pageComplex n).dTo_comp_dFrom pq)

/-- Helper for Definition 12.20.2: every recursive boundary stage is contained in the matching
recursive cycle stage. -/
private theorem boundaryAuxLeStageCycle
    (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    E.boundaryAux pq n ≤ stageCycle E pq n := by
  induction n with
  | zero =>
      -- Proof comment: the initial recursive boundary is `⊥`, so there is nothing to prove.
      simp [boundaryAux, stageCycle, stageData]
  | succ n ih =>
      -- Proof comment: one recursive step preserves containment after pulling back along the
      -- stage map and pushing forward into `E₁`.
      dsimp [boundaryAux, stageCycle, stageData]
      exact ((Subobject.map (stageCycle E pq n).arrow).monotone <|
        (Subobject.pullback (stageToPage E pq n)).monotone <|
          E.pageBoundary_le_pageCycle pq n)

/-- The recursively defined boundaries form subobjects of the corresponding cycles. -/
@[stacks 011O]
theorem boundary_le_cycle (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.boundary pq r ≤ E.cycle pq r := by
  -- Proof comment: the public statement is the stage-level containment specialized at
  -- `r.natPred`.
  simpa [boundary, cycle] using boundaryAuxLeStageCycle E pq r.natPred
/-- The positive page index `r.natPred + 1` is `r`. -/
private theorem succ_natPred_eq (r : ℕ+) : (Nat.succ r.natPred : ℤ) = (r : ℤ) := by
  -- Proof comment: this is the standard predecessor-successor normalization for positive naturals.
  exact_mod_cast (show Nat.succ r.natPred = r by
    simpa [Nat.succ_eq_add_one] using r.natPred_add_one)

/-- Helper for Definition 12.20.2: the underlying natural number of a positive page index is the
successor of its predecessor. -/
private theorem positiveNat_eq_succ_natPred (r : ℕ+) : (r : ℕ) = Nat.succ r.natPred := by
  -- Proof comment: this natural-number normalization is the one used to unfold the successor
  -- branch of the recursive stage presentation.
  simpa [Nat.succ_eq_add_one] using (PNat.natPred_add_one r).symm
/-- The canonical map `Z_r^{pq} ⟶ E_r^{pq}`. -/
@[stacks 011O]
def cycleToPage (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    (E.cycle pq r : C) ⟶ E⟦r, pq⟧ :=
  let pageIso :
      (E.pageComplex r.natPred).X pq ≅ E⟦r, pq⟧ :=
    E.pageXIsoOfEq pq (Nat.succ r.natPred : ℤ) (r : ℤ) (succ_natPred_eq r)
  stageToPage E pq r.natPred ≫ pageIso.hom

/-- Helper for Definition 12.20.2: before inserting the public `cycleToPage` transport, the
successor cycle stage is the recursive `map (pullback kernel)` construction on `stageToPage`. -/
private theorem cycleSucc_eq_map_pullbackPageCycles
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.cycle pq (r + 1) =
      (Subobject.map (E.cycle pq r).arrow).obj
        ((Subobject.pullback (stageToPage E pq r.natPred)).obj
          (E.pageCyclesSubobject pq r.natPred)) := by
  -- Proof comment: this is exactly the recursive successor clause of `stageData`, rewritten in
  -- the source-facing `cycle` notation.
  rw [cycle, PNat.add_one, Nat.natPred_succPNat]
  rw [positiveNat_eq_succ_natPred r]
  simp [cycle, stageCycle, stageData, pageCyclesSubobject]

/-- Helper for Definition 12.20.2: before inserting the public `cycleToPage` transport, the
successor boundary stage is the recursive `map (pullback image)` construction on `stageToPage`. -/
private theorem boundarySucc_eq_map_pullbackPageBoundaries
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.boundary pq (r + 1) =
      (Subobject.map (E.cycle pq r).arrow).obj
        ((Subobject.pullback (stageToPage E pq r.natPred)).obj
          (E.pageBoundariesSubobject pq r.natPred)) := by
  -- Proof comment: this is the recursive successor clause of `boundaryAux`, again rewritten into
  -- the public `boundary` and `cycle` notation.
  rw [boundary, PNat.add_one, Nat.natPred_succPNat]
  rw [positiveNat_eq_succ_natPred r]
  simp [boundaryAux, cycle, stageCycle, pageBoundariesSubobject]

/-- The successor cycle piece is obtained by pulling back the page-`r` cycles along
`cycleToPage : Z_r^{pq} ⟶ E_r^{pq}` and mapping the result back into `E₁^{pq}`. -/
@[stacks 011O]
theorem cycle_succ_eq_map_pullback_kernel
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.cycle pq (r + 1) =
      (Subobject.map (E.cycle pq r).arrow).obj
        ((Subobject.pullback (E.cycleToPage pq r)).obj
          (kernelSubobject ((E.page (r : ℤ) (by exact_mod_cast r.2)).dFrom pq))) := by
  -- Proof comment: after rewriting the tautological page-identification isomorphism inside
  -- `cycleToPage`, the public statement is the stage-level successor clause.
  let r' : ℕ+ := ⟨Nat.succ r.natPred, Nat.succ_pos _⟩
  have hr' : r' = r := PNat.eq (by simpa [r'] using r.natPred_add_one)
  simpa [r', cycleToPage, SpectralSequence.pageXIsoOfEq] using
    (hr'.symm ▸ cycleSucc_eq_map_pullbackPageCycles E pq r')
/-- The successor boundary piece is obtained by pulling back the page-`r` boundaries along
`cycleToPage : Z_r^{pq} ⟶ E_r^{pq}` and mapping the result back into `E₁^{pq}`. -/
@[stacks 011O]
theorem boundary_succ_eq_map_pullback_image
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    E.boundary pq (r + 1) =
      (Subobject.map (E.cycle pq r).arrow).obj
        ((Subobject.pullback (E.cycleToPage pq r)).obj
          (imageSubobject ((E.page (r : ℤ) (by exact_mod_cast r.2)).dTo pq))) := by
  -- Proof comment: this is the same successor normalization as for cycles, now using the
  -- page-level boundary subobject.
  let r' : ℕ+ := ⟨Nat.succ r.natPred, Nat.succ_pos _⟩
  have hr' : r' = r := PNat.eq (by simpa [r'] using r.natPred_add_one)
  simpa [r', cycleToPage, SpectralSequence.pageXIsoOfEq] using
    (hr'.symm ▸ boundarySucc_eq_map_pullbackPageBoundaries E pq r')

/-- Helper for Definition 12.20.2: precomposing a morphism by an epimorphism does not change its
image subobject in an abelian category. -/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : C} (h : X ⟶ Y) [Epi h] (f : Y ⟶ Z) :
    imageSubobject (h ≫ f) = imageSubobject f := by
  -- Proof comment: the canonical comparison from `image (h ≫ f)` to `image f` is both mono and
  -- epi, hence an isomorphism.
  let hle := imageSubobject_comp_le h f
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi h f
  haveI : IsIso (Subobject.ofLE _ _ hle) :=
    isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)

/-- Helper for Definition 12.20.2: pulling back a subobject along an epimorphism produces an
epimorphic pullback projection. -/
private theorem epi_pullbackπ_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    Epi (Subobject.pullbackπ f P) := by
  -- Proof comment: `Subobject.pullbackπ` is the first map in a pullback square, so it is epi
  -- whenever the other leg is epi in an abelian category.
  exact Abelian.epi_fst_of_isLimit P.arrow f (Subobject.isPullback f P).isLimit

/-- Helper for Definition 12.20.2: the pullback of the standard `imageToKernel` morphism is the
inclusion from the pulled image into the pulled kernel. -/
private theorem pullbackImageToKernel
    {X X' Y Z : C} (u : X ⟶ Y) (f : X' ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    Subobject.ofLE ((Subobject.pullback u).obj (imageSubobject f))
        ((Subobject.pullback u).obj (kernelSubobject g))
        ((Subobject.pullback u).monotone (image_le_kernel _ _ w)) ≫
      Subobject.pullbackπ u (kernelSubobject g) =
        Subobject.pullbackπ u (imageSubobject f) ≫ imageToKernel f g w := by
  -- Proof comment: both morphisms become the same arrow after composing with the mono
  -- `kernelSubobject g ⟶ Y`, so mono cancellation identifies them.
  apply (cancel_mono (kernelSubobject g).arrow).1
  have hker := (Subobject.isPullback u (kernelSubobject g)).w
  have himg := (Subobject.isPullback u (imageSubobject f)).w
  simpa [Category.assoc, imageToKernel_arrow, hker, himg]

/-- Helper for Definition 12.20.2: an epimorphism whose kernel is the given mono presents its
codomain as the corresponding cokernel. -/
private theorem cokernelDescIsIsoOfEpiOfKernel
    {X Y Z : C} (i : X ⟶ Y) [Mono i] (f : Y ⟶ Z) [Epi f]
    (hzero : i ≫ f = 0) (hKernel : kernelSubobject f = Subobject.mk i) :
    IsIso (cokernel.desc i f hzero) := by
  -- Proof comment: exactness identifies the kernel of `f` with the image of `i`, so the usual
  -- short exact sequence argument makes `Z` the cokernel of `i`.
  have hExact : (ShortComplex.mk i f hzero).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    calc
      imageSubobject i = Subobject.mk i := by
        simpa using (Limits.imageSubobject_mono i)
      _ = kernelSubobject f := by
        simpa using hKernel.symm
  have hShort : (ShortComplex.mk i f hzero).ShortExact := by
    exact ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  let e : cokernel i ≅ Z :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel i)
      (ShortComplex.ShortExact.gIsCokernel hShort)
  have he : e.hom = cokernel.desc i f hzero := by
    -- Proof comment: both arrows are characterized by the same composite with the epi
    -- `cokernel.π i`, so epi cancellation identifies them.
    apply (cancel_epi (cokernel.π i)).1
    simpa [e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel i)
        (ShortComplex.ShortExact.gIsCokernel hShort) WalkingParallelPair.one)
  rw [← he]
  infer_instance

/-- Helper for Definition 12.20.2: every recursive stage map onto the current page entry is an
epimorphism. -/
private theorem stageToPageEpi
    (E : SpectralSequence C c 1) (pq : κ) (n : ℕ) :
    Epi (stageToPage E pq n) := by
  induction n with
  | zero =>
      -- Proof comment: the initial stage map is the top-subobject arrow, hence an isomorphism.
      change Epi ((⊤ : Subobject (E⟦1, pq⟧)).arrow)
      infer_instance
  | succ n ih =>
      -- Proof comment: one recursive step is a composite of front isomorphisms, an epimorphic
      -- pullback projection, the kernel/cycles isomorphism, the homology projection, and the page
      -- comparison isomorphism.
      haveI := ih
      haveI :
          Epi (Subobject.pullbackπ (stageToPage E pq n) (E.pageCyclesSubobject pq n)) :=
        epi_pullbackπ_of_epi (stageToPage E pq n) (E.pageCyclesSubobject pq n)
      let pulledCycles : Subobject ((stageCycle E pq n : C)) :=
        (Subobject.pullback (stageToPage E pq n)).obj (E.pageCyclesSubobject pq n)
      let frontIso :
          ((Subobject.map (stageCycle E pq n).arrow).obj pulledCycles : C) ≅ (pulledCycles : C) :=
        (Subobject.isoOfEq _ _
          (by
            simpa [Subobject.mk_arrow] using
              (Subobject.map_mk pulledCycles.arrow (stageCycle E pq n).arrow))) ≪≫
          Subobject.underlyingIso (pulledCycles.arrow ≫ (stageCycle E pq n).arrow)
      haveI : Epi frontIso.hom := by infer_instance
      haveI : IsIso (kernelSubobjectToCycles (E.pageComplex n) pq) := by
        exact isIsoKernelSubobjectToCycles (E.pageComplex n) pq
      haveI : Epi (kernelSubobjectToCycles (E.pageComplex n) pq) := by infer_instance
      haveI : Epi ((E.pageComplex n).homologyπ pq) := by infer_instance
      haveI : Epi ((E.iso (Nat.succ n : ℤ) (Nat.succ (Nat.succ n) : ℤ) pq).hom) := by
        infer_instance
      simpa [stageToPage, stageData, pulledCycles, frontIso] using
        (show Epi
          (frontIso.hom ≫
            Subobject.pullbackπ (stageToPage E pq n) (E.pageCyclesSubobject pq n) ≫
              kernelSubobjectToCycles (E.pageComplex n) pq ≫
                (E.pageComplex n).homologyπ pq ≫
                  (E.iso (Nat.succ n : ℤ) (Nat.succ (Nat.succ n) : ℤ) pq).hom) from
          inferInstance)

/-- Helper for Definition 12.20.2: the public map `Z_r^{pq} ⟶ E_r^{pq}` is epimorphic. -/
private theorem epi_cycleToPage
    (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Epi (E.cycleToPage pq r) := by
  -- Proof comment: `cycleToPage` is `stageToPage` followed by the tautological page-index
  -- transport isomorphism.
  haveI := E.stageToPageEpi pq r.natPred
  let pageIso :
      (E.pageComplex r.natPred).X pq ≅ E⟦r, pq⟧ :=
    E.pageXIsoOfEq pq (Nat.succ r.natPred : ℤ) (r : ℤ) (succ_natPred_eq r)
  haveI : Epi pageIso.hom := by infer_instance
  change Epi (stageToPage E pq r.natPred ≫ pageIso.hom)
  infer_instance
/-- The recursive map `Z_r^{pq} ⟶ E_r^{pq}` kills the boundary subobject
`B_r^{pq} ⊆ Z_r^{pq}`. -/
@[stacks 011O]
theorem boundaryToPage_zero (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject.ofLE (E.boundary pq r) (E.cycle pq r) (E.boundary_le_cycle pq r) ≫
      E.cycleToPage pq r = 0 := sorry
/-- The canonical morphism from the quotient `Z_r^{pq} / B_r^{pq}` to the page entry
`E_r^{pq}`. -/
@[stacks 011O]
def pageQuotientToPage (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    cokernel (Subobject.ofLE (E.boundary pq r) (E.cycle pq r) (E.boundary_le_cycle pq r)) ⟶
      E⟦r, pq⟧ :=
  cokernel.desc _ (E.cycleToPage pq r) (E.boundaryToPage_zero pq r)

/-- The canonical quotient map `Z_r^{pq} / B_r^{pq} ⟶ E_r^{pq}` is an isomorphism. -/
@[stacks 011O]
theorem pageQuotientToPage_isIso (E : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    IsIso (E.pageQuotientToPage pq r) := sorry
section InfinityPage

variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasCoproducts C]
  [InitialMonoClass C]

/-- The eventual cycles subobject `Z_∞^{pq} = ⋂_r Z_r^{pq}` inside `E₁^{pq}`. -/
@[stacks 011O]
def cycleInfinity (E : SpectralSequence C c 1) (pq : κ) :
    Subobject (E⟦1, pq⟧) :=
  ⨅ r : ℕ+, E.cycle pq r

/-- The eventual boundaries subobject `B_∞^{pq} = ⋃_r B_r^{pq}` inside `E₁^{pq}`. -/
@[stacks 011O]
def boundaryInfinity (E : SpectralSequence C c 1) (pq : κ) :
    Subobject (E⟦1, pq⟧) :=
  ⨆ r : ℕ+, E.boundary pq r

-- Proof sketch: each `B_r` lies in `Z_r`; taking the supremum over the boundaries and the infimum
-- over the cycles preserves the eventual containment `B_∞ ≤ Z_∞`.
/-- The eventual boundaries are contained in the eventual cycles. -/
@[stacks 011O]
theorem boundaryInfinity_le_cycleInfinity (E : SpectralSequence C c 1) (pq : κ) :
    E.boundaryInfinity pq ≤ E.cycleInfinity pq := sorry
/-- Definition 12.20.2: if the eventual intersection `Z_∞ = ⋂_r Z_r` and eventual union
`B_∞ = ⋃_r B_r` exist as subobjects of `E₁`, then each entry `E_∞^{pq}` is the quotient
`Z_∞^{pq} / B_∞^{pq}`. -/
@[stacks 011O]
def infinityPage (E : SpectralSequence C c 1) (pq : κ) : C :=
  cokernel
    (Subobject.ofLE
      (E.boundaryInfinity pq)
      (E.cycleInfinity pq)
      (E.boundaryInfinity_le_cycleInfinity pq))

-- Proof sketch: unfold `infinityPage`; it is defined to be the cokernel of the inclusion
-- `B_∞ ↪ Z_∞` supplied by `boundaryInfinity_le_cycleInfinity`.
/-- The limit object `E_∞` is the cokernel of the inclusion `B_∞ ⟶ Z_∞`. -/
@[stacks 011O]
theorem infinityPage_def (E : SpectralSequence C c 1) (pq : κ) :
    E.infinityPage pq =
      cokernel
        (Subobject.ofLE
          (E.boundaryInfinity pq)
          (E.cycleInfinity pq)
          (E.boundaryInfinity_le_cycleInfinity pq)) := sorry
end InfinityPage

/-- The spectral sequence degenerates at `E_r` if all differentials `d_r, d_{r+1}, ...` vanish. -/
@[stacks 011O]
def degeneratesAt (E : SpectralSequence C c 1) (r : ℕ+) : Prop :=
  ∀ (pq : κ) (s : ℕ+), r ≤ s →
    (E.positivePage s).dFrom pq = 0

end SpectralSequence
end CategoryTheory
