import Mathlib
import stacks_proof.stacks_project.Chap12.Aux_12_20_3_1

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- For Remark 12.20.3 (Variant): a shifted spectral sequence relative to translation
autoequivalences `T_r` on an abelian category consists of pages `E_r`, differentials
`d_r : E_r ⟶ T_r(E_r)` with `T_r(d_r) ∘ d_r = 0`, and identifications of `E_{r+1}` with the
homology `Ker(d_r) / Im(T_r⁻¹ d_r)` of the induced short complex
`T_r⁻¹ E_r ⟶ E_r ⟶ T_r E_r`. -/
@[stacks 0AMI]
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

/-- Helper for Remark 12.20.3 (Variant): the page-level boundary subobject lies in the page-level
cycle subobject because the shifted previous differential composes with `d` to zero. -/
private theorem pageBoundary_le_pageCycle (S : ShiftedSpectralSequence T) (n : ℕ) :
    pageBoundariesSubobject S n ≤ pageCyclesSubobject S n := by
  -- Proof comment: the incoming shifted differential squares to zero with the outgoing
  -- differential on the same page, so its image factors through the kernel.
  exact image_le_kernel _ _
    (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
      (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared)

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

/-- Helper for Remark 12.20.3 (Variant): at each recursive stage, the pulled-back page boundaries
remain contained in the pulled-back page cycles. -/
private theorem boundaryAuxLeStageCycle
    (S : ShiftedSpectralSequence T) (n : ℕ) :
    S.boundaryAux n ≤ stageCycle S n := by
  induction n with
  | zero =>
      -- Proof comment: the initial recursive boundary is `⊥`, so there is nothing to prove.
      simp [boundaryAux, stageCycle, stageData]
  | succ n ih =>
      -- Proof comment: one recursive step preserves containment after pulling back along the stage
      -- map and pushing forward into `E₁`.
      dsimp [boundaryAux, stageCycle, stageData]
      exact ((Subobject.map (stageCycle S n).arrow).monotone <|
        (Subobject.pullback (stageToPage S n)).monotone <|
          S.pageBoundary_le_pageCycle n)

/-- The recursively defined boundaries form subobjects of the corresponding cycles. -/
theorem boundary_le_cycle (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.boundary r ≤ S.cycle r := by
  -- Proof comment: the public statement is exactly the stage-level containment specialized at
  -- `r.natPred`.
  simpa [boundary, cycle] using boundaryAuxLeStageCycle S r.natPred

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

/-- Helper for Remark 12.20.3 (Variant): the canonical comparison from the kernel subobject of a
shifted differential to the cycles object has the expected underlying arrow into the page object. -/
private theorem kernelSubobjectToCycles_iCycles
    {R : A ⥤ A} [Functor.IsEquivalence R] (X : ShiftedDifferentialObject R) :
    X.kernelSubobjectToCycles ≫ X.shortComplex.iCycles = (kernelSubobject X.d).arrow := by
  -- Proof comment: `kernelSubobjectToCycles` is defined by `liftCycles`, so composing with the
  -- cycles inclusion recovers the original kernel-subobject arrow.
  dsimp [ShiftedDifferentialObject.kernelSubobjectToCycles]
  simpa using X.shortComplex.liftCycles_i (kernelSubobject X.d).arrow
    (kernelSubobject_arrow_comp X.d)

/-- Helper for Remark 12.20.3 (Variant): the cycles object maps back to the kernel subobject of
the outgoing shifted differential. -/
private noncomputable def cyclesToKernelSubobject
    {R : A ⥤ A} [Functor.IsEquivalence R] (X : ShiftedDifferentialObject R) :
    X.shortComplex.cycles ⟶ (kernelSubobject X.d : A) :=
  factorThruKernelSubobject X.d X.shortComplex.iCycles X.shortComplex.iCycles_g

/-- Helper for Remark 12.20.3 (Variant): the reverse comparison from cycles to the kernel
subobject again has the expected underlying arrow into the page object. -/
private theorem cyclesToKernelSubobject_arrow
    {R : A ⥤ A} [Functor.IsEquivalence R] (X : ShiftedDifferentialObject R) :
    cyclesToKernelSubobject X ≫ (kernelSubobject X.d).arrow = X.shortComplex.iCycles := by
  -- Proof comment: this is the universal-property computation for
  -- `factorThruKernelSubobject`.
  dsimp [cyclesToKernelSubobject]
  simpa using
    (factorThruKernelSubobject_comp_arrow X.d X.shortComplex.iCycles X.shortComplex.iCycles_g)

/-- Helper for Remark 12.20.3 (Variant): the comparison between the kernel subobject of `d` and
the cycles object is an isomorphism. -/
private theorem isIso_kernelSubobjectToCycles
    {R : A ⥤ A} [Functor.IsEquivalence R] (X : ShiftedDifferentialObject R) :
    IsIso X.kernelSubobjectToCycles := by
  -- Proof comment: the two comparison maps are inverse because both become the same mono into the
  -- ambient page object after composing with the corresponding inclusion.
  refine ⟨⟨cyclesToKernelSubobject X, ?_, ?_⟩⟩
  · apply (cancel_mono ((kernelSubobject X.d).arrow)).1
    rw [Category.assoc, cyclesToKernelSubobject_arrow, kernelSubobjectToCycles_iCycles]
    simp
  · apply (cancel_mono X.shortComplex.iCycles).1
    rw [Category.assoc, kernelSubobjectToCycles_iCycles, cyclesToKernelSubobject_arrow]
    simp

/-- Helper for Remark 12.20.3 (Variant): before inserting the public `cycleToPage` transport, the
successor cycle stage is the recursive `map (pullback kernel)` construction on `stageToPage`. -/
private theorem cycleSucc_eq_map_pullbackPageCycles
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.cycle (r + 1) =
      (Subobject.map (S.cycle r).arrow).obj
        ((Subobject.pullback (stageToPage S r.natPred)).obj
          (pageCyclesSubobject S r.natPred)) := by
  -- Proof comment: this is exactly the recursive successor clause of `stageData`, rewritten in the
  -- source-facing `cycle` notation.
  rw [cycle, PNat.add_one, Nat.natPred_succPNat]
  rw [show (r : ℕ) = Nat.succ r.natPred by
    simpa using (PNat.natPred_add_one r).symm]
  simp [cycle, stageCycle, stageData, pageCyclesSubobject]

/-- Helper for Remark 12.20.3 (Variant): before inserting the public `cycleToPage` transport, the
successor boundary stage is the recursive `map (pullback image)` construction on `stageToPage`. -/
private theorem boundarySucc_eq_map_pullbackPageBoundaries
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    S.boundary (r + 1) =
      (Subobject.map (S.cycle r).arrow).obj
        ((Subobject.pullback (stageToPage S r.natPred)).obj
          (pageBoundariesSubobject S r.natPred)) := by
  -- Proof comment: this is the recursive successor clause of `boundaryAux`, again rewritten into
  -- the public `boundary` and `cycle` notation.
  rw [boundary, PNat.add_one, Nat.natPred_succPNat]
  rw [show (r : ℕ) = Nat.succ r.natPred by
    simpa using (PNat.natPred_add_one r).symm]
  simp [cycle, boundaryAux, stageCycle, pageBoundariesSubobject]

/-- Helper for Remark 12.20.3 (Variant): the kernel of a composite is the pullback of the later
kernel along the earlier map. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  -- Proof comment: factoring through the pullback is exactly the same as factoring the composite
  -- through the kernel of `g`.
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback f).obj (kernelSubobject g)).factorThru
        (kernelSubobject (f ≫ g)).arrow ?_)
      ?_
    · exact (pullback_factors_iff (f := f) (kernelSubobject g)
        (kernelSubobject (f ≫ g)).arrow).2 <| by
          rw [kernelSubobject_factors_iff, Category.assoc]
          exact kernelSubobject_arrow_comp (f ≫ g)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback f (kernelSubobject g)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Remark 12.20.3 (Variant): composing the canonical map into the kernel subobject
with the kernel-to-cycles comparison recovers the standard `toCycles` map. -/
private theorem factorThruKernelSubobject_kernelSubobjectToCycles_eq_toCycles
    (S : ShiftedSpectralSequence T) (n : ℕ) :
    factorThruKernelSubobject
        (S.page (pageIndex n)).d
        (shiftedPreviousDifferential (T (pageIndex n)).functor (S.page (pageIndex n)).d)
        (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
          (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared) ≫
      (S.page (pageIndex n)).kernelSubobjectToCycles =
        (S.page (pageIndex n)).shortComplex.toCycles := by
  -- Proof comment: after composing both candidates with the cycles inclusion, they become the same
  -- map from the shifted previous page into the current page object.
  apply (cancel_mono (S.page (pageIndex n)).shortComplex.iCycles).1
  rw [Category.assoc, kernelSubobjectToCycles_iCycles,
    (S.page (pageIndex n)).shortComplex.toCycles_i]
  simp

/-- Helper for Remark 12.20.3 (Variant): after precomposing by the canonical map onto the image
of the incoming shifted differential, the image-to-kernel comparison recovers the standard map to
cycles. -/
private theorem factorThruImageSubobject_imageToKernel_kernelSubobjectToCycles_eq_toCycles
    (S : ShiftedSpectralSequence T) (n : ℕ) :
    factorThruImageSubobject
        (shiftedPreviousDifferential (T (pageIndex n)).functor (S.page (pageIndex n)).d) ≫
      imageToKernel
          (shiftedPreviousDifferential (T (pageIndex n)).functor (S.page (pageIndex n)).d)
          (S.page (pageIndex n)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
            (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared) ≫
      (S.page (pageIndex n)).kernelSubobjectToCycles =
      (S.page (pageIndex n)).shortComplex.toCycles := by
  -- Proof comment: the image factorization and the kernel factorization of the incoming
  -- differential coincide, and the latter is exactly the canonical map into cycles.
  let prevDiff :=
    shiftedPreviousDifferential (T (pageIndex n)).functor (S.page (pageIndex n)).d
  calc
    factorThruImageSubobject prevDiff ≫
        imageToKernel prevDiff (S.page (pageIndex n)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
            (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared) ≫
        (S.page (pageIndex n)).kernelSubobjectToCycles =
      factorThruKernelSubobject (S.page (pageIndex n)).d prevDiff
          (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
            (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared) ≫
        (S.page (pageIndex n)).kernelSubobjectToCycles := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ (S.page (pageIndex n)).kernelSubobjectToCycles)
          (factorThruImageSubobject_comp_imageToKernel
            (f := prevDiff)
            (g := (S.page (pageIndex n)).d)
            (w := shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
              (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared))
    _ = (S.page (pageIndex n)).shortComplex.toCycles := by
      exact S.factorThruKernelSubobject_kernelSubobjectToCycles_eq_toCycles n

/-- Helper for Remark 12.20.3 (Variant): on any shifted page, the image-to-kernel comparison for
the incoming differential is killed by the homology projection. -/
private theorem imageToKernel_kernelSubobjectToCycles_homologyπ_zero
    (S : ShiftedSpectralSequence T) (n : ℕ) :
    imageToKernel
        (shiftedPreviousDifferential (T (pageIndex n)).functor (S.page (pageIndex n)).d)
        (S.page (pageIndex n)).d
        (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
          (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared) ≫
      (S.page (pageIndex n)).kernelSubobjectToCycles ≫
        (S.page (pageIndex n)).shortComplex.homologyπ = 0 := by
  -- Proof comment: precompose with the canonical epimorphism onto the image subobject, identify
  -- the resulting composite with `toCycles`, and cancel the canonical epimorphism onto the image.
  let prevDiff :=
    shiftedPreviousDifferential (T (pageIndex n)).functor (S.page (pageIndex n)).d
  apply (cancel_epi (factorThruImageSubobject prevDiff)).1
  calc
    factorThruImageSubobject prevDiff ≫
        imageToKernel prevDiff (S.page (pageIndex n)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
            (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared) ≫
        (S.page (pageIndex n)).kernelSubobjectToCycles ≫
        (S.page (pageIndex n)).shortComplex.homologyπ =
      (factorThruImageSubobject prevDiff ≫
          imageToKernel prevDiff (S.page (pageIndex n)).d
            (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
              (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared) ≫
          (S.page (pageIndex n)).kernelSubobjectToCycles) ≫
        (S.page (pageIndex n)).shortComplex.homologyπ := by
          simp [Category.assoc]
    _ = (S.page (pageIndex n)).shortComplex.toCycles ≫
          (S.page (pageIndex n)).shortComplex.homologyπ := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ (S.page (pageIndex n)).shortComplex.homologyπ)
              (S.factorThruImageSubobject_imageToKernel_kernelSubobjectToCycles_eq_toCycles n)
    _ = 0 := by
          simpa using (S.page (pageIndex n)).shortComplex.toCycles_comp_homologyπ
    _ = factorThruImageSubobject prevDiff ≫ 0 := by
          simp

/-- Helper for Remark 12.20.3 (Variant): pulling back the page image-to-kernel comparison along
the recursive stage map matches the inclusion from the pulled image into the pulled kernel. -/
private theorem pullbackImageToKernel
    {X X' Y Z : A} (u : X ⟶ Y) (f : X' ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
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

/-- Helper for Remark 12.20.3 (Variant): precomposing a morphism by an epimorphism does not
change its image subobject in an abelian category. -/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : A} (h : X ⟶ Y) [Epi h] (f : Y ⟶ Z) :
    imageSubobject (h ≫ f) = imageSubobject f := by
  -- Proof comment: the canonical comparison from `image (h ≫ f)` to `image f` is epi because `h`
  -- is epi, and it is always mono, hence an isomorphism.
  let hle := imageSubobject_comp_le h f
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi h f
  haveI : IsIso (Subobject.ofLE _ _ hle) :=
    isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)

/-- Helper for Remark 12.20.3 (Variant): pulling back a subobject along an epimorphism produces
an epimorphic pullback projection. -/
private theorem epi_pullbackπ_of_epi {X Y : A} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    Epi (Subobject.pullbackπ f P) := by
  -- Proof comment: `Subobject.pullbackπ` is the first map in the defining pullback square, and in
  -- an abelian category that first projection is epi whenever the other leg is epi.
  exact Abelian.epi_fst_of_isLimit P.arrow f (Subobject.isPullback f P).isLimit

/-- Helper for Remark 12.20.3 (Variant): an epimorphism whose kernel is the given mono presents
its codomain as the corresponding cokernel. -/
private theorem cokernelDescIsIsoOfEpiOfKernel
    {X Y Z : A} (i : X ⟶ Y) [Mono i] (f : Y ⟶ Z) [Epi f]
    (hzero : i ≫ f = 0) (hKernel : kernelSubobject f = Subobject.mk i) :
    IsIso (cokernel.desc i f hzero) := by
  -- Proof comment: in an abelian category, exactness is equality of image and kernel; once that
  -- is recorded, the short exact row gives the desired cokernel comparison.
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

/-- Helper for Remark 12.20.3 (Variant): every recursive stage map onto the current page is an
epimorphism. -/
private theorem stageToPageEpi
    (S : ShiftedSpectralSequence T) (n : ℕ) :
    Epi (stageToPage S n) := by
  induction n with
  | zero =>
      -- Proof comment: the initial stage map is the top-subobject arrow, hence an isomorphism.
      change Epi ((⊤ : Subobject ((S.page 1).obj)).arrow)
      infer_instance
  | succ n ih =>
      -- Proof comment: one recursive step is a composite of front isomorphisms, the epimorphic
      -- pullback projection, the cycles/kernel isomorphism, the homology projection, and the final
      -- page comparison isomorphism.
      haveI := ih
      haveI :
          Epi (Subobject.pullbackπ (stageToPage S n) (pageCyclesSubobject S n)) :=
        Abelian.epi_fst_of_isLimit (pageCyclesSubobject S n).arrow (stageToPage S n)
          (Subobject.isPullback (stageToPage S n) (pageCyclesSubobject S n)).isLimit
      let pulledCycles : Subobject ((stageCycle S n : A)) :=
        (Subobject.pullback (stageToPage S n)).obj (pageCyclesSubobject S n)
      let frontIso :
          ((Subobject.map (stageCycle S n).arrow).obj pulledCycles : A) ≅ (pulledCycles : A) :=
        (Subobject.isoOfEq _ _
          (by
            simpa [Subobject.mk_arrow] using
              (Subobject.map_mk pulledCycles.arrow (stageCycle S n).arrow))) ≪≫
          Subobject.underlyingIso (pulledCycles.arrow ≫ (stageCycle S n).arrow)
      haveI : Epi frontIso.hom := by infer_instance
      haveI : IsIso ((S.page (pageIndex n)).kernelSubobjectToCycles) := by
        exact isIso_kernelSubobjectToCycles (S.page (pageIndex n))
      haveI : Epi ((S.page (pageIndex n)).kernelSubobjectToCycles) := by infer_instance
      haveI : Epi ((S.page (pageIndex n)).shortComplex.homologyπ) := by infer_instance
      haveI : Epi ((S.iso (pageIndex n)).hom) := by infer_instance
      simpa [stageToPage, stageData, pulledCycles, frontIso] using
        (show Epi
          (frontIso.hom ≫
            Subobject.pullbackπ (stageToPage S n) (pageCyclesSubobject S n) ≫
              (S.page (pageIndex n)).kernelSubobjectToCycles ≫
                (S.page (pageIndex n)).shortComplex.homologyπ ≫
                  (S.iso (pageIndex n)).hom) from inferInstance)

/-- Helper for Remark 12.20.3 (Variant): the public map `Z_r ⟶ E_r` is already epimorphic before
identifying `E_r` with the quotient `Z_r / B_r`. -/
private theorem epi_cycleToPage
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Epi (S.cycleToPage r) := by
  -- Proof comment: `cycleToPage` is the recursive epi `stageToPage` followed by the tautological
  -- page-index transport isomorphism.
  haveI := S.stageToPageEpi r.natPred
  let pageIso : (S.page (pageIndex r.natPred)).obj ≅ (S.page r).obj :=
    eqToIso (by simpa using congrArg (fun s ↦ (S.page s).obj) (pageIndex_natPred r))
  haveI : Epi pageIso.hom := by infer_instance
  change Epi (stageToPage S r.natPred ≫ pageIso.hom)
  infer_instance

/-- Helper for Remark 12.20.3 (Variant): the front of the successor-stage `stageToPage`
identifies the mapped boundary inclusion with the pulled-back page-boundary inclusion. -/
private theorem stageToPageSucc_imageFront
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let pulledBoundaries : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageBoundariesSubobject S r.natPred)
    let pulledCycles : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageCyclesSubobject S r.natPred)
    let mappedBoundaries : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
    let mappedCycles : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledCycles
    let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
        (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
    let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
        (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
    Subobject.ofLE mappedBoundaries mappedCycles
        ((Subobject.map (S.cycle r).arrow).monotone <|
          (Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
      cycleFront =
        boundaryFront ≫
          Subobject.ofLE pulledBoundaries pulledCycles
            ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
              S.pageBoundary_le_pageCycle r.natPred) := by
  -- Proof comment: both morphisms become the same mono `pulledBoundaries ⟶ E₁` after composing
  -- with the defining inclusion of the pulled-back cycle piece, so mono cancellation removes the
  -- successor-front transport once and for all.
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let mappedBoundaries : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
  let mappedCycles : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledCycles
  let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
  let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
  change Subobject.ofLE mappedBoundaries mappedCycles
      ((Subobject.map (S.cycle r).arrow).monotone <|
        (Subobject.pullback (stageToPage S r.natPred)).monotone <|
          S.pageBoundary_le_pageCycle r.natPred) ≫
    cycleFront =
      boundaryFront ≫
        Subobject.ofLE pulledBoundaries pulledCycles
          ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred)
  apply (cancel_mono (pulledCycles.arrow ≫ (S.cycle r).arrow)).1
  simp [cycleFront, boundaryFront, Category.assoc]

/-- Helper for Remark 12.20.3 (Variant): after transporting the mapped successor boundary to the
pulled-back model, the remaining comparison with the page-level cycles is the pullback of the
usual image-to-kernel morphism. -/
private theorem boundaryFront_comp_pullbackImageToKernel
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let prevDiff :=
      shiftedPreviousDifferential (T (pageIndex r.natPred)).functor (S.page (pageIndex r.natPred)).d
    let pulledBoundaries : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageBoundariesSubobject S r.natPred)
    let pulledCycles : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageCyclesSubobject S r.natPred)
    let mappedBoundaries : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
    let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
        (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
    boundaryFront ≫
        Subobject.ofLE pulledBoundaries pulledCycles
          ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
      Subobject.pullbackπ (stageToPage S r.natPred) (pageCyclesSubobject S r.natPred) =
      boundaryFront ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageBoundariesSubobject S r.natPred) ≫
        imageToKernel prevDiff (S.page (pageIndex r.natPred)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
            (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared) := by
  -- Proof comment: this is the generic pullback identity for `imageToKernel`, with the successor
  -- front isomorphism inserted on the left and no further transport.
  let prevDiff :=
    shiftedPreviousDifferential (T (pageIndex r.natPred)).functor (S.page (pageIndex r.natPred)).d
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let mappedBoundaries : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
  let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
  simpa [prevDiff, pulledBoundaries, pulledCycles, mappedBoundaries, boundaryFront, Category.assoc]
    using
      congrArg (fun k ↦ boundaryFront ≫ k)
        (pullbackImageToKernel (stageToPage S r.natPred) prevDiff
          (S.page (pageIndex r.natPred)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
            (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared))

/-- Helper for Remark 12.20.3 (Variant): the successor-front comparison remains valid after
postcomposing with the full pullback-cycles-to-homology tail. -/
private theorem stageToPageSucc_imageFront_compTail
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let pulledBoundaries : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageBoundariesSubobject S r.natPred)
    let pulledCycles : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageCyclesSubobject S r.natPred)
    let mappedBoundaries : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
    let mappedCycles : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledCycles
    let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
        (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
    let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
        (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
    Subobject.ofLE mappedBoundaries mappedCycles
        ((Subobject.map (S.cycle r).arrow).monotone <|
          (Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
      cycleFront ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ =
      boundaryFront ≫
        Subobject.ofLE pulledBoundaries pulledCycles
          ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
  -- Proof comment: postcompose the already-proved successor-front equality by the exact common
  -- tail needed in the vanishing theorem, so the long transport appears only once.
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let mappedBoundaries : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
  let mappedCycles : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledCycles
  let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
  let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
  calc
    Subobject.ofLE mappedBoundaries mappedCycles
        ((Subobject.map (S.cycle r).arrow).monotone <|
          (Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
      cycleFront ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ =
      (Subobject.ofLE mappedBoundaries mappedCycles
          ((Subobject.map (S.cycle r).arrow).monotone <|
            (Subobject.pullback (stageToPage S r.natPred)).monotone <|
              S.pageBoundary_le_pageCycle r.natPred) ≫
        cycleFront) ≫
          Subobject.pullbackπ (stageToPage S r.natPred)
            (pageCyclesSubobject S r.natPred) ≫
          (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
          (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
            simp [Category.assoc]
    _ =
      (boundaryFront ≫
          Subobject.ofLE pulledBoundaries pulledCycles
            ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
              S.pageBoundary_le_pageCycle r.natPred)) ≫
          Subobject.pullbackπ (stageToPage S r.natPred)
            (pageCyclesSubobject S r.natPred) ≫
          (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
          (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
            rw [S.stageToPageSucc_imageFront r]
    _ =
      boundaryFront ≫
        Subobject.ofLE pulledBoundaries pulledCycles
          ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
          simp [Category.assoc]

/-- Helper for Remark 12.20.3 (Variant): the pulled-boundary normalization remains valid after
postcomposing with the cycles-to-homology tail. -/
private theorem boundaryFront_comp_pullbackImageToKernel_compTail
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let prevDiff :=
      shiftedPreviousDifferential (T (pageIndex r.natPred)).functor (S.page (pageIndex r.natPred)).d
    let pulledBoundaries : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageBoundariesSubobject S r.natPred)
    let pulledCycles : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageCyclesSubobject S r.natPred)
    let mappedBoundaries : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
    let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
        (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
    boundaryFront ≫
        Subobject.ofLE pulledBoundaries pulledCycles
          ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
      Subobject.pullbackπ (stageToPage S r.natPred)
        (pageCyclesSubobject S r.natPred) ≫
      (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
      (S.page (pageIndex r.natPred)).shortComplex.homologyπ =
      boundaryFront ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageBoundariesSubobject S r.natPred) ≫
        imageToKernel prevDiff (S.page (pageIndex r.natPred)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
            (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
  -- Proof comment: this is the previous pulled-boundary rewrite with the common
  -- `kernelSubobjectToCycles ≫ homologyπ` tail appended on both sides.
  let prevDiff :=
    shiftedPreviousDifferential (T (pageIndex r.natPred)).functor (S.page (pageIndex r.natPred)).d
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let mappedBoundaries : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
  let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
  calc
    boundaryFront ≫
        Subobject.ofLE pulledBoundaries pulledCycles
          ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
      Subobject.pullbackπ (stageToPage S r.natPred)
        (pageCyclesSubobject S r.natPred) ≫
      (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
      (S.page (pageIndex r.natPred)).shortComplex.homologyπ =
      (boundaryFront ≫
          Subobject.ofLE pulledBoundaries pulledCycles
            ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
              S.pageBoundary_le_pageCycle r.natPred) ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred)) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
          simp [Category.assoc]
    _ =
      (boundaryFront ≫
          Subobject.pullbackπ (stageToPage S r.natPred)
            (pageBoundariesSubobject S r.natPred) ≫
          imageToKernel prevDiff (S.page (pageIndex r.natPred)).d
            (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
              (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared)) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
          rw [S.boundaryFront_comp_pullbackImageToKernel r]
    _ =
      boundaryFront ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageBoundariesSubobject S r.natPred) ≫
        imageToKernel prevDiff (S.page (pageIndex r.natPred)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
            (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
          simp [Category.assoc]

/-- Helper for Remark 12.20.3 (Variant): on the mapped pullback successor normal form, the
boundary inclusion is killed already before inserting the page-comparison isomorphism. -/
private theorem mappedPullbackBoundary_toSuccHomology_zero
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let pulledBoundaries : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageBoundariesSubobject S r.natPred)
    let pulledCycles : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageCyclesSubobject S r.natPred)
    let mappedBoundaries : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
    let mappedCycles : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledCycles
    let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
        (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
    Subobject.ofLE mappedBoundaries mappedCycles
        ((Subobject.map (S.cycle r).arrow).monotone <|
          (Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
      cycleFront ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ = 0 := by
  -- Proof comment: first rewrite the mapped successor boundary through the front comparison, then
  -- replace the pulled boundary-to-cycles map by `imageToKernel`, and finally use the standard
  -- page-homology vanishing `imageToKernel ≫ kernelSubobjectToCycles ≫ homologyπ = 0`.
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let mappedBoundaries : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
  let mappedCycles : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledCycles
  let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
  let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
  calc
    Subobject.ofLE mappedBoundaries mappedCycles
        ((Subobject.map (S.cycle r).arrow).monotone <|
          (Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
      cycleFront ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ =
      boundaryFront ≫
        Subobject.ofLE pulledBoundaries pulledCycles
          ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred) ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
          rw [S.stageToPageSucc_imageFront_compTail r]
    _ =
      boundaryFront ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageBoundariesSubobject S r.natPred) ≫
        imageToKernel
          (shiftedPreviousDifferential (T (pageIndex r.natPred)).functor
            (S.page (pageIndex r.natPred)).d)
          (S.page (pageIndex r.natPred)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
            (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ := by
          rw [S.boundaryFront_comp_pullbackImageToKernel_compTail r]
    _ = 0 := by
      calc
        boundaryFront ≫
            Subobject.pullbackπ (stageToPage S r.natPred)
              (pageBoundariesSubobject S r.natPred) ≫
            imageToKernel
              (shiftedPreviousDifferential (T (pageIndex r.natPred)).functor
                (S.page (pageIndex r.natPred)).d)
              (S.page (pageIndex r.natPred)).d
              (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
                (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared) ≫
            (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
            (S.page (pageIndex r.natPred)).shortComplex.homologyπ =
          (boundaryFront ≫
              Subobject.pullbackπ (stageToPage S r.natPred)
                (pageBoundariesSubobject S r.natPred)) ≫
            (imageToKernel
                (shiftedPreviousDifferential (T (pageIndex r.natPred)).functor
                  (S.page (pageIndex r.natPred)).d)
                (S.page (pageIndex r.natPred)).d
                (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
                  (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared) ≫
              (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
              (S.page (pageIndex r.natPred)).shortComplex.homologyπ) := by
                simp [Category.assoc]
        _ =
          (boundaryFront ≫
              Subobject.pullbackπ (stageToPage S r.natPred)
                (pageBoundariesSubobject S r.natPred)) ≫ 0 := by
                rw [S.imageToKernel_kernelSubobjectToCycles_homologyπ_zero r.natPred]
        _ = 0 := by
          rw [comp_zero]

/-- Helper for Remark 12.20.3 (Variant): on a fixed page, the kernel of the map from the
kernel-subobject of the outgoing differential to homology is exactly the boundary subobject. -/
private theorem kernelSubobjectToCycles_homologyπ_kernel
    (S : ShiftedSpectralSequence T) (n : ℕ) :
    kernelSubobject
        ((S.page (pageIndex n)).kernelSubobjectToCycles ≫
          (S.page (pageIndex n)).shortComplex.homologyπ) =
      Subobject.mk
        (imageToKernel
          (shiftedPreviousDifferential (T (pageIndex n)).functor (S.page (pageIndex n)).d)
          (S.page (pageIndex n)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
            (S.page (pageIndex n)).d (S.page (pageIndex n)).d_squared)) := by
  -- Route correction: instead of transporting exactness through two auxiliary short complexes,
  -- compare images directly with the standard `toCycles` map and then pull the resulting kernel
  -- equality back across the cycles/kernel isomorphism.
  let page := S.page (pageIndex n)
  let prevDiff := shiftedPreviousDifferential (T (pageIndex n)).functor page.d
  let imageToKer :=
    imageToKernel prevDiff page.d
      (shiftedPreviousDifferential_comp_d (T (pageIndex n)).functor
        page.d page.d_squared)
  have hExactToCycles :
      (ShortComplex.mk
          page.shortComplex.toCycles
          page.shortComplex.homologyπ
          page.shortComplex.toCycles_comp_homologyπ).Exact := by
    exact ShortComplex.exact_of_g_is_cokernel _ page.shortComplex.homologyIsCokernel
  have hToCyclesKernel :
      imageSubobject page.shortComplex.toCycles =
        kernelSubobject page.shortComplex.homologyπ := by
    simpa using
      (ShortComplex.exact_iff_image_eq_kernel
        (S := ShortComplex.mk
          page.shortComplex.toCycles
          page.shortComplex.homologyπ
          page.shortComplex.toCycles_comp_homologyπ)).1 hExactToCycles
  have hImageKernel :
      imageSubobject (imageToKer ≫ page.kernelSubobjectToCycles) =
        kernelSubobject page.shortComplex.homologyπ := by
    calc
      imageSubobject (imageToKer ≫ page.kernelSubobjectToCycles) =
          imageSubobject
            (factorThruImageSubobject prevDiff ≫
              (imageToKer ≫ page.kernelSubobjectToCycles)) := by
            symm
            exact imageSubobject_comp_eq_of_epi
              (factorThruImageSubobject prevDiff)
              (imageToKer ≫ page.kernelSubobjectToCycles)
      _ = imageSubobject page.shortComplex.toCycles := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ imageSubobject k)
                (S.factorThruImageSubobject_imageToKernel_kernelSubobjectToCycles_eq_toCycles n)
      _ = kernelSubobject page.shortComplex.homologyπ := hToCyclesKernel
  haveI : Mono imageToKer := by
    dsimp [imageToKer]
    infer_instance
  haveI : IsIso page.kernelSubobjectToCycles := by
    exact isIso_kernelSubobjectToCycles page
  haveI : Mono (imageToKer ≫ page.kernelSubobjectToCycles) := by
    infer_instance
  have hKernelHomology :
      kernelSubobject page.shortComplex.homologyπ =
        Subobject.mk (imageToKer ≫ page.kernelSubobjectToCycles) := by
    calc
      kernelSubobject page.shortComplex.homologyπ =
          imageSubobject (imageToKer ≫ page.kernelSubobjectToCycles) := by
            exact hImageKernel.symm
      _ = Subobject.mk (imageToKer ≫ page.kernelSubobjectToCycles) := by
            simpa [imageToKer] using
              (imageSubobject_mono (imageToKer ≫ page.kernelSubobjectToCycles))
  calc
    kernelSubobject (page.kernelSubobjectToCycles ≫ page.shortComplex.homologyπ) =
      (Subobject.pullback page.kernelSubobjectToCycles).obj
        (kernelSubobject page.shortComplex.homologyπ) := by
          exact kernelSubobject_comp_eq_pullback _ _
    _ =
      (Subobject.pullback page.kernelSubobjectToCycles).obj
        (Subobject.mk (imageToKer ≫ page.kernelSubobjectToCycles)) := by
          rw [hKernelHomology]
    _ = Subobject.mk imageToKer := by
          haveI : Mono page.kernelSubobjectToCycles := by infer_instance
          simpa [imageToKer] using
            (Subobject.pullback_obj_mk
              (f := page.kernelSubobjectToCycles)
              (i := imageToKer ≫ page.kernelSubobjectToCycles)
              (j := imageToKer)
              (f' := 𝟙 _)
              (IsPullback.of_horiz_isIso (CommSq.mk (by simp))))

/-- Helper for Remark 12.20.3 (Variant): on the pulled-back successor normal form, the pulled
boundary inclusion is the pullback of the page-level `imageToKernel` comparison. -/
private theorem pulledBoundaryImageToKernel_isPullback
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let prevDiff :=
      shiftedPreviousDifferential (T (pageIndex r.natPred)).functor (S.page (pageIndex r.natPred)).d
    let pulledBoundaries : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageBoundariesSubobject S r.natPred)
    let pulledCycles : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageCyclesSubobject S r.natPred)
    let boundaryInCycles : (pulledBoundaries : A) ⟶ (pulledCycles : A) :=
      Subobject.ofLE pulledBoundaries pulledCycles
        ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
          S.pageBoundary_le_pageCycle r.natPred)
    IsPullback
      (Subobject.pullbackπ (stageToPage S r.natPred)
        (pageBoundariesSubobject S r.natPred))
      boundaryInCycles
      (imageToKernel prevDiff (S.page (pageIndex r.natPred)).d
        (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
          (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared))
      (Subobject.pullbackπ (stageToPage S r.natPred)
        (pageCyclesSubobject S r.natPred)) := by
  -- Proof comment: paste the pullback square for the page-boundary subobject with the pullback
  -- square for the page-cycle subobject; the middle square is exactly the pulled comparison with
  -- `imageToKernel`.
  let prevDiff :=
    shiftedPreviousDifferential (T (pageIndex r.natPred)).functor (S.page (pageIndex r.natPred)).d
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let boundaryInCycles : (pulledBoundaries : A) ⟶ (pulledCycles : A) :=
    Subobject.ofLE pulledBoundaries pulledCycles
      ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
        S.pageBoundary_le_pageCycle r.natPred)
  have hOuter :
      IsPullback
        pulledBoundaries.arrow
        (Subobject.pullbackπ (stageToPage S r.natPred)
          (pageBoundariesSubobject S r.natPred))
        (stageToPage S r.natPred)
        (pageBoundariesSubobject S r.natPred).arrow := by
    simpa using
      (Subobject.isPullback (stageToPage S r.natPred)
        (pageBoundariesSubobject S r.natPred)).flip
  have hRight :
      IsPullback
        pulledCycles.arrow
        (Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred))
        (stageToPage S r.natPred)
        (pageCyclesSubobject S r.natPred).arrow := by
    simpa using
      (Subobject.isPullback (stageToPage S r.natPred)
        (pageCyclesSubobject S r.natPred)).flip
  have hComm :
      boundaryInCycles ≫
        Subobject.pullbackπ (stageToPage S r.natPred)
          (pageCyclesSubobject S r.natPred) =
      Subobject.pullbackπ (stageToPage S r.natPred)
          (pageBoundariesSubobject S r.natPred) ≫
        imageToKernel prevDiff (S.page (pageIndex r.natPred)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
            (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared) := by
    simpa [boundaryInCycles, prevDiff] using
      (pullbackImageToKernel (stageToPage S r.natPred)
        prevDiff
        (S.page (pageIndex r.natPred)).d
        (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
          (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared))
  have hOuter' :
      IsPullback
        (boundaryInCycles ≫ pulledCycles.arrow)
        (Subobject.pullbackπ (stageToPage S r.natPred)
          (pageBoundariesSubobject S r.natPred))
        (stageToPage S r.natPred)
        (imageToKernel prevDiff (S.page (pageIndex r.natPred)).d
          (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
            (S.page (pageIndex r.natPred)).d (S.page (pageIndex r.natPred)).d_squared) ≫
          (pageCyclesSubobject S r.natPred).arrow) := by
    simpa [boundaryInCycles, prevDiff, Category.assoc, pageBoundariesSubobject, pageCyclesSubobject,
      imageToKernel_arrow, Subobject.ofLE_arrow] using hOuter
  exact ((IsPullback.paste_horiz_iff hRight hComm).1 hOuter').flip

/-- Helper for Remark 12.20.3 (Variant): on the pulled-back successor normal form, the kernel of
the homology map is the pulled-back page-boundary inclusion. -/
private theorem pulledBoundary_eq_kernel_succHomologyMap
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let pulledBoundaries : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageBoundariesSubobject S r.natPred)
    let pulledCycles : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageCyclesSubobject S r.natPred)
    kernelSubobject
        (Subobject.pullbackπ (stageToPage S r.natPred)
            (pageCyclesSubobject S r.natPred) ≫
          (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
          (S.page (pageIndex r.natPred)).shortComplex.homologyπ) =
      Subobject.mk
        (Subobject.ofLE pulledBoundaries pulledCycles
          ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred)) := by
  -- Proof comment: first compute the page-level kernel inside the pulled-back cycle object, then
  -- identify the resulting pullback subobject with the already defined pulled boundary piece.
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let boundaryInCycles : (pulledBoundaries : A) ⟶ (pulledCycles : A) :=
    Subobject.ofLE pulledBoundaries pulledCycles
      ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
        S.pageBoundary_le_pageCycle r.natPred)
  let pullbackCyclesπ :
      (pulledCycles : A) ⟶ (pageCyclesSubobject S r.natPred : A) :=
    Subobject.pullbackπ (stageToPage S r.natPred) (pageCyclesSubobject S r.natPred)
  haveI : Mono boundaryInCycles := by
    change Mono
      (Subobject.ofLE pulledBoundaries pulledCycles
        ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
          S.pageBoundary_le_pageCycle r.natPred))
    infer_instance
  calc
    kernelSubobject
        (pullbackCyclesπ ≫
          (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
          (S.page (pageIndex r.natPred)).shortComplex.homologyπ) =
      (Subobject.pullback pullbackCyclesπ).obj
        (kernelSubobject
          ((S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
            (S.page (pageIndex r.natPred)).shortComplex.homologyπ)) := by
          exact kernelSubobject_comp_eq_pullback _ _
    _ =
      (Subobject.pullback pullbackCyclesπ).obj
        (Subobject.mk
          (imageToKernel
            (shiftedPreviousDifferential (T (pageIndex r.natPred)).functor
              (S.page (pageIndex r.natPred)).d)
            (S.page (pageIndex r.natPred)).d
            (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
              (S.page (pageIndex r.natPred)).d
              (S.page (pageIndex r.natPred)).d_squared))) := by
          rw [S.kernelSubobjectToCycles_homologyπ_kernel r.natPred]
    _ = Subobject.mk boundaryInCycles := by
          simpa [pulledBoundaries, pulledCycles, boundaryInCycles, pullbackCyclesπ,
            pageBoundariesSubobject] using
            (Subobject.pullback_obj_mk
              (f := pullbackCyclesπ)
              (i := imageToKernel
                (shiftedPreviousDifferential (T (pageIndex r.natPred)).functor
                  (S.page (pageIndex r.natPred)).d)
                (S.page (pageIndex r.natPred)).d
                (shiftedPreviousDifferential_comp_d (T (pageIndex r.natPred)).functor
                  (S.page (pageIndex r.natPred)).d
                  (S.page (pageIndex r.natPred)).d_squared))
              (j := boundaryInCycles)
              (f' := Subobject.pullbackπ (stageToPage S r.natPred)
                (pageBoundariesSubobject S r.natPred))
              (S.pulledBoundaryImageToKernel_isPullback r))

/-- Helper for Remark 12.20.3 (Variant): after transporting across the successor front
isomorphism, the mapped pulled-back boundary inclusion is exactly the kernel of the normalized
successor homology map. -/
private theorem mappedPullbackBoundary_eq_kernel_succHomologyMap
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let pulledBoundaries : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageBoundariesSubobject S r.natPred)
    let pulledCycles : Subobject ((S.cycle r : A)) :=
      (Subobject.pullback (stageToPage S r.natPred)).obj
        (pageCyclesSubobject S r.natPred)
    let mappedBoundaries : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
    let mappedCycles : Subobject ((S.page 1).obj) :=
      (Subobject.map (S.cycle r).arrow).obj pulledCycles
    let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
        (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
    kernelSubobject
        (cycleFront ≫
          Subobject.pullbackπ (stageToPage S r.natPred)
            (pageCyclesSubobject S r.natPred) ≫
          (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
          (S.page (pageIndex r.natPred)).shortComplex.homologyπ) =
      Subobject.mk
        (Subobject.ofLE mappedBoundaries mappedCycles
          ((Subobject.map (S.cycle r).arrow).monotone <|
            (Subobject.pullback (stageToPage S r.natPred)).monotone <|
              S.pageBoundary_le_pageCycle r.natPred)) := by
  -- Proof comment: pull back the already computed kernel on the pulled successor stage across the
  -- front isomorphism linking the mapped and pulled presentations.
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let mappedBoundaries : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
  let mappedCycles : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledCycles
  let boundaryInCycles : (pulledBoundaries : A) ⟶ (pulledCycles : A) :=
    Subobject.ofLE pulledBoundaries pulledCycles
      ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
        S.pageBoundary_le_pageCycle r.natPred)
  let mappedBoundaryInCycles : (mappedBoundaries : A) ⟶ (mappedCycles : A) :=
    Subobject.ofLE mappedBoundaries mappedCycles
      ((Subobject.map (S.cycle r).arrow).monotone <|
        (Subobject.pullback (stageToPage S r.natPred)).monotone <|
          S.pageBoundary_le_pageCycle r.natPred)
  let boundaryFront : (mappedBoundaries : A) ⟶ (pulledBoundaries : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledBoundaries.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledBoundaries.arrow ≫ (S.cycle r).arrow)).hom
  let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
  haveI : Mono boundaryInCycles := by
    change Mono
      (Subobject.ofLE pulledBoundaries pulledCycles
        ((Subobject.pullback (stageToPage S r.natPred)).monotone <|
          S.pageBoundary_le_pageCycle r.natPred))
    infer_instance
  haveI : Mono mappedBoundaryInCycles := by
    change Mono
      (Subobject.ofLE mappedBoundaries mappedCycles
        ((Subobject.map (S.cycle r).arrow).monotone <|
          (Subobject.pullback (stageToPage S r.natPred)).monotone <|
            S.pageBoundary_le_pageCycle r.natPred))
    infer_instance
  have hFront :
      IsPullback boundaryFront mappedBoundaryInCycles boundaryInCycles cycleFront := by
    exact IsPullback.of_horiz_isIso <|
      CommSq.mk (by
        simpa [boundaryInCycles, mappedBoundaryInCycles, boundaryFront, cycleFront,
          Category.assoc] using (S.stageToPageSucc_imageFront r).symm)
  have hKernel :
      kernelSubobject
          (Subobject.pullbackπ (stageToPage S r.natPred)
              (pageCyclesSubobject S r.natPred) ≫
            (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
            (S.page (pageIndex r.natPred)).shortComplex.homologyπ) =
        Subobject.mk boundaryInCycles := by
    simpa [pulledBoundaries, pulledCycles, boundaryInCycles] using
      (S.pulledBoundary_eq_kernel_succHomologyMap r)
  calc
    kernelSubobject
        (cycleFront ≫
          Subobject.pullbackπ (stageToPage S r.natPred)
            (pageCyclesSubobject S r.natPred) ≫
          (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
          (S.page (pageIndex r.natPred)).shortComplex.homologyπ) =
      (Subobject.pullback cycleFront).obj
        (kernelSubobject
          (Subobject.pullbackπ (stageToPage S r.natPred)
              (pageCyclesSubobject S r.natPred) ≫
            (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
            (S.page (pageIndex r.natPred)).shortComplex.homologyπ)) := by
          exact kernelSubobject_comp_eq_pullback _ _
    _ = (Subobject.pullback cycleFront).obj (Subobject.mk boundaryInCycles) := by
          exact congrArg ((Subobject.pullback cycleFront).obj) hKernel
    _ = Subobject.mk mappedBoundaryInCycles := by
          simpa [pulledBoundaries, pulledCycles, mappedBoundaries, mappedCycles,
            boundaryInCycles, mappedBoundaryInCycles, boundaryFront, cycleFront] using
            (Subobject.pullback_obj_mk
              (f := cycleFront)
              (i := boundaryInCycles)
              (j := mappedBoundaryInCycles)
              (f' := boundaryFront)
              hFront)

/-- Helper for Remark 12.20.3 (Variant): a positive natural number is the successor of its
predecessor. -/
private theorem positiveNat_eq_succ_natPred (r : ℕ+) : (r : ℕ) = Nat.succ r.natPred := by
  -- Proof comment: this is the standard normalization needed to unfold the successor branch of
  -- the recursive stage presentation.
  simpa using (PNat.natPred_add_one r).symm

/-- Helper for Remark 12.20.3 (Variant): unfolding one successor clause of `stageData`
identifies the owner-side successor map with the normalized successor homology composite used by
the mapped-pullback kernel theorem. -/
private theorem stageToPageSucc_eq_normalizedSuccHomologyMap
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    let prev := stageData S r.natPred
    let pulledCycles : Subobject (prev.cycle : A) :=
      (Subobject.pullback prev.toPage).obj
        (pageCyclesSubobject S r.natPred)
    let nextCycle : Subobject ((S.page 1).obj) :=
      (Subobject.map prev.cycle.arrow).obj pulledCycles
    let cycleFront : (nextCycle : A) ⟶ (pulledCycles : A) :=
      (Subobject.isoOfEq _ _
        (by
          simpa [Subobject.mk_arrow] using
            (Subobject.map_mk pulledCycles.arrow prev.cycle.arrow))).hom ≫
        (Subobject.underlyingIso (pulledCycles.arrow ≫ prev.cycle.arrow)).hom
    (stageData S (Nat.succ r.natPred)).toPage =
      cycleFront ≫
        Subobject.pullbackπ prev.toPage
          (pageCyclesSubobject S r.natPred) ≫
        (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
        (S.page (pageIndex r.natPred)).shortComplex.homologyπ ≫
        (S.iso (pageIndex r.natPred)).hom := by
  -- Proof comment: the successor clause of `stageData` is literally the mapped-pullback
  -- composite used in the successor kernel computation.
  dsimp [stageData]
  simp_rw [Category.assoc]
  rfl

/-- Helper for Remark 12.20.3 (Variant): at the owner-side successor stage, the kernel of
`stageToPage` is exactly the recursive successor boundary inclusion. -/
private theorem kernelStageToPageSucc_eq_boundaryAuxSucc
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    kernelSubobject (stageToPage S (Nat.succ r.natPred)) =
      Subobject.mk
        (Subobject.ofLE
          (S.boundaryAux (Nat.succ r.natPred))
          (stageCycle S (Nat.succ r.natPred))
          (boundaryAuxLeStageCycle S (Nat.succ r.natPred))) := by
  -- Proof comment: rewrite the successor `stageToPage` map into the normalized mapped-pullback
  -- composite, remove the trailing page-comparison isomorphism from the kernel, and then unfold
  -- the successor clauses of `boundaryAux` and `stageCycle`.
  let pulledBoundaries : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageBoundariesSubobject S r.natPred)
  let pulledCycles : Subobject ((S.cycle r : A)) :=
    (Subobject.pullback (stageToPage S r.natPred)).obj
      (pageCyclesSubobject S r.natPred)
  let mappedBoundaries : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledBoundaries
  let mappedCycles : Subobject ((S.page 1).obj) :=
    (Subobject.map (S.cycle r).arrow).obj pulledCycles
  let cycleFront : (mappedCycles : A) ⟶ (pulledCycles : A) :=
    (Subobject.isoOfEq _ _
      (by
        simpa [Subobject.mk_arrow] using
          (Subobject.map_mk pulledCycles.arrow (S.cycle r).arrow))).hom ≫
      (Subobject.underlyingIso (pulledCycles.arrow ≫ (S.cycle r).arrow)).hom
  let succHomologyMap :
      (mappedCycles : A) ⟶ ((S.page (pageIndex r.natPred)).shortComplex.homology : A) :=
    cycleFront ≫
      Subobject.pullbackπ (stageToPage S r.natPred)
        (pageCyclesSubobject S r.natPred) ≫
      (S.page (pageIndex r.natPred)).kernelSubobjectToCycles ≫
      (S.page (pageIndex r.natPred)).shortComplex.homologyπ
  have hStageToPage :
      stageToPage S (Nat.succ r.natPred) =
        succHomologyMap ≫ (S.iso (pageIndex r.natPred)).hom := by
    simpa [stageToPage, succHomologyMap, pulledCycles, mappedCycles, cycleFront, Category.assoc]
      using S.stageToPageSucc_eq_normalizedSuccHomologyMap r
  have hKernelSuccIso :
      kernelSubobject (succHomologyMap ≫ (S.iso (pageIndex r.natPred)).hom) =
        kernelSubobject succHomologyMap := by
    simpa [succHomologyMap, Category.assoc] using
      (kernelSubobject_comp_mono succHomologyMap ((S.iso (pageIndex r.natPred)).hom))
  have hKernelStageToPage :
      kernelSubobject (stageToPage S (Nat.succ r.natPred)) =
        kernelSubobject (succHomologyMap ≫ (S.iso (pageIndex r.natPred)).hom) := by
    rw [hStageToPage]
    rfl
  have hKernelMapped :
      kernelSubobject succHomologyMap =
        Subobject.mk
          (Subobject.ofLE mappedBoundaries mappedCycles
            ((Subobject.map (S.cycle r).arrow).monotone <|
              (Subobject.pullback (stageToPage S r.natPred)).monotone <|
                S.pageBoundary_le_pageCycle r.natPred)) := by
    simpa [succHomologyMap, pulledBoundaries, pulledCycles, mappedBoundaries, mappedCycles,
      cycleFront] using
      S.mappedPullbackBoundary_eq_kernel_succHomologyMap r
  have hBoundaryAux :
      Subobject.mk
          (Subobject.ofLE mappedBoundaries mappedCycles
            ((Subobject.map (S.cycle r).arrow).monotone <|
              (Subobject.pullback (stageToPage S r.natPred)).monotone <|
                S.pageBoundary_le_pageCycle r.natPred)) =
      Subobject.mk
          (Subobject.ofLE
            (S.boundaryAux (Nat.succ r.natPred))
            (stageCycle S (Nat.succ r.natPred))
            (boundaryAuxLeStageCycle S (Nat.succ r.natPred))) := by
    simpa [boundaryAux, cycle, stageCycle, stageData, pulledBoundaries, pulledCycles,
      mappedBoundaries, mappedCycles]
  exact hKernelStageToPage.trans <| hKernelSuccIso.trans <| hKernelMapped.trans hBoundaryAux

/-- Helper for Remark 12.20.3 (Variant): the public successor map has the same kernel as the
owner-side successor `stageToPage` map before the final page-identification isomorphism. -/
private theorem cycleToPageSucc_kernel_eq_stageToPageSuccKernel
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    kernelSubobject (S.cycleToPage (r + 1)) =
      kernelSubobject (stageToPage S (r : ℕ)) := by
  -- Proof comment: `cycleToPage (r + 1)` is `stageToPage` followed by a tautological page-index
  -- isomorphism, so kernel invariance under composition with a mono removes that final transport.
  let pageIso : (S.page (pageIndex (r : ℕ))).obj ≅ (S.page (r + 1)).obj :=
    eqToIso (by
      simpa [positiveNat_eq_succ_natPred r] using
        congrArg (fun s ↦ (S.page s).obj) (pageIndex_natPred (r + 1)))
  have hcomp :=
    kernelSubobject_comp_mono (stageToPage S (r : ℕ)) pageIso.hom
  change
    kernelSubobject (stageToPage S (r : ℕ) ≫ pageIso.hom) =
      kernelSubobject (stageToPage S (r : ℕ))
  simpa [cycleToPage, pageIso, PNat.add_one, Nat.natPred_succPNat] using hcomp

/-- Remark 12.20.3 (Variant): the public successor map `Z_{r + 1} ⟶ E_{r + 1}` has the
successor boundary inclusion as its kernel arrow. -/
private theorem boundarySucc_eq_kernel_cycleToPage
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    kernelSubobject (S.cycleToPage (r + 1)) =
      Subobject.mk
        (Subobject.ofLE (S.boundary (r + 1)) (S.cycle (r + 1))
          (S.boundary_le_cycle (r + 1))) := by
  -- Proof comment: first remove the final public page-identification from `cycleToPage`, then
  -- compute the kernel at the owner-side successor stage, and only at the end rewrite the public
  -- `boundary`/`cycle` notation to the recursive `boundaryAux`/`stageCycle` spelling.
  -- Route correction: the hard dependent transport is avoided by proving the kernel theorem in the
  -- recursive `stageData` world and using only a final notation rewrite here.
  have hStage :
      kernelSubobject (stageToPage S (r : ℕ)) =
        Subobject.mk
          (Subobject.ofLE
            (S.boundaryAux (r : ℕ))
            (stageCycle S (r : ℕ))
            (boundaryAuxLeStageCycle S (r : ℕ))) := by
    rw [positiveNat_eq_succ_natPred r, Nat.succ_eq_add_one]
    exact S.kernelStageToPageSucc_eq_boundaryAuxSucc r
  have hBoundaryNotation :
      Subobject.mk
          (Subobject.ofLE
            (S.boundaryAux (r : ℕ))
            (stageCycle S (r : ℕ))
            (boundaryAuxLeStageCycle S (r : ℕ))) =
        Subobject.mk
          (Subobject.ofLE (S.boundary (r + 1)) (S.cycle (r + 1))
            (S.boundary_le_cycle (r + 1))) := by
    simpa [boundary, cycle, PNat.add_one, Nat.natPred_succPNat]
  exact (S.cycleToPageSucc_kernel_eq_stageToPageSuccKernel r).trans <|
    hStage.trans hBoundaryNotation

/-- Helper for Remark 12.20.3 (Variant): on the first page, `B₁ = 0`, so the induced map from
`B₁` to `E₁` is zero. -/
private theorem boundaryToPage_zero_one (S : ShiftedSpectralSequence T) :
    Subobject.ofLE (S.boundary 1) (S.cycle 1) (S.boundary_le_cycle 1) ≫
      S.cycleToPage 1 = 0 := by
  -- Proof comment: after unfolding the first recursive stage, the source is the bottom subobject,
  -- whose arrow into `E₁` is the zero morphism.
  rw [cycleToPage]
  let pageIso : (S.page (pageIndex (1 : ℕ+).natPred)).obj ≅ (S.page 1).obj :=
    eqToIso (by simpa using congrArg (fun s ↦ (S.page s).obj) (pageIndex_natPred 1))
  change Subobject.ofLE (⊥ : Subobject ((S.page 1).obj)) (⊤ : Subobject ((S.page 1).obj)) (by simp) ≫
      ((⊤ : Subobject ((S.page 1).obj)).arrow ≫ pageIso.hom) = 0
  simp

/-- Helper for Remark 12.20.3 (Variant): the successor boundary inclusion already vanishes as the
kernel arrow of the successor map. -/
private theorem boundaryToPage_zero_succ
    (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject.ofLE (S.boundary (r + 1)) (S.cycle (r + 1))
        (S.boundary_le_cycle (r + 1)) ≫
      S.cycleToPage (r + 1) = 0 := by
  -- Proof comment: identify the successor boundary inclusion with the kernel arrow of
  -- `cycleToPage (r + 1)` and then use the universal vanishing of the kernel arrow.
  have hKernel := S.boundarySucc_eq_kernel_cycleToPage r
  let i :
      (S.boundary (r + 1) : A) ⟶ (S.cycle (r + 1) : A) :=
    Subobject.ofLE (S.boundary (r + 1)) (S.cycle (r + 1))
      (S.boundary_le_cycle (r + 1))
  let e :
      (kernelSubobject (S.cycleToPage (r + 1)) : A) ≅ (S.boundary (r + 1) : A) :=
    Subobject.isoOfEqMk (kernelSubobject (S.cycleToPage (r + 1))) i hKernel
  have hComp :
      e.hom ≫ i = (kernelSubobject (S.cycleToPage (r + 1))).arrow := by
    simpa [e] using
      (Subobject.ofLEMk_comp (X := kernelSubobject (S.cycleToPage (r + 1))) (f := i)
        hKernel.le)
  apply (cancel_epi e.hom).1
  calc
    e.hom ≫ i ≫ S.cycleToPage (r + 1) =
        (kernelSubobject (S.cycleToPage (r + 1))).arrow ≫ S.cycleToPage (r + 1) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ S.cycleToPage (r + 1)) hComp
    _ = 0 := by
          exact kernelSubobject_arrow_comp (S.cycleToPage (r + 1))
    _ = e.hom ≫ 0 := by
          simp

/-- The recursive map `Z_r ⟶ E_r` kills the boundary subobject `B_r ⊆ Z_r`. -/
theorem boundaryToPage_zero (S : ShiftedSpectralSequence T) (r : ℕ+) :
    Subobject.ofLE (S.boundary r) (S.cycle r) (S.boundary_le_cycle r) ≫
      S.cycleToPage r =
    0 := by
  refine PNat.recOn r ?_ ?_
  · -- Proof comment: on the first page, `B₁ = ⊥` and `Z₁ = ⊤`, so the induced map is zero.
    exact S.boundaryToPage_zero_one
  · intro r _
    -- Proof comment: the successor case is exactly the kernel-arrow vanishing above.
    exact S.boundaryToPage_zero_succ r

/-- The canonical morphism from the quotient `Z_r / B_r` to the page object `E_r`. -/
def pageQuotientToPageObject (S : ShiftedSpectralSequence T) (r : ℕ+) :
    cokernel (Subobject.ofLE (S.boundary r) (S.cycle r) (S.boundary_le_cycle r)) ⟶
      (S.page r).obj :=
  cokernel.desc _ (S.cycleToPage r) (S.boundaryToPage_zero r)

/-- The canonical quotient map `Z_r / B_r ⟶ E_r` is an isomorphism. -/
theorem pageQuotientToPageObject_isIso (S : ShiftedSpectralSequence T) (r : ℕ+) :
    IsIso (S.pageQuotientToPageObject r) := by
  refine PNat.recOn r ?_ ?_
  · -- Proof comment: on the first page, the map is the cokernel of the zero inclusion into `E₁`.
    haveI : Epi (S.cycleToPage 1) := S.epi_cycleToPage 1
    have hKernel :
        kernelSubobject (S.cycleToPage 1) =
          Subobject.mk (Subobject.ofLE (S.boundary 1) (S.cycle 1) (S.boundary_le_cycle 1)) := by
      let pageIso : (S.page (pageIndex (1 : ℕ+).natPred)).obj ≅ (S.page 1).obj :=
        eqToIso (by simpa using congrArg (fun s ↦ (S.page s).obj) (pageIndex_natPred 1))
      have hKernelComp :
          kernelSubobject (S.cycleToPage 1) =
            kernelSubobject (stageToPage S (1 : ℕ+).natPred) := by
        change kernelSubobject (stageToPage S (1 : ℕ+).natPred ≫ pageIso.hom) =
          kernelSubobject (stageToPage S (1 : ℕ+).natPred)
        simpa [cycleToPage, pageIso] using
          (kernelSubobject_comp_mono (stageToPage S (1 : ℕ+).natPred) pageIso.hom)
      have hKernelStage :
          kernelSubobject (stageToPage S (1 : ℕ+).natPred) =
            Subobject.mk
              (Subobject.ofLE (S.boundary 1) (S.cycle 1) (S.boundary_le_cycle 1)) := by
        have hKernelZero :
            kernelSubobject ((stageData S 0).toPage) =
              (⊥ : Subobject ((stageData S 0).cycle : A)) := by
          change kernelSubobject ((stageData S 0).toPage) =
            (⊥ : Subobject ((stageData S 0).cycle : A))
          haveI : IsIso ((stageData S 0).toPage) := by
            simpa [stageData] using
              (inferInstance : IsIso ((⊤ : Subobject ((S.page 1).obj)).arrow))
          rw [← Subobject.mk_arrow (kernelSubobject ((stageData S 0).toPage))]
          simpa [stageData] using
            (Subobject.mk_eq_bot_iff_zero
              (f := (kernelSubobject ((stageData S 0).toPage)).arrow)).2
              ((cancel_mono ((stageData S 0).toPage)).1 <|
                by simpa [Category.assoc] using
                  kernelSubobject_arrow_comp ((stageData S 0).toPage))
        have hKernelZeroStage :
            kernelSubobject (stageToPage S (1 : ℕ+).natPred) =
              (⊥ : Subobject ((stageData S 0).cycle : A)) := by
          simpa [stageToPage] using hKernelZero
        have hBoundaryOne :
            Subobject.mk
                (Subobject.ofLE (S.boundary 1) (S.cycle 1) (S.boundary_le_cycle 1)) =
              (⊥ : Subobject ((stageData S 0).cycle : A)) := by
          change Subobject.mk
              (Subobject.ofLE (⊥ : Subobject ((S.page 1).obj))
                (⊤ : Subobject ((S.page 1).obj)) (by simp)) =
            (⊥ : Subobject ((⊤ : Subobject ((S.page 1).obj)) : A))
          apply (Subobject.mk_eq_bot_iff_zero
            (f := Subobject.ofLE (⊥ : Subobject ((S.page 1).obj))
              (⊤ : Subobject ((S.page 1).obj)) (by simp))).2
          apply (cancel_mono ((⊤ : Subobject ((S.page 1).obj)).arrow)).1
          simp [Subobject.ofLE_arrow]
        exact hKernelZeroStage.trans hBoundaryOne.symm
      exact hKernelComp.trans hKernelStage
    exact cokernelDescIsIsoOfEpiOfKernel
      (Subobject.ofLE (S.boundary 1) (S.cycle 1) (S.boundary_le_cycle 1))
      (S.cycleToPage 1) (S.boundaryToPage_zero 1) hKernel
  · intro r _
    -- Proof comment: the successor case uses the already computed kernel of the successor map.
    haveI : Epi (S.cycleToPage (r + 1)) := S.epi_cycleToPage (r + 1)
    exact cokernelDescIsIsoOfEpiOfKernel
      (Subobject.ofLE (S.boundary (r + 1)) (S.cycle (r + 1)) (S.boundary_le_cycle (r + 1)))
      (S.cycleToPage (r + 1))
      (S.boundaryToPage_zero (r + 1))
      (S.boundarySucc_eq_kernel_cycleToPage r)

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
