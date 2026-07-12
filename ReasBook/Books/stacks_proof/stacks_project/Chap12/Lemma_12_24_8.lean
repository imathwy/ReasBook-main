import Mathlib
import StacksProject_2024.Chap12.Definition_12_20_2
import StacksProject_2024.Chap12.Definition_12_24_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {r₀ : ℤ}

/- Domain-style sampling for Lemma 12.24.8:
- primary domain: regularity/coregularity and boundedness for cohomological spectral sequences;
- sampled owner declarations:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.SpectralSequence.cycle`,
  `CategoryTheory.SpectralSequence.boundary`,
  `CategoryTheory.CohomologicalSpectralSequence.IsRegular`,
  `CategoryTheory.CohomologicalSpectralSequence.IsCoregular`;
- best owner abstraction: the canonical owner `CohomologicalSpectralSequence 𝒜 r₀`, together with
  its page-`E_{r₀}` reindexing to the chapter owner `SpectralSequence.cycle`/`boundary`;
- primitive data: the owner pages `(E.page r).X (p, q)`, their differentials `(E.page r).d`, and
  the page-to-page isomorphisms `E.iso`;
- derived API in this file: the source-facing recursive pieces `Z_r^{p,q}` and `B_r^{p,q}` on the
  initial page, the stabilization characterizations of regularity/coregularity, and the boundedness
  implications.
Source/core/bridge triage:
- `source-facing`: the recursive pieces `cycle`, `boundary` and the predicates `IsRegular`,
  `IsCoregular`, `IsBounded`, `IsBoundedBelow`, `IsBoundedAbove`;
- `core/canonical`: the spectral sequence `E : CohomologicalSpectralSequence 𝒜 r₀`;
- `bridge/view`: the reindexing `toInitialPageSpectralSequence` from the initial page `E_{r₀}` to
  the page-`E₁` owner used by `SpectralSequence.cycle` and `SpectralSequence.boundary`. -/

/-- Bridge/view layer: reindex a cohomological spectral sequence from its initial page `E_{r₀}`
as a page-`E₁` spectral sequence so that the canonical recursive pieces `Z_r` and `B_r` are
reused from `SpectralSequence.cycle` and `SpectralSequence.boundary` instead of being duplicated
locally. -/
abbrev toInitialPageSpectralSequence (E : CohomologicalSpectralSequence 𝒜 r₀) :
    SpectralSequence 𝒜
      (fun r ↦ ComplexShape.up' (⟨r₀ + r - 1, 1 - (r₀ + r - 1)⟩ : ℤ × ℤ)) 1 where
  page r hr := E.page (r₀ + r - 1) (by omega)
  iso r r' pq hrr' hr := by
    simpa using E.iso (r₀ + r - 1) (r₀ + r' - 1) pq (by omega) (by omega)

/-- The page-`E₁` owner index corresponding to the actual page number `r ≥ r₀`. -/
private def initialPageNumber (r₀ r : ℤ) (hr : r₀ ≤ r) : ℕ+ :=
  ⟨Int.toNat (r - r₀ + 1), by omega⟩

/-- Helper for Lemma 12.24.8: shifting the actual page number by one shifts the owner positive
page index by one as well. -/
private theorem initialPageNumber_succ {r₀ r : ℤ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r + 1) :
    initialPageNumber r₀ (r + 1) hr' = initialPageNumber r₀ r hr + 1 := by
  -- Both page numbers are determined by the same integer arithmetic on `r - r₀ + 1`.
  apply PNat.eq
  simp [initialPageNumber]
  omega

/-- Helper for Lemma 12.24.8: converting the owner positive page index back to an actual page
number recovers the original page. -/
private theorem initialPageNumber_page_eq {r₀ r : ℤ} (hr : r₀ ≤ r) :
    r₀ + ((initialPageNumber r₀ r hr : ℕ+) : ℤ) - 1 = r := by
  -- Unfold the positive page index and simplify the integer arithmetic once.
  simp [initialPageNumber]
  omega

/-- Helper for Lemma 12.24.8: transporting vanishing of the outgoing owner differential from the
reindexed owner page to the explicit page `r`. -/
private theorem toInitialPageSpectralSequence_outgoing_zero_iff_page_zero
    (E : CohomologicalSpectralSequence 𝒜 r₀) (p q r : ℤ) (rPos : ℕ+)
    (howner : r₀ ≤ r₀ + (rPos : ℤ) - 1) (hr : r₀ ≤ r)
    (hpage : r₀ + (rPos : ℤ) - 1 = r) :
    (E.page (r₀ + (rPos : ℤ) - 1) howner).d
        (p, q)
        (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1) = 0 ↔
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0 := by
  -- Route correction: once `rPos` is an independent parameter, eliminating `hpage` rewrites the
  -- two differentials without entangling the local definition of the owner page index.
  cases hpage
  simp

/-- Helper for Lemma 12.24.8: transporting vanishing of the incoming owner differential from the
reindexed owner page to the explicit page `r`. -/
private theorem toInitialPageSpectralSequence_incoming_zero_iff_page_zero
    (E : CohomologicalSpectralSequence 𝒜 r₀) (p q r : ℤ) (rPos : ℕ+)
    (howner : r₀ ≤ r₀ + (rPos : ℤ) - 1) (hr : r₀ ≤ r)
    (hpage : r₀ + (rPos : ℤ) - 1 = r) :
    (E.page (r₀ + (rPos : ℤ) - 1) howner).d
        (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
        (p, q) = 0 ↔
      (E.page r hr).d (p - r, q + r - 1) (p, q) = 0 := by
  -- The same independent-index transport works for the incoming differential.
  cases hpage
  simp

/-- The source-facing cycle piece `Z_r^{p,q}` on the initial-page entry corresponding to
`E_{r₀}^{p,q}` under the canonical reindexing to a page-`E₁` spectral sequence. -/
abbrev cycle (E : CohomologicalSpectralSequence 𝒜 r₀) (pq : ℤ × ℤ)
    (r : ℤ) (hr : r₀ ≤ r) :=
  E.toInitialPageSpectralSequence.cycle pq (initialPageNumber r₀ r hr)

/-- The source-facing boundary piece `B_r^{p,q}` on the initial-page entry corresponding to
`E_{r₀}^{p,q}` under the canonical reindexing to a page-`E₁` spectral sequence. -/
abbrev boundary (E : CohomologicalSpectralSequence 𝒜 r₀) (pq : ℤ × ℤ)
    (r : ℤ) (hr : r₀ ≤ r) :=
  E.toInitialPageSpectralSequence.boundary pq (initialPageNumber r₀ r hr)

/-- Helper for Lemma 12.24.8: the kernel of a composite is the pullback of the later kernel along
the earlier map. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback f).obj (kernelSubobject g)).factorThru
        (kernelSubobject (f ≫ g)).arrow ?_)
      ?_
    · exact (pullback_factors_iff f (kernelSubobject g) (kernelSubobject (f ≫ g)).arrow).2 <| by
        rw [kernelSubobject_factors_iff, Category.assoc]
        exact kernelSubobject_arrow_comp (f ≫ g)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback f (kernelSubobject g)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Lemma 12.24.8: pulling back the zero subobject along a morphism recovers its
kernel subobject. -/
private theorem pullback_bot_eq_kernel {X Y : 𝒜} (f : X ⟶ Y) :
    (Subobject.pullback f).obj (⊥ : Subobject Y) = kernelSubobject f := by
  apply le_antisymm
  · -- The pullback of `⊥` consists of the points mapping to zero, so it lies in the kernel.
    exact le_kernelSubobject _ _ <| by
      simpa using (Subobject.isPullback f (⊥ : Subobject Y)).w.symm
  · -- Conversely, the kernel arrow factors through that pullback because it composes to zero.
    have hFactors :
        ((Subobject.pullback f).obj (⊥ : Subobject Y)).Factors (kernelSubobject f).arrow :=
      (Limits.pullback_factors_iff (f := f) (y := (⊥ : Subobject Y))
        (h := (kernelSubobject f).arrow)).2 <| by
          rw [Subobject.bot_factors_iff_zero]
          exact kernelSubobject_arrow_comp f
    exact Subobject.le_of_comm
      (((Subobject.pullback f).obj (⊥ : Subobject Y)).factorThru
        (kernelSubobject f).arrow hFactors)
      (((Subobject.pullback f).obj (⊥ : Subobject Y)).factorThru_arrow
        (kernelSubobject f).arrow hFactors)

/-- Helper for Lemma 12.24.8: on each owner page, the source-facing boundary piece is exactly the
kernel of the canonical map from the cycle piece to the page entry. -/
private theorem boundary_subobject_eq_kernel_cycleToPage
    {C : Type u} [Category.{v} C] [Abelian C]
    {κ : Type*} {c : ℤ → ComplexShape κ}
    (S : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Subobject.mk (Subobject.ofLE (S.boundary pq r) (S.cycle pq r) (S.boundary_le_cycle pq r)) =
      kernelSubobject (S.cycleToPage pq r) := by
  let ι : (S.boundary pq r : C) ⟶ (S.cycle pq r : C) :=
    Subobject.ofLE (S.boundary pq r) (S.cycle pq r) (S.boundary_le_cycle pq r)
  let T : ShortComplex C :=
    ShortComplex.mk ι (S.cycleToPage pq r) (S.boundaryToPage_zero pq r)
  have hπ : cokernel.π ι ≫ S.pageQuotientToPage pq r = S.cycleToPage pq r :=
    cokernel.π_desc ι (S.cycleToPage pq r) (S.boundaryToPage_zero pq r)
  have hColim : IsColimit (CokernelCofork.ofπ (S.cycleToPage pq r) (S.boundaryToPage_zero pq r)) := by
    letI : IsIso (S.pageQuotientToPage pq r) := S.pageQuotientToPage_isIso pq r
    letI : Epi (S.cycleToPage pq r) := by
      rw [← hπ]
      infer_instance
    -- Transport the universal property of the canonical cokernel along the isomorphism
    -- `pageQuotientToPage`.
    refine CokernelCofork.IsColimit.ofπ _ _
      (fun {Z} k hk ↦ inv (S.pageQuotientToPage pq r) ≫ cokernel.desc ι k hk)
      ?_ ?_
    · intro Z k hk
      rw [← hπ, Category.assoc, IsIso.hom_inv_id_assoc, cokernel.π_desc]
    · intro Z k hk m hm
      apply (cancel_epi (S.cycleToPage pq r)).1
      rw [hm, ← hπ, Category.assoc, IsIso.hom_inv_id_assoc, cokernel.π_desc]
  have hExact : T.Exact := by
    -- Once `cycleToPage` is identified as a cokernel of the boundary inclusion, exactness is
    -- immediate.
    apply ShortComplex.exact_of_g_is_cokernel
    simpa [T] using hColim
  have hImageKernel : imageSubobject ι = kernelSubobject (S.cycleToPage pq r) := by
    -- Exactness identifies the image of the boundary inclusion with the kernel of `cycleToPage`.
    simpa [T] using (ShortComplex.exact_iff_image_eq_kernel (S := T)).1 hExact
  calc
    Subobject.mk ι = imageSubobject ι := by
      symm
      exact imageSubobject_mono ι
    _ = kernelSubobject (S.cycleToPage pq r) := hImageKernel

/-- Helper for Lemma 12.24.8: the canonical map `Z_r^{pq} ⟶ E_r^{pq}` is always an epimorphism
because it factors through the quotient `Z_r^{pq} / B_r^{pq}`, and that quotient is canonically
isomorphic to the page entry `E_r^{pq}`. -/
private theorem cycleToPage_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    {κ : Type*} {c : ℤ → ComplexShape κ}
    (S : SpectralSequence C c 1) (pq : κ) (r : ℕ+) :
    Epi (S.cycleToPage pq r) := by
  let ι : (S.boundary pq r : C) ⟶ (S.cycle pq r : C) :=
    Subobject.ofLE (S.boundary pq r) (S.cycle pq r) (S.boundary_le_cycle pq r)
  have hπ : cokernel.π ι ≫ S.pageQuotientToPage pq r = S.cycleToPage pq r :=
    cokernel.π_desc ι (S.cycleToPage pq r) (S.boundaryToPage_zero pq r)
  letI : IsIso (S.pageQuotientToPage pq r) := S.pageQuotientToPage_isIso pq r
  -- The quotient projection is epi, and composing it with the page isomorphism recovers
  -- `cycleToPage`.
  rw [← hπ]
  infer_instance

/-- Helper for Lemma 12.24.8: applying `Subobject.exists` to a subobject recovers the image of
its arrow followed by the ambient morphism. -/
private theorem exists_obj_eq_imageSubobject_comp {X Y : 𝒜} (f : X ⟶ Y) (S : Subobject X) :
    (Subobject.exists f).obj S = imageSubobject (S.arrow ≫ f) := by
  -- Route correction: the boundary proof needs this pushforward identity locally in this file,
  -- so we replay the earlier chapter proof here instead of reproving around the missing private
  -- API.
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage f S ≪≫ (imageSubobjectIso _).symm)
  calc
    ((Subobject.existsIsoImage f S).hom ≫ (imageSubobjectIso (S.arrow ≫ f)).inv) ≫
        (imageSubobject (S.arrow ≫ f)).arrow =
      (Subobject.existsIsoImage f S).hom ≫ image.ι (S.arrow ≫ f) := by
        simp [Category.assoc]
    _ = ((Subobject.exists f).obj S).arrow := by
        simpa [Subobject.existsIsoImage] using
          (Over.w ((Subobject.existsCompRepresentativeIso f).app S).hom.hom)

/-- Helper for Lemma 12.24.8: pushing forward a pullback along an epimorphism recovers the
original subobject. -/
private theorem exists_pullback_eq_of_epi {X Y : 𝒜} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    (Subobject.exists f).obj ((Subobject.pullback f).obj P) = P := by
  -- First identify the pushed-forward pullback with the image of the original subobject arrow.
  have hImage : imageSubobject (((Subobject.pullback f).obj P).arrow ≫ f) = P := by
    rw [← (Subobject.isPullback f P).w]
    haveI : Epi (Subobject.pullbackπ f P) :=
      Abelian.epi_fst_of_isLimit P.arrow f (Subobject.isPullback f P).isLimit
    have hle :
        imageSubobject (Subobject.pullbackπ f P ≫ P.arrow) ≤ imageSubobject P.arrow :=
      imageSubobject_comp_le (Subobject.pullbackπ f P) P.arrow
    haveI : Epi (Subobject.ofLE _ _ hle) :=
      imageSubobject_comp_le_epi_of_epi (Subobject.pullbackπ f P) P.arrow
    haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
    have hEq :
        imageSubobject (Subobject.pullbackπ f P ≫ P.arrow) = imageSubobject P.arrow :=
      Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)
    simpa [imageSubobject_mono] using hEq
  -- Then rewrite `Subobject.exists` itself to that image.
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage f ((Subobject.pullback f).obj P) ≪≫
      (imageSubobjectIso _).symm ≪≫
      Subobject.isoOfEq _ _ hImage)
  calc
    ((Subobject.existsIsoImage f ((Subobject.pullback f).obj P)).hom ≫
        (imageSubobjectIso (((Subobject.pullback f).obj P).arrow ≫ f)).inv ≫
        (Subobject.isoOfEq
          (imageSubobject (((Subobject.pullback f).obj P).arrow ≫ f))
          P hImage).hom) ≫
        P.arrow =
      (Subobject.existsIsoImage f ((Subobject.pullback f).obj P)).hom ≫
        image.ι (((Subobject.pullback f).obj P).arrow ≫ f) := by
        simp [Category.assoc]
    _ = ((Subobject.exists f).obj ((Subobject.pullback f).obj P)).arrow := by
        simpa [Subobject.existsIsoImage] using
          (Over.w ((Subobject.existsCompRepresentativeIso f).app ((Subobject.pullback f).obj P)).hom.hom)

/-- Helper for Lemma 12.24.8: stabilization of the cycle piece from page `r` to page `r + 1`
is equivalent to vanishing of the outgoing page-`r` differential. -/
private theorem cycle_eq_cycle_succ_iff_page_d_eq_zero
    (E : CohomologicalSpectralSequence 𝒜 r₀) (p q r : ℤ)
    (hr : r₀ ≤ r) (hr' : r₀ ≤ r + 1) :
    E.cycle (p, q) r hr = E.cycle (p, q) (r + 1) hr' ↔
      (E.page r).d (p, q) (p + r, q - r + 1) = 0 := by
  let S := E.toInitialPageSpectralSequence
  let rPos : ℕ+ := initialPageNumber r₀ r hr
  have hsucc : initialPageNumber r₀ (r + 1) hr' = rPos + 1 := by
    simpa [rPos] using initialPageNumber_succ hr hr'
  have hpage : r₀ + (rPos : ℤ) - 1 = r := by
    simpa [rPos] using initialPageNumber_page_eq hr
  have hkernel :
      kernelSubobject ((S.page (rPos : ℤ) (by exact_mod_cast rPos.2)).dFrom (p, q)) =
        kernelSubobject
          ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
            (p, q)
            (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1)) := by
    -- Normalize the owner `dFrom` to the explicit outgoing page differential.
    simpa [S, toInitialPageSpectralSequence] using
      (HomologicalComplex.kernel_from_eq_kernel
        (C := E.page (r₀ + (rPos : ℤ) - 1) (by omega))
        (r := by
          simp [ComplexShape.up']
          omega))
  have hmain :
      S.cycle (p, q) rPos = S.cycle (p, q) (rPos + 1) ↔
        (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
          (p, q)
          (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1) = 0 := by
    -- Rewrite the successor cycle piece by the one-step pullback/kernel formula.
    rw [SpectralSequence.cycle_succ_eq_map_pullback_kernel]
    rw [hkernel]
    constructor
    · intro hEq
      have hPullbackTop :
          (Subobject.pullback (S.cycleToPage (p, q) rPos)).obj
              (kernelSubobject
                ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                  (p, q)
                  (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1))) =
            ⊤ := by
        -- Since `map` along the cycle inclusion is injective, equality upstairs means the
        -- pulled-back kernel must already be the top subobject of `Z_r`.
        apply (Subobject.map_obj_injective (S.cycle (p, q) rPos).arrow)
        simpa [Subobject.map_top, Subobject.mk_arrow] using hEq.symm
      have hKernelComp :
          kernelSubobject
              (S.cycleToPage (p, q) rPos ≫
                (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                  (p, q)
                  (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1)) =
            ⊤ := by
        -- Pulling back the kernel along `cycleToPage` is the kernel of the composite.
        rw [kernelSubobject_comp_eq_pullback, hPullbackTop]
      have hCompZero :
          S.cycleToPage (p, q) rPos ≫
              (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                (p, q)
                (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1) =
            0 := by
        -- If the composite has full kernel, then the composite itself is zero.
        have hArrowComp :=
          kernelSubobject_arrow_comp
            (S.cycleToPage (p, q) rPos ≫
              (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                (p, q)
                (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1))
        rw [hKernelComp] at hArrowComp
        simpa using hArrowComp
      letI : Epi (S.cycleToPage (p, q) rPos) := cycleToPage_epi S (p, q) rPos
      -- The canonical map `Z_r ⟶ E_r` is epi, so the vanishing of the composite forces
      -- the outgoing page differential to vanish.
      exact (cancel_epi (S.cycleToPage (p, q) rPos)).1 <| by
        simpa using hCompZero
    · intro hd
      have hPullbackTop :
          (Subobject.pullback (S.cycleToPage (p, q) rPos)).obj
              (kernelSubobject
                ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                  (p, q)
                  (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1))) =
            ⊤ := by
        -- If the differential vanishes, its kernel is the whole page, and pulling back preserves
        -- that top subobject.
        rw [hd, Limits.kernelSubobject_zero, Subobject.pullback_top]
      -- Mapping the pulled-back top subobject back into `E₁` recovers `Z_r`.
      simpa [Subobject.map_top, Subobject.mk_arrow] using
        (congrArg ((Subobject.map (S.cycle (p, q) rPos).arrow).obj) hPullbackTop).symm
  have hright :
      (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
          (p, q)
          (p + (r₀ + (rPos : ℤ) - 1), q - (r₀ + (rPos : ℤ) - 1) + 1) = 0 ↔
        (E.page r).d (p, q) (p + r, q - r + 1) = 0 := by
    have howner : r₀ ≤ r₀ + (rPos : ℤ) - 1 := by
      omega
    -- Route correction: the final transport is packaged with `rPos` as an independent parameter,
    -- so the closing lemma only composes the stabilized owner equivalence with that transport.
    simpa using
      (toInitialPageSpectralSequence_outgoing_zero_iff_page_zero E p q r rPos howner hr hpage)
  -- Unfold the source-facing notation and rewrite the successor index back to `rPos + 1`.
  simpa [cycle, rPos, hsucc] using hmain.trans hright

/-- Helper for Lemma 12.24.8: stabilization of the boundary piece from page `r` to page `r + 1`
is equivalent to vanishing of the incoming page-`r` differential. -/
private theorem boundary_eq_boundary_succ_iff_page_d_eq_zero
    (E : CohomologicalSpectralSequence 𝒜 r₀) (p q r : ℤ)
    (hr : r₀ ≤ r) (hr' : r₀ ≤ r + 1) :
    E.boundary (p, q) r hr = E.boundary (p, q) (r + 1) hr' ↔
      (E.page r).d (p - r, q + r - 1) (p, q) = 0 := by
  let S := E.toInitialPageSpectralSequence
  let rPos : ℕ+ := initialPageNumber r₀ r hr
  have hsucc : initialPageNumber r₀ (r + 1) hr' = rPos + 1 := by
    simpa [rPos] using initialPageNumber_succ hr hr'
  have hpage : r₀ + (rPos : ℤ) - 1 = r := by
    simpa [rPos] using initialPageNumber_page_eq hr
  have himage :
      imageSubobject ((S.page (rPos : ℤ) (by exact_mod_cast rPos.2)).dTo (p, q)) =
        imageSubobject
          ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
            (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
            (p, q)) := by
    -- Normalize the owner `dTo` to the explicit incoming page differential.
    simpa [S, toInitialPageSpectralSequence] using
      (HomologicalComplex.image_to_eq_image
        (C := E.page (r₀ + (rPos : ℤ) - 1) (by omega))
        (r := by
          simp [ComplexShape.up']))
  have hBoundaryMap :
      S.boundary (p, q) rPos =
        (Subobject.map (S.cycle (p, q) rPos).arrow).obj
          (Subobject.mk
            (Subobject.ofLE
              (S.boundary (p, q) rPos)
              (S.cycle (p, q) rPos)
              (S.boundary_le_cycle (p, q) rPos))) := by
    -- `B_r` is exactly the image in `E₁` of its corresponding subobject inside `Z_r`.
    simp [Subobject.map_mk, Subobject.ofLE_arrow, Subobject.mk_arrow]
  have hmain :
      S.boundary (p, q) rPos = S.boundary (p, q) (rPos + 1) ↔
        (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
          (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
          (p, q) = 0 := by
    -- Rewrite the successor boundary piece by the one-step pullback/image formula.
    rw [hBoundaryMap, SpectralSequence.boundary_succ_eq_map_pullback_image]
    rw [himage]
    constructor
    · intro hEq
      have hInside :
          Subobject.mk
              (Subobject.ofLE
                (S.boundary (p, q) rPos)
                (S.cycle (p, q) rPos)
                (S.boundary_le_cycle (p, q) rPos)) =
            (Subobject.pullback (S.cycleToPage (p, q) rPos)).obj
              (imageSubobject
                ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                  (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
                  (p, q))) := by
        -- Again, injectivity of `map` lets us work inside the cycle piece `Z_r`.
        exact (Subobject.map_obj_injective (S.cycle (p, q) rPos).arrow) hEq
      have hKernelEq :
          kernelSubobject (S.cycleToPage (p, q) rPos) =
            (Subobject.pullback (S.cycleToPage (p, q) rPos)).obj
              (imageSubobject
                ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                  (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
                  (p, q))) := by
        -- Replace the abstract `B_r ⊆ Z_r` with the kernel description of `cycleToPage`.
        simpa [boundary_subobject_eq_kernel_cycleToPage S (p, q) rPos] using hInside
      letI : Epi (S.cycleToPage (p, q) rPos) := cycleToPage_epi S (p, q) rPos
      have hPush :
          (Subobject.exists (S.cycleToPage (p, q) rPos)).obj
              (kernelSubobject (S.cycleToPage (p, q) rPos)) =
            (Subobject.exists (S.cycleToPage (p, q) rPos)).obj
              ((Subobject.pullback (S.cycleToPage (p, q) rPos)).obj
                (imageSubobject
                  ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                    (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
                    (p, q)))) :=
        congrArg ((Subobject.exists (S.cycleToPage (p, q) rPos)).obj) hKernelEq
      have hLeft :
          (Subobject.exists (S.cycleToPage (p, q) rPos)).obj
              (kernelSubobject (S.cycleToPage (p, q) rPos)) =
            ⊥ := by
        -- Pushing forward the kernel along its own map gives the zero image.
        rw [exists_obj_eq_imageSubobject_comp, kernelSubobject_arrow_comp, Limits.imageSubobject_zero]
      have hImageEq :
          imageSubobject
              ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
                (p, q)) =
            ⊥ := by
        -- Pushing forward the pullback along the epi `cycleToPage` recovers the incoming image.
        rw [exists_pullback_eq_of_epi
          (S.cycleToPage (p, q) rPos)
          (imageSubobject
            ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
              (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
              (p, q)))] at hPush
        rw [hLeft] at hPush
        exact hPush.symm
      let d :
          (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).X
              (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1) ⟶
            (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).X (p, q) :=
        (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
          (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
          (p, q)
      have hImageEq' : imageSubobject d = ⊥ := by
        simpa [d] using hImageEq
      have hFactors : (imageSubobject d).Factors d := by
        simpa using (Limits.imageSubobject_factors_comp_self (f := d) (𝟙 _))
      have hBotFactors : (⊥ : Subobject ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).X (p, q))).Factors d := by
        simpa [hImageEq'] using hFactors
      -- If the image factors through the zero subobject, the differential must vanish.
      exact (Subobject.bot_factors_iff_zero d).1 hBotFactors
    · intro hd
      have hInside :
          Subobject.mk
              (Subobject.ofLE
                (S.boundary (p, q) rPos)
                (S.cycle (p, q) rPos)
                (S.boundary_le_cycle (p, q) rPos)) =
            (Subobject.pullback (S.cycleToPage (p, q) rPos)).obj
              (imageSubobject
                ((E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
                  (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
                  (p, q))) := by
        -- Vanishing of the incoming differential turns the pulled-back image into the pullback of
        -- the zero subobject, i.e. the kernel of `cycleToPage`.
        rw [boundary_subobject_eq_kernel_cycleToPage]
        rw [hd, Limits.imageSubobject_zero, pullback_bot_eq_kernel]
      -- Mapping that equality back into `E₁` recovers the equality of boundary pieces.
      simpa [hBoundaryMap] using
        congrArg ((Subobject.map (S.cycle (p, q) rPos).arrow).obj) hInside
  have hright :
      (E.page (r₀ + (rPos : ℤ) - 1) (by omega)).d
          (p - (r₀ + (rPos : ℤ) - 1), q + (r₀ + (rPos : ℤ) - 1) - 1)
          (p, q) = 0 ↔
        (E.page r).d (p - r, q + r - 1) (p, q) = 0 := by
    have howner : r₀ ≤ r₀ + (rPos : ℤ) - 1 := by
      omega
    -- Route correction: package the final incoming-differential transport separately from the
    -- already-verified image/pullback argument.
    simpa using
      (toInitialPageSpectralSequence_incoming_zero_iff_page_zero E p q r rPos howner hr hpage)
  -- Unfold the source-facing notation and rewrite the successor index back to `rPos + 1`.
  simpa [boundary, rPos, hsucc] using hmain.trans hright

/-- Lemma 12.24.8 (1): a cohomological spectral sequence is regular exactly when, for every
bidegree `(p,q)`, the source-facing cycle pieces `Z_r^{p,q}` eventually stabilize. -/
@[stacks 0BDV]
theorem isRegular_iff_eventually_cycle_eq
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsRegular E ↔
      ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
        E.cycle (p, q) r hr = E.cycle (p, q) (r + 1) (by omega) := by
  constructor
  · intro hE
    intro p q
    rcases hE p q with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro r hr hbr
    have hr_succ : r₀ ≤ r + 1 := by
      omega
    -- The pagewise stabilization criterion converts regularity into eventual equality of cycles.
    exact (cycle_eq_cycle_succ_iff_page_d_eq_zero E p q r hr hr_succ).2 (hb hr hbr)
  · intro hE
    intro p q
    rcases hE p q with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro r hr hbr
    have hr_succ : r₀ ≤ r + 1 := by
      omega
    have hstable := hb hr hbr
    -- The same criterion read backwards turns eventual cycle stabilization into regularity.
    exact (cycle_eq_cycle_succ_iff_page_d_eq_zero E p q r hr hr_succ).1 hstable

/-- Lemma 12.24.8 (2): a cohomological spectral sequence is coregular exactly when, for every
bidegree `(p,q)`, the source-facing boundary pieces `B_r^{p,q}` eventually stabilize. -/
@[stacks 0BDV]
theorem isCoregular_iff_eventually_boundary_eq
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsCoregular E ↔
      ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
        E.boundary (p, q) r hr = E.boundary (p, q) (r + 1) (by omega) := by
  constructor
  · intro hE
    intro p q
    rcases hE p q with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro r hr hbr
    have hr_succ : r₀ ≤ r + 1 := by
      omega
    -- The boundary-side stabilization criterion converts coregularity into eventual equality.
    exact (boundary_eq_boundary_succ_iff_page_d_eq_zero E p q r hr hr_succ).2 (hb hr hbr)
  · intro hE
    intro p q
    rcases hE p q with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro r hr hbr
    have hr_succ : r₀ ≤ r + 1 := by
      omega
    have hstable := hb hr hbr
    -- Reading the same criterion backwards recovers coregularity from eventual boundary equality.
    exact (boundary_eq_boundary_succ_iff_page_d_eq_zero E p q r hr hr_succ).1 hstable

section

variable (E : CohomologicalSpectralSequence 𝒜 r₀)

-- Proof sketch: boundedness on each initial antidiagonal is equivalent to having both an upper and
-- a lower eventual vanishing bound on that antidiagonal; translate between the finite-support
-- condition of `IsBounded` and the two one-sided eventual-vanishing conditions.
/-- Lemma 12.24.8 (3): a cohomological spectral sequence is bounded exactly when it is both
bounded below and bounded above. -/
@[stacks 0BDV]
theorem isBounded_iff_isBoundedBelow_and_isBoundedAbove :
    IsBounded E ↔ IsBoundedBelow E ∧ IsBoundedAbove E := by
  constructor
  · intro hE
    refine ⟨(isBoundedBelow_iff_bddAbove E).2 ?_, (isBoundedAbove_iff_bddBelow E).2 ?_⟩
    · intro n
      exact (Set.finite_iff_bddBelow_bddAbove.mp (hE n)).2
    · intro n
      exact (Set.finite_iff_bddBelow_bddAbove.mp (hE n)).1
  · rintro ⟨hbelow, habove⟩ n
    exact (Set.finite_iff_bddBelow_bddAbove.2
      ⟨((isBoundedAbove_iff_bddBelow E).1 habove) n,
        ((isBoundedBelow_iff_bddAbove E).1 hbelow) n⟩)

-- Proof sketch: the page transition isomorphism identifies `E_{s+1}^{p,q}` with the homology of
-- the short complex extracted from the `s`th page, so vanishing of `E_s^{p,q}` forces vanishing
-- of the same bidegree on every later page by induction.
/-- If an entry on the initial page is zero, then the corresponding entry on every later page is
zero. -/
theorem isZero_pageObj_of_isZero_initialPageObj
    {pq : ℤ × ℤ} {r : ℤ}
    (h₀ : IsZero ((E.page r₀).X pq)) (hr : r₀ ≤ r) :
    IsZero ((E.page r).X pq) := by
  induction r, hr using Int.le_induction with
  | base =>
      exact h₀
  | succ s hs hsZero =>
      let c : ComplexShape (ℤ × ℤ) := ComplexShape.up' (⟨s, 1 - s⟩ : ℤ × ℤ)
      refine IsZero.of_iso ?_ (E.iso s (s + 1) pq).symm
      simpa [HomologicalComplex.homology] using
        (ShortComplex.isZero_homology_of_isZero_X₂
          ((E.page s).sc' (c.prev pq) pq (c.next pq))
          hsZero)

-- Proof sketch: if the initial page is eventually zero for large `p` on each antidiagonal, then
-- for fixed `(p,q)` the outgoing targets `E_r^{p + r, q - r + 1}` are zero for all sufficiently
-- large `r`, so the outgoing differentials vanish and the spectral sequence is regular.
/-- Lemma 12.24.8 (4): a bounded-below cohomological spectral sequence is regular. -/
@[stacks 0BDV]
theorem isRegular_of_isBoundedBelow
    (hE : IsBoundedBelow E) : IsRegular E := by
  intro p q
  rcases hE (p + q + 1) with ⟨b, hb⟩
  refine ⟨b - p, ?_⟩
  intro r hr hbr
  have hp : b ≤ p + r := by
    omega
  have hq : p + q + 1 - (p + r) = q - r + 1 := by
    omega
  have h₀ : IsZero ((E.page r₀).X (p + r, q - r + 1)) := by
    simpa [hq] using hb hp
  have hzero : IsZero ((E.page r).X (p + r, q - r + 1)) :=
    isZero_pageObj_of_isZero_initialPageObj E h₀ hr
  exact hzero.eq_zero_of_tgt _

-- Proof sketch: if the initial page is eventually zero for small `p` on each antidiagonal, then
-- for fixed `(p,q)` the sources `E_r^{p - r, q + r - 1}` of the incoming differentials are zero
-- for all sufficiently large `r`, so those differentials vanish and the spectral sequence is
-- coregular.
/-- Lemma 12.24.8 (5): a bounded-above cohomological spectral sequence is coregular. -/
@[stacks 0BDV]
theorem isCoregular_of_isBoundedAbove
    (hE : IsBoundedAbove E) : IsCoregular E := by
  intro p q
  rcases hE (p + q - 1) with ⟨b, hb⟩
  refine ⟨p - b, ?_⟩
  intro r hr hbr
  have hp : p - r ≤ b := by
    omega
  have hq : p + q - 1 - (p - r) = q + r - 1 := by
    omega
  have h₀ : IsZero ((E.page r₀).X (p - r, q + r - 1)) := by
    simpa [hq] using hb hp
  have hzero : IsZero ((E.page r).X (p - r, q + r - 1)) :=
    isZero_pageObj_of_isZero_initialPageObj E h₀ hr
  exact hzero.eq_zero_of_src _

end

end CohomologicalSpectralSequence
end CategoryTheory
