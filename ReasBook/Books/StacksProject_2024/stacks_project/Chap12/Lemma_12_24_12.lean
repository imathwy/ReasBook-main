import StacksProject_2024.Chap12.Definition_12_11_1
import StacksProject_2024.Chap12.Lemma_12_10_3
import StacksProject_2024.Chap12.Lemma_12_24_2
import StacksProject_2024.Chap12.Lemma_12_24_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]

namespace DecreasingFiltration

/-- Helper for Lemma 12.24.12: a filtration stage equal to the zero subobject is canonically
isomorphic to the zero object. -/
noncomputable lemma stageIsoZeroOfEqBot {A : 𝒜} (F : DecreasingFiltration A) (p : ℤ)
    (hp : F.obj p = ⊥) : (F.obj p : 𝒜) ≅ 0 := by
  -- Replace the stage by the canonical zero subobject.
  refine Subobject.isoOfEqMk (F.obj p) (0 : 0 ⟶ A) ?_
  simpa [Subobject.bot_eq_zero] using hp

/-- Helper for Lemma 12.24.12: a stage equal to the zero subobject has zero underlying object. -/
lemma stage_isZero_of_eq_bot {A : 𝒜} (F : DecreasingFiltration A) (p : ℤ)
    (hp : F.obj p = ⊥) : IsZero (F.obj p : 𝒜) := by
  -- Transport the zero-object witness across the canonical stage isomorphism.
  exact (Limits.isZero_zero 𝒜).of_iso (F.stageIsoZeroOfEqBot p hp).symm

/-- Helper for Lemma 12.24.12: a top filtration stage identifies with the ambient object. -/
noncomputable lemma stageIsoOfEqTop {A : 𝒜} (F : DecreasingFiltration A) (p : ℤ)
    (hp : F.obj p = ⊤) : (F.obj p : 𝒜) ≅ A := by
  -- The stage arrow is an isomorphism exactly for the top subobject.
  letI : IsIso (F.obj p).arrow := (Subobject.isIso_arrow_iff_eq_top (F.obj p)).2 hp
  exact asIso (F.obj p).arrow

/-- Helper for Lemma 12.24.12: a zero graded piece makes the adjacent stage inclusion an
isomorphism. -/
lemma isIso_stageInclusion_of_gradedPiece_isZero {A : 𝒜} (F : DecreasingFiltration A) (p : ℤ)
    (hp : IsZero (F.gradedPiece p)) : IsIso (F.stageInclusion p) := by
  -- The graded piece is the cokernel of the stage inclusion, so zero cokernel gives epi.
  have hEpi : Epi (F.stageInclusion p) := by
    exact (epi_iff_isZero_cokernel (F.stageInclusion p)).2 (by
      simpa [DecreasingFiltration.gradedPiece] using hp)
  -- In an abelian category the stage inclusion is already mono.
  exact isIso_of_mono_of_epi (F.stageInclusion p)

/-- Helper for Lemma 12.24.12: if a finite filtration has zero graded pieces in every degree,
then the ambient object is zero. -/
lemma isZero_obj_of_isFinite_of_gradedPiece_isZero {A : 𝒜} (F : DecreasingFiltration A)
    (hfin : F.IsFinite) (hgraded : ∀ p : ℤ, IsZero (F.gradedPiece p)) : IsZero A := by
  rcases hfin with ⟨t, b, htop, hbot⟩
  have hstageIso : ∀ p : ℤ, IsIso (F.stageInclusion p) := by
    intro p
    exact F.isIso_stageInclusion_of_gradedPiece_isZero p (hgraded p)
  by_cases hbt : b ≤ t
  · -- If the zero stage occurs no later than the top stage, the top stage is already zero.
    have hstageBot : F.obj t = ⊥ := by
      apply bot_unique
      simpa [hbot] using F.antitone_obj hbt
    have hzeroStage : IsZero (F.obj t : 𝒜) := F.stage_isZero_of_eq_bot t hstageBot
    exact IsZero.of_iso hzeroStage (F.stageIsoOfEqTop t htop)
  · -- Otherwise descend from the bottom stage and use the stage isomorphisms.
    have htb : t < b := lt_of_not_ge hbt
    have hzeroBottom : IsZero (F.obj b : 𝒜) := F.stage_isZero_of_eq_bot b hbot
    have hdesc : ∀ k : ℕ, IsZero (F.obj (b - k) : 𝒜) := by
      intro k
      induction k with
      | zero =>
          simpa using hzeroBottom
      | succ k ih =>
          have hsource :
              IsZero (F.obj ((b - (k + 1)) + 1) : 𝒜) := by
            have hEq : b - k = (b - (k + 1)) + 1 := by
              omega
            simpa [hEq] using ih
          exact IsZero.of_iso hsource (asIso (F.stageInclusion (b - (k + 1))))
    let d : ℕ := Int.toNat (b - t)
    have hd : (d : ℤ) = b - t := by
      have hnonneg : 0 ≤ b - t := by
        omega
      simpa [d] using Int.toNat_of_nonneg hnonneg
    have hzeroStage : IsZero (F.obj t : 𝒜) := by
      have hEq : b - d = t := by
        omega
      simpa [hEq] using hdesc d
    exact IsZero.of_iso hzeroStage (F.stageIsoOfEqTop t htop)

/-- Helper for Lemma 12.24.12: a nonzero object with a finite filtration has a nonzero graded
piece. -/
lemma exists_nonzero_gradedPiece_of_nonzero_of_isFinite {A : 𝒜} (F : DecreasingFiltration A)
    (hA : ¬ IsZero A) (hfin : F.IsFinite) :
    ∃ p : ℤ, ¬ IsZero (F.gradedPiece p) := by
  by_contra h
  apply hA
  refine F.isZero_obj_of_isFinite_of_gradedPiece_isZero hfin ?_
  intro p
  by_contra hp
  exact h ⟨p, hp⟩

/-- Helper for Lemma 12.24.12: in the ambient Grothendieck group, a finite filtration window
telescopes into the sum of its graded-piece classes plus the terminal stage. -/
lemma k0_eq_sum_gradedPieces_window_ambient {A : 𝒜} (F : DecreasingFiltration A) :
    ∀ a : ℤ, ∀ d : ℕ,
      K₀[(F.obj a : 𝒜)] =
        (Finset.sum (Finset.range d) fun i ↦ K₀[(F.gradedPiece (a + i) : 𝒜)]) +
          K₀[(F.obj (a + d) : 𝒜)] := by
  intro a d
  induction d generalizing a with
  | zero =>
      -- The empty window contributes no graded pieces.
      simp
  | succ d ih =>
      let S : ShortComplex 𝒜 :=
        ShortComplex.mk
          (F.stageInclusion a)
          (cokernel.π (F.stageInclusion a))
          (cokernel.condition _)
      have hS : S.ShortExact := by
        -- The canonical row `0 ⟶ F^(a + 1) ⟶ F^a ⟶ gr^a(F) ⟶ 0` is short exact.
        refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
        exact ShortComplex.exact_cokernel (F.stageInclusion a)
      have hstep :
          K₀[(F.obj a : 𝒜)] =
            K₀[(F.obj (a + 1) : 𝒜)] + K₀[(F.gradedPiece a : 𝒜)] := by
        -- Read the stage row in `K₀`.
        simpa [S, DecreasingFiltration.gradedPiece, add_comm] using
          (AbelianK0.of_shortExact S hS)
      calc
        K₀[(F.obj a : 𝒜)]
            = K₀[(F.gradedPiece a : 𝒜)] + K₀[(F.obj (a + 1) : 𝒜)] := by
                simpa [add_comm] using hstep
        _ =
            K₀[(F.gradedPiece a : 𝒜)] +
              ((Finset.sum (Finset.range d) fun i ↦
                  K₀[(F.gradedPiece ((a + 1) + i) : 𝒜)]) +
                K₀[(F.obj ((a + 1) + d) : 𝒜)]) := by
                rw [ih (a + 1)]
        _ =
            (K₀[(F.gradedPiece a : 𝒜)] +
                Finset.sum (Finset.range d) fun i ↦
                  K₀[(F.gradedPiece ((a + 1) + i) : 𝒜)]) +
              K₀[(F.obj (a + (d + 1)) : 𝒜)] := by
                simp [add_assoc, add_comm, add_left_comm]
        _ =
            (Finset.sum (Finset.range (d + 1)) fun i ↦
                K₀[(F.gradedPiece (a + i) : 𝒜)]) +
              K₀[(F.obj (a + (d + 1)) : 𝒜)] := by
                rw [Finset.sum_range_succ']
                simp [add_assoc, add_comm, add_left_comm]

end DecreasingFiltration

/-- Helper for Lemma 12.24.12: the zero object has trivial class in `K₀`. -/
lemma k0_zero_eq {A : Type u} [Category.{v} A] [Abelian A] :
    K₀[(0 : A)] = 0 := by
  let S : ShortComplex A := ShortComplex.mk (0 : (0 : A) ⟶ 0) (0 : (0 : A) ⟶ 0) (by simp)
  -- Compute the Grothendieck relation for the zero short exact sequence and cancel one copy.
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 : K₀[(0 : A)] = K₀[(0 : A)] + K₀[(0 : A)] := by
    simpa [S] using (AbelianK0.of_shortExact S hShort)
  have hSub := congrArg (fun z : AbelianK0 A ↦ z - K₀[(0 : A)]) hK0
  have hZero : (0 : AbelianK0 A) = K₀[(0 : A)] := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  simpa using hZero.symm

/-- Helper for Lemma 12.24.12: isomorphic objects have the same `K₀` class. -/
lemma k0_eq_of_iso {A : Type u} [Category.{v} A] [Abelian A] {X Y : A} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  let S : ShortComplex A := ShortComplex.mk e.hom (0 : Y ⟶ 0) (by simp)
  -- Route the isomorphism through the short exact sequence `0 → X → Y → 0`.
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  simpa [S, k0_zero_eq (A := A), add_comm] using (AbelianK0.of_shortExact S hShort).symm

namespace CohomologicalSpectralSequence

/-- Helper for Lemma 12.24.12: if a positive-page entry vanishes, then the corresponding
`E_\infty` term vanishes as well. -/
lemma infinityPage_isZero_of_pageObj_isZero
    (E : CohomologicalSpectralSequence 𝒜 0) (pq : ℤ × ℤ)
    {r : ℤ} (hr : 1 ≤ r)
    (hzero : IsZero ((E.page r).X pq)) :
    IsZero (E.toPageOneSpectralSequence.infinityPage pq) := by
  let S := E.toPageOneSpectralSequence
  let rPos : ℕ+ := ⟨Int.toNat r, by
    have hr' : 0 < r := by
      omega
    exact Int.toNat_pos.2 hr'⟩
  let stageInclusion :
      (S.boundary pq rPos : 𝒜) ⟶ (S.cycle pq rPos : 𝒜) :=
    Subobject.ofLE (S.boundary pq rPos) (S.cycle pq rPos) (S.boundary_le_cycle pq rPos)
  -- The page-`r` quotient identifies with the vanishing page entry, so the stage inclusion is an
  -- isomorphism and the cycle and boundary subobjects agree at that stage.
  have hpageZero : IsZero (S⟦rPos, pq⟧) := by
    simpa [S, SpectralSequence.pageObject, rPos] using hzero
  have hquotZero : IsZero (cokernel stageInclusion) := by
    let hpageIso : cokernel stageInclusion ≅ S⟦rPos, pq⟧ := by
      letI : IsIso (S.pageQuotientToPage pq rPos) :=
        SpectralSequence.pageQuotientToPage_isIso S pq rPos
      exact asIso (S.pageQuotientToPage pq rPos)
    exact IsZero.of_iso hpageZero hpageIso.symm
  have hstageEpi : Epi stageInclusion := by
    exact (epi_iff_isZero_cokernel stageInclusion).2 (by simpa [stageInclusion] using hquotZero)
  have hstageIso : IsIso stageInclusion := by
    exact isIso_of_mono_of_epi stageInclusion
  have hstageEq : S.boundary pq rPos = S.cycle pq rPos := by
    refine Subobject.eq_of_comm (asIso stageInclusion) ?_
    simpa [stageInclusion] using
      (Subobject.ofLE_arrow (X := S.boundary pq rPos) (Y := S.cycle pq rPos)
        (h := S.boundary_le_cycle pq rPos))
  -- Squeezing the eventual boundary and cycle between that equal stage forces `B_∞ = Z_∞`.
  have h∞eq : S.boundaryInfinity pq = S.cycleInfinity pq := by
    apply le_antisymm
    · exact S.boundaryInfinity_le_cycleInfinity pq
    · calc
        S.cycleInfinity pq ≤ S.cycle pq rPos := iInf_le (fun s : ℕ+ ↦ S.cycle pq s) rPos
        _ = S.boundary pq rPos := hstageEq.symm
        _ ≤ S.boundaryInfinity pq := le_iSup (fun s : ℕ+ ↦ S.boundary pq s) rPos
  -- With equal limiting cycle and boundary objects, the `E_∞` quotient is the cokernel of an
  -- identity map, hence zero.
  have h∞stageIso :
      IsIso
        (Subobject.ofLE
          (S.boundaryInfinity pq)
          (S.cycleInfinity pq)
          (S.boundaryInfinity_le_cycleInfinity pq)) := by
    cases h∞eq
    simpa using
      (inferInstance :
        IsIso
          (𝟙 (((S.cycleInfinity pq : Subobject S⟦1, pq⟧) : 𝒜))))
  rw [SpectralSequence.infinityPage_def]
  simpa using
    (Limits.isZero_cokernel_of_epi
      (Subobject.ofLE
        (S.boundaryInfinity pq)
        (S.cycleInfinity pq)
        (S.boundaryInfinity_le_cycleInfinity pq)))

/-- Helper for Lemma 12.24.12: once an `E_∞` term is nonzero, every positive page at the same
bidegree is nonzero. -/
lemma nonzero_pageObj_of_nonzero_infinityPage
    (E : CohomologicalSpectralSequence 𝒜 0)
    (hbounded : CohomologicalSpectralSequence.IsBounded E) (pq : ℤ × ℤ)
    {r : ℤ} (hr : 1 ≤ r)
    (hinfty : ¬ IsZero (E.toPageOneSpectralSequence.infinityPage pq)) :
    ¬ IsZero ((E.page r).X pq) := by
  -- Route correction: for nonvanishing transfer it is enough to note that a zero page entry makes
  -- the page quotient `Z_r / B_r` zero, hence `B_r = Z_r`, which already forces `E_∞` to vanish.
  intro hzero
  exact hinfty (infinityPage_isZero_of_pageObj_isZero E pq hr hzero)

/-- Helper for Lemma 12.24.12: once the cycle and boundary pieces have stabilized at a positive
page, the corresponding page entry is canonically isomorphic to the `E_\infty` term. -/
noncomputable lemma pageObj_iso_infinityPage_of_stable
    (E : CohomologicalSpectralSequence 𝒜 0) (pq : ℤ × ℤ)
    {N : ℤ} (hN : 1 ≤ N)
    (hcycle :
      E.toPageOneSpectralSequence.cycle pq
          ⟨Int.toNat N, by
            have hN' : 0 < N := by
              omega
            exact Int.toNat_pos.2 hN'⟩ =
        E.toPageOneSpectralSequence.cycleInfinity pq)
    (hboundary :
      E.toPageOneSpectralSequence.boundary pq
          ⟨Int.toNat N, by
            have hN' : 0 < N := by
              omega
            exact Int.toNat_pos.2 hN'⟩ =
        E.toPageOneSpectralSequence.boundaryInfinity pq) :
    ((E.page N).X pq) ≅ E.toPageOneSpectralSequence.infinityPage pq := by
  let S := E.toPageOneSpectralSequence
  let rPos : ℕ+ := ⟨Int.toNat N, by
    have hN' : 0 < N := by
      omega
    exact Int.toNat_pos.2 hN'⟩
  -- The canonical quotient `Z_N/B_N` already identifies with the page-`N` entry.
  have hpage :
      cokernel
          (Subobject.ofLE
            (S.boundary pq rPos)
            (S.cycle pq rPos)
            (S.boundary_le_cycle pq rPos)) ≅
        ((E.page N).X pq) := by
    letI : IsIso (S.pageQuotientToPage pq rPos) :=
      SpectralSequence.pageQuotientToPage_isIso S pq rPos
    simpa [S, SpectralSequence.pageObject, rPos] using asIso (S.pageQuotientToPage pq rPos)
  -- After stabilization, the same quotient is exactly the defining quotient for `E_\infty`.
  have hstable :
      cokernel
          (Subobject.ofLE
            (S.boundary pq rPos)
            (S.cycle pq rPos)
            (S.boundary_le_cycle pq rPos)) ≅
        S.infinityPage pq := by
    cases hcycle
    cases hboundary
    simpa [SpectralSequence.infinityPage]
  exact hpage.symm ≪≫ hstable

end CohomologicalSpectralSequence

/- Domain-style triage for Lemma `12.24.12`.
- source-facing layer: the finiteness and `K₀` consequences for the cohomology of a filtered
  complex whose associated spectral sequence has a finite-support page;
- core/canonical owners already available upstream in this chapter:
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.HasFiniteFiltrations`,
  `FilteredComplex.cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations`;
- bridge/view layer: the finite-support and alternating-sum conclusions stated in this file.

This file now reuses the Chapter 12 owners directly instead of rebuilding a parallel local
filtered-complex API. -/

namespace FilteredComplex

/- Canonical owner input reused below: pagewise membership in a weak Serre subcategory already
comes from Lemma `12.24.11`. -/
#check FilteredComplex.cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations

/-- Helper for Lemma 12.24.12: a nonzero page-one term forces the corresponding page-zero term to
be nonzero. -/
lemma pageZero_nonzero_of_pageOne_nonzero
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (p q : ℤ)
    (h₁ : ¬ IsZero ((E.page 1).X (p, q))) :
    ¬ IsZero ((E.page 0).X (p, q)) := by
  intro h₀
  -- First transport the zero page-zero term to the corresponding graded-piece object.
  have hgradedObj : IsZero ((K.gradedPiece p).X (p + q)) := by
    exact IsZero.of_iso h₀ (asIso ((pageZeroIso K E p).hom.f q))
  -- Then the page-one term, computed as the homology of that graded piece, is zero.
  have hgradedHomology : IsZero ((K.gradedPiece p).homology (p + q)) := by
    simpa [HomologicalComplex.homology] using
      (ShortComplex.isZero_homology_of_isZero_X₂
        ((K.gradedPiece p).sc' (p + q - 1) (p + q) (p + q + 1))
        hgradedObj)
  have hpageOne : IsZero ((E.page 1).X (p, q)) := by
    exact IsZero.of_iso hgradedHomology (pageOneIso K E p q).symm
  exact h₁ hpageOne

-- Proof sketch: compare the alternating Euler characteristic of the even and odd parts of the
-- `r`-th page with that of the `r + 1`-st page, iterate until the differential vanishes, and then
-- use the finite filtration on each `H^n(K^•)` from Lemma `12.24.11` to read off that only
-- finitely many cohomology objects can remain nonzero.
/-- Lemma 12.24.12 (1): if the filtration on each `K^n` is finite and some page `E_r` of the
associated spectral sequence has only finitely many nonzero terms, then only finitely many
cohomology objects `H^n(K^•)` are nonzero. -/
theorem cohomologyObject_finite_nonzero_of_page_finite_nonzero
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r)
    (hpageFinite : { pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X (pq.1, pq.2)) }.Finite) :
    { n : ℤ | ¬ IsZero (K.underlying.homology n) }.Finite := by
  classical
  let hbounded := associatedSpectralSequence_isBounded_of_hasFiniteFiltrations K E hfin
  let hconv := convergesToCohomology_of_hasFiniteFiltrations K E hfin
  let hweak := hconv.2.1.1
  -- Any nonzero cohomology object contributes a nonzero infinity-page term on the same
  -- antidiagonal, hence a nonzero term on the chosen supporting page.
  refine (hpageFinite.image fun pq : ℤ × ℤ ↦ pq.1 + pq.2).subset ?_
  intro n hn
  have hHfin := cohomologyFiltrationIsFinite_of_hasFiniteFiltrations K E hfin n
  obtain ⟨p, hp⟩ :=
    DecreasingFiltration.exists_nonzero_gradedPiece_of_nonzero_of_isFinite
      (K.inducedCohomologyFiltration n) hn hHfin
  have e∞ :
      (K.inducedCohomologyFiltration n).gradedPiece p ≅
        E.toPageOneSpectralSequence.infinityPage (p, n - p) :=
    Classical.choice (hweak n p)
  have h∞ : ¬ IsZero (E.toPageOneSpectralSequence.infinityPage (p, n - p)) := by
    intro hzero
    exact hp (IsZero.of_iso hzero e∞.symm)
  have hpage : ¬ IsZero ((E.page r hr).X (p, n - p)) := by
    by_cases hzero : r = 0
    · -- Route correction: page `0` is handled by first passing through page `1`, where the
      -- weak-convergence comparison lands, and then descending back using `pageZeroIso`.
      have hpageOne : ¬ IsZero ((E.page 1).X (p, n - p)) := by
        exact CohomologicalSpectralSequence.nonzero_pageObj_of_nonzero_infinityPage
          E hbounded (p, n - p) (by omega) h∞
      simpa [hzero] using K.pageZero_nonzero_of_pageOne_nonzero E p (n - p) hpageOne
    · have hpos : 1 ≤ r := by
        omega
      exact CohomologicalSpectralSequence.nonzero_pageObj_of_nonzero_infinityPage
        E hbounded (p, n - p) hpos h∞
  refine ⟨(p, n - p), hpage, ?_⟩
  simp

/-- Helper for Lemma 12.24.12: if no supporting page-`r` term lies on total degree `n`, then the
cohomology object `H^n(K^•)` is zero. -/
lemma cohomology_isZero_of_not_mem_totalDegree_image_support
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (s : Finset (ℤ × ℤ))
    (hs : ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s → IsZero ((E.page r hr).X (pq.1, pq.2)))
    {n : ℤ} (hn : n ∉ s.image (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)) :
    IsZero (K.underlying.homology n) := by
  classical
  let hbounded := associatedSpectralSequence_isBounded_of_hasFiniteFiltrations K E hfin
  let hconv := convergesToCohomology_of_hasFiniteFiltrations K E hfin
  let hweak := hconv.2.1.1
  by_contra hzero
  have hHfin := cohomologyFiltrationIsFinite_of_hasFiniteFiltrations K E hfin n
  -- A nonzero cohomology object has a nonzero graded piece in its induced finite filtration.
  obtain ⟨p, hp⟩ :=
    DecreasingFiltration.exists_nonzero_gradedPiece_of_nonzero_of_isFinite
      (K.inducedCohomologyFiltration n) hzero hHfin
  have e∞ :
      (K.inducedCohomologyFiltration n).gradedPiece p ≅
        E.toPageOneSpectralSequence.infinityPage (p, n - p) :=
    Classical.choice (hweak n p)
  have h∞ : ¬ IsZero (E.toPageOneSpectralSequence.infinityPage (p, n - p)) := by
    intro hzero∞
    exact hp (IsZero.of_iso hzero∞ e∞.symm)
  -- Route correction: pass through page `1` only in the initial-page case `r = 0`.
  have hpage : ¬ IsZero ((E.page r hr).X (p, n - p)) := by
    by_cases hzero_r : r = 0
    · have hpageOne : ¬ IsZero ((E.page 1).X (p, n - p)) := by
        exact CohomologicalSpectralSequence.nonzero_pageObj_of_nonzero_infinityPage
          E hbounded (p, n - p) (by omega) h∞
      simpa [hzero_r] using K.pageZero_nonzero_of_pageOne_nonzero E p (n - p) hpageOne
    · have hpos : 1 ≤ r := by
        omega
      exact CohomologicalSpectralSequence.nonzero_pageObj_of_nonzero_infinityPage
        E hbounded (p, n - p) hpos h∞
  -- The nonzero page term must lie inside the chosen support, contradicting the total-degree
  -- exclusion hypothesis.
  have hmem : (p, n - p) ∈ s := by
    by_contra hnot
    exact hpage (hs hnot)
  apply hn
  exact Finset.mem_image.mpr ⟨(p, n - p), hmem, by simp⟩

/-- Helper for Lemma 12.24.12: every `E_\infty` term belongs to the same weak Serre
subcategory as the supporting page `E_r`. -/
lemma infinityPage_mem_of_page_mem_of_hasFiniteFiltrations
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (p q : ℤ) :
    P (E.toPageOneSpectralSequence.infinityPage (p, q)) := by
  let hconv := convergesToCohomology_of_hasFiniteFiltrations K E hfin
  let hweak := hconv.2.1.1
  let n : ℤ := p + q
  let e∞ :
      (K.inducedCohomologyFiltration n).gradedPiece p ≅
        E.toPageOneSpectralSequence.infinityPage (p, q) := by
    simpa [n] using (Classical.choice (hweak n p))
  have hH :
      P (K.underlying.homology n) :=
    cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
      K E P hfin r hr hpageP n
  have hstage :
      ∀ i : ℤ, P (((K.inducedCohomologyFiltration n).obj i : Subobject (K.underlying.homology n)) : 𝒜) := by
    intro i
    -- Each filtration stage is a subobject of the ambient cohomology object.
    exact P.prop_of_mono ((K.inducedCohomologyFiltration n).obj i).arrow inferInstance hH
  have hgraded :
      P ((K.inducedCohomologyFiltration n).gradedPiece p) := by
    -- The graded piece is the cokernel of the consecutive stage inclusion.
    simpa [DecreasingFiltration.gradedPiece] using
      (P.prop_of_isColimit_cokernelCofork
        (cokernelIsColimit ((K.inducedCohomologyFiltration n).stageInclusion p))
        (hstage (p + 1)) (hstage p))
  exact P.prop_of_iso e∞ hgraded

/-- Helper for Lemma 12.24.12: outside the chosen page-`r` support, the corresponding
`E_\infty` term vanishes. -/
lemma infinityPage_isZero_of_not_mem_support
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (s : Finset (ℤ × ℤ))
    (hs : ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s → IsZero ((E.page r hr).X (pq.1, pq.2)))
    {pq : ℤ × ℤ} (hpq : pq ∉ s) :
    IsZero (E.toPageOneSpectralSequence.infinityPage pq) := by
  let hbounded := associatedSpectralSequence_isBounded_of_hasFiniteFiltrations K E hfin
  by_contra hzero
  have h∞ : ¬ IsZero (E.toPageOneSpectralSequence.infinityPage pq) := hzero
  have hpage : ¬ IsZero ((E.page r hr).X pq) := by
    by_cases hzero_r : r = 0
    · -- Route correction: the `r = 0` case must pass through page `1` before descending back.
      have hpageOne : ¬ IsZero ((E.page 1).X pq) := by
        exact CohomologicalSpectralSequence.nonzero_pageObj_of_nonzero_infinityPage
          E hbounded pq (by omega) h∞
      simpa [hzero_r] using K.pageZero_nonzero_of_pageOne_nonzero E pq.1 pq.2 hpageOne
    · have hpos : 1 ≤ r := by
        omega
      exact CohomologicalSpectralSequence.nonzero_pageObj_of_nonzero_infinityPage
        E hbounded pq hpos h∞
  exact hpage (hs hpq)

-- Proof sketch: the differentials on each page split the finite-support page into even and odd
-- parts whose Euler characteristic is unchanged from `E_r` to `E_{r+1}`; after iterating to a
-- page with zero differential, identify the stable page with the graded pieces of the finite
-- filtration on `H^n(K^•)` and use additivity in `K₀`.
/-- Helper for Lemma 12.24.12: the page-`r` entry at `pq` viewed inside the weak Serre
subcategory `P`. -/
abbrev pageEntryInWeakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (pq : ℤ × ℤ) : P.FullSubcategory :=
  ⟨(E.page r hr).X pq, hpageP pq.1 pq.2⟩

/-- Helper for Lemma 12.24.12: the limiting entry at `pq` viewed inside the same weak Serre
subcategory as the supporting page. -/
abbrev infinityPageInWeakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (pq : ℤ × ℤ) : P.FullSubcategory :=
  ⟨E.toPageOneSpectralSequence.infinityPage pq,
    infinityPage_mem_of_page_mem_of_hasFiniteFiltrations
      K E hfin hr P hpageP pq.1 pq.2⟩

/-- Helper for Lemma 12.24.12: the cohomology object in degree `n` viewed inside the weak Serre
subcategory generated by the page-`r` objects. -/
abbrev cohomologyInWeakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n : ℤ) : P.FullSubcategory :=
  ⟨K.underlying.homology n,
    cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
      K E P hfin r hr hpageP n⟩

/-- Helper for Lemma 12.24.12: the `p`-th stage of the induced cohomology filtration belongs to
the same weak Serre subcategory as the cohomology object. -/
lemma inducedCohomologyFiltration_stage_mem
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n p : ℤ) :
    P (((K.inducedCohomologyFiltration n).obj p : Subobject (K.underlying.homology n)) : 𝒜) := by
  -- Each filtration stage is a subobject of the ambient cohomology object.
  exact P.prop_of_mono ((K.inducedCohomologyFiltration n).obj p).arrow inferInstance
    (cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
      K E P hfin r hr hpageP n)

/-- Helper for Lemma 12.24.12: the `p`-th graded piece of the induced cohomology filtration
belongs to the same weak Serre subcategory as the cohomology object. -/
lemma inducedCohomologyFiltration_gradedPiece_mem
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n p : ℤ) :
    P ((K.inducedCohomologyFiltration n).gradedPiece p) := by
  -- The graded piece is the cokernel of the consecutive stage inclusion.
  simpa [DecreasingFiltration.gradedPiece] using
    (P.prop_of_isColimit_cokernelCofork
      (cokernelIsColimit ((K.inducedCohomologyFiltration n).stageInclusion p))
      (inducedCohomologyFiltration_stage_mem K E hfin hr P hpageP n (p + 1))
      (inducedCohomologyFiltration_stage_mem K E hfin hr P hpageP n p))

/-- Helper for Lemma 12.24.12: the `p`-th stage of the induced cohomology filtration, viewed
inside the weak Serre full subcategory. -/
abbrev inducedCohomologyStageInWeakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n p : ℤ) : P.FullSubcategory :=
  ⟨((K.inducedCohomologyFiltration n).obj p : 𝒜),
    inducedCohomologyFiltration_stage_mem K E hfin hr P hpageP n p⟩

/-- Helper for Lemma 12.24.12: the `p`-th graded piece of the induced cohomology filtration,
viewed inside the weak Serre full subcategory. -/
abbrev inducedCohomologyGradedPieceInWeakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n p : ℤ) : P.FullSubcategory :=
  ⟨(K.inducedCohomologyFiltration n).gradedPiece p,
    inducedCohomologyFiltration_gradedPiece_mem K E hfin hr P hpageP n p⟩

/-- Helper for Lemma 12.24.12: the induced cohomology filtration can be regarded as a decreasing
filtration in the weak Serre full subcategory. -/
noncomputable abbrev inducedCohomologyFiltrationInWeakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n : ℤ) : DecreasingFiltration (cohomologyInWeakSerre K E hfin hr P hpageP n) := sorry

/-- Helper for Lemma 12.24.12: the stage objects of the bundled weak-Serre filtration are exactly
the ambient filtration stages with their inherited membership witnesses. -/
noncomputable lemma inducedCohomologyFiltrationInWeakSerre_stageIso
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n p : ℤ) :
    (((inducedCohomologyFiltrationInWeakSerre K E hfin hr P hpageP n).obj p : Subobject
        (cohomologyInWeakSerre K E hfin hr P hpageP n)) : P.FullSubcategory) ≅
      inducedCohomologyStageInWeakSerre K E hfin hr P hpageP n p := by
  -- TODO: identify the bundled subobject stage with its explicit ambient-stage presentation via
  -- `Subobject.underlyingIso`.
  sorry

/-- Helper for Lemma 12.24.12: after bundling into the weak Serre full subcategory, the stage
inclusion is still the ambient stage inclusion. -/
noncomputable lemma inducedCohomologyFiltrationInWeakSerre_stageInclusion
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n p : ℤ) :
    (inducedCohomologyFiltrationInWeakSerre K E hfin hr P hpageP n).stageInclusion p =
      (inducedCohomologyFiltrationInWeakSerre_stageIso
          K E hfin hr P hpageP n (p + 1)).hom ≫
        (K.inducedCohomologyFiltration n).stageInclusion p ≫
          (inducedCohomologyFiltrationInWeakSerre_stageIso
            K E hfin hr P hpageP n p).inv := by
  -- TODO: rewrite the bundled stage inclusion through the two stage identifications using
  -- `Subobject.ofLE_mk_le_mk_of_comm`.
  sorry

/-- Helper for Lemma 12.24.12: the bundled graded piece of the induced cohomology filtration is
canonically the ambient graded piece with its inherited weak-Serre structure. -/
noncomputable lemma inducedCohomologyFiltration_gradedPiece_iso_in_weakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n p : ℤ) :
    (((inducedCohomologyFiltrationInWeakSerre K E hfin hr P hpageP n).gradedPiece p :
        P.FullSubcategory)) ≅
      inducedCohomologyGradedPieceInWeakSerre K E hfin hr P hpageP n p := by
  -- TODO: transport the cokernel of the bundled stage inclusion to the ambient graded piece by
  -- `cokernel.mapIso`.
  sorry

/-- Helper for Lemma 12.24.12: the `K₀` class of a stage of the induced cohomology filtration
inside the weak Serre full subcategory telescopes across any finite window. -/
lemma inducedCohomologyFiltration_k0_window_in_weakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n a : ℤ) (d : ℕ) :
    K₀[inducedCohomologyStageInWeakSerre K E hfin hr P hpageP n a] =
      (Finset.sum (Finset.range d) fun i ↦
        K₀[inducedCohomologyGradedPieceInWeakSerre K E hfin hr P hpageP n (a + i)]) +
        K₀[inducedCohomologyStageInWeakSerre K E hfin hr P hpageP n (a + d)] := by
  -- TODO: apply `DecreasingFiltration.k0_eq_sum_gradedPieces_window_ambient` to the bundled weak
  -- Serre filtration and rewrite stages/graded pieces via the three comparison isomorphisms above.
  sorry

/-- Helper for Lemma 12.24.12: the bundled graded piece of the induced cohomology filtration is
canonically the bundled `E_\infty` object on the same antidiagonal. -/
noncomputable lemma inducedCohomologyFiltration_gradedPiece_iso_infinityPage_in_weakSerre
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (n p : ℤ) :
    inducedCohomologyGradedPieceInWeakSerre K E hfin hr P hpageP n p ≅
      infinityPageInWeakSerre K E hfin hr P hpageP (p, n - p) := by
  let hconv := convergesToCohomology_of_hasFiniteFiltrations K E hfin
  let hweak := hconv.2.1.1
  -- This is just the weak-convergence comparison packaged inside `P.FullSubcategory`.
  simpa [inducedCohomologyGradedPieceInWeakSerre, infinityPageInWeakSerre] using
    (Classical.choice (hweak n p))

/-- Helper for Lemma 12.24.12: summing over the image of a finite support is the same as summing
over the corresponding fibers inside that support. -/
lemma sum_image_eq_sum_filter {α β γ : Type*} [AddCommMonoid γ]
    (s : Finset α) (f : α → β) [DecidableEq β] (g : α → γ) :
    (Finset.sum (s.image f) fun b ↦
      Finset.sum (s.filter fun a ↦ f a = b) g) =
      Finset.sum s g := by
  classical
  calc
    (Finset.sum (s.image f) fun b ↦
        Finset.sum (s.filter fun a ↦ f a = b) g) =
      Finset.sum (s.image f) fun b ↦
        Finset.sum s (fun a ↦ if f a = b then g a else 0) := by
          -- Rewrite each fiber sum as a filtered sum over the original support.
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [Finset.sum_filter]
    _ =
      Finset.sum s fun a ↦
        Finset.sum (s.image f) (fun b ↦ if f a = b then g a else 0) := by
          -- Swap the finite sums so each support element contributes exactly on its own fiber.
          rw [Finset.sum_comm]
    _ = Finset.sum s g := by
          -- Each element of the support appears in exactly one fiber, namely that of `f a`.
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hfa : f a ∈ s.image f := Finset.mem_image.mpr ⟨a, ha, rfl⟩
          rw [Finset.sum_eq_single (f a)]
          · simp
          · intro b hb hne
            simp [hne]
          · exact False.elim (hb hfa)

/-- Helper for Lemma 12.24.12: for a fixed total degree `n`, the class of the cohomology object
is the signed sum of the limiting page objects over the fiber `{(p,q) ∈ s | p + q = n}`. -/
lemma single_cohomology_eq_infinity_fiber
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s → IsZero ((E.page r hr).X (pq.1, pq.2)))
    (n : ℤ) :
    (if Even n then
      K₀[cohomologyInWeakSerre K E hfin hr P hpageP n]
    else
      -K₀[cohomologyInWeakSerre K E hfin hr P hpageP n]) =
      (Finset.sum (s.filter fun pq : ℤ × ℤ ↦ pq.1 + pq.2 = n) fun pq ↦
        if Even (pq.1 + pq.2) then
          K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]
        else
          -K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]) := by
  -- TODO: telescope the induced filtration on `H^n(K^•)` inside `P.FullSubcategory`, then rewrite
  -- each graded piece to `E_∞^{p,n-p}` and discard the terms off the fixed fiber using
  -- `infinityPage_isZero_of_not_mem_support`.
  sorry

/-- Helper for Lemma 12.24.12: the alternating `K₀`-sum on a fixed finite support is unchanged
when the chosen supporting page is replaced by the limiting page `E_\infty`. -/
lemma alternatingSum_page_eq_infinityPage_support
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s → IsZero ((E.page r hr).X (pq.1, pq.2))) :
    (Finset.sum s fun pq ↦
      if Even (pq.1 + pq.2) then
        K₀[pageEntryInWeakSerre K E hr P hpageP pq]
      else
        -K₀[pageEntryInWeakSerre K E hr P hpageP pq]) =
      (Finset.sum s fun pq ↦
        if Even (pq.1 + pq.2) then
          K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]
        else
          -K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]) :=
  -- TODO: iterate the fixed-support page-step Euler invariance from the starting page to one
  -- uniform stable page, then rewrite each stable page entry using
  -- `CohomologicalSpectralSequence.pageObj_iso_infinityPage_of_stable`; the remaining blocker is
  -- the missing positive-page one-step equality inside `AbelianK0 (P.FullSubcategory)`.
  sorry

/-- Helper for Lemma 12.24.12: the alternating cohomology sum equals the alternating sum of the
`E_\infty`-graded pieces indexed by the original page support. -/
lemma alternatingSum_cohomology_eq_infinityPage_support
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s → IsZero ((E.page r hr).X (pq.1, pq.2))) :
    (Finset.sum (s.image (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)) fun n ↦
      if Even n then
        K₀[cohomologyInWeakSerre K E hfin hr P hpageP n]
      else
        -K₀[cohomologyInWeakSerre K E hfin hr P hpageP n]) =
      (Finset.sum s fun pq ↦
        if Even (pq.1 + pq.2) then
          K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]
        else
          -K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]) :=
by
  classical
  -- Sum the fixed-degree identities over the finite set of total degrees appearing in the page
  -- support.
  calc
    (Finset.sum (s.image (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)) fun n ↦
        if Even n then
          K₀[cohomologyInWeakSerre K E hfin hr P hpageP n]
        else
          -K₀[cohomologyInWeakSerre K E hfin hr P hpageP n]) =
      (Finset.sum (s.image (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)) fun n ↦
        Finset.sum (s.filter fun pq : ℤ × ℤ ↦ pq.1 + pq.2 = n) fun pq ↦
          if Even (pq.1 + pq.2) then
            K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]
          else
            -K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]) := by
            -- Replace each total-degree summand by the corresponding fiberwise `E_\infty` sum.
            refine Finset.sum_congr rfl ?_
            intro n hn
            simpa using single_cohomology_eq_infinity_fiber K E hfin hr P hpageP s hs n
    _ =
      (Finset.sum s fun pq ↦
        if Even (pq.1 + pq.2) then
          K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]
        else
          -K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]) := by
            -- Reassemble the finite fiber partition into the original support sum.
            simpa using
              (sum_image_eq_sum_filter
                (s := s)
                (f := fun pq : ℤ × ℤ ↦ pq.1 + pq.2)
                (g := fun pq : ℤ × ℤ ↦
                  if Even (pq.1 + pq.2) then
                    K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]
                  else
                    -K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]))

/-- Lemma 12.24.12 (2): let `P` be a weak Serre subcategory containing the objects `E_r^{p,q}` on
some page `r`. For any finite set supporting the nonzero terms on that page, there is a finite set
supporting the nonzero cohomology objects `H^n(K^•)` such that the alternating sums of their
classes agree in the Grothendieck group `K₀(P.FullSubcategory)`. In particular, this applies to
the smallest weak Serre subcategory generated by the objects `E_r^{p,q}` from the text. -/
theorem k0_alternatingSum_eq_of_page_support
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E] (hfin : K.HasFiniteFiltrations)
    {r : ℤ} (hr : 0 ≤ r) (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hpageP : ∀ p q : ℤ, P ((E.page r hr).X (p, q)))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s → IsZero ((E.page r hr).X (pq.1, pq.2))) :
    ∃ t : Finset ℤ,
      (∀ ⦃n : ℤ⦄, n ∉ t → IsZero (K.underlying.homology n)) ∧
        ((Finset.sum t fun n ↦
            if Even n then
              K₀[(⟨K.underlying.homology n,
                  cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
                    K E P hfin r hr hpageP n⟩ : P.FullSubcategory)]
            else
              -K₀[(⟨K.underlying.homology n,
                  cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
                    K E P hfin r hr hpageP n⟩ : P.FullSubcategory)]) =
          (Finset.sum s fun pq ↦
            if Even (pq.1 + pq.2) then
              K₀[(⟨(E.page r hr).X (pq.1, pq.2), hpageP pq.1 pq.2⟩ : P.FullSubcategory)]
            else
              -K₀[(⟨(E.page r hr).X (pq.1, pq.2), hpageP pq.1 pq.2⟩ : P.FullSubcategory)])) := by
  classical
  refine ⟨s.image (fun pq : ℤ × ℤ ↦ pq.1 + pq.2), ?_, ?_⟩
  · intro n hn
    -- The total-degree image of the page support controls exactly which cohomology objects can be
    -- nonzero.
    exact cohomology_isZero_of_not_mem_totalDegree_image_support K E hfin hr s hs hn
  · have h∞P :
        ∀ p q : ℤ, P (E.toPageOneSpectralSequence.infinityPage (p, q)) := by
      intro p q
      -- The limiting terms are graded pieces of the induced cohomology filtrations.
      exact infinityPage_mem_of_page_mem_of_hasFiniteFiltrations
        K E hfin hr P hpageP p q
    have h∞zero :
        ∀ ⦃pq : ℤ × ℤ⦄, pq ∉ s → IsZero (E.toPageOneSpectralSequence.infinityPage pq) := by
      intro pq hpq
      -- The support on page `E_r` propagates to the limit page via nonvanishing transfer.
      exact infinityPage_isZero_of_not_mem_support K E hfin hr s hs hpq
    -- Route correction: the endgame is now factored into the two source-faithful identities from
    -- the plan, one on the page side and one on the cohomology-filtration side.
    have hpageToInfinity :=
      alternatingSum_page_eq_infinityPage_support K E hfin hr P hpageP s hs
    have hcohomToInfinity :=
      alternatingSum_cohomology_eq_infinityPage_support K E hfin hr P hpageP s hs
    -- Both alternating sums are identified with the same `E_\infty` expression.
    calc
      (Finset.sum (s.image (fun pq : ℤ × ℤ ↦ pq.1 + pq.2)) fun n ↦
          if Even n then
            K₀[cohomologyInWeakSerre K E hfin hr P hpageP n]
          else
            -K₀[cohomologyInWeakSerre K E hfin hr P hpageP n]) =
          (Finset.sum s fun pq ↦
            if Even (pq.1 + pq.2) then
              K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]
            else
              -K₀[infinityPageInWeakSerre K E hfin hr P hpageP pq]) := hcohomToInfinity
      _ =
          (Finset.sum s fun pq ↦
            if Even (pq.1 + pq.2) then
              K₀[pageEntryInWeakSerre K E hr P hpageP pq]
            else
              -K₀[pageEntryInWeakSerre K E hr P hpageP pq]) := hpageToInfinity.symm

end FilteredComplex
end CategoryTheory
