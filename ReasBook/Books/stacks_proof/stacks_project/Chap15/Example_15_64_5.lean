import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_75_8
import stacks_proof.stacks_project.Chap12.Lemma_12_19_13
import stacks_proof.stacks_project.Chap12.Lemma_12_24_8
import stacks_proof.stacks_project.Chap12.Lemma_12_24_12
import stacks_proof.stacks_project.Chap15.Lemma_15_22_11
import stacks_proof.stacks_project.Chap15.Definition_15_61_1
import stacks_proof.stacks_project.Chap15.Lemma_15_67_2
import stacks_proof.stacks_project.Chap15.Lemma_15_67_6
import stacks_proof.stacks_project.Chap15.Lemma_15_64_4_K_nneth_Spectral_Sequence

open scoped BigOperators
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace CategoryTheory

open Limits
open MonoidalCategory

section

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory Mod
local notation "H" => DerivedCategory.homologyFunctor Mod
local notation "single₀" => (ModuleCat.single0Functor : Mod ⥤ DMod)

/-- Helper for Example 15.64.5: every module over a Dedekind domain has tor dimension at most
`1`. -/
theorem moduleHasTorDimensionLE_one_of_dedekind_domain (M : Mod) :
    ModuleHasTorDimensionLE M 1 := by
  let q : Projective.over M ⟶ M := Projective.π M
  let F : Fin 2 → Mod := fun i ↦ Fin.cases (Projective.over M) (fun _ ↦ kernel q) i
  let δ : (i : Fin 1) → F i.succ ⟶ F i.castSucc :=
    fun i ↦ Fin.cases (kernel.ι q) (fun j ↦ Fin.elim0 j) i
  have hProjectiveFlat : Module.Flat R (Projective.over M) := by
    -- The chosen cover object is projective, hence flat.
    exact Module.Flat.of_projective
  have hProjectiveTorsionFree : IsTorsionFree R (Projective.over M) := by
    -- Over a Dedekind domain, flat and torsion-free coincide.
    exact
      (flat_iff_isTorsionFree_of_isDedekindDomain (A := R) (M := Projective.over M)).1
        hProjectiveFlat
  have hKernelFlat : Module.Flat R (kernel q) := by
    -- The kernel is torsion-free because it injects into the torsion-free projective cover.
    refine
      (flat_iff_isTorsionFree_of_isDedekindDomain (A := R) (M := kernel q)).2 ?_
    rw [Submodule.isTorsionFree_iff_torsion_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hmono : Function.Injective (kernel.ι q).hom :=
      (ModuleCat.mono_iff_injective (kernel.ι q)).1 inferInstance
    apply hmono
    rw [Submodule.isTorsionFree_iff_torsion_eq_bot, Submodule.eq_bot_iff]
      at hProjectiveTorsionFree
    apply hProjectiveTorsionFree
    rw [Submodule.mem_torsion_iff] at hx ⊢
    rcases hx with ⟨a, ha, hax⟩
    refine ⟨a, ha, ?_⟩
    simpa using congrArg (fun y ↦ (kernel.ι q).hom y) hax
  have hq_surj : Function.Surjective q.hom := by
    -- The canonical projective cover map is an epimorphism in `ModuleCat`.
    exact (ModuleCat.epi_iff_surjective q).1 inferInstance
  have hq_exact : Function.Exact (kernel.ι q).hom q.hom := by
    -- The kernel row `0 → ker q → Projective.over M → M` is exact.
    let S : ShortComplex Mod := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
    have hSExact : S.Exact := by
      simpa [S] using ShortComplex.exact_kernel q
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hSExact
  have hδ_injective : Function.Injective (kernel.ι q).hom := by
    -- Kernels are monomorphisms in `ModuleCat`.
    exact (ModuleCat.mono_iff_injective (kernel.ι q)).1 inferInstance
  have hresolution : ModuleCat.HasFiniteFlatResolutionLengthLE M 1 := by
    -- Package the canonical two-term flat resolution.
    refine ⟨F, ?_, δ, q, hq_surj, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa [F] using hProjectiveFlat
      · intro j
        simpa [F] using hKernelFlat
    · simpa [δ] using hq_exact
    · intro i
      exact Fin.elim0 i
    · simpa [δ] using hδ_injective
  -- Convert the explicit flat resolution to the canonical tor-dimension owner.
  exact ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE (M := M) hresolution

/-- Helper for Example 15.64.5: `Tor_p^R(C, N)` is canonically the `(-p)`-th homology of
`C[0] ⊗_R^{\mathbf L} N[0]`. -/
noncomputable theorem tor_single0_tensor_homology_iso_local
    (C N : Mod) (p : ℕ) :
    ((((Tor Mod p).obj C).obj N)) ≅
      (H (-(p : ℤ))).obj ((single₀.obj C) ⊗[R]^L (single₀.obj N)) := by
  let eFlip :
      ((((Tor Mod p).obj C).obj N)) ≅
        ((((Functor.flip (Tor' Mod p)).obj C).obj N)) :=
    asIso (((tor_flip_iso Mod p).app C).hom.app N)
  let eResolution :
      ((((Functor.flip (Tor' Mod p)).obj C).obj N)) ≅
        (HomologicalComplex.homologyFunctor Mod (ComplexShape.down ℕ) p).obj
          (((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.projectiveResolution N).complex) := by
    -- Compute the flipped `Tor_p` term from the projective resolution of `N`.
    simpa [Tor', Functor.flip] using
      ((CategoryTheory.projectiveResolution N).isoLeftDerivedObj (tensorRight C) p)
  let eCochain :
      (HomologicalComplex.homologyFunctor Mod (ComplexShape.down ℕ) p).obj
          (((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.projectiveResolution N).complex) ≅
        ((((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CategoryTheory.ProjectiveResolution.cochainComplex
              (CategoryTheory.projectiveResolution N))).homology (-(p : ℤ))) := by
    let e :
        ((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CategoryTheory.ProjectiveResolution.cochainComplex
              (CategoryTheory.projectiveResolution N)) ≅
          ((((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
              (CategoryTheory.projectiveResolution N).complex).extend
            ComplexShape.embeddingDownNat) :=
      eqToIso rfl
    -- Reindex the chain-model homology to the cochain-model homology in degree `-p`.
    exact
      (((HomologicalComplex.homologyFunctor Mod (ComplexShape.up ℤ) (-(p : ℤ))).mapIso
          e) ≪≫
        ((((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.projectiveResolution N).complex).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp))).symm
  let eDerived :
      ((((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution N))).homology (-(p : ℤ))) ≅
        (H (-(p : ℤ))).obj
          ((DerivedCategory.Q.obj (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution N))) ⊗[R]^L (single₀.obj C)) :=
    tensorObj_single0_homology_iso_derivedTensor (R := R)
      (CategoryTheory.ProjectiveResolution.cochainComplex
        (CategoryTheory.projectiveResolution N))
      (-(p : ℤ)) C
  let eSingle :
      (H (-(p : ℤ))).obj
          ((DerivedCategory.Q.obj (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution N))) ⊗[R]^L (single₀.obj C)) ≅
        (H (-(p : ℤ))).obj ((single₀.obj N) ⊗[R]^L (single₀.obj C)) :=
    (H (-(p : ℤ))).mapIso
      ((derivedTensorProduct (single₀.obj C)).mapIso
        (projective_resolution_single0_iso (R := R) N))
  let eComm :
      (H (-(p : ℤ))).obj ((single₀.obj N) ⊗[R]^L (single₀.obj C)) ≅
        (H (-(p : ℤ))).obj ((single₀.obj C) ⊗[R]^L (single₀.obj N)) :=
    (H (-(p : ℤ))).mapIso
      (derivedTensorProduct_comm (single₀.obj N) (single₀.obj C))
  -- Compose the projective-resolution model with the canonical transports to the derived tensor.
  exact eFlip ≪≫ eResolution ≪≫ eCochain ≪≫ eDerived ≪≫ eSingle ≪≫ eComm

-- Proof sketch: `ModuleHasTorDimensionLE M 1` already says that `M[0] ⊗_R^{\mathbf L} N[0]` has
-- homology only in degrees `-1` and `0`. The local comparison above translates that tor-amplitude
-- statement into the explicit vanishing of `Tor_i^R(M, N)` for `i ≥ 2`.
/-- Helper for Example 15.64.5: tor dimension at most `1` forces all higher `Tor` groups to
vanish. -/
theorem isZero_tor_of_two_le_of_moduleHasTorDimensionLE_one
    (M N : Mod) {i : ℕ} (hM : ModuleHasTorDimensionLE M 1) (hi : 2 ≤ i) :
    IsZero (Tor[R, i](M, N)) := by
  have hi_outside : (-(i : ℤ)) ∉ Set.Icc (-(1 : ℤ)) 0 := by
    -- Degrees `-i` with `i ≥ 2` lie strictly to the left of the allowed interval `[-1, 0]`.
    intro hmem
    omega
  have hzeroHomology :
      IsZero ((H (-(i : ℤ))).obj ((single₀.obj M) ⊗[R]^L (single₀.obj N))) := by
    -- Unfold the tor-dimension owner and evaluate it at the test module `N`.
    simpa [ModuleHasTorDimensionLE] using hM N (-(i : ℤ)) hi_outside
  -- Transport the homology vanishing statement back to the canonical `Tor` object.
  exact IsZero.of_iso hzeroHomology (tor_single0_tensor_homology_iso_local (R := R) M N i).symm

-- Proof sketch: over a Dedekind domain every module has projective dimension at most one, so the
-- higher left derived functors of tensor product vanish in degrees `i ≥ 2`.
/-- Over a Dedekind domain, the higher `Tor` groups of two modules vanish above degree `1`. -/
theorem isZero_tor_of_two_le_of_dedekind_domain
    (M N : Mod) {i : ℕ} (hi : 2 ≤ i) :
    IsZero (Tor[R, i](M, N)) := by
  -- Reuse the canonical tor-dimension bound established above for modules over Dedekind domains.
  exact isZero_tor_of_two_le_of_moduleHasTorDimensionLE_one M N
    (moduleHasTorDimensionLE_one_of_dedekind_domain M) hi

end

section

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable [LocallySmall.{0} (ModuleCat R)] [WellPowered.{0} (ModuleCat R)]
  [HasWidePullbacks (ModuleCat R)] [HasCoproducts (ModuleCat R)]
  [InitialMonoClass (ModuleCat R)]

local notation "Mod" => ModuleCat R
local notation "H" => DerivedCategory.homologyFunctor Mod

/- Domain-style sampling for Example `15.64.5`.
- primary domain: bounded-derived Künneth spectral sequences over a Dedekind domain and the
  resulting short exact sequence in total degree `n`;
- sampled owner declarations in this domain:
  `ShortComplex.ShortExact`,
  `boundedDerivedTensorCohomology`,
  `kunnethDerivedTensorPageTwo`,
  `exists_kunnethDerivedTensorSpectralSequence`;
- best owner abstraction: the canonical owner for the short exact sequence itself is a
  `ShortComplex (ModuleCat R)` together with `ShortComplex.ShortExact`, but the source-facing
  theorem should expose the actual edge maps on the named `E₂`-terms and abutment objects rather
  than an auxiliary short complex up to isomorphism; the terms themselves should be reused from
  the chapter bridge declarations `kunnethDerivedTensorPageTwo` and
  `boundedDerivedTensorCohomology`, not recopied locally;
- primitive vs. derived: the primitive data for the public theorem are the maps
  `ι : kunnethDerivedTensorPageTwo K L 0 n ⟶ boundedDerivedTensorCohomology K L n` and
  `π : boundedDerivedTensorCohomology K L n ⟶ kunnethDerivedTensorPageTwo K L (-1) (n + 1)`
  together with the vanishing relation `ι ≫ π = 0`; the canonical short-complex owner
  `(ShortComplex.mk ι π h).ShortExact` is then the derived exactness packaging;
- source/core/bridge triage:
  `source-facing`: the existence theorem below for the Künneth short exact sequence;
  `core/canonical`: `ShortComplex` and `ShortComplex.ShortExact`;
  `bridge/view`: `kunnethDerivedTensorPageTwo`, `boundedDerivedTensorCohomology`, and the
  spectral-sequence existence theorem `exists_kunnethDerivedTensorSpectralSequence`.

This example is source-facing, but the previous wrapper class duplicated the canonical
short-complex owner and recopied the `E₂`-page formulas already owned upstream. The theorem below
now states the same mathematics directly in the chapter's canonical vocabulary.
-/

-- Proof sketch: start with the Künneth spectral sequence from Lemma `15.64.4`; the previous
-- vanishing theorem kills all `E₂^{p,q}` with `p ≤ -2`, so only the columns `p = 0, -1` remain.
-- The resulting two-line spectral sequence degenerates at `E₂`, and the usual filtration
-- argument yields the short exact sequence in total degree `n`.
/-- Helper for Example 15.64.5: the Künneth `E₂`-page is zero away from the columns `0` and
`-1`. -/
theorem kunneth_pageTwo_isZero_outside_zero_negOne
    (K L : boundedDerivedCategory (ModuleCat R)) (p q : ℤ)
    (hp0 : p ≠ 0) (hpneg1 : p ≠ -1) :
    IsZero (kunnethDerivedTensorPageTwo K L p q) := by
  classical
  by_cases hp : p ≤ 0
  · let Z : ℤ → Mod := fun i ↦
        (((Tor Mod (Int.toNat (-p))).obj ((H i).obj K.obj)).obj
          ((H (q - i)).obj L.obj))
    -- Proof comment: for `p ≤ -2`, every summand is a higher `Tor` term and therefore vanishes.
    rw [kunnethDerivedTensorPageTwo, dif_pos hp]
    change IsZero (∐ Z)
    have hp_le_neg_two : p ≤ -2 := by
      omega
    have hdeg : 2 ≤ Int.toNat (-p) := by
      have hnonneg : 0 ≤ -p := by
        omega
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    have hZi : ∀ i : ℤ, IsZero (Z i) := by
      intro i
      simpa [Z] using
        isZero_tor_of_two_le_of_dedekind_domain (R := R)
          ((H i).obj K.obj) ((H (q - i)).obj L.obj) (i := Int.toNat (-p)) hdeg
    letI : ∀ i : ℤ, Subsingleton (Z i) := fun i ↦ ModuleCat.subsingleton_of_isZero (hZi i)
    have hsum : Subsingleton (⨁ i : ℤ, Z i) := by
      refine ⟨?_⟩
      intro x y
      ext i
      exact Subsingleton.elim _ _
    have hzero : IsZero (ModuleCat.of R (⨁ i : ℤ, Z i)) :=
      ModuleCat.isZero_of_subsingleton _
    exact IsZero.of_iso hzero (ModuleCat.coprodIsoDirectSum (R := R) Z).symm
  · -- Proof comment: for `p > 0`, the `E₂`-term is definitionally the zero object.
    rw [kunnethDerivedTensorPageTwo, dif_neg hp]
    simpa using (Limits.isZero_zero Mod)

/-- Helper for Example 15.64.5: rebasing a cohomological spectral sequence at page `2` keeps the
same pages from `E₂` onward. -/
private abbrev page_two_tail
    (E : CohomologicalSpectralSequence (ModuleCat R) 0) :
    CohomologicalSpectralSequence (ModuleCat R) 2 where
  page r hr := E.page r (by omega)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (by omega)

/-- Helper for Example 15.64.5: if the `E₂` page is supported only in the columns `0` and `-1`,
then every later page has the same support. -/
private theorem page_isZero_outside_zero_negOne_from_pageTwo
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hpageTwo :
      ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page 2).X (p, q))) :
    ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page r).X (p, q)) := by
  intro r hr p q hp0 hpneg1
  have hinitial : IsZero (((page_two_tail E).page 2).X (p, q)) := by
    -- Proof comment: on the rebased owner, the initial page is literally the original `E₂` page.
    simpa [page_two_tail] using hpageTwo p q hp0 hpneg1
  -- Proof comment: the Chapter 12 propagation lemma now applies directly to the rebased owner.
  simpa [page_two_tail] using
    (CohomologicalSpectralSequence.isZero_pageObj_of_isZero_initialPageObj
      (E := page_two_tail E) (pq := (p, q)) (r := r) hinitial hr)

/-- Helper for Example 15.64.5: once every page `r ≥ 2` is supported only in the columns `0`
and `-1`, every differential touching one of those two surviving columns vanishes. -/
private theorem page_differentials_zero_on_surviving_columns_of_two_column_support
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hpage :
      ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page r).X (p, q))) :
    ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, (p = 0 ∨ p = -1) →
      (E.page r).d (p, q) (p + r, q - r + 1) = 0 ∧
        (E.page r).d (p - r, q + r - 1) (p, q) = 0 := by
  intro r hr p q hp
  constructor
  · have hp_target0 : p + r ≠ 0 := by
      rcases hp with rfl | rfl <;> omega
    have hp_target_neg1 : p + r ≠ -1 := by
      rcases hp with rfl | rfl <;> omega
    -- Proof comment: the target column of the outgoing differential lies outside `0` and `-1`.
    have htarget : IsZero ((E.page r).X (p + r, q - r + 1)) := by
      exact hpage hr (p + r) (q - r + 1) hp_target0 hp_target_neg1
    exact htarget.eq_zero_of_tgt _
  · have hp_source0 : p - r ≠ 0 := by
      rcases hp with rfl | rfl <;> omega
    have hp_source_neg1 : p - r ≠ -1 := by
      rcases hp with rfl | rfl <;> omega
    -- Proof comment: the source column of the incoming differential also lies outside `0` and
    -- `-1`, so the source object is already zero.
    have hsource : IsZero ((E.page r).X (p - r, q + r - 1)) := by
      exact hpage hr (p - r) (q + r - 1) hp_source0 hp_source_neg1
    exact hsource.eq_zero_of_src _

/-- Helper for Example 15.64.5: forgetting the `E₀` page keeps the same positive pages, now
viewed as a spectral sequence starting at `E₁`. -/
private abbrev page_one_tail
    (E : CohomologicalSpectralSequence (ModuleCat R) 0) :
    CohomologicalSpectralSequence (ModuleCat R) 1 where
  page r hr := E.page r (by omega)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (by omega)

/-- Helper for Example 15.64.5: once only the columns `0` and `-1` remain from page `2`
onward, the page-one tail is regular with stabilization beginning at page `2`. -/
private theorem page_one_tail_isRegular_of_two_column_support
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hpage :
      ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page r).X (p, q))) :
    CohomologicalSpectralSequence.IsRegular (page_one_tail E) := by
  intro p q
  refine ⟨2, ?_⟩
  intro r hr hbr
  by_cases hp0 : p = 0
  · -- Proof comment: on column `0`, the outgoing target column `r` is outside the support.
    simpa [page_one_tail] using
      (page_differentials_zero_on_surviving_columns_of_two_column_support
        (E := E) hpage hbr p q (Or.inl hp0)).1
  · by_cases hpneg1 : p = -1
    · -- Proof comment: on column `-1`, the outgoing target column `r - 1` is outside the
      -- support as soon as `r ≥ 2`.
      simpa [page_one_tail] using
        (page_differentials_zero_on_surviving_columns_of_two_column_support
          (E := E) hpage hbr p q (Or.inr hpneg1)).1
    · -- Proof comment: away from the two surviving columns, the source page object is already
      -- zero, so every outgoing differential vanishes.
      have hzero : IsZero (((page_one_tail E).page r).X (p, q)) := by
        simpa [page_one_tail] using hpage hbr p q hp0 hpneg1
      exact hzero.eq_zero_of_src _

/-- Helper for Example 15.64.5: once only the columns `0` and `-1` remain from page `2`
onward, the page-one tail is coregular with stabilization beginning at page `2`. -/
private theorem page_one_tail_isCoregular_of_two_column_support
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hpage :
      ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page r).X (p, q))) :
    CohomologicalSpectralSequence.IsCoregular (page_one_tail E) := by
  intro p q
  refine ⟨2, ?_⟩
  intro r hr hbr
  by_cases hp0 : p = 0
  · -- Proof comment: on column `0`, the incoming source column `-r` is outside the support.
    simpa [page_one_tail] using
      (page_differentials_zero_on_surviving_columns_of_two_column_support
        (E := E) hpage hbr p q (Or.inl hp0)).2
  · by_cases hpneg1 : p = -1
    · -- Proof comment: on column `-1`, the incoming source column `-1 - r` is still outside the
      -- support for `r ≥ 2`.
      simpa [page_one_tail] using
        (page_differentials_zero_on_surviving_columns_of_two_column_support
          (E := E) hpage hbr p q (Or.inr hpneg1)).2
    · -- Proof comment: away from columns `0` and `-1`, the target page object itself is zero.
      have hzero : IsZero (((page_one_tail E).page r).X (p, q)) := by
        simpa [page_one_tail] using hpage hbr p q hp0 hpneg1
      exact hzero.eq_zero_of_tgt _

/-- Helper for Example 15.64.5: if the source of a morphism is zero, then its cokernel
projection is an isomorphism. -/
private theorem cokernel_pi_isIso_of_isZero_src
    {X Y : Mod} (f : X ⟶ Y) (hX : IsZero X) :
    IsIso (cokernel.π f) := by
  let σ : cokernel f ⟶ Y :=
    cokernel.desc f (𝟙 Y) (by
      -- Proof comment: every morphism out of a zero object vanishes, so the identity cocone
      -- already satisfies the cokernel relation.
      simpa using hX.eq_of_src (f ≫ 𝟙 Y) 0)
  refine ⟨⟨σ, ?_, ?_⟩⟩
  · -- Proof comment: the chosen descender is a right inverse to the cokernel projection.
    exact cokernel.π_desc _ _ _
  · -- Proof comment: cokernel projections are epimorphisms, so equality is checked after
    -- precomposing with `cokernel.π`.
    apply (cancel_epi (cokernel.π f)).1
    simp [σ, Category.assoc]

/-- Helper for Example 15.64.5: on the surviving columns `0` and `-1`, the page-one cycle piece
stabilizes already at page `2`, so it agrees with the limiting cycle piece. -/
private theorem cycle_pageTwo_eq_cycleInfinity_of_two_column_support
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hpage :
      ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page r).X (p, q)))
    {p q : ℤ} (hp : p = 0 ∨ p = -1) :
    E.toPageOneSpectralSequence.cycle (p, q) 2 =
      E.toPageOneSpectralSequence.cycleInfinity (p, q) := by
  let S := E.toPageOneSpectralSequence
  have hstep :
      ∀ r : ℕ+, 2 ≤ (r : ℤ) → S.cycle (p, q) (r + 1) = S.cycle (p, q) r := by
    intro r hr
    have hzero :
        (E.page (r : ℤ)).d (p, q) (p + (r : ℤ), q - (r : ℤ) + 1) = 0 := by
      exact
        (page_differentials_zero_on_surviving_columns_of_two_column_support
          (E := E) hpage hr p q hp).1
    -- Proof comment: after page `2`, the outgoing differential vanishes on the surviving columns,
    -- so the successor cycle is the pullback of the whole target page.
    rw [SpectralSequence.cycle_succ_eq_map_pullback_kernel]
    rw [hzero, Limits.kernelSubobject_zero, Subobject.pullback_top]
    simpa [Subobject.map_top, Subobject.mk_arrow]
  have hconst_nat :
      ∀ m : ℕ, S.cycle (p, q) ⟨m + 2, by omega⟩ = S.cycle (p, q) 2 := by
    intro m
    induction m with
    | zero =>
        rfl
    | succ m ih =>
        let r : ℕ+ := ⟨m + 2, by omega⟩
        -- Proof comment: each successor step from page `r` to `r + 1` is already constant.
        calc
          S.cycle (p, q) ⟨m + 3, by omega⟩ = S.cycle (p, q) r := by
              simpa [r] using hstep r (by omega)
          _ = S.cycle (p, q) 2 := ih
  have hconst :
      ∀ r : ℕ+, 2 ≤ (r : ℤ) → S.cycle (p, q) r = S.cycle (p, q) 2 := by
    intro r hr
    let m : ℕ := (r : ℕ) - 2
    have hr_nat : 2 ≤ (r : ℕ) := by
      omega
    have hr_eq : r = ⟨m + 2, by omega⟩ := by
      apply PNat.eq
      simpa [m] using (Nat.sub_add_cancel hr_nat).symm
    simpa [hr_eq] using hconst_nat m
  have hle :
      S.cycle (p, q) 2 ≤ S.cycleInfinity (p, q) := by
    refine le_iInf ?_
    intro r
    by_cases hr1 : r = 1
    · subst hr1
      -- Proof comment: the page-one cycle is definitionally the whole initial-page object.
      simp [SpectralSequence.cycle]
    · have hr2 : 2 ≤ (r : ℤ) := by
        omega
      simpa [hconst r hr2] using le_rfl
  -- Proof comment: the limiting cycles are the infimum of page-one cycles, and every page from
  -- `2` onward is already equal to the page-two cycle.
  exact le_antisymm (iInf_le (fun r : ℕ+ ↦ S.cycle (p, q) r) 2) hle

/-- Helper for Example 15.64.5: on the surviving columns `0` and `-1`, the page-one boundary
piece stabilizes already at page `2`, so it agrees with the limiting boundary piece. -/
private theorem boundary_pageTwo_eq_boundaryInfinity_of_two_column_support
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hpage :
      ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page r).X (p, q)))
    {p q : ℤ} (hp : p = 0 ∨ p = -1) :
    E.toPageOneSpectralSequence.boundary (p, q) 2 =
      E.toPageOneSpectralSequence.boundaryInfinity (p, q) := by
  let S := E.toPageOneSpectralSequence
  have hstep :
      ∀ r : ℕ+, 2 ≤ (r : ℤ) → S.boundary (p, q) (r + 1) = S.boundary (p, q) r := by
    intro r hr
    have hzero :
        (E.page (r : ℤ)).d (p - (r : ℤ), q + (r : ℤ) - 1) (p, q) = 0 := by
      exact
        (page_differentials_zero_on_surviving_columns_of_two_column_support
          (E := E) hpage hr p q hp).2
    -- Proof comment: after page `2`, the incoming differential vanishes on the surviving columns,
    -- so the successor boundary is the pullback of the zero image.
    rw [SpectralSequence.boundary_succ_eq_map_pullback_image]
    rw [hzero, Limits.imageSubobject_zero, Subobject.pullback_bot]
    simpa [Subobject.map_bot]
  have hconst_nat :
      ∀ m : ℕ, S.boundary (p, q) ⟨m + 2, by omega⟩ = S.boundary (p, q) 2 := by
    intro m
    induction m with
    | zero =>
        rfl
    | succ m ih =>
        let r : ℕ+ := ⟨m + 2, by omega⟩
        -- Proof comment: once the incoming differential is zero, every later boundary agrees
        -- with the page-two boundary.
        calc
          S.boundary (p, q) ⟨m + 3, by omega⟩ = S.boundary (p, q) r := by
              simpa [r] using hstep r (by omega)
          _ = S.boundary (p, q) 2 := ih
  have hconst :
      ∀ r : ℕ+, 2 ≤ (r : ℤ) → S.boundary (p, q) r = S.boundary (p, q) 2 := by
    intro r hr
    let m : ℕ := (r : ℕ) - 2
    have hr_nat : 2 ≤ (r : ℕ) := by
      omega
    have hr_eq : r = ⟨m + 2, by omega⟩ := by
      apply PNat.eq
      simpa [m] using (Nat.sub_add_cancel hr_nat).symm
    simpa [hr_eq] using hconst_nat m
  have hle :
      S.boundaryInfinity (p, q) ≤ S.boundary (p, q) 2 := by
    refine iSup_le ?_
    intro r
    by_cases hr1 : r = 1
    · subst hr1
      -- Proof comment: the page-one boundary is definitionally the zero subobject.
      simp [SpectralSequence.boundary]
    · have hr2 : 2 ≤ (r : ℤ) := by
        omega
      simpa [hconst r hr2] using le_rfl
  -- Proof comment: the limiting boundaries are the supremum of page-one boundaries, and every
  -- page from `2` onward is already equal to the page-two boundary.
  exact le_antisymm hle (le_iSup (fun r : ℕ+ ↦ S.boundary (p, q) r) 2)

/-- Helper for Example 15.64.5: on the surviving columns `0` and `-1`, the page-two term is
already the limiting `E_\infty` term. -/
private noncomputable theorem pageTwo_iso_infinityPage_of_two_column_support
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hpage :
      ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page r).X (p, q)))
    {p q : ℤ} (hp : p = 0 ∨ p = -1) :
    ((E.page 2).X (p, q)) ≅ E.toPageOneSpectralSequence.infinityPage (p, q) := by
  -- Proof comment: once both the cycle and boundary pieces stabilize at page `2`, the generic
  -- Chapter 12 comparison identifies the page-two object with the infinity page.
  refine CohomologicalSpectralSequence.pageObj_iso_infinityPage_of_stable
      (E := E) (pq := (p, q)) (N := 2) (by omega) ?_ ?_
  · simpa using
      cycle_pageTwo_eq_cycleInfinity_of_two_column_support (E := E) hpage hp
  · simpa using
      boundary_pageTwo_eq_boundaryInfinity_of_two_column_support (E := E) hpage hp

/-- Helper for Example 15.64.5: if only the graded pieces in columns `0` and `-1` survive, then
the induced cohomology filtration has bottom stage `F^1 = 0` and top stage `F^{-1} = A`. -/
private theorem
    inducedCohomologyFiltration_stage_one_eq_bot_and_stage_negOne_eq_top_of_two_column_support
    (F : FilteredComplex Mod) (E : CohomologicalSpectralSequence Mod 0)
    [IsAssociatedToFilteredComplex F E]
    (hconv : F.convergesToCohomology E) (n : ℤ)
    (hinfinitySupport :
      ∀ p q : ℤ, p ≠ 0 → p ≠ -1 →
        IsZero (E.toPageOneSpectralSequence.infinityPage (p, q))) :
    (F.inducedCohomologyFiltration n).obj 1 = ⊥ ∧
      (F.inducedCohomologyFiltration n).obj (-1) = ⊤ := by
  let G := F.inducedCohomologyFiltration n
  have hweak := hconv.2.1.1
  have hgradedZero :
      ∀ p : ℤ, p ≠ 0 → p ≠ -1 → IsZero (G.gradedPiece p) := by
    intro p hp0 hpneg1
    rcases hweak n p with ⟨e⟩
    -- Proof comment: weak convergence identifies each graded piece with the matching infinity-page
    -- term, so off-column `E_\infty` vanishing kills the corresponding graded piece.
    exact IsZero.of_iso (hinfinitySupport p (n - p) hp0 hpneg1) e.symm
  have hstage_ge_one_nat :
      ∀ m : ℕ, G.obj (Int.ofNat m + 1) = G.obj 1 := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        have hiso : IsIso (G.stageInclusion (Int.ofNat m + 1)) := by
          apply G.isIso_stageInclusion_of_gradedPiece_isZero
          exact hgradedZero (Int.ofNat m + 1) (by omega) (by omega)
        have hEq :
            G.obj (Int.ofNat m + 2) = G.obj (Int.ofNat m + 1) := by
          -- Proof comment: a zero graded piece makes the adjacent stage inclusion an
          -- isomorphism, hence the two neighboring stage subobjects coincide.
          refine Subobject.eq_of_comm (asIso (G.stageInclusion (Int.ofNat m + 1))) ?_
          simpa [DecreasingFiltration.stageInclusion] using
            (Subobject.ofLE_arrow
              (X := G.obj (Int.ofNat m + 2))
              (Y := G.obj (Int.ofNat m + 1))
              (h := G.succ_le (Int.ofNat m + 1)))
        calc
          G.obj (Int.ofNat (m + 1) + 1) = G.obj (Int.ofNat m + 1) := by
              simpa [Int.ofNat_succ, add_assoc] using hEq
          _ = G.obj 1 := ih
  have hstage_ge_one :
      ∀ p : ℤ, 1 ≤ p → G.obj p = G.obj 1 := by
    intro p hp
    let m : ℕ := Int.toNat (p - 1)
    have hp_nonneg : 0 ≤ p - 1 := by
      omega
    have hp_eq : p = Int.ofNat m + 1 := by
      have hm : (m : ℤ) = p - 1 := by
        simpa [m] using Int.toNat_of_nonneg hp_nonneg
      omega
    simpa [hp_eq] using hstage_ge_one_nat m
  have hstage_le_negOne_nat :
      ∀ m : ℕ, G.obj (-1 - Int.ofNat m) = G.obj (-1) := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        have hiso : IsIso (G.stageInclusion (-2 - Int.ofNat m)) := by
          apply G.isIso_stageInclusion_of_gradedPiece_isZero
          exact hgradedZero (-2 - Int.ofNat m) (by omega) (by omega)
        have hEq :
            G.obj (-1 - Int.ofNat m) = G.obj (-2 - Int.ofNat m) := by
          -- Proof comment: the same zero-graded-piece argument makes the negative tail of the
          -- filtration constant from stage `-1` downward.
          refine Subobject.eq_of_comm (asIso (G.stageInclusion (-2 - Int.ofNat m))) ?_
          simpa [DecreasingFiltration.stageInclusion] using
            (Subobject.ofLE_arrow
              (X := G.obj (-1 - Int.ofNat m))
              (Y := G.obj (-2 - Int.ofNat m))
              (h := G.succ_le (-2 - Int.ofNat m)))
        calc
          G.obj (-1 - Int.ofNat (m + 1)) = G.obj (-2 - Int.ofNat m) := by
              simp [Int.ofNat_succ, add_assoc, sub_eq_add_neg, add_comm, add_left_comm]
          _ = G.obj (-1 - Int.ofNat m) := hEq.symm
          _ = G.obj (-1) := ih
  have hstage_le_negOne :
      ∀ p : ℤ, p ≤ -1 → G.obj p = G.obj (-1) := by
    intro p hp
    let m : ℕ := Int.toNat (-1 - p)
    have hp_nonneg : 0 ≤ -1 - p := by
      omega
    have hp_eq : p = -1 - Int.ofNat m := by
      have hm : (m : ℤ) = -1 - p := by
        simpa [m] using Int.toNat_of_nonneg hp_nonneg
      omega
    simpa [hp_eq] using hstage_le_negOne_nat m
  have hiInf_eq : (⨅ p : ℤ, G.obj p) = G.obj 1 := by
    apply le_antisymm
    · exact iInf_le (fun p : ℤ ↦ G.obj p) 1
    · refine le_iInf ?_
      intro p
      by_cases hp : 1 ≤ p
      · simpa [hstage_ge_one p hp] using le_rfl
      · exact G.antitone_obj (by omega)
  have hiSup_eq : (⨆ p : ℤ, G.obj p) = G.obj (-1) := by
    apply le_antisymm
    · refine iSup_le ?_
      intro p
      by_cases hp : p ≤ -1
      · simpa [hstage_le_negOne p hp] using le_rfl
      · exact G.antitone_obj (by omega)
    · exact le_iSup (fun p : ℤ ↦ G.obj p) (-1)
  have hsep :
      (⨅ p : ℤ, G.obj p) = ⊥ := by
    exact (DecreasingFiltration.isSeparated_iff_iInf_eq_bot G).1 (hconv.2.1.2 n).1
  have hexh :
      (⨆ p : ℤ, G.obj p) = ⊤ := by
    exact (DecreasingFiltration.isExhaustive_iff_iSup_eq_top G).1 (hconv.2.1.2 n).2
  constructor
  · -- Proof comment: the positive tail is constant and separated, so the common stage at `1`
    -- must already be the zero subobject.
    simpa [hiInf_eq] using hsep
  · -- Proof comment: the negative tail is constant and exhaustive, so the common stage at `-1`
    -- is the whole cohomology object.
    simpa [hiSup_eq] using hexh

/-- Helper for Example 15.64.5: a two-step decreasing filtration yields the canonical short exact
row `0 → gr^0 → A → gr^{-1} → 0`. -/
private theorem two_step_induced_filtration_shortExact_of_stage_one_bot_stage_negOne_top
    (A : Mod) (G : DecreasingFiltration A)
    (hbot : G.obj 1 = ⊥) (htop : G.obj (-1) = ⊤) :
    ∃ (ι : G.gradedPiece 0 ⟶ A) (π : A ⟶ G.gradedPiece (-1)) (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let S : ShortComplex Mod :=
    ShortComplex.mk (G.stageInclusion (-1)) (cokernel.π (G.stageInclusion (-1)))
      (cokernel.condition _)
  have hS : S.ShortExact := by
    -- Proof comment: the stage `-1` row is the canonical cokernel short exact sequence
    -- `0 → F^0 A → F^{-1} A → gr^{-1} A → 0`.
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact ShortComplex.exact_cokernel (G.stageInclusion (-1))
  have hzeroStage : IsZero (G.obj 1 : Mod) := by
    exact G.stage_isZero_of_eq_bot 1 hbot
  have hleftIso : IsIso (cokernel.π (G.stageInclusion 0)) := by
    -- Proof comment: because `F^1 A = 0`, the quotient `F^0 A / F^1 A` is just `F^0 A`.
    exact cokernel_pi_isIso_of_isZero_src (G.stageInclusion 0) hzeroStage
  let eLeft : (G.obj 0 : Mod) ≅ G.gradedPiece 0 :=
    asIso (cokernel.π (G.stageInclusion 0))
  let eMid : (G.obj (-1) : Mod) ≅ A :=
    G.stageIsoOfEqTop (-1) htop
  let ι : G.gradedPiece 0 ⟶ A :=
    eLeft.inv ≫ S.f ≫ eMid.hom
  let π : A ⟶ G.gradedPiece (-1) :=
    eMid.inv ≫ S.g
  have hcomp : ι ≫ π = 0 := by
    -- Proof comment: the transported maps still compose to zero because they come from the
    -- stage short complex at `p = -1`.
    simp [ι, π, S, Category.assoc]
  let eSc : S ≅ ShortComplex.mk ι π hcomp :=
    ShortComplex.isoMk eLeft eMid (Iso.refl _) (by
      simp [ι, S, Category.assoc]) (by
      simp [π, S, Category.assoc])
  refine ⟨ι, π, hcomp, ?_⟩
  -- Proof comment: transport the canonical stage short exact sequence across the three endpoint
  -- identifications just constructed.
  exact ShortComplex.shortExact_of_iso eSc hS

/-- Example 15.64.5: over a Dedekind domain, the Künneth spectral sequence of
Lemma `15.64.4` degenerates at the `E_2` page, yielding for every `n` a short exact sequence
`0 → ⨁_{i + j = n} H^i(K) ⊗_R H^j(L) → H^n(K ⊗_R^L L) →
⨁_{i + j = n + 1} Tor_1^R(H^i(K), H^j(L)) → 0`. -/
@[stacks 0H80]
theorem exists_kunneth_short_exact_sequence_of_dedekind_domain
    (K L : boundedDerivedCategory (ModuleCat R)) (n : ℤ) :
    ∃ (ι :
        kunnethDerivedTensorPageTwo K L 0 n ⟶
          boundedDerivedTensorCohomology K L n)
      (π :
        boundedDerivedTensorCohomology K L n ⟶
          kunnethDerivedTensorPageTwo K L (-1) (n + 1))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  classical
  have hpageTwoSupport :
      ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero (kunnethDerivedTensorPageTwo K L p q) := by
    intro p q hp0 hpneg1
    exact kunneth_pageTwo_isZero_outside_zero_negOne (R := R) K L p q hp0 hpneg1
  rcases exists_kunnethDerivedTensorSpectralSequence (R := R) K L with ⟨E, hE⟩
  rcases hE with ⟨hbounded, hpageTwo, hconverges⟩
  rcases hconverges with ⟨F, hassoc, hconv, habutment⟩
  have hpageTwoSupport' :
      ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page 2).X (p, q)) := by
    intro p q hp0 hpneg1
    rcases hpageTwo p q with ⟨e⟩
    -- Proof comment: transport the source-facing `E₂` vanishing across the chosen page-two
    -- comparison isomorphism from the Künneth spectral sequence package.
    exact IsZero.of_iso (hpageTwoSupport p q hp0 hpneg1) e.symm
  have hpageSupport :
      ∀ {r : ℤ}, 2 ≤ r → ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero ((E.page r).X (p, q)) := by
    intro r hr p q hp0 hpneg1
    exact page_isZero_outside_zero_negOne_from_pageTwo (R := R) E hpageTwoSupport' hr p q hp0
      hpneg1
  have hinfinitySupport :
      ∀ p q : ℤ, p ≠ 0 → p ≠ -1 → IsZero (E.toPageOneSpectralSequence.infinityPage (p, q)) := by
    intro p q hp0 hpneg1
    -- Proof comment: the `E_∞` term is a quotient of any later positive page at the same
    -- bidegree, so vanishing on `E₂` already forces vanishing on `E_∞`.
    exact CohomologicalSpectralSequence.infinityPage_isZero_of_pageObj_isZero
      E (p, q) (by omega) (hpageSupport (r := 2) (by omega) p q hp0 hpneg1)
  have hstageEnds :
      (F.inducedCohomologyFiltration n).obj 1 = ⊥ ∧
        (F.inducedCohomologyFiltration n).obj (-1) = ⊤ := by
    -- Route correction: instead of stopping at eventual stabilization data, use the explicit
    -- page-two support to identify the only nonzero `E_\infty` columns and collapse the induced
    -- cohomology filtration to two steps.
    exact
      inducedCohomologyFiltration_stage_one_eq_bot_and_stage_negOne_eq_top_of_two_column_support
        (F := F) (E := E) hconv n hinfinitySupport
  rcases
      two_step_induced_filtration_shortExact_of_stage_one_bot_stage_negOne_top
        (A := F.underlying.homology n)
        (G := F.inducedCohomologyFiltration n)
        hstageEnds.1 hstageEnds.2 with
    ⟨ι₀, π₀, hcomp₀, hshort₀⟩
  rcases hpageTwo 0 n with ⟨ePageTwo₀⟩
  rcases hpageTwo (-1) (n + 1) with ⟨ePageTwo₋₁⟩
  rcases hconv.2.1.1 n 0 with ⟨eWeak₀⟩
  rcases hconv.2.1.1 n (-1) with ⟨eWeak₋₁⟩
  rcases habutment n with ⟨eAbutment⟩
  let eLeft :
      (F.inducedCohomologyFiltration n).gradedPiece 0 ≅
        kunnethDerivedTensorPageTwo K L 0 n :=
    eWeak₀ ≪≫
      (pageTwo_iso_infinityPage_of_two_column_support
        (E := E) hpageSupport (p := 0) (q := n) (Or.inl rfl)).symm ≪≫
      ePageTwo₀
  let eRight :
      (F.inducedCohomologyFiltration n).gradedPiece (-1) ≅
        kunnethDerivedTensorPageTwo K L (-1) (n + 1) :=
    eWeak₋₁ ≪≫
      (pageTwo_iso_infinityPage_of_two_column_support
        (E := E) hpageSupport (p := -1) (q := n + 1) (Or.inr rfl)).symm ≪≫
      ePageTwo₋₁
  let ι :
      kunnethDerivedTensorPageTwo K L 0 n ⟶
        boundedDerivedTensorCohomology K L n :=
    eLeft.inv ≫ ι₀ ≫ eAbutment.hom
  let π :
      boundedDerivedTensorCohomology K L n ⟶
        kunnethDerivedTensorPageTwo K L (-1) (n + 1) :=
    eAbutment.inv ≫ π₀ ≫ eRight.hom
  have hcomp : ι ≫ π = 0 := by
    -- Proof comment: transport the two-step filtration maps along the page-two, weak-convergence,
    -- and abutment isomorphisms.
    simp [ι, π, hcomp₀, Category.assoc]
  let eSc :
      ShortComplex.mk ι₀ π₀ hcomp₀ ≅ ShortComplex.mk ι π hcomp :=
    ShortComplex.isoMk eLeft eAbutment eRight (by
      simp [ι, Category.assoc]) (by
      simp [π, Category.assoc])
  refine ⟨ι, π, hcomp, ?_⟩
  -- Proof comment: the transported short complex is exactly the textbook Künneth short exact row.
  exact ShortComplex.shortExact_of_iso eSc hshort₀

end

end CategoryTheory
