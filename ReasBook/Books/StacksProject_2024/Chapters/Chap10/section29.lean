import Mathlib
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_29_1 (from Chap10) -/
universe u

open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} [CommSemiring R] {U : Set (PrimeSpectrum R)}

/- Domain-style sampling for quasi-compact open subsets of `Spec(R)`:
- primary domain: prime spectrum topology, retrocompactness, and compact-open descriptions;
- same-domain declarations inspected:
  `QuasiSeparatedSpace.isRetrocompact_iff_isCompact`,
  `PrimeSpectrum.isCompact_isOpen_iff`,
  `PrimeSpectrum.isCompact_isOpen_iff_ideal`,
  `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`,
  `StacksProject_2024.Chap10.Definition_10_17_1`'s notation owners `D(-)` and `V(-)`;
- best owner abstraction: the core/canonical owners are the ambient predicates `IsRetrocompact`,
  `IsCompact`, and the spectrum-specific compact-open characterizations above;
- primitive data: an open subset `U ⊆ Spec(R)`;
- derived API: the finite-union-of-basic-opens and finitely-generated-ideal presentations of the
  same compact open subset.

Layer triage:
- `source-facing`: the four-way textbook equivalence for an open subset of `Spec(R)`;
- `core/canonical`: `QuasiSeparatedSpace.isRetrocompact_iff_isCompact`,
  `PrimeSpectrum.isCompact_isOpen_iff`, and `PrimeSpectrum.isCompact_isOpen_iff_ideal`;
- `bridge/view`: converting `(V(t))ᶜ` into a finite union of standard opens `D(f)`.
-/

private theorem compl_V_eq_iUnion_D (t : Finset R) :
    ((V(t) : Set (PrimeSpectrum R)))ᶜ = ⋃ f ∈ t, D(f) := by
  ext x
  simp [basicOpen_eq_zeroLocus_compl, mem_zeroLocus, Set.not_subset]

-- Proof sketch: identify retrocompactness with compactness for the open subset `U` using
-- quasi-separatedness of `Spec(R)`, then rewrite compactness through the compact-open owner
-- theorems for finite unions of standard opens and complements of zero loci of finitely generated
-- ideals.
/-- Lemma 10.29.1: for an open subset `U ⊆ Spec(R)`, the following are equivalent: `U` is
retrocompact in `Spec(R)`, `U` is quasi-compact, `U` is a finite union of standard opens `D(f)`,
and `U` is the complement of a closed subset `V(I)` for a finitely generated ideal `I`. -/
theorem primeSpectrum_open_tfae_retrocompact
    (hU : IsOpen U) :
    List.TFAE
      [ IsRetrocompact U
      , IsCompact U
      , ∃ t : Finset R, U = ⋃ f ∈ t, D(f)
      , ∃ I : Ideal R, I.FG ∧ U = (V(I))ᶜ ] := by
  have hcompact_basicOpen :
      IsCompact U ↔ ∃ t : Finset R, U = ⋃ f ∈ t, D(f) := by
    constructor
    · intro hCompact
      obtain ⟨t, ht⟩ := isCompact_isOpen_iff.mp ⟨hCompact, hU⟩
      exact ⟨t, ht.symm.trans (compl_V_eq_iUnion_D t)⟩
    · rintro ⟨t, rfl⟩
      exact (isCompact_isOpen_iff.mpr
        ⟨t, compl_V_eq_iUnion_D t⟩).1
  have hcompact_ideal :
      IsCompact U ↔ ∃ I : Ideal R, I.FG ∧ U = (V(I))ᶜ := by
    constructor
    · intro hCompact
      obtain ⟨I, hI, hIU⟩ := isCompact_isOpen_iff_ideal.mp ⟨hCompact, hU⟩
      exact ⟨I, hI, hIU.symm⟩
    · rintro ⟨I, hI, rfl⟩
      exact (isCompact_isOpen_iff_ideal.mpr ⟨I, hI, rfl⟩).1
  tfae_have 1 ↔ 2 := QuasiSeparatedSpace.isRetrocompact_iff_isCompact hU
  tfae_have 2 ↔ 3 := hcompact_basicOpen
  tfae_have 2 ↔ 4 := hcompact_ideal
  tfae_finish

end

/-! ### Lemma_10_29_2 (from Chap10) -/
universe u v

open PrimeSpectrum
open Topology

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Layering for this item:
* core/canonical owner: `IsSpectralMap`.
* bridge/view: show the canonical `Spec` map `comap φ` is spectral, then derive constructible
  preimages from the chapter-level owner API `IsSpectralMap.isConstructible_preimage`.
-/

/-- Lemma 10.29.2 (1): for a ring homomorphism `φ : R →+* S`, the induced map
`Spec(S) → Spec(R)` is spectral; equivalently, the preimage of a quasi-compact open subset of
`Spec(R)` is quasi-compact. -/
theorem primeSpectrum_comap_isSpectralMap (φ : R →+* S) :
    IsSpectralMap (comap φ) := by
  refine ⟨continuous_comap φ, ?_⟩
  intro U hU_open hU_compact
  classical
  obtain ⟨t, rfl⟩ := isCompact_isOpen_iff.mp ⟨hU_compact, hU_open⟩
  refine (PrimeSpectrum.isCompact_isOpen_iff.mpr ?_).1
  refine ⟨t.image φ, ?_⟩
  rw [Set.preimage_compl, preimage_comap_zeroLocus]
  ext x
  simp

/-- Lemma 10.29.2 (2): the preimage of a constructible subset of `Spec(R)` under the induced map
`Spec(S) → Spec(R)` is constructible in `Spec(S)`. -/
theorem primeSpectrum_comap_preimage_isConstructible
    (φ : R →+* S) {E : Set (PrimeSpectrum R)} (hE : IsConstructible E) :
    IsConstructible (comap φ ⁻¹' E) :=
  (primeSpectrum_comap_isSpectralMap φ).isConstructible_preimage hE

end

/-! ### Lemma_10_29_3 (from Chap10) -/
universe u

open PrimeSpectrum
open Topology

section

variable {R : Type u} [CommSemiring R]

/- Lemma 10.29.3: a subset of `Spec(R)` is constructible if and only if it is a finite union of
subsets of the form `D(f) ∩ V(g₁, …, gₘ)`.

The canonical mathlib formulation is `PrimeSpectrum.exists_constructibleSetData_iff`: a
constructible subset is exactly a set represented by `PrimeSpectrum.ConstructibleSetData R`, where
each basic piece is packaged as `V(g₁, …, gₘ) \ V(f) = D(f) ∩ V(g₁, …, gₘ)`. -/
recall PrimeSpectrum.exists_constructibleSetData_iff

private noncomputable def pairToBasicConstructibleSetData (a : R × Finset R) :
    BasicConstructibleSetData R where
  f := a.1
  n := a.2.card
  g := fun i ↦ ((Finset.equivFin a.2).symm i).1

omit [CommSemiring R] in
private theorem range_pairToBasicConstructibleSetData
    (a : R × Finset R) :
    Set.range (pairToBasicConstructibleSetData a).g = (a.2 : Set R) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Finset.equivFin a.2).symm i).2
  · intro hx
    refine ⟨Finset.equivFin a.2 ⟨x, hx⟩, ?_⟩
    simp [pairToBasicConstructibleSetData]

private theorem pairToBasicConstructibleSetData_toSet
    (a : R × Finset R) :
    (pairToBasicConstructibleSetData a).toSet =
      ((basicOpen a.1 : Set (PrimeSpectrum R)) ∩ zeroLocus (a.2 : Set R)) := by
  rw [BasicConstructibleSetData.toSet, range_pairToBasicConstructibleSetData,
    Set.diff_eq_compl_inter, basicOpen_eq_zeroLocus_compl]
  simp [pairToBasicConstructibleSetData, Set.inter_comm]

/-- Textbook finset reformulation of Lemma 10.29.3: a subset of `Spec(R)` is constructible if and
only if it is a finite union of subsets of the form `D(f) ∩ V(G)` with `f ∈ R` and `G ⊆ R`
finite. This is the finite-set form of the textbook description `D(f) ∩ V(g₁, …, gₘ)`. -/
-- Proof sketch: unpack `PrimeSpectrum.exists_constructibleSetData_iff`, convert between a finite
-- family `g : Fin n → R` and the corresponding finite set of generators, and use
-- `PrimeSpectrum.basicOpen_eq_zeroLocus_compl` to identify `V(G) \ V(f)` with `D(f) ∩ V(G)`.
theorem isConstructible_iff_exists_finset_union_basicOpen_inter_zeroLocus
    {T : Set (PrimeSpectrum R)} :
    IsConstructible T ↔
      ∃ s : Finset (R × Finset R),
        T = ⋃ a ∈ s,
          ((basicOpen a.1 : Set (PrimeSpectrum R)) ∩ zeroLocus (a.2 : Set R)) := by
  classical
  constructor
  · intro hT
    obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hT
    refine ⟨S.image fun C ↦ (C.f, (Set.finite_range C.g).toFinset), ?_⟩
    rw [ConstructibleSetData.toSet, Finset.set_biUnion_finset_image]
    congr! with C hC
    rw [BasicConstructibleSetData.toSet, Set.diff_eq_compl_inter, basicOpen_eq_zeroLocus_compl,
      Set.Finite.coe_toFinset (Set.finite_range C.g)]
  · rintro ⟨s, rfl⟩
    apply exists_constructibleSetData_iff.mp
    refine ⟨s.image pairToBasicConstructibleSetData, ?_⟩
    rw [ConstructibleSetData.toSet, Finset.set_biUnion_finset_image]
    congr! with a ha
    exact pairToBasicConstructibleSetData_toSet a

end

/-! ### Lemma_10_29_4 (from Chap10) -/
universe u

open PrimeSpectrum Topology

section

variable {R : Type u} [CommRing R]

private abbrev pieceIdeal (C : BasicConstructibleSetData R) : Ideal R :=
  Ideal.span (Set.range C.g)

private abbrev pieceRing (C : BasicConstructibleSetData R) : Type u :=
  Localization.Away (Ideal.Quotient.mk (pieceIdeal C) C.f)

private instance (C : BasicConstructibleSetData R) :
    Algebra.FinitePresentation R (pieceRing C) := by
  have hI : (pieceIdeal C).FG := by
    dsimp [pieceIdeal]
    simpa using Submodule.fg_span (Set.finite_range C.g)
  letI : Algebra.FinitePresentation R (R ⧸ pieceIdeal C) :=
    Algebra.FinitePresentation.quotient hI
  change Algebra.FinitePresentation R
    (Localization.Away (Ideal.Quotient.mk (pieceIdeal C) C.f))
  infer_instance

private theorem range_comap_pieceRing_eq_toSet (C : BasicConstructibleSetData R) :
    Set.range (comap (algebraMap R (pieceRing C))) = C.toSet := by
  let I := pieceIdeal C
  let f : R ⧸ I := Ideal.Quotient.mk I C.f
  trans comap (Ideal.Quotient.mk I) '' (Set.range (comap (algebraMap (R ⧸ I) (pieceRing C))))
  · rw [← Set.range_comp]
    rfl
  · rw [localization_away_comap_range _ f, ← comap_basicOpen,
      TopologicalSpace.Opens.coe_comap, ContinuousMap.coe_mk, Set.image_preimage_eq_inter_range,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, BasicConstructibleSetData.toSet,
      Set.diff_eq_compl_inter, basicOpen_eq_zeroLocus_compl, Ideal.mk_ker, zeroLocus_span]

private abbrev constructibleWitnessRing (s : ConstructibleSetData R) : Type u :=
  (C : s) → pieceRing C.1

private theorem range_comap_constructibleWitnessRing_eq_toSet (s : ConstructibleSetData R) :
    Set.range (comap (algebraMap R (constructibleWitnessRing s))) = s.toSet := by
  rw [← iUnion_range_comap_comp_evalRingHom, ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_coe, Set.biUnion_eq_iUnion]
  congr! with _ _ C
  simpa [constructibleWitnessRing] using range_comap_pieceRing_eq_toSet C.1

-- Proof sketch: use Lemma `10.29.3` to write a constructible subset as a finite union of sets of
-- the form `D(f) ∩ V(g₁, ..., gₘ)`. Each such piece is the image of
-- `Spec ((R ⧸ (g₁, ..., gₘ))_f) → Spec(R)` by Lemmas `10.17.6` and `10.17.7`, and finite unions
-- are handled by passing to finite products, whose spectra are disjoint unions by Lemma `10.21.2`.
--
-- This is the source-facing finite-presentation refinement of the owner theorem
-- `PrimeSpectrum.exists_range_eq_of_isConstructible`: it uses the same canonical witness ring built
-- from `PrimeSpectrum.ConstructibleSetData`, and records that each quotient-localization factor is
-- finitely presented over `R`.
/-- Lemma 10.29.4: every constructible subset of `Spec(R)` is the image of `Spec(S)` in `Spec(R)`
for some finitely presented ring map `R → S`. -/
theorem exists_finitePresentation_comap_range_eq_of_isConstructible
    {T : Set (PrimeSpectrum R)} (hT : IsConstructible T) :
    ∃ (S : Type u) (_ : CommRing S) (f : R →+* S),
      f.FinitePresentation ∧ Set.range (comap f) = T := by
  obtain ⟨s, rfl⟩ := exists_constructibleSetData_iff.mpr hT
  refine ⟨
    constructibleWitnessRing s,
    inferInstance, algebraMap R (constructibleWitnessRing s), ?_⟩
  constructor
  · exact RingHom.finitePresentation_algebraMap.2 inferInstance
  · exact range_comap_constructibleWitnessRing_eq_toSet s

end

/-! ### Lemma_10_29_5 (from Chap10) -/
universe u

open PrimeSpectrum Topology

section

variable {R : Type u} [CommRing R]

-- Proof sketch: this is the `bridge/view` localization-away specialization of the owner theorem
-- `PrimeSpectrum.isConstructible_comap_image`. The primitive input is the constructible subset of
-- `Spec(R_f)`; the finite-presentation hypothesis is derived canonically from
-- `IsLocalization.Away.finitePresentation`.
/-- Lemma 10.29.5: for `S = R_f`, the image of a constructible subset of `Spec(S)` in `Spec(R)` is
constructible. -/
theorem isConstructible_image_comap_localizationAway (f : R)
    {s : Set (PrimeSpectrum (Localization.Away f))} (hs : IsConstructible s) :
    IsConstructible (comap (algebraMap R (Localization.Away f)) '' s) := by
  simpa using
    PrimeSpectrum.isConstructible_comap_image
      (RingHom.finitePresentation_algebraMap.mpr (IsLocalization.Away.finitePresentation f)) hs

end

/-! ### Lemma_10_29_6 (from Chap10) -/
universe u

open PrimeSpectrum
open Topology

section

variable {R : Type u} [CommRing R]

-- Proof sketch: this is the quotient specialization of the owner theorem
-- `PrimeSpectrum.isConstructible_comap_image`. The only primitive input is `hI : I.FG`; the
-- finite-presentation structure on `R ⧸ I` is derived canonically from
-- `Algebra.FinitePresentation.quotient hI`.
/-- Lemma 10.29.6: if `I` is a finitely generated ideal of a commutative ring `R`, then the image
of a constructible subset of `Spec (R ⧸ I)` under the quotient map to `Spec(R)` is constructible
in `Spec(R)`. -/
theorem isConstructible_image_comap_quotient
    (I : Ideal R) (hI : I.FG) {s : Set (PrimeSpectrum (R ⧸ I))} (hs : IsConstructible s) :
    IsConstructible (comap (Ideal.Quotient.mk I) '' s) := by
  letI : Algebra.FinitePresentation R (R ⧸ I) := Algebra.FinitePresentation.quotient hI
  simpa using
    isConstructible_comap_image
      (RingHom.finitePresentation_algebraMap.mpr inferInstance) hs

end

/-! ### Lemma_10_29_7 (from Chap10) -/
open Polynomial PrimeSpectrum
open TopologicalSpace

universe u

section

variable {R : Type u} [CommRing R]

-- Layering for this item:
-- * source-facing: the textbook compact-open image statement below.
-- * core/canonical owners: `Polynomial.image_comap_C_basicOpen`, `Polynomial.isOpenMap_comap_C`,
--   and `CompactOpens.map`.
-- * bridge/view: `isCompact_isOpen_image_comap_C_basicOpen` unwraps the owner-level compact-open
--   image back to the textbook `IsCompact ∧ IsOpen` formulation.

/-
Lemma 10.29.7: the exact image formula for a standard open under the structure morphism
`Spec(R[X]) → Spec(R)` is the canonical theorem `Polynomial.image_comap_C_basicOpen`.
-/
recall Polynomial.image_comap_C_basicOpen

/-- Lemma 10.29.7: for a polynomial `f : R[X]`, the image of the standard open `D(f)` under the
structure map `Spec(R[X]) → Spec(R)` is a compact open, i.e. a quasi-compact open subset of
`Spec(R)`. -/
theorem isCompact_isOpen_image_comap_C_basicOpen (f : R[X]) :
    IsCompact (comap C '' (basicOpen f : Set (PrimeSpectrum R[X]))) ∧
      IsOpen (comap C '' (basicOpen f : Set (PrimeSpectrum R[X]))) := by
  let U : CompactOpens (PrimeSpectrum R[X]) :=
    ⟨⟨basicOpen f, PrimeSpectrum.isCompact_basicOpen f⟩, (basicOpen f).isOpen⟩
  let V : CompactOpens (PrimeSpectrum R) :=
    U.map (comap C) (continuous_comap C) isOpenMap_comap_C
  refine ⟨?_, ?_⟩
  · simpa [U, V] using V.isCompact
  · simpa [U, V] using V.isOpen

/- The structure morphism `Spec(R[X]) → Spec(R)` is the canonical open-map theorem
`Polynomial.isOpenMap_comap_C` from mathlib. -/
recall Polynomial.isOpenMap_comap_C

end

/-! ### Lemma_10_29_8 (from Chap10) -/
open PrimeSpectrum
open scoped TensorProduct

universe u v

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Free R A] [Module.Finite R A]

/- Lemma 10.29.8 uses the canonical theorem `isNilpotent_tensor_residueField_iff`, which
characterizes fiberwise nilpotence by the non-leading coefficients of the characteristic
polynomial. -/
recall isNilpotent_tensor_residueField_iff

/-- Lemma 10.29.8: equivalently, if `P(T) = T^n + r_{n-1} T^{n-1} + ··· + r₀` is the
characteristic polynomial of `Algebra.lmul R A f`, then the fiber of `f` over `p` is nilpotent if
and only if `p ∈ V(r₀, …, r_{n-1})`. -/
theorem fiber_nilpotent_iff_mem_zeroLocus_charpoly_coeffs
    (f : A) (p : PrimeSpectrum R) :
    IsNilpotent ((algebraMap A (A ⊗[R] p.asIdeal.ResidueField)) f) ↔
      p ∈ zeroLocus
        (Set.range fun i : Fin (Module.finrank R A) ↦
          (Algebra.lmul R A f).charpoly.coeff i) := by
  simpa [mem_zeroLocus, Set.range_subset_iff] using
    (isNilpotent_tensor_residueField_iff f p.asIdeal).trans Nat.forall_lt_iff_fin

end

/-! ### Lemma_10_29_9 (from Chap10) -/
open Polynomial PrimeSpectrum

universe u

section

variable {R : Type u} [CommRing R]

/-- Canonical complement-of-zero-locus form of Lemma 10.29.9: if `f, g : R[X]` and the leading
coefficient of `g` is a unit, then the image of `D(f) ∩ V(g)` in `Spec(R)` under the structure
morphism `Spec(R[X]) → Spec(R)` is a compact open of the canonical form `(V(t))ᶜ`. This is the
`isUnit`-leading-coefficient variant of `Polynomial.exists_image_comap_of_monic`. -/
theorem exists_image_basicOpen_inter_zeroLocus_eq_zeroLocus_compl_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    ∃ t : Finset R,
      comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X])) =
        (zeroLocus t : Set (PrimeSpectrum R))ᶜ := by
  let g' : R[X] := hg.unit⁻¹ • g
  have hg' : g'.Monic := by
    simpa [g'] using monic_of_isUnit_leadingCoeff_inv_smul hg
  have hg'_eq : g' = C (↑(hg.unit⁻¹) : R) * g := by
    ext i
    simp [g', coeff_C_mul, Units.smul_def]
  have hzero :
      (zeroLocus ({g'} : Set R[X]) : Set (PrimeSpectrum R[X])) = zeroLocus ({g} : Set R[X]) := by
    rw [hg'_eq, ← zeroLocus_span ({C (↑(hg.unit⁻¹) : R) * g} : Set R[X]),
      ← zeroLocus_span ({g} : Set R[X]),
      Ideal.span_singleton_mul_left_unit (isUnit_C.mpr (Units.isUnit _))]
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g' hg'
  refine ⟨t, ?_⟩
  calc
    comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]))
        = comap C '' (zeroLocus ({g'} : Set R[X]) \ zeroLocus ({f} : Set R[X])) := by
            congr 1
            ext x
            rw [hzero]
            constructor <;> intro h <;>
              simpa [basicOpen_eq_zeroLocus_compl, Set.diff_eq, and_comm] using h
    _ = (zeroLocus t : Set (PrimeSpectrum R))ᶜ := ht

/-- If `f, g : R[X]` and the leading coefficient of `g` is a unit, then the image of
`D(f) ∩ V(g)` in `Spec(R)` under the structure morphism `Spec(R[X]) → Spec(R)` is compact open. -/
theorem isCompact_isOpen_image_basicOpen_inter_zeroLocus_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    IsCompact (comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]))) ∧
      IsOpen (comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]))) := by
  let U : Set (PrimeSpectrum R) :=
    comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]))
  obtain ⟨t, ht⟩ := exists_image_basicOpen_inter_zeroLocus_eq_zeroLocus_compl_of_isUnit_leadingCoeff
    f g hg
  change IsCompact U ∧ IsOpen U
  exact
    (PrimeSpectrum.isCompact_isOpen_iff :
      IsCompact U ∧ IsOpen U ↔
        ∃ s : Finset R, (zeroLocus s : Set (PrimeSpectrum R))ᶜ = U).mpr
      ⟨t, by simpa [U] using ht.symm⟩

/-- Lemma 10.29.9: if `f, g : R[X]` and the leading coefficient of `g` is a unit, then the image
of `D(f) ∩ V(g)` in `Spec(R)` under the structure morphism `Spec(R[X]) → Spec(R)` is a finite
union of basic opens. -/
theorem exists_finite_basicOpen_cover_image_basicOpen_inter_zeroLocus_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    ∃ t : Finset R,
      comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X])) =
        ⋃ r ∈ t, (basicOpen r : Set (PrimeSpectrum R)) := by
  obtain ⟨t, ht⟩ := exists_image_basicOpen_inter_zeroLocus_eq_zeroLocus_compl_of_isUnit_leadingCoeff
    f g hg
  refine ⟨t, ht.trans ?_⟩
  ext p
  simp [basicOpen_eq_zeroLocus_compl, Set.not_subset]

end

/-! ### Theorem_10_29_10_Chevalley_s_Theorem (from Chap10) -/
/- Theorem 10.29.10 (Chevalley's Theorem): suppose that `R →+* S` is of finite presentation. Then
the image of a constructible subset of `Spec(S)` in `Spec(R)` is constructible. This is exactly the
canonical theorem `PrimeSpectrum.isConstructible_comap_image`. -/
recall PrimeSpectrum.isConstructible_comap_image
