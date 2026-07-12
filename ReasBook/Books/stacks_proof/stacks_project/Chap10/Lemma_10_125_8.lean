import Mathlib
import StacksProject_2024.Chap10.Lemma_10_125_7

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]

/- 
Domain-style sampling:
- primary domain: source-facing loci on `Spec(S)` cut out by local fiber invariants of a finite
  presentation ring map, together with their topological finiteness properties;
- sampled owner declarations of the same kind:
  `relativeDimensionAtLELocus`,
  `exists_openNhdsOf_mem_relativeDimensionAtLELocus`,
  `Module.flatOverBaseLocus`,
  `Module.isOpen_flatOverBaseLocus_of_finitePresentation`;
- best owner abstraction: the named locus owner `relativeDimensionAtLELocus`; openness and
  quasi-compactness are derived API of that owner rather than new primitive data;
- primitive data: the finite presentation map `R → S` and the bound `n`;
- derived API: the open and compactness statements for the owner locus.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the bounded relative-dimension locus is open and
  quasi-compact;
- `core/canonical`: the owner `relativeDimensionAtLELocus R S n`;
- `bridge/view`: the separate `IsOpen` and `IsCompact` companion theorems below.
-/

-- Proof sketch: openness is exactly the local neighborhood criterion from
-- `exists_openNhdsOf_mem_relativeDimensionAtLELocus`.
/-- The locus where the relative dimension of a finitely presented algebra is at most `n` is open
in `Spec(S)`. -/
theorem isOpen_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsOpen (relativeDimensionAtLELocus R S n) := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  rcases exists_openNhdsOf_mem_relativeDimensionAtLELocus n q hq with ⟨U, hU⟩
  exact Filter.mem_of_superset (U.isOpen.mem_nhds U.mem) hU

/-- Helper for Chap10 Lemma 10 125 8: inverse images of compact open subsets of affine spectra
under maps induced by ring homomorphisms are compact. -/
private theorem isCompact_preimage_comap_of_isCompact_isOpen
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {U : Set (PrimeSpectrum A)} (hUcompact : IsCompact U) (hUopen : IsOpen U) :
    IsCompact (PrimeSpectrum.comap f ⁻¹' U) := by
  classical
  -- Represent the compact open as the complement of a finite zero locus.
  obtain ⟨t, rfl⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hUcompact, hUopen⟩
  -- Pull that finite presentation back along `comap` and reapply the spectrum compact-open
  -- criterion.
  refine (PrimeSpectrum.isCompact_isOpen_iff.mpr ?_).1
  refine ⟨t.image f, ?_⟩
  rw [Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
  ext x
  simp

/-- Helper for Chap10 Lemma 10 125 8: compactness of the bounded relative-dimension locus
descends through an exact tensor-product base-change identity when the original locus is compact
open. -/
private theorem isCompact_relativeDimensionAtLELocus_baseChange_of_isCompact_isOpen
    {R0 S0 T : Type*} [CommRing R0] [CommRing S0] [CommRing T]
    [Algebra R0 S0] [Algebra R0 T] [Algebra.FiniteType R0 S0] (n : ℕ)
    (hcompact : IsCompact (relativeDimensionAtLELocus R0 S0 n))
    (hopen : IsOpen (relativeDimensionAtLELocus R0 S0 n)) :
    IsCompact (relativeDimensionAtLELocus T (T ⊗[R0] S0) n) := by
  -- Pull compactness of the downstairs compact open along the spectrum map of `includeRight`.
  have hpre : IsCompact (PrimeSpectrum.comap
      (includeRight (R := R0) (A := T) (B := S0)).toRingHom ⁻¹'
      relativeDimensionAtLELocus R0 S0 n) := by
    classical
    obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hcompact, hopen⟩
    rw [← ht]
    refine (PrimeSpectrum.isCompact_isOpen_iff.mpr ?_).1
    refine ⟨t.image (includeRight (R := R0) (A := T) (B := S0)).toRingHom, ?_⟩
    rw [Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
    ext x
    simp
  -- The imported base-change theorem identifies this preimage with the upstairs locus.
  rwa [relativeDimensionAt_le_preimage_eq_baseChange] at hpre

/-- Helper for Chap10 Lemma 10 125 8: relative dimension at corresponding primes is invariant
under an algebra equivalence over the base. -/
private theorem relativeDimensionAt_eq_of_algEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    relativeDimensionAt R A (PrimeSpectrum.comap e.toRingHom q) =
      relativeDimensionAt R B q := by
  let qA : PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R B) q
  have hpA : PrimeSpectrum.comap (algebraMap R A) qA = p := by
    ext r
    simp [qA, p]
  have hUnderA : qA.asIdeal.under R = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
  let eFiber : p.asIdeal.Fiber A ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber B :=
    Algebra.TensorProduct.congr AlgEquiv.refl e
  have hprime :
      hUnderA ▸ (fiberPrimeAt R A qA).asIdeal =
        (fiberPrimeAt R B q).asIdeal.comap eFiber.toRingEquiv.toRingHom := by
    cases hUnderA
    dsimp [qA, p, eFiber]
    ext x
    simp [fiberPrimeAt]
  -- The induced equivalence of fiber rings identifies the two localized fiber local rings.
  subst qA
  rw [relativeDimensionAt, fiberLocalRingAt]
  rw [hUnderA]
  exact ringKrullDim_eq_of_ringEquiv
    (Localization.localRingEquiv _ _ eFiber.toRingEquiv hprime)

/-- Helper for Chap10 Lemma 10 125 8: compactness of the bounded relative-dimension locus is
preserved by algebra equivalences over the base. -/
private theorem isCompact_relativeDimensionAtLELocus_of_algEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (n : ℕ)
    (hcompact : IsCompact (relativeDimensionAtLELocus R A n)) :
    IsCompact (relativeDimensionAtLELocus R B n) := by
  let hspec := (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm
  have hpre : IsCompact (hspec ⁻¹' relativeDimensionAtLELocus R A n) :=
    hspec.isCompact_preimage.mpr hcompact
  convert hpre using 1
  ext q
  simp only [relativeDimensionAtLELocus, Set.mem_setOf_eq, Set.mem_preimage]
  change relativeDimensionAt R B q ≤ (n : WithBot ℕ∞) ↔
    relativeDimensionAt R A (PrimeSpectrum.comap e.toRingHom q) ≤ (n : WithBot ℕ∞)
  rw [relativeDimensionAt_eq_of_algEquiv e q]

-- Proof sketch: descend the finite presentation to a finite type `ℤ`-model, identify the locus by
-- `relativeDimensionAt_le_preimage_eq_baseChange`, and use quasi-compactness of open subsets of the
-- Noetherian spectrum downstairs.
/-- The locus where the relative dimension of a finitely presented algebra is at most `n` is
quasi-compact in `Spec(S)`. -/
theorem isCompact_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsCompact (relativeDimensionAtLELocus R S n) := by
  classical
  -- Choose a finite presentation and descend its finitely many coefficients to a Noetherian
  -- `ℤ`-subalgebra of the base.
  let P := Algebra.Presentation.ofFinitePresentation R S
  let R0 := P.Core
  let S0 := P.ModelOfHasCoeffs R0
  letI : IsNoetherianRing R0 := Algebra.FiniteType.isNoetherianRing ℤ R0
  letI : IsNoetherianRing S0 := Algebra.FiniteType.isNoetherianRing R0 S0
  have hcompact_downstairs : IsCompact (relativeDimensionAtLELocus R0 S0 n) :=
    NoetherianSpace.isCompact _
  have hopen_downstairs : IsOpen (relativeDimensionAtLELocus R0 S0 n) :=
    isOpen_relativeDimensionAtLELocus_of_finitePresentation (R := R0) (S := S0) n
  -- Base-change compactness from the Noetherian model to `R ⊗[R0] S0`.
  have hcompact_tensor : IsCompact (relativeDimensionAtLELocus R (R ⊗[R0] S0) n) :=
    isCompact_relativeDimensionAtLELocus_baseChange_of_isCompact_isOpen
      (R0 := R0) (S0 := S0) (T := R) n hcompact_downstairs hopen_downstairs
  -- The chosen presentation identifies `S` with that tensor-product model.
  exact isCompact_relativeDimensionAtLELocus_of_algEquiv
    (P.tensorModelOfHasCoeffsEquiv R0) n hcompact_tensor

-- Proof sketch: openness is the pointwise neighborhood statement of Lemma `10.125.6`. For
-- quasi-compactness, descend the finite presentation to a finitely generated `ℤ`-subalgebra of
-- the source, identify the locus with the inverse image of the corresponding locus after base
-- change using Lemma `10.125.7`, and use that open subsets of the Noetherian spectrum downstairs
-- are quasi-compact.
/-- Lemma 10.125.8: if `R → S` is of finite presentation, then the locus
`{ q ∈ Spec(S) | dim_q(S/R) ≤ n }` is an open and quasi-compact subset of `Spec(S)`. -/
@[stacks 00QJ]
theorem isOpen_isCompact_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsOpen (relativeDimensionAtLELocus R S n) ∧
      IsCompact (relativeDimensionAtLELocus R S n) :=
  ⟨isOpen_relativeDimensionAtLELocus_of_finitePresentation n,
    isCompact_relativeDimensionAtLELocus_of_finitePresentation n⟩

end
