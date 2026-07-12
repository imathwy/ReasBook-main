import Mathlib
import StacksProject_2024.Chap05.Definition_5_10_5
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Definition_10_125_1
import StacksProject_2024.Chap10.Lemma_10_17_6
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Lemma_10_104_2
import StacksProject_2024.Chap10.Lemma_10_112_6
import StacksProject_2024.Chap10.Lemma_10_129_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open PrimeSpectrum
open RingTheory Sequence
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/-
Domain-style sampling:
* primary domain: regular-sequence loci on the canonical fiber local rings over `Spec R`;
* sampled owner declarations of the same kind:
  `fiberLocalRingAt`,
  `toFiberLocalRingAt`,
  `PrimeSpectrum.IsRegularInFiberLocalRing`,
  `PrimeSpectrum.zeroLocus`,
  `RingTheory.Sequence.IsRegular`;
* best owner abstraction: the source-facing locus should live directly on the closed subspace
  `V(Ideal.ofList fs)`, because containment of `Ideal.ofList fs` is primitive data in the source
  statement; the pointwise regular-sequence owner on a prime `q` should be the bridge
  `q.IsRegularInFiberLocalRing R fs`, whose canonical content is regularity of the image of `fs`
  in the owner fiber local ring `fiberLocalRingAt R S q`;
* primitive data: the list `fs`, the point `q : V(Ideal.ofList fs)`, and regularity of the image
  of `fs` in the owner fiber local ring at `q.1`;
* derived API: the named regular-sequence locus on `V(Ideal.ofList fs)` and the openness theorem
  below.

Source/core/bridge triage:
* `source-facing`: the regular-sequence locus inside `V(Ideal.ofList fs)` and its openness;
* `core/canonical`: `fiberLocalRingAt`, `toFiberLocalRingAt`, and `Sequence.IsRegular`;
* `bridge/view`: `PrimeSpectrum.IsRegularInFiberLocalRing`, the subtype-valued locus, and its
  point-membership lemma.
-/

/-- The locus in `V(Ideal.ofList fs)` where the images of `fs` form a regular sequence in the
local fiber ring. -/
def fiberLocalRingRegularSequenceLocus (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (fs : List S) :
    Set (V((Ideal.ofList fs : Set S))) :=
  { q | q.1.IsRegularInFiberLocalRing R fs }

/-- A point of `V(Ideal.ofList fs)` lies in `fiberLocalRingRegularSequenceLocus` exactly when the
images of `fs` form a regular sequence in the corresponding local fiber ring. -/
theorem mem_fiberLocalRingRegularSequenceLocus_iff
    (fs : List S) (q : V((Ideal.ofList fs : Set S))) :
    q ∈ fiberLocalRingRegularSequenceLocus R S fs ↔
      q.1.IsRegularInFiberLocalRing R fs := by
  rfl

/-- Helper for Chap10 Lemma 10 129 2: the fiber-local regularity predicate is exactly the
regularity of the image of the list in the canonical fiber local ring. -/
private theorem isRegularInFiberLocalRing_iff_isRegularSequence
    (q : PrimeSpectrum S) (fs : List S) :
    q.IsRegularInFiberLocalRing R fs ↔
      RingTheory.Sequence.IsRegular (fiberLocalRingAt R S q)
        (fs.map (toFiberLocalRingAt R S q)) := by
  -- The pointwise predicate was introduced as a thin wrapper around `Sequence.IsRegular`.
  rfl

/-- Helper for Chap10 Lemma 10 129 2: a ring equivalence transports a regular sequence to the
mapped coefficient list. -/
private theorem isRegular_map_iff_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (rs : List A) :
    RingTheory.Sequence.IsRegular A rs ↔ RingTheory.Sequence.IsRegular B (rs.map e) := by
  -- Proof comment: on the regular self-modules, the scalar action is multiplication, so the
  -- transport is exactly preservation of multiplication by the ring equivalence.
  refine e.toAddEquiv.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a _ x
  simpa [Algebra.smul_def] using e.map_mul a x

/-- Helper for Chap10 Lemma 10 129 2: membership in the zero-locus regular-sequence locus is the
regularity of the corresponding list in the fiber local ring. -/
private theorem mem_fiberLocalRingRegularSequenceLocus_iff_isRegularSequence
    (fs : List S) (q : V((Ideal.ofList fs : Set S))) :
    q ∈ fiberLocalRingRegularSequenceLocus R S fs ↔
      RingTheory.Sequence.IsRegular (fiberLocalRingAt R S q.1)
        (fs.map (toFiberLocalRingAt R S q.1)) := by
  -- Proof comment: first unfold membership in the locus, then remove the wrapper predicate.
  rw [mem_fiberLocalRingRegularSequenceLocus_iff,
    isRegularInFiberLocalRing_iff_isRegularSequence]

/-- Helper for Chap10 Lemma 10 129 2: a point of the locus gives a regular sequence in the
corresponding fiber local ring. -/
private theorem regularSequence_of_mem_fiberLocalRingRegularSequenceLocus
    {fs : List S} {q : V((Ideal.ofList fs : Set S))}
    (hq : q ∈ fiberLocalRingRegularSequenceLocus R S fs) :
    RingTheory.Sequence.IsRegular (fiberLocalRingAt R S q.1)
      (fs.map (toFiberLocalRingAt R S q.1)) := by
  -- Proof comment: this is the forward direction of the pointwise membership criterion above.
  exact (mem_fiberLocalRingRegularSequenceLocus_iff_isRegularSequence
    (R := R) (S := S) fs q).mp hq

/-- Helper for Chap10 Lemma 10 129 2: the order height of `fiberPrimeAt R T q` is the same as
the height of the corresponding point of the fiber over `PrimeSpectrum.comap (algebraMap R T) q`.
-/
private lemma fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq
    {T : Type*} [CommRing T] [Algebra R T]
    {p : PrimeSpectrum R} (q : PrimeSpectrum T)
    (hq : PrimeSpectrum.comap (algebraMap R T) q = p) :
    Order.height (fiberPrimeAt R T q) =
      Order.height
        (⟨q, hq⟩ : (PrimeSpectrum.comap (algebraMap R T)) ⁻¹' {p}) := by
  -- Proof comment: replace the named base point by the actual contraction of `q`, so the fiber
  -- order isomorphism is definitionally the one used to build `fiberPrimeAt`.
  subst p
  let p0 : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R T) q
  let qOver : ↑(PrimeSpectrum.comap (algebraMap R T) ⁻¹' {p0}) := ⟨q, rfl⟩
  let ePre : ↑(PrimeSpectrum.comap (algebraMap R T) ⁻¹' {p0}) ≃o
      PrimeSpectrum (p0.asIdeal.Fiber T) :=
    PrimeSpectrum.preimageOrderIsoFiber R T p0
  have heq : ePre qOver = fiberPrimeAt R T q := rfl
  calc
    Order.height (fiberPrimeAt R T q) = Order.height (ePre qOver) := by
      exact congrArg Order.height heq.symm
    _ = Order.height qOver := Order.height_orderIso ePre qOver
    _ =
        Order.height
          (⟨q, rfl⟩ : (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R T) q}) := rfl

/-- Helper for Chap10 Lemma 10 129 2: pointwise bounds on `relativeDimensionAt R T` over a fixed
fiber bound the Krull dimension of that whole fiber. -/
private lemma ringKrullDim_fiber_le_of_forall_relativeDimensionAt_le
    {T : Type*} [CommRing T] [Algebra R T]
    (p : PrimeSpectrum R) (d : WithBot ℕ∞)
    (h : ∀ q : PrimeSpectrum T, PrimeSpectrum.comap (algebraMap R T) q = p →
      relativeDimensionAt R T q ≤ d) :
    ringKrullDim (p.asIdeal.Fiber T) ≤ d := by
  -- Proof comment: it is enough to bound the height of every maximal ideal of the fiber, and
  -- those heights are exactly the relative dimensions at the corresponding primes of `Spec(T)`.
  refine (ringKrullDim_le_iff_isMaximal_height_le d).2 ?_
  intro J hJ
  let qF : PrimeSpectrum (p.asIdeal.Fiber T) := ⟨J, hJ.isPrime⟩
  let ePre : ↑(PrimeSpectrum.comap (algebraMap R T) ⁻¹' {p}) ≃o
      PrimeSpectrum (p.asIdeal.Fiber T) :=
    PrimeSpectrum.preimageOrderIsoFiber R T p
  let qOver := ePre.symm qF
  have hqF_height :
      ((J.height : ℕ∞) : WithBot ℕ∞) = (Order.height qOver : WithBot ℕ∞) := by
    calc
      ((J.height : ℕ∞) : WithBot ℕ∞) = (Order.height qF : WithBot ℕ∞) := by
        rw [Ideal.height_eq_primeHeight]
        rfl
      _ = (Order.height (ePre qOver) : WithBot ℕ∞) := by
        rw [show ePre qOver = qF by simp [qOver, ePre, qF]]
      _ = (Order.height qOver : WithBot ℕ∞) := by
        rw [Order.height_orderIso ePre qOver]
  have hrel_height :
      relativeDimensionAt R T qOver.1 = (Order.height qOver : WithBot ℕ∞) := by
    calc
      relativeDimensionAt R T qOver.1 =
          ringKrullDim (fiberLocalRingAt R T qOver.1) := rfl
      _ = ((fiberPrimeAt R T qOver.1).asIdeal.height : WithBot ℕ∞) := by
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height
            (fiberPrimeAt R T qOver.1).asIdeal (fiberLocalRingAt R T qOver.1)]
      _ = (Order.height (fiberPrimeAt R T qOver.1) : WithBot ℕ∞) := by
          rw [Ideal.height_eq_primeHeight]
          rfl
      _ = (Order.height qOver : WithBot ℕ∞) := by
          rw [fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq
            (R := R) (T := T) qOver.1 qOver.2]
  have hrel : relativeDimensionAt R T qOver.1 ≤ d := h qOver.1 qOver.2
  rwa [hqF_height, ← hrel_height]

/-- Helper for Chap10 Lemma 10 129 2: the quotient presentation of the localized fiber ring is
unchanged after localizing away from an element. -/
private lemma ringKrullDim_quotient_localizationAway_comap
    {T : Type*} [CommRing T] [Algebra R T]
    (g : T) (qg : PrimeSpectrum (Localization.Away g)) :
    let q := PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qg
    ringKrullDim
        ((Localization.AtPrime qg.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
            (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)) =
      ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (Ideal.comap (algebraMap R T) q.asIdeal)) := by
  intro q
  -- Proof comment: first compare the two prime localizations, then transport the extended base
  -- ideal through that localization equivalence.
  let qI : Ideal T := Ideal.comap (algebraMap T (Localization.Away g)) qg.asIdeal
  have hqI : q.asIdeal = Ideal.comap (AlgEquiv.refl : T ≃ₐ[T] T) qI := by
    have hq : q.asIdeal = qI := by
      simpa [qI, q] using
        (PrimeSpectrum.comap_asIdeal (f := algebraMap T (Localization.Away g)) qg)
    rw [hq]
    exact (Ideal.comap_id qI).symm
  let eSource : Localization.AtPrime q.asIdeal ≃ₐ[T] Localization.AtPrime qI :=
    Localization.localAlgEquiv q.asIdeal qI (AlgEquiv.refl : T ≃ₐ[T] T) hqI
  let eTower : Localization.AtPrime qI ≃ₐ[T] Localization.AtPrime qg.asIdeal :=
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := Submonoid.powers g) qg.asIdeal)
  let e : Localization.AtPrime q.asIdeal ≃ₐ[T] Localization.AtPrime qg.asIdeal :=
    eSource.trans eTower
  let Iq : Ideal (Localization.AtPrime q.asIdeal) :=
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
      (Ideal.comap (algebraMap R T) q.asIdeal)
  let Ig : Ideal (Localization.AtPrime qg.asIdeal) :=
    Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
      (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)
  have hbase :
      Ideal.comap (algebraMap R T) q.asIdeal =
        Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal := by
    simpa [q, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap,
      IsScalarTower.algebraMap_eq R T (Localization.Away g)]
  have heR : e.toRingHom.comp (algebraMap R (Localization.AtPrime q.asIdeal)) =
      algebraMap R (Localization.AtPrime qg.asIdeal) := by
    ext r
    change e ((algebraMap R (Localization.AtPrime q.asIdeal)) r) =
      algebraMap R (Localization.AtPrime qg.asIdeal) r
    calc
      e ((algebraMap R (Localization.AtPrime q.asIdeal)) r) =
          e (algebraMap T (Localization.AtPrime q.asIdeal) (algebraMap R T r)) := by
            rw [IsScalarTower.algebraMap_apply R T (Localization.AtPrime q.asIdeal)]
      _ = algebraMap T (Localization.AtPrime qg.asIdeal) (algebraMap R T r) := by
            exact e.commutes (algebraMap R T r)
      _ = algebraMap R (Localization.AtPrime qg.asIdeal) r := by
            rw [IsScalarTower.algebraMap_apply R T (Localization.AtPrime qg.asIdeal)]
  have hmap : Ig = Ideal.map e.toRingHom Iq := by
    calc
      Ig = Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
          (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal) := rfl
      _ = Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
          (Ideal.comap (algebraMap R T) q.asIdeal) := by
            rw [← hbase]
      _ = Ideal.map (e.toRingHom.comp (algebraMap R (Localization.AtPrime q.asIdeal)))
          (Ideal.comap (algebraMap R T) q.asIdeal) := by
            rw [heR]
      _ = Ideal.map e.toRingHom Iq := by
            rw [Ideal.map_map]
  let eQuot :
      ((Localization.AtPrime q.asIdeal) ⧸ Iq) ≃+*
        ((Localization.AtPrime qg.asIdeal) ⧸ Ig) :=
    Ideal.quotientEquiv Iq Ig e.toRingEquiv hmap
  -- Proof comment: Krull dimension is invariant under the induced quotient equivalence.
  exact (ringKrullDim_eq_of_ringEquiv eQuot).symm

/-- Helper for Chap10 Lemma 10 129 2: relative dimension is unchanged after localizing away from
an element and then pulling back along the localization comap. -/
private lemma relativeDimensionAt_localizationAway_comap
    {T : Type*} [CommRing T] [Algebra R T]
    (g : T) (qg : PrimeSpectrum (Localization.Away g)) :
    relativeDimensionAt R (Localization.Away g) qg =
      relativeDimensionAt R T (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qg) := by
  -- Proof comment: compare the two fiber local rings through their canonical quotient
  -- presentations, exactly as in the relative-dimension owner theorem.
  let q := PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qg
  calc
    relativeDimensionAt R (Localization.Away g) qg =
        ringKrullDim (fiberLocalRingAt R (Localization.Away g) qg) := rfl
    _ = ringKrullDim
        ((Localization.AtPrime qg.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
            (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)) := by
          rw [← ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
            (R := R) (S := Localization.Away g) qg]
    _ = ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (Ideal.comap (algebraMap R T) q.asIdeal)) := by
          exact ringKrullDim_quotient_localizationAway_comap (R := R) (T := T) g qg
    _ = ringKrullDim (fiberLocalRingAt R T q) := by
          rw [ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
            (R := R) (S := T) q]
    _ = relativeDimensionAt R T q := rfl

/-- Helper for Chap10 Lemma 10 129 2: any open neighbourhood in `Spec A` can be shrunk to a
basic open neighbourhood while preserving containment in a target set. -/
private theorem exists_basicOpen_subset_of_openNhds
    {A : Type*} [CommRing A] (q : PrimeSpectrum A) (s : Set (PrimeSpectrum A))
    (U : TopologicalSpace.OpenNhdsOf q) (hU : ∀ q' ∈ U, q' ∈ s) :
    ∃ g : A, q ∈ PrimeSpectrum.basicOpen g ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆ s := by
  -- Proof comment: the Zariski basic opens form a basis, so we refine the given neighborhood to
  -- one basic open through `q` and then keep the original subset relation.
  obtain ⟨_, ⟨g, rfl⟩, hqg, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.1.2 q U.2
  refine ⟨g, hqg, ?_⟩
  intro q' hq'
  exact hU q' (hgU hq')

variable [Algebra.FiniteType R S]

-- Proof sketch: for `q` in the locus, pass to the quotient `S ⧸ Ideal.ofList fs`. The fiber over
-- `q ∩ R` stays Cohen--Macaulay and equidimensional, and `hConstDim` identifies its Krull
-- dimension with that of every other fiber. Regularity of `fs` in the local fiber ring gives the
-- expected dimension drop by `fs.length` for the quotient fiber. Lemma `10.125.6` should then
-- yield an open neighborhood on which all quotient fibers have relative dimension bounded by this
-- common fiber dimension minus `fs.length`, and Lemma `10.129.1` upgrades that bound to
-- regularity of the localized sequence at every nearby point.
/-- Lemma 10.129.2: let `R → S` be a finite type ring map, and let `fs` be a finite list of
elements of `S`. Assume every fiber `κ(𝔭) ⊗[R] S` is Cohen--Macaulay and equidimensional, and
that these fibers all have the same Krull dimension. Then the primes `q` of `S` containing
`Ideal.ofList fs` for which the images of `fs` form a regular sequence in the local fiber ring at
`q` form an open subset of `V(Ideal.ofList fs)`. -/
@[stacks 00RA]
theorem isOpen_fiberLocalRingRegularSequenceLocusWithinZeroLocus_of_fiberwise_cohenMacaulay_equidimensional
    (fs : List S)
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S))
    (hEqdim : ∀ p : PrimeSpectrum R,
      TopologicalSpace.EquidimensionalSpace (PrimeSpectrum (p.asIdeal.Fiber S)))
    (hConstDim : ∀ p p' : PrimeSpectrum R,
      ringKrullDim (p.asIdeal.Fiber S) = ringKrullDim (p'.asIdeal.Fiber S)) :
    IsOpen (fiberLocalRingRegularSequenceLocus R S fs) := by
  -- Proof comment: the local part of the source argument is already available here. A point of
  -- the locus gives a regular sequence in its fiber local ring, and the remaining step is to
  -- shrink to a zero-locus neighborhood where the quotient fibers satisfy the uniform
  -- relative-dimension bound required by `Lemma 10.129.1`.
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hreg :
      RingTheory.Sequence.IsRegular (fiberLocalRingAt R S q.1)
        (fs.map (toFiberLocalRingAt R S q.1)) :=
    regularSequence_of_mem_fiberLocalRingRegularSequenceLocus
      (R := R) (S := S) hq
  let I : Ideal S := Ideal.ofList fs
  let T : Type v := S ⧸ I
  let qbar : PrimeSpectrum T :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q.1
  let d : WithBot ℕ∞ := ringKrullDim (p.asIdeal.Fiber S)
  -- Route correction: the viable local route is to pass to the quotient ring and shrink to a
  -- basic-open neighborhood where the quotient fibers satisfy a uniform relative-dimension bound.
  -- The localization-away transport needed for that route is now available in the helper lemmas
  -- above. The remaining blocker is still the bounded-neighborhood owner: importing
  -- `Lemma_10_125_6` rebuilds the broken upstream file `Lemma_10_125_2`, so this file still
  -- lacks a dependency-closed theorem producing a basic open in the quotient with uniformly
  -- bounded `relativeDimensionAt`.
  -- Proof comment: the next local step would be to show
  -- `relativeDimensionAt R T qbar = d - fs.length`, invoke the missing owner theorem
  -- `exists_openNhdsOf_relativeDimensionAt_eq` on the quotient ring `T`, and then shrink that
  -- neighborhood with `exists_basicOpen_subset_of_openNhds` before using the transport lemmas
  -- above together with `Lemma 10.129.1`.
  let _ := hreg
  let _ := qbar
  let _ := d
  sorry

end
