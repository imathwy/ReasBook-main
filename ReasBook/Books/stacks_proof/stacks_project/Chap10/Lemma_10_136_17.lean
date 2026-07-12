import Mathlib
import StacksProject_2024.Chap10.Definition_10_112_5
import StacksProject_2024.Chap10.Definition_10_135_1
import StacksProject_2024.Chap10.Definition_10_136_5
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Lemma_10_135_2
import StacksProject_2024.Chap10.Lemma_10_136_3
import StacksProject_2024.Chap10.Lemma_10_136_4
import StacksProject_2024.Chap10.Lemma_10_136_9
import StacksProject_2024.Chap10.Lemma_10_136_15
import StacksProject_2024.Chap10.Lemma_10_136_17_Support

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Algebra.TensorProduct.leftAlgebra

/- Domain-style sampling:
- primary domain: composition stability for syntomic ring maps and relative global complete
  intersections in commutative algebra;
- inspected owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Flat.comp`,
  `RingHom.FinitePresentation.comp`,
  `RingHom.Syntomic.ofLocalizationSpanTarget`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`;
- best owner abstractions:
  `RingHom.Syntomic` is a ring-hom property, so its canonical composition API should expose the
  owner-namespace theorem `RingHom.Syntomic.comp`, with the bundled witness
  `RingHom.Syntomic.stableUnderComposition` as derived API;
  `Algebra.IsRelativeGlobalCompleteIntersection R S` is already the source-facing algebra owner,
  so composition belongs in the owner namespace rather than as a parallel freestanding theorem;
- primitive vs. derived:
  flatness, finite presentation, and chosen presentation data remain derived API from the two
  owners and should not be repackaged here.
-/

namespace Algebra

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']

/-- Helper for Chap10 Lemma 10 136 17: the fiber of the composite algebra is canonically the base
change of the second algebra to the first fiber. -/
private noncomputable def fiberCompAlgEquivBaseChange (p : PrimeSpectrum R) :
    p.asIdeal.Fiber S' ≃ₐ[p.asIdeal.ResidueField] (p.asIdeal.Fiber S ⊗[S] S') :=
  let F := p.asIdeal.Fiber S
  letI : Algebra S F := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower R S F := inferInstance
  (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField S F S').symm

/-- Helper for Chap10 Lemma 10 136 17: the fiber of the composite algebra has the same Krull
dimension as the base change of the second algebra to the first fiber. -/
private theorem fiberComp_ringKrullDim_eq_baseChange (p : PrimeSpectrum R) :
    ringKrullDim (p.asIdeal.Fiber S') = ringKrullDim (p.asIdeal.Fiber S ⊗[S] S') := by
  -- Proof comment: transport Krull dimension across the canonical tensor/base-change equivalence.
  exact ringKrullDim_eq_of_ringEquiv (fiberCompAlgEquivBaseChange (R := R) (S := S) (S' := S') p).toRingEquiv

/-- Helper for Chap10 Lemma 10 136 17: nonemptiness of the composite fiber prime spectrum
transfers across the canonical tensor/base-change equivalence. -/
private theorem fiberComp_nonempty_baseChange
    (p : PrimeSpectrum R) (hp : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S'))) :
    Nonempty (PrimeSpectrum (p.asIdeal.Fiber S ⊗[S] S')) := by
  -- Route correction: instead of transporting `Nontrivial` across the algebra equivalence, move
  -- an explicit prime through the inverse ring homomorphism.  This avoids the brittle
  -- `nontrivial_congr` bridge entirely.
  let e := fiberCompAlgEquivBaseChange (R := R) (S := S) (S' := S') p
  rcases hp with ⟨q⟩
  exact ⟨PrimeSpectrum.comap e.symm.toRingHom q⟩

/-- Helper for Chap10 Lemma 10 136 17: a prime of the tensor-product fiber contracts to a prime
of the first fiber. -/
private theorem nonemptyFiber_of_nonemptyTensorFiber
    (p : PrimeSpectrum R)
    (hp : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S ⊗[S] S'))) :
    Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) := by
  -- Proof comment: contract any prime of the tensor-product fiber along the base algebra map to
  -- obtain a prime of the first fiber.
  let F := p.asIdeal.Fiber S
  let B := F ⊗[S] S'
  rcases hp with ⟨q⟩
  exact ⟨PrimeSpectrum.comap (algebraMap F B) q⟩

/-- Helper for Chap10 Lemma 10 136 17: reindexing a presentation along `equivFin` preserves its
numerical dimension. -/
private theorem presentationDimension_reindex_equivFin
    {A : Type*} [CommRing A] [Algebra R A]
    {ι τ : Type*} [Fintype ι] [Fintype τ]
    (P : Algebra.Presentation R A ι τ) :
    P.dimension =
      (P.reindex (Fintype.equivFin ι).symm (Fintype.equivFin τ).symm).dimension := by
  -- Proof comment: package the standard reindex formula once so later composite-presentation
  -- arguments avoid repeating the same equivalence bookkeeping.
  simpa using
    (Algebra.Presentation.dimension_reindex P
      (Fintype.equivFin ι).symm
      (Fintype.equivFin τ).symm)


/-- Helper for Chap10 Lemma 10 136 17: base-changing both presentations preserves the composite
dimension. -/
private theorem baseChangedCompPresentation_dimension
    {n c n' c' : ℕ}
    (P : Algebra.Presentation R S (Fin n) (Fin c))
    (Q : Algebra.Presentation S S' (Fin n') (Fin c'))
    (p : PrimeSpectrum R) :
    ((Q.baseChange (p.asIdeal.Fiber S)).comp (P.baseChange p.asIdeal.ResidueField)).dimension =
      (Q.comp P).dimension := by
  -- Proof comment: both sides count the same generators and relations after replacing the two
  -- base rings by the residue field and first fiber, so the dimension formula is unchanged.
  simp [Algebra.Presentation.dimension, Fintype.card_sum, Nat.add_comm, Nat.add_assoc]

/-- Helper for Chap10 Lemma 10 136 17: after base change, the composite presentation dimension is
the sum of the two base-changed presentation dimensions. -/
private theorem baseChangedCompPresentation_dimension_add
    {n c n' c' : ℕ}
    (P : Algebra.Presentation R S (Fin n) (Fin c))
    (Q : Algebra.Presentation S S' (Fin n') (Fin c'))
    (p : PrimeSpectrum R) :
    (P.baseChange p.asIdeal.ResidueField).dimension +
        (Q.baseChange (p.asIdeal.Fiber S)).dimension =
      ((Q.baseChange (p.asIdeal.Fiber S)).comp (P.baseChange p.asIdeal.ResidueField)).dimension := by
  -- Proof comment: composition concatenates the generator and relation index sets, and base
  -- change leaves those finite-cardinality counts unchanged.
  simp [Algebra.Presentation.dimension, Fintype.card_sum, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

/-- Helper for Chap10 Lemma 10 136 17: once the composite fiber is rewritten as a tensor base
change, the remaining dimension computation is the field-level composition step. -/
private theorem fiberBaseChange_ringKrullDim_eq_compPresentationDimension
    {n c n' c' : ℕ}
    (P : Algebra.Presentation R S (Fin n) (Fin c))
    (Q : Algebra.Presentation S S' (Fin n') (Fin c'))
    (hP : P.IsRelativeGlobalCompleteIntersection)
    (hQ : Q.IsRelativeGlobalCompleteIntersection)
    (p : PrimeSpectrum R)
    (hp : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S ⊗[S] S'))) :
    ringKrullDim (p.asIdeal.Fiber S ⊗[S] S') = (Q.comp P).dimension := by
  let k := p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber S
  have hpF : Nonempty (PrimeSpectrum F) :=
    nonemptyFiber_of_nonemptyTensorFiber (R := R) (S := S) (S' := S') p hp
  have hPbase : ringKrullDim F = (P.baseChange k).dimension := by
    -- Proof comment: the first witness specializes to the fiber over `p`, and base change does
    -- not alter the numerical presentation dimension.
    simpa [Algebra.Presentation.dimension] using hP p hpF
  have hQBase :
      (Q.baseChange F).IsRelativeGlobalCompleteIntersection := by
    -- Proof comment: the second presentation witness remains relatively GCI after base change to
    -- the first fiber.
    exact Algebra.Presentation.IsRelativeGlobalCompleteIntersection.baseChange
      (R' := F) hQ
  have hcompDim :
      (P.baseChange k).dimension + (Q.baseChange F).dimension =
        ((Q.baseChange F).comp (P.baseChange k)).dimension := by
    -- Proof comment: use the dedicated arithmetic normalization for the base-changed composite
    -- presentation instead of replaying the cardinality simp locally.
    simpa [k, F] using
      baseChangedCompPresentation_dimension_add (R := R) (S := S) (S' := S')
        (P := P) (Q := Q) p
  -- Route correction: the existing field-level composition theorem already applies to the
  -- base-changed witnesses once their arithmetic dimension compatibility is stated explicitly.
  calc
    ringKrullDim (p.asIdeal.Fiber S ⊗[S] S') =
        ((Q.baseChange F).comp (P.baseChange k)).dimension := by
          exact fieldCompPresentation_ringKrullDim
            (P := P.baseChange k) (Q := Q.baseChange F) hPbase hQBase hcompDim hp
    _ = (Q.comp P).dimension := by
          simpa [k, F] using
            baseChangedCompPresentation_dimension (R := R) (S := S) (S' := S')
              (P := P) (Q := Q) p

namespace IsRelativeGlobalCompleteIntersection

-- Proof sketch: choose relative global complete intersection presentations for `S` over `R` and
-- for `S'` over `S`, concatenate the generators and lifted relations to obtain a presentation of
-- `S'` over `R`, and then bound the fiber dimensions by additivity of dimensions along the finite
-- type map between the fibers.
/-- Chap10 Lemma 10 136 17 (2): relative global complete intersections are stable under
composition. -/
@[stacks 00SZ]
theorem comp (hRS : IsRelativeGlobalCompleteIntersection R S)
    (hSS' : IsRelativeGlobalCompleteIntersection S S') :
    IsRelativeGlobalCompleteIntersection R S' := by
  -- The source proof composes finite presentations and reindexes the resulting sum-indexed
  -- presentation back to `Fin` index types.
  rcases hRS.exists_presentation with ⟨n, c, P, hP⟩
  rcases hSS'.exists_presentation with ⟨n', c', Q, hQ⟩
  let C : Algebra.Presentation R S'
      (Fin (Fintype.card (Fin n' ⊕ Fin n))) (Fin (Fintype.card (Fin c' ⊕ Fin c))) :=
    (Q.comp P).reindex
      (Fintype.equivFin (Fin n' ⊕ Fin n)).symm
      (Fintype.equivFin (Fin c' ⊕ Fin c)).symm
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := C) ?_
  intro p hp
  -- Proof comment: first rewrite the composite fiber to the tensor base-change model, then reduce
  -- the remaining dimension formula to the composed presentation before reindexing back to `Fin`.
  have hpBase : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S ⊗[S] S')) :=
    fiberComp_nonempty_baseChange (R := R) (S := S) (S' := S') p hp
  calc
    ringKrullDim (p.asIdeal.Fiber S')
        = ringKrullDim (p.asIdeal.Fiber S ⊗[S] S') := by
            rw [fiberComp_ringKrullDim_eq_baseChange (R := R) (S := S) (S' := S') p]
    _ = (Q.comp P).dimension := by
          exact fiberBaseChange_ringKrullDim_eq_compPresentationDimension
            (P := P) (Q := Q) hP hQ p hpBase
    _ = C.dimension := by
          simpa [C] using
            (presentationDimension_reindex_equivFin (R := R) (P := Q.comp P)).symm

end IsRelativeGlobalCompleteIntersection

end Algebra

namespace RingHom

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']

/-- Helper for Chap10 Lemma 10 136 17: the unit element avoids every prime ideal. -/
private theorem one_notMem_primeSpectrum_asIdeal
    {A : Type*} [CommRing A] (q : PrimeSpectrum A) :
    (1 : A) ∉ q.asIdeal := by
  -- Proof comment: a prime ideal is proper, so it cannot contain `1`.
  simpa [Ideal.eq_top_iff_one] using q.2.ne_top

/-- Helper for Chap10 Lemma 10 136 17: composing the base algebra map with the trivial
localization map `A → A[1⁻¹]` is the base algebra map into the localization. -/
private theorem localizationAwayOne_comp_algebraMap
    {A : Type*} [CommRing A] [Algebra R A] :
    (algebraMap A (Localization.Away (1 : A))).comp (algebraMap R A) =
      algebraMap R (Localization.Away (1 : A)) := by
  -- Proof comment: both ring homomorphisms send `r : R` to the same element by definition.
  ext r
  rfl

/-- Helper for Chap10 Lemma 10 136 17: the trivial chart `D(1)` of a syntomic algebra is
finitely presented over the base. -/
private theorem finitePresentation_localizationAway_one_of_syntomic
    {A : Type*} [CommRing A] [Algebra R A]
    (hA : (algebraMap R A).Syntomic) :
    Algebra.FinitePresentation R (Localization.Away (1 : A)) := by
  -- Proof comment: compose the finite-presentation algebra map with the finite-presentation
  -- localization map on the trivial chart.
  have hloc :
      (algebraMap A (Localization.Away (1 : A))).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr
      (IsLocalization.Away.finitePresentation (S := Localization.Away (1 : A)) (1 : A))
  have hcomp :
      ((algebraMap A (Localization.Away (1 : A))).comp (algebraMap R A)).FinitePresentation :=
    RingHom.FinitePresentation.comp hloc hA.finitePresentation
  -- Proof comment: rewrite the composed algebra map to the canonical algebra map into the
  -- localization, then read off finite presentation.
  exact (RingHom.finitePresentation_algebraMap).mp <|
    localizationAwayOne_comp_algebraMap (R := R) (A := A) ▸ hcomp

/-- Helper for Chap10 Lemma 10 136 17: a syntomic algebra has a relative global
complete-intersection principal-open neighborhood at every prime. -/
private theorem relativeGciNeighborhoodOfSyntomicAtPrime
    {A : Type*} [CommRing A] [Algebra R A]
    (hA : (algebraMap R A).Syntomic) (q : PrimeSpectrum A) :
    ∃ g : A, g ∉ q.asIdeal ∧ Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) :=
by
  have hone : (1 : A) ∉ q.asIdeal := one_notMem_primeSpectrum_asIdeal q
  have hfiber :
      Algebra.FiberCompleteIntersectionAtPrime R q := by
    -- Proof comment: the syntomic fiber hypothesis already gives a local complete intersection on
    -- the residue-field fiber, and the prime-local TFAE upgrades that to the required stalkwise
    -- complete-intersection statement.
    have hFibers :
        (algebraMap R A).HasLocalCompleteIntersectionFibers :=
      hA.hasLocalCompleteIntersectionFibers
    rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap] at hFibers
    have hlocal :
        _root_.IsLocalCompleteIntersection (q.asIdeal.under R).ResidueField
          ((q.asIdeal.under R).Fiber A) := by
      simpa [Ideal.under] using hFibers (PrimeSpectrum.comap (algebraMap R A) q)
    letI :
        _root_.IsLocalCompleteIntersection (q.asIdeal.under R).ResidueField
          ((q.asIdeal.under R).Fiber A) := hlocal
    letI :
        Algebra.FiniteType (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber A) :=
      inferInstance
    have hfiberTFAE :=
      completeIntersectionOver_atPrime_tfae
        (k := (q.asIdeal.under R).ResidueField)
        (S := (q.asIdeal.under R).Fiber A)
        (fiberPrimeAt R A q)
    have honeFiber :
        (1 : (q.asIdeal.under R).Fiber A) ∉ (fiberPrimeAt R A q).asIdeal :=
      one_notMem_primeSpectrum_asIdeal (fiberPrimeAt R A q)
    have hnear :
        isLocalCompleteIntersectionNearPrime
          (q.asIdeal.under R).ResidueField
          (fiberPrimeAt R A q) := ⟨1, honeFiber, inferInstance⟩
    simpa [Algebra.FiberCompleteIntersectionAtPrime, fiberLocalRingAt] using
      (hfiberTFAE.out 1 0 rfl rfl).mp hnear
  have hpackaged :
      Algebra.FinitePresentationFlatAndFiberCompleteIntersectionAtPrime R q := by
    -- Proof comment: clause `(3)` of the at-prime TFAE is realized on the trivial chart `D(1)`.
    refine ⟨1, hone, ?_, ?_, hfiber⟩
    · exact finitePresentation_localizationAway_one_of_syntomic (R := R) hA
    · simpa using RingHom.Flat.localRingHom hA.flat q.asIdeal (q.asIdeal.under R) rfl
  have hTFAE := Algebra.syntomicAtPrime_tfae (R := R) (S := A) q
  have hrgciAtPrime :
      Algebra.RelativeGlobalCompleteIntersectionAtPrime R q :=
    (hTFAE.out 2 1 rfl rfl).mp hpackaged
  -- Proof comment: the public TFAE already packages the desired RGCI neighborhood at `q`.
  simpa using hrgciAtPrime

/-- Helper for Chap10 Lemma 10 136 17: base changing an away localization along `S → S'`
identifies the tensor product with the corresponding away localization of `S'`. -/
private noncomputable def tensorRightAwayAlgEquiv
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] (x : S) :
    Localization.Away x ⊗[S] S' ≃ₐ[Localization.Away x]
      Localization.Away (algebraMap S S' x) :=
  Localization.tensorRightAlgEquiv (Submonoid.powers x) S'

/-- Helper for Chap10 Lemma 10 136 17: a prime avoiding an away parameter lifts to the away
localization. -/
private theorem exists_primeSpectrum_away_comap_eq_of_notMem
    {A : Type*} [CommRing A] (p : PrimeSpectrum A) {f : A} (hf : f ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap A (Localization.Away f)) q = p := by
  -- Proof comment: the image of `Spec(A_f)` is exactly the basic open `D(f)`.
  have hp_range : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    simpa [PrimeSpectrum.mem_basicOpen] using hf
  exact Set.mem_range.mp hp_range

/-- Helper for Chap10 Lemma 10 136 17: a comap equality turns membership in the target prime into
membership in the source prime, and conversely. -/
private theorem map_mem_asIdeal_iff_of_comap_eq
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    (hcomap : PrimeSpectrum.comap f q = p) (x : A) :
    f x ∈ q.asIdeal ↔ x ∈ p.asIdeal := by
  have hcomapIdeal : Ideal.comap f q.asIdeal = p.asIdeal := by
    -- Proof comment: rewrite the prime-spectrum comap equality at the ideal layer.
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap
  -- Proof comment: membership in the contracted ideal is definitionally the target membership.
  change x ∈ Ideal.comap f q.asIdeal ↔ x ∈ p.asIdeal
  simpa [hcomapIdeal]

/-- Helper for Chap10 Lemma 10 136 17: an RGCI neighborhood transports across an algebra
equivalence after rewriting the source prime into the corresponding comap form. -/
private theorem existsLocalizedRgciNeighborhood_of_algEquivSourceNeighborhood
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (qA : PrimeSpectrum A) (qB : PrimeSpectrum B)
    (hqA : qA = PrimeSpectrum.comap e.toRingHom qB)
    (h :
      ∃ u : A,
        u ∉ qA.asIdeal ∧
          Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away u)) :
    ∃ v : B,
      v ∉ qB.asIdeal ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away v) := by
  -- Proof comment: rewrite the source prime to the comap spelling so the chosen denominator can
  -- be pushed across `e`, then transport the localized RGCI chart along the induced
  -- equivalence of away localizations.
  subst qA
  rcases h with ⟨u, huqA, huRGCI⟩
  let eAway : Localization.Away u ≃ₐ[R] Localization.Away (e u) :=
    IsLocalization.algEquivOfAlgEquiv
      (A := R)
      (S := Localization.Away u)
      (Q := Localization.Away (e u))
      e
      (Submonoid.map_powers e u)
  refine ⟨e u, ?_, ?_⟩
  · -- Proof comment: membership in the comapped prime is computed through `e`, so nonvanishing
    -- of the chosen denominator is preserved.
    intro heuq
    exact huqA (by
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using heuq)
  · -- Proof comment: the RGCI property is intrinsic to the localized chart and therefore
    -- transfers across the induced algebra equivalence.
    exact Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv huRGCI eAway

/-- Helper for Chap10 Lemma 10 136 17: an iterated away localization of a principal open is a
single principal open of the original ring. -/
private theorem singleOriginalAwayAlgEquiv
    [Algebra R S']
    (g : S') (u : Localization.Away g) :
    let h : S' := g * (IsLocalization.Away.sec g u).1
    Nonempty (Localization.Away u ≃ₐ[R] Localization.Away h) := by
  let a : S' := (IsLocalization.Away.sec g u).1
  let h : S' := g * a
  let hassoc :
      Associated (algebraMap S' (Localization.Away g) a) u :=
    IsLocalization.Away.associated_sec_fst g u
  letI :
      IsLocalization.Away u (Localization.Away (algebraMap S' (Localization.Away g) a)) :=
    IsLocalization.Away.of_associated hassoc
  let eIter :
      Localization.Away u ≃ₐ[R] Localization.Away (algebraMap S' (Localization.Away g) a) :=
    (Localization.algEquiv
      (Submonoid.powers u)
      (Localization.Away (algebraMap S' (Localization.Away g) a))).restrictScalars R
  letI :
      IsLocalization.Away h (Localization.Away (algebraMap S' (Localization.Away g) a)) := by
    -- Proof comment: once the cleared denominator is definitionally `g * a`, the iterated away
    -- chart is also an away localization at that single element.
    simpa [h] using
      (inferInstance :
        IsLocalization.Away h (Localization.Away (algebraMap S' (Localization.Away g) a)))
  let eSingle :
      Localization.Away (algebraMap S' (Localization.Away g) a) ≃ₐ[R] Localization.Away h :=
    (Localization.algEquiv
      (Submonoid.powers h)
      (Localization.Away (algebraMap S' (Localization.Away g) a))).symm.restrictScalars R
  -- Proof comment: compare the iterated localization with the single cleared denominator through
  -- the common middle away localization.
  exact ⟨eIter.trans eSingle⟩

/-- Helper for Chap10 Lemma 10 136 17: clearing the denominator of an iterated away localization
keeps the resulting element outside the original prime. -/
private theorem notMem_original_away_of_iterated_away
    (q : PrimeSpectrum S') {g : S'} (hg : g ∉ q.asIdeal)
    (qAway : PrimeSpectrum (Localization.Away g))
    (hqAway : PrimeSpectrum.comap (algebraMap S' (Localization.Away g)) qAway = q)
    {u : Localization.Away g} (hu : u ∉ qAway.asIdeal) :
    g * (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
  -- Proof comment: if the section numerator landed in the lifted prime, associatedness would
  -- force `u` into the same prime.
  have hsec_not_mem_away :
      algebraMap S' (Localization.Away g) (IsLocalization.Away.sec g u).1 ∉ qAway.asIdeal := by
    intro hsec_mem
    have hu_mem : u ∈ qAway.asIdeal := by
      exact (Ideal.mem_iff_of_associated
        (IsLocalization.Away.associated_sec_fst g u)).mp hsec_mem
    exact hu hu_mem
  have hsec_not_mem :
      (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
    intro hsec_mem
    have hmap_mem :
        algebraMap S' (Localization.Away g) (IsLocalization.Away.sec g u).1 ∈ qAway.asIdeal := by
      exact
        (map_mem_asIdeal_iff_of_comap_eq
          (algebraMap S' (Localization.Away g)) hqAway (IsLocalization.Away.sec g u).1).mpr
          hsec_mem
    exact hsec_not_mem_away hmap_mem
  exact q.2.mul_notMem hg hsec_not_mem

/-- Helper for Chap10 Lemma 10 136 17: every prime of the target of a composite of syntomic maps
has a principal-open neighborhood that is a relative global complete intersection over the
source. -/
private theorem pointwiseRelativeGciChartOfSyntomicComp
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    {f : R →+* S} {g : S →+* S'} (hf : f.Syntomic) (hg : g.Syntomic)
    (q' : PrimeSpectrum S') :
    ∃ z : S', z ∉ q'.asIdeal ∧ Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away z) :=
by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra S S' := g.toAlgebra
  let _ : Algebra R S' := (g.comp f).toAlgebra
  let _ : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S') q'
  obtain ⟨x, hxq, hxRGCI⟩ :=
    relativeGciNeighborhoodOfSyntomicAtPrime (R := R) (A := S) hf q
  have hxq' : algebraMap S S' x ∉ q'.asIdeal := by
    -- Proof comment: the first chart denominator stays outside `q'` because `q` is the
    -- contraction of `q'` along `S → S'`.
    intro hxmem
    exact hxq ((map_mem_asIdeal_iff_of_comap_eq (algebraMap S S') rfl x).mp hxmem)
  obtain ⟨qAway, hqAway⟩ :=
    exists_primeSpectrum_away_comap_eq_of_notMem q' hxq'
  have hgBase :
      (algebraMap (Localization.Away x) (Localization.Away x ⊗[S] S')).Syntomic := by
    -- Proof comment: syntomicity survives the base change to the first principal-open chart.
    simpa using
      (RingHom.Syntomic.baseChange (R := S) (S := S') (R' := Localization.Away x) hg)
  let e : Localization.Away x ⊗[S] S' ≃ₐ[Localization.Away x]
      Localization.Away (algebraMap S S' x) :=
    tensorRightAwayAlgEquiv (R := R) (S := S) (S' := S') x
  let qTensor : PrimeSpectrum (Localization.Away x ⊗[S] S') :=
    PrimeSpectrum.comap e.toRingHom qAway
  have hTensor :
      ∃ u : Localization.Away x ⊗[S] S',
        u ∉ qTensor.asIdeal ∧
          Algebra.IsRelativeGlobalCompleteIntersection
            (Localization.Away x) (Localization.Away u) :=
    relativeGciNeighborhoodOfSyntomicAtPrime
      (R := Localization.Away x)
      (A := Localization.Away x ⊗[S] S')
      hgBase
      qTensor
  have hAway :
      ∃ u : Localization.Away (algebraMap S S' x),
        u ∉ qAway.asIdeal ∧
          Algebra.IsRelativeGlobalCompleteIntersection
            (Localization.Away x) (Localization.Away u) := by
    -- Route correction: transport the second chart through the canonical tensor-away
    -- equivalence instead of trying to compare the two away-localization models by defeq.
    exact
      existsLocalizedRgciNeighborhood_of_algEquivSourceNeighborhood
        (R := Localization.Away x)
        (A := Localization.Away x ⊗[S] S')
        (B := Localization.Away (algebraMap S S' x))
        e
        qTensor
        qAway
        rfl
        hTensor
  rcases hAway with ⟨u, huqAway, huRGCI⟩
  let _ : IsScalarTower R (Localization.Away x) (Localization.Away u) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hIterated :
      Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away u) :=
    -- Proof comment: compose the first RGCI chart with the transported second RGCI chart.
    Algebra.IsRelativeGlobalCompleteIntersection.comp hxRGCI huRGCI
  let z : S' := algebraMap S S' x * (IsLocalization.Away.sec (algebraMap S S' x) u).1
  have hzq' : z ∉ q'.asIdeal :=
    -- Proof comment: clear the iterated denominator back to a single element of `S'`.
    notMem_original_away_of_iterated_away q' hxq' qAway hqAway huqAway
  obtain ⟨eSingle⟩ :=
    singleOriginalAwayAlgEquiv (R := R) (S' := S') (algebraMap S S' x) u
  refine ⟨z, hzq', ?_⟩
  -- Proof comment: the iterated localization is algebra-equivalent to the single cleared chart,
  -- so the RGCI property transports to the required principal open of `S'`.
  simpa [z] using
    Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv hIterated eSingle

/-- Helper for Chap10 Lemma 10 136 17: a family of principal opens covering every prime has unit
ideal span. -/
private theorem span_eq_top_of_basicOpen_cover
    {A : Type*} [CommRing A] (s : Set A)
    (hs : ∀ q : PrimeSpectrum A, ∃ g ∈ s, g ∉ q.asIdeal) :
    Ideal.span s = ⊤ := by
  -- Proof comment: translate the pointwise basic-open cover into the standard affine-spectrum
  -- span criterion.
  have hscover :
      (⨆ g ∈ s, PrimeSpectrum.basicOpen g) = ⊤ := by
    apply SetLike.ext'
    change (↑(⨆ g ∈ s, PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum A)) = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro q
    rcases hs q with ⟨g, hgs, hgq⟩
    have hgmem : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hgq
    exact
      (show (PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum A)) ≤
          ⨆ h ∈ s, PrimeSpectrum.basicOpen h from
        le_iSup_of_le g <| le_iSup_of_le hgs le_rfl) hgmem
  exact PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hscover

/-- Helper for Chap10 Lemma 10 136 17: the primewise syntomic-composition chart theorem already
produces a pointwise cover by relative global complete-intersection principal opens. -/
private theorem pointwiseRelativeGciCoverOfSyntomicComp
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    {f : R →+* S} {g : S →+* S'} (hf : f.Syntomic) (hg : g.Syntomic)
    (q' : PrimeSpectrum S') :
    ∃ z ∈ {z : S' | Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away z)},
      z ∉ q'.asIdeal := by
  -- Proof comment: unpack the previously constructed chart around `q'` and record only the cover
  -- data needed for the span argument.
  rcases pointwiseRelativeGciChartOfSyntomicComp hf hg q' with ⟨z, hzq', hzRGCI⟩
  exact ⟨z, hzRGCI, hzq'⟩

/-- Helper for Chap10 Lemma 10 136 17: a composite of syntomic maps has a finite principal-open
cover by relative global complete intersections over the source. -/
private theorem relativeGciFinsetCoverOfSyntomicComp
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    {f : R →+* S} {g : S →+* S'} (hf : f.Syntomic) (hg : g.Syntomic) :
    ∃ s : Finset S', Ideal.span (s : Set S') = ⊤ ∧
      ∀ z ∈ s, Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away z) := by
  classical
  let t : Set S' := {z : S' | Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away z)}
  have hspan : Ideal.span t = ⊤ := by
    -- Proof comment: every target prime lies in one RGCI principal chart produced by the
    -- pointwise theorem, so those charts span the unit ideal.
    refine span_eq_top_of_basicOpen_cover t ?_
    intro q'
    rcases pointwiseRelativeGciCoverOfSyntomicComp hf hg q' with ⟨z, hz, hzq'⟩
    exact ⟨z, hz, hzq'⟩
  obtain ⟨s, hs_subset, hs_top⟩ := (Ideal.span_eq_top_iff_finite t).mp hspan
  refine ⟨s, hs_top, ?_⟩
  intro z hz
  exact hs_subset hz

namespace Syntomic

-- Proof sketch: the composition of syntomic morphisms is flat by `RingHom.Flat.comp` and finitely
-- presented by `RingHom.FinitePresentation.comp`. For the fiber condition, apply the relative
-- global complete intersection neighborhood criterion from Lemma `10.136.15` and then the
-- composition statement for relative global complete intersections from part `(2)`.
/-- Chap10 Lemma 10 136 17 (1): the composition of syntomic ring maps is syntomic. -/
@[stacks 00SZ]
theorem comp {f : R →+* S} {g : S →+* S'} (hf : f.Syntomic) (hg : g.Syntomic) :
    (g.comp f).Syntomic :=
by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra S S' := g.toAlgebra
  let _ : Algebra R S' := (g.comp f).toAlgebra
  let _ : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  rcases relativeGciFinsetCoverOfSyntomicComp (R := R) (S := S) (S' := S') hf hg with
    ⟨s, hs, hloc⟩
  -- Proof comment: syntomicity is local on the target, so it is enough to use the finite RGCI
  -- cover produced above and convert each localized chart to a syntomic map.
  exact
    RingHom.Syntomic.ofLocalizationSpanTarget
      (f := g.comp f)
      (s := (s : Set S'))
      hs
      (fun r ↦ by
        have hrRGCI :
            Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away (r : S')) :=
          hloc (r : S') r.2
        have hrSyntomic :
            (algebraMap R (Localization.Away (r : S'))).Syntomic :=
          Algebra.IsRelativeGlobalCompleteIntersection.syntomic hrRGCI
        have hcomp :
            (algebraMap S' (Localization.Away (r : S'))).comp (g.comp f) =
              algebraMap R (Localization.Away (r : S')) := by
          ext x
          rw [RingHom.comp_apply, RingHom.comp_apply]
          exact IsScalarTower.algebraMap_apply R S' (Localization.Away (r : S')) x
        simpa [hcomp] using hrSyntomic)

/-- Companion meta-property witness for Lemma 10.136.17 (1). -/
theorem stableUnderComposition : RingHom.StableUnderComposition RingHom.Syntomic :=
  -- Proof comment: package the owner-level composition theorem as the generic stability witness.
  fun _ _ _ _ _ _ _ _ hf hg ↦ Syntomic.comp hf hg

end Syntomic

end RingHom

end
