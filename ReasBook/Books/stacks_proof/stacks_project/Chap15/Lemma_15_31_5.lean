import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_32_1
import stacks_proof.stacks_project.Chap10.Definition_10_69_1
import stacks_proof.stacks_project.Chap10.Lemma_10_69_6
import stacks_proof.stacks_project.Chap10.Definition_10_112_5
import stacks_proof.stacks_project.Chap10.Lemma_10_39_18
import stacks_proof.stacks_project.Chap10.Lemma_10_69_3
import stacks_proof.stacks_project.Chap10.Lemma_10_128_6
import stacks_proof.stacks_project.Chap15.Lemma_15_31_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory
open scoped TensorProduct

namespace RingTheory.Sequence

section

variable {A' : Type u} [CommRing A']
variable {B' : Type u} [CommRing B'] [Algebra A' B']
variable [Module.Flat A' B'] [Algebra.FinitePresentation A' B']

variable {I : Ideal A'} {r : ℕ} (f' : Fin r → B')

local notation "IB" => Ideal.map (algebraMap A' B') I
local notation "FiberRing" => B' ⧸ IB
local notation "fbar" => fun i : Fin r ↦ Ideal.Quotient.mk IB (f' i)
local notation "FiberQuot" => FiberRing ⧸ Ideal.span (Set.range fbar)
local notation "Quot" => B' ⧸ Ideal.span (Set.range f')

/- Domain-style sampling for Lemma 15.31.5:
* primary domain: flatness of quotients by finite quasi-regular sequences across a locally
  nilpotent thickening in commutative algebra;
* sampled owner declarations:
  `Ideal.IsLocallyNilpotent`,
  `RingTheory.Sequence.IsQuasiRegularSequence`,
  `RingTheory.Sequence.isQuasiRegularSequence_baseChange_of_flat_quotient`,
  `flat_over_middleRing_of_locallyNilpotent_of_flat_over_base_and_flat_mod_extended_ideal`;
* best owner abstraction: the theorem itself is `source-facing` and should stay a direct flatness
  statement for the quotient ring `B' ⧸ (f'_1, ..., f'_r)`, but the ambient flatness and finite
  presentation of `A' → B'` belong to the canonical algebra owners `[Module.Flat A' B']` and
  `[Algebra.FinitePresentation A' B']`;
* primitive data vs derived API: the primitive data are the algebra `A' → B'`, the locally
  nilpotent ideal `I`, and the tuple `f'`; the quotient presentations `FiberRing`, `FiberQuot`,
  and `Quot` are only bridge views, and the quasi-regularity hypothesis serves only to supply the
  closed-fiber flatness input.

Source/core/bridge triage:
* `source-facing`: the flatness of `Quot` over `A'`;
* `core/canonical`: `Module.Flat`, `Algebra.FinitePresentation`, `Ideal.IsLocallyNilpotent`, and
  `IsQuasiRegularSequence`;
* `bridge/view`: the quotient models `FiberRing = B' / IB` and
  `FiberQuot = FiberRing / (fbar_1, ..., fbar_r)`.
-/

-- Proof sketch: localize at a prime of `Quot` and use the local criterion for flatness. The
-- ambient owners `[Module.Flat A' B']` and `[Algebra.FinitePresentation A' B']` provide the
-- finitely presented flat map needed to invoke the fiberwise criterion on the localized diagram,
-- reducing to regularity in the fiber. Lemma `15.31.4` gives quasi-regularity after passage to
-- the fiber, and Lemma `15.30.7` upgrades quasi-regularity to regularity in the Noetherian local
-- fiber ring, yielding flatness of `Quot` over `A'`.
/-- Helper for Lemma 15.31.5: a locally nilpotent ideal is contained in every prime ideal. -/
lemma locallyNilpotent_le_prime
    (hI : I.IsLocallyNilpotent) (p : PrimeSpectrum A') :
    I ≤ p.asIdeal := by
  -- Local nilpotence is containment in the nilradical, and every prime contains the nilradical.
  exact hI.trans (nilradical_le_prime p.asIdeal)

/-- Helper for Lemma 15.31.5: if a prime `p` contains `I`, then its residue field carries the
quotient algebra structure over `A' ⧸ I`. -/
noncomputable abbrev residueField_quotient_algebra
    (p : PrimeSpectrum A') (hpI : I ≤ p.asIdeal) :
    Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
  RingHom.toAlgebra <|
    Ideal.Quotient.lift I (algebraMap A' p.asIdeal.ResidueField) fun a ha ↦ by
      -- Elements of `I` vanish in the residue field because `I ⊆ p`.
      simpa [Ideal.algebraMap_quotient_residueField_mk] using (hpI ha : a ∈ p.asIdeal)

/-- Helper for Lemma 15.31.5: after base change from `A' ⧸ I` to the residue field `κ(p)`, the
quotient `B' / I B'` recovers the closed fiber `κ(p) ⊗[A'] B'`. -/
noncomputable abbrev closedFiber_mod_ideal_algEquiv
    (p : PrimeSpectrum A') (hpI : I ≤ p.asIdeal) :
    let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
      residueField_quotient_algebra (I := I) p hpI
    (p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberRing) ≃ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber B' := by
  let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
    residueField_quotient_algebra (I := I) p hpI
  letI : IsScalarTower A' (A' ⧸ I) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  -- Route correction: compare the mod-`I` quotient with the tensor model first, then cancel the
  -- redundant middle base change to recover the textbook closed fiber.
  exact
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' I)).trans <|
      Algebra.TensorProduct.cancelBaseChange A' (A' ⧸ I) p.asIdeal.ResidueField
        p.asIdeal.ResidueField B'

/-- Helper for Lemma 15.31.5: after precomposing with `B' → B' / I B'`, the closed-fiber
comparison carries the quotient-side `includeRight` map to the usual `B' → κ(p) ⊗[A'] B'`
generator map. -/
lemma closedFiber_mod_ideal_algEquiv_comp_includeRight
    (p : PrimeSpectrum A') (hpI : I ≤ p.asIdeal) :
    let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
      residueField_quotient_algebra (I := I) p hpI
    (((closedFiber_mod_ideal_algEquiv (I := I) p hpI).toRingHom).comp
        ((Algebra.TensorProduct.includeRight :
            FiberRing →ₐ[A' ⧸ I] p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberRing).toRingHom)).comp
        (Ideal.Quotient.mk IB) =
      (Algebra.TensorProduct.includeRight : B' →ₐ[A'] p.asIdeal.Fiber B').toRingHom := by
  let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
    residueField_quotient_algebra (I := I) p hpI
  letI : IsScalarTower A' (A' ⧸ I) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  ext x
  -- Proof comment: on the class of `x`, `quotIdealMapEquivQuotTensor` produces the canonical
  -- pure tensor over `A' ⧸ I`, and `cancelBaseChange` then collapses the redundant middle factor.
  simp [closedFiber_mod_ideal_algEquiv, Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.31.5: the global closed fiber of a finitely presented algebra is
Noetherian because it is essentially of finite type over a field. -/
lemma fiber_isNoetherianRing (p : PrimeSpectrum A') :
    IsNoetherianRing (p.asIdeal.Fiber B') := by
  let _ : Algebra.EssFiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber B') := inferInstance
  -- Proof comment: the fiber is a residue-field algebra of essential finite type, hence
  -- Noetherian by the standard Hilbert-basis owner theorem.
  exact Algebra.EssFiniteType.isNoetherianRing p.asIdeal.ResidueField (p.asIdeal.Fiber B')

/-- Helper for Lemma 15.31.5: the local fiber ring at `q'` is Noetherian as a localization of the
Noetherian global fiber over `q' ∩ A'`. -/
lemma fiberLocalRingAt_isNoetherianRing (q' : PrimeSpectrum B') :
    IsNoetherianRing (fiberLocalRingAt A' B' q') := by
  let p : PrimeSpectrum A' := PrimeSpectrum.comap (algebraMap A' B') q'
  have hp_noetherian : IsNoetherianRing (p.asIdeal.Fiber B') :=
    fiber_isNoetherianRing (A' := A') (B' := B') p
  let _ : IsNoetherianRing ((q'.asIdeal.under A').Fiber B') := by
    -- Proof comment: `p` is definitionally `q' ∩ A'`, so the global fiber owner does not change.
    simpa [p, RingHom.algebraMap_toAlgebra] using hp_noetherian
  -- Proof comment: `fiberLocalRingAt` is the prime localization of that global fiber ring.
  simpa [fiberLocalRingAt] using
    (IsLocalization.isNoetherianRing (fiberPrimeAt A' B' q').asIdeal.primeCompl
      (fiberLocalRingAt A' B' q') inferInstance)

/-- Helper for Lemma 15.31.5: quasi-regular sequences are preserved after transporting the ring
through a ring equivalence. -/
private theorem isQuasiRegularSequence_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) {rs : List R}
    (hqr : IsQuasiRegularSequence rs) :
    IsQuasiRegularSequence (rs.map e.toRingHom) := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  have hflat : (algebraMap R S).Flat := by
    -- A ring equivalence is flat because its underlying map is bijective.
    simpa using (RingHom.Flat.of_bijective e.bijective : e.toRingHom.Flat)
  let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  -- Proof comment: transport quasi-regularity across the ring equivalence by viewing it as a
  -- flat owner-level base change.
  simpa [IsQuasiRegularSequence] using
    (IsQuasiRegular.of_flat_of_isBaseChange
      (R := R) (S := S) (M := R) (N := S)
      (f := Algebra.linearMap R S)
      (hf := IsBaseChange.linearMap (R := R) (S := S))
      (rs := rs) hqr)

/-- Helper for Lemma 15.31.5: the closed-fiber equivalence sends the quotient-side generator
coming from `f'_i` to the ambient closed-fiber generator. -/
lemma closedFiber_mod_ideal_algEquiv_includeRight_fbar
    (p : PrimeSpectrum A') (hpI : I ≤ p.asIdeal) (i : Fin r) :
    let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
      residueField_quotient_algebra (I := I) p hpI
    (closedFiber_mod_ideal_algEquiv (I := I) p hpI)
        (Algebra.TensorProduct.includeRight (Ideal.Quotient.mk IB (f' i))) =
      (Algebra.TensorProduct.includeRight (f' i) : p.asIdeal.Fiber B') := by
  let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
    residueField_quotient_algebra (I := I) p hpI
  have hcomp :
      ((((closedFiber_mod_ideal_algEquiv (I := I) p hpI).toRingHom).comp
          ((Algebra.TensorProduct.includeRight :
              FiberRing →ₐ[A' ⧸ I] p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberRing).toRingHom)).comp
          (Ideal.Quotient.mk IB)) (f' i) =
        (Algebra.TensorProduct.includeRight : B' →ₐ[A'] p.asIdeal.Fiber B') (f' i) := by
    simpa using congrArg (fun φ : B' →+* p.asIdeal.Fiber B' ↦ φ (f' i))
      (closedFiber_mod_ideal_algEquiv_comp_includeRight (I := I) p hpI)
  -- Proof comment: evaluate the already-proved ring-hom equality on the single generator `f'_i`.
  exact hcomp

/-- Helper for Lemma 15.31.5: the quasi-regular sequence on `B' / I B'` stays quasi-regular on
the global closed fiber over `p`. -/
lemma closedFiber_quasiRegularSequence_of_mod_ideal_quasiRegular
    (p : PrimeSpectrum A') (hpI : I ≤ p.asIdeal)
    (hqr : IsQuasiRegularSequence (List.ofFn fbar))
    (hquot : Module.Flat (A' ⧸ I) FiberQuot) :
    IsQuasiRegularSequence
      (List.ofFn fun i : Fin r ↦
        (Algebra.TensorProduct.includeRight (f' i) : p.asIdeal.Fiber B')) := by
  -- Proof comment: first invoke the previously packaged arbitrary-base-change theorem on
  -- `FiberRing = B' / I B'`, using the flat quotient hypothesis on `FiberQuot`.
  let _ : Module.Flat (A' ⧸ I) FiberQuot := hquot
  let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
    residueField_quotient_algebra (I := I) p hpI
  have hbase :
      IsQuasiRegularSequence
        (List.ofFn fun i : Fin r ↦
          (Algebra.TensorProduct.includeRight (Ideal.Quotient.mk IB (f' i)) :
            p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberRing)) := by
    -- Route correction: reuse the earlier Chapter 15 owner theorem for arbitrary base change with
    -- flat quotient instead of rebuilding the graded-module argument in this file.
    simpa using
      (isQuasiRegularSequence_baseChange_of_flat_quotient
        (A := A' ⧸ I) (A' := p.asIdeal.ResidueField)
        (B := FiberRing)
        (f := fbar) hqr)
  let e :
      (p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberRing) ≃+* p.asIdeal.Fiber B' :=
    (closedFiber_mod_ideal_algEquiv (I := I) p hpI).toRingEquiv
  have htransport :
      IsQuasiRegularSequence
        ((List.ofFn fun i : Fin r ↦
          (Algebra.TensorProduct.includeRight (Ideal.Quotient.mk IB (f' i)) :
            p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberRing)).map e.toRingHom) :=
    isQuasiRegularSequence_of_ringEquiv e hbase
  have hfun :
      (fun i : Fin r ↦
        e (Algebra.TensorProduct.includeRight (Ideal.Quotient.mk IB (f' i)))) =
      fun i : Fin r ↦ (Algebra.TensorProduct.includeRight (f' i) : p.asIdeal.Fiber B') := by
    funext i
    exact closedFiber_mod_ideal_algEquiv_includeRight_fbar
      (A' := A') (B' := B') (I := I) (f' := f') p hpI i
  have hlist :
      List.ofFn (⇑e ∘ fun i : Fin r ↦
        (Algebra.TensorProduct.includeRight (Ideal.Quotient.mk IB (f' i)) :
          p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberRing)) =
      List.ofFn fun i : Fin r ↦
        (Algebra.TensorProduct.includeRight (f' i) : p.asIdeal.Fiber B') := by
    simpa [Function.comp] using congrArg List.ofFn hfun
  -- Proof comment: identify the transported generators with the usual ambient closed-fiber
  -- generators one index at a time.
  exact hlist ▸ (by simpa [List.map_ofFn, Function.comp] using htransport)

/-- Helper for Lemma 15.31.5: the fiber prime contracts back to the original prime `q'` under the
right tensor-factor inclusion into the global fiber. -/
lemma fiberPrimeAt_asIdeal_comap
    (q' : PrimeSpectrum B') :
    Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
      ((fiberPrimeAt A' B' q').asIdeal) = q'.asIdeal := by
  let p : PrimeSpectrum A' := PrimeSpectrum.comap (algebraMap A' B') q'
  -- Proof comment: `fiberPrimeAt` is defined by `PrimeSpectrum.preimageEquivFiber`, so its
  -- contraction is exactly the ambient prime it came from.
  change
    ((PrimeSpectrum.preimageEquivFiber A' B' p).symm
      (PrimeSpectrum.preimageEquivFiber A' B' p ⟨q', rfl⟩)).1.asIdeal =
      q'.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap A' B') ⁻¹' {p} ↦ x.1.asIdeal)
    ((PrimeSpectrum.preimageEquivFiber A' B' p).symm_apply_apply ⟨q', rfl⟩)

/-- Helper for Lemma 15.31.5: a quasi-regular sequence on the global closed fiber remains
quasi-regular after localizing at the fiber prime over `q'`. -/
lemma fiberLocalRingAt_quasiRegularSequence_of_closedFiber_quasiRegular
    (q' : PrimeSpectrum B')
    (hqrFiber :
      IsQuasiRegularSequence
        (List.ofFn fun i : Fin r ↦
          (Algebra.TensorProduct.includeRight (f' i) :
            (q'.asIdeal.under A').Fiber B'))) :
    IsQuasiRegularSequence
      (List.ofFn fun i : Fin r ↦
        (toFiberLocalRingAt A' B' q' (f' i) : fiberLocalRingAt A' B' q')) := by
  let R0 := (q'.asIdeal.under A').Fiber B'
  let S0 := fiberLocalRingAt A' B' q'
  let _ : Module.Flat R0 S0 := by
    -- `fiberLocalRingAt` is literally the prime localization of the global fiber ring.
    simpa [R0, S0, fiberLocalRingAt] using
      (IsLocalization.flat (Localization.AtPrime (fiberPrimeAt A' B' q').asIdeal)
        (fiberPrimeAt A' B' q').asIdeal.primeCompl :
        Module.Flat R0 (Localization.AtPrime (fiberPrimeAt A' B' q').asIdeal))
  -- Proof comment: the local fiber ring is the prime localization of the global fiber ring, so
  -- quasi-regularity survives by flat base change along the localization map.
  simpa [R0, S0, IsQuasiRegularSequence, toFiberLocalRingAt] using
    (IsQuasiRegular.of_flat_of_isBaseChange
      (R := R0) (S := S0) (M := R0) (N := S0)
      (f := Algebra.linearMap R0 S0)
      (hf := IsBaseChange.linearMap (R := R0) (S := S0))
      (rs := List.ofFn fun i : Fin r ↦
        (Algebra.TensorProduct.includeRight (f' i) : R0))
      hqrFiber)

/-- Helper for Lemma 15.31.5: each localized generator lies in the maximal ideal of the local
fiber ring once the original span lies in `q'`. -/
lemma toFiberLocalRingAt_mem_maximalIdeal_of_mem_span
    (q' : PrimeSpectrum B') (hspan_q' : Ideal.span (Set.range f') ≤ q'.asIdeal) (i : Fin r) :
    toFiberLocalRingAt A' B' q' (f' i) ∈
      IsLocalRing.maximalIdeal (fiberLocalRingAt A' B' q') := by
  have hfiber :
      (Algebra.TensorProduct.includeRight (f' i) :
        (q'.asIdeal.under A').Fiber B') ∈ (fiberPrimeAt A' B' q').asIdeal := by
    have hfi : f' i ∈ q'.asIdeal := hspan_q' (Ideal.subset_span ⟨i, rfl⟩)
    change f' i ∈
      Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
        (fiberPrimeAt A' B' q').asIdeal
    rw [fiberPrimeAt_asIdeal_comap (A' := A') (B' := B') q']
    exact hfi
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (fiberPrimeAt A' B' q').asIdeal
      (fiberLocalRingAt A' B' q')]
  -- Proof comment: pass membership from the fiber prime to its image in the localization.
  simpa [toFiberLocalRingAt] using
    (Ideal.mem_map_of_mem
      (algebraMap ((q'.asIdeal.under A').Fiber B') (fiberLocalRingAt A' B' q')) hfiber)

/-- Helper for Lemma 15.31.5: over the Noetherian local fiber ring at `q'`, quasi-regularity plus
membership in the maximal ideal upgrades to regularity. -/
lemma fiberLocalRingAt_regularSequence_of_quasiRegular_mem_maximal
    (q' : PrimeSpectrum B')
    (hqrLoc :
      IsQuasiRegularSequence
        (List.ofFn fun i : Fin r ↦
          (toFiberLocalRingAt A' B' q' (f' i) : fiberLocalRingAt A' B' q')))
    (hspan_q' : Ideal.span (Set.range f') ≤ q'.asIdeal) :
    Sequence.IsRegular (fiberLocalRingAt A' B' q')
      (List.ofFn fun i : Fin r ↦ toFiberLocalRingAt A' B' q' (f' i)) := by
  let _ : IsNoetherianRing (fiberLocalRingAt A' B' q') :=
    fiberLocalRingAt_isNoetherianRing (A' := A') (B' := B') q'
  let _ : Nontrivial (fiberLocalRingAt A' B' q') := by infer_instance
  have hmem :
      ∀ x ∈ List.ofFn (fun i : Fin r ↦ toFiberLocalRingAt A' B' q' (f' i)),
        x ∈ IsLocalRing.maximalIdeal (fiberLocalRingAt A' B' q') := by
    intro x hx
    have hx' : ∃ i : Fin r, toFiberLocalRingAt A' B' q' (f' i) = x := by
      simpa [List.mem_ofFn', Set.range] using hx
    rcases hx' with ⟨i, rfl⟩
    exact toFiberLocalRingAt_mem_maximalIdeal_of_mem_span
      (A' := A') (B' := B') (f' := f') q' hspan_q' i
  -- Proof comment: Lemma 10.69.6 is exactly the local Noetherian upgrade needed here.
  exact hqrLoc.isRegular_of_mem_maximalIdeal hmem

/-- Helper for Lemma 15.31.5: regularity in the canonical local fiber ring is exactly the
closed-fiber regularity predicate attached to `q'`. -/
lemma closedFiber_localized_map_isRegular_iff
    (q' : PrimeSpectrum B') :
    PrimeSpectrum.IsRegularInFiberLocalRing q' A' (List.ofFn f') ↔
      Sequence.IsRegular (fiberLocalRingAt A' B' q')
        (List.ofFn fun i : Fin r ↦ toFiberLocalRingAt A' B' q' (f' i)) := by
  -- Proof comment: this is just the owner definition from `Definition 10.112.5`.
  rw [PrimeSpectrum.IsRegularInFiberLocalRing]
  have hlist :
      List.map (⇑(toFiberLocalRingAt A' B' q')) (List.ofFn f') =
        List.ofFn fun i : Fin r ↦ toFiberLocalRingAt A' B' q' (f' i) := by
    ext i <;> simp
  rw [hlist]

/-- Helper for Lemma 15.31.5: any element of the span of the generators vanishes in the quotient
`B' / (f'_1, \ldots, f'_r)`. -/
lemma quotient_mk_eq_zero_of_mem_span_range
    {x : B'} (hx : x ∈ Ideal.span (Set.range f')) :
    Ideal.Quotient.mk (Ideal.span (Set.range f')) x = 0 := by
  -- Proof comment: this is exactly the quotient-model characterization of membership in the span.
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

/-- Helper for Lemma 15.31.5: after passing from `B'` to the quotient `Quot`, the image of the
prime complement of the pullback prime `q'` is exactly the prime complement of `q`. -/
lemma quotient_primeCompl_eq_algebraMapSubmonoid
    (q : PrimeSpectrum Quot) :
    let q' : PrimeSpectrum B' :=
      PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f'))) q
    Algebra.algebraMapSubmonoid Quot q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
  let q' : PrimeSpectrum B' :=
    PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f'))) q
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- Proof comment: by definition of the pullback prime `q'`, an element outside `q'` stays
    -- outside `q` after quotienting.
    change Ideal.Quotient.mk (Ideal.span (Set.range f')) y ∉ q.asIdeal
    simpa [q', PrimeSpectrum.comap_asIdeal] using hy
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨y, ?_, rfl⟩
    -- Proof comment: any representative of a quotient class outside `q` must already lie outside
    -- the pullback prime `q'`.
    change Ideal.Quotient.mk (Ideal.span (Set.range f')) y ∉ q.asIdeal
    simpa [q', PrimeSpectrum.comap_asIdeal] using hx

/-- Helper for Lemma 15.31.5: quotienting the localization `B'_{q'}` by the extended ideal
generated by `f'_1, \ldots, f'_r` recovers the localization of the global quotient ring at `q`. -/
noncomputable def quotient_localizationAtPrime_algEquiv
    (q : PrimeSpectrum Quot) :
    let q' : PrimeSpectrum B' :=
      PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f'))) q
    ((Localization.AtPrime q'.asIdeal) ⧸
        Ideal.map (algebraMap B' (Localization.AtPrime q'.asIdeal))
          (Ideal.span (Set.range f'))) ≃ₐ[Quot]
      Localization.AtPrime q.asIdeal := by
  let q' : PrimeSpectrum B' :=
    PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f'))) q
  let hloc :
      IsLocalization (Algebra.algebraMapSubmonoid Quot q'.asIdeal.primeCompl)
        ((Localization.AtPrime q'.asIdeal) ⧸
          Ideal.map (algebraMap B' (Localization.AtPrime q'.asIdeal))
            (Ideal.span (Set.range f'))) := by
    infer_instance
  have hU :
      Algebra.algebraMapSubmonoid Quot q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
    simpa [q'] using quotient_primeCompl_eq_algebraMapSubmonoid (f' := f') q
  let _ :
      IsLocalization q.asIdeal.primeCompl
        ((Localization.AtPrime q'.asIdeal) ⧸
          Ideal.map (algebraMap B' (Localization.AtPrime q'.asIdeal))
            (Ideal.span (Set.range f'))) := by
    -- Proof comment: the previous submonoid identification rewrites the owner localization
    -- structure on the localized quotient to the canonical localization at `q`.
    exact hU ▸ hloc
  -- Proof comment: both rings are now recognized as localizations of `Quot` at `q`, so the
  -- canonical uniqueness equivalence supplies the comparison.
  exact IsLocalization.algEquiv q.asIdeal.primeCompl _ _

/-- Lemma 15.31.5: let `A' → B'` be a flat finitely presented ring map, let `I ⊆ A'` be a locally
nilpotent ideal, and let `f'_1, \ldots, f'_r ∈ B'`. If the images of `f'_1, \ldots, f'_r` in
`B' / I B'` form a quasi-regular sequence and the quotient `(B' / I B') / (f'_1, \ldots, f'_r)`
is flat over `A' / I`, then `B' / (f'_1, \ldots, f'_r)` is flat over `A'`. -/
@[stacks 0CEQ]
theorem flat_quotient_of_quasiRegularSequence_mod_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hqr : IsQuasiRegularSequence (List.ofFn fbar))
    (hquot : Module.Flat (A' ⧸ I) FiberQuot) :
    Module.Flat A' Quot := by
  by_cases hr : r = 0
  · subst hr
    -- Proof comment: with no generators, the quotient ring is just `B'`, so the target flatness
    -- is exactly the ambient flatness assumption, transported across the quotient-by-`⊥`
    -- algebra equivalence.
    have hspan : Ideal.span (Set.range f') = (⊥ : Ideal B') := by
      simp
    let eBot : (B' ⧸ (⊥ : Ideal B')) ≃ₗ[A'] B' :=
      { toFun := RingEquiv.quotientBot B'
        invFun := (RingEquiv.quotientBot B').symm
        left_inv := (RingEquiv.quotientBot B').left_inv
        right_inv := (RingEquiv.quotientBot B').right_inv
        map_add' := (RingEquiv.quotientBot B').map_add
        map_smul' := by
          intro a x
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          rfl }
    rw [hspan]
    exact Module.Flat.of_linearEquiv eBot
  -- Proof comment: use the prime-local flatness criterion and fix a prime of the quotient.
  rw [flat_iff_flat_localizedModule_atPrime_over_under (R := A') (A := Quot) (M := Quot)]
  intro q
  let q' : PrimeSpectrum B' :=
    PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f'))) q
  let p : PrimeSpectrum A' := PrimeSpectrum.comap (algebraMap A' B') q'
  have hpI : I ≤ p.asIdeal := locallyNilpotent_le_prime (I := I) hI p
  let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField :=
    residueField_quotient_algebra (I := I) p hpI
  have hspan_q' : Ideal.span (Set.range f') ≤ q'.asIdeal := by
    -- Every generator of `Ideal.span (Set.range f')` maps to zero in the quotient, hence lies in
    -- the preimage prime `q'`.
    intro x hx
    have hx0 : Ideal.Quotient.mk (Ideal.span (Set.range f')) x = 0 :=
      quotient_mk_eq_zero_of_mem_span_range (f' := f') hx
    change Ideal.Quotient.mk (Ideal.span (Set.range f')) x ∈ q.asIdeal
    simp [hx0]
  have hclosedFiber :
      (p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberRing) ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber B' :=
    closedFiber_mod_ideal_algEquiv (I := I) p hpI
  have hfiberLocal_noetherian : IsNoetherianRing (fiberLocalRingAt A' B' q') :=
    fiberLocalRingAt_isNoetherianRing (A' := A') (B' := B') q'
  have hclosedFiber_qr :
      IsQuasiRegularSequence
        (List.ofFn fun i : Fin r ↦
          (Algebra.TensorProduct.includeRight (f' i) : p.asIdeal.Fiber B')) :=
    closedFiber_quasiRegularSequence_of_mod_ideal_quasiRegular
      (A' := A') (B' := B') (I := I) (f' := f') p hpI hqr hquot
  have hfiberLocal_qr :
      IsQuasiRegularSequence
        (List.ofFn fun i : Fin r ↦
          (toFiberLocalRingAt A' B' q' (f' i) : fiberLocalRingAt A' B' q')) := by
    -- Proof comment: localize the global closed-fiber quasi-regular sequence at the prime over
    -- `q'`.
    simpa [p, RingHom.algebraMap_toAlgebra] using
      (fiberLocalRingAt_quasiRegularSequence_of_closedFiber_quasiRegular
        (A' := A') (B' := B') (f' := f') q' hclosedFiber_qr)
  have hfiberLocal_reg :
      Sequence.IsRegular (fiberLocalRingAt A' B' q')
        (List.ofFn fun i : Fin r ↦ toFiberLocalRingAt A' B' q' (f' i)) :=
    fiberLocalRingAt_regularSequence_of_quasiRegular_mem_maximal
      (A' := A') (B' := B') (f' := f') q' hfiberLocal_qr hspan_q'
  have hclosedFiber_local :
      PrimeSpectrum.IsRegularInFiberLocalRing q' A' (List.ofFn f') :=
    (closedFiber_localized_map_isRegular_iff (A' := A') (B' := B') (f' := f') q').2
      hfiberLocal_reg
  have hquotLocEquiv :
      ((Localization.AtPrime q'.asIdeal) ⧸
          Ideal.map (algebraMap B' (Localization.AtPrime q'.asIdeal))
            (Ideal.span (Set.range f'))) ≃ₐ[Quot]
        Localization.AtPrime q.asIdeal :=
    quotient_localizationAtPrime_algEquiv (A' := A') (B' := B') (f' := f') q
  -- Proof comment: the source-faithful core is now established: the sequence is quasi-regular on
  -- the global closed fiber, remains quasi-regular on the local fiber ring at `q'`, and hence is
  -- regular there, and the localized quotient output is already identified with the actual stalk
  -- `Localization.AtPrime q.asIdeal`. The remaining step is only the localized closed-fiber
  -- interface needed to feed `hclosedFiber_local` into Lemma `10.128.6`.
  -- TODO for Lemma 15.31.5: apply
  -- `isRegular_and_flat_quotient_take_of_closedFiber_isRegular_of_essFinitePresentation` to the
  -- localized map `A'_p → B'_{q'}` using `hclosedFiber_local`. The remaining unresolved blocker is
  -- the owner-level identification between the actual closed fiber of that local map and the
  -- already-controlled local fiber ring `fiberLocalRingAt A' B' q'`.
  sorry

end

end RingTheory.Sequence
