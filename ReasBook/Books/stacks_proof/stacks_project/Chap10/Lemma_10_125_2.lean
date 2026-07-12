import StacksProject_2024.Chap05.Definition_5_10_1
import StacksProject_2024.Chap10.Definition_10_125_1
import StacksProject_2024.Chap10.Lemma_10_17_6
import StacksProject_2024.Chap10.Remark_10_18_5
import StacksProject_2024.Chap10.Lemma_10_46_8
import StacksProject_2024.Chap10.Lemma_10_115_4
import StacksProject_2024.Chap10.Lemma_10_123_13

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra.TensorProduct
open Algebra.FiniteType
open AlgebraicGeometry
open RingHom
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- Helper for Chap10 Lemma 10 125 2: a prime ideal that avoids the element being inverted maps
to a prime ideal in the corresponding away localization. -/
private lemma localizedPrimeMap_isPrime
    {A : Type u} [CommRing A] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    (Ideal.map (algebraMap A (Localization.Away x)) I).IsPrime := by
  -- Convert avoidance of `x` into disjointness from all powers, then use the localization API.
  have hdisj : Disjoint (Submonoid.powers x : Set A) (I : Set A) := by
    exact (Ideal.disjoint_powers_iff_notMem x (Ideal.IsPrime.isRadical inferInstance)).2 hx
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers x) (Localization.Away x) I inferInstance hdisj

/-- Helper for Chap10 Lemma 10 125 2: the localized extension of a prime avoiding the inverted
element contracts back to the original prime. -/
private lemma localizedPrime_comap_map_eq
    {A : Type u} [CommRing A] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    Ideal.comap (algebraMap A (Localization.Away x))
      (Ideal.map (algebraMap A (Localization.Away x)) I) = I := by
  -- The same disjointness condition identifies the extension-contraction of the prime.
  have hdisj : Disjoint (Submonoid.powers x : Set A) (I : Set A) := by
    exact (Ideal.disjoint_powers_iff_notMem x (Ideal.IsPrime.isRadical inferInstance)).2 hx
  exact IsLocalization.comap_map_of_isPrime_disjoint
    (Submonoid.powers x) (Localization.Away x) inferInstance hdisj

/-- Helper for Chap10 Lemma 10 125 2: quasi-finiteness at a prime is transported through a target
localization whose prime contracts to the given one. -/
private lemma quasiFiniteAt_of_localization_comap
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] (M : Submonoid C)
    (q : Ideal C) [q.IsPrime] (Q : Ideal (Localization M)) [Q.IsPrime]
    (hcomap : Ideal.comap (algebraMap C (Localization M)) Q = q)
    (hq : Algebra.QuasiFiniteAt A q) :
    Algebra.QuasiFiniteAt A Q := by
  -- Compare the two local rings by the canonical iterated-localization equivalence.
  have hiff :
      Algebra.QuasiFinite A
          (Localization.AtPrime (Ideal.comap (algebraMap C (Localization M)) Q)) ↔
        Algebra.QuasiFinite A (Localization.AtPrime Q) := by
    let e :=
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M Q).restrictScalars A
    exact Algebra.QuasiFinite.iff_of_algEquiv e
  subst q
  exact hiff.mp hq

/-- Helper for Chap10 Lemma 10 125 2: in a finite-type fiber, the quasi-finite-at locus is finite.
-/
private lemma finiteQuasiFiniteAtFiberPrimes
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (p : PrimeSpectrum A) :
    Set.Finite { Q : PrimeSpectrum (p.asIdeal.Fiber C) |
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal } := by
  let T : Set (PrimeSpectrum (p.asIdeal.Fiber C)) :=
    { Q | Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal }
  -- Noetherianity makes the quasi-finite-at subspace compact.
  have hnoeth : IsNoetherianRing (p.asIdeal.Fiber C) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  letI : IsNoetherianRing (p.asIdeal.Fiber C) := hnoeth
  have hcompact : IsCompact T :=
    TopologicalSpace.NoetherianSpace.isCompact T
  -- Quasi-finiteness at a point makes that fiber point clopen, hence the subspace is discrete.
  have hdiscrete : IsDiscrete T := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro Q hQ
    letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal := hQ
    refine ⟨{Q}, ?_, ?_⟩
    · have hClopen :
          IsClopen ({Q} : Set (PrimeSpectrum (p.asIdeal.Fiber C))) :=
        @Algebra.QuasiFiniteAt.isClopen_singleton
          p.asIdeal.ResidueField (p.asIdeal.Fiber C) _ _ _ Q inferInstance inferInstance hQ
      exact hClopen.isOpen
    · ext Q'
      constructor
      · intro h
        exact h.1
      · intro h
        subst Q'
        exact ⟨rfl, hQ⟩
  simpa [T] using hcompact.finite hdiscrete

/-- Helper for Chap10 Lemma 10 125 2: over a fixed base prime, only finitely many target primes
are quasi-finite-at. -/
private lemma finiteQuasiFinitePrimesOver
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (p : Ideal A) [p.IsPrime] :
    Set.Finite { q : p.primesOver C | Algebra.QuasiFiniteAt A q.1 } := by
  -- Transfer the finite locus in the fiber across the standard primes-over equivalence.
  let e := PrimeSpectrum.primesOverOrderIsoFiber A C p
  let T : Set (p.primesOver C) := { q | Algebra.QuasiFiniteAt A q.1 }
  let pSpec : PrimeSpectrum A := ⟨p, inferInstance⟩
  have hImage : Set.Finite (e '' T) := by
    let hFiber :
        Set.Finite { Q : PrimeSpectrum (pSpec.asIdeal.Fiber C) |
          Algebra.QuasiFiniteAt pSpec.asIdeal.ResidueField Q.asIdeal } :=
      finiteQuasiFiniteAtFiberPrimes pSpec
    refine hFiber.subset ?_
    intro Q hQ
    rcases hQ with ⟨q, hqT, rfl⟩
    have hcomap : (e q).asIdeal.comap includeRight.toRingHom = q.1 := by
      change ((PrimeSpectrum.primesOverOrderIsoFiber A C p).symm (e q)).1 = q.1
      simp [e]
    letI : Algebra.QuasiFiniteAt A q.1 := hqT
    exact Algebra.QuasiFiniteAt.baseChange q.1 (e q).asIdeal hcomap.symm
  have hinj : Set.InjOn e T := by
    intro x _ y _ hxy
    exact e.injective hxy
  exact hImage.of_finite_image hinj

/-- Helper for Chap10 Lemma 10 125 2: a finite-type algebra is quasi-finite if it is
quasi-finite at every target prime. -/
private lemma quasiFinite_of_forall_quasiFiniteAt
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (h : ∀ Q : PrimeSpectrum C, Algebra.QuasiFiniteAt A Q.asIdeal) :
    Algebra.QuasiFinite A C := by
  -- Use the finite-fiber characterization of global quasi-finiteness.
  rw [Algebra.QuasiFinite.iff_finite_primesOver]
  intro p hp
  letI : p.IsPrime := hp
  have hfin : Set.Finite { q : p.primesOver C | Algebra.QuasiFiniteAt A q.1 } :=
    finiteQuasiFinitePrimesOver p
  have hset :
      ({ q : p.primesOver C | Algebra.QuasiFiniteAt A q.1 } : Set (p.primesOver C)) =
        Set.univ := by
    ext q
    simp [h ⟨q.1, inferInstance⟩]
  rw [hset] at hfin
  simpa [Set.image_univ] using hfin.image (fun q : p.primesOver C ↦ (q : Ideal C))

/-- Helper for Chap10 Lemma 10 125 2: if a basic open is contained in the quasi-finite-at locus,
then the corresponding away localization is quasi-finite over the base. -/
private lemma quasiFinite_localizationAway_of_basicOpen_subset_quasiFiniteAt
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (g : C)
    (hbasic : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
      { Q : PrimeSpectrum C | Algebra.QuasiFiniteAt A Q.asIdeal }) :
    Algebra.QuasiFinite A (Localization.Away g) := by
  -- Check quasi-finiteness at every prime of the localization by contracting it to `D(g)`.
  apply quasiFinite_of_forall_quasiFiniteAt
  intro Q
  let q : PrimeSpectrum C := PrimeSpectrum.comap (algebraMap C (Localization.Away g)) Q
  have hqbasic : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) := by
    have hRange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away g))) := by
      exact ⟨Q, rfl⟩
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hRange
  have hq : Algebra.QuasiFiniteAt A q.asIdeal :=
    hbasic hqbasic
  have hcomap : Ideal.comap (algebraMap C (Localization.Away g)) Q.asIdeal = q.asIdeal := by
    simpa [q] using (PrimeSpectrum.comap_asIdeal (algebraMap C (Localization.Away g)) Q).symm
  exact quasiFiniteAt_of_localization_comap
    (Submonoid.powers g) q.asIdeal Q.asIdeal hcomap hq

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: a prime avoiding an away parameter lifts to the away
localization. -/
private lemma exists_primeSpectrum_away_comap_eq_of_notMem
    {A : Type*} [CommRing A] (p : PrimeSpectrum A) {f : A} (hf : f ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap A (Localization.Away f)) q = p := by
  -- Proof comment: the image of `Spec(A_f)` is exactly the basic open `D(f)`.
  have hp_range : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    simpa [PrimeSpectrum.mem_basicOpen] using hf
  exact Set.mem_range.mp hp_range

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: an iterated away localization of `S_g` is a single away
localization of `S` after clearing the denominator of the second parameter. -/
private lemma singleOriginalAwayAlgEquiv
    (g : S) (u : Localization.Away g) :
    let h : S := g * (IsLocalization.Away.sec g u).1
    Nonempty (Localization.Away u ≃ₐ[R] Localization.Away h) := by
  -- Proof comment: replace the iterated denominator by a numerator representative, then compare
  -- both localizations through the standard associated-element equivalences.
  let a : S := (IsLocalization.Away.sec g u).1
  let h : S := g * a
  let hassoc :
      Associated (algebraMap S (Localization.Away g) a) u :=
    IsLocalization.Away.associated_sec_fst g u
  letI :
      IsLocalization.Away u (Localization.Away (algebraMap S (Localization.Away g) a)) :=
    IsLocalization.Away.of_associated hassoc
  let eIter :
      Localization.Away u ≃ₐ[R] Localization.Away (algebraMap S (Localization.Away g) a) :=
    (Localization.algEquiv
      (Submonoid.powers u)
      (Localization.Away (algebraMap S (Localization.Away g) a))).restrictScalars R
  letI :
      IsLocalization.Away h (Localization.Away (algebraMap S (Localization.Away g) a)) := by
    simpa [h]
      using
        (inferInstance :
          IsLocalization.Away h (Localization.Away (algebraMap S (Localization.Away g) a)))
  let eSingle :
      Localization.Away (algebraMap S (Localization.Away g) a) ≃ₐ[R] Localization.Away h :=
    (Localization.algEquiv
      (Submonoid.powers h)
      (Localization.Away (algebraMap S (Localization.Away g) a))).symm.restrictScalars R
  exact ⟨eIter.trans eSingle⟩

/-- Helper for Chap10 Lemma 10 125 2: if an element of `S_g` avoids a lifted prime over `q`,
then the corresponding cleared denominator in `S` still avoids `q`. -/
private lemma notMem_originalAway_of_iteratedAway
    (q : PrimeSpectrum S) {g : S} (hg : g ∉ q.asIdeal)
    {u : Localization.Away g} (qAway : PrimeSpectrum (Localization.Away g))
    (hqAway : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qAway = q)
    (hu : u ∉ qAway.asIdeal) :
    g * (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
  -- Proof comment: the numerator chosen by `sec` is associated to `u`, so if that numerator
  -- entered the lifted prime then `u` would enter as well; the product then avoids `q` by
  -- primality.
  have hsec_not_mem_away :
      algebraMap S (Localization.Away g) (IsLocalization.Away.sec g u).1 ∉ qAway.asIdeal := by
    intro hsec_mem
    have hu_mem : u ∈ qAway.asIdeal := by
      exact (Ideal.mem_iff_of_associated
        (IsLocalization.Away.associated_sec_fst g u)).mp hsec_mem
    exact hu hu_mem
  have hsec_not_mem :
      (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
    intro hsec_mem
    have hqAwayIdeal :
        Ideal.comap (algebraMap S (Localization.Away g)) qAway.asIdeal = q.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqAway
    have hmap_mem :
        algebraMap S (Localization.Away g) (IsLocalization.Away.sec g u).1 ∈
          qAway.asIdeal := by
      have :
          (IsLocalization.Away.sec g u).1 ∈
            Ideal.comap (algebraMap S (Localization.Away g)) qAway.asIdeal := by
        rw [hqAwayIdeal]
        exact hsec_mem
      simpa [Ideal.mem_comap] using this
    exact hsec_not_mem_away hmap_mem
  exact q.2.mul_notMem hg hsec_not_mem

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: the canonical fiber prime attached to `q` contracts back
to `q` along `S → (q ∩ R).Fiber S`. -/
private lemma fiberPrimeAt_comap_asIdeal_eq
    (q : PrimeSpectrum S) :
    Ideal.comap includeRight.toRingHom (fiberPrimeAt R S q).asIdeal = q.asIdeal := by
  -- Proof comment: `fiberPrimeAt` is defined by the fiber-prime equivalence, so contracting its
  -- underlying ideal is exactly the inverse branch applied to `q`.
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  change
    ((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)).1.asIdeal =
      q.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} ↦ x.1.asIdeal)
    (by simpa [fiberPrimeAt, p] using
      ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, rfl⟩))

/-- Helper for Chap10 Lemma 10 125 2: quasi-finiteness at `q` is equivalent to quasi-finiteness
at the corresponding prime of the fiber over `q ∩ R`. -/
private lemma quasiFiniteAt_iff_quasiFiniteAt_fiberPrime
    (q : PrimeSpectrum S) :
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      Algebra.QuasiFiniteAt (q.asIdeal.under R).ResidueField (fiberPrimeAt R S q).asIdeal := by
  constructor
  · intro hqf
    letI : Algebra.QuasiFiniteAt R q.asIdeal := hqf
    have hcomap :
        Ideal.comap includeRight.toRingHom (fiberPrimeAt R S q).asIdeal = q.asIdeal :=
      fiberPrimeAt_comap_asIdeal_eq q
    exact
      Algebra.QuasiFiniteAt.baseChange q.asIdeal (fiberPrimeAt R S q).asIdeal (by
        simpa using hcomap.symm)
  · intro hqf
    letI : q.asIdeal.LiesOver (q.asIdeal.under R) := ⟨by rfl⟩
    letI :
        Algebra.QuasiFiniteAt (q.asIdeal.under R).ResidueField (fiberPrimeAt R S q).asIdeal :=
      hqf
    have hcomap :
        Ideal.comap includeRight.toRingHom (fiberPrimeAt R S q).asIdeal = q.asIdeal :=
      fiberPrimeAt_comap_asIdeal_eq q
    exact
      Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
        (q.asIdeal.under R) q.asIdeal (fiberPrimeAt R S q).asIdeal (by
          simpa using hcomap)

/-- Helper for Chap10 Lemma 10 125 2: a prime of a fiber ring is the canonical `fiberPrimeAt`
once its contraction along `includeRight` is the original ambient prime. -/
private lemma fiberPrimeAt_eq_of_includeRight_comap_eq
    {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B)
    (r : PrimeSpectrum ((q.asIdeal.under A).Fiber B))
    (h :
      PrimeSpectrum.comap
          ((includeRight : B →ₐ[A] ((q.asIdeal.under A).Fiber B)).toRingHom) r =
        q) :
    r = fiberPrimeAt A B q := by
  let e := PrimeSpectrum.preimageEquivFiber A B (PrimeSpectrum.comap (algebraMap A B) q)
  have hs :
      e.symm r = ⟨q, rfl⟩ := by
    -- Proof comment: after returning through the fiber equivalence, the assumed contraction is
    -- exactly the defining subtype equality for the ambient prime `q`.
    apply Subtype.ext
    simpa [e] using h
  -- Proof comment: `fiberPrimeAt` is the image of the canonical ambient prime under the same
  -- equivalence, so both points agree once the inverse image is identified.
  rw [fiberPrimeAt]
  rw [← hs]
  exact (e.apply_symm_apply r).symm

/-- Helper for Chap10 Lemma 10 125 2: quasi-finiteness at a prime is preserved when restricting
scalars along a tower of commutative rings. -/
private lemma quasiFiniteAt_of_restrictScalars_local
    {A : Type u} {B : Type v} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (r : PrimeSpectrum C) (hAC : Algebra.QuasiFiniteAt A r.asIdeal) :
    Algebra.QuasiFiniteAt B r.asIdeal := by
  letI : Algebra.QuasiFiniteAt A r.asIdeal := hAC
  -- Restrict scalars on the local target ring `C_r`.
  change Algebra.QuasiFinite B (Localization.AtPrime r.asIdeal)
  exact Algebra.QuasiFinite.of_restrictScalars A B (Localization.AtPrime r.asIdeal)

/-- Helper for Chap10 Lemma 10 125 2: the tensor-side contraction identities force the localized
target prime `q₀` to lie over the same source prime `P₀Spec` carried by `rTensor`. -/
private lemma targetPrime_eq_comap_of_tensorPrime
    {A : Type u} {B : Type v} {F : Type*}
    [CommRing A] [CommRing B] [CommRing F]
    [Algebra R A] [Algebra R B] [Algebra R F]
    [Algebra A B] [IsScalarTower R A B] [Algebra A F] [IsScalarTower R A F]
    (P₀Spec : PrimeSpectrum A) (q₀ : PrimeSpectrum B) (rTensor : PrimeSpectrum F)
    (qTensor : PrimeSpectrum (F ⊗[A] B))
    (hrTensor_comap_P0 :
      Ideal.comap (algebraMap A F) rTensor.asIdeal = P₀Spec.asIdeal)
    (hqTensor_comap_q0 :
      Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom
        qTensor.asIdeal = q₀.asIdeal)
    (hqTensor_comap_rTensor :
      Ideal.comap (algebraMap F (F ⊗[A] B)) qTensor.asIdeal = rTensor.asIdeal) :
    P₀Spec = PrimeSpectrum.comap (algebraMap A B) q₀ := by
  -- Proof comment: contract first from the tensor product to `F`, then from `F` back to `A`;
  -- the two given comap identities identify the result with the contraction of `q₀`.
  apply PrimeSpectrum.ext
  calc
    P₀Spec.asIdeal = Ideal.comap (algebraMap A F) rTensor.asIdeal := by
      symm
      exact hrTensor_comap_P0
    _ = Ideal.comap (algebraMap A F)
          (Ideal.comap (algebraMap F (F ⊗[A] B)) qTensor.asIdeal) := by
        rw [hqTensor_comap_rTensor]
    _ = Ideal.comap ((algebraMap F (F ⊗[A] B)).comp (algebraMap A F)) qTensor.asIdeal := by
        rw [Ideal.comap_comap]
    _ = Ideal.comap
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom.comp
            (algebraMap A B))
          qTensor.asIdeal := by
        congr 1
        ext a
        simp [AlgHom.comp_algebraMap_of_tower]
    _ = Ideal.comap (algebraMap A B)
          (Ideal.comap
            (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom
            qTensor.asIdeal) := by
        rw [Ideal.comap_comap]
    _ = Ideal.comap (algebraMap A B) q₀.asIdeal := by
        rw [hqTensor_comap_q0]
    _ = (PrimeSpectrum.comap (algebraMap A B) q₀).asIdeal := by
        rfl

/-- Helper for Chap10 Lemma 10 125 2: before transporting across the residue-field bridge, one
can already normalize quasi-finiteness at `qTensor` to the canonical fiber prime over
`qTensor ∩ F`. -/
private lemma qTensorFiberQuasi_of_qTensorQuasi
    {A : Type u} {B : Type v} {F : Type*}
    [CommRing A] [CommRing B] [CommRing F]
    [Algebra R A] [Algebra R B] [Algebra R F]
    [Algebra A B] [IsScalarTower R A B] [Algebra A F] [IsScalarTower R A F]
    [Algebra.FiniteType A B]
    (qTensor : PrimeSpectrum (F ⊗[A] B))
    (hqTensor_quasi_F : Algebra.QuasiFiniteAt F qTensor.asIdeal) :
    @Algebra.QuasiFiniteAt
      (qTensor.asIdeal.under F).ResidueField
      ((qTensor.asIdeal.under F).Fiber (F ⊗[A] B))
      _ _ inferInstance
      (fiberPrimeAt F (F ⊗[A] B) qTensor).asIdeal inferInstance := by
  -- Proof comment: this is the direct ambient-to-fiber reformulation of quasi-finiteness at
  -- `qTensor`; no residue-field transport is needed yet.
  exact (quasiFiniteAt_iff_quasiFiniteAt_fiberPrime qTensor).mp hqTensor_quasi_F

/-- Helper for Chap10 Lemma 10 125 2: once the tensor-side fiber prime is quasi-finite and the
residue-field comparison between `P` and `r` is bijective, that quasi-finiteness descends to the
ambient target prime `q`. -/
private lemma quasiFiniteAt_of_tensorFiberPrimeTransport
    {A : Type u} {B : Type v} {F : Type*}
    [CommRing A] [CommRing B] [CommRing F]
    [Algebra R A] [Algebra R B] [Algebra R F]
    [Algebra A B] [IsScalarTower R A B] [Algebra A F] [IsScalarTower R A F]
    [Algebra.FiniteType A B]
    (P : PrimeSpectrum A) (q : PrimeSpectrum B) (r : PrimeSpectrum F)
    (Q : PrimeSpectrum (F ⊗[A] B)) (Qf : PrimeSpectrum (r.asIdeal.Fiber (F ⊗[A] B)))
    (hr : Ideal.comap (algebraMap A F) r.asIdeal = P.asIdeal)
    [r.asIdeal.LiesOver P.asIdeal]
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ P.asIdeal r.asIdeal
          (Algebra.ofId A F) (r.asIdeal.over_def P.asIdeal)))
    (hQq :
      Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom
        Q.asIdeal = q.asIdeal)
    (hQr :
      Ideal.comap (algebraMap F (F ⊗[A] B)) Q.asIdeal = r.asIdeal)
    (hQf_comap :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : (F ⊗[A] B) →ₐ[F] r.asIdeal.Fiber (F ⊗[A] B))
          Qf =
        Q)
    (hQfiber :
      @Algebra.QuasiFiniteAt
        r.asIdeal.ResidueField
        (r.asIdeal.Fiber (F ⊗[A] B))
        _ _ inferInstance
        Qf.asIdeal inferInstance) :
    Algebra.QuasiFiniteAt A q.asIdeal := by
  have hκTower :
      Function.Bijective
        (Ideal.ResidueField.mapₐ P.asIdeal r.asIdeal
          (IsScalarTower.toAlgHom R A F) hr.symm) := by
    simpa using hκ
  have hqOver : q.asIdeal.LiesOver P.asIdeal := by
    refine ⟨?_⟩
    have htarget : P = PrimeSpectrum.comap (algebraMap A B) q :=
      @targetPrime_eq_comap_of_tensorPrime R _ A B F _ _ _ _ _ _ _ _ _ _
        P q r Q hr hQq hQr
    simpa [Ideal.under, PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal htarget
  let qOver : P.asIdeal.primesOver B := ⟨q.asIdeal, inferInstance, hqOver⟩
  let qTransport : PrimeSpectrum (P.asIdeal.Fiber B) :=
    PrimeSpectrum.primesOverOrderIsoFiber A B P.asIdeal qOver
  let qTensorOver : r.asIdeal.primesOver (F ⊗[A] B) :=
    ⟨Q.asIdeal, inferInstance, ⟨hQr.symm⟩⟩
  have hqOver_eq :
      Ideal.fiberIsoOfBijectiveResidueField (S := B) hκTower qTensorOver = qOver := by
    -- Proof comment: the residue-field fiber equivalence contracts back to the same ambient prime,
    -- so the transported primes-over datum is the chosen point over `q`.
    apply Subtype.ext
    exact
      (Ideal.comap_fiberIsoOfBijectiveResidueField_apply (S := B) hκTower qTensorOver).trans hQq
  have hqTransport_comap_q :
      Ideal.comap includeRight.toRingHom qTransport.asIdeal = q.asIdeal := by
    change ((PrimeSpectrum.primesOverOrderIsoFiber A B P.asIdeal).symm qTransport).1 = q.asIdeal
    simpa [qTransport, qOver]
  let eResidue :
      P.asIdeal.ResidueField ≃ₐ[P.asIdeal.ResidueField] r.asIdeal.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hκ
  let eFiber :
      r.asIdeal.Fiber (F ⊗[A] B) ≃ₐ[P.asIdeal.ResidueField] P.asIdeal.Fiber B :=
    ((Algebra.TensorProduct.cancelBaseChange A F r.asIdeal.ResidueField
        r.asIdeal.ResidueField B).restrictScalars P.asIdeal.ResidueField).trans
      (Algebra.TensorProduct.congr (.symm <| .ofBijective (Algebra.ofId _ _) hκ) .refl)
  have hqTensorOverFiber :
      PrimeSpectrum.primesOverOrderIsoFiber F (F ⊗[A] B) r.asIdeal qTensorOver =
        Qf := by
    -- Proof comment: after applying the inverse `primesOver ↔ fiber` equivalence, both points
    -- become the same primes-over datum over the ambient tensor prime `Q`.
    apply (PrimeSpectrum.primesOverOrderIsoFiber F (F ⊗[A] B) r.asIdeal).symm.injective
    apply Subtype.ext
    simpa [qTensorOver, PrimeSpectrum.primesOverOrderIsoFiber, PrimeSpectrum.preimageOrderIsoFiber,
      PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hQf_comap).symm
  have htransportPrime :
      PrimeSpectrum.comapEquiv eFiber.toRingEquiv Qf = qTransport := by
    -- Proof comment: package the transported owner point at the `primesOver` level, then use the
    -- canonical comap formula for `Ideal.fiberIsoOfBijectiveResidueField`.
    rw [← hqTensorOverFiber]
    apply (PrimeSpectrum.primesOverOrderIsoFiber A B P.asIdeal).symm.injective
    change Ideal.fiberIsoOfBijectiveResidueField (S := B) hκTower qTensorOver = qOver
    exact hqOver_eq
  have hQfiberP :
      @Algebra.QuasiFiniteAt
        P.asIdeal.ResidueField
        (r.asIdeal.Fiber (F ⊗[A] B))
        _ _ inferInstance
        Qf.asIdeal inferInstance := by
    letI : Module.Finite P.asIdeal.ResidueField r.asIdeal.ResidueField :=
      Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
    letI : Algebra.QuasiFinite P.asIdeal.ResidueField r.asIdeal.ResidueField := inferInstance
    letI :
        @Algebra.QuasiFiniteAt
          r.asIdeal.ResidueField
          (r.asIdeal.Fiber (F ⊗[A] B))
          _ _ inferInstance
          Qf.asIdeal inferInstance :=
      hQfiber
    -- Proof comment: the finite residue-field extension `κ(P) → κ(r)` lets quasi-finiteness
    -- descend along transitivity on the corresponding localization.
    change
      Algebra.QuasiFinite P.asIdeal.ResidueField
        (Localization.AtPrime Qf.asIdeal)
    exact Algebra.QuasiFinite.trans
      P.asIdeal.ResidueField r.asIdeal.ResidueField
      (Localization.AtPrime Qf.asIdeal)
  have hqTransport_quasi :
      @Algebra.QuasiFiniteAt
        P.asIdeal.ResidueField
        (P.asIdeal.Fiber B)
        _ _ inferInstance
        qTransport.asIdeal inferInstance := by
    letI :
        @Algebra.QuasiFiniteAt
          P.asIdeal.ResidueField
          (r.asIdeal.Fiber (F ⊗[A] B))
          _ _ inferInstance
          Qf.asIdeal inferInstance :=
      hQfiberP
    have htemp :
        @Algebra.QuasiFiniteAt
          P.asIdeal.ResidueField
          (P.asIdeal.Fiber B)
          _ _ inferInstance
          (PrimeSpectrum.comapEquiv eFiber.toRingEquiv Qf).asIdeal inferInstance := by
      simpa [PrimeSpectrum.comapEquiv, PrimeSpectrum.comap_asIdeal] using
        (Algebra.QuasiFiniteAt.comap_algEquiv Qf.asIdeal eFiber.symm :
          @Algebra.QuasiFiniteAt
            P.asIdeal.ResidueField
            (P.asIdeal.Fiber B)
            _ _ inferInstance
            (Ideal.comap eFiber.symm.toRingHom Qf.asIdeal) inferInstance)
    have hPrimeEq : PrimeSpectrum.comapEquiv eFiber.toRingEquiv Qf = qTransport := htransportPrime
    cases hPrimeEq
    exact htemp
  letI :
      @Algebra.QuasiFiniteAt
        P.asIdeal.ResidueField
        (P.asIdeal.Fiber B)
        _ _ inferInstance
        qTransport.asIdeal inferInstance :=
    hqTransport_quasi
  -- Proof comment: after transporting quasi-finiteness to the target fiber prime over `q`, the
  -- standard residue-field criterion returns quasi-finiteness at the ambient prime `q`.
  exact Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
    P.asIdeal q.asIdeal qTransport.asIdeal (by simpa using hqTransport_comap_q)

/-- Helper for Chap10 Lemma 10 125 2: a finite algebra map is quasi-finite at every target prime.
-/
private lemma quasiFiniteAt_of_finiteAlgHom
    {K : Type*} [CommRing K]
    {A : Type*} [CommRing A] [Algebra K A]
    {B : Type*} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (hφ : AlgHom.Finite φ) (q : PrimeSpectrum B) :
    @Algebra.QuasiFiniteAt A B _ _ φ.toAlgebra q.asIdeal inferInstance := by
  -- Proof comment: global finiteness of `φ` gives global quasi-finiteness, and the target prime
  -- `q` then inherits the corresponding local statement by instance search.
  letI : Algebra A B := φ.toAlgebra
  have hφ_ring : RingHom.Finite φ.toRingHom := by
    simpa using hφ
  have hqf_ring : RingHom.QuasiFinite φ.toRingHom := by
    exact RingHom.QuasiFinite.of_finite hφ_ring
  letI : RingHom.QuasiFinite φ.toRingHom := hqf_ring
  letI : Algebra.QuasiFinite A B := hqf_ring
  infer_instance

/-- Helper for Chap10 Lemma 10 125 2: base-changing an `R`-algebra map along `K` commutes with the
canonical `includeRight` maps on the source and target. -/
private lemma tensorMap_comp_includeRight
    {K : Type*} [CommRing K] [Algebra R K]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (φ : A →ₐ[R] B) :
    (Algebra.TensorProduct.map (AlgHom.id _ _) φ).comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] (K ⊗[R] A)) =
      (Algebra.TensorProduct.includeRight : B →ₐ[R] (K ⊗[R] B)).comp φ := by
  -- Proof comment: both compositions send `a : A` to the tensor generator `1 ⊗ φ(a)`.
  ext a
  simp

/-- Helper for Chap10 Lemma 10 125 2: the quasi-finite-at locus is open even when the affine
source and target rings live in different universes. -/
private lemma isOpen_setOf_quasiFiniteAt_univ
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsOpen { Q : PrimeSpectrum C | Algebra.QuasiFiniteAt A Q.asIdeal } := by
  let Au := ULift.{v} A
  let Cu := ULift.{u} C
  letI : Algebra A Cu := ULift.algebra
  letI : Algebra Au Cu := ULift.algebra' A Cu
  letI : Algebra A Au := ULift.algebra
  letI : Algebra Au C := ULift.algebra' A C
  letI : Algebra Au A := ULift.algebra' A A
  letI : IsScalarTower A Au Cu := IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  letI : IsScalarTower A Au C := IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  letI : IsScalarTower Au A C := IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  have hftAuCu : Algebra.FiniteType Au Cu := by
    have hftACu : Algebra.FiniteType A Cu := by
      exact Algebra.FiniteType.equiv
        (inferInstance : Algebra.FiniteType A C)
        ULift.algEquiv.symm
    letI : Algebra.FiniteType A Cu := hftACu
    exact Algebra.FiniteType.of_restrictScalars_finiteType A Au Cu
  letI : Algebra.FiniteType Au Cu := hftAuCu
  let eC : Cu ≃+* C := ULift.ringEquiv
  let eSpec : PrimeSpectrum Cu ≃ₜ PrimeSpectrum C :=
    PrimeSpectrum.homeomorphOfRingEquiv eC
  let eAlg : Cu ≃ₐ[Au] C := ULift.algEquiv
  let T : Set (PrimeSpectrum Cu) := { Q : PrimeSpectrum Cu | Algebra.QuasiFiniteAt Au Q.asIdeal }
  have hopenLift : IsOpen T := by
    simpa [Au, Cu, T] using (isOpen_setOf_quasiFiniteAt : IsOpen T)
  have himage :
      eSpec '' T = { Q : PrimeSpectrum C | Algebra.QuasiFiniteAt A Q.asIdeal } := by
    ext q
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      have hqAu : Algebra.QuasiFiniteAt Au (eSpec Q).asIdeal := by
        letI : Algebra.QuasiFiniteAt Au Q.asIdeal := hQ
        have :
            Algebra.QuasiFiniteAt Au (Ideal.comap eAlg.symm.toRingHom Q.asIdeal) := by
          infer_instance
        simpa [eSpec, eAlg, PrimeSpectrum.comap_asIdeal] using this
      exact
        @quasiFiniteAt_of_restrictScalars_local Au A C _ _ _ _ _ _ _
          (eSpec Q) hqAu
    · intro hq
      refine ⟨eSpec.symm q, ?_, eSpec.apply_symm_apply q⟩
      have hqAu : Algebra.QuasiFiniteAt Au q.asIdeal :=
        @quasiFiniteAt_of_restrictScalars_local A Au C _ _ _ _ _ _ _ q hq
      letI : Algebra.QuasiFiniteAt Au q.asIdeal := hqAu
      have :
          Algebra.QuasiFiniteAt Au
            (Ideal.comap eAlg.toRingHom q.asIdeal) := by
        infer_instance
      simpa [T, eSpec, eAlg, PrimeSpectrum.comap_asIdeal] using this
  -- Transport the same-universe open locus on `ULift C` back to `Spec(C)`.
  have hopenImage : IsOpen (eSpec '' T) := eSpec.isOpenMap _ hopenLift
  simpa [himage] using hopenImage

/-- Helper for Chap10 Lemma 10 125 2: the fiber of a principal localization is ring-isomorphic to
the corresponding principal localization of the fiber ring. -/
private noncomputable def fiberLocalizationAwayRingEquiv_local
    (p : PrimeSpectrum R) [p.asIdeal.IsPrime] (g : S)
    [Algebra S (p.asIdeal.Fiber S)] [IsScalarTower R S (p.asIdeal.Fiber S)] :
    p.asIdeal.Fiber (Localization.Away g) ≃+*
      Localization.Away
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g) :=
  let K := p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber S
  let Sg := Localization.Away g
  letI : Algebra S Sg := inferInstance
  letI : Algebra R Sg := inferInstance
  letI : IsScalarTower R S Sg := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S F := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower R S F := inferInstance
  letI : Algebra F (Sg ⊗[S] F) := Algebra.TensorProduct.rightAlgebra
  let eCancel : p.asIdeal.Fiber Sg ≃ₐ[K] F ⊗[S] Sg :=
    (Algebra.IsPushout.cancelBaseChangeAlg R K S F Sg).symm
  let eComm : F ⊗[S] Sg ≃ₐ[F] Sg ⊗[S] F :=
    Algebra.TensorProduct.commRight S F Sg
  let eAway : Sg ⊗[S] F ≃ₐ[F]
      Localization.Away
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g) :=
    IsLocalization.Away.tensorRightEquiv F g Sg
  eCancel.toRingEquiv.trans eComm.toRingEquiv |>.trans eAway.toRingEquiv

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: a surjective polynomial presentation of `Localization.Away g₀`
base-changes to a surjective polynomial presentation of the closed fiber over `p`. -/
private lemma baseChangedAwayPresentation_surjective
    (p : PrimeSpectrum R) {g₀ : S} {m : ℕ}
    (π : MvPolynomial (Fin m) R →ₐ[R] Localization.Away g₀)
    (hπsurj : Function.Surjective π) :
    ∃ πκ : MvPolynomial (Fin m) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
        p.asIdeal.Fiber (Localization.Away g₀),
      Function.Surjective πκ ∧
        (∀ i, πκ (MvPolynomial.X i) =
          Algebra.TensorProduct.includeRight (π (MvPolynomial.X i))) := by
  let tensorPresentation :
      TensorProduct R p.asIdeal.ResidueField (MvPolynomial (Fin m) R) →ₐ[p.asIdeal.ResidueField]
        p.asIdeal.Fiber (Localization.Away g₀) :=
    Algebra.TensorProduct.map (AlgHom.id _ _) π
  let πκ :
      MvPolynomial (Fin m) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
        p.asIdeal.Fiber (Localization.Away g₀) :=
    tensorPresentation.comp
      (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).symm.toAlgHom
  have htensor_surj : Function.Surjective tensorPresentation := by
    -- Tensoring the fixed surjective presentation with `κ(p)` keeps it surjective.
    exact Algebra.FiniteType.baseChangeAux_surj p.asIdeal.ResidueField hπsurj
  have hπκ_surj : Function.Surjective πκ := by
    -- The tensor/polynomial equivalence turns the tensor presentation into the closed-fiber one.
    rw [show πκ =
      tensorPresentation.comp
        (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).symm.toAlgHom by rfl]
    exact htensor_surj.comp (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).symm.surjective
  refine ⟨πκ, hπκ_surj, ?_⟩
  intro i
  -- On variables, the base-changed map sends `X i` to the tensorized presentation generator.
  simp [πκ, tensorPresentation]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: a coordinate expression in the `ℤ`-subalgebra of the closed
fiber polynomial ring lifts to an actual element of the away localization. -/
private lemma exists_away_coordinate_int_expression_lift
    (p : PrimeSpectrum R) {g₀ : S} {m : ℕ}
    [_intAlg : Algebra ℤ p.asIdeal.ResidueField]
    (πκ : MvPolynomial (Fin m) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber (Localization.Away g₀))
    (x : Fin m → Localization.Away g₀)
    (hπκ_X : ∀ i, πκ (MvPolynomial.X i) = Algebra.TensorProduct.includeRight (x i))
    {z : MvPolynomial (Fin m) p.asIdeal.ResidueField}
    (hz : z ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
      Fin m → MvPolynomial (Fin m) p.asIdeal.ResidueField))) :
    ∃ s : Localization.Away g₀, Algebra.TensorProduct.includeRight s = πκ z := by
  let P :
      (w : MvPolynomial (Fin m) p.asIdeal.ResidueField) →
        w ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
          Fin m → MvPolynomial (Fin m) p.asIdeal.ResidueField)) → Prop :=
    fun w _ ↦ ∃ s : Localization.Away g₀, Algebra.TensorProduct.includeRight s = πκ w
  change P z hz
  -- Expressions in the coordinate `ℤ`-subalgebra are generated by variables and integer scalars.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
  · intro w hw
    rcases hw with ⟨i, rfl⟩
    refine ⟨x i, ?_⟩
    simpa using (hπκ_X i).symm
  · intro n
    refine ⟨algebraMap ℤ (Localization.Away g₀) n, ?_⟩
    -- Integer scalars agree in the tensor product and in the closed-fiber polynomial map.
    calc
      Algebra.TensorProduct.includeRight (algebraMap ℤ (Localization.Away g₀) n)
          = algebraMap (p.asIdeal.ResidueField) (p.asIdeal.Fiber (Localization.Away g₀))
              (algebraMap ℤ p.asIdeal.ResidueField n) := by
                simp
      _ = πκ (algebraMap ℤ (MvPolynomial (Fin m) p.asIdeal.ResidueField) n) := by
            symm
            simpa using πκ.commutes (algebraMap ℤ p.asIdeal.ResidueField n)
  · intro a b ha hb hPa hPb
    rcases hPa with ⟨sa, hsa⟩
    rcases hPb with ⟨sb, hsb⟩
    refine ⟨sa + sb, ?_⟩
    calc
      Algebra.TensorProduct.includeRight (sa + sb)
          = Algebra.TensorProduct.includeRight sa +
              Algebra.TensorProduct.includeRight sb := by
                simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add]
      _ = πκ a + πκ b := by rw [hsa, hsb]
      _ = πκ (a + b) := by rw [map_add]
  · intro a b ha hb hPa hPb
    rcases hPa with ⟨sa, hsa⟩
    rcases hPb with ⟨sb, hsb⟩
    refine ⟨sa * sb, ?_⟩
    calc
      Algebra.TensorProduct.includeRight (sa * sb)
          = Algebra.TensorProduct.includeRight sa *
              Algebra.TensorProduct.includeRight sb := by
                simp [Algebra.TensorProduct.includeRight_apply]
      _ = πκ a * πκ b := by rw [hsa, hsb]
      _ = πκ (a * b) := by rw [map_mul]

/-- Helper for Chap10 Lemma 10 125 2: after base change to `κ(p)`, the `i`th variable of
`MvPolynomial (Fin n) R` still evaluates to the tensor image of the chosen coordinate `y i`. -/
private lemma baseChangedMvPolynomialAeval_X
    (p : PrimeSpectrum R) {A : Type*} [CommRing A] [Algebra R A]
    {n : ℕ} (y : Fin n → A) (i : Fin n) :
    let φ : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval y
    ((Algebra.TensorProduct.map
        (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ).comp
        (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).symm.toAlgHom)
      (MvPolynomial.X i) =
        Algebra.TensorProduct.includeRight (y i) := by
  let φ : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval y
  -- Proof comment: the base-change equivalence sends `X i` to `1 ⊗ X i`, and the tensorized
  -- evaluation map then sends that tensor generator to `1 ⊗ y i`.
  simp [MvPolynomial.algebraTensorAlgEquiv_symm_X]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: normalization coordinates in the closed fiber descend to a
tuple in `Localization.Away g₀` once each coordinate polynomial lies in the ambient `ℤ`-subalgebra.
-/
private lemma descendedAwayNormalizationGenerators_from_coordinate_witnesses
    (p : PrimeSpectrum R) {g₀ : S} {m n : ℕ}
    [_intAlg : Algebra ℤ p.asIdeal.ResidueField]
    (πκ : MvPolynomial (Fin m) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber (Localization.Away g₀))
    (x : Fin m → Localization.Away g₀)
    (hπκ_X : ∀ i, πκ (MvPolynomial.X i) = Algebra.TensorProduct.includeRight (x i))
    (yκ : Fin n → MvPolynomial (Fin m) p.asIdeal.ResidueField)
    (hyκ : ∀ i, yκ i ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
      Fin m → MvPolynomial (Fin m) p.asIdeal.ResidueField)))
    (gκ : MvPolynomial (Fin n) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber (Localization.Away g₀))
    (hgκ_X : ∀ i, gκ (MvPolynomial.X i) = πκ (yκ i)) :
    ∃ y₀ : Fin n → Localization.Away g₀,
      ∀ i, Algebra.TensorProduct.includeRight (y₀ i) = gκ (MvPolynomial.X i) := by
  -- Lift each normalization coordinate separately and then rewrite with the defining variable
  -- formula for `gκ`.
  choose y₀ hy₀ using fun i ↦
    exists_away_coordinate_int_expression_lift p πκ x hπκ_X (hyκ i)
  refine ⟨y₀, ?_⟩
  intro i
  rw [hgκ_X i]
  exact hy₀ i

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: an element of the fiber base ring that avoids the base prime
also avoids every prime of the fiber ring. -/
private lemma notMem_fiberPrime_algebraMap_of_notMem
    (p : PrimeSpectrum R) (Q : PrimeSpectrum (p.asIdeal.Fiber S)) {r : R}
    (hr : r ∉ p.asIdeal) :
    algebraMap R (p.asIdeal.Fiber S) r ∉ Q.asIdeal := by
  -- Proof comment: every prime of the fiber contracts to `p`, so membership of `r` upstairs would
  -- force membership in the base prime.
  intro hrQ
  have hcomap :
      PrimeSpectrum.comap (algebraMap R (p.asIdeal.Fiber S)) Q = p := by
    exact (PrimeSpectrum.residueField_comap p).le ⟨Q.comap (algebraMap _ _), rfl⟩
  have hcomapIdeal :
      Ideal.comap (algebraMap R (p.asIdeal.Fiber S)) Q.asIdeal = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap
  have hrQ' :
      r ∈ Ideal.comap (algebraMap R (p.asIdeal.Fiber S)) Q.asIdeal := by
    simpa [Ideal.mem_comap] using hrQ
  rw [hcomapIdeal] at hrQ'
  exact hr hrQ'

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: clearing a denominator in the fiber ring does not change the
corresponding principal open subset of the fiber spectrum. -/
private lemma fiber_basicOpen_eq_basicOpen_one_tmul
    (p : PrimeSpectrum R) {a : p.asIdeal.Fiber S} {r : R} {g : S}
    (hr : r ∉ p.asIdeal) (h : r • a = (1 ⊗ₜ[R] g : p.asIdeal.Fiber S)) :
    (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (p.asIdeal.Fiber S))) =
      (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g : p.asIdeal.Fiber S) :
        Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
  -- Proof comment: the scalar `r` becomes a unit in every fiber-local ring, so multiplying by it
  -- does not change the vanishing locus.
  ext Q
  have hrQ :
      algebraMap R (p.asIdeal.Fiber S) r ∉ Q.asIdeal :=
    notMem_fiberPrime_algebraMap_of_notMem p Q hr
  have hmem :
      (1 ⊗ₜ[R] g : p.asIdeal.Fiber S) ∈ Q.asIdeal ↔ a ∈ Q.asIdeal := by
    rw [← h, Algebra.smul_def, Ideal.IsPrime.mul_mem_left_iff hrQ]
  simpa [PrimeSpectrum.mem_basicOpen] using (not_congr hmem).symm

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: from the local fiber-dimension equality at `q`, one can
choose an element `g₀ ∉ q` whose away localization has closed fiber of Krull dimension `n`. -/
private lemma exists_localizationAway_with_closedFiberDimension_eq
    (n : ℕ) (q : PrimeSpectrum S)
    (hdim :
      let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
      let qbar : PrimeSpectrum (p.asIdeal.Fiber S) :=
        PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
      topologicalKrullDimAt qbar = (n : WithBot ℕ∞)) :
    ∃ g₀ : S, g₀ ∉ q.asIdeal ∧
      let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
      ringKrullDim (p.asIdeal.Fiber (Localization.Away g₀)) = (n : WithBot ℕ∞) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let qbar : PrimeSpectrum (p.asIdeal.Fiber S) :=
    PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
  have hdim' : topologicalKrullDimAt qbar = (n : WithBot ℕ∞) := by
    simpa [p, qbar] using hdim
  -- Proof comment: realize the local dimension on an open neighborhood and then refine to a
  -- principal open of the form `D(1 ⊗ g₀)` by clearing one denominator in the fiber ring.
  obtain ⟨U, hU⟩ := exists_openNhdsOf_topologicalKrullDimAt_eq qbar
  have hqbarU : qbar ∈ (U : Set (PrimeSpectrum (p.asIdeal.Fiber S))) := U.2
  obtain ⟨V, ⟨a, rfl⟩, hqbarV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqbarU U.1.2
  obtain ⟨r, hr, g₀, hrg₀⟩ :=
    Ideal.Fiber.exists_smul_eq_one_tmul p.asIdeal a
  have hbasic_eq :
      (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (p.asIdeal.Fiber S))) =
        (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
          Set (PrimeSpectrum (p.asIdeal.Fiber S))) :=
    fiber_basicOpen_eq_basicOpen_one_tmul p hr hrg₀
  have hqbar_basic :
      qbar ∈ (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
        Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
    simpa [hbasic_eq] using hqbarV
  have hbasic_subset :
      (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
        Set (PrimeSpectrum (p.asIdeal.Fiber S))) ⊆ U := by
    simpa [hbasic_eq] using hVU
  have hg₀ : g₀ ∉ q.asIdeal := by
    -- Proof comment: if `g₀` lay in `q`, then `1 ⊗ g₀` would lie in the corresponding fiber
    -- prime, contradicting membership in the basic open.
    intro hg₀_mem
    have hmem_qbar :
        (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) ∈ qbar.asIdeal := by
      rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]
      simpa [IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField] using hg₀_mem
    exact (PrimeSpectrum.mem_basicOpen _ qbar).1 hqbar_basic hmem_qbar
  have hbasic_dim_le :
      topologicalKrullDim
          (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)) ≤
        topologicalKrullDim U := by
    -- Proof comment: view the principal open as a subspace of the minimizing neighborhood `U`.
    let e₁ :
        PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) ≃ₜ
          (((U : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∩
              (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
                Set (PrimeSpectrum (p.asIdeal.Fiber S)))) :
            Set (PrimeSpectrum (p.asIdeal.Fiber S))) :=
      Homeomorph.setCongr <| by
        ext y
        constructor
        · intro hy
          exact ⟨hbasic_subset hy, hy⟩
        · intro hy
          exact hy.2
    let e₂ :
        { y : U // y.1 ∈ (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
            Set (PrimeSpectrum (p.asIdeal.Fiber S))) } ≃ₜ
          (((U : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∩
              (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
                Set (PrimeSpectrum (p.asIdeal.Fiber S)))) :
            Set (PrimeSpectrum (p.asIdeal.Fiber S))) :=
      (Homeomorph.setCongr <| by
          ext y
          constructor
          · intro hy
            exact ⟨y.2, hy⟩
          · intro hy
            exact hy.2).trans
        (Topology.IsEmbedding.homeomorphOfSubsetRange Topology.IsEmbedding.subtypeVal fun y hy ↦
          ⟨⟨y, hy.1⟩, rfl⟩)
    have hsubspace :
        topologicalKrullDim
            { y : U // y.1 ∈ (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
                Set (PrimeSpectrum (p.asIdeal.Fiber S))) } ≤
          topologicalKrullDim U :=
      topologicalKrullDim_subspace_le U
        { y : U | y.1 ∈ (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
            Set (PrimeSpectrum (p.asIdeal.Fiber S))) }
    have heq₁ :
        topologicalKrullDim
            (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)) =
          topologicalKrullDim
            (((U : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∩
                (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
                  Set (PrimeSpectrum (p.asIdeal.Fiber S)))) :
              Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
      simpa [e₁] using IsHomeomorph.topologicalKrullDim_eq e₁ e₁.isHomeomorph
    have heq₂ :
        topologicalKrullDim
            { y : U // y.1 ∈ (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
                Set (PrimeSpectrum (p.asIdeal.Fiber S))) } =
          topologicalKrullDim
            (((U : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∩
                (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S) :
                  Set (PrimeSpectrum (p.asIdeal.Fiber S)))) :
              Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
      simpa [e₂] using IsHomeomorph.topologicalKrullDim_eq e₂ e₂.isHomeomorph
    rw [heq₁, ← heq₂]
    exact hsubspace
  have hdim_basic :
      topologicalKrullDimAt qbar =
        topologicalKrullDim
          (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)) := by
    refine le_antisymm ?_ ?_
    · exact topologicalKrullDimAt_le qbar
        ⟨PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S), hqbar_basic⟩
    · rw [hU]
      exact hbasic_dim_le
  have hhomeo :
      topologicalKrullDim (PrimeSpectrum (p.asIdeal.Fiber (Localization.Away g₀))) =
        topologicalKrullDim
          (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)) := by
    letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
    letI : IsScalarTower R S (p.asIdeal.Fiber S) := inferInstance
    let eRing :=
      fiberLocalizationAwayRingEquiv_local p g₀
    let eSpec :
        PrimeSpectrum (p.asIdeal.Fiber (Localization.Away g₀)) ≃ₜ
          PrimeSpectrum (Localization.Away (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)) :=
      PrimeSpectrum.homeomorphOfRingEquiv eRing
    have hloc :
        topologicalKrullDim (PrimeSpectrum (Localization.Away (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S))) =
          topologicalKrullDim
            (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)) := by
      simpa using
        IsHomeomorph.topologicalKrullDim_eq
          (primeSpectrum_localizationAway_homeomorph_D
            (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S))
          (primeSpectrum_localizationAway_homeomorph_D
            (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)).isHomeomorph
    calc
      topologicalKrullDim (PrimeSpectrum (p.asIdeal.Fiber (Localization.Away g₀))) =
          topologicalKrullDim
            (PrimeSpectrum (Localization.Away (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S))) := by
              simpa [eSpec] using IsHomeomorph.topologicalKrullDim_eq eSpec eSpec.isHomeomorph
      _ =
          topologicalKrullDim
            (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)) := hloc
  refine ⟨g₀, hg₀, ?_⟩
  -- Proof comment: identify the localized fiber with the principal open in the old fiber and
  -- transport the local dimension equality to a Krull-dimension equality of rings.
  change ringKrullDim (p.asIdeal.Fiber (Localization.Away g₀)) = (n : WithBot ℕ∞)
  calc
    ringKrullDim (p.asIdeal.Fiber (Localization.Away g₀)) =
        topologicalKrullDim (PrimeSpectrum (p.asIdeal.Fiber (Localization.Away g₀))) := by
          rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    _ =
        topologicalKrullDim
          (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g₀ : p.asIdeal.Fiber S)) := hhomeo
    _ = topologicalKrullDimAt qbar := hdim_basic.symm
    _ = (n : WithBot ℕ∞) := hdim'

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: once the away localization has closed fiber of dimension
`n`, the remaining normalization/descent argument should build the `n`-variable presentation that
is quasi-finite at the localized prime over `q`. -/
private lemma localizationAwayPresentation_comap_under_eq
    {A : Type*} [CommRing A] [Algebra R A] (q : PrimeSpectrum S) {g₀ : S}
    (hg₀ : g₀ ∉ q.asIdeal) (φ₀ : A →ₐ[R] Localization.Away g₀) :
    Ideal.under R
      (Ideal.comap φ₀.toRingHom (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal)) =
      (PrimeSpectrum.comap (algebraMap R S) q).asIdeal := by
  -- Proof comment: contract the localized prime first along `S → S_g`, then along `R → S`.
  calc
    Ideal.under R
        (Ideal.comap φ₀.toRingHom (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal))
      = Ideal.comap (algebraMap R A)
          (Ideal.comap φ₀.toRingHom (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal)) := by
            rfl
    _ = Ideal.comap (algebraMap R (Localization.Away g₀))
          (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal) := by
          rw [Ideal.comap_comap]
          congr
          ext r
          exact φ₀.commutes r
    _ = Ideal.comap (algebraMap R S)
          (Ideal.comap (algebraMap S (Localization.Away g₀))
            (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal)) := by
          ext r
          simp [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.Away g₀)]
    _ = Ideal.comap (algebraMap R S) q.asIdeal := by
          rw [localizedPrime_comap_map_eq q.asIdeal hg₀]
    _ = (PrimeSpectrum.comap (algebraMap R S) q).asIdeal := by
          rfl

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: descending the closed-fiber normalization coordinates
produces an away-local polynomial map whose base change recovers the finite normalization map. -/
private lemma exists_descendedAwayNormalizationAeval
    (p : PrimeSpectrum R) {g₀ : S} {m n : ℕ}
    [_intAlg : Algebra ℤ p.asIdeal.ResidueField]
    (πκ : MvPolynomial (Fin m) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber (Localization.Away g₀))
    (x : Fin m → Localization.Away g₀)
    (hπκ_X : ∀ i, πκ (MvPolynomial.X i) = Algebra.TensorProduct.includeRight (x i))
    (yκ : Fin n → MvPolynomial (Fin m) p.asIdeal.ResidueField)
    (hyκ : ∀ i, yκ i ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
      Fin m → MvPolynomial (Fin m) p.asIdeal.ResidueField)))
    (gκ : MvPolynomial (Fin n) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber (Localization.Away g₀))
    (hgκ_X : ∀ i, gκ (MvPolynomial.X i) = πκ (yκ i)) :
    ∃ φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀,
      ((Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ₀).comp
          (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).symm.toAlgHom) =
        gκ := by
  -- Proof comment: first descend the normalization coordinates from the closed fiber to
  -- `Localization.Away g₀`, then compare the resulting base-changed polynomial maps on generators.
  obtain ⟨y₀, hy₀⟩ :=
    descendedAwayNormalizationGenerators_from_coordinate_witnesses
      p πκ x hπκ_X yκ hyκ gκ hgκ_X
  let φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀ := MvPolynomial.aeval y₀
  refine ⟨φ₀, ?_⟩
  ext i
  calc
    ((Algebra.TensorProduct.map
        (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ₀).comp
        (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).symm.toAlgHom)
        (MvPolynomial.X i) =
        Algebra.TensorProduct.includeRight (y₀ i) := by
          simpa [φ₀] using baseChangedMvPolynomialAeval_X p y₀ i
    _ = gκ (MvPolynomial.X i) := by
          exact hy₀ i

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 2: the prime of the closed fiber over
`q₀ : PrimeSpectrum (Localization.Away g₀)` contracts back to `q₀` along the standard fiber
inclusion. -/
private lemma localizationAwayFiberPrime_comap_eq
    (p : PrimeSpectrum R) {g₀ : S}
    (q₀ : PrimeSpectrum (Localization.Away g₀))
    (hq₀ : PrimeSpectrum.comap (algebraMap R (Localization.Away g₀)) q₀ = p) :
    Ideal.comap
        (Algebra.TensorProduct.includeRight :
          Localization.Away g₀ →ₐ[R] p.asIdeal.Fiber (Localization.Away g₀)).toRingHom
        (PrimeSpectrum.preimageEquivFiber R (Localization.Away g₀) p ⟨q₀, hq₀⟩).asIdeal =
      q₀.asIdeal := by
  let qf : PrimeSpectrum (p.asIdeal.Fiber (Localization.Away g₀)) :=
    PrimeSpectrum.preimageEquivFiber R (Localization.Away g₀) p ⟨q₀, hq₀⟩
  -- Proof comment: `preimageEquivFiber` is inverse to the standard inclusion of the fiber, so
  -- the chosen closed-fiber prime contracts back to the original localized prime.
  change ((PrimeSpectrum.preimageEquivFiber R (Localization.Away g₀) p).symm qf).1.asIdeal =
    q₀.asIdeal
  have hqf_apply :
      (PrimeSpectrum.preimageEquivFiber R (Localization.Away g₀) p).symm qf =
        ⟨q₀, hq₀⟩ := by
    simpa [qf] using
      ((PrimeSpectrum.preimageEquivFiber R (Localization.Away g₀) p).symm_apply_apply
        ⟨q₀, hq₀⟩)
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap R (Localization.Away g₀)) ⁻¹' {p} ↦ x.1.asIdeal)
    hqf_apply

/-- Helper for Chap10 Lemma 10 125 2: finiteness of the closed-fiber normalization can be
rewritten from the raw polynomial presentation to the bundled source fiber
`p.asIdeal.Fiber (MvPolynomial (Fin n) R)`. -/
private lemma finiteBundledFiberPresentation
    (p : PrimeSpectrum R) {B : Type*} [CommRing B] [Algebra R B]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) R) B]
    [IsScalarTower R (MvPolynomial (Fin n) R) B]
    (φ : MvPolynomial (Fin n) R →ₐ[R] B)
    (hφκ_finite :
      AlgHom.Finite
        (((Algebra.TensorProduct.map
            (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ).comp
            (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).symm.toAlgHom))) :
    let F := p.asIdeal.Fiber (MvPolynomial (Fin n) R)
    let T := p.asIdeal.Fiber B
    let φF : F →ₐ[p.asIdeal.ResidueField] T :=
      Algebra.TensorProduct.map (AlgHom.id _ _) φ
    AlgHom.Finite φF := by
  -- Proof comment: the bundled source-fiber map differs from the raw polynomial-spelled map only
  -- by precomposing with the standard `MvPolynomial`/tensor equivalence.
  dsimp
  exact AlgHom.Finite.of_comp_finite hφκ_finite

/-- Helper for Chap10 Lemma 10 125 2: before any `cancelBaseChangeAlg` transport, the contracted
prime of the bundled source fiber already recovers the source prime `Ideal.comap φ q`. -/
private lemma bundledFiberSourcePrimeComap_eq
    (p : PrimeSpectrum R) {B : Type*} [CommRing B] [Algebra R B]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) R) B]
    [IsScalarTower R (MvPolynomial (Fin n) R) B]
    (φ : MvPolynomial (Fin n) R →ₐ[R] B)
    (q : PrimeSpectrum B)
    (hq_comap_p : PrimeSpectrum.comap (algebraMap R B) q = p) :
    let A := MvPolynomial (Fin n) R
    let F := p.asIdeal.Fiber A
    letI : Algebra A F := Algebra.TensorProduct.rightAlgebra
    let rightModule : Module A F := Algebra.toModule
    let rightSMul : SMul A F := rightModule.toDistribMulAction.toSMul
    letI : Module A F := rightModule
    letI : SMul A F := rightSMul
    let T := p.asIdeal.Fiber B
    let φF : F →ₐ[p.asIdeal.ResidueField] T :=
      Algebra.TensorProduct.map (AlgHom.id _ _) φ
    let qf : PrimeSpectrum T := PrimeSpectrum.preimageEquivFiber R B p ⟨q, hq_comap_p⟩
    Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] F).toRingHom
      (PrimeSpectrum.comap φF.toRingHom qf).asIdeal =
      Ideal.comap φ.toRingHom q.asIdeal := by
  -- Proof comment: unfold the contraction of the fiber prime once, rewrite the composite map with
  -- `tensorMap_comp_includeRight`, and then contract the ambient fiber prime back to `q`.
  dsimp
  change Ideal.comap
      (Algebra.TensorProduct.includeRight :
        MvPolynomial (Fin n) R →ₐ[R] p.asIdeal.Fiber (MvPolynomial (Fin n) R)).toRingHom
      (Ideal.comap
        (Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ).toRingHom
        (PrimeSpectrum.preimageEquivFiber R B p ⟨q, hq_comap_p⟩).asIdeal) =
    Ideal.comap φ.toRingHom q.asIdeal
  rw [Ideal.comap_comap]
  rw [show
      (Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          MvPolynomial (Fin n) R →ₐ[R] p.asIdeal.Fiber (MvPolynomial (Fin n) R)).toRingHom =
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).comp φ).toRingHom by
        exact congrArg AlgHom.toRingHom
          (tensorMap_comp_includeRight
            (R := R) (K := p.asIdeal.ResidueField)
            (A := MvPolynomial (Fin n) R) (B := B) φ)]
  change Ideal.comap φ.toRingHom
      (Ideal.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).toRingHom
        (PrimeSpectrum.preimageEquivFiber R B p ⟨q, hq_comap_p⟩).asIdeal) =
    Ideal.comap φ.toRingHom q.asIdeal
  rw [show
      Ideal.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).toRingHom
        (PrimeSpectrum.preimageEquivFiber R B p ⟨q, hq_comap_p⟩).asIdeal = q.asIdeal by
          simpa [hq_comap_p] using
            (fiber_prime_comap_asIdeal (R := R) (S := B) p
              (PrimeSpectrum.preimageEquivFiber R B p ⟨q, hq_comap_p⟩))]

/-- Helper for Chap10 Lemma 10 125 2: the closed-fiber cancellation equivalence sends the source
tensor inclusion back to the bundled finite map `φF`. -/
private lemma cancelBaseChangeComp_sourceIncludeLeft
    (p : PrimeSpectrum R) {B : Type*} [CommRing B] [Algebra R B]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) R) B]
    [IsScalarTower R (MvPolynomial (Fin n) R) B] :
    let A := MvPolynomial (Fin n) R
    let F := p.asIdeal.Fiber A
    letI : Algebra A F := Algebra.TensorProduct.rightAlgebra
    let rightModule : Module A F := Algebra.toModule
    let rightSMul : SMul A F := rightModule.toDistribMulAction.toSMul
    letI : Module A F := rightModule
    letI : SMul A F := rightSMul
    (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField A F B).toRingHom.comp
      (Algebra.TensorProduct.includeLeft : F →ₐ[p.asIdeal.ResidueField] F ⊗[A] B).toRingHom =
      (Algebra.TensorProduct.map
        (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
        (IsScalarTower.toAlgHom R A B)).toRingHom := by
  -- Proof comment: `cancelBaseChange_symm_comp_lTensor` identifies the inverse comparison with
  -- the source inclusion, and applying the forward equivalence recovers `φF`.
  dsimp
  letI :
      Algebra (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :=
    Algebra.TensorProduct.rightAlgebra
  letI :
      Module (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :=
    Algebra.toModule
  let rightSMul :
      SMul (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :=
    (show Module (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) from
      inferInstance).toDistribMulAction.toSMul
  letI :
      SMul (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :=
    rightSMul
  have hsymm :
      (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField
          (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) B).symm.toAlgHom.comp
        (Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
          (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) B)) =
      (Algebra.TensorProduct.includeLeft :
        p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
          p.asIdeal.Fiber (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] B) := by
    simpa using
      (Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor
        (R := R) (S := p.asIdeal.ResidueField)
        (A := MvPolynomial (Fin n) R) (C := B))
  apply RingHom.ext
  intro x
  have hx :
      (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField
          (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) B).symm
        ((Algebra.TensorProduct.map
            (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
            (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) B)) x) =
      (Algebra.TensorProduct.includeLeft :
        p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
          p.asIdeal.Fiber (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] B) x := by
    exact congrArg
      (fun f :
        p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
          p.asIdeal.Fiber (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] B ↦ f x)
      hsymm
  calc
    (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField
        (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) B)
        ((Algebra.TensorProduct.includeLeft :
          p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
            p.asIdeal.Fiber (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] B) x)
      =
        (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField
          (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) B)
          ((Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField
            (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) B).symm
            ((Algebra.TensorProduct.map
              (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
              (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) B)) x)) := by
                rw [hx.symm]
    _ =
        (Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
          (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) B)) x := by
            simp

/-- Helper for Chap10 Lemma 10 125 2: the same cancellation equivalence fixes the target-side
tensor inclusion `B → F ⊗[A] B`. -/
private lemma cancelBaseChangeComp_targetIncludeRight
    (p : PrimeSpectrum R) {B : Type*} [CommRing B] [Algebra R B]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) R) B]
    [IsScalarTower R (MvPolynomial (Fin n) R) B] :
    let A := MvPolynomial (Fin n) R
    let F := p.asIdeal.Fiber A
    letI : Algebra A F := Algebra.TensorProduct.rightAlgebra
    let rightModule : Module A F := Algebra.toModule
    let rightSMul : SMul A F := rightModule.toDistribMulAction.toSMul
    letI : Module A F := rightModule
    letI : SMul A F := rightSMul
    let T := p.asIdeal.Fiber B
    (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField A F B).toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom =
      (Algebra.TensorProduct.includeRight : B →ₐ[R] T).toRingHom := by
  -- Proof comment: both maps send `b : B` to the pure tensor `1 ⊗ b`, and
  -- `cancelBaseChangeAlg_tmul` leaves that tensor unchanged.
  dsimp
  letI :
      Algebra (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :=
    Algebra.TensorProduct.rightAlgebra
  letI :
      Module (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :=
    Algebra.toModule
  let rightSMul :
      SMul (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :=
    (show Module (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) from
      inferInstance).toDistribMulAction.toSMul
  letI :
      SMul (MvPolynomial (Fin n) R) (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :=
    rightSMul
  ext b
  simpa using
    (Algebra.IsPushout.cancelBaseChangeAlg_tmul
      (R := R) (S := p.asIdeal.ResidueField)
      (A := MvPolynomial (Fin n) R) (B := p.asIdeal.Fiber (MvPolynomial (Fin n) R))
      (C := B) b)

/-- Helper for Chap10 Lemma 10 125 2: the closed-fiber cancel-base-change equivalence sends the
`F`-algebra structure map on `F ⊗[A] Localization.Away g₀` to the finite closed-fiber map `φF`. -/
private lemma closedFiberCancelBaseChangeComp_sourceIncludeLeft
    (n : ℕ) (p : PrimeSpectrum R) {g₀ : S}
    (φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀)
    (φF : p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber (Localization.Away g₀))
    (hφF_def :
      φF =
        Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ₀) :
    let A := MvPolynomial (Fin n) R
    letI : Algebra A (Localization.Away g₀) := φ₀.toAlgebra
    letI : IsScalarTower R A (Localization.Away g₀) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ (φ₀.commutes r).symm
    let F := p.asIdeal.Fiber A
    letI : Algebra A F := Algebra.TensorProduct.rightAlgebra
    let rightModule : Module A F := Algebra.toModule
    let rightSMul : SMul A F := rightModule.toDistribMulAction.toSMul
    letI : Module A F := rightModule
    letI : SMul A F := rightSMul
    let T := p.asIdeal.Fiber (Localization.Away g₀)
    let U := F ⊗[A] Localization.Away g₀
    let eClosed :=
      Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField A F (Localization.Away g₀)
    eClosed.toRingHom.comp (Algebra.TensorProduct.includeLeft : F →ₐ[p.asIdeal.ResidueField] U).toRingHom =
      φF.toRingHom := by
  dsimp only
  rw [show φF.toRingHom =
      (Algebra.TensorProduct.map
        (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
        (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) (Localization.Away g₀))).toRingHom by
        simpa using congrArg AlgHom.toRingHom hφF_def]
  exact cancelBaseChangeComp_sourceIncludeLeft
    (R := R) (p := p) (B := Localization.Away g₀) (n := n)

/-- Helper for Chap10 Lemma 10 125 2: the closed-fiber cancel-base-change equivalence sends the
`F`-algebra structure map on `F ⊗[A] Localization.Away g₀` to the finite closed-fiber map `φF`. -/
private lemma closedFiberCancelBaseChangeAlg_commutes
    (n : ℕ) (p : PrimeSpectrum R) {g₀ : S}
    (φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀)
    (φF : p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber (Localization.Away g₀))
    (hφF_def :
      φF =
        Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ₀)
    (x : p.asIdeal.Fiber (MvPolynomial (Fin n) R)) :
    let A := MvPolynomial (Fin n) R
    letI : Algebra A (Localization.Away g₀) := φ₀.toAlgebra
    letI : IsScalarTower R A (Localization.Away g₀) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ (φ₀.commutes r).symm
    let F := p.asIdeal.Fiber A
    letI : Algebra A F := Algebra.TensorProduct.rightAlgebra
    let rightModule : Module A F := Algebra.toModule
    let rightSMul : SMul A F := rightModule.toDistribMulAction.toSMul
    letI : Module A F := rightModule
    letI : SMul A F := rightSMul
    let T := p.asIdeal.Fiber (Localization.Away g₀)
    let U := F ⊗[A] Localization.Away g₀
    let eClosed :=
      Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField A F (Localization.Away g₀)
    letI : Algebra F T := φF.toAlgebra
    eClosed (algebraMap F U x) = algebraMap F T x := by
  dsimp only
  rw [show eClosed.toRingHom.comp (Algebra.TensorProduct.includeLeft :
      p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
        (p.asIdeal.Fiber (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] Localization.Away g₀)).toRingHom =
      φF.toRingHom by
        simpa using
          closedFiberCancelBaseChangeComp_sourceIncludeLeft n p φ₀ φF hφF_def]
  simpa using
    congrArg
      (fun f : p.asIdeal.Fiber (MvPolynomial (Fin n) R) →+*
        p.asIdeal.Fiber (Localization.Away g₀) ↦ f x)
      rfl

/-- Helper for Chap10 Lemma 10 125 2: once the away localization has closed fiber of dimension
`n`, the remaining normalization/descent argument should build the `n`-variable presentation that
is quasi-finite at the localized prime over `q`. -/
private lemma quasiFiniteAt_localizedPrime_of_finiteClosedFiberPresentation
    (n : ℕ) (q : PrimeSpectrum S) {g₀ : S} (hg₀ : g₀ ∉ q.asIdeal)
    (p : PrimeSpectrum R)
    (Q₀ : Ideal (Localization.Away g₀)) (hQ₀ : Q₀.IsPrime)
    (hq₀_comap_p :
      PrimeSpectrum.comap (algebraMap R (Localization.Away g₀)) ⟨Q₀, hQ₀⟩ = p)
    (φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀)
    (φF : p.asIdeal.Fiber (MvPolynomial (Fin n) R) →ₐ[p.asIdeal.ResidueField]
      p.asIdeal.Fiber (Localization.Away g₀))
    (hφF_def :
      φF =
        Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ₀)
    (hφF_finite : AlgHom.Finite φF) :
    @Algebra.QuasiFiniteAt (MvPolynomial (Fin n) R) (Localization.Away g₀)
      _ _ φ₀.toAlgebra Q₀ hQ₀ := by
  let q₀ : PrimeSpectrum (Localization.Away g₀) := ⟨Q₀, hQ₀⟩
  let A := MvPolynomial (Fin n) R
  letI : Algebra A (Localization.Away g₀) := φ₀.toAlgebra
  letI : IsScalarTower R A (Localization.Away g₀) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ₀.commutes r).symm
  let F := p.asIdeal.Fiber A
  letI : Algebra A F := Algebra.TensorProduct.rightAlgebra
  let rightModule : Module A F := Algebra.toModule
  let rightSMul : SMul A F := rightModule.toDistribMulAction.toSMul
  letI : Module A F := rightModule
  letI : SMul A F := rightSMul
  let T := p.asIdeal.Fiber (Localization.Away g₀)
  let qf : PrimeSpectrum T :=
    PrimeSpectrum.preimageEquivFiber R (Localization.Away g₀) p ⟨q₀, hq₀_comap_p⟩
  let qAmbient : PrimeSpectrum A := ((PrimeSpectrum.preimageEquivFiber R A p).symm
    (PrimeSpectrum.comap φF.toRingHom qf)).1
  let rF : PrimeSpectrum F := PrimeSpectrum.comap φF.toRingHom qf
  have hrF_comap_qAmbient :
      Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] F).toRingHom rF.asIdeal =
        qAmbient.asIdeal := by
    simpa [rF, qAmbient] using (fiber_prime_comap_asIdeal (R := R) (S := A) p rF)
  letI : rF.asIdeal.LiesOver qAmbient.asIdeal := ⟨by
    simpa [Ideal.under] using hrF_comap_qAmbient⟩
  have hrF_residueFieldMap_bijective :
      Function.Bijective
        (Ideal.ResidueField.mapₐ qAmbient.asIdeal rF.asIdeal
          (IsScalarTower.toAlgHom R A F) (rF.asIdeal.over_def qAmbient.asIdeal)) := by
    simpa [qAmbient] using
      (fiber_prime_residueField_map_bijective (R := R) (S := A) p rF)
  let U := F ⊗[A] Localization.Away g₀
  let eClosed :=
    Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField A F (Localization.Away g₀)
  let qTensor : PrimeSpectrum U :=
    PrimeSpectrum.comap eClosed.toRingHom qf
  have hφF_eq :
      φF.toRingHom =
        (Algebra.TensorProduct.map
          (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
          (IsScalarTower.toAlgHom R A (Localization.Away g₀))).toRingHom := by
    simpa [A, T] using congrArg AlgHom.toRingHom hφF_def
  have hqTensor_comap_rF :
      Ideal.comap (Algebra.TensorProduct.includeLeft :
          F →ₐ[p.asIdeal.ResidueField] U).toRingHom
        qTensor.asIdeal = rF.asIdeal := by
    calc
      Ideal.comap (Algebra.TensorProduct.includeLeft :
          F →ₐ[p.asIdeal.ResidueField] U).toRingHom qTensor.asIdeal
        = Ideal.comap (eClosed.toRingHom.comp
            (Algebra.TensorProduct.includeLeft :
              F →ₐ[p.asIdeal.ResidueField] U).toRingHom) qf.asIdeal := by
                simpa [qTensor, Ideal.comap_comap]
      _ = Ideal.comap φF.toRingHom qf.asIdeal := by
            rw [closedFiberCancelBaseChangeComp_sourceIncludeLeft n p φ₀ φF hφF_def]
      _ = rF.asIdeal := rfl
  have hqTensor_comap_q0 :
      Ideal.comap (Algebra.TensorProduct.includeRight :
          Localization.Away g₀ →ₐ[A] U).toRingHom
        qTensor.asIdeal = q₀.asIdeal := by
    calc
      Ideal.comap (Algebra.TensorProduct.includeRight :
          Localization.Away g₀ →ₐ[A] U).toRingHom qTensor.asIdeal
        = Ideal.comap (eClosed.toRingHom.comp
            (Algebra.TensorProduct.includeRight :
              Localization.Away g₀ →ₐ[A] U).toRingHom)
            qf.asIdeal := by
                simpa [qTensor, Ideal.comap_comap]
      _ = Ideal.comap
          (Algebra.TensorProduct.includeRight : Localization.Away g₀ →ₐ[R] T).toRingHom
          qf.asIdeal := by
            exact congrArg
              (fun f : Localization.Away g₀ →+* T ↦ Ideal.comap f qf.asIdeal)
              (cancelBaseChangeComp_targetIncludeRight
                (R := R) (p := p) (B := Localization.Away g₀) (n := n))
      _ = q₀.asIdeal := localizationAwayFiberPrime_comap_eq p q₀ hq₀_comap_p
  have hqTensor_quasi_F :
      Algebra.QuasiFiniteAt F qTensor.asIdeal := by
    letI : Algebra F T := φF.toAlgebra
    let eClosedF : U ≃ₐ[F] T :=
      { __ := eClosed.toRingEquiv
        commutes' := fun x ↦
          closedFiberCancelBaseChangeAlg_commutes n p φ₀ φF hφF_def x }
    letI : Algebra.QuasiFiniteAt F qf.asIdeal :=
      quasiFiniteAt_of_finiteAlgHom φF hφF_finite qf
    simpa [qTensor, U] using (Algebra.QuasiFiniteAt.comap_algEquiv qf.asIdeal eClosedF)
  have hqTensorFiber_quasi :
      @Algebra.QuasiFiniteAt
        rF.asIdeal.ResidueField
        (rF.asIdeal.Fiber U)
        _ _ inferInstance
        (fiberPrimeAt F U qTensor).asIdeal inferInstance := by
    simpa [rF, qTensor, A, F, U] using
      qTensorFiberQuasi_of_qTensorQuasi
        (R := R) (A := A) (B := Localization.Away g₀) (F := F)
        qTensor hqTensor_quasi_F
  have hqTensorFiber_comap :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight :
            U →ₐ[F] rF.asIdeal.Fiber U)
          (fiberPrimeAt F U qTensor) =
        qTensor := by
    apply PrimeSpectrum.ext
    simpa [PrimeSpectrum.comap_asIdeal, rF, qTensor, A, F, U] using
      fiberPrimeAt_comap_asIdeal_eq qTensor
  -- Proof comment: once the closed-fiber presentation is finite, the tensor-fiber bridge returns
  -- quasi-finiteness at the localized prime of `Localization.Away g₀`.
  simpa [A, q₀] using
    quasiFiniteAt_of_tensorFiberPrimeTransport
      (R := R) (A := A) (B := Localization.Away g₀) (F := F)
      qAmbient q₀ rF qTensor (fiberPrimeAt F U qTensor)
      hrF_comap_qAmbient hrF_residueFieldMap_bijective
      hqTensor_comap_q0 hqTensor_comap_rF hqTensorFiber_comap hqTensorFiber_quasi

/-- Helper for Chap10 Lemma 10 125 2: once the away localization has closed fiber of dimension
`n`, the remaining normalization/descent argument should build the `n`-variable presentation that
is quasi-finite at the localized prime over `q`. -/
private lemma exists_quasiFiniteAt_polynomial_localizationAway_of_closedFiberDimension_eq
    (n : ℕ) (q : PrimeSpectrum S) {g₀ : S} (hg₀ : g₀ ∉ q.asIdeal)
    (hdim :
      let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
      ringKrullDim (p.asIdeal.Fiber (Localization.Away g₀)) = (n : WithBot ℕ∞)) :
    ∃ φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀,
      let Q₀ : Ideal (Localization.Away g₀) :=
        Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal
      ∃ hQ₀ : Q₀.IsPrime,
        @Algebra.QuasiFiniteAt (MvPolynomial (Fin n) R) (Localization.Away g₀)
          _ _ φ₀.toAlgebra Q₀ hQ₀ := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let T := p.asIdeal.Fiber (Localization.Away g₀)
  letI : Algebra ℤ p.asIdeal.ResidueField := Ring.toIntAlgebra p.asIdeal.ResidueField
  have hdim' : ringKrullDim T = (n : WithBot ℕ∞) := by
    simpa [p, T] using hdim
  let Q₀ : Ideal (Localization.Away g₀) :=
    Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal
  have hQ₀ : Q₀.IsPrime := localizedPrimeMap_isPrime q.asIdeal hg₀
  let q₀ : PrimeSpectrum (Localization.Away g₀) := ⟨Q₀, hQ₀⟩
  have hq₀_comap_p :
      PrimeSpectrum.comap (algebraMap R (Localization.Away g₀)) q₀ = p := by
    apply PrimeSpectrum.ext
    change
      Ideal.comap (algebraMap R (Localization.Away g₀)) Q₀ =
        Ideal.comap (algebraMap R S) q.asIdeal
    calc
      Ideal.comap (algebraMap R (Localization.Away g₀)) Q₀ =
          Ideal.comap (algebraMap R S)
            (Ideal.comap (algebraMap S (Localization.Away g₀)) Q₀) := by
              ext r
              simp [Q₀, Ideal.mem_comap,
                IsScalarTower.algebraMap_apply R S (Localization.Away g₀)]
      _ = Ideal.comap (algebraMap R S) q.asIdeal := by
            rw [localizedPrime_comap_map_eq q.asIdeal hg₀]
  let qf : PrimeSpectrum T :=
    PrimeSpectrum.preimageEquivFiber R (Localization.Away g₀) p ⟨q₀, hq₀_comap_p⟩
  letI : Nontrivial T := PrimeSpectrum.nontrivial qf
  -- Proof comment: choose a fixed affine presentation of `S_g₀` and base-change it to the closed
  -- fiber over `p = q ∩ R`.
  obtain ⟨m, π, hπsurj⟩ :=
    iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType R (Localization.Away g₀))
  let x : Fin m → Localization.Away g₀ := fun i ↦ π (MvPolynomial.X i)
  obtain ⟨πκ, hπκsurj, hπκ_X⟩ :=
    baseChangedAwayPresentation_surjective p π hπsurj
  let eκ :
      (MvPolynomial (Fin m) p.asIdeal.ResidueField ⧸ RingHom.ker πκ) ≃ₐ[p.asIdeal.ResidueField] T :=
    Ideal.quotientKerAlgEquivOfSurjective hπκsurj
  -- Proof comment: apply the field-case normalization theorem to the kernel quotient of the
  -- closed-fiber presentation, then transport it across the quotient-kernel equivalence.
  obtain ⟨r, yκ, hyκ, hnorm⟩ :=
    exists_noether_normalization_polynomials_quotient_mvPolynomial
      (RingHom.ker πκ) (RingHom.ker_ne_top πκ)
  let gquot :
      MvPolynomial (Fin r) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
        (MvPolynomial (Fin m) p.asIdeal.ResidueField ⧸ RingHom.ker πκ) :=
    MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk (RingHom.ker πκ) (yκ i)
  have hgquot_injective : Function.Injective gquot := by
    simpa [gquot] using hnorm.1
  have hgquot_finite : AlgHom.Finite gquot := by
    simpa [gquot] using hnorm.2
  let gκ :
      MvPolynomial (Fin r) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField] T :=
    eκ.toAlgHom.comp gquot
  have hgκ_injective : Function.Injective gκ := by
    exact eκ.injective.comp hgquot_injective
  have heκ_finite : AlgHom.Finite eκ.toAlgHom := by
    exact AlgHom.Finite.of_surjective eκ.toAlgHom eκ.surjective
  have hgκ_finite : AlgHom.Finite gκ := by
    exact AlgHom.Finite.comp heκ_finite hgquot_finite
  have hgκ_X : ∀ i, gκ (MvPolynomial.X i) = πκ (yκ i) := by
    intro i
    simp [gκ, gquot, eκ, Ideal.quotientKerAlgEquivOfSurjective_mk]
  have hr_eq : r = n := by
    have hdim_quot :
        ringKrullDim
            (MvPolynomial (Fin m) p.asIdeal.ResidueField ⧸ RingHom.ker πκ) =
          (r : WithBot ℕ∞) := by
      exact ringKrullDim_quotient_mvPolynomial_eq_of_finite_injective_polynomial_algebra
        (RingHom.ker πκ) gquot hgquot_injective hgquot_finite
    have hdim_gκ : ringKrullDim T = (r : WithBot ℕ∞) := by
      calc
        ringKrullDim T =
            ringKrullDim
              (MvPolynomial (Fin m) p.asIdeal.ResidueField ⧸ RingHom.ker πκ) := by
              simpa [eκ] using (ringKrullDim_eq_of_ringEquiv eκ.toRingEquiv).symm
        _ = (r : WithBot ℕ∞) := hdim_quot
    have hr_cast : (r : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hdim', hdim_gκ]
    exact_mod_cast hr_cast
  subst r
  -- Proof comment: descend the normalization coordinates to `Localization.Away g₀` and package
  -- the resulting away-local polynomial map together with its closed-fiber identification.
  obtain ⟨φ₀, hφκ_eq⟩ :=
    exists_descendedAwayNormalizationAeval p πκ x hπκ_X yκ hyκ gκ hgκ_X
  let φκ :
      MvPolynomial (Fin n) p.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField] T :=
    ((Algebra.TensorProduct.map
        (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ₀).comp
        (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).symm.toAlgHom)
  have hφκ_finite : AlgHom.Finite φκ := by
    simpa [φκ, hφκ_eq] using hgκ_finite
  let A := MvPolynomial (Fin n) R
  letI : Algebra A (Localization.Away g₀) := φ₀.toAlgebra
  letI : IsScalarTower R A (Localization.Away g₀) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ₀.commutes r).symm
  let F := p.asIdeal.Fiber A
  let T' := p.asIdeal.Fiber (Localization.Away g₀)
  let φF : F →ₐ[p.asIdeal.ResidueField] T' :=
    Algebra.TensorProduct.map
      (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField) φ₀
  have hφF_finite : AlgHom.Finite φF := by
    simpa [A, F, T', φF] using
      finiteBundledFiberPresentation
        (R := R) (p := p) (B := Localization.Away g₀) φ₀ hφκ_finite
  refine ⟨φ₀, hQ₀, ?_⟩
  -- Proof comment: the tensor/fiber descent is now isolated in a separate helper declaration,
  -- keeping this normalization lemma below the elaborator heartbeat budget.
  exact
    quasiFiniteAt_localizedPrime_of_finiteClosedFiberPresentation
      n q hg₀ p Q₀ hQ₀ hq₀_comap_p φ₀ φF rfl hφF_finite

/-- Helper for Chap10 Lemma 10 125 2: after one localization away from `q`, the source proof
produces an `n`-variable polynomial presentation that is quasi-finite at the localized prime over
`q` once the local topological dimension of the corresponding fiber point is `n`. -/
private lemma exists_quasiFiniteAt_polynomial_localizationAway_of_relativeDimensionAt_eq
    (n : ℕ) (q : PrimeSpectrum S)
    (hdim :
      let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
      let qbar : PrimeSpectrum (p.asIdeal.Fiber S) :=
        PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
      topologicalKrullDimAt qbar = (n : WithBot ℕ∞)) :
    ∃ g₀ : S, g₀ ∉ q.asIdeal ∧
      ∃ φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀,
        let Q₀ : Ideal (Localization.Away g₀) :=
          Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal
        ∃ hQ₀ : Q₀.IsPrime,
          @Algebra.QuasiFiniteAt (MvPolynomial (Fin n) R) (Localization.Away g₀)
            _ _ φ₀.toAlgebra Q₀ hQ₀ := by
  -- Route correction: first isolate the topological part and choose `g₀` so the closed fiber of
  -- `Localization.Away g₀` has Krull dimension `n`; then hand the purely algebraic normalization
  -- and finite-fiber descent to the dedicated closing helper.
  obtain ⟨g₀, hg₀, hdimFiber⟩ :=
    exists_localizationAway_with_closedFiberDimension_eq n q hdim
  obtain ⟨φ₀, hφ₀⟩ :=
    exists_quasiFiniteAt_polynomial_localizationAway_of_closedFiberDimension_eq
      n q hg₀ hdimFiber
  exact ⟨g₀, hg₀, φ₀, hφ₀⟩

/-- Helper for Chap10 Lemma 10 125 2: a polynomial presentation that is quasi-finite at the
localized prime over `q` can be shrunk once more to a globally quasi-finite away localization. -/
private lemma exists_quasiFinite_localizationAway_of_quasiFiniteAt_polynomial_localizationAway
    (q : PrimeSpectrum S) {n : ℕ} {g₀ : S} (hg₀ : g₀ ∉ q.asIdeal)
    (φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀)
    (hQ₀ :
      (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal).IsPrime)
    (hφ₀ :
      @Algebra.QuasiFiniteAt (MvPolynomial (Fin n) R) (Localization.Away g₀)
        _ _ φ₀.toAlgebra
        (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal) hQ₀) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        φ.QuasiFinite := by
  let A := MvPolynomial (Fin n) R
  letI : Algebra A (Localization.Away g₀) := φ₀.toAlgebra
  letI : IsScalarTower R A (Localization.Away g₀) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ₀.commutes r).symm
  letI : Algebra.FiniteType A (Localization.Away g₀) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R A (Localization.Away g₀)
  let q₀ : PrimeSpectrum (Localization.Away g₀) :=
    ⟨Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal, hQ₀⟩
  have hq₀_comap :
      PrimeSpectrum.comap (algebraMap S (Localization.Away g₀)) q₀ = q := by
    ext s
    change
      s ∈ Ideal.comap (algebraMap S (Localization.Away g₀)) q₀.asIdeal ↔
        s ∈ q.asIdeal
    simpa [q₀] using congrArg (fun I : Ideal S ↦ s ∈ I)
      (localizedPrime_comap_map_eq q.asIdeal hg₀)
  have hq₀_quasi :
      q₀ ∈ { Q : PrimeSpectrum (Localization.Away g₀) |
        Algebra.QuasiFiniteAt A Q.asIdeal } := by
    simpa [A, q₀] using hφ₀
  have hopen :
      IsOpen { Q : PrimeSpectrum (Localization.Away g₀) |
        Algebra.QuasiFiniteAt A Q.asIdeal } := by
    -- The quasi-finite-at locus is open for the polynomial presentation `φ₀`.
    exact isOpen_setOf_quasiFiniteAt_univ
  obtain ⟨V, ⟨u, rfl⟩, hq₀u, hVu⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq₀_quasi hopen
  have hu_not_mem : u ∉ q₀.asIdeal :=
    (PrimeSpectrum.mem_basicOpen u q₀).1 hq₀u
  have hquasi_u :
      Algebra.QuasiFinite A (Localization.Away u) :=
    quasiFinite_localizationAway_of_basicOpen_subset_quasiFiniteAt u hVu
  let g : S := g₀ * (IsLocalization.Away.sec g₀ u).1
  have hsingle : Nonempty (Localization.Away u ≃ₐ[R] Localization.Away g) :=
    @singleOriginalAwayAlgEquiv R S _ _ _ g₀ u
  obtain ⟨e⟩ := hsingle
  have hg_not_mem : g ∉ q.asIdeal := by
    -- Clearing the second denominator preserves avoidance of the original prime.
    simpa [g] using
      notMem_originalAway_of_iteratedAway q hg₀ q₀ hq₀_comap hu_not_mem
  let φu : A →ₐ[R] Localization.Away u :=
    IsScalarTower.toAlgHom R A (Localization.Away u)
  let φ : A →ₐ[R] Localization.Away g := e.toAlgHom.comp φu
  letI : Algebra A (Localization.Away g) := φ.toAlgebra
  let eA : Localization.Away u ≃ₐ[A] Localization.Away g :=
    { toRingEquiv := e.toRingEquiv
      commutes' := by
        intro a
        change e (φu a) = φ a
        simp [φ, φu] }
  have hquasi_g : Algebra.QuasiFinite A (Localization.Away g) := by
    -- Transport global quasi-finiteness across the single-away localization equivalence.
    exact (Algebra.QuasiFinite.iff_of_algEquiv eA).mp hquasi_u
  refine ⟨g, hg_not_mem, φ, ?_⟩
  simpa [φ] using hquasi_g

/- Domain-style sampling:
- primary domain: relative fiber dimension and quasi-finite polynomial presentations for finite-type
  algebras;
- sampled owner declarations:
  `relativeDimensionAt`,
  `Algebra.QuasiFinite`,
  `Localization.Away`;
- best owner abstraction: the source-facing public surface should use the fiber-point/topological
  dimension hypothesis from the Stacks source together with the resulting quasi-finite polynomial
  localization, while the chapter owner `relativeDimensionAt R S q` remains available as nearby
  project API;

Source/core/bridge triage:
- `source-facing`: after inverting some `g ∉ q`, the localized algebra `S_g` is quasi-finite over
  the polynomial algebra in `n` variables over `R`;
- `core/canonical`: `relativeDimensionAt`, `Algebra.QuasiFinite`, and `Localization.Away`;
- `bridge/view`: the quasi-finite polynomial-localization helpers above, which are used only to
  establish the source-facing presentation and the later open-neighbourhood consequence.

Primitive data are only the prime `q`, the integer `n`, and the equality
`topologicalKrullDimAt qbar = n` at the corresponding fiber point `qbar`. The away parameter `g`
and the polynomial presentation are the source-facing witnesses; the later open-neighbourhood
consequence belongs to Lemma `10.125.6`.
-/

/-- Chap10 Lemma 10 125 2 (Lemma 10.125.2): let `R → S` be a finite type ring map, let
`q : Spec(S)` be a prime, and let `p = q ∩ R` and `qbar` be the corresponding point of
`Spec(κ(p) ⊗[R] S)`. Assume `topologicalKrullDimAt qbar = n`. Then there exists `g : S` with
`g ∉ q` such that `S_g` is quasi-finite over the polynomial algebra `R[t₁, …, tₙ]`, formalized
here by an `R`-algebra map `MvPolynomial (Fin n) R →ₐ[R] Localization.Away g` that is
quasi-finite. -/
@[stacks 00QE]
theorem exists_quasiFinite_polynomial_localizationAway_of_relativeDimensionAt_eq
    (n : ℕ) (q : PrimeSpectrum S)
    (hdim :
      let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
      let qbar : PrimeSpectrum (p.asIdeal.Fiber S) :=
        PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
      topologicalKrullDimAt qbar = (n : WithBot ℕ∞)) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        φ.QuasiFinite := by
  -- Proof comment: first build the polynomial presentation that is quasi-finite at the localized
  -- prime, then shrink once more so the away localization becomes globally quasi-finite.
  obtain ⟨g₀, hg₀, φ₀, hQ₀, hφ₀⟩ :=
    exists_quasiFiniteAt_polynomial_localizationAway_of_relativeDimensionAt_eq n q hdim
  obtain ⟨g, hg, φ, hφ⟩ :=
    exists_quasiFinite_localizationAway_of_quasiFiniteAt_polynomial_localizationAway
      q hg₀ φ₀ hQ₀ hφ₀
  exact ⟨g, hg, φ, hφ⟩

end
