import Mathlib
import StacksProject_2024.Chap10.Lemma_10_122_4
import StacksProject_2024.Chap10.Lemma_10_25_1
import StacksProject_2024.Chap10.Lemma_10_32_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

open scoped Polynomial
open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- Helper for Lemma 10.122.11: finiteness of the primes of `S` over `p` makes every point of the
fiber over `p` quasi-finite. -/
lemma quasiFiniteAt_of_finite_primesOver
    (p : PrimeSpectrum R) (hfinite : Finite (p.asIdeal.primesOver S)) :
    ∀ q : PrimeSpectrum S,
      PrimeSpectrum.comap (algebraMap R S) q = p → Algebra.QuasiFiniteAt R q.asIdeal := by
  -- First transfer the finite-owner hypothesis to the canonical fiber algebra.
  let e := PrimeSpectrum.primesOverOrderIsoFiber R S p.asIdeal
  have hfiber : Finite (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    Finite.of_equiv (p.asIdeal.primesOver S) e.toEquiv
  -- Then invoke the `3 → 1` implication in Lemma `10.122.4`.
  exact
    ((quasiFiniteAt_primesOver_tfae_fiberFinite (R := R) (S := S) p).out 2 0 rfl rfl).mp hfiber

/-- Helper for Lemma 10.122.11: after localizing at a minimal prime `p`, every element of the
extended maximal ideal in the `S`-localization is nilpotent. -/
lemma isNilpotent_mem_extended_maximalIdeal_localization_of_minimalPrime
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    {x : Localization.AtPrime p.asIdeal}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) :
    IsNilpotent
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) x) := by
  let pmin : minimalPrimes R := ⟨p.asIdeal, hp⟩
  have hxnil :
      IsNilpotent x :=
    isNilpotent_of_mem_maximalIdeal_localizationAtPrime_of_minimalPrime pmin hx
  -- Map the nilpotent relation to the localization of `S`.
  exact hxnil.map <| algebraMap (Localization.AtPrime p.asIdeal)
    (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))

/-- Helper for Lemma 10.122.11: the extended maximal ideal `pS_p` is locally nilpotent when `p`
is a minimal prime. -/
lemma extended_maximalIdeal_localization_isLocallyNilpotent_of_minimalPrime
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) :
    (Ideal.map
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))).IsLocallyNilpotent := by
  let pmin : minimalPrimes R := ⟨p.asIdeal, hp⟩
  have hRp :
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).IsLocallyNilpotent := by
    -- The source route first proves local nilpotence in `R_p`.
    rw [Ideal.isLocallyNilpotent_iff]
    intro x hx
    exact isNilpotent_of_mem_maximalIdeal_localizationAtPrime_of_minimalPrime pmin hx
  -- Then Lemma `10.32.3` transports that ideal-level invariant across the map to `S_p`.
  simpa using
    Ideal.map_isLocallyNilpotent
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) hRp

/-- Helper for Lemma 10.122.11: every element of the extended maximal ideal `pS_p` is nilpotent.
This is the elementwise form of the source proof's local-nilpotence invariant. -/
lemma isNilpotent_mem_pSp_of_minimalPrime
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    {z : Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)}
    (hz : z ∈ Ideal.map
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))) :
    IsNilpotent z := by
  have hpSp :
      (Ideal.map
        (algebraMap (Localization.AtPrime p.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))).IsLocallyNilpotent :=
    extended_maximalIdeal_localization_isLocallyNilpotent_of_minimalPrime
      (R := R) (S := S) p hp
  -- Route correction: use the ideal-level local nilpotence from the source proof, then read off
  -- nilpotence of the specific element via `Ideal.isLocallyNilpotent_iff`.
  exact (Ideal.isLocallyNilpotent_iff _).mp hpSp z hz

/-- Helper for Lemma 10.122.11: finiteness of the primes of `S` over `p` makes the fiber algebra
itself finite over `κ(p)`. -/
lemma moduleFinite_fiber_of_finite_primesOver
    (p : PrimeSpectrum R) (hfinite : Finite (p.asIdeal.primesOver S)) :
    Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  -- First pass to the quasi-finite-at-every-point description of the finite fiber hypothesis.
  have hqf :
      ∀ q : PrimeSpectrum S,
        PrimeSpectrum.comap (algebraMap R S) q = p → Algebra.QuasiFiniteAt R q.asIdeal :=
    quasiFiniteAt_of_finite_primesOver (R := R) (S := S) p hfinite
  -- Then invoke the `1 → 2` direction in Lemma `10.122.4`.
  exact
    ((quasiFiniteAt_primesOver_tfae_fiberFinite (R := R) (S := S) p).out 0 1 rfl rfl).mp hqf

/-- Helper for Lemma 10.122.11: once the fiber algebra is finite over `κ(p)`, every tensor
generator `1 ⊗ x` is integral over `κ(p)`. -/
lemma isIntegral_tmul_right_of_moduleFinite_fiber
    (p : PrimeSpectrum R) [Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S)] (x : S) :
    IsIntegral p.asIdeal.ResidueField (1 ⊗ₜ[R] x : p.asIdeal.Fiber S) := by
  -- In a finite algebra, every element is integral over the base.
  exact IsIntegral.of_finite (R := p.asIdeal.ResidueField)
    (x := (1 ⊗ₜ[R] x : p.asIdeal.Fiber S))

/-- Helper for Lemma 10.122.11: after localizing `S` away from `p`, the image of `p` from `R`
coincides with the image of the maximal ideal of `R_p`. This is the source proof's stable
identification of `pS_p`. -/
lemma map_prime_to_semilocal_ideal_eq_pSp
    (p : PrimeSpectrum R) :
    Ideal.map
        (algebraMap R (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
        p.asIdeal =
      Ideal.map
        (algebraMap (Localization.AtPrime p.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) := by
  -- Push the canonical identification `pR_p = m_{R_p}` forward along `R_p → S_p`.
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  have hmap :
      Ideal.map (algebraMap R Rp) p.asIdeal = IsLocalRing.maximalIdeal Rp :=
    Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)
  -- The two descriptions differ only by whether we map through `R_p` first.
  calc
    Ideal.map (algebraMap R Sp) p.asIdeal
        = Ideal.map ((algebraMap Rp Sp).comp (algebraMap R Rp)) p.asIdeal := by
            simp [IsScalarTower.algebraMap_eq R Rp Sp]
    _ = Ideal.map (algebraMap Rp Sp) (Ideal.map (algebraMap R Rp) p.asIdeal) := by
          rw [Ideal.map_map]
    _ = Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp) := by rw [hmap]

/-- Helper for Lemma 10.122.11: the canonical `κ(p)`-algebra map from the residue field to the
quotient `S_p / pS_p`. -/
noncomputable def localized_quotient_residueFieldAlgHom
    (p : PrimeSpectrum R) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    p.asIdeal.ResidueField →ₐ[R] Sp ⧸ pSp := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  have hle : IsLocalRing.maximalIdeal Rp ≤ Ideal.comap (algebraMap Rp Sp) pSp :=
    Ideal.le_comap_map
  -- Descend the localized map `R_p → S_p` to the corresponding quotients.
  exact Ideal.quotientMapₐ pSp (IsScalarTower.toAlgHom R Rp Sp) hle

/-- Helper for Lemma 10.122.11: the source comparison map from the fiber algebra `κ(p) ⊗[R] S`
to the quotient `S_p / pS_p`. -/
noncomputable def fiber_to_localized_quotient_algHom
    (p : PrimeSpectrum R) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    p.asIdeal.Fiber S →ₐ[R] Sp ⧸ pSp := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  let φ₁ := localized_quotient_residueFieldAlgHom (R := R) (S := S) p
  -- Use the tensor-product universal property over `κ(p)` exactly as in the source proof.
  exact
    Algebra.TensorProduct.lift φ₁
      ((Ideal.Quotient.mkₐ R pSp).comp (IsScalarTower.toAlgHom R S Sp))
      (fun _ _ ↦ Commute.all _ _)

/-- Helper for Lemma 10.122.11: under the canonical comparison map, the tensor generator `1 ⊗ x`
becomes the class of `x` in `S_p / pS_p`. -/
lemma fiber_to_localized_quotient_algHom_tmul
    (p : PrimeSpectrum R) (x : S) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    let φ := fiber_to_localized_quotient_algHom (R := R) (S := S) p
    φ (1 ⊗ₜ[R] x) = Ideal.Quotient.mk pSp (algebraMap S Sp x) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  let φ₁ := localized_quotient_residueFieldAlgHom (R := R) (S := S) p
  let g : S →ₐ[R] Sp ⧸ pSp := (Ideal.Quotient.mkₐ R pSp).comp (IsScalarTower.toAlgHom R S Sp)
  -- Evaluate the tensor-product lift through the canonical inclusion `S → κ(p) ⊗[R] S`.
  change
      (Algebra.TensorProduct.lift φ₁ g (fun _ _ ↦ Commute.all _ _))
        (Algebra.TensorProduct.includeRight x) =
        Ideal.Quotient.mk pSp (algebraMap S Sp x)
  have hcomp :=
    DFunLike.congr_fun
      (Algebra.TensorProduct.lift_comp_includeRight'
        φ₁ g (fun _ _ ↦ Commute.all _ _)) x
  simpa [g] using hcomp

/-- Helper for Lemma 10.122.11: the comparison map from the fiber to `S_p / pS_p` agrees with the
canonical residue-field map on the left tensor factor. -/
lemma fiber_to_localized_quotient_comp_includeLeft
    (p : PrimeSpectrum R) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    let φ := fiber_to_localized_quotient_algHom (R := R) (S := S) p
    φ.comp (Algebra.TensorProduct.includeLeft : p.asIdeal.ResidueField →ₐ[R] p.asIdeal.Fiber S) =
      localized_quotient_residueFieldAlgHom (R := R) (S := S) p := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  let φ₁ := localized_quotient_residueFieldAlgHom (R := R) (S := S) p
  let g : S →ₐ[R] Sp ⧸ pSp := (Ideal.Quotient.mkₐ R pSp).comp (IsScalarTower.toAlgHom R S Sp)
  -- The tensor-product universal property records the source proof's scalar-compatibility step.
  change
      (Algebra.TensorProduct.lift φ₁ g (fun _ _ ↦ Commute.all _ _)).comp
        (Algebra.TensorProduct.includeLeft : p.asIdeal.ResidueField →ₐ[R] p.asIdeal.Fiber S) =
        φ₁
  simpa using
    (Algebra.TensorProduct.lift_comp_includeLeft
      φ₁ g (fun _ _ ↦ Commute.all _ _))

/-- Helper for Lemma 10.122.11: after installing the quotient `κ(p)`-algebra structure coming
from the source comparison map, the resulting scalar map is definitionally the usual
`algebraMap`. -/
lemma localized_quotient_residueFieldAlgHom_eq_algebraMap
    (p : PrimeSpectrum R) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
      (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
    (localized_quotient_residueFieldAlgHom (R := R) (S := S) p :
        p.asIdeal.ResidueField →+* Sp ⧸ pSp) =
      algebraMap p.asIdeal.ResidueField (Sp ⧸ pSp) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
    (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
  -- This is just the standard `toAlgebra` packaging of a ring hom as an `algebraMap`.
  rfl

/-- Helper for Lemma 10.122.11: integrality of a tensor generator in the fiber transports across
the source comparison map to integrality of its class in `S_p / pS_p`. -/
lemma isIntegral_quotient_class_of_isIntegral_fiber
    (p : PrimeSpectrum R) (x : S)
    (hx : IsIntegral p.asIdeal.ResidueField (1 ⊗ₜ[R] x : p.asIdeal.Fiber S)) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    let φ := fiber_to_localized_quotient_algHom (R := R) (S := S) p
    letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
      (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
    IsIntegral p.asIdeal.ResidueField (Ideal.Quotient.mk pSp (algebraMap S Sp x)) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  let φ : p.asIdeal.Fiber S →ₐ[R] Sp ⧸ pSp := by
    simpa [Rp, Sp, pSp] using fiber_to_localized_quotient_algHom (R := R) (S := S) p
  letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
    (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
  have hφ_scalars :
      φ.comp (Algebra.TensorProduct.includeLeft : p.asIdeal.ResidueField →ₐ[R] p.asIdeal.Fiber S) =
        localized_quotient_residueFieldAlgHom (R := R) (S := S) p := by
    -- The fiber comparison map agrees with the quotient scalar map on the left tensor factor.
    simpa [Rp, Sp, pSp, φ] using
      fiber_to_localized_quotient_comp_includeLeft (R := R) (S := S) p
  have hcomp :
      (algebraMap p.asIdeal.ResidueField (Sp ⧸ pSp)).comp (RingHom.id p.asIdeal.ResidueField) =
        φ.toRingHom.comp (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) := by
    -- Re-express the source scalar compatibility with the installed `κ(p)`-algebra structures.
    change (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toRingHom.comp
        (RingHom.id p.asIdeal.ResidueField) =
      φ.toRingHom.comp
        (Algebra.TensorProduct.includeLeft : p.asIdeal.ResidueField →ₐ[R] p.asIdeal.Fiber S).toRingHom
    rw [RingHom.comp_id]
    exact (congrArg AlgHom.toRingHom hφ_scalars).symm
  have hmap :
      IsIntegral p.asIdeal.ResidueField (φ (1 ⊗ₜ[R] x : p.asIdeal.Fiber S)) :=
    IsIntegral.map_of_comp_eq (φ := RingHom.id p.asIdeal.ResidueField) (ψ := φ.toRingHom) hcomp hx
  have hφx :
      φ (1 ⊗ₜ[R] x : p.asIdeal.Fiber S) =
        Ideal.Quotient.mk pSp (algebraMap S Sp x) := by
    -- This is the tensor-generator computation already isolated above.
    simpa [Rp, Sp, pSp, φ] using
      fiber_to_localized_quotient_algHom_tmul (R := R) (S := S) p x
  -- Finally rewrite the image of the tensor generator as the quotient class of `x`.
  simpa [hφx] using hmap

/-- Helper for Lemma 10.122.11: after identifying `S_p / pS_p` as a `κ(p)`-algebra via the source
comparison map, the evident maps `R_p → κ(p) → S_p / pS_p` form the expected scalar tower. -/
lemma localized_quotient_isScalarTower
    (p : PrimeSpectrum R) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
      (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
    IsScalarTower Rp p.asIdeal.ResidueField (Sp ⧸ pSp) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
    (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
  -- Evaluate the explicit quotient comparison on a residue class from `R_p`.
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  have hcomp :
      (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).comp
          (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal Rp)) =
        (Ideal.Quotient.mkₐ R pSp).comp (IsScalarTower.toAlgHom R Rp Sp) := by
    -- This is exactly the quotient-map computation built into `Ideal.quotientMapₐ`.
    simpa [localized_quotient_residueFieldAlgHom, Rp, Sp, pSp] using
      (Ideal.quotient_map_comp_mkₐ
        (R₁ := R) (I := IsLocalRing.maximalIdeal Rp) (J := pSp)
        (f := IsScalarTower.toAlgHom R Rp Sp) (H := Ideal.le_comap_map))
  simpa [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_def,
    Ideal.Quotient.mkₐ_eq_mk] using
    congrArg (fun f : Rp →ₐ[R] Sp ⧸ pSp => f r) hcomp

/-- Helper for Lemma 10.122.11: a monic annihilator over the residue field `κ(p)` lifts to a
monic polynomial over the localization `R_p`. -/
lemma lift_monic_annihilator_from_residueField
    (p : PrimeSpectrum R) (q : p.asIdeal.ResidueField[X]) (hq : q.Monic) :
    let Rp := Localization.AtPrime p.asIdeal
    ∃ Q : Rp[X], Q.Monic ∧ Polynomial.map (algebraMap Rp p.asIdeal.ResidueField) Q = q := by
  let Rp := Localization.AtPrime p.asIdeal
  -- Lift each coefficient along the surjective residue map, then invoke the monic lifting API.
  have hlifts : q ∈ Polynomial.lifts (algebraMap Rp p.asIdeal.ResidueField) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact IsLocalRing.residue_surjective (q.coeff n)
  obtain ⟨Q, hQmap, _, hQmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hq
  exact ⟨Q, hQmonic, hQmap⟩

/-- Helper for Lemma 10.122.11: integrality of the quotient class of `x` over `κ(p)` yields a
monic polynomial over `R_p` whose value on `x` lands in `pS_p`. -/
lemma exists_monic_relation_mem_pSp_of_isIntegral_quotient_class
    (p : PrimeSpectrum R) (x : S)
    (hz :
      let Rp := Localization.AtPrime p.asIdeal
      let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
      let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
      letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
        (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
      IsIntegral p.asIdeal.ResidueField (Ideal.Quotient.mk pSp (algebraMap S Sp x))) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
      (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
    ∃ Q : Rp[X], Q.Monic ∧ Polynomial.aeval (algebraMap S Sp x) Q ∈ pSp := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
    (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
  haveI : IsScalarTower Rp p.asIdeal.ResidueField (Sp ⧸ pSp) := by
    simpa [Rp, Sp, pSp] using localized_quotient_isScalarTower (R := R) (S := S) p
  obtain ⟨q, hqmonic, hqzero⟩ := by
    simpa [Rp, Sp, pSp] using hz
  obtain ⟨Q, hQmonic, hQmap⟩ := by
    simpa [Rp] using lift_monic_annihilator_from_residueField (R := R) p q hqmonic
  have hQmap' : Polynomial.map (algebraMap Rp p.asIdeal.ResidueField) Q = q := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using hQmap
  have hQzero :
      Polynomial.aeval (Ideal.Quotient.mk pSp (algebraMap S Sp x)) Q = 0 := by
    -- Rewrite the quotient annihilator from the residue-field coefficients back to `R_p`.
    rw [← Polynomial.aeval_map_algebraMap (A := p.asIdeal.ResidueField)
      (x := Ideal.Quotient.mk pSp (algebraMap S Sp x)) (p := Q), hQmap']
    exact hqzero
  refine ⟨Q, hQmonic, ?_⟩
  -- Then rewrite the quotient vanishing as membership in the extended maximal ideal `pS_p`.
  have hQzero' :
      Ideal.Quotient.mk pSp (Polynomial.aeval (algebraMap S Sp x) Q) = 0 := by
    calc
      Ideal.Quotient.mk pSp (Polynomial.aeval (algebraMap S Sp x) Q)
          = Polynomial.aeval (Ideal.Quotient.mk pSp (algebraMap S Sp x)) Q := by
              simpa [Ideal.Quotient.mkₐ_eq_mk] using
                (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ Rp pSp)
                  (algebraMap S Sp x) Q).symm
      _ = 0 := hQzero
  exact Ideal.Quotient.eq_zero_iff_mem.mp hQzero'

/-- Helper for Lemma 10.122.11: once the fiber generator `1 ⊗ x` is integral, local nilpotence of
`pS_p` upgrades the monic relation modulo `pS_p` to a genuine monic zero relation in `S_p`. -/
lemma exists_monic_zero_relation_in_semilocal_localization_of_isIntegral_fiber
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) (x : S)
    (hx : IsIntegral p.asIdeal.ResidueField (1 ⊗ₜ[R] x : p.asIdeal.Fiber S)) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
    ∃ Q : Rp[X], Q.Monic ∧ Polynomial.aeval (algebraMap S Sp x) Q = 0 := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp := Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
    (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
  obtain ⟨Q, hQmonic, hQmem⟩ :=
    exists_monic_relation_mem_pSp_of_isIntegral_quotient_class (R := R) (S := S) p x <|
      by
        -- The fiber-integral generator first becomes integral in the quotient `S_p / pS_p`.
        simpa [Rp, Sp, pSp] using
          isIntegral_quotient_class_of_isIntegral_fiber (R := R) (S := S) p x hx
  have hnil :
      IsNilpotent (Polynomial.aeval (algebraMap S Sp x) Q) :=
    isNilpotent_mem_pSp_of_minimalPrime (R := R) (S := S) p hp hQmem
  obtain ⟨n, hn⟩ := hnil
  refine ⟨Q ^ (n + 1), hQmonic.pow (n + 1), ?_⟩
  -- Replace `Q` by a positive power so the nilpotent value becomes literally zero.
  calc
    Polynomial.aeval (algebraMap S Sp x) (Q ^ (n + 1))
        = (Polynomial.aeval (algebraMap S Sp x) Q) ^ (n + 1) := by
            simp [Polynomial.aeval_def]
    _ = 0 := by
      rw [pow_succ, hn, zero_mul]

/-- Helper for Lemma 10.122.11: a finite family of monic polynomials over `R_p` descends to one
principal localization `R[1 / g₁]` with `g₁ ∉ p`. -/
lemma exists_notMem_monic_lift_family_from_localizationAtPrime
    (p : PrimeSpectrum R) {n : ℕ}
    (Q : Fin n → (Localization.AtPrime p.asIdeal)[X])
    (hQmonic : ∀ i, (Q i).Monic) :
    ∃ g₁ : R, ∃ hg₁ : g₁ ∉ p.asIdeal,
      ∃ Q₁ : Fin n → (Localization.Away g₁)[X],
        (∀ i, (Q₁ i).Monic) ∧
        ∀ i,
          Polynomial.map
              (Localization.awayLift
                (algebraMap R (Localization.AtPrime p.asIdeal)) g₁
                ((IsLocalization.AtPrime.isUnit_to_map_iff
                  (Localization.AtPrime p.asIdeal) p.asIdeal g₁).2 hg₁))
              (Q₁ i) = Q i := by
  classical
  let Rp := Localization.AtPrime p.asIdeal
  let coeffs : Finset Rp :=
    Finset.univ.biUnion fun i ↦ (Q i).support.image fun m ↦ (Q i).coeff m
  choose a s hs using fun x : { x // x ∈ coeffs } ↦
    IsLocalization.exists_mk'_eq p.asIdeal.primeCompl (x : Rp)
  let m : p.asIdeal.primeCompl := coeffs.attach.prod s
  have hcoeffs :
      ∀ x ∈ coeffs,
        x ∈ Set.range
          (Localization.awayLift (algebraMap R Rp) (m : R)
            ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal (m : R)).2 m.2)) := by
    intro x hx
    let x' : { x // x ∈ coeffs } := ⟨x, hx⟩
    let t : p.asIdeal.primeCompl := (coeffs.attach.erase x').prod s
    have hm : m = s x' * t := by
      -- Split the common denominator into the chosen factor and the complementary product.
      symm
      simpa [m, t] using
        (Finset.mul_prod_erase (s := coeffs.attach) (a := x') (f := s) (by simp))
    letI : IsLocalization.Away (algebraMap R Rp (m : R)) Rp :=
      IsLocalization.away_of_isUnit_of_bijective Rp
        ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal (m : R)).2 m.2)
        Function.bijective_id
    have hAway :
        Localization.awayLift (algebraMap R Rp) (m : R)
            ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal (m : R)).2 m.2) =
          IsLocalization.Away.map (S := Localization.Away (m : R)) (Q := Rp)
            (algebraMap R Rp) (m : R) := by
      -- Both maps agree on `R`, so localization extensionality identifies them.
      apply IsLocalization.ringHom_ext (Submonoid.powers (m : R))
      ext r
      simpa [Localization.awayLift, IsLocalization.Away.map] using
        (IsLocalization.map_eq (M := Submonoid.powers (m : R))
          (S := Localization.Away (m : R)) (Q := Rp) (g := algebraMap R Rp)
          (hy := by
            rintro x ⟨n, rfl⟩
            exact ⟨n, by simp⟩) r)
    refine ⟨Localization.mk (a x' * (t : R)) ⟨(m : R), by exact ⟨1, by simp⟩⟩, ?_⟩
    rw [Localization.mk_eq_mk']
    rw [hAway]
    simp only [IsLocalization.Away.map, IsLocalization.map_mk', map_mul]
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    rw [show x = ↑x' by rfl, ← hs x']
    rw [hm, map_mul]
    calc
      algebraMap R Rp (a x') * algebraMap R Rp (t : R)
          = (algebraMap R Rp (s x') * IsLocalization.mk' Rp (a x') (s x')) *
              algebraMap R Rp (t : R) := by
                rw [IsLocalization.mk'_spec']
      _ = IsLocalization.mk' Rp (a x') (s x') *
            (algebraMap R Rp (s x') * algebraMap R Rp (t : R)) := by
              ring
      _ = _ := by
            simpa [hm, map_mul]
  let g₁ : R := m
  let lift : Localization.Away g₁ →+* Rp :=
    Localization.awayLift
      (algebraMap R Rp) g₁
      ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal g₁).2 <| by
        simpa [g₁, Ideal.primeCompl] using m.2)
  have hcoeff_lifts (i : Fin n) :
      Q i ∈ Polynomial.lifts lift := by
    -- Every nonzero coefficient lies in the chosen finite coefficient set, so the common
    -- denominator from `exists_awayMap_range_finset` lifts the whole polynomial.
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    by_cases hm : m ∈ (Q i).support
    · have hmem_coeffs : (Q i).coeff m ∈ coeffs := by
        change (Q i).coeff m ∈
          Finset.biUnion Finset.univ (fun j : Fin n ↦ (Q j).support.image fun k ↦ (Q j).coeff k)
        exact
          Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
      exact hcoeffs _ hmem_coeffs
    · refine ⟨0, ?_⟩
      simpa [Polynomial.notMem_support_iff.mp hm]
  choose Q₁ hQ₁map hQ₁deg hQ₁monic using
    fun i ↦ Polynomial.lifts_and_natDegree_eq_and_monic (hcoeff_lifts i) (hQmonic i)
  have hg₁ : g₁ ∉ p.asIdeal := by
    change (m : R) ∉ p.asIdeal
    exact m.2
  refine ⟨g₁, hg₁, Q₁, hQ₁monic, ?_⟩
  intro i
  simpa [lift] using hQ₁map i

/-- Helper for Lemma 10.122.11: a monic annihilating polynomial continues to witness integrality
after applying an algebra hom. -/
lemma isIntegral_image_of_monic_zero_relation_under_algHom
    {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (φ : B →ₐ[A] C) {x : B} {Q : A[X]} (hQmonic : Q.Monic)
    (hQzero : φ (Polynomial.aeval x Q) = 0) :
    IsIntegral A (φ x) := by
  refine ⟨Q, hQmonic, ?_⟩
  -- Rewrite the mapped relation as evaluation of the same polynomial on the image element.
  simpa using
    (Polynomial.map_aeval_eq_aeval_map
      (R := A) (S := B) (T := A) (U := C)
      (φ := RingHom.id A) (ψ := φ.toRingHom)
      (by
        ext a
        simp)
      Q x).symm.trans hQzero

/-- Helper for Lemma 10.122.11: if a chosen generator family is integral over the base, then the
whole algebra is integral over the base. -/
lemma isIntegral_of_integral_generators
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} (P : Algebra.Generators A B ι)
    (hP : ∀ i, IsIntegral A (P.val i)) :
    Algebra.IsIntegral A B := by
  refine ⟨fun x ↦ ?_⟩
  have hAdjoin :
      Algebra.IsIntegral A (Algebra.adjoin A (Set.range P.val)) :=
    Algebra.IsIntegral.adjoin fun y hy ↦ by
      rcases hy with ⟨i, rfl⟩
      exact hP i
  have hxmem : x ∈ Algebra.adjoin A (Set.range P.val) := by
    -- The generators come with a section of the universal polynomial evaluation map.
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨P.σ x, P.aeval_val_σ x⟩
  let x' : Algebra.adjoin A (Set.range P.val) := ⟨x, hxmem⟩
  have hx' : IsIntegral A x' :=
    Algebra.IsIntegral.isIntegral x'
  -- Forget from the integral subalgebra back to the ambient algebra.
  simpa [x'] using hx'.map (Algebra.adjoin A (Set.range P.val)).val

/-- Helper for Lemma 10.122.11: if `g ∉ p`, then the image of `g` in the semilocal localization of
`S` at `p` is a unit. -/
lemma semilocal_image_isUnit_of_notMem
    (p : PrimeSpectrum R) {g : R} (hg : g ∉ p.asIdeal) :
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    IsUnit (algebraMap S Sp (algebraMap R S g)) := by
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  exact
    IsLocalization.map_units Sp
      ⟨algebraMap R S g,
        Algebra.mem_algebraMapSubmonoid_of_mem
          (S := S) (M := p.asIdeal.primeCompl) ⟨g, hg⟩⟩

/-- Helper for Lemma 10.122.11: if finitely many elements of `S[1 / g₁]` become zero after
localizing further at the image of `R \ p`, then one element `g₂ ∉ p` annihilates all of them
already in `S[1 / g₁]`. -/
lemma exists_notMem_zero_family_of_zero_in_semilocal_localization
    (p : PrimeSpectrum R) {n : ℕ} {g₁ : R} (hg₁ : g₁ ∉ p.asIdeal)
    (z : Fin n → Localization.Away (algebraMap R S g₁))
    (hz :
      let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
      let ψ : Localization.Away (algebraMap R S g₁) →+* Sp :=
        Localization.awayLift (algebraMap S Sp) (algebraMap R S g₁)
          (semilocal_image_isUnit_of_notMem (R := R) (S := S) p hg₁)
      ∀ i, ψ (z i) = 0) :
    ∃ g₂ : R, g₂ ∉ p.asIdeal ∧
      ∀ i, algebraMap R (Localization.Away (algebraMap R S g₁)) g₂ * z i = 0 := by
  classical
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let ψ : Localization.Away (algebraMap R S g₁) →+* Sp :=
    Localization.awayLift (algebraMap S Sp) (algebraMap R S g₁)
      (semilocal_image_isUnit_of_notMem (R := R) (S := S) p hg₁)
  have hz' : ∀ i, ψ (z i) = 0 := by
    simpa [Sp, ψ] using hz
  choose e a ha using fun i : Fin n ↦
    IsLocalization.Away.surj (algebraMap R S g₁) (z i)
  have ha_zero_sp (i : Fin n) : algebraMap S Sp (a i) = 0 := by
    -- Clear the fixed `g₁`-denominator and then use that `z i` vanishes in the semilocal ring.
    have hmap := congrArg ψ (ha i)
    rw [map_mul, hz' i, zero_mul] at hmap
    simpa [ψ, map_pow, Localization.awayLift] using hmap.symm
  have hkill :
      ∀ i : Fin n, ∃ t : p.asIdeal.primeCompl, algebraMap R S t * a i = 0 := by
    intro i
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) Sp (a i)).mp (ha_zero_sp i)
    rcases m with ⟨m, hm_mem⟩
    rcases
        (show ∃ t : p.asIdeal.primeCompl, algebraMap R S t = m by
          simpa [Algebra.algebraMapSubmonoid, Submonoid.mem_map] using hm_mem) with
      ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simpa [ht, mul_comm] using hm
  choose t ht using hkill
  let g₂ : R := Finset.univ.prod fun i : Fin n ↦ (t i : R)
  have hg₂_compl : g₂ ∈ p.asIdeal.primeCompl := by
    -- The product of finitely many elements outside the prime ideal still avoids the prime ideal.
    simpa [g₂] using
      (Submonoid.prod_mem p.asIdeal.primeCompl fun i _ ↦ (t i).2)
  have hg₂ : g₂ ∉ p.asIdeal := hg₂_compl
  refine ⟨g₂, hg₂, ?_⟩
  intro i
  let u : p.asIdeal.primeCompl := (Finset.univ.erase i).prod t
  have hg₂_split : g₂ = t i * u := by
    -- Split the common product into the `i`-th factor and the complementary product.
    symm
    simpa [g₂, u] using
      (Finset.mul_prod_erase (s := Finset.univ) (a := i) (f := fun j : Fin n ↦ (t j : R))
        (by simp))
  have hkill_g₂ :
      algebraMap R S g₂ * a i = 0 := by
    calc
      algebraMap R S g₂ * a i
          = (algebraMap R S (t i) * algebraMap R S (u : R)) * a i := by
              rw [hg₂_split, map_mul]
      _ = algebraMap R S (u : R) * (algebraMap R S (t i) * a i) := by ring
      _ = 0 := by simp [ht i]
  have hmap_kill :
      algebraMap S (Localization.Away (algebraMap R S g₁))
        (algebraMap R S g₂) * algebraMap S (Localization.Away (algebraMap R S g₁)) (a i) = 0 := by
    simpa [map_mul, mul_comm] using congrArg
      (algebraMap S (Localization.Away (algebraMap R S g₁))) hkill_g₂
  have hg₁_unit :
      IsUnit (algebraMap R (Localization.Away (algebraMap R S g₁)) g₁) := by
    simpa [IsScalarTower.algebraMap_eq R S (Localization.Away (algebraMap R S g₁))] using
      (IsLocalization.Away.algebraMap_isUnit
        (R := S) (S := Localization.Away (algebraMap R S g₁)) (x := algebraMap R S g₁))
  -- Cancel the invertible `g₁`-power from the denominator-cleared relation.
  have haux :
      (algebraMap R (Localization.Away (algebraMap R S g₁)) g₂ * z i) *
        algebraMap R (Localization.Away (algebraMap R S g₁)) g₁ ^ e i = 0 := by
    have ha' :
        z i * algebraMap R (Localization.Away (algebraMap R S g₁)) g₁ ^ e i =
          algebraMap S (Localization.Away (algebraMap R S g₁)) (a i) := by
      simpa [IsScalarTower.algebraMap_eq R S (Localization.Away (algebraMap R S g₁))] using
        ha i
    calc
      (algebraMap R (Localization.Away (algebraMap R S g₁)) g₂ * z i) *
          algebraMap R (Localization.Away (algebraMap R S g₁)) g₁ ^ e i
          =
        algebraMap R (Localization.Away (algebraMap R S g₁)) g₂ *
          (z i * algebraMap R (Localization.Away (algebraMap R S g₁)) g₁ ^ e i) := by
            ring
      _ =
        algebraMap S (Localization.Away (algebraMap R S g₁))
          (algebraMap R S g₂) *
          algebraMap S (Localization.Away (algebraMap R S g₁)) (a i) := by
            rw [ha']
            simp [IsScalarTower.algebraMap_eq R S (Localization.Away (algebraMap R S g₁))]
      _ = 0 := hmap_kill
  exact (IsUnit.mul_left_eq_zero (hg₁_unit.pow _)).mp haux

/-- Helper for Lemma 10.122.11: after the first denominator-clearing step in `S[1 / g₁]`,
localizing once more away from `g₂ ∉ p` makes the whole family literally vanish in
`S[1 / (g₁ * g₂)]`. -/
lemma awayToAwayRight_eq_zero_of_mul_eq_zero
    {g₁ g₂ : R} {z : Localization.Away (algebraMap R S g₁)}
    (hz : algebraMap R (Localization.Away (algebraMap R S g₁)) g₂ * z = 0) :
    let B := Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂))
    let ρS : Localization.Away (algebraMap R S g₁) →+* B :=
      IsLocalization.Away.awayToAwayRight
        (P := B) (algebraMap R S g₁) (algebraMap R S g₂)
    ρS z = 0 := by
  intro B ρS
  have hmap : ρS (algebraMap R (Localization.Away (algebraMap R S g₁)) g₂) * ρS z = 0 := by
    simpa [map_mul] using congrArg ρS hz
  have hρg₂ :
      ρS (algebraMap R (Localization.Away (algebraMap R S g₁)) g₂) =
        algebraMap S B (algebraMap R S g₂) := by
    -- Rewrite the transported scalar into the obvious image of `g₂` in the second localization.
    rw [show algebraMap R (Localization.Away (algebraMap R S g₁)) g₂ =
        algebraMap S (Localization.Away (algebraMap R S g₁)) (algebraMap R S g₂) by
          simp [IsScalarTower.algebraMap_eq R S (Localization.Away (algebraMap R S g₁))]]
    simpa [ρS] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away (algebraMap R S g₁))
        (P := B) (x := algebraMap R S g₁) (y := algebraMap R S g₂)
        (a := algebraMap R S g₂))
  have hunit : IsUnit (ρS (algebraMap R (Localization.Away (algebraMap R S g₁)) g₂)) := by
    rw [hρg₂]
    exact IsLocalization.Away.isUnit_of_dvd
      (R := S) (S := B) (x := (algebraMap R S g₁) * (algebraMap R S g₂))
      (by
        refine ⟨algebraMap R S g₁, ?_⟩
        simp [mul_comm, mul_left_comm, mul_assoc])
  -- Cancel the invertible image of `g₂` after mapping to the second away-localization.
  exact (IsUnit.mul_right_eq_zero hunit).mp hmap

/-- Helper for Lemma 10.122.11: after the first denominator-clearing step in `S[1 / g₁]`,
localizing once more away from `g₂ ∉ p` makes the whole family literally vanish in
`S[1 / (g₁ * g₂)]`. -/
lemma exists_notMem_zero_family_away_of_zero_in_semilocal_localization
    (p : PrimeSpectrum R) {n : ℕ} {g₁ : R} (hg₁ : g₁ ∉ p.asIdeal)
    (z : Fin n → Localization.Away (algebraMap R S g₁))
    (hz :
      let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
      let ψ : Localization.Away (algebraMap R S g₁) →+* Sp :=
        Localization.awayLift (algebraMap S Sp) (algebraMap R S g₁)
          (semilocal_image_isUnit_of_notMem (R := R) (S := S) p hg₁)
      ∀ i, ψ (z i) = 0) :
    ∃ g₂ : R, g₂ ∉ p.asIdeal ∧
      let B := Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂))
      let ρS : Localization.Away (algebraMap R S g₁) →+* B :=
        IsLocalization.Away.awayToAwayRight
          (P := B) (algebraMap R S g₁) (algebraMap R S g₂)
      ∀ i, ρS (z i) = 0 := by
  obtain ⟨g₂, hg₂, hkill⟩ :=
    exists_notMem_zero_family_of_zero_in_semilocal_localization
      (R := R) (S := S) p hg₁ z hz
  refine ⟨g₂, hg₂, ?_⟩
  intro B ρS i
  -- Map the annihilating relation to `S[1 / (g₁ * g₂)]` and cancel the now-invertible image of `g₂`.
  exact awayToAwayRight_eq_zero_of_mul_eq_zero
    (R := R) (S := S) (g₁ := g₁) (g₂ := g₂) (z := z i) (hkill i)

/-- Helper for Lemma 10.122.11: once the away-map localization is installed as the local algebra
structure, its underlying ring hom is literally the corresponding `algebraMap`. -/
lemma awayMap_eq_algebraMap
    {g : R} :
    let S₁ := Localization.Away (algebraMap R S g)
    let σ : Localization.Away g →+* S₁ := Localization.awayMap (algebraMap R S) g
    letI : Algebra (Localization.Away g) S₁ := σ.toAlgebra
    σ = algebraMap (Localization.Away g) S₁ := by
  intro S₁ σ
  -- This is exactly the `toAlgebra` packaging of the away map.
  change σ = @algebraMap (Localization.Away g) S₁ _ _ σ.toAlgebra
  symm
  exact RingHom.algebraMap_toAlgebra σ

/-- Helper for Lemma 10.122.11: for the second localization, the away map
`R[1 / (g₁ * g₂)] → B` is the installed scalar map whenever `B` localizes `S` away from the
image of `g₁ * g₂`. -/
lemma awayMap_mul_eq_algebraMap
    {g₁ g₂ : R} {B : Type v} [CommRing B] [Algebra S B]
    [IsLocalization.Away (algebraMap R S (g₁ * g₂)) B]
    (τ : Localization.Away (g₁ * g₂) →+* B) :
    letI : Algebra (Localization.Away (g₁ * g₂)) B := τ.toAlgebra
    τ = algebraMap (Localization.Away (g₁ * g₂)) B := by
  -- This is the same `toAlgebra` packaging as in the one-step away-map lemma.
  symm
  exact RingHom.algebraMap_toAlgebra τ

/-- Helper for Lemma 10.122.11: the two scalar-tower routes from `R` to the semilocal
localization `S_p` agree on coefficients. -/
lemma semilocal_base_image_eq
    (p : PrimeSpectrum R) (r : R) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    (algebraMap Rp Sp) (algebraMap R Rp r) = (algebraMap S Sp) (algebraMap R S r) := by
  intro Rp Sp
  -- Both routes are the same scalar-tower image of `r` in `S_p`.
  calc
    (algebraMap Rp Sp) (algebraMap R Rp r) = algebraMap R Sp r := by
      simp [IsScalarTower.algebraMap_eq R Rp Sp]
    _ = (algebraMap S Sp) (algebraMap R S r) := by
      simp [IsScalarTower.algebraMap_eq R S Sp]

/-- Helper for Lemma 10.122.11: the second-localization square between `R` and `S` is compatible
with the corresponding away maps. -/
lemma awayToAwayRight_comp_awayMap_eq_awayMap_comp_awayToAwayRight
    {g₁ g₂ : R} :
    ∃ ρS : Localization.Away (algebraMap R S g₁) →+*
        Localization.Away (algebraMap R S (g₁ * g₂)),
      ρS.comp (Localization.awayMap (algebraMap R S) g₁) =
        (Localization.awayMap (algebraMap R S) (g₁ * g₂)).comp
          (IsLocalization.Away.awayToAwayRight
            (P := Localization.Away (g₁ * g₂)) g₁ g₂) := by
  let S₁ := Localization.Away (algebraMap R S g₁)
  let B := Localization.Away (algebraMap R S (g₁ * g₂))
  let σ : Localization.Away g₁ →+* S₁ := Localization.awayMap (algebraMap R S) g₁
  let τ : Localization.Away (g₁ * g₂) →+* B := Localization.awayMap (algebraMap R S) (g₁ * g₂)
  letI : Algebra (Localization.Away g₁) S₁ := σ.toAlgebra
  letI : Algebra (Localization.Away (g₁ * g₂)) B := τ.toAlgebra
  letI : IsScalarTower R (Localization.Away g₁) S₁ :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using
        ((Localization.awayMapₐ (Algebra.ofId R S) g₁).commutes r).symm
  letI : IsScalarTower R (Localization.Away (g₁ * g₂)) B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using
        ((Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).commutes r).symm
  letI : IsLocalization.Away ((algebraMap R S g₁) * (algebraMap R S g₂))
      B := by
    simpa [map_mul] using
      (inferInstance : IsLocalization.Away (algebraMap R S (g₁ * g₂)) B)
  let ρS : S₁ →+* B :=
    IsLocalization.Away.awayToAwayRight
      (P := B)
      (algebraMap R S g₁) (algebraMap R S g₂)
  have hσ : σ = algebraMap (Localization.Away g₁) S₁ := by
    symm
    exact RingHom.algebraMap_toAlgebra σ
  have hτ : τ = algebraMap (Localization.Away (g₁ * g₂)) B := by
    symm
    exact RingHom.algebraMap_toAlgebra τ
  refine ⟨ρS, ?_⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
  ext r
  calc
    ρS (σ (algebraMap R (Localization.Away g₁) r))
        = ρS ((algebraMap (Localization.Away g₁) S₁) (algebraMap R (Localization.Away g₁) r)) := by
            rw [hσ]
    _ = ρS ((algebraMap S S₁) (algebraMap R S r)) := by
          congr 1
          calc
            (algebraMap (Localization.Away g₁) S₁) (algebraMap R (Localization.Away g₁) r)
                = algebraMap R S₁ r := by
                    simpa using
                      (DFunLike.congr_fun
                        (IsScalarTower.algebraMap_eq R (Localization.Away g₁) S₁) r).symm
            _ = (algebraMap S S₁) (algebraMap R S r) := by
                  simpa using DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S S₁) r
    _ = (algebraMap S B) (algebraMap R S r) := by
          simpa [ρS] using
            (IsLocalization.Away.awayToAwayRight_eq
              (S := S₁)
              (P := B)
              (x := algebraMap R S g₁) (y := algebraMap R S g₂)
              (a := algebraMap R S r))
    _ = τ (algebraMap R (Localization.Away (g₁ * g₂)) r) := by
          rw [hτ]
          calc
            (algebraMap S B) (algebraMap R S r) = algebraMap R B r := by
              simpa using (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S B) r).symm
            _ = (algebraMap (Localization.Away (g₁ * g₂)) B)
                (algebraMap R (Localization.Away (g₁ * g₂)) r) := by
                  simpa using
                    DFunLike.congr_fun
                      (IsScalarTower.algebraMap_eq R (Localization.Away (g₁ * g₂)) B) r
    _ = τ
          ((IsLocalization.Away.awayToAwayRight
            (P := Localization.Away (g₁ * g₂)) g₁ g₂)
            (algebraMap R (Localization.Away g₁) r)) := by
          rw [show (IsLocalization.Away.awayToAwayRight
              (P := Localization.Away (g₁ * g₂)) g₁ g₂)
              (algebraMap R (Localization.Away g₁) r) =
              algebraMap R (Localization.Away (g₁ * g₂)) r by
                simpa using
                  (IsLocalization.Away.awayToAwayRight_eq
                    (S := Localization.Away g₁) (P := Localization.Away (g₁ * g₂))
                    (x := g₁) (y := g₂) (a := r))]

/-- Helper for Lemma 10.122.11: a descended monic zero relation after the second localization
should yield integrality of the image generator over `R[1 / (g₁ * g₂)]`. -/
lemma isIntegral_generator_image_of_monic_zero_relation_after_second_localization
    {g₁ g₂ : R} (x : S) {Q : (Localization.Away g₁)[X]} (hQmonic : Q.Monic)
    (hQzero :
      let ρS : Localization.Away (algebraMap R S g₁) →+*
          Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂)) :=
        IsLocalization.Away.awayToAwayRight
          (P := Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂)))
          (algebraMap R S g₁) (algebraMap R S g₂)
      let σ : Localization.Away g₁ →+* Localization.Away (algebraMap R S g₁) :=
        Localization.awayMap (algebraMap R S) g₁
      ρS (Polynomial.eval₂ σ
        (algebraMap S (Localization.Away (algebraMap R S g₁)) x) Q) = 0) :
    ((Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).toRingHom).IsIntegralElem
      (algebraMap S (Localization.Away (algebraMap R S (g₁ * g₂))) x) := by
  let S₁ := Localization.Away (algebraMap R S g₁)
  let B := Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂))
  let B' := Localization.Away (algebraMap R S (g₁ * g₂))
  let ρS : Localization.Away (algebraMap R S g₁) →+*
      Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂)) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂)))
      (algebraMap R S g₁) (algebraMap R S g₂)
  let σ : Localization.Away g₁ →+* Localization.Away (algebraMap R S g₁) :=
    Localization.awayMap (algebraMap R S) g₁
  letI : Algebra (Localization.Away g₁) S₁ := σ.toAlgebra
  letI : IsScalarTower R (Localization.Away g₁) S₁ :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using
        ((Localization.awayMapₐ (Algebra.ofId R S) g₁).commutes r).symm
  have hσ : σ = algebraMap (Localization.Away g₁) S₁ := by
    symm
    exact RingHom.algebraMap_toAlgebra σ
  have hQzero'base :
      ρS (Polynomial.eval₂ σ (algebraMap S S₁ x) Q) = 0 := by
    simpa [S₁, B, ρS, σ] using hQzero
  letI : IsLocalization.Away (algebraMap R S (g₁ * g₂))
      (Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂))) := by
    simpa [map_mul] using
      (inferInstance :
        IsLocalization.Away ((algebraMap R S g₁) * (algebraMap R S g₂))
          (Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂))))
  let e : B ≃ₐ[S] B' :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (g₁ * g₂)))
      B B'
  let ρS' : S₁ →+* B' := (e : B →+* B').comp ρS
  let ρR : Localization.Away g₁ →+* Localization.Away (g₁ * g₂) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (g₁ * g₂)) g₁ g₂
  let τ : Localization.Away (g₁ * g₂) →+* B' := Localization.awayMap (algebraMap R S) (g₁ * g₂)
  letI : Algebra (Localization.Away (g₁ * g₂)) B' := τ.toAlgebra
  letI : IsScalarTower R (Localization.Away (g₁ * g₂)) B' :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using
        ((Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).commutes r).symm
  have hτ : τ = algebraMap (Localization.Away (g₁ * g₂)) B' := by
    symm
    exact RingHom.algebraMap_toAlgebra τ
  have hcomp : ρS'.comp σ = τ.comp ρR := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
    ext r
    calc
      ρS' (σ (algebraMap R (Localization.Away g₁) r))
          = ρS' ((algebraMap (Localization.Away g₁) S₁) (algebraMap R (Localization.Away g₁) r)) := by
              rw [hσ]
      _ = ρS' ((algebraMap S S₁) (algebraMap R S r)) := by
            congr 1
            calc
              (algebraMap (Localization.Away g₁) S₁) (algebraMap R (Localization.Away g₁) r)
                  = algebraMap R S₁ r := by
                      simpa using
                        (DFunLike.congr_fun
                          (IsScalarTower.algebraMap_eq R (Localization.Away g₁) S₁) r).symm
              _ = (algebraMap S S₁) (algebraMap R S r) := by
                    simpa using DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S S₁) r
      _ = (algebraMap S B') (algebraMap R S r) := by
            change e (ρS ((algebraMap S S₁) (algebraMap R S r))) =
              (algebraMap S B') (algebraMap R S r)
            rw [show ρS (algebraMap S S₁ (algebraMap R S r)) =
                (algebraMap S B) (algebraMap R S r) by
                  simpa [ρS] using
                    (IsLocalization.Away.awayToAwayRight_eq
                      (S := S₁)
                      (P := B)
                      (x := algebraMap R S g₁)
                      (y := algebraMap R S g₂) (a := algebraMap R S r))]
            exact e.commutes (algebraMap R S r)
      _ = τ (algebraMap R (Localization.Away (g₁ * g₂)) r) := by
            rw [hτ]
            calc
              (algebraMap S B') (algebraMap R S r) = algebraMap R B' r := by
                simpa using (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S B') r).symm
              _ = (algebraMap (Localization.Away (g₁ * g₂)) B')
                  (algebraMap R (Localization.Away (g₁ * g₂)) r) := by
                    simpa using
                      DFunLike.congr_fun
                        (IsScalarTower.algebraMap_eq R (Localization.Away (g₁ * g₂)) B') r
      _ = τ (ρR (algebraMap R (Localization.Away g₁) r)) := by
            rw [show ρR (algebraMap R (Localization.Away g₁) r) =
                algebraMap R (Localization.Away (g₁ * g₂)) r by
                  simpa [ρR] using
                    (IsLocalization.Away.awayToAwayRight_eq
                      (S := Localization.Away g₁) (P := Localization.Away (g₁ * g₂))
                      (x := g₁) (y := g₂) (a := r))]
  have hQzero' :
      ρS' (Polynomial.eval₂ σ (algebraMap S S₁ x) Q) = 0 := by
    simpa [ρS'] using congrArg (e : B →+* B') hQzero'base
  have hcomp' :
      (algebraMap (Localization.Away (g₁ * g₂)) B').comp ρR =
        ρS'.comp (algebraMap (Localization.Away g₁) S₁) := by
    simpa [hσ, hτ]
      using hcomp.symm
  have hQzero'' :
      ρS' (Polynomial.aeval (algebraMap S S₁ x) Q) = 0 := by
    simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hQzero'
  have hx :
      ρS' (algebraMap S S₁ x) = algebraMap S B' x := by
    change e (ρS (algebraMap S S₁ x)) = algebraMap S B' x
    rw [show ρS (algebraMap S S₁ x) = algebraMap S B x by
          simpa [ρS] using
            (IsLocalization.Away.awayToAwayRight_eq
              (S := S₁) (P := B) (x := algebraMap R S g₁) (y := algebraMap R S g₂)
              (a := x))]
    simpa using e.commutes x
  refine ⟨Polynomial.map ρR Q, hQmonic.map ρR, ?_⟩
  calc
    Polynomial.aeval (algebraMap S B' x) (Polynomial.map ρR Q)
        = Polynomial.aeval (ρS' (algebraMap S S₁ x)) (Polynomial.map ρR Q) := by
            rw [hx]
    _ = ρS' (Polynomial.aeval (algebraMap S S₁ x) Q) := by
          symm
          exact Polynomial.map_aeval_eq_aeval_map hcomp' Q (algebraMap S S₁ x)
    _ = 0 := hQzero''

/-- Helper for Lemma 10.122.11: the two routes from `R[1 / g₁]` to the semilocal localization
`S_p` agree, either by first passing through `R_p` or by first localizing `S`. -/
lemma awayLift_comp_algebraMap_eq_semilocal_map
    (p : PrimeSpectrum R) {g₁ : R} (hg₁ : g₁ ∉ p.asIdeal) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let S₁ := Localization.Away (algebraMap R S g₁)
    let lift : Localization.Away g₁ →+* Rp :=
      Localization.awayLift (algebraMap R Rp) g₁
        ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal g₁).2 hg₁)
    letI : Algebra (Localization.Away g₁) S₁ :=
      (Localization.awayMapₐ (Algebra.ofId R S) g₁).toAlgebra
    let ψ : S₁ →+* Sp :=
      Localization.awayLift (algebraMap S Sp) (algebraMap R S g₁)
        (semilocal_image_isUnit_of_notMem (R := R) (S := S) p hg₁)
    (algebraMap Rp Sp).comp lift = ψ.comp (algebraMap (Localization.Away g₁) S₁) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let S₁ := Localization.Away (algebraMap R S g₁)
  let lift : Localization.Away g₁ →+* Rp :=
    Localization.awayLift (algebraMap R Rp) g₁
      ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal g₁).2 hg₁)
  letI : Algebra (Localization.Away g₁) S₁ :=
    (Localization.awayMapₐ (Algebra.ofId R S) g₁).toAlgebra
  letI : IsScalarTower R (Localization.Away g₁) S₁ :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using
        ((Localization.awayMapₐ (Algebra.ofId R S) g₁).commutes r).symm
  let ψ : S₁ →+* Sp :=
    Localization.awayLift (algebraMap S Sp) (algebraMap R S g₁)
      (semilocal_image_isUnit_of_notMem (R := R) (S := S) p hg₁)
  suffices
      (algebraMap Rp Sp).comp lift = ψ.comp (algebraMap (Localization.Away g₁) S₁) by
    simpa [Rp, Sp, S₁, lift, ψ]
  apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
  ext r
  calc
    ((algebraMap Rp Sp).comp lift) (algebraMap R (Localization.Away g₁) r)
        = (algebraMap Rp Sp) (algebraMap R Rp r) := by
            simp [lift, Localization.awayLift]
    _ = (algebraMap S Sp) (algebraMap R S r) := by
          simpa [Rp, Sp] using semilocal_base_image_eq (R := R) (S := S) p r
    _ = ψ (algebraMap S S₁ (algebraMap R S r)) := by
          simp [ψ, Localization.awayLift]
    _ = (ψ.comp (algebraMap (Localization.Away g₁) S₁))
          (algebraMap R (Localization.Away g₁) r) := by
          rw [RingHom.comp_apply]
          congr 1
          calc
            (algebraMap S S₁) (algebraMap R S r) = algebraMap R S₁ r := by
              simpa using (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S S₁) r).symm
            _ = (algebraMap (Localization.Away g₁) S₁)
                (algebraMap R (Localization.Away g₁) r) := by
                  simpa using
                    DFunLike.congr_fun (IsScalarTower.algebraMap_eq R (Localization.Away g₁) S₁) r

/-- Helper for Lemma 10.122.11: the semilocal away-lift turns the first localized `aeval` into
the corresponding mapped polynomial evaluation in `S_p`. -/
lemma awayLift_aeval_eq_map_aeval
    (p : PrimeSpectrum R) {g₁ : R} (hg₁ : g₁ ∉ p.asIdeal)
    {x : S} {Q : (Localization.Away g₁)[X]} :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    let S₁ := Localization.Away (algebraMap R S g₁)
    let lift : Localization.Away g₁ →+* Rp :=
      Localization.awayLift (algebraMap R Rp) g₁
        ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal g₁).2 hg₁)
    letI : Algebra (Localization.Away g₁) S₁ :=
      (Localization.awayMapₐ (Algebra.ofId R S) g₁).toAlgebra
    let ψ : S₁ →+* Sp :=
      Localization.awayLift (algebraMap S Sp) (algebraMap R S g₁)
        (semilocal_image_isUnit_of_notMem (R := R) (S := S) p hg₁)
    let φ : Localization.Away g₁ →+* Sp := (algebraMap Rp Sp).comp lift
    ψ (Polynomial.eval₂ (Localization.awayMap (algebraMap R S) g₁) (algebraMap S S₁ x) Q) =
      Polynomial.aeval (algebraMap S Sp x) (Polynomial.map φ Q) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let S₁ := Localization.Away (algebraMap R S g₁)
  let lift : Localization.Away g₁ →+* Rp :=
    Localization.awayLift (algebraMap R Rp) g₁
      ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal g₁).2 hg₁)
  letI : Algebra (Localization.Away g₁) S₁ :=
    (Localization.awayMapₐ (Algebra.ofId R S) g₁).toAlgebra
  let ψ : S₁ →+* Sp :=
    Localization.awayLift (algebraMap S Sp) (algebraMap R S g₁)
      (semilocal_image_isUnit_of_notMem (R := R) (S := S) p hg₁)
  let φ : Localization.Away g₁ →+* Sp := (algebraMap Rp Sp).comp lift
  suffices
      ψ (Polynomial.eval₂ (Localization.awayMap (algebraMap R S) g₁) (algebraMap S S₁ x) Q) =
        Polynomial.aeval (algebraMap S Sp x) (Polynomial.map φ Q) by
    simpa [Rp, Sp, S₁, lift, ψ, φ]
  let σ : Localization.Away g₁ →+* S₁ := Localization.awayMap (algebraMap R S) g₁
  letI : Algebra (Localization.Away g₁) S₁ := σ.toAlgebra
  have hcomp :
      (algebraMap Sp Sp).comp φ = ψ.comp (algebraMap (Localization.Away g₁) S₁) := by
    simpa [φ] using
      awayLift_comp_algebraMap_eq_semilocal_map
        (R := R) (S := S) (p := p) (g₁ := g₁) hg₁
  have hmap :=
    Polynomial.map_aeval_eq_aeval_map hcomp Q (algebraMap S S₁ x)
  simpa [σ, Polynomial.aeval_def, RingHom.algebraMap_toAlgebra, ψ, Localization.awayLift,
    IsScalarTower.algebraMap_eq R S S₁] using hmap

/-- Helper for Lemma 10.122.11: the localization generator over `S` is the image of the base
inverse under the canonical away map `R_g → S_g`. -/
lemma localizationAway_generator_eq_awayMap_invSelf_image
    {g : R} :
    let Sg := Localization.Away (algebraMap R S g)
    (Algebra.Generators.localizationAway (R := S) (S := Sg) (algebraMap R S g)).val () =
      Localization.awayMap (algebraMap R S) g (IsLocalization.Away.invSelf g) := by
  -- The canonical localization generator is definitionally the inverse of the image of `g`.
  simp [Algebra.Generators.localizationAway, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.Away.invSelf, IsLocalization.map_mk']

/-- Helper for Lemma 10.122.11: after viewing `S_g` as an `R_g`-algebra, the localization
generator over `S` is the image of `g⁻¹` from the localized base ring. -/
lemma localizationAway_generator_eq_base_invSelf_image
    {g : R} :
    let Sg := Localization.Away (algebraMap R S g)
    letI : Algebra (Localization.Away g) Sg :=
      (Localization.awayMapₐ (Algebra.ofId R S) g).toAlgebra
    (Algebra.Generators.localizationAway (R := S) (S := Sg) (algebraMap R S g)).val () =
      algebraMap (Localization.Away g) Sg (IsLocalization.Away.invSelf g) := by
  -- Rewrite the away-map presentation as the `algebraMap` coming from `Localization.awayMapₐ`.
  simpa [RingHom.algebraMap_toAlgebra] using
    (localizationAway_generator_eq_awayMap_invSelf_image (R := R) (S := S) (g := g))

/-- Helper for Lemma 10.122.11: if the original finite-type generators become integral after
localizing away from `g`, then the canonical localized generator package makes the whole
localized algebra integral over the localized base. -/
lemma localized_generator_family_integral
    {n : ℕ} {g : R} (P : Algebra.Generators R S (Fin n))
    (hP : ∀ i,
      ((Localization.awayMapₐ (Algebra.ofId R S) g).toRingHom).IsIntegralElem
        (algebraMap S (Localization.Away (algebraMap R S g)) (P.val i))) :
    ((Localization.awayMapₐ (Algebra.ofId R S) g).toRingHom).IsIntegral := by
  let Sg := Localization.Away (algebraMap R S g)
  letI : Algebra (Localization.Away g) Sg :=
    (Localization.awayMapₐ (Algebra.ofId R S) g).toAlgebra
  letI : IsScalarTower R (Localization.Away g) Sg :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := Localization.Away g) (A := Sg) fun r ↦ by
      -- The localized comparison map extends the original map `R → S_g`.
      simpa [RingHom.algebraMap_toAlgebra] using
        ((Localization.awayMapₐ (Algebra.ofId R S) g).commutes r).symm
  let Q : Algebra.Generators S Sg Unit :=
    Algebra.Generators.localizationAway (R := S) (S := Sg) (algebraMap R S g)
  let Pg : Algebra.Generators (Localization.Away g) Sg (Unit ⊕ Fin n) :=
    (Q.comp P).extendScalars (Localization.Away g)
  have hPg : ∀ j, IsIntegral (Localization.Away g) (Pg.val j) := by
    intro j
    cases j with
    | inl u =>
        cases u
        -- The extra localization generator already comes from the localized base ring.
        have hunit :
            Pg.val (Sum.inl ()) =
              algebraMap (Localization.Away g) Sg (IsLocalization.Away.invSelf g) := by
          simpa [Pg, Q] using
            (localizationAway_generator_eq_base_invSelf_image
              (R := R) (S := S) (g := g))
        rw [hunit]
        exact isIntegral_algebraMap (R := Localization.Away g) (A := Sg)
    | inr i =>
        -- The original chosen generators are integral by hypothesis after localization.
        simpa [Pg, Q, RingHom.IsIntegralElem, IsIntegral, RingHom.algebraMap_toAlgebra] using hP i
  have hInt : Algebra.IsIntegral (Localization.Away g) Sg :=
    isIntegral_of_integral_generators Pg hPg
  letI : Algebra.IsIntegral (Localization.Away g) Sg := hInt
  -- Convert the algebra-form integral statement back to the canonical localized ring-hom form.
  intro x
  simpa [RingHom.IsIntegralElem, IsIntegral, RingHom.algebraMap_toAlgebra] using
    (Algebra.IsIntegral.isIntegral (R := Localization.Away g) (A := Sg) x)

/- Domain triage:
* primary domain: primes of a finite type algebra lying over a fixed minimal prime;
* source-facing layer: the existence of `g ∉ p` making the localization `R_g → S_g` finite;
* core/canonical owner sampled for the finite fiber hypothesis: `Ideal.primesOver`;
* bridge/view relating the textbook fiber of `Spec(S) → Spec(R)` to that owner set:
  `PrimeSpectrum.primesOverOrderIsoFiber`.

Primitive data are `R`, `S`, the minimal prime `p`, and the canonical owner set
`p.asIdeal.primesOver S`. The finiteness hypothesis belongs on that owner set rather than on the
parallel raw subtype of `Spec(S)` points over `p`. -/

-- Proof sketch: by Lemma `10.122.4`, the finite-over-`p` hypothesis implies that the fiber
-- algebra `S ⊗[R] κ(p)` is finite over `κ(p)`, so a finite set of `R`-algebra generators of `S`
-- satisfies monic relations modulo `p`. Since `p` is minimal, Lemmas `10.25.1` and `10.32.3`
-- make the extended ideal `pS_p` locally nilpotent, so powers of those relations vanish in
-- `S_p`. Clearing denominators away from a suitable element `g ∉ p` then makes each generator
-- integral over `R_g`, and a finite type integral algebra is finite.
/-- Lemma 10.122.11: if `R → S` is of finite type, `p` is a minimal prime of `R`, and only
finitely many primes of `S` lie over `p`, then there exists `g ∈ R \ p` such that the localized
map `R_g → S_g` is finite. -/
theorem exists_notMem_and_away_finite_of_finite_primesOver_minimalPrime
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (hfinite : Finite (p.asIdeal.primesOver S)) :
    ∃ g : R, g ∉ p.asIdeal ∧ (Localization.awayMapₐ (Algebra.ofId R S) g).Finite := by
  -- The verified prefix is the source-faithful reduction to quasi-finiteness on the whole fiber.
  have hqf :
      ∀ q : PrimeSpectrum S,
        PrimeSpectrum.comap (algebraMap R S) q = p → Algebra.QuasiFiniteAt R q.asIdeal :=
    quasiFiniteAt_of_finite_primesOver (R := R) (S := S) p hfinite
  -- Next upgrade the fiberwise quasi-finiteness statement to actual finiteness of the fiber algebra.
  have hfiber : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    moduleFinite_fiber_of_finite_primesOver (R := R) (S := S) p hfinite
  -- Choose a finite generating family of `S` over `R`; these are the textbook generators `x_i`.
  obtain ⟨n, ⟨P⟩⟩ :=
    (Algebra.FiniteType.iff_exists_generators (R := R) (S := S)).mp inferInstance
  -- Each generator is integral in the fiber algebra, which is the starting point for the monic
  -- relations modulo `pS_p`.
  have h_integral_generator (i : Fin n) :
      IsIntegral p.asIdeal.ResidueField (1 ⊗ₜ[R] P.val i : p.asIdeal.Fiber S) := by
    let _ : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := hfiber
    exact isIntegral_tmul_right_of_moduleFinite_fiber (R := R) (S := S) p (P.val i)
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let pSp : Ideal Sp :=
    Ideal.map (algebraMap Rp Sp) (IsLocalRing.maximalIdeal Rp)
  letI : Algebra p.asIdeal.ResidueField (Sp ⧸ pSp) :=
    (localized_quotient_residueFieldAlgHom (R := R) (S := S) p).toAlgebra
  have hpSp :
      Ideal.map (algebraMap R Sp) p.asIdeal = pSp := by
    simpa [Rp, Sp, pSp] using map_prime_to_semilocal_ideal_eq_pSp (R := R) (S := S) p
  let φ : p.asIdeal.Fiber S →ₐ[R] Sp ⧸ pSp := by
    simpa [Rp, Sp, pSp] using fiber_to_localized_quotient_algHom p
  have hφ_generator (i : Fin n) :
      φ (1 ⊗ₜ[R] P.val i) = Ideal.Quotient.mk pSp (algebraMap S Sp (P.val i)) := by
    simpa [Rp, Sp, pSp] using fiber_to_localized_quotient_algHom_tmul p (P.val i)
  have hφ_scalars :
      φ.comp (Algebra.TensorProduct.includeLeft : p.asIdeal.ResidueField →ₐ[R] p.asIdeal.Fiber S) =
        localized_quotient_residueFieldAlgHom (R := R) (S := S) p := by
    -- This isolates the transport from the fiber scalars to the localized quotient scalars.
    simpa [Rp, Sp, pSp, φ] using
      fiber_to_localized_quotient_comp_includeLeft (R := R) (S := S) p
  have h_integral_quotient_generator (i : Fin n) :
      IsIntegral p.asIdeal.ResidueField
        (Ideal.Quotient.mk pSp (algebraMap S Sp (P.val i))) := by
    -- Route correction: the fiber-integral generators are now transported to `S_p / pS_p`
    -- before any coefficient lifting or denominator clearing is attempted.
    simpa [Rp, Sp, pSp] using
      isIntegral_quotient_class_of_isIntegral_fiber
        (R := R) (S := S) p (P.val i) (h_integral_generator i)
  have h_zero_relation_generator (i : Fin n) :
      ∃ Q : Rp[X], Q.Monic ∧ Polynomial.aeval (algebraMap S Sp (P.val i)) Q = 0 := by
    -- This is the source-proof local-nilpotence step for the chosen generator family.
    simpa [Rp, Sp, pSp] using
      exists_monic_zero_relation_in_semilocal_localization_of_isIntegral_fiber
        (R := R) (S := S) p hp (P.val i) (h_integral_generator i)
  choose Q hQmonic hQzero using h_zero_relation_generator
  obtain ⟨g₁, hg₁, Q₁, hQ₁monic, hQ₁map⟩ :=
    exists_notMem_monic_lift_family_from_localizationAtPrime
      (R := R) p Q hQmonic
  let lift : Localization.Away g₁ →+* Rp :=
    Localization.awayLift (algebraMap R Rp) g₁
      ((IsLocalization.AtPrime.isUnit_to_map_iff Rp p.asIdeal g₁).2 hg₁)
  let S₁ := Localization.Away (algebraMap R S g₁)
  letI : Algebra (Localization.Away g₁) S₁ :=
    (Localization.awayMapₐ (Algebra.ofId R S) g₁).toAlgebra
  let z : Fin n → S₁ := fun i ↦
    Polynomial.aeval (algebraMap S S₁ (P.val i)) (Q₁ i)
  have h_eval_in_semilocal (i : Fin n) :
      let φ : Localization.Away g₁ →+* Sp := (algebraMap Rp Sp).comp lift
      Polynomial.aeval (algebraMap S Sp (P.val i)) (Polynomial.map φ (Q₁ i)) = 0 := by
    intro φ
    have hmap :
        Polynomial.map φ (Q₁ i) = Polynomial.map (algebraMap Rp Sp) (Q i) := by
      -- Push the coefficient lift forward from `R[1 / g₁]` to the semilocal target `S_p`.
      calc
        Polynomial.map φ (Q₁ i)
            = Polynomial.map (algebraMap Rp Sp) (Polynomial.map lift (Q₁ i)) := by
                simp [φ, Polynomial.map_map]
        _ = Polynomial.map (algebraMap Rp Sp) (Q i) := by
              rw [hQ₁map i]
    calc
      Polynomial.aeval (algebraMap S Sp (P.val i)) (Polynomial.map φ (Q₁ i))
          = Polynomial.aeval (algebraMap S Sp (P.val i))
              (Polynomial.map (algebraMap Rp Sp) (Q i)) := by
                rw [hmap]
      _ = Polynomial.aeval (algebraMap S Sp (P.val i)) (Q i) := by
            rw [Polynomial.aeval_map_algebraMap]
      _ = 0 := hQzero i
  have hz_semilocal :
      let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
      let ψ : Localization.Away (algebraMap R S g₁) →+* Sp :=
        Localization.awayLift (algebraMap S Sp) (algebraMap R S g₁)
          (semilocal_image_isUnit_of_notMem (R := R) (S := S) p hg₁)
      ∀ i, ψ (z i) = 0 := by
    intro Sp ψ i
    -- Route correction: rewrite the semilocal image of the descended polynomial as a literal
    -- mapped `aeval`, then apply the already verified semilocal zero relation.
    calc
      ψ (z i)
          = Polynomial.aeval (algebraMap S Sp (P.val i))
              (Polynomial.map ((algebraMap Rp Sp).comp lift) (Q₁ i)) := by
                simpa [Rp, Sp, S₁, z] using
                  awayLift_aeval_eq_map_aeval
                    (R := R) (S := S) (p := p) (g₁ := g₁) hg₁
                    (x := P.val i) (Q := Q₁ i)
      _ = 0 := by
            simpa [Rp, Sp] using h_eval_in_semilocal i
  obtain ⟨g₂, hg₂, hz₂⟩ :=
    exists_notMem_zero_family_away_of_zero_in_semilocal_localization
      (R := R) (S := S) p hg₁ z hz_semilocal
  have h_integral_generator_away (i : Fin n) :
      ((Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).toRingHom).IsIntegralElem
        (algebraMap S (Localization.Away (algebraMap R S (g₁ * g₂))) (P.val i)) := by
    have hz_i :
        let S₁ := Localization.Away (algebraMap R S g₁)
        let B := Localization.Away ((algebraMap R S g₁) * (algebraMap R S g₂))
        let ρS : S₁ →+* B :=
          IsLocalization.Away.awayToAwayRight
            (P := B) (algebraMap R S g₁) (algebraMap R S g₂)
        let σ : Localization.Away g₁ →+* S₁ := Localization.awayMap (algebraMap R S) g₁
        ρS (Polynomial.eval₂ σ (algebraMap S S₁ (P.val i)) (Q₁ i)) = 0 := by
      -- Convert the descended vanishing relation into the `eval₂` surface expected by the
      -- second-localization integrality witness.
      simpa [S₁, z, Polynomial.aeval_def] using hz₂ i
    exact
      isIntegral_generator_image_of_monic_zero_relation_after_second_localization
        (R := R) (S := S) (g₁ := g₁) (g₂ := g₂) (x := P.val i)
        (Q := Q₁ i) (hQmonic := hQ₁monic i) hz_i
  letI :
      Algebra (Localization.Away (g₁ * g₂))
        (Localization.Away (algebraMap R S (g₁ * g₂))) :=
    (Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).toAlgebra
  letI : IsScalarTower R (Localization.Away (g₁ * g₂))
      (Localization.Away (algebraMap R S (g₁ * g₂))) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := Localization.Away (g₁ * g₂))
      (A := Localization.Away (algebraMap R S (g₁ * g₂))) fun r ↦ by
        simpa [RingHom.algebraMap_toAlgebra] using
          ((Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).commutes r).symm
  have hIntegralStage :
      ((Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).toRingHom).IsIntegral :=
    localized_generator_family_integral (R := R) (S := S) P h_integral_generator_away
  have hFiniteTypeStage :
      ((Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).toRingHom).FiniteType := by
    have hRT : (algebraMap R (Localization.Away (algebraMap R S (g₁ * g₂)))).FiniteType := by
      exact
        RingHom.FiniteType.comp
          (RingHom.finiteType_algebraMap.mpr
            (inferInstance :
              Algebra.FiniteType S
                (Localization.Away (algebraMap R S (g₁ * g₂)))))
          (RingHom.finiteType_algebraMap.mpr inferInstance)
    have hcomp :
        (((Localization.awayMapₐ (Algebra.ofId R S) (g₁ * g₂)).toRingHom).comp
          (algebraMap R (Localization.Away (g₁ * g₂)))).FiniteType := by
      simpa [Localization.awayMapₐ, RingHom.algebraMap_toAlgebra,
        IsScalarTower.algebraMap_eq R (Localization.Away (g₁ * g₂))
          (Localization.Away (algebraMap R S (g₁ * g₂)))] using hRT
    exact RingHom.FiniteType.of_comp_finiteType hcomp
  refine ⟨g₁ * g₂, ?_, ?_⟩
  · -- The final denominator still avoids the minimal prime because both factors do.
    intro hmem
    exact (p.isPrime.mem_or_mem hmem).elim hg₁ hg₂
  · -- The localized map is finite because it is both finite type and integral.
    simpa [AlgHom.Finite] using
      (RingHom.Finite.of_isIntegral_of_finiteType hIntegralStage hFiniteTypeStage)

end
