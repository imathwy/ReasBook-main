import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_113_1 (from Chap10) -/
noncomputable section

universe u v

open PrimeSpectrum
open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S]

/-- Bridge/view: the natural-number transcendence degree of the induced fraction-field extension
attached to an injective algebra map of domains. The `FaithfulSMul` witness needed to lift the
algebra to fraction rings is derived internally from injectivity, so it stays out of theorem
surfaces. -/
noncomputable abbrev fractionRingTrdeg
    (hinj : Function.Injective (algebraMap R S)) : ℕ :=
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  Cardinal.toNat (trdeg (FractionRing R) (FractionRing S))

end

end Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S]

/-- Helper for Lemma 10.113.1: once the source proof has been reduced to a tower
`R ⊆ T ⊆ S`, the two induction-step inequalities combine by plain arithmetic. -/
lemma tower_step_primeHeight_residueFieldTrdeg_le
    {heightR heightT heightS genericRT genericTS residueRT residueTS : ℕ}
    (hRT : heightT + residueRT ≤ heightR + genericRT)
    (hTS : heightS + residueTS ≤ heightT + genericTS) :
    heightS + (residueRT + residueTS) ≤ heightR + (genericRT + genericTS) := by
  -- Add the two induction-step bounds and cancel the intermediate height contribution.
  omega

/-- Helper for Lemma 10.113.1: in the universally catenary case, the same tower step
preserves equality after adding the transcendence-degree contributions. -/
lemma tower_step_primeHeight_residueFieldTrdeg_eq
    {heightR heightT heightS genericRT genericTS residueRT residueTS : ℕ}
    (hRT : heightT + residueRT = heightR + genericRT)
    (hTS : heightS + residueTS = heightT + genericTS) :
    heightS + (residueRT + residueTS) = heightR + (genericRT + genericTS) := by
  -- The equality case is the same arithmetic cancellation as in the inequality step.
  omega

/-- Helper for Lemma 10.113.1: after coercing to `WithBot ℕ∞`, the natural-number prime
height of a Noetherian prime ideal is the Krull dimension of its localization. -/
lemma primeHeight_natCast_eq_ringKrullDim_localizationAtPrime
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] :
    (((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime p) := by
  -- Convert the local Krull dimension back to the height of the original prime.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    Ideal.height_eq_primeHeight]
  -- Noetherianity makes the prime height finite, so the cast of `toNat` recovers it.
  exact_mod_cast ENat.coe_toNat (Ideal.primeHeight_ne_top p)

/-- Helper for Lemma 10.113.1: the fiber prime attached to `q` contracts back to `q` along the
canonical map `S → κ(q ∩ R) ⊗[R] S`. -/
theorem fiberPrime_contracts_to_source_prime
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    PrimeSpectrum.comap (algebraMap B ((q.asIdeal.under A).Fiber B)) (fiberPrimeAt A B q) = q := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  have hleft :
      ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q)) = q := by
    -- `fiberPrimeAt` was defined using `preimageEquivFiber`, so the inverse map returns `q`.
    simpa [p, fiberPrimeAt] using
      congrArg Subtype.val
        ((PrimeSpectrum.preimageEquivFiber A B p).symm_apply_apply ⟨q, rfl⟩)
  -- Unfold the defining contraction map of `preimageEquivFiber` and rewrite by the inverse law.
  calc
    PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) (fiberPrimeAt A B q)
        = ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q)) := by
            change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
                (fiberPrimeAt A B q) =
              ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q))
            rfl
    _ = q := hleft

/-- Helper for Lemma 10.113.1: on ideals, the fiber prime attached to `q` contracts back to
`q.asIdeal`. -/
theorem fiberPrime_comap_asIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    Ideal.comap (algebraMap B ((q.asIdeal.under A).Fiber B)) (fiberPrimeAt A B q).asIdeal =
      q.asIdeal := by
  -- Pass from the prime-spectrum statement to the underlying ideals.
  simpa using congrArg PrimeSpectrum.asIdeal
    (fiberPrime_contracts_to_source_prime (A := A) (B := B) q)

/-- Helper for Lemma 10.113.1: the residue field at the fiber prime is canonically identified
with the residue field at the original prime. -/
noncomputable def fiberPrime_residueField_equiv_source
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    (fiberPrimeAt A B q).asIdeal.ResidueField ≃ₐ[B] q.asIdeal.ResidueField := by
  let hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ q.asIdeal (fiberPrimeAt A B q).asIdeal
          (Algebra.ofId B ((q.asIdeal.under A).Fiber B))
          (fiberPrime_comap_asIdeal (A := A) (B := B) q).symm) := by
    -- The canonical map to the fiber is surjective on stalks, so it induces a residue-field
    -- bijection at the corresponding primes.
    simpa using
      RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        ((Ideal.surjectiveOnStalks_residueField (R := A) (q.asIdeal.under A)).baseChange')
        q.asIdeal (fiberPrimeAt A B q).asIdeal
        (fiberPrime_comap_asIdeal (A := A) (B := B) q).symm
  -- Package the bijective residue-field map as the desired algebra equivalence.
  exact
    (AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ q.asIdeal (fiberPrimeAt A B q).asIdeal
      (Algebra.ofId B ((q.asIdeal.under A).Fiber B))
      (fiberPrime_comap_asIdeal (A := A) (B := B) q).symm)
      hbij).symm

/-- Helper for Lemma 10.113.1: localizing corresponding primes along an algebra equivalence gives
an algebra equivalence of the local rings. -/
private noncomputable def localizationAtPrime_algEquiv_of_algEquiv
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Localization.AtPrime (PrimeSpectrum.comap e.toRingHom q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  -- Transport the source prime by `e` and then invoke the canonical localization comparison.
  Localization.localAlgEquiv
    (I := (PrimeSpectrum.comap e.toRingHom q).asIdeal)
    (J := q.asIdeal)
    e
    (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)

/-- Helper for Lemma 10.113.1: an `R`-algebra equivalence identifies the residue fields of
corresponding prime ideals. -/
private noncomputable def residueField_algEquiv_of_algEquiv
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    (PrimeSpectrum.comap e.toRingHom q).asIdeal.ResidueField ≃ₐ[R] q.asIdeal.ResidueField := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom q
  have hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal e.toAlgHom
          (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)) := by
    -- A ring equivalence is surjective on stalks, so the induced residue-field map is bijective.
    simpa [p] using
      RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (RingHom.surjectiveOnStalks_of_surjective e.surjective)
        p.asIdeal q.asIdeal
        (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)
  -- Package the canonical bijection as the required algebra equivalence on residue fields.
  exact
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal e.toAlgHom
        (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q))
      hbij

/-- Helper for Lemma 10.113.1: the fiber of `A[X]` over a prime `p` is canonically the polynomial
ring `κ(p)[X]`. -/
private noncomputable def polynomial_fiber_algEquiv_residueField_polynomial
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    p.Fiber (Polynomial A) ≃ₐ[p.ResidueField] Polynomial p.ResidueField := by
  let eQuot :
      p.Fiber (Polynomial A) ≃ₐ[p.ResidueField]
        Polynomial p.ResidueField ⧸
          ((RingHom.ker (AlgHom.id A (Polynomial A) : Polynomial A →ₐ[A] Polynomial A)).map
            (Polynomial.mapRingHom (algebraMap A p.ResidueField))) :=
    Polynomial.fiberEquivQuotient
      (f := (AlgHom.id A (Polynomial A) : Polynomial A →ₐ[A] Polynomial A))
      (by intro x; exact ⟨x, rfl⟩)
      p
  have hker :
      ((RingHom.ker (AlgHom.id A (Polynomial A) : Polynomial A →ₐ[A] Polynomial A)).map
        (Polynomial.mapRingHom (algebraMap A p.ResidueField))) = ⊥ := by
    -- For the identity presentation, the quotient kernel is zero, so the quotient disappears.
    have hker0 :
        RingHom.ker (AlgHom.id A (Polynomial A) : Polynomial A →ₐ[A] Polynomial A) =
          (⊥ : Ideal (Polynomial A)) := by
      ext f
      simp [RingHom.mem_ker]
    rw [hker0, Ideal.map_bot]
  -- Route correction: use the library owner `Polynomial.fiberEquivQuotient` first, then collapse
  -- the resulting quotient by the zero ideal back to the polynomial ring itself.
  exact eQuot.trans ((Ideal.quotientEquivAlgOfEq _ hker).trans (AlgEquiv.quotientBot _ _))

/-- Helper for Lemma 10.113.1: transport `fiberPrimeAt` for `A[X]` to a literal prime of
`κ(q ∩ A)[X]`. -/
private noncomputable def fiberPrime_polynomial_transport
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    PrimeSpectrum (Polynomial ((q.asIdeal.under A).ResidueField)) := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  -- The transported prime is just the comap of `fiberPrimeAt q` along the polynomial-fiber
  -- equivalence.
  exact PrimeSpectrum.comap
    ((polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).symm.toRingHom)
    (fiberPrimeAt A (Polynomial A) q)

/-- Helper for Lemma 10.113.1: after transporting the polynomial fiber to `κ(p)[X]`, the fiber
local ring becomes the localization of that polynomial ring at the transported prime. -/
private lemma comap_polynomial_fiber_transport_eq_fiberPrimeAt
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    PrimeSpectrum.comap
        (polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).toRingHom
        (fiberPrime_polynomial_transport (A := A) q) =
      fiberPrimeAt A (Polynomial A) q := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  -- The transported prime was defined by comapping along the inverse equivalence, so comapping it
  -- back along the forward equivalence recovers the original fiber prime.
  apply PrimeSpectrum.ext
  change
      Ideal.comap
        (polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).toRingHom
        (fiberPrime_polynomial_transport (A := A) q).asIdeal =
      (fiberPrimeAt A (Polynomial A) q).asIdeal
  simpa [fiberPrime_polynomial_transport] using
    (Ideal.comap_of_equiv (I := (fiberPrimeAt A (Polynomial A) q).asIdeal)
      (polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).toRingEquiv)

/-- Helper for Lemma 10.113.1: after transporting the polynomial fiber to `κ(p)[X]`, the fiber
local ring becomes the localization of that polynomial ring at the transported prime. -/
private lemma ringKrullDim_fiberLocalRingAt_polynomial_eq_ringKrullDim_localization_transport
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    ringKrullDim (fiberLocalRingAt A (Polynomial A) q) =
      ringKrullDim (Localization.AtPrime (fiberPrime_polynomial_transport (A := A) q).asIdeal) := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let eκ : p.Fiber (Polynomial A) ≃ₐ[p.ResidueField] Polynomial p.ResidueField :=
    polynomial_fiber_algEquiv_residueField_polynomial (A := A) p
  let qκ : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let eLoc :
      Localization.AtPrime qκ.asIdeal ≃ₐ[p.ResidueField]
        Localization.AtPrime (PrimeSpectrum.comap eκ.toRingHom qκ).asIdeal :=
    (localizationAtPrime_algEquiv_of_algEquiv (R := p.ResidueField) eκ qκ).symm
  have hqκ : PrimeSpectrum.comap eκ.toRingHom qκ = fiberPrimeAt A (Polynomial A) q := by
    -- Reuse the dedicated prime-transport owner instead of reproving the comap calculation.
    simpa [p, qκ] using comap_polynomial_fiber_transport_eq_fiberPrimeAt (A := A) q
  -- Unfold `fiberLocalRingAt` and transport Krull dimension across the localized algebra
  -- equivalence.
  have hdim :
      ringKrullDim (Localization.AtPrime (PrimeSpectrum.comap eκ.toRingHom qκ).asIdeal) =
        ringKrullDim (Localization.AtPrime qκ.asIdeal) := by
    exact (ringKrullDim_eq_of_ringEquiv eLoc.toRingEquiv).symm
  rw [hqκ] at hdim
  simpa [fiberLocalRingAt, p, qκ] using hdim

/-- Helper for Lemma 10.113.1: the missing transport blocker is an explicit `κ(q ∩ A)`-algebra
structure on the residue field of the fiber prime over `q`. -/
private noncomputable abbrev fiberPrime_residueField_baseAlgebra
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    Algebra p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField :=
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  (((fiberPrime_residueField_equiv_source (A := A) (B := B) q).symm.toRingHom).comp
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) rfl)).toAlgebra

/-- Helper for Lemma 10.113.1: the transported prime of `κ(p)[X]` likewise needs its explicit
base-field algebra structure recorded to keep later residue-field trdeg statements type-stable. -/
private noncomputable abbrev fiberPrime_polynomial_transport_residueField_baseAlgebra
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    Algebra p.ResidueField (fiberPrime_polynomial_transport (A := A) q).asIdeal.ResidueField :=
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := inferInstance
  (((algebraMap (Polynomial p.ResidueField)
      (fiberPrime_polynomial_transport (A := A) q).asIdeal.ResidueField)).comp
    Polynomial.C).toAlgebra

/-- Helper for Lemma 10.113.1: the explicit `κ(q ∩ A)`-algebra on the residue field of the
transported polynomial prime agrees with the default scalar map coming from the polynomial ring. -/
private lemma transported_polynomial_residueField_baseAlgebra_eq_default
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    letI : p.IsPrime := by
      dsimp [p]
      infer_instance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let _ : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      fiberPrime_polynomial_transport_residueField_baseAlgebra (A := A) q
    algebraMap p.ResidueField Q.asIdeal.ResidueField =
      (algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp Polynomial.C := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let _ : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    fiberPrime_polynomial_transport_residueField_baseAlgebra (A := A) q
  let _ : IsScalarTower p.ResidueField (Polynomial p.ResidueField) Q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- The explicit transported scalar structure was defined exactly as the polynomial scalar tower.
  simpa using
    (IsScalarTower.algebraMap_eq p.ResidueField (Polynomial p.ResidueField)
      Q.asIdeal.ResidueField)

/-- Helper for Lemma 10.113.1: after installing the explicit `κ(q ∩ A)`-algebra on the fiber-prime
residue field, the canonical equivalence back to `κ(q)` respects those base scalars. -/
private lemma fiberPrime_residueField_equiv_source_commutes
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B)
    (x : (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    let _ : Algebra p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := B) q
    fiberPrime_residueField_equiv_source (A := A) (B := B) q
        (algebraMap p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField x) =
      algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField x := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  -- Unfold the explicit source-side algebra map and cancel the inverse equivalence.
  change
    fiberPrime_residueField_equiv_source (A := A) (B := B) q
        ((((fiberPrime_residueField_equiv_source (A := A) (B := B) q).symm.toRingHom).comp
          (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) rfl)) x) =
      algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField x
  -- The explicit algebra map was defined by composing the residue-field map with the inverse
  -- equivalence, so applying the equivalence cancels that inverse immediately.
  simpa [RingHom.comp_apply] using
    (fiberPrime_residueField_equiv_source (A := A) (B := B) q).apply_symm_apply
      ((Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) rfl) x)

/-- Helper for Lemma 10.113.1: after composing the default `κ(p)`-algebra map on the fiber-prime
residue field with the canonical map back to `κ(q)`, one recovers the usual residue-field map
`κ(p) → κ(q)`. -/
private lemma fiberPrime_polynomial_source_default_comp_commutes
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    (fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q).toRingHom.comp
        ((algebraMap (p.Fiber (Polynomial A))
            (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
          (algebraMap p.ResidueField (p.Fiber (Polynomial A)))) =
      Ideal.ResidueField.map p q.asIdeal (algebraMap A (Polynomial A)) rfl := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  -- Compare both maps out of `κ(p)` by checking them on the image of `A`.
  apply Ideal.ResidueField.ringHom_ext (I := p)
  ext a
  -- Rewrite the default source scalar map through the tensor-product right inclusion.
  simp only [RingHom.comp_apply]
  have hbase :
      (algebraMap p.ResidueField (p.Fiber (Polynomial A))) ((algebraMap A p.ResidueField) a) =
        ((Algebra.TensorProduct.includeRight : Polynomial A →ₐ[A] p.Fiber (Polynomial A)).toRingHom.comp
          Polynomial.C) a := by
    simpa [RingHom.comp_apply] using
      congrArg (fun f : A →+* p.Fiber (Polynomial A) => f a)
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
          (R := A) (A := p.ResidueField) (B := Polynomial A))
  rw [hbase, RingHom.comp_apply]
  have hright_apply :
      (algebraMap (p.Fiber (Polynomial A))
          (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField)
        ((Algebra.TensorProduct.includeRight : Polynomial A →ₐ[A] p.Fiber (Polynomial A)).toRingHom
          (Polynomial.C a)) =
      algebraMap (Polynomial A) (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        (Polynomial.C a) := by
    simpa [RingHom.comp_apply] using
      congrArg
        (fun f : Polynomial A →+* (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField =>
          f (Polynomial.C a))
        (AlgHom.comp_algebraMap_of_tower (R := Polynomial A)
          (f := IsScalarTower.toAlgHom (Polynomial A)
            (p.Fiber (Polynomial A))
            (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField))
  rw [hright_apply]
  -- The source-to-target residue-field equivalence is `Polynomial A`-linear, so it carries the
  -- right-inclusion scalar map to the ordinary polynomial scalar map on `κ(q)`.
  calc
    (fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q).toRingHom
        ((algebraMap (Polynomial A) (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField)
          (Polynomial.C a))
      = algebraMap (Polynomial A) q.asIdeal.ResidueField (Polynomial.C a) := by
          simpa using
            (fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q).commutes
              (Polynomial.C a)
    _ = (Ideal.ResidueField.map p q.asIdeal (algebraMap A (Polynomial A)) rfl)
          ((algebraMap A p.ResidueField) a) := by
          symm
          simpa using
            (Ideal.ResidueField.map_algebraMap p q.asIdeal (algebraMap A (Polynomial A)) rfl a)

/-- Helper for Lemma 10.113.1: the fiber-prime residue field is canonically identified with
`κ(q)` as an algebra over the contracted residue field `κ(q ∩ A)`. -/
private noncomputable def fiberPrime_residueField_algEquiv_base
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    let _ : Algebra p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := B) q
    (fiberPrimeAt A B q).asIdeal.ResidueField ≃ₐ[
      (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField] q.asIdeal.ResidueField := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  let _ : Algebra p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := B) q
  -- Repackage the existing ring equivalence using the explicit `κ(p)`-linearity recorded above.
  exact
    AlgEquiv.ofRingEquiv
      (f := (fiberPrime_residueField_equiv_source (A := A) (B := B) q).toRingEquiv)
      (fiberPrime_residueField_equiv_source_commutes (A := A) (B := B) q)

/-- Helper for Lemma 10.113.1: transporting the polynomial fiber prime to `κ(p)[X]` does not
change the residue-field transcendence degree over `κ(p)`. -/
private lemma fiberPrime_polynomial_residueFieldTrdeg_eq_transport
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : Algebra p.ResidueField (fiberPrime_polynomial_transport (A := A) q).asIdeal.ResidueField :=
      fiberPrime_polynomial_transport_residueField_baseAlgebra (A := A) q
    Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat
        (Algebra.trdeg p.ResidueField
          (fiberPrime_polynomial_transport (A := A) q).asIdeal.ResidueField) := by
  -- TODO: combine the new source-side commutation owner
  -- `fiberPrime_polynomial_source_default_comp_commutes` with
  -- `transported_polynomial_residueField_baseAlgebra_eq_default` to upgrade the transported ring
  -- equivalence to a `κ(p)`-algebra equivalence. The remaining blocker is packaging the explicit
  -- source scalar map from `fiberPrime_residueField_baseAlgebra` as the default scalar tower used
  -- by `residueField_algEquiv_of_algEquiv`.
  sorry

/-- Helper for Lemma 10.113.1: over a domain, the residue field at the zero prime is canonically
the fraction field. -/
private noncomputable def bot_residueField_fractionRing_algEquiv
    (S : Type*) [CommRing S] [IsDomain S] :
    FractionRing S ≃ₐ[S] ((⊥ : Ideal S).ResidueField) := by
  let e : S ≃ₐ[S] S ⧸ (⊥ : Ideal S) := (AlgEquiv.quotientBot S S).symm
  letI : IsFractionRing S ((⊥ : Ideal S).ResidueField) := by
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap S ((⊥ : Ideal S).ResidueField) x =
      algebraMap (S ⧸ (⊥ : Ideal S)) ((⊥ : Ideal S).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    rfl
  -- Transport the fraction-field structure across the quotient-by-zero identification.
  exact FractionRing.algEquiv S ((⊥ : Ideal S).ResidueField)

/-- Helper for Lemma 10.113.1: a nonzero prime of `k[X]` cuts out an algebraic field extension of
`k`. -/
private lemma polynomial_quotient_isAlgebraic_of_ne_bot
    {k : Type*} [Field k] (Q : Ideal (Polynomial k)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    Algebra.IsAlgebraic k (Polynomial k ⧸ Q) := by
  let g₀ : Polynomial k := Submodule.IsPrincipal.generator Q
  have hg₀_ne : g₀ ≠ 0 := by
    intro hg₀
    exact hQ ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero Q).2 hg₀)
  let g : Polynomial k := g₀ * Polynomial.C (Polynomial.leadingCoeff g₀)⁻¹
  have hg_monic : g.Monic := by
    -- Over a field, scaling the generator by the inverse leading coefficient makes it monic.
    simpa [g] using Polynomial.monic_mul_leadingCoeff_inv hg₀_ne
  have hg_mem : g ∈ Q := by
    -- The chosen monic generator is a unit multiple of the principal generator of `Q`.
    simpa [g] using Q.mul_mem_right (Polynomial.C (Polynomial.leadingCoeff g₀)⁻¹)
      (Submodule.IsPrincipal.generator_mem Q)
  -- A monic relation inside `Q` makes the whole quotient integral over the ground field.
  have hIntegralHom : (algebraMap k (Polynomial k ⧸ Q)).IsIntegral := by
    simpa using
      (Polynomial.Monic.quotient_isIntegral (S := k) (I := Q) hg_monic hg_mem)
  letI : Algebra.IsIntegral k (Polynomial k ⧸ Q) :=
    (algebraMap_isIntegral_iff (R := k) (A := Polynomial k ⧸ Q)).mp hIntegralHom
  infer_instance

/-- Helper for Lemma 10.113.1: the residue field at the zero prime of a field is canonically the
field itself. This is the owner needed for the `Q = ⊥` branch in the polynomial case. -/
private noncomputable def bot_residueField_algEquiv
    (K : Type*) [Field K] :
    ((⊥ : Ideal K).ResidueField) ≃ₐ[K] K := by
  let eQuot :
      (K ⧸ (⊥ : Ideal K)) ≃ₐ[K] ((⊥ : Ideal K).ResidueField) :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K (K ⧸ (⊥ : Ideal K)) ((⊥ : Ideal K).ResidueField))
      (Ideal.bijective_algebraMap_quotient_residueField (⊥ : Ideal K))
  -- Replace the zero-prime residue field by the quotient by the zero ideal.
  exact eQuot.symm.trans (AlgEquiv.quotientBot K K)

/-- Helper for Lemma 10.113.1: over a field, the polynomial ring in one variable has Krull
dimension `1`. -/
private lemma polynomial_ringKrullDim_eq_one
    {k : Type*} [Field k] :
    ringKrullDim (Polynomial k) = 1 := by
  -- The general polynomial-dimension formula specializes to `0 + 1` over a field.
  simpa [ringKrullDim_eq_zero_of_field] using
    (Polynomial.ringKrullDim_of_isNoetherianRing (R := k))

/-- Helper for Lemma 10.113.1: localizing `k[X]` at the zero prime gives its fraction field, so
the resulting local ring has Krull dimension `0`. -/
private lemma polynomial_ringKrullDim_localizationAtPrime_bot_eq_zero
    {k : Type*} [Field k] :
    ringKrullDim (Localization.AtPrime (⊥ : Ideal (Polynomial k))) = 0 := by
  -- Identify the localization at `(0)` with the fraction field of `k[X]`.
  letI : IsFractionRing (Polynomial k) (Localization.AtPrime (⊥ : Ideal (Polynomial k))) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance :
        IsLocalization ((⊥ : Ideal (Polynomial k)).primeCompl)
          (Localization.AtPrime (⊥ : Ideal (Polynomial k))))
  let e : FractionRing (Polynomial k) ≃ₐ[Polynomial k]
      Localization.AtPrime (⊥ : Ideal (Polynomial k)) :=
    FractionRing.algEquiv (Polynomial k) (Localization.AtPrime (⊥ : Ideal (Polynomial k)))
  -- Transport the claim to the fraction field, whose Krull dimension is zero.
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact ringKrullDim_eq_zero_of_field (FractionRing (Polynomial k))

/-- Helper for Lemma 10.113.1: in `k[X]`, every nonzero prime ideal is maximal. -/
private lemma polynomial_prime_isMaximal_of_ne_bot
    {k : Type*} [Field k] (Q : Ideal (Polynomial k)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    Q.IsMaximal := by
  have hdim : ringKrullDim (Polynomial k) = 1 :=
    polynomial_ringKrullDim_eq_one (k := k)
  have hdim' : Ring.KrullDimLE 1 (Polynomial k) :=
    Ring.krullDimLE_iff.mpr (by simpa [hdim])
  letI : Ring.DimensionLEOne (Polynomial k) := by
    refine ⟨fun {p} hp hprime ↦ ?_⟩
    exact Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim' p hp hprime
  -- In a dimension-one domain, a nonzero prime is automatically maximal.
  exact Ring.DimensionLEOne.maximalOfPrime hQ inferInstance

/-- Helper for Lemma 10.113.1: localizing `k[X]` at a nonzero prime ideal gives a one-dimensional
local ring. -/
private lemma polynomial_ringKrullDim_localizationAtPrime_eq_one_of_ne_bot
    {k : Type*} [Field k] (Q : Ideal (Polynomial k)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ringKrullDim (Localization.AtPrime Q) = 1 := by
  letI : Q.IsMaximal := polynomial_prime_isMaximal_of_ne_bot (Q := Q) hQ
  letI : Q.LiesOver (⊥ : Ideal k) := by
    -- Contracting a prime of `k[X]` back to the field `k` can only give `(0)`.
    refine ⟨?_⟩
    simpa [Ideal.under_def] using
      (Ideal.eq_bot_of_prime (I := Ideal.comap Polynomial.C Q)).symm
  have hbot_height : (⊥ : Ideal k).height = 0 := by
    -- The zero ideal is the unique minimal prime of a field.
    have hbot_primeHeight : (⊥ : Ideal k).primeHeight = 0 := by
      rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
      simp
    simpa [Ideal.height_eq_primeHeight] using hbot_primeHeight
  have hQ_height : Q.height = 1 := by
    -- The polynomial height-jump formula over the zero prime gives height exactly one.
    calc
      Q.height = (⊥ : Ideal k).height + 1 := by
        simpa using (Polynomial.height_eq_height_add_one (p := (⊥ : Ideal k)) (P := Q))
      _ = 1 := by simp [hbot_height]
  -- Convert the height computation into the local Krull dimension.
  simpa [hQ_height] using
    (IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q))

/-- Helper for Lemma 10.113.1: after transporting a prime of `A[X]` to `κ(p)[X]`, the residue
field transcendence-degree contribution is `1` in the generic branch and `0` in the closed
branch. -/
private lemma polynomial_transport_branch_trdeg_values
    {k : Type*} [Field k] (Q : PrimeSpectrum (Polynomial k)) :
    Cardinal.toNat (Algebra.trdeg k Q.asIdeal.ResidueField) =
      if Q.asIdeal = ⊥ then 1 else 0 := by
  by_cases hQ : Q.asIdeal = ⊥
  · have hQbot : Q = ⊥ := by
      -- A prime-spectrum point is determined by its underlying ideal.
      apply PrimeSpectrum.ext
      simpa using hQ
    subst hQbot
    let S := Polynomial k
    let e : FractionRing S ≃ₐ[k] ((⊥ : Ideal S).ResidueField) :=
      AlgEquiv.restrictScalars k (bot_residueField_fractionRing_algEquiv (S := S))
    have hAlgFrac : Algebra.IsAlgebraic S (FractionRing S) := by
      -- The fraction field is algebraic over the polynomial ring, so the upper trdeg term vanishes.
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := FractionRing S)
          (C := FractionRing S)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing S) (FractionRing S))
    have htrdegFrac : Algebra.trdeg k (FractionRing S) = Algebra.trdeg k S := by
      -- Split the tower `k ⟶ S ⟶ Frac(S)` and kill the relative transcendence degree upstairs.
      have hsplit := trdeg_add_eq (R := k) (S := S) (A := FractionRing S)
      have hzero : Algebra.trdeg S (FractionRing S) = 0 :=
        trdeg_eq_zero (R := S) (A := FractionRing S)
      simpa [hzero] using hsplit.symm
    calc
      Cardinal.toNat (Algebra.trdeg k ((⊥ : Ideal S).ResidueField))
          = Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := by
              simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq (R := k) e).symm
      _ = Cardinal.toNat (Algebra.trdeg k S) := by rw [htrdegFrac]
      _ = 1 := by
        simpa [S] using congrArg Cardinal.toNat (Polynomial.trdeg_of_isDomain (R := k))
      _ = if (⊥ : Ideal S) = ⊥ then 1 else 0 := by simp
  · have hQmax : Q.asIdeal.IsMaximal :=
      polynomial_prime_isMaximal_of_ne_bot (Q := Q.asIdeal) hQ
    letI : Q.asIdeal.IsMaximal := hQmax
    let eQuot : (Polynomial k ⧸ Q.asIdeal) ≃ₐ[k] Q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective
        (IsScalarTower.toAlgHom k (Polynomial k ⧸ Q.asIdeal) Q.asIdeal.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField Q.asIdeal)
    letI : Algebra.IsAlgebraic k (Polynomial k ⧸ Q.asIdeal) :=
      polynomial_quotient_isAlgebraic_of_ne_bot (Q := Q.asIdeal) hQ
    letI : Algebra.IsAlgebraic k Q.asIdeal.ResidueField :=
      Algebra.IsAlgebraic.of_injective eQuot.symm.toAlgHom eQuot.symm.injective
    -- The nonzero branch is algebraic over `k`, so its transcendence degree vanishes.
    simpa [hQ, trdeg_eq_zero (R := k) (A := Q.asIdeal.ResidueField)]

/-- Helper for Lemma 10.113.1: in the one-generator polynomial case, the local-dimension term and
the residue-field transcendence-degree term add up to `1`. -/
private lemma polynomial_step_primeHeight_residueFieldTrdeg_eq
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (q : PrimeSpectrum (Polynomial A)) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
  -- TODO: combine the transported fiber-dimension equality with
  -- `fiberPrime_polynomial_residueFieldTrdeg_eq_transport` and
  -- `polynomial_transport_branch_trdeg_values`; the current blocker is keeping the `κ(p)`-algebra
  -- structure on the transported residue fields explicit enough to avoid typeclass-search timeouts.
  sorry

/-
Domain-style sampling:
- primary domain: the dimension formula for finite type maps of domains, organized around prime
  spectra, localizations at primes, and universal catenarity;
- sampled owner API:
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`,
  `FractionRing.liftAlgebra`,
  `FractionRing.isScalarTower_liftAlgebra`,
  `faithfulSMul_iff_algebraMap_injective`,
  `Algebra.fractionRingTrdeg`,
  `Ideal.over_under`,
  `UniversallyCatenaryRing`,
  `Ideal.Quotient.algebraOfLiesOver`;
- owner abstraction: a point `q : PrimeSpectrum S`, with the source prime recovered canonically as
  `q.asIdeal.under R`; the induced fraction-field algebra `Frac(R) → Frac(S)` is canonical
  derived scaffolding from injectivity is obtained directly from the canonical owner theorem
  `faithfulSMul_iff_algebraMap_injective`;
- primitive data: the finite type map `R → S`, injectivity of `algebraMap R S`, and the target
  point `q`;
- derived API: the fraction-field tower needed to state transcendence degrees, and the explicit
  ideal-level lies-over restatements below. The generic fraction-field transcendence-degree term is
  packaged as the thin bridge `Algebra.fractionRingTrdeg`, so the public statements do not expose
  instance plumbing.

Layer triage:
- `source-facing`: the height/transcendence-degree inequality and equality;
- `core/canonical`: the prime-spectrum/local-fiber owners from Lemma `10.112.7` together with the
  universally catenary owner from Definition `10.105.3`;
- `bridge/view`: the ideal-level formulations with an explicit `hq : q.LiesOver p`.

This file therefore uses the `PrimeSpectrum` statement as the public owner layer and derives the
ideal-level restatements from it, rather than keeping only the lower-level lies-over surface. The
fraction-field algebra/tower itself is the canonical `FractionRing` owner interface; only the
`FaithfulSMul` input needed to build it is derived from injectivity.
-/

section FiniteType

variable [IsNoetherianRing R] [Algebra.FiniteType R S]

-- Proof sketch: replace the heights of `p` and `q` by the dimensions of the local rings `R_p` and
-- `S_q`, then induct on a finite generating set of `S` over `R`. Reduce to the one-generator cases
-- `S = R[x]` and `S = R[x] / 𝔫`, using the flat dimension formula in the polynomial case, the drop
-- by at least one after quotienting by a nonzero principal ideal, and additivity of transcendence
-- degree in towers for the induction step.
/-- Prime-spectrum owner form of Lemma 10.113.1: for a point `q` of `Spec S`, the height of `q`
plus the transcendence degree of `κ(q)` over `κ(q ∩ R)` is bounded by the height of the
contraction together with the generic transcendence degree term. -/
theorem primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_trdeg_of_finiteType
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
        Algebra.fractionRingTrdeg hinj :=
  by
    -- Route correction: Lemma `10.112.7` needs going down, so the source-faithful proof must
    -- proceed by adjoining generators one at a time instead of applying the local formula directly.
    -- TODO: the polynomial fiber transport is now packaged by
    -- `fiberPrime_polynomial_transport` and
    -- `ringKrullDim_fiberLocalRingAt_polynomial_eq_ringKrullDim_localization_transport`, and the
    -- field-level branch computation is now isolated in
    -- `polynomial_transport_branch_trdeg_values`.
    -- TODO: compare the transported residue field back to `κ(q)` over `κ(q ∩ R)`, then carry out
    -- the localized quotient comparison for the one-generator quotient case using Lemma `10.60.13`.
    -- The remaining structural blocker is this residue-field transport plus the local quotient model.
    sorry

/-- Lemma 10.113.1: if `R → S` is an injective finite type map of domains with `R` Noetherian and
`q` lies over `p`, then the height of `q` plus the transcendence degree of the residue-field
extension `κ(q) / κ(p)` is bounded by the height of `p` plus the transcendence degree of `Frac(S)`
over `Frac(R)`. -/
theorem primeHeight_add_residueFieldTrdeg_le_primeHeight_add_trdeg_of_finiteType
    (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] (hq : q.LiesOver p) :
    ENat.toNat (Ideal.primeHeight q) +
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight p) +
        Algebra.fractionRingTrdeg hinj :=
  by
    have hp : p = q.under R := by
      simpa using hq.over
    subst p
    simpa using
      (primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_trdeg_of_finiteType
        hinj (⟨q, inferInstance⟩ : PrimeSpectrum S))

end FiniteType

section UniversallyCatenary

variable [Algebra.FiniteType R S] [UniversallyCatenaryRing.{u, v} R]

-- Proof sketch: in the universally catenary case, the one-generator polynomial step is already an
-- equality, and in the quotient step by a nonzero prime of `R[x]` catenarity shows the local
-- dimension drops by exactly one. Running the same induction as for the inequality keeps equality
-- at each stage.
/-- Prime-spectrum owner form of the universally catenary equality case. -/
theorem primeHeight_add_residueFieldTrdeg_eq_primeHeight_under_add_trdeg_of_universallyCatenary
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
        Algebra.fractionRingTrdeg hinj :=
  by
    -- Route correction: the equality case follows the same generator induction as the inequality,
    -- with the quotient step upgraded to equality by the universally catenary exact-drop argument.
    -- TODO: reuse the polynomial branch owner above, then upgrade the quotient step from
    -- `≤ ht(q') - 1` to `= ht(q') - 1` by proving the localized image of the defining prime has
    -- height `1` and applying the universally catenary exact-drop computation in the local
    -- polynomial ring. The unresolved transport is the same `κ(p)`-linear residue-field bridge as
    -- in the inequality theorem, together with the localized quotient owner.
    sorry

/-- Under the dimension-formula hypotheses, universal catenarity of `R` upgrades the inequality to
an equality. -/
theorem primeHeight_add_residueFieldTrdeg_eq_primeHeight_add_trdeg_of_universallyCatenary
    (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] (hq : q.LiesOver p) :
    ENat.toNat (Ideal.primeHeight q) +
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) =
      ENat.toNat (Ideal.primeHeight p) +
        Algebra.fractionRingTrdeg hinj :=
  by
    have hp : p = q.under R := by
      simpa using hq.over
    subst p
    simpa using
      (primeHeight_add_residueFieldTrdeg_eq_primeHeight_under_add_trdeg_of_universallyCatenary
        hinj (⟨q, inferInstance⟩ : PrimeSpectrum S))

end UniversallyCatenary

end

/-! ### Lemma_10_113_2 (from Chap10) -/
noncomputable section

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [Algebra A B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)]
  [FiniteDimensional (FractionRing A) (FractionRing B)]

/-
Domain triage:
* primary domain: finite-type maps of domains, the height-one fiber over a prime, and the induced
  fraction-ring extension;
* source-facing layer: the finite fiber `p.primesOver B` over a height-one prime and the height of
  each prime in that fiber;
* core/canonical owners sampled for this refinement:
  `FiniteDimensional (FractionRing A) (FractionRing B)`,
  `Algebra (FractionRing A) (FractionRing B)`,
  `IsScalarTower A (FractionRing A) (FractionRing B)`,
  `Ideal.primesOver`,
  `primeHeight_le_primeHeight_add_trdeg_sub_residueFieldTrdeg_of_finiteType`,
  `isMaximal_of_liesOver_of_isAlgebraic_residueField`;
* bridge/view: no extra wrapper is needed here, since the source statement already lives on the
  canonical owner set `p.primesOver B`.

Primitive data are the rings `A`, `B`, the canonical finite-dimensional fraction-field extension
`Frac(A) → Frac(B)`, and the height-one prime `p`. The injectivity of `A → B` is derived
internally from
`algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)` and the given
fraction-field tower. The public theorem is
derived API on the owner set `p.primesOver B`. -/

-- Proof sketch: first derive injectivity of `A → B` from the fraction-field tower via
-- `algebraMap_injective_of_field_isFractionRing`, then apply Lemma `10.113.1` with transcendence
-- degree `0`, since a finite extension of fraction fields is algebraic. For every `q` over `p`,
-- the dimension inequality forces
-- `primeHeight q = 1`, and the residue-field extension `κ(q) / κ(p)` is algebraic. Hence each such
-- `q` is a closed point of the fiber over `p` by Lemma `10.35.9`. The fiber is Noetherian because
-- `B` is finite type over the Noetherian ring `A`, so its prime spectrum is a Noetherian space;
-- a Noetherian space all of whose points are closed is finite, yielding finiteness of
-- `p.primesOver B`.
/-- Lemma 10.113.2: if `A → B` is a finite type map of domains, `A` is Noetherian, the induced
extension of fraction rings is finite, and `p` is a height-one prime of `A`, then there are only
finitely many prime ideals of `B` lying over `p`, and every such prime also has height one. Under
the fraction-field tower hypotheses, injectivity of `A → B` is automatic. -/
theorem finite_primesOver_and_primeHeight_eq_one_of_primeHeight_eq_one
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] (hp : Ideal.primeHeight p = 1) :
    Finite (p.primesOver B) ∧ ∀ q : p.primesOver B, Ideal.primeHeight q.1 = 1 := sorry

end
