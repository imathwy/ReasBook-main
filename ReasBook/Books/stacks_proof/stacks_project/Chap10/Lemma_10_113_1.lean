import Mathlib
import stacks_proof.stacks_project.Chap09.Lemma_9_26_5
import stacks_proof.stacks_project.Chap10.Lemma_10_46_8
import stacks_proof.stacks_project.Chap10.Lemma_10_60_13
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7
import stacks_proof.stacks_project.Chap10.Definition_10_105_3
import stacks_proof.stacks_project.Chap10.Lemma_10_105_5
import stacks_proof.stacks_project.Chap10.Lemma_10_105_10
import stacks_proof.stacks_project.Chap10.Lemma_10_113_1.Index

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Helper for Lemma 10.113.1: rewrite the canonical corresponding-prime residue-field transport
to a literal source ideal owner. -/
private noncomputable def residueField_algEquiv_of_algEquiv_of_comap_asIdeal_eq
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (Q : PrimeSpectrum B) (I : Ideal A) [I.IsPrime]
    (hI : Ideal.comap e.toRingHom Q.asIdeal = I) :
    I.ResidueField ≃ₐ[R] Q.asIdeal.ResidueField := by
  let J : Ideal A := Ideal.comap e.toRingHom Q.asIdeal
  let eSource : I.ResidueField ≃ₐ[R] J.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ I J (AlgHom.id R A) hI.symm)
      ((RingHom.surjectiveOnStalks_of_surjective (fun x ↦ ⟨x, rfl⟩)).residueFieldMap_bijective
        I J hI.symm)
  -- First rewrite the source residue field to the literal contracted ideal, then transport
  -- along the algebra equivalence to the target residue field.
  exact eSource.trans (residueField_algEquiv_of_algEquiv (R := R) e Q)

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
          exact
            Ideal.ResidueField.map_algebraMap p q.asIdeal (algebraMap A (Polynomial A)) rfl a

/-- Helper for Lemma 10.113.1: the explicit `κ(q ∩ A)`-algebra on the fiber-prime residue field
agrees with the default scalar map inherited from the polynomial fiber. -/
private lemma fiberPrime_polynomial_source_baseAlgebra_eq_default
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
    algebraMap p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField =
      ((algebraMap (p.Fiber (Polynomial A))
          (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))) := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let _ : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  -- Compare the two source scalar maps on residue classes coming from `A`.
  apply Ideal.ResidueField.ringHom_ext (I := p)
  ext a
  apply (fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q).injective
  -- Rewrite both scalar maps after transporting them to `κ(q)`.
  calc
    fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q
        (((algebraMap p.ResidueField
              (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
            (algebraMap A p.ResidueField)) a)
      = algebraMap p.ResidueField q.asIdeal.ResidueField (algebraMap A p.ResidueField a) := by
          simpa [RingHom.comp_apply] using
            (fiberPrime_residueField_equiv_source_commutes (A := A) (B := Polynomial A) q
              (algebraMap A p.ResidueField a))
    _ =
        fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q
          ((((algebraMap (p.Fiber (Polynomial A))
                (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
              (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).comp
            (algebraMap A p.ResidueField)) a) := by
          symm
          simpa [RingHom.comp_apply] using
            congrArg
              (fun f : p.ResidueField →+* q.asIdeal.ResidueField =>
                f (algebraMap A p.ResidueField a))
              (fiberPrime_polynomial_source_default_comp_commutes (A := A) q)

/-- Helper for Lemma 10.113.1: equal prime ideals in the same `K`-algebra have canonically
identified residue fields over `K`. -/
private noncomputable def residueField_algEquiv_of_eq
    {K : Type*} [CommRing K]
    {A : Type*} [CommRing A] [Algebra K A]
    (I J : Ideal A) [I.IsPrime] [J.IsPrime] (h : I = J) :
    I.ResidueField ≃ₐ[K] J.ResidueField := by
  let f : I.ResidueField →ₐ[K] J.ResidueField :=
    Ideal.ResidueField.mapₐ I J (AlgHom.id K A) (by simpa using h)
  have hbij : Function.Bijective f := by
    -- The identity map on the ambient ring is surjective on stalks, so equal prime ideals have
    -- bijective residue-field comparison maps.
    simpa [f] using
      (RingHom.surjectiveOnStalks_of_surjective (fun x ↦ ⟨x, rfl⟩)).residueFieldMap_bijective
        I J (by simpa using h)
  -- Package the bijective owner map as the desired algebra equivalence.
  exact AlgEquiv.ofBijective f hbij

/-- Helper for Lemma 10.113.1: the source fiber-prime residue field carries the same
`κ(q ∩ A)`-algebra structure whether one uses the default fiber scalar map or the explicit
source-faithful scalar map. -/
private noncomputable def fiberPrime_polynomial_source_default_residueField_id_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
    let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
    let defaultAlg : Algebra p.ResidueField RF :=
      ((algebraMap (p.Fiber (Polynomial A)) RF).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
    let explicitAlg : Algebra p.ResidueField RF :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
    @AlgEquiv p.ResidueField RF RF _ _ _ explicitAlg defaultAlg := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
  let defaultAlg : Algebra p.ResidueField RF :=
    ((algebraMap (p.Fiber (Polynomial A)) RF).comp
      (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
  let explicitAlg : Algebra p.ResidueField RF :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  -- Package the source-side scalar-map equality as the identity algebra equivalence on the same
  -- residue field.
  exact
    @AlgEquiv.ofRingEquiv p.ResidueField RF RF _ _ _ explicitAlg defaultAlg
      (f := RingEquiv.refl _)
      (fun x ↦
        DFunLike.congr_fun (fiberPrime_polynomial_source_baseAlgebra_eq_default (A := A) q) x)

/-- Helper for Lemma 10.113.1: the local-ring owner on the transported polynomial residue field
agrees with the literal `κ(q ∩ A)[X]`-owner. -/
private noncomputable def transported_polynomial_residueField_id_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let defaultAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
    let explicitAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
        Polynomial.C).toAlgebra
    @AlgEquiv p.ResidueField Q.asIdeal.ResidueField Q.asIdeal.ResidueField
      _ _ _ defaultAlg explicitAlg := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let defaultAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let explicitAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
      Polynomial.C).toAlgebra
  exact
    @AlgEquiv.ofRingEquiv p.ResidueField Q.asIdeal.ResidueField Q.asIdeal.ResidueField
      _ _ _ defaultAlg explicitAlg (f := RingEquiv.refl _)
      (fun x ↦ by
        change
          IsLocalRing.residue (Localization.AtPrime Q.asIdeal)
              (algebraMap p.ResidueField (Localization.AtPrime Q.asIdeal) x) =
            IsLocalRing.residue (Localization.AtPrime Q.asIdeal)
              (algebraMap (Polynomial p.ResidueField) (Localization.AtPrime Q.asIdeal)
                (Polynomial.C x))
        simpa using congrArg
          (IsLocalRing.residue (Localization.AtPrime Q.asIdeal))
          ((IsScalarTower.algebraMap_apply p.ResidueField
            (Polynomial p.ResidueField)
            (Localization.AtPrime Q.asIdeal) x).symm))

/-- Helper for Lemma 10.113.1: on the source fiber-prime residue field, the default local-ring
scalar map agrees with the literal scalar map coming from the fiber algebra. -/
private lemma fiberPrime_polynomial_source_local_baseAlgebra_eq_default
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
    algebraMap p.ResidueField RF =
      ((algebraMap (p.Fiber (Polynomial A)) RF).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))) := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
  let _ : Algebra p.ResidueField RF :=
    ((algebraMap (p.Fiber (Polynomial A)) RF).comp
      (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
  let _ : IsScalarTower p.ResidueField (p.Fiber (Polynomial A)) RF :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- With the explicit source owner installed, the two scalar maps agree by the tower identity.
  simpa using
    (IsScalarTower.algebraMap_eq p.ResidueField (p.Fiber (Polynomial A)) RF)

/-- Helper for Lemma 10.113.1: before reinstalling the explicit source-faithful scalar structures,
the polynomial-fiber equivalence already identifies the two residue fields over the default
`κ(q ∩ A)`-algebras. -/
private noncomputable opaque fiberPrime_polynomial_transport_default_residueField_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let sourceAlg : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
      ((algebraMap (p.Fiber (Polynomial A))
          (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
    let targetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
    @AlgEquiv p.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      Q.asIdeal.ResidueField
      _ _ _ sourceAlg targetAlg := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let eκ : p.Fiber (Polynomial A) ≃ₐ[p.ResidueField] Polynomial p.ResidueField :=
    polynomial_fiber_algEquiv_residueField_polynomial (A := A) p
  let sourceDefaultAlg :
      Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime (fiberPrimeAt A (Polynomial A) q).asIdeal)
  let targetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  have hI :
      Ideal.comap eκ.toRingHom Q.asIdeal = (fiberPrimeAt A (Polynomial A) q).asIdeal := by
    simpa [Q] using congrArg PrimeSpectrum.asIdeal
      (comap_polynomial_fiber_transport_eq_fiberPrimeAt (A := A) q)
  let eResidue :
      @AlgEquiv p.ResidueField
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        Q.asIdeal.ResidueField
        _ _ _ sourceDefaultAlg targetAlg :=
    residueField_algEquiv_of_algEquiv_of_comap_asIdeal_eq
      (R := p.ResidueField) eκ Q (fiberPrimeAt A (Polynomial A) q).asIdeal hI
  let sourceAlg :
      Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    ((algebraMap (p.Fiber (Polynomial A))
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
      (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
  let eSource :
      @AlgEquiv p.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      _ _ _ sourceAlg sourceDefaultAlg :=
    @AlgEquiv.ofRingEquiv p.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      _ _ _ sourceAlg sourceDefaultAlg
      (RingEquiv.refl _)
      (fun x ↦
        DFunLike.congr_fun
          (fiberPrime_polynomial_source_local_baseAlgebra_eq_default (A := A) q) x)
  -- First switch the source residue field from the literal fiber owner to the local-ring owner,
  -- then transport across the polynomial-fiber equivalence.
  exact eSource.trans eResidue

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

/-- Helper for Lemma 10.113.1: in the polynomial case, freeze the source-side residue-field
comparison as a literal `κ(q ∩ A)`-algebra equivalence. -/
private noncomputable def fiberPrime_polynomial_source_residueField_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let sourceAlg : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
    let targetAlg : Algebra p.ResidueField q.asIdeal.ResidueField := inferInstance
    @AlgEquiv p.ResidueField
      q.asIdeal.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      _ _ _ targetAlg sourceAlg := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let sourceAlg : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  let targetAlg : Algebra p.ResidueField q.asIdeal.ResidueField := inferInstance
  -- Freeze the contracted prime as the ideal `q ∩ A` so later `trdeg` transport does not unfold
  -- `PrimeSpectrum.comap` inside the polynomial case.
  let _ : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField := sourceAlg
  let _ : Algebra p.ResidueField q.asIdeal.ResidueField := targetAlg
  let e :
      @AlgEquiv p.ResidueField
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        q.asIdeal.ResidueField
        _ _ _ sourceAlg targetAlg :=
    fiberPrime_residueField_algEquiv_base (A := A) (B := Polynomial A) q
  exact
    @AlgEquiv.ofRingEquiv p.ResidueField
      q.asIdeal.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      _ _ _ targetAlg sourceAlg e.toRingEquiv.symm
      (fun x ↦ by
        simpa using e.symm.commutes x)

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

/-- Helper for Lemma 10.113.1: after transporting to a prime of `k[X]`, the local Krull-dimension
term is `0` at the zero prime and `1` at every nonzero prime. -/
private lemma polynomial_transport_branch_ringKrullDim_values
    {k : Type*} [Field k] (Q : PrimeSpectrum (Polynomial k)) :
    ringKrullDim (Localization.AtPrime Q.asIdeal) =
      if Q.asIdeal = ⊥ then 0 else 1 := by
  by_cases hQ : Q.asIdeal = ⊥
  · have hQbot : Q = (⊥ : PrimeSpectrum (Polynomial k)) := by
      apply PrimeSpectrum.ext
      simpa using hQ
    subst hQbot
    -- Proof comment: the zero prime localizes to the fraction field of `k[X]`, hence dimension `0`.
    simpa using polynomial_ringKrullDim_localizationAtPrime_bot_eq_zero (k := k)
  · -- Proof comment: every nonzero prime of `k[X]` is maximal, so the localization is
    -- one-dimensional.
    simpa [hQ] using
      polynomial_ringKrullDim_localizationAtPrime_eq_one_of_ne_bot (Q := Q.asIdeal) hQ

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

/-- Helper for Lemma 10.113.1: in the polynomial branch, the residue-field term can be read off
from the transported prime of `κ(q ∩ A)[X]`. -/
private lemma polynomial_source_residueFieldTrdeg_eq_branch
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
      if Q.asIdeal = ⊥ then 1 else 0 := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let sourceFaithfulAlg :
      Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  let sourceDefaultAlg :
      Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    ((algebraMap (p.Fiber (Polynomial A))
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
      (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
  let targetLocalAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let targetDefault : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
      Polynomial.C).toAlgebra
  have eSourceFaithful :
      @AlgEquiv p.ResidueField
        q.asIdeal.ResidueField
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        _ _ _ inferInstance sourceFaithfulAlg := by
    simpa [sourceFaithfulAlg] using
      fiberPrime_polynomial_source_residueField_algEquiv (A := A) q
  have eSourceDefault :
      @AlgEquiv p.ResidueField
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        _ _ _ sourceFaithfulAlg sourceDefaultAlg := by
    simpa [sourceFaithfulAlg, sourceDefaultAlg] using
      fiberPrime_polynomial_source_default_residueField_id_algEquiv (A := A) q
  have eTransport :
      @AlgEquiv p.ResidueField
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        Q.asIdeal.ResidueField
        _ _ _ sourceDefaultAlg targetLocalAlg := by
    simpa [sourceDefaultAlg, targetLocalAlg] using
      fiberPrime_polynomial_transport_default_residueField_algEquiv (A := A) q
  have eTargetOwner :
      @AlgEquiv p.ResidueField
        Q.asIdeal.ResidueField
        Q.asIdeal.ResidueField
        _ _ _ targetLocalAlg targetDefault := by
    simpa [targetLocalAlg, targetDefault] using
      transported_polynomial_residueField_id_algEquiv (A := A) q
  -- Proof comment: transport the transcendence degree along the direct `κ(q) ≃ κ(Q)` comparison,
  -- using the already-established owner changes, then read off the branch value from the
  -- transported prime in `κ(p)[X]`.
  calc
    Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField)
        = Cardinal.toNat
            (Algebra.trdeg p.ResidueField
              (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField) := by
            simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq eSourceFaithful)
    _ = Cardinal.toNat
          (Algebra.trdeg p.ResidueField
            (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField) := by
          simpa [sourceFaithfulAlg, sourceDefaultAlg] using
            congrArg Cardinal.toNat (AlgEquiv.trdeg_eq eSourceDefault)
    _ = Cardinal.toNat (Algebra.trdeg p.ResidueField Q.asIdeal.ResidueField) := by
          simpa [sourceDefaultAlg, targetLocalAlg] using
            congrArg Cardinal.toNat (AlgEquiv.trdeg_eq eTransport)
    _ = Cardinal.toNat (Algebra.trdeg p.ResidueField Q.asIdeal.ResidueField) := by
          simpa [targetLocalAlg, targetDefault] using
            congrArg Cardinal.toNat (AlgEquiv.trdeg_eq eTargetOwner)
    _ = if Q.asIdeal = ⊥ then 1 else 0 := by
          simpa using polynomial_transport_branch_trdeg_values (Q := Q)

/-- Helper for Lemma 10.113.1: in the polynomial branch, the height term is the contracted height
plus the fiber-local dimension branch value. -/
private lemma polynomial_height_eq_under_add_branch_dim
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    ENat.toNat (Ideal.primeHeight q.asIdeal) =
      ENat.toNat (Ideal.primeHeight p) + (if Q.asIdeal = ⊥ then 0 else 1) := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  have hdim :
      (((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        ((((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) +
          (if Q.asIdeal = ⊥ then 0 else 1)) := by
    calc
      (((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞)
          = ringKrullDim (Localization.AtPrime q.asIdeal) := by
              simpa using
                primeHeight_natCast_eq_ringKrullDim_localizationAtPrime (p := q.asIdeal)
      _ =
          ringKrullDim (Localization.AtPrime p) +
            ringKrullDim (fiberLocalRingAt A (Polynomial A) q) := by
              simpa using
                ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
                  (R := A) (S := Polynomial A) q
      _ =
          ringKrullDim (Localization.AtPrime p) +
            ringKrullDim (Localization.AtPrime Q.asIdeal) := by
              rw [ringKrullDim_fiberLocalRingAt_polynomial_eq_ringKrullDim_localization_transport
                (A := A) q]
      _ =
          (((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) +
            (if Q.asIdeal = ⊥ then 0 else 1) := by
              rw [primeHeight_natCast_eq_ringKrullDim_localizationAtPrime (p := p)]
              rw [polynomial_transport_branch_ringKrullDim_values (Q := Q)]
  have hsum :
      ((((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) +
          (if Q.asIdeal = ⊥ then 0 else 1)) =
        (((ENat.toNat (Ideal.primeHeight p) + (if Q.asIdeal = ⊥ then 0 else 1) : ℕ) : ℕ∞) :
          WithBot ℕ∞) := by
    by_cases hQ : Q.asIdeal = ⊥
    · simp [hQ]
    · simp [hQ]
  -- Convert the normalized `WithBot ℕ∞` equality back to the intended natural-number statement.
  exact_mod_cast (hdim.trans hsum)

/-- Helper for Lemma 10.113.1: if one element `x` generates `S` over `R`, then the evaluation map
`R[X] → S` at `x` is surjective. -/
private lemma single_generator_aeval_surjective_of_adjoin_singleton_eq_top
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) :
    Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] B) := by
  -- The source route starts from the standard one-generator presentation `B = A[X] / ker(aeval x)`.
  exact
    (AlgHom.range_eq_top _).mp
      ((Algebra.adjoin_singleton_eq_range_aeval A x).symm.trans hx)

/-- Helper for Lemma 10.113.1: universal catenarity upgrades the nonzero-kernel quotient branch to
an equality of prime heights. -/
private lemma single_generator_quotient_case_primeHeight_succ_eq_comap_primeHeight_of_universallyCatenary
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [Algebra A B] [UniversallyCatenaryRing A]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    n ≠ ⊥ →
      ENat.toNat (Ideal.primeHeight q.asIdeal) + 1 =
        ENat.toNat (Ideal.primeHeight q'.asIdeal) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let L := Localization.AtPrime q'.asIdeal
  let K : Ideal L := Ideal.map (algebraMap (Polynomial A) L) n
  intro hn
  let e :
      Localization.AtPrime q.asIdeal ≃ₐ[A] (L ⧸ K) :=
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    let hφ_surj : Function.Surjective φ :=
      single_generator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
    let hφloc_surj : Function.Surjective φloc := by
      -- Localizing a surjective map at corresponding primes stays surjective on the local rings.
      simpa [φloc, Localization.localAlgHom] using
        (RingHom.surjectiveOnStalks_of_surjective hφ_surj).localRingHom_surjective
          q'.asIdeal q.asIdeal rfl
    let hprimeCompl :
        Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
      -- The localized source and target use the corresponding prime complements.
      ext f
      simp [q', Ideal.mem_primeCompl, Ideal.mem_comap]
    let hker :
        RingHom.ker φloc.toRingHom = K := by
      -- The kernel of the localized map is exactly the localization of the original kernel.
      dsimp [φloc, K, n]
      simpa [Localization.localAlgHom, Localization.localRingHom] using
        (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
          φ.toRingHom hprimeCompl)
    -- Repackage the localized surjection as the quotient by its kernel, then rewrite that kernel to
    -- the literal localized ideal `K`.
    (Ideal.quotientKerAlgEquivOfSurjective hφloc_surj).symm.trans
      (Ideal.quotientEquivAlgOfEq L hker)
  letI : UniversallyCatenaryRing (Polynomial A) :=
    universallyCatenaryRing_of_finiteType (A := A) (S := Polynomial A)
  letI : UniversallyCatenaryRing L := localization_universallyCatenaryRing q'.asIdeal.primeCompl
  have hK :
      Ideal.primeHeight K = 1 := by
    have hn_prime : n.IsPrime := by
      dsimp [n]
      exact RingHom.ker_isPrime φ.toRingHom
    letI : n.IsPrime := hn_prime
    have hK_prime : K.IsPrime := by
      let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
        Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
      have hprimeCompl :
          Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
        -- The localized source and target use the corresponding prime complements.
        ext f
        simp [q', Ideal.mem_primeCompl, Ideal.mem_comap]
      have hker :
          RingHom.ker φloc.toRingHom = K := by
        -- Localization turns `ker φ` into the literal localized kernel ideal `K`.
        dsimp [φloc, K, n]
        simpa [Localization.localAlgHom, Localization.localRingHom] using
          (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
            φ.toRingHom hprimeCompl)
      rw [← hker]
      exact RingHom.ker_isPrime φloc.toRingHom
    letI : K.IsPrime := hK_prime
    have hcomap :
        Ideal.comap (algebraMap (Polynomial A) L) K = n := by
      have hn_le : n ≤ q'.asIdeal := by
        intro f hf
        change f ∈ Ideal.comap φ.toRingHom q.asIdeal
        rw [Ideal.mem_comap]
        have hzero : φ f = 0 := by
          simpa [n, RingHom.mem_ker] using hf
        simpa [hzero] using (show (0 : B) ∈ q.asIdeal from Ideal.zero_mem _)
      have hdisj : Disjoint (q'.asIdeal.primeCompl : Set (Polynomial A)) n := by
        simpa [Set.disjoint_iff, Set.ext_iff, not_imp_comm] using hn_le
      -- Contracting the localized kernel back to `A[X]` recovers the original kernel.
      simpa [K] using
        (IsLocalization.comap_map_of_isPrime_disjoint q'.asIdeal.primeCompl L hn_prime hdisj)
    have hbot_height : (⊥ : Ideal A).height = 0 := by
      -- In a domain, the zero ideal is the unique minimal prime.
      have hbot_primeHeight : (⊥ : Ideal A).primeHeight = 0 := by
        rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
        simp
      simpa [Ideal.height_eq_primeHeight] using hbot_primeHeight
    have hunder : n.under A = (⊥ : Ideal A) := by
      ext a
      -- The kernel on constants is exactly the kernel of `A → B`, which is zero by injectivity.
      change φ (Polynomial.C a) = 0 ↔ a ∈ (⊥ : Ideal A)
      constructor
      · intro ha
        exact hinj <| by simpa [φ] using ha
      · intro ha
        simpa [φ] using ha
    have hheight :
        K.height = 1 := by
      calc
        K.height = (Ideal.comap (algebraMap (Polynomial A) L) K).height := by
          symm
          exact IsLocalization.height_comap q'.asIdeal.primeCompl K
        _ = n.height := by rw [hcomap]
        _ = (⊥ : Ideal A).height + 1 := by
          letI : n.LiesOver (⊥ : Ideal A) := by
            refine ⟨?_⟩
            change n.under A = (⊥ : Ideal A)
            exact hunder
          simpa using (Polynomial.height_eq_height_add_one (p := (⊥ : Ideal A)) (P := n))
        _ = 1 := by simp [hbot_height]
    -- Rewrite the computed height back to prime height.
    simpa [Ideal.height_eq_primeHeight] using hheight
  have hdrop :
      ringKrullDim (L ⧸ K) + 1 = ringKrullDim L :=
    -- Route correction: call the extracted Case II exact-drop owner directly to avoid one more
    -- layer of target-file elaboration.
    ringKrullDim_quotient_add_eq_of_primeHeight_one_catenary_local_domain (L := L) K hK
  have hlocal :
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1 =
        ringKrullDim (Localization.AtPrime q'.asIdeal) := by
    -- Transport the exact one-step quotient drop back through the localized presentation.
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1
          = ringKrullDim (L ⧸ K) + 1 := by
              rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
      _ = ringKrullDim L := hdrop
      _ = ringKrullDim (Localization.AtPrime q'.asIdeal) := by
            rfl
  have hheight :
      ((((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) + 1) =
        (((ENat.toNat (Ideal.primeHeight q'.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    -- Rewrite both local dimensions as prime heights.
    rw [primeHeight_natCast_eq_ringKrullDim_localizationAtPrime (p := q.asIdeal)]
    simpa [L] using hlocal
  exact_mod_cast hheight

/-- Helper for Lemma 10.113.1: for the one-generator evaluation map `A[X] → B`, contracting a
prime `q` first to `A[X]` and then to `A` gives the same source prime as contracting `q`
directly to `A`. -/
private lemma single_generator_comap_under_eq
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    q'.asIdeal.under A = q.asIdeal.under A := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  ext a
  -- Proof comment: the `A`-algebra structure on `A[X]` is given by `Polynomial.C`, and
  -- `aeval x` sends `Polynomial.C a` to the original scalar `a` in `B`.
  change Polynomial.C a ∈ Ideal.comap φ.toRingHom q.asIdeal ↔ algebraMap A B a ∈ q.asIdeal
  rw [Ideal.mem_comap]
  simp [φ]

/-- Helper for Lemma 10.113.1: for the surjective one-generator presentation `A[X] → B`, the
induced map on residue fields at corresponding primes is bijective. -/
private lemma single_generator_residueFieldMap_bijective_of_surjective_aeval
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    Function.Bijective (Ideal.ResidueField.map q'.asIdeal q.asIdeal φ rfl) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  have hsurj : Function.Surjective φ :=
    single_generator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
  -- Proof comment: the surjective evaluation map is surjective on stalks, so the residue fields
  -- at corresponding primes are identified bijectively.
  exact (RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective _ _ rfl

/-- Helper for Lemma 10.113.1: in the one-generator quotient presentation, the residue-field
transcendence-degree term is unchanged after transporting `q` back to the corresponding polynomial
prime `q'`. -/
private lemma single_generator_residueFieldTrdeg_eq_comap_of_surjective_aeval
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let e :
      q'.asIdeal.ResidueField ≃ₐ[(q'.asIdeal.under A).ResidueField] q.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ q'.asIdeal q.asIdeal φ rfl)
      (single_generator_residueFieldMap_bijective_of_surjective_aeval
        (A := A) (B := B) x hx q)
  have hunder : q'.asIdeal.under A = q.asIdeal.under A :=
    single_generator_comap_under_eq (A := A) (B := B) x q
  -- Proof comment: first rewrite the polynomial-side base residue field to the literal source
  -- residue field `κ(q ∩ A)`, then transport the target residue field along the canonical
  -- corresponding-prime equivalence.
  calc
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField)
        = Cardinal.toNat (Algebra.trdeg (q'.asIdeal.under A).ResidueField q.asIdeal.ResidueField) := by
            simpa [hunder]
    _ = Cardinal.toNat (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
          simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq e).symm

/-- Helper for Lemma 10.113.1: in the injective one-generator branch, the generic fraction-field
transcendence degree is `1`. -/
private lemma single_generator_fractionRingTrdeg_eq_one_of_ker_eq_bot
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
    n = ⊥ →
      Algebra.fractionRingTrdeg hinj = 1 := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  intro hker
  have hφ_surj : Function.Surjective φ :=
    single_generator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
  have hφ_inj : Function.Injective φ := by
    -- The zero-kernel branch is exactly the transcendental polynomial case.
    rw [RingHom.injective_iff_ker_eq_bot]
    simpa [φ, n] using hker
  let e : Polynomial A ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  let eFrac : FractionRing (Polynomial A) ≃ₐ[A] FractionRing B :=
    IsFractionRing.algEquivOfAlgEquiv e
  let _ : FaithfulSMul A (Polynomial A) :=
    (faithfulSMul_iff_algebraMap_injective A (Polynomial A)).mpr (by
      simpa using (Polynomial.C_injective (R := A)))
  let _ : FaithfulSMul (Polynomial A) (FractionRing (Polynomial A)) :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial A)
      (FractionRing (Polynomial A))).mpr
      (IsFractionRing.injective (Polynomial A) (FractionRing (Polynomial A)))
  let _ : FaithfulSMul A (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective A (FractionRing A)).mpr
      (IsFractionRing.injective A (FractionRing A))
  have hfrac_poly :
      Algebra.trdeg (Polynomial A) (FractionRing (Polynomial A)) = 0 := by
    -- Passing from a domain to its fraction field adds no transcendence.
    simpa using
      (trdeg_eq_zero :
        Algebra.trdeg (Polynomial A) (FractionRing (Polynomial A)) = 0)
  have hpoly_frac :
      Algebra.trdeg A (FractionRing (Polynomial A)) = 1 := by
    -- Compute the polynomial fraction field over `A` by the tower
    -- `A ⟶ A[X] ⟶ Frac(A[X])`.
    have hsum := trdeg_add_eq (R := A) (S := Polynomial A)
      (A := FractionRing (Polynomial A))
    rw [Polynomial.trdeg_of_isDomain, hfrac_poly] at hsum
    simpa using hsum.symm
  have hA_fracA :
      Algebra.trdeg A (FractionRing A) = 0 := by
    let _ : Algebra.IsAlgebraic A (FractionRing A) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
          (C := FractionRing A)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing A))
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing A) = 0)
  have hA_fracB :
      Algebra.trdeg A (FractionRing B) = 1 := by
    -- Transport the computation from `Frac(A[X])` to `Frac(B)` along the polynomial
    -- presentation.
    calc
      Algebra.trdeg A (FractionRing B)
          = Algebra.trdeg A (FractionRing (Polynomial A)) := by
              simpa using (AlgEquiv.trdeg_eq (R := A) eFrac).symm
      _ = 1 := hpoly_frac
  have hFrac :
      Algebra.trdeg (FractionRing A) (FractionRing B) = 1 := by
    -- The base change `A ⟶ Frac(A)` is algebraic, so it does not alter the generic
    -- transcendence degree.
    have hsum := trdeg_add_eq (R := A) (S := FractionRing A) (A := FractionRing B)
    rw [hA_fracA, hA_fracB] at hsum
    simpa using hsum
  change Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 1
  simpa [hFrac] using rfl

/-- Helper for Lemma 10.113.1: in the nonzero-kernel one-generator branch, the generic
fraction-field transcendence degree is `0`. -/
private lemma single_generator_fractionRingTrdeg_eq_zero_of_ker_ne_bot
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
    n ≠ ⊥ →
      Algebra.fractionRingTrdeg hinj = 0 := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  intro hker
  let _ : FaithfulSMul A (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective A (FractionRing A)).mpr
      (IsFractionRing.injective A (FractionRing A))
  have hx_alg : IsAlgebraic A x := by
    -- A nonzero relation in `ker(aeval x)` makes `x` algebraic over `A`.
    rw [isAlgebraic_iff_not_injective]
    intro hφ_inj
    apply hker
    rw [RingHom.injective_iff_ker_eq_bot] at hφ_inj
    simpa [φ, n] using hφ_inj
  have hB_alg : Algebra.IsAlgebraic A B := by
    -- Since `B = A[x]`, algebraicity of the single generator makes the whole algebra
    -- algebraic.
    rw [← hx]
    refine (Algebra.isAlgebraic_adjoin_iff (R := A) (s := ({x} : Set B))).2 ?_
    intro y hy
    simpa [Set.mem_singleton_iff.mp hy] using hx_alg
  have hA_fracB :
      Algebra.trdeg A (FractionRing B) = 0 := by
    let _ : Algebra.IsAlgebraic A B := hB_alg
    let _ : Algebra.IsAlgebraic B (FractionRing B) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := B) (K := FractionRing B)
          (C := FractionRing B)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing B) (FractionRing B))
    let _ : Algebra.IsAlgebraic A (FractionRing B) :=
      Algebra.IsAlgebraic.trans (R := A) (S := B) (A := FractionRing B)
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing B) = 0)
  have hA_fracA :
      Algebra.trdeg A (FractionRing A) = 0 := by
    let _ : Algebra.IsAlgebraic A (FractionRing A) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
          (C := FractionRing A)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing A))
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing A) = 0)
  have hFrac :
      Algebra.trdeg (FractionRing A) (FractionRing B) = 0 := by
    -- Again, the algebraic base change `A ⟶ Frac(A)` leaves the generic term unchanged.
    have hsum := trdeg_add_eq (R := A) (S := FractionRing A) (A := FractionRing B)
    rw [hA_fracA, hA_fracB] at hsum
    simpa using hsum
  change Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 0
  simpa [hFrac] using rfl

/-- Helper for Lemma 10.113.1: in the universally catenary case, the one-generator source proof
closes with equality in both the polynomial and quotient branches. -/
private lemma single_generator_primeHeight_residueFieldTrdeg_eq_of_universallyCatenary
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [Algebra A B] [UniversallyCatenaryRing A]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) (q : PrimeSpectrum B) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) +
        Algebra.fractionRingTrdeg hinj := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  by_cases hker : n = ⊥
  · have hgeneric :
        Algebra.fractionRingTrdeg hinj = 1 :=
      single_generator_fractionRingTrdeg_eq_one_of_ker_eq_bot
        (A := A) (B := B) x hx hinj hker
    have hφ_surj : Function.Surjective φ :=
      single_generator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
    have hφ_inj : Function.Injective φ := by
      rw [RingHom.injective_iff_ker_eq_bot]
      simpa [φ, n] using hker
    let e : Polynomial A ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    have hheight :
        ENat.toNat (Ideal.primeHeight q'.asIdeal) =
          ENat.toNat (Ideal.primeHeight q.asIdeal) := by
      -- In the polynomial branch, `q'` and `q` correspond under the presentation equivalence.
      have hheight_eq : q'.asIdeal.height = q.asIdeal.height := by
        simpa [q', e, φ] using
          (RingEquiv.height_comap e.toRingEquiv q.asIdeal)
      simpa [Ideal.height_eq_primeHeight] using hheight_eq
    have hres :
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          Cardinal.toNat
            (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) :=
      single_generator_residueFieldTrdeg_eq_comap_of_surjective_aeval
        (A := A) (B := B) x hx q
    have hunder : q'.asIdeal.under A = q.asIdeal.under A :=
      single_generator_comap_under_eq (A := A) (B := B) x q
    -- The zero-kernel branch is exactly the polynomial equality from the source.
    calc
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField)
        = ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
                rw [← hheight, hres]
      _ = ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) + 1 := by
            let p' : Ideal A := q'.asIdeal.under A
            let _ : p'.IsPrime := inferInstance
            let Q' : PrimeSpectrum (Polynomial p'.ResidueField) :=
              fiberPrime_polynomial_transport (A := A) q'
            have hheight' :
                ENat.toNat (Ideal.primeHeight q'.asIdeal) =
                  ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) +
                    (if Q'.asIdeal = ⊥ then 0 else 1) := by
              simpa [p', Q'] using polynomial_height_eq_under_add_branch_dim (A := A) q'
            have htrdeg' :
                Cardinal.toNat
                    (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) =
                  if Q'.asIdeal = ⊥ then 1 else 0 := by
              simpa [p', Q'] using polynomial_source_residueFieldTrdeg_eq_branch (A := A) q'
            exact polynomial_branch_values_sum_eq_one hheight' htrdeg'
      _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
            rw [hunder]
      _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) +
            Algebra.fractionRingTrdeg hinj := by
              simpa [hgeneric]
  · have hgeneric :
        Algebra.fractionRingTrdeg hinj = 0 :=
      single_generator_fractionRingTrdeg_eq_zero_of_ker_ne_bot
        (A := A) (B := B) x hx hinj hker
    have hres :
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          Cardinal.toNat
            (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) :=
      single_generator_residueFieldTrdeg_eq_comap_of_surjective_aeval
        (A := A) (B := B) x hx q
    have hheight :
        ENat.toNat (Ideal.primeHeight q.asIdeal) + 1 =
          ENat.toNat (Ideal.primeHeight q'.asIdeal) :=
      single_generator_quotient_case_primeHeight_succ_eq_comap_primeHeight_of_universallyCatenary
        (A := A) (B := B) x hx hinj q hker
    have hpoly :
        ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
      -- Route correction: rewrite the residue-field term back to the polynomial antecedent `q'`
      -- and then apply the polynomial branch equality.
      calc
        ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField)
          = ENat.toNat (Ideal.primeHeight q'.asIdeal) +
              Cardinal.toNat
                (Algebra.trdeg (q'.asIdeal.under A).ResidueField
                  q'.asIdeal.ResidueField) := by
                    rw [hres]
        _ = ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) + 1 := by
              let p' : Ideal A := q'.asIdeal.under A
              let _ : p'.IsPrime := inferInstance
              let Q' : PrimeSpectrum (Polynomial p'.ResidueField) :=
                fiberPrime_polynomial_transport (A := A) q'
              have hheight' :
                  ENat.toNat (Ideal.primeHeight q'.asIdeal) =
                    ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) +
                      (if Q'.asIdeal = ⊥ then 0 else 1) := by
                simpa [p', Q'] using polynomial_height_eq_under_add_branch_dim (A := A) q'
              have htrdeg' :
                  Cardinal.toNat
                      (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) =
                    if Q'.asIdeal = ⊥ then 1 else 0 := by
                simpa [p', Q'] using polynomial_source_residueFieldTrdeg_eq_branch (A := A) q'
              exact polynomial_branch_values_sum_eq_one hheight' htrdeg'
        _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
              rw [single_generator_comap_under_eq (A := A) (B := B) x q]
    have hgoal :
        ENat.toNat (Ideal.primeHeight q.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) := by
      omega
    simpa [hgeneric] using hgoal

/-- Helper for Lemma 10.113.1: in the one-generator quotient case with nonzero kernel, the prime
height at `q` is at least one less than the height of its polynomial antecedent `q'`. -/
private lemma single_generator_quotient_case_primeHeight_succ_le_comap_primeHeight
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    n ≠ ⊥ →
      ENat.toNat (Ideal.primeHeight q.asIdeal) + 1 ≤
        ENat.toNat (Ideal.primeHeight q'.asIdeal) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let L := Localization.AtPrime q'.asIdeal
  let K : Ideal L := Ideal.map (algebraMap (Polynomial A) L) n
  intro hn
  let e :
      Localization.AtPrime q.asIdeal ≃ₐ[A] (L ⧸ K) :=
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    let hφ_surj : Function.Surjective φ :=
      single_generator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
    let hφloc_surj : Function.Surjective φloc := by
      -- Localizing a surjective map at corresponding primes stays surjective on the local rings.
      simpa [φloc, Localization.localAlgHom] using
        (RingHom.surjectiveOnStalks_of_surjective hφ_surj).localRingHom_surjective
          q'.asIdeal q.asIdeal rfl
    let hprimeCompl :
        Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
      -- The localized source and target use the corresponding prime complements.
      ext f
      simp [q', Ideal.mem_primeCompl, Ideal.mem_comap]
    let hker :
        RingHom.ker φloc.toRingHom = K := by
      -- The kernel of the localized map is exactly the localization of the original kernel.
      dsimp [φloc, K, n]
      simpa [Localization.localAlgHom, Localization.localRingHom] using
        (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
          φ.toRingHom hprimeCompl)
    -- Repackage the localized surjection as the quotient by its kernel, then rewrite that kernel to
    -- the literal localized ideal `K`.
      (Ideal.quotientKerAlgEquivOfSurjective hφloc_surj).symm.trans
      (Ideal.quotientEquivAlgOfEq L hker)
  have hdrop :
      ringKrullDim (L ⧸ K) + 1 ≤ ringKrullDim L := by
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    have hprimeCompl :
        Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
      -- The local source and target are localized at the corresponding primes of `aeval x`.
      ext f
      simp [q', Ideal.mem_primeCompl, Ideal.mem_comap]
    have hker :
        RingHom.ker φloc.toRingHom = K := by
      -- Localization turns `ker φ` into the localized ideal `K`.
      dsimp [φloc, K, n]
      simpa [Localization.localAlgHom, Localization.localRingHom] using
        (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
          φ.toRingHom hprimeCompl)
    have hK_prime : K.IsPrime := by
      -- The kernel of a map to the domain `B_q` is prime, hence so is `K`.
      rw [← hker]
      exact RingHom.ker_isPrime φloc.toRingHom
    have hK_ne_bot : K ≠ ⊥ := by
      -- The localization map is injective on the domain `A[X]`, so a nonzero kernel element stays
      -- nonzero after localization.
      have hL_inj : Function.Injective (algebraMap (Polynomial A) L) :=
        IsLocalization.injective L q'.asIdeal.primeCompl_le_nonZeroDivisors
      exact (Ideal.map_eq_bot_iff_of_injective hL_inj).not.mpr hn
    let P : PrimeSpectrum L := ⟨K, hK_prime⟩
    let _ : Nonempty (PrimeSpectrum L) := ⟨P⟩
    have hP_bot : (⊥ : PrimeSpectrum L) < P := by
      change (⊥ : Ideal L) < K
      exact bot_lt_iff_ne_bot.mpr hK_ne_bot
    have hheight_pos : 1 ≤ Order.height P := by
      simpa using Order.height_pos_of_bot_lt hP_bot
    have hquot :
        ringKrullDim (L ⧸ K) = Order.coheight P := by
      -- Quotient Krull dimension is the coheight of the corresponding prime.
      rw [ringKrullDim_quotient]
      have hzero : PrimeSpectrum.zeroLocus (K : Set L) = Set.Ici P := by
        ext r
        change K ≤ r.asIdeal ↔ P ≤ r
        rfl
      rw [hzero]
      exact (Order.coheight_eq_krullDim_Ici P).symm
    have hsum :
        (((Order.coheight P + 1 : ℕ∞)) : WithBot ℕ∞) ≤
          (((Order.height P + Order.coheight P : ℕ∞)) : WithBot ℕ∞) := by
      -- A nonzero prime has positive height, so its height-plus-coheight term dominates
      -- `coheight + 1`.
      exact_mod_cast
        (show Order.coheight P + 1 ≤ Order.height P + Order.coheight P by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hheight_pos (Order.coheight P))
    have hdim :
        (((Order.height P + Order.coheight P : ℕ∞)) : WithBot ℕ∞) ≤ ringKrullDim L := by
      -- The ambient Krull dimension dominates the height-plus-coheight of every prime.
      rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
      exact WithBot.coe_le_coe.mpr
        (le_iSup (fun r : PrimeSpectrum L ↦ Order.height r + Order.coheight r) P)
    calc
      ringKrullDim (L ⧸ K) + 1
          = (((Order.coheight P + 1 : ℕ∞)) : WithBot ℕ∞) := by
              rw [hquot]
              simp
      _ ≤ (((Order.height P + Order.coheight P : ℕ∞)) : WithBot ℕ∞) := hsum
      _ ≤ ringKrullDim L := hdim
  have hlocal :
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1 ≤
        ringKrullDim (Localization.AtPrime q'.asIdeal) := by
    -- Transport the quotient-side local dimension drop back to `B_q`.
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1
          = ringKrullDim (L ⧸ K) + 1 := by
              rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
      _ ≤ ringKrullDim L := hdrop
      _ = ringKrullDim (Localization.AtPrime q'.asIdeal) := by
            rfl
  have hheight :
      ((((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) + 1) ≤
        (((ENat.toNat (Ideal.primeHeight q'.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    -- Rewrite both local dimensions as prime heights.
    rw [primeHeight_natCast_eq_ringKrullDim_localizationAtPrime (p := q.asIdeal)]
    simpa [L] using hlocal
  -- Convert the cast inequality back to natural numbers.
  exact_mod_cast hheight

/-- Helper for Lemma 10.113.1: if `q` lies over `p` and the source ring map is surjective on
stalks, then the induced map `κ(p) → κ(q)` is bijective. -/
private lemma bijective_algebraMap_residueField_of_surjectiveOnStalks
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hsurj : (algebraMap A B).SurjectiveOnStalks) :
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := by
  have hmap :
      Ideal.ResidueField.map p q (algebraMap A B) (Ideal.over_def q p) =
        algebraMap p.ResidueField q.ResidueField := by
    -- Compare the canonical owner map with the default algebra map out of `κ(p)`.
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext a
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap]
    calc
      algebraMap B q.ResidueField (algebraMap A B a) = algebraMap A q.ResidueField a := by
        rw [IsScalarTower.algebraMap_apply A B q.ResidueField a]
      _ = algebraMap p.ResidueField q.ResidueField (algebraMap A p.ResidueField a) := by
        rw [IsScalarTower.algebraMap_apply A p.ResidueField q.ResidueField a]
  -- Surjective-on-stalks then upgrades the owner residue-field map to a bijection.
  simpa [hmap] using hsurj.residueFieldMap_bijective p q (Ideal.over_def q p)

/-- Helper for Lemma 10.113.1: the one-generator case follows the source split into the
polynomial branch and the nonzero-kernel quotient branch. -/
private lemma single_generator_primeHeight_residueFieldTrdeg_le
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) (q : PrimeSpectrum B) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) +
        Algebra.fractionRingTrdeg hinj := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  by_cases hker : n = ⊥
  · have hgeneric :
        Algebra.fractionRingTrdeg hinj = 1 :=
      single_generator_fractionRingTrdeg_eq_one_of_ker_eq_bot
        (A := A) (B := B) x hx hinj hker
    have hφ_surj : Function.Surjective φ :=
      single_generator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
    have hφ_inj : Function.Injective φ := by
      rw [RingHom.injective_iff_ker_eq_bot]
      simpa [φ, n] using hker
    let e : Polynomial A ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    have hheight :
        ENat.toNat (Ideal.primeHeight q'.asIdeal) =
          ENat.toNat (Ideal.primeHeight q.asIdeal) := by
      -- In the polynomial branch, `q'` and `q` correspond under a ring equivalence.
      have hheight_eq : q'.asIdeal.height = q.asIdeal.height := by
        simpa [q', e, φ] using
          (RingEquiv.height_comap e.toRingEquiv q.asIdeal)
      simpa [Ideal.height_eq_primeHeight] using hheight_eq
    have hres :
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          Cardinal.toNat
            (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) :=
      single_generator_residueFieldTrdeg_eq_comap_of_surjective_aeval
        (A := A) (B := B) x hx q
    -- The zero-kernel branch is exactly the polynomial case from the source.
    have hpoly :
        ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) =
          ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) + 1 := by
      let p' : Ideal A := q'.asIdeal.under A
      let _ : p'.IsPrime := inferInstance
      let Q' : PrimeSpectrum (Polynomial p'.ResidueField) :=
        fiberPrime_polynomial_transport (A := A) q'
      have hheight' :
          ENat.toNat (Ideal.primeHeight q'.asIdeal) =
            ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) +
              (if Q'.asIdeal = ⊥ then 0 else 1) := by
        simpa [p', Q'] using polynomial_height_eq_under_add_branch_dim (A := A) q'
      have htrdeg' :
          Cardinal.toNat
              (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) =
            if Q'.asIdeal = ⊥ then 1 else 0 := by
        simpa [p', Q'] using polynomial_source_residueFieldTrdeg_eq_branch (A := A) q'
      exact polynomial_branch_values_sum_eq_one hheight' htrdeg'
    have hunder : q'.asIdeal.under A = q.asIdeal.under A :=
      single_generator_comap_under_eq (A := A) (B := B) x q
    apply le_of_eq
    calc
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField)
        = ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
                rw [← hheight, hres]
      _ = ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) + 1 := hpoly
      _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by rw [hunder]
      _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) +
            Algebra.fractionRingTrdeg hinj := by simpa [hgeneric]
  · have hgeneric :
        Algebra.fractionRingTrdeg hinj = 0 :=
      single_generator_fractionRingTrdeg_eq_zero_of_ker_ne_bot
        (A := A) (B := B) x hx hinj hker
    have hres :
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          Cardinal.toNat
            (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) :=
      single_generator_residueFieldTrdeg_eq_comap_of_surjective_aeval
        (A := A) (B := B) x hx q
    have hheight :
        ENat.toNat (Ideal.primeHeight q.asIdeal) + 1 ≤
          ENat.toNat (Ideal.primeHeight q'.asIdeal) :=
      single_generator_quotient_case_primeHeight_succ_le_comap_primeHeight
        (A := A) (B := B) x hx q hker
    have hpoly :
        ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
      -- Route correction: after rewriting the residue-field term back to the polynomial
      -- antecedent `q'`, the quotient case is the source Case II arithmetic.
      calc
        ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField)
          = ENat.toNat (Ideal.primeHeight q'.asIdeal) +
              Cardinal.toNat
                (Algebra.trdeg (q'.asIdeal.under A).ResidueField
                  q'.asIdeal.ResidueField) := by rw [hres]
        _ = ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) + 1 := by
              let p' : Ideal A := q'.asIdeal.under A
              let _ : p'.IsPrime := inferInstance
              let Q' : PrimeSpectrum (Polynomial p'.ResidueField) :=
                fiberPrime_polynomial_transport (A := A) q'
              have hheight' :
                  ENat.toNat (Ideal.primeHeight q'.asIdeal) =
                    ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) +
                      (if Q'.asIdeal = ⊥ then 0 else 1) := by
                simpa [p', Q'] using polynomial_height_eq_under_add_branch_dim (A := A) q'
              have htrdeg' :
                  Cardinal.toNat
                      (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) =
                    if Q'.asIdeal = ⊥ then 1 else 0 := by
                simpa [p', Q'] using polynomial_source_residueFieldTrdeg_eq_branch (A := A) q'
              exact polynomial_branch_values_sum_eq_one hheight' htrdeg'
        _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
              rw [single_generator_comap_under_eq (A := A) (B := B) x q]
    have hgoal :
        ENat.toNat (Ideal.primeHeight q.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) ≤
          ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) := by
      omega
    simpa [hgeneric] using hgoal

/-- Helper for Lemma 10.113.1: the structure map into a finite adjoin stage stays injective once
the ambient map `R → S` is injective. -/
private lemma adjoin_finset_algebraMap_injective
    (hinj : Function.Injective (algebraMap R S)) (s : Finset S) :
    Function.Injective (algebraMap R (Algebra.adjoin R (s : Set S))) := by
  -- The stage inclusion into `S` is injective, so equality in the stage can be checked in `S`.
  intro x y hxy
  apply hinj
  change (((algebraMap R (Algebra.adjoin R (s : Set S)) x :
      Algebra.adjoin R (s : Set S)) : S)) =
    (((algebraMap R (Algebra.adjoin R (s : Set S)) y :
      Algebra.adjoin R (s : Set S)) : S))
  simpa using congrArg (fun z : Algebra.adjoin R (s : Set S) => (z : S)) hxy

/-- Helper for Lemma 10.113.1: a finite adjoin stage is finitely generated, hence finite type,
over the source ring. -/
private lemma adjoin_finset_finiteType (s : Finset S) :
    Algebra.FiniteType R (Algebra.adjoin R (s : Set S)) := by
  let T : Subalgebra R S := Algebra.adjoin R (s : Set S)
  have hfg : T.FG := by
    -- The stage is literally generated by the finite set `s`.
    exact Subalgebra.fg_def.2 ⟨(s : Set S), s.finite_toSet, rfl⟩
  have hfgTop : (⊤ : Subalgebra R T).FG := (Subalgebra.fg_top T).2 hfg
  have hftTop : Algebra.FiniteType R (⊤ : Subalgebra R T) :=
    (Subalgebra.fg_iff_finiteType (⊤ : Subalgebra R T)).mp hfgTop
  -- Transfer finite type from the top subalgebra of the stage back to the stage itself.
  exact Algebra.FiniteType.equiv hftTop Subalgebra.topEquiv

/-- Helper for Lemma 10.113.1: finite adjoin stages over a Noetherian domain are themselves
Noetherian domains. -/
private lemma adjoin_finset_isNoetherianRing [IsNoetherianRing R] (s : Finset S) :
    IsNoetherianRing (Algebra.adjoin R (s : Set S)) := by
  let T : Subalgebra R S := Algebra.adjoin R (s : Set S)
  have hfg : T.FG := by
    -- Again, the chosen finite set already presents the stage as an adjoin.
    exact Subalgebra.fg_def.2 ⟨(s : Set S), s.finite_toSet, rfl⟩
  exact Subalgebra.isNoetherianRing_of_fg hfg

/-- Helper for Lemma 10.113.1: an essentially finite type field extension has finite
transcendence degree. -/
private lemma trdeg_lt_aleph0_of_essFiniteType_field
    {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L] :
    Algebra.trdeg K L < Cardinal.aleph0 := by
  obtain ⟨t, ht⟩ := IntermediateField.fg_top K L
  have ht_alg : Algebra.IsAlgebraic (Algebra.adjoin K (t : Set L)) L := by
    -- Once the generated intermediate field is all of `L`, the top extension is algebraic.
    rw [← isAlgebraic_adjoin_iff_top, ht, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  -- The transcendence degree is bounded by the chosen finite generating set.
  exact
    lt_of_le_of_lt
      (Algebra.IsAlgebraic.trdeg_le_cardinalMk K (t : Set L))
      (by simpa using t.finite_toSet.lt_aleph0)

/-- Helper for Lemma 10.113.1: along a tower of finite-type domain extensions, the generic
fraction-field transcendence degree is additive. -/
private lemma fractionRingTrdeg_tower_eq
    {T : Type*} {U : Type*}
    [CommRing T] [CommRing U] [IsDomain T] [IsDomain U]
    [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    [Algebra.FiniteType R T] [Algebra.FiniteType T U]
    (hinjRT : Function.Injective (algebraMap R T))
    (hinjTU : Function.Injective (algebraMap T U))
    (hinjRU : Function.Injective (algebraMap R U)) :
    Algebra.fractionRingTrdeg (R := R) (S := U) hinjRU =
      Algebra.fractionRingTrdeg (R := R) (S := T) hinjRT +
        Algebra.fractionRingTrdeg (R := T) (S := U) hinjTU := by
  let _ : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr hinjRT
  let _ : FaithfulSMul T U := (faithfulSMul_iff_algebraMap_injective T U).mpr hinjTU
  let _ : FaithfulSMul R U := (faithfulSMul_iff_algebraMap_injective R U).mpr hinjRU
  letI : Algebra.EssFiniteType R (FractionRing T) := Algebra.EssFiniteType.comp R T (FractionRing T)
  letI : Algebra.EssFiniteType T (FractionRing U) := Algebra.EssFiniteType.comp T U (FractionRing U)
  letI : Algebra.EssFiniteType R (FractionRing U) := Algebra.EssFiniteType.comp R T (FractionRing U)
  letI : Algebra.EssFiniteType (FractionRing R) (FractionRing T) :=
    Algebra.EssFiniteType.of_comp R (FractionRing R) (FractionRing T)
  letI : Algebra.EssFiniteType (FractionRing T) (FractionRing U) :=
    Algebra.EssFiniteType.of_comp T (FractionRing T) (FractionRing U)
  have hRT_lt :
      Algebra.trdeg (FractionRing R) (FractionRing T) < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field (K := FractionRing R) (L := FractionRing T)
  have hTU_lt :
      Algebra.trdeg (FractionRing T) (FractionRing U) < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field (K := FractionRing T) (L := FractionRing U)
  -- Rewrite the cardinal tower formula for the fraction fields into a nat-valued identity.
  dsimp [Algebra.fractionRingTrdeg]
  rw [← trdeg_add_eq (R := FractionRing R) (S := FractionRing T) (A := FractionRing U)]
  exact Cardinal.toNat_add hRT_lt hTU_lt

/-- Helper for Lemma 10.113.1: contracting a prime first to an intermediate stage and then to `R`
is the same as contracting directly to `R`. -/
private lemma comap_under_eq_under_in_tower
    {T : Type*} {U : Type*}
    [CommRing T] [CommRing U] [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    (q : PrimeSpectrum U) :
    let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
    qT.asIdeal.under R = q.asIdeal.under R := by
  let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
  ext r
  -- Both contractions are defined by testing membership after mapping `r` into `U`.
  change algebraMap T U (algebraMap R T r) ∈ q.asIdeal ↔ algebraMap R U r ∈ q.asIdeal
  rw [IsScalarTower.algebraMap_apply R T U r]

/-- Helper for Lemma 10.113.1: residue-field transcendence degree is additive in towers of
finite-type extensions of prime spectra. -/
private lemma residueFieldTrdeg_tower_eq
    {T : Type*} {U : Type*}
    [CommRing T] [CommRing U] [IsDomain T] [IsDomain U]
    [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    [Algebra.FiniteType R T] [Algebra.FiniteType T U]
    (q : PrimeSpectrum U) :
    let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
        Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
  let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
  let p : Ideal R := qT.asIdeal.under R
  letI : qT.asIdeal.LiesOver p := ⟨rfl⟩
  letI : q.asIdeal.LiesOver qT.asIdeal := by
    -- By definition, `qT` is the contraction of `q` along `T → U`.
    exact ⟨rfl⟩
  letI : Algebra.EssFiniteType p.ResidueField qT.asIdeal.ResidueField := inferInstance
  letI : Algebra.EssFiniteType qT.asIdeal.ResidueField q.asIdeal.ResidueField := inferInstance
  have hp : p = q.asIdeal.under R :=
    comap_under_eq_under_in_tower (R := R) (T := T) (U := U) q
  have hbase_lt :
      Algebra.trdeg p.ResidueField qT.asIdeal.ResidueField < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field
      (K := p.ResidueField) (L := qT.asIdeal.ResidueField)
  have htop_lt :
      Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field
      (K := qT.asIdeal.ResidueField) (L := q.asIdeal.ResidueField)
  have hsum :
      Algebra.trdeg p.ResidueField qT.asIdeal.ResidueField +
          Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField =
        Algebra.trdeg p.ResidueField q.asIdeal.ResidueField :=
    trdeg_add_eq (R := p.ResidueField) (S := qT.asIdeal.ResidueField) (A := q.asIdeal.ResidueField)
  -- Rewrite the lower residue field by the tower contraction identity and then apply `toNat_add`.
  calc
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
      = Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
          rw [← hp]
    _ = Cardinal.toNat (Algebra.trdeg p.ResidueField qT.asIdeal.ResidueField) +
          Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
            rw [← hsum, Cardinal.toNat_add hbase_lt htop_lt]

/-- Helper for Lemma 10.113.1: in the empty-generator stage, the bottom subalgebra is identified
with `R`, so both the height term and the residue-field term are unchanged. -/
private lemma adjoin_empty_primeHeight_residueFieldTrdeg_eq
    [IsNoetherianRing R]
    (hinj : Function.Injective (algebraMap R S))
    (q : PrimeSpectrum (Algebra.adjoin R (∅ : Set S))) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) := by
  let e : Algebra.adjoin R (∅ : Set S) ≃ₐ[R] R := by
    simpa [Algebra.adjoin_empty] using Algebra.botEquivOfInjective hinj
  have hheight :
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) =
        ENat.toNat (Ideal.primeHeight q.asIdeal) := by
    -- The bottom stage and `R` are ring-equivalent, so corresponding prime heights coincide.
    have hheight_eq :
        (q.asIdeal.under R).height = q.asIdeal.height := by
      simpa [e, Algebra.adjoin_empty, Ideal.under_def] using
        RingEquiv.height_comap e.toRingEquiv q.asIdeal
    simpa [Ideal.height_eq_primeHeight] using hheight_eq
  have hsurj :
      (algebraMap R (Algebra.adjoin R (∅ : Set S))).SurjectiveOnStalks := by
    -- The bottom-stage equivalence makes the structure map surjective, hence surjective on stalks.
    refine RingHom.surjectiveOnStalks_of_surjective ?_
    intro y
    refine ⟨e y, ?_⟩
    change e.symm (e y) = y
    simp
  have hbij :
      Function.Bijective
        (algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) :=
    bijective_algebraMap_residueField_of_surjectiveOnStalks
      (A := R) (B := Algebra.adjoin R (∅ : Set S))
      (p := q.asIdeal.under R) (q := q.asIdeal) hsurj
  have htrdeg_zero :
      Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField = 0 := by
    let eResidue :
        (q.asIdeal.under R).ResidueField ≃ₐ[(q.asIdeal.under R).ResidueField]
          q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective
        (Algebra.ofId (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
        hbij
    let _ :
        Algebra.IsAlgebraic (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField :=
      Algebra.IsAlgebraic.of_injective eResidue.symm.toAlgHom eResidue.symm.injective
    exact trdeg_eq_zero (R := (q.asIdeal.under R).ResidueField) (A := q.asIdeal.ResidueField)
  -- The residue-field extension is an isomorphism, so its transcendence degree vanishes.
  omega

/-- Helper for Lemma 10.113.1: after adjoining one new element to a finite stage, the resulting
stage is generated over the previous stage by that single new element. -/
private lemma adjoin_singleton_eq_top_over_adjoin_finset_stage
    (t : Finset S) (x : S) :
    let T : Subalgebra R S := Algebra.adjoin R (t : Set S)
    let A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
    let hTA : T ≤ A := by
      dsimp [T, A]
      exact Algebra.adjoin_mono (by
        intro y hy
        exact Finset.mem_insert_of_mem hy)
    letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
    letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
    let xA : A := ⟨x, by
      change x ∈ Algebra.adjoin R (((insert x t : Finset S) : Set S))
      exact Algebra.subset_adjoin (by simp)⟩
    Algebra.adjoin T ({xA} : Set A) = ⊤ := by
  classical
  dsimp
  set T : Subalgebra R S := Algebra.adjoin R (t : Set S)
  set A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
  have hTA : T ≤ A := by
    -- The old stage sits inside the new one because `t ⊆ insert x t`.
    dsimp [T, A]
    exact Algebra.adjoin_mono (by
      intro y hy
      exact Finset.mem_insert_of_mem hy)
  letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
  letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
  let xA : A := ⟨x, by
    change x ∈ Algebra.adjoin R (((insert x t : Finset S) : Set S))
    exact Algebra.subset_adjoin (by simp)⟩
  apply top_unique
  intro y hy
  clear hy
  -- Route correction: keep the normalization inside the stage `A` and generate every element of
  -- `A` by induction from the old stage plus the single new generator `xA`.
  refine Algebra.adjoin_induction
    (s := (((insert x t : Finset S) : Set S)))
    (p := fun z hz => ∀ hzA : z ∈ A, (⟨z, hzA⟩ : A) ∈ Algebra.adjoin T ({xA} : Set A))
    ?_ ?_ ?_ ?_ y.2 y.2
  · intro z hz hzA
    rcases Finset.mem_insert.mp hz with rfl | hzt
    · -- The inserted generator is the chosen singleton generator over `T`.
      change xA ∈ Algebra.adjoin T ({xA} : Set A)
      exact Algebra.subset_adjoin (by simp)
    · -- Elements of the old stage come from the `T`-algebra structure on `A`.
      have hzT : z ∈ T := by
        dsimp [T]
        exact Algebra.subset_adjoin hzt
      change algebraMap T A ⟨z, hzT⟩ ∈ Algebra.adjoin T ({xA} : Set A)
      exact Subalgebra.algebraMap_mem _ _
  · intro r hrA
    -- Scalars from `R` already lie in the old stage `T`.
    change algebraMap T A (algebraMap R T r) ∈ Algebra.adjoin T ({xA} : Set A)
    exact Subalgebra.algebraMap_mem _ _
  · intro z w hz hw hrecz hrecw hzpw
    -- The stage generated by `xA` over `T` is closed under addition.
    exact Subalgebra.add_mem _ (hrecz hz) (hrecw hw)
  · intro z w hz hw hrecz hrecw hzpw
    -- The same stage is also closed under multiplication.
    exact Subalgebra.mul_mem _ (hrecz hz) (hrecw hw)

/-- Helper for Lemma 10.113.1: adjoining a finite set of generators one at a time proves the
finite-type inequality for the corresponding stage. -/
private theorem adjoin_finset_primeHeight_residueFieldTrdeg_le
    [IsNoetherianRing R]
    (hinj : Function.Injective (algebraMap R S)) (s : Finset S) :
    ∀ q : PrimeSpectrum (Algebra.adjoin R (s : Set S)),
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
          Algebra.fractionRingTrdeg
            (R := R) (S := Algebra.adjoin R (s : Set S))
            (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro q
      have hbase := adjoin_empty_primeHeight_residueFieldTrdeg_eq (R := R) (S := S) hinj q
      -- In the empty stage the generic term is nonnegative, so the equality from the base case
      -- already implies the desired inequality.
      omega
  | @insert x t hxnotin ih =>
      set T : Subalgebra R S := Algebra.adjoin R (t : Set S)
      set A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
      have hTA : T ≤ A := by
        -- The previous stage embeds into the next stage by the obvious set inclusion.
        dsimp [T, A]
        exact Algebra.adjoin_mono (by
          intro y hy
          exact Finset.mem_insert_of_mem hy)
      letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
      letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
      haveI : IsNoetherianRing T := by
        simpa [T] using adjoin_finset_isNoetherianRing (R := R) (S := S) t
      haveI : Algebra.FiniteType R T := by
        simpa [T] using adjoin_finset_finiteType (R := R) (S := S) t
      have hTA_inj : Function.Injective (algebraMap T A) :=
        Subalgebra.inclusion_injective hTA
      let xA : A := ⟨x, by
        change x ∈ Algebra.adjoin R (((insert x t : Finset S) : Set S))
        exact Algebra.subset_adjoin (by simp)⟩
      have hxA : Algebra.adjoin T ({xA} : Set A) = ⊤ :=
        adjoin_singleton_eq_top_over_adjoin_finset_stage (R := R) (S := S) t x
      haveI : Algebra.FiniteType T A := by
        -- The new stage is generated over the old stage by the single element `xA`.
        exact
          (Subalgebra.fg_iff_finiteType (R := T) (A := A) (⊤ : Subalgebra T A)).mp
            (Subalgebra.fg_def.2 ⟨({xA} : Set A), Set.finite_singleton xA, hxA⟩)
      intro q
      let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T A) q
      have hRT :
          ENat.toNat (Ideal.primeHeight qT.asIdeal) +
              Cardinal.toNat
                (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) ≤
            ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              Algebra.fractionRingTrdeg
                (R := R) (S := T)
                (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t) := by
        -- Apply the induction hypothesis to the contracted prime on the previous stage.
        simpa [T, qT] using ih qT
      have hTS :
          ENat.toNat (Ideal.primeHeight q.asIdeal) +
              Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) ≤
            ENat.toNat (Ideal.primeHeight qT.asIdeal) +
              Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj := by
        -- The insert step is the source one-generator case over the stage `T`.
        simpa [qT, xA] using
          single_generator_primeHeight_residueFieldTrdeg_le
            (A := T) (B := A) xA hxA hTA_inj q
      have hres :
          Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
            Cardinal.toNat
                (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
              Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
        -- Rewrite the residue-field term by the tower formula `κ(q∩R) ⟶ κ(qT) ⟶ κ(q)`.
        simpa [qT] using residueFieldTrdeg_tower_eq (R := R) (T := T) (U := A) q
      have hfrac :
          Algebra.fractionRingTrdeg
              (R := R) (S := A)
              (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj (insert x t)) =
            Algebra.fractionRingTrdeg
                (R := R) (S := T)
                (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t) +
              Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj := by
        -- Rewrite the generic transcendence degree by the fraction-field tower formula.
        simpa [T, A] using
          fractionRingTrdeg_tower_eq
            (R := R) (T := T) (U := A)
            (hinjRT := adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t)
            (hinjTU := hTA_inj)
            (hinjRU := adjoin_finset_algebraMap_injective (R := R) (S := S) hinj (insert x t))
      have hunder : qT.asIdeal.under R = q.asIdeal.under R := by
        -- Contracting through `T` and then to `R` is the same as contracting directly to `R`.
        simpa [qT] using comap_under_eq_under_in_tower (R := R) (T := T) (U := A) q
      have hstep :
          ENat.toNat (Ideal.primeHeight q.asIdeal) +
              (Cardinal.toNat
                  (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
                Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField)) ≤
            ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              (Algebra.fractionRingTrdeg
                  (R := R) (S := T)
                  (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t) +
                Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj) :=
        tower_step_primeHeight_residueFieldTrdeg_le hRT hTS
      -- Combine the induction hypothesis and the one-generator step, then rewrite the tower terms
      -- back to the total residue-field and fraction-field contributions.
      calc
        ENat.toNat (Ideal.primeHeight q.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
          =
            ENat.toNat (Ideal.primeHeight q.asIdeal) +
              (Cardinal.toNat
                  (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
                Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField)) := by
                  rw [hres]
        _ ≤ ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              (Algebra.fractionRingTrdeg
                  (R := R) (S := T)
                  (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t) +
                Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj) := hstep
        _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
              Algebra.fractionRingTrdeg
                (R := R) (S := A)
                (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj (insert x t)) := by
                  rw [hunder, ← hfrac]

/-- Helper for Lemma 10.113.1: in the empty-generator stage, the generic transcendence-degree term
vanishes because the stage is ring-equivalent to the source ring `R`. -/
private lemma adjoin_empty_fractionRingTrdeg_eq_zero
    (hinj : Function.Injective (algebraMap R S)) :
    Algebra.fractionRingTrdeg
        (R := R) (S := Algebra.adjoin R (∅ : Set S))
        (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj ∅) = 0 := by
  let e : Algebra.adjoin R (∅ : Set S) ≃ₐ[R] R := by
    simpa [Algebra.adjoin_empty] using Algebra.botEquivOfInjective hinj
  let eFrac : FractionRing (Algebra.adjoin R (∅ : Set S)) ≃ₐ[R] FractionRing R :=
    IsFractionRing.algEquivOfAlgEquiv e
  have hfrac :
      Algebra.trdeg (FractionRing R) (FractionRing (Algebra.adjoin R (∅ : Set S))) = 0 := by
    -- The fraction fields are isomorphic over `Frac(R)`.
    let _ :
        Algebra.IsAlgebraic (FractionRing R) (FractionRing (Algebra.adjoin R (∅ : Set S))) :=
      Algebra.IsAlgebraic.of_injective eFrac.symm.toAlgHom eFrac.symm.injective
    simpa using
      (trdeg_eq_zero :
        Algebra.trdeg (FractionRing R) (FractionRing (Algebra.adjoin R (∅ : Set S))) = 0)
  simpa [Algebra.fractionRingTrdeg] using congrArg Cardinal.toNat hfrac

/-- Helper for Lemma 10.113.1: adjoining finitely many generators one at a time preserves the
source equality in the universally catenary case. -/
private theorem adjoin_finset_primeHeight_residueFieldTrdeg_eq_of_universallyCatenary
    [UniversallyCatenaryRing.{u, v} R]
    (hinj : Function.Injective (algebraMap R S)) (s : Finset S) :
    ∀ q : PrimeSpectrum (Algebra.adjoin R (s : Set S)),
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
          Algebra.fractionRingTrdeg
            (R := R) (S := Algebra.adjoin R (s : Set S))
            (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro q
      -- The empty stage is identified with `R`, so the base equality from the source closes
      -- after rewriting the generic term to `0`.
      simpa [adjoin_empty_fractionRingTrdeg_eq_zero (R := R) (S := S) hinj] using
        adjoin_empty_primeHeight_residueFieldTrdeg_eq (R := R) (S := S) hinj q
  | @insert x t hxnotin ih =>
      set T : Subalgebra R S := Algebra.adjoin R (t : Set S)
      set A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
      have hTA : T ≤ A := by
        -- The previous stage embeds into the next stage by the obvious set inclusion.
        dsimp [T, A]
        exact Algebra.adjoin_mono (by
          intro y hy
          exact Finset.mem_insert_of_mem hy)
      letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
      letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
      haveI : IsNoetherianRing T := by
        simpa [T] using adjoin_finset_isNoetherianRing (R := R) (S := S) t
      haveI : Algebra.FiniteType R T := by
        simpa [T] using adjoin_finset_finiteType (R := R) (S := S) t
      haveI : UniversallyCatenaryRing T :=
        universallyCatenaryRing_of_finiteType (A := R) (S := T)
      have hTA_inj : Function.Injective (algebraMap T A) :=
        Subalgebra.inclusion_injective hTA
      let xA : A := ⟨x, by
        change x ∈ Algebra.adjoin R (((insert x t : Finset S) : Set S))
        exact Algebra.subset_adjoin (by simp)⟩
      have hxA : Algebra.adjoin T ({xA} : Set A) = ⊤ :=
        adjoin_singleton_eq_top_over_adjoin_finset_stage (R := R) (S := S) t x
      haveI : Algebra.FiniteType T A := by
        -- The new stage is generated over the previous stage by the singleton `{xA}`.
        exact
          (Subalgebra.fg_iff_finiteType (R := T) (A := A) (⊤ : Subalgebra T A)).mp
            (Subalgebra.fg_def.2 ⟨({xA} : Set A), Set.finite_singleton xA, hxA⟩)
      intro q
      let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T A) q
      have hRT :
          ENat.toNat (Ideal.primeHeight qT.asIdeal) +
              Cardinal.toNat
                (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) =
            ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              Algebra.fractionRingTrdeg
                (R := R) (S := T)
                (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t) := by
        -- Apply the induction hypothesis to the contracted prime on the previous stage.
        simpa [T, qT] using ih qT
      have hTS :
          ENat.toNat (Ideal.primeHeight q.asIdeal) +
              Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) =
            ENat.toNat (Ideal.primeHeight qT.asIdeal) +
              Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj := by
        -- The insert step is the source one-generator equality over the stage `T`.
        simpa [qT, xA] using
          single_generator_primeHeight_residueFieldTrdeg_eq_of_universallyCatenary
            (A := T) (B := A) xA hxA hTA_inj q
      have hres :
          Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
            Cardinal.toNat
                (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
              Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
        -- Rewrite the residue-field term by the tower formula `κ(q∩R) ⟶ κ(qT) ⟶ κ(q)`.
        simpa [qT] using residueFieldTrdeg_tower_eq (R := R) (T := T) (U := A) q
      have hfrac :
          Algebra.fractionRingTrdeg
              (R := R) (S := A)
              (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj (insert x t)) =
            Algebra.fractionRingTrdeg
                (R := R) (S := T)
                (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t) +
              Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj := by
        -- Rewrite the generic transcendence degree by the fraction-field tower formula.
        simpa [T, A] using
          fractionRingTrdeg_tower_eq
            (R := R) (T := T) (U := A)
            (hinjRT := adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t)
            (hinjTU := hTA_inj)
            (hinjRU := adjoin_finset_algebraMap_injective (R := R) (S := S) hinj (insert x t))
      have hunder : qT.asIdeal.under R = q.asIdeal.under R := by
        -- Contracting through `T` and then to `R` is the same as contracting directly to `R`.
        simpa [qT] using comap_under_eq_under_in_tower (R := R) (T := T) (U := A) q
      have hstep :
          ENat.toNat (Ideal.primeHeight q.asIdeal) +
              (Cardinal.toNat
                  (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
                Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField)) =
            ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              (Algebra.fractionRingTrdeg
                  (R := R) (S := T)
                  (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t) +
                Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj) :=
        tower_step_primeHeight_residueFieldTrdeg_eq hRT hTS
      -- Combine the induction hypothesis and the one-generator equality, then rewrite the tower
      -- terms back to the total residue-field and fraction-field contributions.
      calc
        ENat.toNat (Ideal.primeHeight q.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
          =
            ENat.toNat (Ideal.primeHeight q.asIdeal) +
              (Cardinal.toNat
                  (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
                Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField)) := by
                  rw [hres]
        _ = ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              (Algebra.fractionRingTrdeg
                  (R := R) (S := T)
                  (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj t) +
                Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj) := hstep
        _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
              Algebra.fractionRingTrdeg
                (R := R) (S := A)
                (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj (insert x t)) := by
                  rw [hunder, ← hfrac]

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

/-- Helper for Lemma 10.113.1: after identifying a finite adjoin stage with the ambient algebra,
the source-side height plus residue-field term is unchanged. -/
private lemma adjoin_stage_left_side_eq
    [IsNoetherianRing R]
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    ENat.toNat (Ideal.primeHeight qA.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
  let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
  have hheight :
      ENat.toNat (Ideal.primeHeight qA.asIdeal) =
        ENat.toNat (Ideal.primeHeight q.asIdeal) := by
    -- Corresponding primes under the stage equivalence have the same height.
    have hheight_eq : qA.asIdeal.height = q.asIdeal.height := by
      simpa [qA] using RingEquiv.height_comap eStage.toRingEquiv q.asIdeal
    simpa [Ideal.height_eq_primeHeight] using hheight_eq
  have hunder : qA.asIdeal.under R = q.asIdeal.under R := by
    -- Contracting through the identified stage is the same as contracting directly to `R`.
    simpa [qA] using comap_under_eq_under_in_tower (R := R) (T := A) (U := S) q
  have hsurjA : Function.Surjective (algebraMap A S) := by
    intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    -- The chosen finite stage is all of `S`.
    simpa [A, hs] using (show y ∈ (⊤ : Subalgebra R S) from trivial)
  have hsurjStalks : (algebraMap A S).SurjectiveOnStalks :=
    RingHom.surjectiveOnStalks_of_surjective hsurjA
  letI : q.asIdeal.LiesOver qA.asIdeal := ⟨by simpa [qA, PrimeSpectrum.comap_asIdeal]⟩
  have hbij :
      Function.Bijective (algebraMap qA.asIdeal.ResidueField q.asIdeal.ResidueField) :=
    bijective_algebraMap_residueField_of_surjectiveOnStalks
      (A := A) (B := S) (p := qA.asIdeal) (q := q.asIdeal) hsurjStalks
  let eTop :
      qA.asIdeal.ResidueField ≃ₐ[qA.asIdeal.ResidueField] q.asIdeal.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId qA.asIdeal.ResidueField q.asIdeal.ResidueField) hbij
  have htop :
      Algebra.trdeg qA.asIdeal.ResidueField q.asIdeal.ResidueField = 0 := by
    -- The corresponding residue fields are isomorphic, so their relative transcendence degree
    -- vanishes.
    let _ : Algebra.IsAlgebraic qA.asIdeal.ResidueField q.asIdeal.ResidueField :=
      Algebra.IsAlgebraic.of_injective eTop.symm.toAlgHom eTop.symm.injective
    simpa using
      (trdeg_eq_zero :
        Algebra.trdeg qA.asIdeal.ResidueField q.asIdeal.ResidueField = 0)
  have hres :
      Cardinal.toNat
          (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) =
        Cardinal.toNat
          (Algebra.trdeg (qA.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
    -- The tower `κ(q_A ∩ R) ⟶ κ(q_A) ⟶ κ(q)` has trivial top step, so the bottom trdeg is
    -- unchanged.
    exact congrArg Cardinal.toNat <|
      (by
        simpa [htop] using
          (trdeg_add_eq
            (R := (qA.asIdeal.under R).ResidueField)
            (S := qA.asIdeal.ResidueField)
            (A := q.asIdeal.ResidueField)) :
        Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField =
          Algebra.trdeg (qA.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
  -- Rewrite the stage prime to the ambient prime on the height term, then collapse the trivial
  -- residue-field step above `qA`.
  calc
    ENat.toNat (Ideal.primeHeight qA.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField)
      = ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (qA.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
              rw [hheight, hres]
    _ = ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
              simpa [hunder]

/-- Helper for Lemma 10.113.1: once the chosen finite adjoin stage is all of `S`, the generic
fraction-field transcendence degree is unchanged. -/
private lemma adjoin_stage_fractionRingTrdeg_eq
    (hinj : Function.Injective (algebraMap R S))
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) :
    Algebra.fractionRingTrdeg
        (R := R) (S := Algebra.adjoin R (s : Set S))
        (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj s) =
      Algebra.fractionRingTrdeg (R := R) (S := S) hinj := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  have hAS_inj : Function.Injective (algebraMap A S) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hAS_surj : Function.Surjective (algebraMap A S) := by
    intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    -- The stage equality `A = ⊤` lets every element of `S` come from the stage.
    simpa [A, hs] using (show y ∈ (⊤ : Subalgebra R S) from trivial)
  have hAS_zero :
      Algebra.fractionRingTrdeg (R := A) (S := S) hAS_inj = 0 := by
    let eAS : A ≃ₐ[A] S :=
      AlgEquiv.ofBijective (Algebra.ofId A S) (by simpa using ⟨hAS_inj, hAS_surj⟩)
    let eFrac : FractionRing A ≃ₐ[A] FractionRing S :=
      IsFractionRing.algEquivOfAlgEquiv eAS
    have hfrac :
        Algebra.trdeg (FractionRing A) (FractionRing S) = 0 := by
      -- The stage and ambient fraction fields are isomorphic over `Frac(A)`.
      let _ : Algebra.IsAlgebraic (FractionRing A) (FractionRing S) :=
        Algebra.IsAlgebraic.of_injective eFrac.symm.toAlgHom eFrac.symm.injective
      simpa using
        (trdeg_eq_zero :
          Algebra.trdeg (FractionRing A) (FractionRing S) = 0)
    simpa [Algebra.fractionRingTrdeg] using congrArg Cardinal.toNat hfrac
  letI : Algebra.FiniteType R A := by
    simpa [A] using adjoin_finset_finiteType (R := R) (S := S) s
  letI : Algebra.FiniteType A S :=
    (inferInstance : Algebra.FiniteType A A).of_surjective (Algebra.ofId A S)
      (by simpa using hAS_surj)
  -- The source-proof tower `R ⊆ A = S` has trivial top generic term, so the bottom and total
  -- transcendence degrees agree.
  simpa [A, hAS_zero] using
    (fractionRingTrdeg_tower_eq
      (R := R) (T := A) (U := S)
      (hinjRT := adjoin_finset_algebraMap_injective (R := R) (S := S) hinj s)
      (hinjTU := hAS_inj) (hinjRU := hinj))

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
    obtain ⟨t, htfinite, htTop⟩ := Subalgebra.fg_def.1
      (show (⊤ : Subalgebra R S).FG from (inferInstance : Algebra.FiniteType R S).out)
    let s : Finset S := htfinite.toFinset
    have hs : Algebra.adjoin R (s : Set S) = ⊤ := by
      -- Convert the finite generating set from a finite subset to the required `Finset` stage.
      simpa [s, htfinite.coe_toFinset] using htTop
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    have hstage :
        ENat.toNat (Ideal.primeHeight qA.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) ≤
          ENat.toNat (Ideal.primeHeight (qA.asIdeal.under R)) +
            Algebra.fractionRingTrdeg
              (R := R) (S := A)
              (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj s) := by
      -- Apply the finished finite-generator induction at the literal finite adjoin stage.
      simpa [A, qA] using
        adjoin_finset_primeHeight_residueFieldTrdeg_le (R := R) (S := S) hinj s qA
    have hunder : qA.asIdeal.under R = q.asIdeal.under R := by
      -- Contracting through the chosen stage recovers the original source prime.
      simpa [qA] using comap_under_eq_under_in_tower (R := R) (T := A) (U := S) q
    -- Route correction: close the public theorem by the two terminal transports only, matching
    -- the source reduction from `S` to a finite generating stage.
    calc
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
        =
          ENat.toNat (Ideal.primeHeight qA.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) := by
                symm
                simpa [A, eStage, qA] using
                  adjoin_stage_left_side_eq (R := R) (S := S) s hs q
      _ ≤ ENat.toNat (Ideal.primeHeight (qA.asIdeal.under R)) +
            Algebra.fractionRingTrdeg
              (R := R) (S := A)
              (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj s) := hstage
      _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
            Algebra.fractionRingTrdeg hinj := by
              rw [hunder, adjoin_stage_fractionRingTrdeg_eq (R := R) (S := S) hinj s hs]

/-- Lemma 10.113.1: if `R → S` is an injective finite type map of domains with `R` Noetherian and
`q` lies over `p`, then the height of `q` plus the transcendence degree of the residue-field
extension `κ(q) / κ(p)` is bounded by the height of `p` plus the transcendence degree of `Frac(S)`
over `Frac(R)`. -/
@[stacks 02IJ]
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
    obtain ⟨t, htfinite, htTop⟩ := Subalgebra.fg_def.1
      (show (⊤ : Subalgebra R S).FG from (inferInstance : Algebra.FiniteType R S).out)
    let s : Finset S := htfinite.toFinset
    have hs : Algebra.adjoin R (s : Set S) = ⊤ := by
      -- Convert the finite generating set from a finite subset to the required `Finset` stage.
      simpa [s, htfinite.coe_toFinset] using htTop
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    have hstage :
        ENat.toNat (Ideal.primeHeight qA.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) =
          ENat.toNat (Ideal.primeHeight (qA.asIdeal.under R)) +
            Algebra.fractionRingTrdeg
              (R := R) (S := A)
              (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj s) := by
      -- Apply the finite-generator equality theorem at the literal finite adjoin stage.
      simpa [A, qA] using
        adjoin_finset_primeHeight_residueFieldTrdeg_eq_of_universallyCatenary
          (R := R) (S := S) hinj s qA
    have hunder : qA.asIdeal.under R = q.asIdeal.under R := by
      -- Contracting through the chosen stage recovers the original source prime.
      simpa [qA] using comap_under_eq_under_in_tower (R := R) (T := A) (U := S) q
    -- Route correction: the equality case now closes by the same two terminal transports as the
    -- inequality theorem, after rerunning the generator induction with equality.
    calc
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
        =
          ENat.toNat (Ideal.primeHeight qA.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) := by
                symm
                simpa [A, eStage, qA] using
                  adjoin_stage_left_side_eq (R := R) (S := S) s hs q
      _ = ENat.toNat (Ideal.primeHeight (qA.asIdeal.under R)) +
            Algebra.fractionRingTrdeg
              (R := R) (S := A)
              (adjoin_finset_algebraMap_injective (R := R) (S := S) hinj s) := hstage
      _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
            Algebra.fractionRingTrdeg hinj := by
              rw [hunder, adjoin_stage_fractionRingTrdeg_eq (R := R) (S := S) hinj s hs]

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
