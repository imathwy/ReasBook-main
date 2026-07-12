import Mathlib
import Mathlib.FieldTheory.KummerPolynomial
import StacksProject_2024.Chap10.Lemma_10_119_7
import StacksProject_2024.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u

section

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]
variable (a : A)
variable (hresidue : ∀ x : ResidueField A, x ^ p ≠ residue A a)

local notation "K" => FractionRing A
local notation "f" => (X ^ p - C (algebraMap A K a) : Polynomial K)
local notation "L" => AdjoinRoot f
local notation "α" => (AdjoinRoot.root f : L)

noncomputable local instance : Algebra K L := inferInstance

local notation "B" => Algebra.adjoin A ({α} : Set L)

noncomputable local instance : Algebra B L := inferInstance

/- Domain-style sampling:
* primary domain: Kummer-type degree-`p` extensions over the fraction field of a discrete
  valuation ring and the induced normalization over the base DVR;
* sampled owner declarations:
  `Polynomial.X_pow_sub_C_irreducible_of_prime`,
  `IsIntegralClosure.adjoin_le_integralClosure`,
  `integralClosure_isDiscreteValuationRing_of_finite_purelyInseparable`,
  `IsExtensionOfDiscreteValuationRings.WeaklyUnramified`;
* best owner abstraction: the canonical normalization `integralClosure A L`, with the explicit
  adjoin presentation `A[α]` kept only as the source-facing bridge;
* primitive data: the element `a : A`, the residue-field non-`p`th-power hypothesis, the Kummer
  polynomial `f = X ^ p - a`, and its adjoined root `α`;
* derived API: the no-`p`th-root statement in `FractionRing A`, irreducibility of `f`, the
  normalization equality `integralClosure A L = A[α]`, and the DVR / weakly-unramified structure
  on that normalization.

Layer triage:
* `source-facing`: the equality identifying the normalization with `A[α]`;
* `core/canonical`: `integralClosure A L`, `IsExtensionOfDiscreteValuationRings`, and
  `WeaklyUnramified`;
* `bridge/view`: the theorem `integralClosure_eq_adjoin_pth_root_of_residue_not_pth_power`.
-/

include hresidue

-- Proof sketch: if `x ^ p = a` in `FractionRing A`, then applying the residue map to an integral
-- representative of `x` produces a `p`th root of `residue A a` in `ResidueField A`, contradicting
-- `hresidue`.
/-- Lemma 15.116.8 (1): if the residue class of `a` in `ResidueField A` is not a `p`th power, then
`a` is not a `p`th power in the fraction field `FractionRing A`. -/
theorem fractionRing_pow_ne_of_residue_not_pth_power (x : K) :
    x ^ p ≠ algebraMap A K a := by
  intro hx
  have hp : Nat.Prime p := Fact.out
  -- The equation `x ^ p = a` makes `x ^ p`, hence `x`, integral over the DVR `A`.
  have hxIntegralPow : IsIntegral A (x ^ p) := by
    simpa [hx] using (isIntegral_algebraMap : IsIntegral A (algebraMap A K a))
  have hxIntegral : IsIntegral A x :=
    IsIntegral.of_pow hp.pos hxIntegralPow
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff.mp hxIntegral : ∃ y : A, algebraMap A K y = x)
  -- Pull the pth-power equation back to `A`, then reduce modulo the maximal ideal.
  have hy_pow : y ^ p = a := by
    apply (IsFractionRing.injective A K)
    calc
      algebraMap A K (y ^ p) = (algebraMap A K y) ^ p := by simp
      _ = x ^ p := by simpa [hy]
      _ = algebraMap A K a := hx
  exact hresidue (residue A y) <| by
    simpa using congrArg (residue A) hy_pow

/-- Helper for Lemma 15.116.8: the residue polynomial `X ^ p - residue a` is irreducible. -/
private theorem residue_x_pow_sub_C_irreducible_of_residue_not_pth_power :
    Irreducible (X ^ p - C (residue A a) : Polynomial (ResidueField A)) := by
  have hp : Nat.Prime p := Fact.out
  -- Over the residue field, the Kummer criterion applies directly to `hresidue`.
  refine X_pow_sub_C_irreducible_of_prime hp ?_
  intro x
  exact hresidue x

-- Proof sketch: apply the Kummer irreducibility criterion to `X ^ p - C (algebraMap A K a)` over
-- `K = FractionRing A`, using `fractionRing_pow_ne_of_residue_not_pth_power` to rule out `p`th
-- roots in `K`.
/-- The Kummer polynomial `X ^ p - a` over `FractionRing A` is irreducible under the residue-field
non-`p`th-power hypothesis. -/
private theorem x_pow_sub_C_irreducible_of_residue_not_pth_power :
    Irreducible f := by
  have hp : Nat.Prime p := Fact.out
  -- The fraction-field polynomial is irreducible because `a` has no pth root in `K`.
  refine X_pow_sub_C_irreducible_of_prime hp ?_
  intro x
  exact fractionRing_pow_ne_of_residue_not_pth_power (a := a) hresidue x

/-- The canonical adjunction `K[a^{1/p}] = AdjoinRoot (X ^ p - a)` is a domain under the
irreducibility of the Kummer polynomial. -/
private instance adjoinRoot_x_pow_sub_C_isDomain_of_residue_not_pth_power :
    IsDomain L := by
  letI : Fact (Irreducible f) :=
    ⟨x_pow_sub_C_irreducible_of_residue_not_pth_power (a := a) hresidue⟩
  infer_instance

/-- Helper for Lemma 15.116.8: the normalization inside the domain `L` is itself a domain. -/
private theorem integralClosure_isDomain_of_residue_not_pth_power :
    IsDomain (integralClosure A L) := by
  letI : IsDomain L := by
    letI : Fact (Irreducible f) :=
      ⟨x_pow_sub_C_irreducible_of_residue_not_pth_power (a := a) hresidue⟩
    infer_instance
  exact Subalgebra.isDomain (integralClosure A L)

/-- Helper for Lemma 15.116.8: the adjoined root satisfies `α ^ p = a` in `L`. -/
private theorem adjoinRoot_root_pow_eq :
    α ^ p = algebraMap A L a := by
  -- The defining equation of `AdjoinRoot.root f` is exactly `f(α) = 0`.
  have hroot := AdjoinRoot.eval₂_root f
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at hroot
  simpa using sub_eq_zero.mp hroot

/-- Helper for Lemma 15.116.8: the adjoined pth root is integral over the base DVR `A`. -/
private theorem adjoinRoot_root_isIntegral_over_base :
    IsIntegral A α := by
  have hp : Nat.Prime p := Fact.out
  -- Once `α ^ p` is in the image of `A`, `IsIntegral.of_pow` gives integrality of `α`.
  refine IsIntegral.of_pow hp.pos ?_
  rw [adjoinRoot_root_pow_eq (a := a) hresidue]
  exact (isIntegral_algebraMap : IsIntegral A (algebraMap A L a))

/-- Helper for Lemma 15.116.8: the explicit adjoin ring lies in the normalization. -/
private theorem adjoin_pth_root_le_integralClosure :
    B ≤ integralClosure A L := by
  -- The normalization contains the `A`-subalgebra generated by any integral element of `L`.
  exact
    adjoin_le_integralClosure
      (R := A) (A := L) (x := α)
      (adjoinRoot_root_isIntegral_over_base (a := a) hresidue)

/-- Helper for Lemma 15.116.8: the explicit adjoin ring `B = A[α]` inherits domain structure from
the ambient field extension `L`. -/
private instance adjoin_pth_root_isDomain_of_residue_not_pth_power :
    IsDomain B := by
  letI : IsDomain L :=
    adjoinRoot_x_pow_sub_C_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  exact Subalgebra.isDomain B

/-- Helper for Lemma 15.116.8: the polynomial `X ^ p - C a` is already irreducible over `A`. -/
private theorem ring_x_pow_sub_C_irreducible_of_residue_not_pth_power :
    Irreducible (X ^ p - C a : Polynomial A) := by
  let g : Polynomial A := X ^ p - C a
  have hmonic : g.Monic := by
    -- The explicit `A`-polynomial is monic, so Gauss's lemma applies.
    simpa [g] using Polynomial.monic_X_pow_sub_C a ((Fact.out : Nat.Prime p).ne_zero : p ≠ 0)
  have hmap : Irreducible (g.map (algebraMap A K)) := by
    -- After base change to `K`, this is exactly the irreducible Kummer polynomial `f`.
    simpa [g] using
      x_pow_sub_C_irreducible_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  exact (hmonic.irreducible_iff_irreducible_map_fraction_map).2 hmap

/-- Helper for Lemma 15.116.8: over the fraction field, the adjoined root has minimal polynomial
`X ^ p - C (algebraMap A K a)`. -/
private theorem minpoly_fractionField_adjoinRoot_root_eq :
    minpoly K α = f := by
  have hp : Nat.Prime p := Fact.out
  letI : Fact (Irreducible f) :=
    ⟨x_pow_sub_C_irreducible_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue⟩
  letI : Field L := by
    infer_instance
  have hroot_eval : Polynomial.eval₂ (AdjoinRoot.of f) α f = 0 := by
    -- The distinguished root of the quotient annihilates the defining polynomial.
    exact AdjoinRoot.eval₂_root f
  have hroot : aeval α f = 0 := by
    -- Rewrite the quotient evaluation into the standard `aeval` form used by `minpoly`.
    simpa [Polynomial.aeval_def] using hroot_eval
  -- The irreducible Kummer polynomial is the unique monic polynomial annihilating `α`.
  exact (minpoly.eq_of_irreducible_of_monic
    (x_pow_sub_C_irreducible_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue)
    hroot (Polynomial.monic_X_pow_sub_C (algebraMap A K a) hp.ne_zero)).symm

/-- Helper for Lemma 15.116.8: over the base DVR, the explicit Kummer polynomial already
annihilates the adjoined root. -/
private theorem aeval_base_kummer_polynomial_root_eq_zero :
    aeval α (X ^ p - C a : Polynomial A) = 0 := by
  -- Evaluate `X ^ p - C a` term-by-term and then use the defining equation `α ^ p = a`.
  rw [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  exact sub_eq_zero.mpr (adjoinRoot_root_pow_eq (A := A) (p := p) (a := a) hresidue)

/-- Helper for Lemma 15.116.8: base-changing `X ^ p - C a` to the fraction field gives the field
Kummer polynomial. -/
private theorem map_base_kummer_polynomial_eq :
    Polynomial.map (algebraMap A K) (X ^ p - C a : Polynomial A) =
      (X ^ p - C (algebraMap A K a) : Polynomial K) := by
  -- Mapping coefficients to the fraction field only changes the constant term.
  simp

/-- Helper for Lemma 15.116.8: over the base DVR `A`, the adjoined root has minimal polynomial
`X ^ p - C a`. -/
private theorem minpoly_base_adjoinRoot_root_eq :
    minpoly A α = (X ^ p - C a : Polynomial A) := by
  letI : IsDomain L :=
    adjoinRoot_x_pow_sub_C_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  have hmap :
      Polynomial.map (algebraMap A K) (minpoly A α) =
        (X ^ p - C (algebraMap A K a) : Polynomial K) := by
    -- The canonical `A → K → L` scalar tower makes the owner minimal-polynomial comparison
    -- theorem available without any bespoke compatibility layer.
    calc
      Polynomial.map (algebraMap A K) (minpoly A α) = minpoly K α := by
        symm
        exact
          (minpoly.isIntegrallyClosed_eq_field_fractions' K
            (adjoinRoot_root_isIntegral_over_base (A := A) (p := p) (a := a) hresidue) :
              minpoly K α = Polynomial.map (algebraMap A K) (minpoly A α))
      _ = (X ^ p - C (algebraMap A K a) : Polynomial K) := by
        exact minpoly_fractionField_adjoinRoot_root_eq (A := A) (p := p) (a := a) hresidue
  -- Injectivity of coefficient extension from the domain `A` to its fraction field brings the
  -- equality back down to the base ring.
  exact
    (Polynomial.map_injective (algebraMap A K) (IsFractionRing.injective A K)) <| by
      calc
        Polynomial.map (algebraMap A K) (minpoly A α) =
            (X ^ p - C (algebraMap A K a) : Polynomial K) := hmap
        _ = Polynomial.map (algebraMap A K) (X ^ p - C a : Polynomial A) := by
          symm
          exact map_base_kummer_polynomial_eq (A := A) (p := p) (a := a) hresidue

/-- Helper for Lemma 15.116.8: the explicit adjoin ring `B = A[α]` is canonically the owner
quotient `A[X] / (X ^ p - a)`. -/
private noncomputable abbrev owner_adjoinRoot_algEquiv_adjoin_pth_root :
    B ≃ₐ[A] AdjoinRoot (X ^ p - C a : Polynomial A) := by
  let hx := adjoinRoot_root_isIntegral_over_base (A := A) (p := p) (a := a) hresidue
  letI : IsDomain L :=
    adjoinRoot_x_pow_sub_C_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  letI : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  -- Route correction: first identify `A[α]` with `AdjoinRoot (minpoly A α)`, then rewrite the
  -- owner polynomial using the already-proved base minimal-polynomial computation.
  exact
    (minpoly.equivAdjoin (R := A) (x := α) hx).symm.trans <|
      AdjoinRoot.algEquivOfEq A (minpoly A α) (X ^ p - C a : Polynomial A)
        (minpoly_base_adjoinRoot_root_eq (A := A) (p := p) (a := a) hresidue)

/-- Helper for Lemma 15.116.8: reducing the base Kummer polynomial modulo the maximal ideal keeps
the same `X ^ p - a` shape over the residue field. -/
private theorem ring_adjoinRoot_special_fiber_polynomial_map :
    (X ^ p - C a : Polynomial A).map (residue A) =
      (X ^ p - C (residue A a) : Polynomial (ResidueField A)) := by
  -- Reducing coefficients modulo the maximal ideal only changes the constant term.
  simp

/-- Helper for Lemma 15.116.8: quotienting by the maximal ideal gives the usual residue field. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldEquiv :
    A ⧸ maximalIdeal A ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).trans <|
      (RingEquiv.ofBijective
        (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Lemma 15.116.8: under the quotient-to-residue-field identification, the quotient
class of `a` is exactly the residue class of `a`. -/
private theorem maximalIdealQuotientResidueFieldEquiv_apply_mk (x : A) :
    maximalIdealQuotientResidueFieldEquiv (A := A)
        (Ideal.Quotient.mk (maximalIdeal A) x) =
      residue A x := by
  -- Both maps factor the same quotient class into the residue field.
  let eκR : ResidueField A ≃+* (maximalIdeal A).ResidueField :=
    RingEquiv.ofBijective
      (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))
  change
    eκR.symm
        (algebraMap A (maximalIdeal A).ResidueField x) =
      residue A x
  rw [show algebraMap A (maximalIdeal A).ResidueField x =
      eκR (residue A x) by rfl]
  exact eκR.symm_apply_apply (residue A x)

/-- Helper for Lemma 15.116.8: the quotient-by-maximal-ideal identification is compatible with
the ambient `A`-algebra structures. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldAlgEquiv :
    (A ⧸ maximalIdeal A) ≃ₐ[A] ResidueField A where
  toRingEquiv := maximalIdealQuotientResidueFieldEquiv (A := A)
  -- Both `A`-algebra structures are the canonical quotient/residue maps, so it is enough to
  -- compare them on representatives.
  commutes' r := by
    exact maximalIdealQuotientResidueFieldEquiv_apply_mk
      (A := A) (p := p) (a := a) hresidue r

/-- Helper for Lemma 15.116.8: after transporting coefficients from `A ⧸ maximalIdeal A` to the
residue field, the owner special-fiber polynomial is exactly the residue Kummer polynomial. -/
private theorem owner_special_fiber_mapped_polynomial_eq :
    Polynomial.map (maximalIdealQuotientResidueFieldEquiv (A := A)).toRingHom
      (Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (X ^ p - C a : Polynomial A)) =
        (X ^ p - C (residue A a) : Polynomial (ResidueField A)) := by
  -- Route correction: normalize coefficients to `ResidueField A` first, then reduce the
  -- transported polynomial by rewriting only the constant coefficient.
  calc
    Polynomial.map (maximalIdealQuotientResidueFieldEquiv (A := A)).toRingHom
        (Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (X ^ p - C a : Polynomial A)) =
      (X ^ p - C
        ((maximalIdealQuotientResidueFieldEquiv (A := A))
          (Ideal.Quotient.mk (maximalIdeal A) a)) : Polynomial (ResidueField A)) := by
        simp
    _ = (X ^ p - C (residue A a) : Polynomial (ResidueField A)) := by
        rw [maximalIdealQuotientResidueFieldEquiv_apply_mk
          (A := A) (p := p) (a := a) hresidue a]

/-- Helper for Lemma 15.116.8: changing coefficients along an `A`-algebra equivalence transports
the principal polynomial quotient to the mapped principal quotient. -/
private noncomputable abbrev polynomial_quotient_equiv_of_coeff_algEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (e : R ≃ₐ[A] S) (g : Polynomial R) :
    (Polynomial R ⧸ Ideal.span ({g} : Set (Polynomial R))) ≃ₐ[A]
      (Polynomial S ⧸ Ideal.span ({Polynomial.map e.toRingHom g} : Set (Polynomial S))) := by
  -- The quotient API already packages coefficient transport via `Polynomial.mapAlgEquiv e`.
  refine Ideal.quotientEquivAlg _ _ (Polynomial.mapAlgEquiv e) ?_
  -- A principal ideal generated by one polynomial maps to the principal ideal of its image.
  rw [Ideal.map_span, Set.image_singleton]
  simpa

/-- Helper for Lemma 15.116.8: the owner special fiber is canonically the quotient of the residue
polynomial ring by the reduced Kummer polynomial. -/
private noncomputable abbrev ring_adjoinRoot_special_fiber_quot_equiv_polynomial_quotient :
    (AdjoinRoot (X ^ p - C a : Polynomial A) ⧸
      Ideal.map (algebraMap A (AdjoinRoot (X ^ p - C a : Polynomial A))) (maximalIdeal A)) ≃ₐ[A]
        Polynomial (ResidueField A) ⧸
          Ideal.span {(X ^ p - C (residue A a) : Polynomial (ResidueField A))} := by
  -- Route correction: first express the special fiber as the quotient over `A ⧸ maximalIdeal A`,
  -- then change coefficients to `ResidueField A`, and only then rewrite the generator.
  let g : Polynomial (A ⧸ maximalIdeal A) :=
    Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (X ^ p - C a : Polynomial A)
  have hspan :
      Ideal.span
          ({Polynomial.map
              (maximalIdealQuotientResidueFieldEquiv (A := A)).toRingHom g} :
            Set (Polynomial (ResidueField A))) =
        Ideal.span ({(X ^ p - C (residue A a) : Polynomial (ResidueField A))} :
          Set (Polynomial (ResidueField A))) := by
    -- Once the transported generator is normalized, the singleton spans agree immediately.
    rw [owner_special_fiber_mapped_polynomial_eq (A := A) (p := p) (a := a) hresidue]
  -- Compose the owner quotient presentation with the coefficient-change equivalence and the
  -- final ideal rewrite to reach the normalized residue Kummer quotient.
  exact
    (AdjoinRoot.quotEquivQuotMap (X ^ p - C a : Polynomial A) (maximalIdeal A)).trans <|
      (polynomial_quotient_equiv_of_coeff_algEquiv
        (A := A)
        (e := maximalIdealQuotientResidueFieldAlgEquiv
          (A := A) (p := p) (a := a) hresidue)
        g).trans <|
        Ideal.quotientEquivAlgOfEq A hspan

/-- Helper for Lemma 15.116.8: the special fiber of the owner `A[X] / (X ^ p - a)` is the
residue-field adjoin-root ring. -/
private noncomputable abbrev ring_adjoinRoot_special_fiber_quot_equiv :
    (AdjoinRoot (X ^ p - C a : Polynomial A) ⧸
      Ideal.map (algebraMap A (AdjoinRoot (X ^ p - C a : Polynomial A))) (maximalIdeal A)) ≃ₐ[A]
        AdjoinRoot (X ^ p - C (residue A a) : Polynomial (ResidueField A)) := by
  -- `AdjoinRoot` is definitionally the polynomial quotient by the singleton-generated ideal, so
  -- the normalized quotient-algebra comparison above already has the required codomain.
  simpa using
    ring_adjoinRoot_special_fiber_quot_equiv_polynomial_quotient
      (A := A) (p := p) (a := a) hresidue

/-- Helper for Lemma 15.116.8: the power-basis generator of `B = A[α]` has the expected reduced
minimal polynomial `X ^ p - C (residue A a)` on the special fiber. -/
private theorem adjoin_powerBasis_residue_minpoly_eq_kummer :
    let _ : IsDomain L :=
      adjoinRoot_x_pow_sub_C_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
    let _ : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
    let pb := Algebra.adjoin.powerBasis'
      (R := A) (S := L) (x := α)
      (adjoinRoot_root_isIntegral_over_base (A := A) (p := p) (a := a) hresidue)
    Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (minpoly A pb.gen) =
      (X ^ p - C (residue A a) : Polynomial (ResidueField A)) := by
  let _ : IsDomain L :=
    adjoinRoot_x_pow_sub_C_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  let _ : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  let hx := adjoinRoot_root_isIntegral_over_base (A := A) (p := p) (a := a) hresidue
  let pb := Algebra.adjoin.powerBasis' (R := A) (S := L) (x := α) hx
  have hpb : minpoly A pb.gen = minpoly A α := by
    -- The abstract power basis for `A[α]` is generated by the same minimal polynomial as `α`.
    simpa [pb, hx] using
      (Algebra.adjoin.powerBasis'_minpoly_gen (R := A) (S := L) (x := α) hx).symm
  -- Rewrite the power-basis minimal polynomial back to the base Kummer polynomial, then reduce.
  calc
    Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (minpoly A pb.gen) =
        Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (minpoly A α) := by
          rw [hpb]
    _ = Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (X ^ p - C a : Polynomial A) := by
          rw [minpoly_base_adjoinRoot_root_eq (A := A) (p := p) (a := a) hresidue]
    _ = (X ^ p - C (residue A a) : Polynomial (ResidueField A)) := by
          exact ring_adjoinRoot_special_fiber_polynomial_map
            (A := A) (p := p) (a := a) hresidue

/-- Helper for Lemma 15.116.8: quotienting `A[a^{1/p}]` by the extended maximal ideal is the same
special-fiber adjoin-root ring as for the owner `A[X] / (X ^ p - a)`. -/
private noncomputable abbrev adjoin_pth_root_special_fiber_quot_equiv :
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) ≃ₐ[A]
      AdjoinRoot (X ^ p - C (residue A a) : Polynomial (ResidueField A)) := by
  let _ : IsDomain L :=
    adjoinRoot_x_pow_sub_C_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  let _ : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  let hx := adjoinRoot_root_isIntegral_over_base (A := A) (p := p) (a := a) hresidue
  let pb := Algebra.adjoin.powerBasis' (R := A) (S := L) (x := α) hx
  have hspan :
      Ideal.span
          ({Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (minpoly A pb.gen)} :
            Set (Polynomial (ResidueField A))) =
        Ideal.span ({(X ^ p - C (residue A a) : Polynomial (ResidueField A))} :
          Set (Polynomial (ResidueField A))) := by
    -- The special-fiber minimal polynomial of the adjoined generator is the residue Kummer one.
    rw [adjoin_powerBasis_residue_minpoly_eq_kummer (A := A) (p := p) (a := a) hresidue]
    rfl
  -- The explicit adjoin model has the same special fiber as the owner once the quotient ideal is
  -- rewritten using the reduced minimal polynomial of the power-basis generator.
  simpa [pb, hx] using
    ((pb.quotientEquivQuotientMinpolyMap (maximalIdeal A)).trans
      (Ideal.quotientEquivAlgOfEq A hspan))

/-- Helper for Lemma 15.116.8: the mapped maximal ideal of the owner `A[X] / (X ^ p - a)` is
maximal because its quotient is the residue-field adjoin-root field. -/
private theorem ring_adjoinRoot_map_maximalIdeal_isMaximal :
    Ideal.IsMaximal
      (Ideal.map (algebraMap A (AdjoinRoot (X ^ p - C a : Polynomial A))) (maximalIdeal A)) := by
  letI : Fact (Irreducible (X ^ p - C (residue A a) : Polynomial (ResidueField A))) :=
    ⟨residue_x_pow_sub_C_irreducible_of_residue_not_pth_power
      (A := A) (p := p) (a := a) hresidue⟩
  letI : Field (AdjoinRoot (X ^ p - C (residue A a) : Polynomial (ResidueField A))) := by
    infer_instance
  let e := ring_adjoinRoot_special_fiber_quot_equiv (A := A) (p := p) (a := a) hresidue
  -- The quotient is a field because it is canonically identified with the residue-field Kummer
  -- extension, so the mapped maximal ideal is maximal.
  exact Ideal.Quotient.maximal_of_isField _ <|
    e.toRingEquiv.toMulEquiv.isField (Field.toIsField _)

/-- Helper for Lemma 15.116.8: in the explicit model `A[a^{1/p}]`, the image of the maximal ideal
of `A` is already maximal. -/
private theorem adjoin_pth_root_map_maximalIdeal_isMaximal :
    Ideal.IsMaximal (Ideal.map (algebraMap A B) (maximalIdeal A)) := by
  letI : Fact (Irreducible (X ^ p - C (residue A a) : Polynomial (ResidueField A))) :=
    ⟨residue_x_pow_sub_C_irreducible_of_residue_not_pth_power
      (A := A) (p := p) (a := a) hresidue⟩
  letI : Field (AdjoinRoot (X ^ p - C (residue A a) : Polynomial (ResidueField A))) := by
    infer_instance
  let e := adjoin_pth_root_special_fiber_quot_equiv (A := A) (p := p) (a := a) hresidue
  -- The same residue-field Kummer identification shows the explicit adjoin quotient is a field.
  exact Ideal.Quotient.maximal_of_isField _ <|
    e.toRingEquiv.toMulEquiv.isField (Field.toIsField _)

/-- Helper for Lemma 15.116.8: every element of the explicit adjoin ring `B = A[α]` is integral
over `A`. -/
private instance adjoin_pth_root_isIntegral :
    Algebra.IsIntegral A B := by
  -- The adjoin of a singleton integral element is integral over the base ring.
  exact
    Algebra.IsIntegral.adjoin (R := A) (A := L) (S := ({α} : Set L)) <|
      fun x hx ↦ by
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact adjoinRoot_root_isIntegral_over_base (A := A) (p := p) (a := a) hresidue

/-- Helper for Lemma 15.116.8: the structure map `A → B` is injective because `B` sits inside the
field extension `L`. -/
private theorem adjoin_pth_root_algebraMap_injective :
    Function.Injective (algebraMap A B) := by
  intro x y hxy
  letI : Fact (Irreducible f) :=
    ⟨x_pow_sub_C_irreducible_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue⟩
  have hxyL : algebraMap A L x = algebraMap A L y := by
    simpa using congrArg (algebraMap B L) hxy
  have hxyK : algebraMap A K x = algebraMap A K y := by
    apply RingHom.injective (algebraMap K L)
    simpa [IsScalarTower.algebraMap_eq A K L] using hxyL
  exact IsFractionRing.injective A K hxyK

/-- Helper for Lemma 15.116.8: the explicit adjoin ring `B = A[α]` is local, and its maximal
ideal is exactly the image of `maximalIdeal A`. -/
private theorem adjoin_pth_root_isLocalRing_and_maximalIdeal_eq :
    ∃ hlocal : IsLocalRing B,
      @maximalIdeal B inferInstance hlocal = Ideal.map (algebraMap A B) (maximalIdeal A) := by
  letI : Algebra.IsIntegral A B :=
    adjoin_pth_root_isIntegral (A := A) (p := p) (a := a) hresidue
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr <|
      adjoin_pth_root_algebraMap_injective (A := A) (p := p) (a := a) hresidue
  have hmap_max :
      Ideal.IsMaximal (Ideal.map (algebraMap A B) (maximalIdeal A)) :=
    adjoin_pth_root_map_maximalIdeal_isMaximal (A := A) (p := p) (a := a) hresidue
  have hlocal : IsLocalRing B := by
    -- Every maximal ideal upstairs contracts to the unique maximal ideal downstairs.
    refine IsLocalRing.of_unique_max_ideal ?_
    refine ⟨Ideal.map (algebraMap A B) (maximalIdeal A), hmap_max, ?_⟩
    intro I hI
    letI : I.IsMaximal := hI
    have hcomap : Ideal.comap (algebraMap A B) I = maximalIdeal A := by
      exact IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I)
    have hle : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ I := by
      rw [← hcomap]
      exact (Ideal.map_le_iff_le_comap).2 le_rfl
    exact (Ideal.IsMaximal.eq_of_le hmap_max hI.ne_top hle).symm
  -- In a local ring, the distinguished maximal ideal is the unique maximal ideal.
  exact ⟨hlocal, (IsLocalRing.eq_maximalIdeal hmap_max).symm⟩

/-- Helper for Lemma 15.116.8: the explicit adjoin ring `B = A[α]` is Noetherian because the
source-faithful owner quotient `A[X] / (X ^ p - a)` is finite over `A`. -/
private theorem adjoin_pth_root_isNoetherianRing :
    IsNoetherianRing B := by
  let g : Polynomial A := X ^ p - C a
  have hg : g.Monic := by
    -- The monic owner quotient is finite over the Noetherian DVR `A`.
    simpa [g] using Polynomial.monic_X_pow_sub_C a ((Fact.out : Nat.Prime p).ne_zero : p ≠ 0)
  letI : Module.Finite A (AdjoinRoot g) := hg.finite_adjoinRoot
  letI : IsNoetherianRing (AdjoinRoot g) := IsNoetherianRing.of_finite A (AdjoinRoot g)
  -- Transport Noetherianity back across the explicit owner equivalence `B ≃ₐ[A] A[X]/(X^p-a)`.
  exact
    isNoetherianRing_of_ringEquiv (AdjoinRoot g)
      (owner_adjoinRoot_algEquiv_adjoin_pth_root
        (A := A) (p := p) (a := a) hresidue).symm.toRingEquiv

/-- Helper for Lemma 15.116.8: package clause `(4)` of `discreteValuationRing_tfae` for the
explicit adjoin ring `B = A[α]`. -/
private theorem adjoin_pth_root_tfae_clause_four :
    ∃ (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : IsDomain B),
      maximalIdeal B ≠ ⊥ ∧ (maximalIdeal B).IsPrincipal := by
  letI : IsDomain B :=
    adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  letI : Algebra.IsIntegral A B :=
    adjoin_pth_root_isIntegral (A := A) (p := p) (a := a) hresidue
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr <|
      adjoin_pth_root_algebraMap_injective (A := A) (p := p) (a := a) hresidue
  letI : IsNoetherianRing B :=
    adjoin_pth_root_isNoetherianRing (A := A) (p := p) (a := a) hresidue
  rcases adjoin_pth_root_isLocalRing_and_maximalIdeal_eq (A := A) (p := p) (a := a) hresidue with
    ⟨hlocal, hmax⟩
  letI : IsLocalRing B := hlocal
  -- The maximal ideal stays nonzero because it is the image of the nonzero maximal ideal of `A`.
  have hmax_ne_bot : maximalIdeal B ≠ ⊥ := by
    rw [hmax]
    intro hbot
    have hle :
        maximalIdeal A ≤ RingHom.ker (algebraMap A B) := by
      exact (Ideal.map_eq_bot_iff_le_ker (algebraMap A B)).mp hbot
    have hker :
        RingHom.ker (algebraMap A B) = ⊥ := by
      exact (RingHom.injective_iff_ker_eq_bot (algebraMap A B)).mp <|
        adjoin_pth_root_algebraMap_injective (A := A) (p := p) (a := a) hresidue
    have hmax_bot : maximalIdeal A = ⊥ := by
      apply le_antisymm
      · rwa [hker] at hle
      · exact bot_le
    exact IsDiscreteValuationRing.not_a_field A hmax_bot
  -- Principality descends from the DVR base after rewriting the maximal ideal upstairs.
  have hprincipal_map :
      (Ideal.map (algebraMap A B) (maximalIdeal A)).IsPrincipal :=
    Submodule.IsPrincipal.map_ringHom (algebraMap A B)
      (show (maximalIdeal A).IsPrincipal by infer_instance)
  have hprincipal : (maximalIdeal B).IsPrincipal := by
    simpa [hmax] using hprincipal_map
  exact ⟨inferInstance, inferInstance, inferInstance, hmax_ne_bot, hprincipal⟩

/-- Helper for Lemma 15.116.8: the explicit adjoin ring `B = A[α]` is a discrete valuation ring. -/
private theorem adjoin_pth_root_isDiscreteValuationRing :
    @IsDiscreteValuationRing B inferInstance
      (adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue) := by
  letI : IsDomain B :=
    adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  -- Route correction: cache the TFAE object and feed it the standalone clause `(4)` package,
  -- rather than unfolding the whole local/Noetherian/principal-ideal witness inline.
  have htfae :=
    (show List.TFAE
        [ (∃ (_ : IsDomain B), IsDiscreteValuationRing B),
          ∃ (_ : IsDomain B) (_ : IsNoetherianRing B), ValuationRing B ∧ ¬ IsField B,
          IsRegularLocalRing B ∧ ringKrullDim B = 1,
          ∃ (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : IsDomain B),
            maximalIdeal B ≠ ⊥ ∧ (maximalIdeal B).IsPrincipal,
          ∃ (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : IsDomain B)
            (_ : IsIntegrallyClosed B), ringKrullDim B = 1 ] from
      discreteValuationRing_tfae (A := B))
  -- Clause `(4) → (1)` gives the DVR structure once the witness package is isolated.
  have hdvr : ∃ (_ : IsDomain B), IsDiscreteValuationRing B := by
    exact (htfae.out 3 0).mp <|
      adjoin_pth_root_tfae_clause_four (A := A) (p := p) (a := a) hresidue
  exact hdvr.choose_spec

/-- Helper for Lemma 15.116.8: use the proved DVR theorem as the local typeclass instance on
`B = A[α]`. -/
private instance adjoin_pth_root_isDiscreteValuationRing_inst :
    @IsDiscreteValuationRing B inferInstance
      (adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue) :=
  adjoin_pth_root_isDiscreteValuationRing (A := A) (p := p) (a := a) hresidue

/-- Helper for Lemma 15.116.8: the explicit adjoin map `A → B` is an extension of discrete
valuation rings. -/
private instance adjoin_pth_root_isExtensionOfDiscreteValuationRings_inst :
    @IsExtensionOfDiscreteValuationRings A B
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue)
      (adjoin_pth_root_isDiscreteValuationRing_inst (A := A) (p := p) (a := a) hresidue) :=
  by
    letI : IsDomain B :=
      adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
    letI : IsDiscreteValuationRing B :=
      adjoin_pth_root_isDiscreteValuationRing_inst (A := A) (p := p) (a := a) hresidue
    -- The source map is integral because `B = A[α]`, and injective because `B` sits in the domain
    -- `L`; these are exactly the two inputs required by the extension-of-DVR owner.
    show IsExtensionOfDiscreteValuationRings A B
    exact
      { toIsLocalHom :=
          (algebraMap_isIntegral_iff.mpr
            (adjoin_pth_root_isIntegral (A := A) (p := p) (a := a) hresidue)).isLocalHom
            (adjoin_pth_root_algebraMap_injective (A := A) (p := p) (a := a) hresidue)
        algebraMap_injective :=
          adjoin_pth_root_algebraMap_injective (A := A) (p := p) (a := a) hresidue }

/-- Helper for Lemma 15.116.8: the explicit adjoin extension `A ⊆ B` is weakly unramified. -/
private theorem adjoin_pth_root_weaklyUnramified :
    @WeaklyUnramified A B
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue)
      (adjoin_pth_root_isDiscreteValuationRing_inst (A := A) (p := p) (a := a) hresidue) :=
  by
    letI : IsDomain B :=
      adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
    letI : IsDiscreteValuationRing B :=
      adjoin_pth_root_isDiscreteValuationRing_inst (A := A) (p := p) (a := a) hresidue
    letI : IsExtensionOfDiscreteValuationRings A B :=
      adjoin_pth_root_isExtensionOfDiscreteValuationRings_inst
        (A := A) (p := p) (a := a) hresidue
    rcases adjoin_pth_root_isLocalRing_and_maximalIdeal_eq (A := A) (p := p) (a := a) hresidue with
      ⟨hlocal, hmax⟩
    letI : IsLocalRing B := hlocal
    -- For extensions of DVRs, weakly unramified is exactly the maximal-ideal equality already
    -- proved in the explicit `A[α]` model.
    rw [IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal]
    simpa [hmax]

/-- Helper for Lemma 15.116.8: the owner quotient `A[X] / (X ^ p - a)` maps to `L` by sending the
distinguished root to `α`. -/
private noncomputable abbrev owner_adjoinRoot_to_L :
    AdjoinRoot (X ^ p - C a : Polynomial A) →ₐ[A] L :=
  AdjoinRoot.liftAlgHom (X ^ p - C a : Polynomial A) (Algebra.ofId A L) α
    (aeval_base_kummer_polynomial_root_eq_zero (A := A) (p := p) (a := a) hresidue)

/-- Helper for Lemma 15.116.8: the owner map agrees with the ambient `A`-algebra map on
coefficients. -/
private theorem owner_adjoinRoot_to_L_of (r : A) :
    owner_adjoinRoot_to_L (A := A) (p := p) (a := a) hresidue
        (AdjoinRoot.of (X ^ p - C a : Polynomial A) r) =
      algebraMap A L r := by
  -- The owner quotient map was defined by lifting the identity on `A`.
  simp [owner_adjoinRoot_to_L]

/-- Helper for Lemma 15.116.8: the owner root is sent to the distinguished root `α` in `L`. -/
private theorem owner_adjoinRoot_to_L_root :
    owner_adjoinRoot_to_L (A := A) (p := p) (a := a) hresidue
        (AdjoinRoot.root (X ^ p - C a : Polynomial A)) =
      α := by
  -- This is the defining property of `AdjoinRoot.liftAlgHom`.
  simp [owner_adjoinRoot_to_L]

/-- Helper for Lemma 15.116.8: every element of the simple extension `L` is a polynomial in the
distinguished root `α`. -/
private theorem adjoinRoot_exists_polynomial_representation (z : L) :
    ∃ q : Polynomial K, aeval α q = z := by
  -- Every quotient class in `AdjoinRoot f` is represented by a polynomial in the distinguished
  -- root, so it suffices to rewrite the quotient representative as an `aeval`.
  refine AdjoinRoot.induction_on f z ?_
  intro q
  refine ⟨q, ?_⟩
  -- The quotient representative `AdjoinRoot.mk f q` is exactly evaluation of `q` at `α`.
  simpa using (AdjoinRoot.aeval_eq q)

/-- Helper for Lemma 15.116.8: evaluating a base-ring polynomial at `α` lands in the explicit
adjoin ring `B = A[α]`. -/
private theorem aeval_base_polynomial_mem_adjoin_pth_root (q : Polynomial A) :
    aeval α q ∈ B := by
  -- `B` is exactly the `A`-subalgebra generated by values of `aeval α`.
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨q, rfl⟩

/-- Helper for Lemma 15.116.8: nonzero base elements stay nonzero in `B = A[α]`. -/
private theorem adjoin_pth_root_algebraMap_ne_zero {s : A} (hs : s ≠ 0) :
    algebraMap A B s ≠ 0 := by
  intro hsB
  -- Injectivity of `A → B` lets us pull the vanishing statement back to `A`.
  have hs0 : s = 0 := by
    apply adjoin_pth_root_algebraMap_injective (A := A) (p := p) (a := a) hresidue
    calc
      algebraMap A B s = 0 := hsB
      _ = algebraMap A B 0 := by simp
  exact hs hs0

/-- Helper for Lemma 15.116.8: a single fraction-field coefficient can be rewritten with a
nonzero denominator from `A`. -/
private theorem coeff_fractionRing_clear_denominator (c : K) :
    ∃ n d : A, d ≠ 0 ∧ algebraMap A K n = algebraMap A K d * c := by
  -- Use localization surjectivity in the exact multiplication-oriented form needed later.
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A) c
  refine ⟨n, d, (mem_nonZeroDivisors_iff_ne_zero.mp d.2), ?_⟩
  calc
    algebraMap A K n = c * algebraMap A K d := by simpa using hnd.symm
    _ = algebraMap A K d * c := by rw [mul_comm]

/-- Helper for Lemma 15.116.8: a finite family of fraction-field coefficients admits one common
nonzero denominator from `A`. -/
private theorem finite_common_denominator_for_family (t : Finset ℕ) (c : ℕ → K) :
    ∃ s : A, s ≠ 0 ∧ ∀ n ∈ t, ∃ b : A, algebraMap A K b = algebraMap A K s * c n := by
  induction t using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_⟩
      intro n hn
      cases hn
  | @insert n t hn ih =>
      rcases ih with ⟨s, hs, hsupport⟩
      rcases coeff_fractionRing_clear_denominator (A := A) (p := p) (a := a) hresidue (c n) with
        ⟨bn, dn, hdn, hbn⟩
      refine ⟨s * dn, mul_ne_zero hs hdn, ?_⟩
      intro m hm
      rw [Finset.mem_insert] at hm
      rcases hm with hm | hm
      · subst m
        refine ⟨s * bn, ?_⟩
        -- For the new coefficient, multiply the old common denominator by the fresh one.
        calc
          algebraMap A K (s * bn)
              = algebraMap A K s * algebraMap A K bn := by simp
          _ = algebraMap A K s * (algebraMap A K dn * c n) := by rw [hbn]
          _ = (algebraMap A K s * algebraMap A K dn) * c n := by ring
          _ = algebraMap A K (s * dn) * c n := by simp [mul_assoc]
      · rcases hsupport m hm with ⟨b, hb⟩
        refine ⟨b * dn, ?_⟩
        -- Previously cleared coefficients absorb the new denominator by one extra multiplication.
        calc
          algebraMap A K (b * dn)
              = algebraMap A K b * algebraMap A K dn := by simp
          _ = (algebraMap A K s * c m) * algebraMap A K dn := by rw [hb]
          _ = (algebraMap A K s * algebraMap A K dn) * c m := by ring
          _ = algebraMap A K (s * dn) * c m := by simp [mul_assoc]

/-- Helper for Lemma 15.116.8: the finitely many supported coefficients of a polynomial over
`K = FractionRing A` admit one common denominator from `A`. -/
private theorem polynomial_support_common_denominator (q : Polynomial K) :
    ∃ s : A, s ≠ 0 ∧
      ∀ n ∈ q.support, ∃ b : A, algebraMap A K b = algebraMap A K s * q.coeff n := by
  -- Apply the finite-family denominator-clearing lemma to the coefficient function.
  simpa using
    (finite_common_denominator_for_family (A := A) (p := p) (a := a) hresidue q.support q.coeff)

/-- Helper for Lemma 15.116.8: clearing the supported coefficients of `q` produces a base
polynomial whose coefficient extension is `C s * q`. -/
private theorem exists_cleared_base_polynomial_map_eq (q : Polynomial K) :
    ∃ s : A, s ≠ 0 ∧ ∃ q₀ : Polynomial A,
      Polynomial.map (algebraMap A K) q₀ = C (algebraMap A K s) * q := by
  classical
  rcases polynomial_support_common_denominator (A := A) (p := p) (a := a) hresidue q with
    ⟨s, hs, hsupport⟩
  choose b hb using hsupport
  let coeff₀ : ℕ → A := fun n => if hn : n ∈ q.support then b n hn else 0
  let q₀ : Polynomial A := q.support.sum fun n ↦ Polynomial.monomial n (coeff₀ n)
  refine ⟨s, hs, q₀, ?_⟩
  -- Compare coefficients on and off the finite support of `q`.
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
  by_cases hn : n ∈ q.support
  · have hq₀ : q₀.coeff n = coeff₀ n := by
      -- On the support, only the `n`th monomial contributes to the `n`th coefficient.
      simp [q₀, Polynomial.coeff_monomial, hn]
    have hqn : q.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    have hcoeff₀ : coeff₀ n = b n hn := by
      simp [coeff₀, hqn]
    rw [hq₀, hcoeff₀, hb n hn]
  · have hq₀ : q₀.coeff n = 0 := by
      -- Off the support, every summand has zero `n`th coefficient.
      simp [q₀, Polynomial.coeff_monomial, hn]
    have hq : q.coeff n = 0 := by
      by_contra hq
      exact hn (Polynomial.mem_support_iff.mpr hq)
    rw [hq₀, hq]
    simp

/-- Helper for Lemma 15.116.8: after the coefficient identity is built in `K[X]`, evaluation at
`α` transports it to the denominator-cleared equality in `L`. -/
private theorem aeval_map_algebraMap_clear_denominator
    {q : Polynomial K} {s : A} {q₀ : Polynomial A}
    (hmap : Polynomial.map (algebraMap A K) q₀ = C (algebraMap A K s) * q) :
    aeval α q₀ = algebraMap A L s * aeval α q := by
  -- Route correction: keep the finite-support clearing separate from the `A → K → L` transport.
  calc
    aeval α q₀ = aeval α (Polynomial.map (algebraMap A K) q₀) := by
      -- The scalar tower identifies evaluation of `q₀` with evaluation of its coefficient
      -- extension from `A` to `K`.
      symm
      simpa using (Polynomial.aeval_map_algebraMap (R := A) K α q₀)
    _ = aeval α (C (algebraMap A K s) * q) := by rw [hmap]
    _ = algebraMap A L s * aeval α q := by
      -- Evaluating `C(s) * q` separates the constant factor from the polynomial part.
      simp [IsScalarTower.algebraMap_eq A K L]

/-- Helper for Lemma 15.116.8: after clearing the supported coefficients of `q`, one obtains a
base polynomial whose evaluation at `α` is `s * aeval α q`. -/
private theorem exists_cleared_base_polynomial_for_aeval (q : Polynomial K) :
    ∃ s : A, s ≠ 0 ∧ ∃ q₀ : Polynomial A, aeval α q₀ = algebraMap A L s * aeval α q := by
  rcases exists_cleared_base_polynomial_map_eq (A := A) (p := p) (a := a) hresidue q with
    ⟨s, hs, q₀, hmap⟩
  refine ⟨s, hs, q₀, ?_⟩
  -- Once the mapped-polynomial identity is known, the scalar-tower `aeval` lemma finishes.
  exact
    aeval_map_algebraMap_clear_denominator (A := A) (p := p) (a := a) hresidue
      (q := q) (s := s) (q₀ := q₀) hmap

/-- Helper for Lemma 15.116.8: every element of the simple extension `L` is a quotient of two
elements of the explicit adjoin ring `B = A[α]`. -/
private theorem exists_num_den_for_adjoin_pth_root_element (z : L) :
    ∃ r s : B, s ≠ 0 ∧ algebraMap B L r = z * algebraMap B L s := by
  rcases adjoinRoot_exists_polynomial_representation (A := A) (p := p) (a := a) hresidue z with
    ⟨q, hq⟩
  rcases exists_cleared_base_polynomial_for_aeval (A := A) (p := p) (a := a) hresidue q with
    ⟨s, hs, q₀, hclear⟩
  -- Package the cleared numerator into the explicit adjoin ring `B = A[α]`.
  have hr_mem : aeval α q₀ ∈ B :=
    aeval_base_polynomial_mem_adjoin_pth_root (A := A) (p := p) (a := a) hresidue q₀
  let r : B := ⟨aeval α q₀, hr_mem⟩
  let sB : B := algebraMap A B s
  have hsB : sB ≠ 0 := by
    -- Nonvanishing of the denominator is inherited from injectivity of `A → B`.
    exact adjoin_pth_root_algebraMap_ne_zero (A := A) (p := p) (a := a) hresidue hs
  refine ⟨r, sB, hsB, ?_⟩
  -- The cleared evaluation identity is already the required quotient equation in `L`.
  calc
    algebraMap B L r = aeval α q₀ := by
      rfl
    _ = algebraMap A L s * aeval α q := hclear
    _ = algebraMap A L s * z := by rw [hq]
    _ = z * algebraMap A L s := by rw [mul_comm]
    _ = z * algebraMap B L sB := by
      change z * algebraMap A L s = z * algebraMap A L s
      rfl

/-- Helper for Lemma 15.116.8: the explicit adjoin ring `B = A[α]` has ambient fraction field
`L`. -/
private theorem adjoin_pth_root_fractionField_bridge :
    IsFractionRing B L := by
  -- Route correction: the remaining source-faithful step is only the evaluation-level
  -- denominator-clearing bridge from `K[α]` to `A[α]`; once
  -- `exists_num_den_for_adjoin_pth_root_element` is available, `IsFractionRing.of_field` closes
  -- this theorem immediately.
  letI : Fact (Irreducible f) :=
    ⟨x_pow_sub_C_irreducible_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue⟩
  letI : Field L := by
    infer_instance
  letI : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr <| by
      intro x y hxy
      exact Subtype.ext hxy
  refine IsFractionRing.of_field B L ?_
  · intro z
    rcases
        exists_num_den_for_adjoin_pth_root_element (A := A) (p := p) (a := a) hresidue z with
      ⟨r, s, hs, hrs⟩
    refine ⟨r, s, ?_⟩
    have hsL : algebraMap B L s ≠ 0 := by
      simpa using hs
    exact (eq_div_iff hsL).2 hrs.symm

/-- Helper for Lemma 15.116.8: once `B` is identified as having fraction field `L`, the DVR
structure on `B` makes it the integral closure of `A` in `L`. -/
private theorem adjoin_pth_root_isIntegralClosure :
    IsIntegralClosure B A L := by
  letI : IsDomain B :=
    adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  letI : IsDiscreteValuationRing B :=
    adjoin_pth_root_isDiscreteValuationRing_inst (A := A) (p := p) (a := a) hresidue
  letI : Algebra.IsIntegral A B :=
    adjoin_pth_root_isIntegral (A := A) (p := p) (a := a) hresidue
  letI : IsFractionRing B L :=
    adjoin_pth_root_fractionField_bridge (A := A) (p := p) (a := a) hresidue
  letI : IsIntegrallyClosed B := by
    infer_instance
  -- A DVR is integrally closed in its fraction field, so the owner theorem applies directly.
  exact IsIntegralClosure.of_isIntegrallyClosed B A L

-- Proof sketch: let `α = AdjoinRoot.root f`. The element `α` is integral over `A` because it
-- satisfies the monic polynomial `X ^ p - C a`, so `A[α]` sits inside the integral closure. For
-- the reverse inclusion, use the irreducibility of `f` and the standard description of the
-- normalization of a DVR in this radicial degree-`p` extension.
/-- Lemma 15.116.8 (2): in the canonical adjunction `K[a^{1/p}] = AdjoinRoot (X ^ p - a)`, the
integral closure of `A` is exactly the `A`-subalgebra generated by the adjoined `p`th root. -/
theorem integralClosure_eq_adjoin_pth_root_of_residue_not_pth_power :
    integralClosure A L = B := by
  letI : IsIntegralClosure B A L :=
    adjoin_pth_root_isIntegralClosure (A := A) (p := p) (a := a) hresidue
  refine le_antisymm ?_ <|
    adjoin_pth_root_le_integralClosure (A := A) (p := p) (a := a) hresidue
  intro z hz
  -- Read membership in the normalization as integrality over `A`, then use the `B`-owner view.
  have hz_integral : IsIntegral A z := hz
  have h_integral_iff : IsIntegral A z ↔ ∃ y : B, algebraMap B L y = z :=
    IsIntegralClosure.isIntegral_iff
  rcases h_integral_iff.mp hz_integral with
    ⟨y, hy⟩
  rw [← hy]
  exact y.property

omit [Fact p.Prime] [CharP (ResidueField A) p] hresidue in
/-- Helper for Lemma 15.116.8: an equality of subalgebras transports the discrete valuation ring
structure once the source and target domain witnesses are fixed. -/
private theorem transport_isDiscreteValuationRing_of_subalgebra_eq
    {S T : Subalgebra A L} (h : S = T)
    (hSdom : IsDomain S) (hTdom : IsDomain T)
    (hDvr : @IsDiscreteValuationRing S inferInstance hSdom) :
    @IsDiscreteValuationRing T inferInstance hTdom := by
  -- After rewriting the carrier equality, only proof-irrelevance for the domain witness remains.
  subst h
  have hdom : hTdom = hSdom := Subsingleton.elim _ _
  cases hdom
  exact hDvr

-- Proof sketch: after identifying the integral closure with `B` by
-- `integralClosure_eq_adjoin_pth_root_of_residue_not_pth_power`, apply the discrete-valuation-ring
-- structure theorem for the normalization of a DVR in this degree-`p` extension.
/-- Lemma 15.116.8 (3): the normalization `integralClosure A L` is a discrete valuation ring;
equivalently, by part `(2)`, the presentation `A[a^{1/p}] = A[AdjoinRoot.root f]` is a discrete
valuation ring. -/
instance integralClosure_isDiscreteValuationRing_of_residue_not_pth_power :
    @IsDiscreteValuationRing (integralClosure A L) inferInstance
      (integralClosure_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue) :=
  by
    let hEq :
        integralClosure A L = B :=
      integralClosure_eq_adjoin_pth_root_of_residue_not_pth_power
        (A := A) (p := p) (a := a) hresidue
    let hBdom : IsDomain B :=
      adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
    let hICdom : IsDomain (integralClosure A L) :=
      integralClosure_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
    -- Route correction: transport only the DVR structure across the normalization equality and
    -- leave the extension-of-DVR owner to the canonical integral-closure instance.
    exact
      transport_isDiscreteValuationRing_of_subalgebra_eq
        (A := A) (p := p) (a := a) (S := B) (T := integralClosure A L) hEq.symm hBdom hICdom
        (adjoin_pth_root_isDiscreteValuationRing_inst (A := A) (p := p) (a := a) hresidue)

-- Proof sketch: the canonical map `A → integralClosure A L` is the normalization map into the DVR
-- from part `(3)`, and part `(2)` identifies this canonical owner with the textbook presentation
-- `A[a^{1/p}]`.
/-- The canonical normalization map `A ⊆ integralClosure A L` is an extension of discrete
valuation rings; via part `(2)`, this is the extension `A ⊆ A[a^{1/p}]`. -/
instance integralClosure_isExtensionOfDiscreteValuationRings_of_residue_not_pth_power :
    @IsExtensionOfDiscreteValuationRings A (integralClosure A L)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (integralClosure_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue)
      (integralClosure_isDiscreteValuationRing_of_residue_not_pth_power
        (A := A) (p := p) (a := a) hresidue) :=
  by
    letI : Fact (Irreducible f) :=
      ⟨x_pow_sub_C_irreducible_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue⟩
    letI : Field L := by
      infer_instance
    letI : FaithfulSMul A L := FaithfulSMul.of_field_isFractionRing A L K L
    letI : IsDomain (integralClosure A L) :=
      integralClosure_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
    letI : IsDiscreteValuationRing (integralClosure A L) :=
      integralClosure_isDiscreteValuationRing_of_residue_not_pth_power
        (A := A) (p := p) (a := a) hresidue
    -- The normalization owner already provides the extension-of-DVR structure once the ambient
    -- field action and DVR instance are in place.
    infer_instance

/-- Helper for Lemma 15.116.8: expose the canonical normalization extension-of-DVR instance so the
final weakly-unramified statement can elaborate its target proposition. -/
private local instance integralClosure_isExtensionOfDiscreteValuationRings_inst :
    @IsExtensionOfDiscreteValuationRings A (integralClosure A L)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (integralClosure_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue)
      (integralClosure_isDiscreteValuationRing_of_residue_not_pth_power
        (A := A) (p := p) (a := a) hresidue) :=
  integralClosure_isExtensionOfDiscreteValuationRings_of_residue_not_pth_power
    (A := A) (p := p) (a := a) hresidue

/-- Helper for Lemma 15.116.8: the explicit-model weakly-unramified theorem is exactly the
maximal-ideal equality for `A ⊆ B`. -/
private theorem adjoin_pth_root_map_maximalIdeal_eq
    (hBlocal : IsLocalRing B) :
    Ideal.map (algebraMap A B) (maximalIdeal A) = @maximalIdeal B inferInstance hBlocal := by
  letI : IsDomain B :=
    adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
  letI : IsDiscreteValuationRing B :=
    adjoin_pth_root_isDiscreteValuationRing_inst (A := A) (p := p) (a := a) hresidue
  letI : IsExtensionOfDiscreteValuationRings A B :=
    adjoin_pth_root_isExtensionOfDiscreteValuationRings_inst
      (A := A) (p := p) (a := a) hresidue
  have hlocal : hBlocal = inferInstance := Subsingleton.elim _ _
  cases hlocal
  -- Rephrase weak unramifiedness of `A ⊆ B` using the owner maximal-ideal criterion.
  rw [← IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal]
  exact adjoin_pth_root_weaklyUnramified (A := A) (p := p) (a := a) hresidue

/-- Helper for Lemma 15.116.8: an equality of subalgebras transports the maximal-ideal criterion
for weakly unramified extensions once the two DVR structures are fixed. -/
private theorem transport_map_maximalIdeal_eq_of_subalgebra_eq
    {S T : Subalgebra A L}
    (h : S = T)
    (hSlocal : IsLocalRing S) (hTlocal : IsLocalRing T)
    (hmap : Ideal.map (algebraMap A S) (maximalIdeal A) =
      @maximalIdeal S inferInstance hSlocal) :
    Ideal.map (algebraMap A T) (maximalIdeal A) = @maximalIdeal T inferInstance hTlocal := by
  -- After substituting the subalgebra equality, only proof-irrelevance for the local-ring data
  -- remains.
  subst h
  have hlocal : hTlocal = hSlocal := Subsingleton.elim _ _
  cases hlocal
  exact hmap

-- Proof sketch: identify the integral closure with `B`, then use the standard criterion for
-- weakly unramified extensions of discrete valuation rings in this radicial extension: the
-- structure map is injective and the maximal ideal of `A` extends to the maximal ideal of `B`.
/-- Lemma 15.116.8 (4): the normalization extension `A ⊆ integralClosure A L` is weakly
unramified; via part `(2)`, this is exactly the extension `A ⊆ A[a^{1/p}]`. -/
theorem weaklyUnramified_integralClosure_of_residue_not_pth_power :
    @WeaklyUnramified A (integralClosure A L)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (integralClosure_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue)
      (integralClosure_isDiscreteValuationRing_of_residue_not_pth_power
        (A := A) (p := p) (a := a) hresidue) :=
  by
    letI : IsDomain B :=
      adjoin_pth_root_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
    letI : IsDiscreteValuationRing B :=
      adjoin_pth_root_isDiscreteValuationRing_inst (A := A) (p := p) (a := a) hresidue
    letI : IsDomain (integralClosure A L) :=
      integralClosure_isDomain_of_residue_not_pth_power (A := A) (p := p) (a := a) hresidue
    letI : IsDiscreteValuationRing (integralClosure A L) :=
      integralClosure_isDiscreteValuationRing_of_residue_not_pth_power
        (A := A) (p := p) (a := a) hresidue
    letI : IsExtensionOfDiscreteValuationRings A (integralClosure A L) :=
      integralClosure_isExtensionOfDiscreteValuationRings_of_residue_not_pth_power
        (A := A) (p := p) (a := a) hresidue
    let hEq :
        integralClosure A L = B :=
      integralClosure_eq_adjoin_pth_root_of_residue_not_pth_power
        (A := A) (p := p) (a := a) hresidue
    let hBlocal : IsLocalRing B := inferInstance
    let hIClocal : IsLocalRing (integralClosure A L) := inferInstance
    have hBmap : Ideal.map (algebraMap A B) (maximalIdeal A) =
        @maximalIdeal B inferInstance hBlocal := by
      -- First rewrite the explicit `A[α]` model using the owner criterion for weak unramifiedness.
      exact adjoin_pth_root_map_maximalIdeal_eq (A := A) (p := p) (a := a) hresidue hBlocal
    -- Route correction: transport only the concrete maximal-ideal equality, not the class-valued
    -- weakly-unramified theorem itself, across the normalization equality.
    rw [IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal]
    exact
      transport_map_maximalIdeal_eq_of_subalgebra_eq
        (A := A) (p := p) (a := a) (S := B) (T := integralClosure A L)
        hEq.symm hBlocal hIClocal hBmap

end
