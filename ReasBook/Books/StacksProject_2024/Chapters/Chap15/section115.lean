import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_15_115_1 (from Chap15) -/
universe u v w x y z

open Ideal IsLocalRing
open scoped TensorProduct

/-
Domain-style sampling for Remark 15.115.1:
- primary domain: reduced tensor-product base change for extensions of discrete valuation rings,
  together with the integral-closure owners on the generic and special fibers;
- sampled owner declarations:
  `IsIntegralClosure.finite`,
  `integralClosure.isDedekindDomain`,
  `IsExtensionOfDiscreteValuationRings`,
  `integralClosure_valuationRing_of_purelyInseparable`;
- owner abstraction: the source-facing objects are the canonical integral closures
  `A₁ = integralClosure A K₁` and `B₁ = integralClosure B ((L ⊗[K] K₁)_red)`, together with the
  canonical comparison map `reducedTensorBaseChangeIntegralClosureMap : A₁ →ₐ[A] B₁`;
- primitive data: the discrete valuation rings `A ⊂ B`, their fraction fields `K ⊂ L`, and the
  field extension `K₁ / K`, with the `A₁`-algebra structure on `B₁` derived from the comparison
  map;
- derived API: the canonical `Spec(B₁) → Spec(A₁)` map in general, then Dedekind/noetherian
  consequences for `B₁`, finiteness in the finite-separable case, and the
  extension-of-discrete-valuation-rings structure in the finite purely inseparable case.
-/

section

variable {A : Type u} {K : Type v} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

local notation "A1" => integralClosure A K1

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section BaseChange

variable {B : Type x} {L : Type y}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]

local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance l1CommRing : CommRing L1 :=
  Ideal.Quotient.commRing _

/-- The canonical `A`-algebra map `K₁ → L₁` induced by the right tensor-factor embedding
`K₁ → L ⊗[K] K₁` and passage to the reduced quotient. -/
private abbrev rightTensorFactorToReducedTensorBaseChange : K1 →ₐ[A] L1 :=
  (Ideal.Quotient.mkₐ A _).comp
    ((Algebra.TensorProduct.includeRight : K1 →ₐ[K] L ⊗[K] K1).restrictScalars A)

/-- The canonical map `A₁ → L₁` induced by the right tensor-factor embedding
`K₁ → L ⊗[K] K₁` and passage to the reduced quotient. -/
private abbrev integralClosureToReducedTensorBaseChange : A1 →ₐ[A] L1 :=
  (integralClosure A L1).val.comp
    rightTensorFactorToReducedTensorBaseChange.mapIntegralClosure

/-- Elements of `A₁` map into the integral closure `B₁` inside the reduced base change `L₁`. -/
private theorem integralClosureToReducedTensorBaseChange_mem_integralClosure (x : A1) :
    integralClosureToReducedTensorBaseChange x ∈ B1 := sorry

/-- The canonical map `A₁ → B₁` induced by reduced tensor-product base change. -/
def reducedTensorBaseChangeIntegralClosureMap : A1 →ₐ[A] B1 :=
  AlgHom.codRestrict
    integralClosureToReducedTensorBaseChange
    ((integralClosure B L1).restrictScalars A)
    integralClosureToReducedTensorBaseChange_mem_integralClosure

/-- The reduced tensor-product integral closure carries its canonical `A₁`-algebra structure
through `reducedTensorBaseChangeIntegralClosureMap`. -/
instance : Algebra A1 B1 :=
  reducedTensorBaseChangeIntegralClosureMap.toRingHom.toAlgebra

/-- The canonical map from the tensor base change `A₁ ⊗[A] B` to the reduced tensor-product
integral closure `B₁`. -/
noncomputable def tensorBaseChangeToReducedTensorBaseChangeIntegralClosure :
    A1 ⊗[A] B →ₐ[A1] B1 :=
  ((IsScalarTower.toAlgHom A B B1).liftEquiv A A1 B B1)

/-- If `A → B` is formally smooth for the `maximalIdeal B`-adic topology, then the reduced
tensor-product integral closure `B₁` is canonically identified with the tensor base change
`A₁ ⊗[A] B`, equivalently with `B ⊗[A] A₁` via `Algebra.TensorProduct.comm`. -/
theorem tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_bijective_of_formallySmoothForAdic
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    Function.Bijective
      (((IsScalarTower.toAlgHom A B B1).liftEquiv A A1 B B1).toFun) := by
  sorry

/-- Under the same formal-smoothness hypothesis, the canonical reduced tensor-product integral
closure `B₁` is canonically identified with the tensor base change `A₁ ⊗[A] B`. -/
noncomputable def tensorBaseChangeIntegralClosureEquivOfFormallySmoothForAdic
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    A1 ⊗[A] B ≃ₐ[A1] B1 :=
  AlgEquiv.ofBijective
    ((IsScalarTower.toAlgHom A B B1).liftEquiv A A1 B B1)
    (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_bijective_of_formallySmoothForAdic
      hfs)

-- Proof sketch: the reduced tensor product `L₁` is a finite product of finite extensions of
-- `K₁`; the integral closure of the Dedekind domain `A₁` in each factor is again Dedekind.
-- Their product is exactly `B₁`, so `B₁` is a Dedekind ring.
/-- Remark 15.115.1: if `K₁ / K` is finite, then the integral closure `B₁` of `B` in
`L₁ = (L ⊗[K] K₁)_red` is a Dedekind ring. -/
instance reducedTensorBaseChangeIntegralClosure_isDedekindRing [FiniteDimensional K K1] :
    IsDedekindRing B1 := sorry

-- Proof sketch: factor `A₁ → B₁` as the faithfully flat tensor-base-change map
-- `A₁ → A₁ ⊗[A] B` followed by the integral map `A₁ ⊗[A] B → B₁`. Surjectivity on spectra for the
-- first map comes from faithful flatness, and the second map has lying over by integrality.
/-- Remark 15.115.1: the canonical map `Spec(B₁) → Spec(A₁)` is surjective. -/
theorem primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A1 B1)) := by
  sorry

variable [FiniteDimensional K K1]

/-- Remark 15.115.1: if `K₁ / K` is finite, then the integral closure `A₁` of `A` in `K₁` is a
Dedekind domain. -/
instance : IsDedekindDomain A1 :=
  by
    sorry

instance integralClosure_localizationAtMaximal_isDiscreteValuationRing
    (p : Ideal A1) [p.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  sorry

instance reducedTensorBaseChangeIntegralClosure_localizationAtMaximal_isDomain
    (q : Ideal B1) [q.IsMaximal] :
    IsDomain (Localization.AtPrime q) := by
  sorry

instance reducedTensorBaseChangeIntegralClosure_localizationAtMaximal_isDiscreteValuationRing
    (q : Ideal B1) [q.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  sorry

-- Proof sketch: `A₁` is a Dedekind domain by the preceding instance, `B₁` is a Dedekind ring by
-- the previous theorem, and localizing at maximal ideals picks out discrete valuation factors. The
-- branch map induced by `A₁ → B₁` is therefore an injective local map between discrete valuation
-- rings, so it is canonically an extension of discrete valuation rings.
/-- For maximal ideals `p ⊂ A₁` and `q ⊂ B₁` with `q` lying over `p`, the induced localized map
`(A₁)_p → (B₁)_q` is an extension of discrete valuation rings. -/
instance isExtensionOfDiscreteValuationRings_localizationBranch
    (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal]
    [q.LiesOver p] :
    IsExtensionOfDiscreteValuationRings (Localization.AtPrime p) (Localization.AtPrime q) := by
  sorry

-- Proof sketch: the spectrum-surjectivity theorem gives at least one prime of `B₁` above each
-- maximal ideal `p ⊂ A₁`, and integrality makes that prime maximal. If `B` is henselian, then the
-- source-facing branch statement of Remark `15.115.1` says that there is only one such maximal
-- ideal, i.e. `B₁` has exactly one branch above each maximal ideal of `A₁`.
/-- Remark 15.115.1: if `K₁ / K` is finite and `B` is henselian, then for every maximal ideal
`p ⊂ A₁` there is a unique maximal ideal `q ⊂ B₁` lying over `p`. -/
theorem existsUnique_maximalIdeal_liesOver_of_reducedTensorBaseChangeIntegralClosure_of_henselian
    [HenselianLocalRing B] (p : Ideal A1) [p.IsMaximal] :
    ∃! q : Ideal B1, q.IsMaximal ∧ q.LiesOver p := by
  sorry

/- Remark 15.115.1: if `K₁ / K` is finite separable, then the integral closure `A₁` of `A` in
`K₁` is finite over `A`. This is the canonical theorem `IsIntegralClosure.finite`. -/
#check IsIntegralClosure.finite

-- Proof sketch: when `K₁ / K` is finite separable, the reduced tensor product `L₁` is a finite
-- product of finite separable extensions of `L`. The integral closure of the discrete valuation
-- ring `B` in each factor is finite over `B` by `IsIntegralClosure.finite`, so their product,
-- namely `B₁`, is finite over `B`.
/-- Remark 15.115.1: if `K₁ / K` is finite separable, then the integral closure `B₁` of `B` in
`L₁ = (L ⊗[K] K₁)_red` is finite over `B`. -/
theorem reducedTensorBaseChangeIntegralClosure_moduleFinite_of_finite_separable
    [Algebra.IsSeparable K K1] :
    Module.Finite B B1 := by
  sorry

end BaseChange

-- Proof sketch: the public `A₁` Dedekind-domain instance above gives the one-dimensional normal
-- owner. Reuse the chapter owner instance `integralClosure_henselianLocalRing` to put the finite
-- integral closure back in the henselian-local world; then a local Dedekind domain is a discrete
-- valuation ring.
/-- Over a henselian discrete valuation ring, the integral closure in a finite field extension is
again a discrete valuation ring. -/
theorem integralClosure_isDiscreteValuationRing_of_henselian
    [FiniteDimensional K K1] [HenselianLocalRing A] :
    IsDiscreteValuationRing A1 := by
  sorry

-- Proof sketch: a finite purely inseparable extension gives a unique prime above the maximal ideal
-- of `A`, so the finite integral closure `A1` is local. Combine this with the Dedekind-domain
-- property to conclude that `A1` is a discrete valuation ring.
/-- For a finite purely inseparable extension `K1 / K`, the integral closure of a discrete
valuation ring `A` in `K1` is again a discrete valuation ring. -/
theorem integralClosure_isDiscreteValuationRing_of_finite_purelyInseparable
    [FiniteDimensional K K1] [IsPurelyInseparable K K1] :
    IsDiscreteValuationRing A1 := by
  sorry

section BaseChange

variable {B : Type x} {L : Type y}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [FiniteDimensional K K1] [IsPurelyInseparable K K1]

local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

-- Proof sketch: `A₁` is a discrete valuation ring by the preceding purely inseparable integral-
-- closure instance. In the purely inseparable base-change case the reduced tensor product `L₁`
-- stays local on the generic fiber, so `B₁` is again a discrete valuation ring; the canonical map
-- `A₁ → B₁` is then the injective local algebra map from Remark 15.115.1.
/-- Remark 15.115.1: if `K₁ / K` is finite purely inseparable, then `B₁` is a domain. -/
theorem reducedTensorBaseChangeIntegralClosure_isDomain_of_finite_purelyInseparable :
    IsDomain B1 := by
  sorry

local instance :
    IsDomain B1 :=
  reducedTensorBaseChangeIntegralClosure_isDomain_of_finite_purelyInseparable

/-- Remark 15.115.1: if `K₁ / K` is finite purely inseparable, then `B₁` is a discrete valuation
ring. -/
instance reducedTensorBaseChangeIntegralClosure_isDiscreteValuationRing_of_finite_purelyInseparable :
    IsDiscreteValuationRing B1 := by
  sorry

end BaseChange

end

/-! ### Lemma_15_115_2 (from Chap15) -/
open Polynomial Ideal IsLocalRing Algebra IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u

noncomputable section

/-
Domain-style sampling for the radical-extension owners:
- primary domain: simple radical extensions presented by `AdjoinRoot (X ^ n - C π)`;
- sampled owner declarations: `Polynomial.monic_X_pow_sub_C`, `AdjoinRoot`, `AdjoinRoot.map`,
  `IntermediateField.adjoin`;
- best owner abstraction: the general `AdjoinRoot` owner over a base commutative ring/domain, with
  DVR hypotheses entering only in the later irreducibility and ramification results;
- primitive-vs-derived split: primitive data are the polynomial `X ^ n - C π`, the quotient
  `AdjoinRoot`, and the canonical map to the fraction-field presentation. Field structure,
  ramification, and tame-ramification statements are derived in the DVR specialization below.
-/

section UniformizerRootOwners

variable {A : Type u} [CommRing A]

/-- The polynomial `X^n - π` over a commutative ring `A`. -/
abbrev uniformizerRootPolynomial (π : A) (n : ℕ) : A[X] :=
  X ^ n - C π

/-- The `A`-algebra `A[π^(1/n)]`, presented as `A[X] / (X^n - π)`. -/
abbrev uniformizerRootExtensionRing (π : A) (n : ℕ) : Type u :=
  AdjoinRoot (uniformizerRootPolynomial π n)

section FractionField

variable [IsDomain A]

/-- The polynomial `X^n - π` over the fraction field of a domain `A`. -/
abbrev uniformizerRootFractionPolynomial (π : A) (n : ℕ) : (FractionRing A)[X] :=
  (uniformizerRootPolynomial π n).map (algebraMap A (FractionRing A))

/-- The `FractionRing A`-algebra `K[π^(1/n)]`, presented as
`K[X] / (X^n - algebraMap A K π)`. -/
abbrev uniformizerRootExtensionField (π : A) (n : ℕ) : Type u :=
  AdjoinRoot (uniformizerRootFractionPolynomial π n)

/-- The distinguished generator `π^(1/n)` of the radical extension field. -/
abbrev uniformizerRootExtensionGenerator (π : A) (n : ℕ) :
    uniformizerRootExtensionField π n :=
  AdjoinRoot.root _

/-- The canonical `A[π^(1/n)] → K[π^(1/n)]` map induced by the fraction-field inclusion
`A → FractionRing A`. -/
abbrev uniformizerRootExtensionRingToField (π : A) (n : ℕ) :
    uniformizerRootExtensionRing π n →+* uniformizerRootExtensionField π n :=
  AdjoinRoot.map (algebraMap A (FractionRing A))
    (uniformizerRootPolynomial π n)
    (uniformizerRootFractionPolynomial π n) dvd_rfl

/-- The radical extension ring acts on the radical extension field through the canonical map. -/
instance uniformizerRootExtensionRingToField_algebra {π : A} {n : ℕ} :
    Algebra (uniformizerRootExtensionRing π n) (uniformizerRootExtensionField π n) :=
  (uniformizerRootExtensionRingToField π n).toAlgebra

/-- The radical extension field is a scalar tower over `A ⊆ A[π^(1/n)]`. -/
instance uniformizerRootExtensionRingToField_isScalarTower {π : A} {n : ℕ} :
    IsScalarTower A (uniformizerRootExtensionRing π n) (uniformizerRootExtensionField π n) := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  change AdjoinRoot.of (uniformizerRootFractionPolynomial π n) (algebraMap A (FractionRing A) x) =
      uniformizerRootExtensionRingToField π n
        (algebraMap A (uniformizerRootExtensionRing π n) x)
  simp [uniformizerRootExtensionRingToField, AdjoinRoot.algebraMap_eq]

instance uniformizerRootExtensionField_algebra {π : A} {n : ℕ} :
    Algebra (FractionRing A) (uniformizerRootExtensionField π n) := by
  infer_instance

instance uniformizerRootExtensionField_baseAlgebra {π : A} {n : ℕ} :
    Algebra A (uniformizerRootExtensionField π n) := by
  infer_instance

instance uniformizerRootExtensionField_isScalarTower {π : A} {n : ℕ} :
    IsScalarTower A (FractionRing A) (uniformizerRootExtensionField π n) := by
  infer_instance

-- Proof sketch: evaluate the defining polynomial `X^n - π` at the quotient root in
-- `K[π^(1/n)]`; the quotient relation identifies `X^n` with `π`.
/-- The distinguished generator of `K[π^(1/n)]` is an `n`th root of `π`. -/
theorem uniformizerRootExtensionGenerator_pow_eq
    (π : A) (n : ℕ) :
    uniformizerRootExtensionGenerator π n ^ n =
      algebraMap A (uniformizerRootExtensionField π n) π := sorry

/-- The radical extension field is finite-dimensional over `FractionRing A` as soon as `n ≠ 0`. -/
noncomputable instance uniformizerRootExtensionField_finiteDimensional
    {π : A} {n : ℕ} (hn : n ≠ 0) :
    FiniteDimensional (FractionRing A) (uniformizerRootExtensionField π n) := by
  have hmonic : (uniformizerRootFractionPolynomial π n).Monic := by
    simpa [uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
      (Polynomial.monic_X_pow_sub_C (algebraMap A (FractionRing A) π) hn)
  exact hmonic.finite_adjoinRoot

end FractionField

end UniformizerRootOwners

set_option quotPrecheck false in
scoped[UniformizerRoot] notation3:max "A[" π "^(1/" n ")]" =>
  uniformizerRootExtensionRing π n

set_option quotPrecheck false in
scoped[UniformizerRoot] notation3:max "K[" π "^(1/" n ")]" =>
  uniformizerRootExtensionField π n

open scoped UniformizerRoot

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

-- Proof sketch: regard `X^n - π` over `FractionRing A` as Eisenstein at the maximal ideal of
-- `A`; the irreducibility hypothesis identifies `π` as a uniformizer, so the constant term has
-- valuation `1`, while all
-- intermediate coefficients vanish.
/-- The polynomial `X^n - π` is irreducible over `FractionRing A` when `π` is irreducible,
equivalently a uniformizer. -/
theorem uniformizerRootFractionPolynomial_irreducible
    {π : A} {n : ℕ}
    (hπ : Irreducible π)
    (hn : n ≠ 0) :
    Irreducible (uniformizerRootFractionPolynomial π n) := sorry

/-- The radical extension field carries the canonical field structure from its irreducible
`AdjoinRoot` presentation. -/
noncomputable instance uniformizerRootExtensionField_field
    {π : A} {n : ℕ}
    (hπ : Irreducible π) [NeZero n] :
    Field (uniformizerRootExtensionField π n) := by
  letI : Fact (Irreducible (uniformizerRootFractionPolynomial π n)) := by
    exact ⟨uniformizerRootFractionPolynomial_irreducible hπ (NeZero.ne n)⟩
  change Field (AdjoinRoot (uniformizerRootFractionPolynomial π n))
  infer_instance

section UniformizerRootExtension

variable {π : A} {n : ℕ}
variable (hπ : Irreducible π) (hn : 2 ≤ n)

local notation "K" => FractionRing A
local notation "R1" => uniformizerRootExtensionRing π n
local notation "K1" => uniformizerRootExtensionField π n

/- Domain-style sampling for the radical-extension conclusions:
- primary domain: tame ramification of simple radical extensions of fraction fields of discrete
  valuation rings, together with the lattice of intermediate subextensions;
- sampled owner declarations:
  `IsTamelyRamifiedWithRespectTo A L`,
  `ramificationIndex A R1`,
  `IntermediateField K K1`,
  `IntermediateField.adjoin`;
- best owner abstraction: the chapter ramification owner `ramificationIndex A R1` for part `(4)`,
  the global tame-ramification owner `IsTamelyRamifiedWithRespectTo A K1` for part `(7)`, and the
  canonical intermediate-subextension owner `IntermediateField K K1` for part `(8)`;
- primitive-vs-derived split: the branchwise residue-separability and ramification-index
  coprimality data are primitive fields of `IsTamelyRamifiedWithRespectTo`, so part `(7)` should
  expose that owner directly; the single-generator description in part `(8)` is a derived theorem
  about an already bundled intermediate field rather than primitive `Subalgebra` data plus an
  auxiliary field hypothesis.

Source/core/bridge triage:
- part `(7)`: `source-facing` statement with the canonical chapter owner
  `IsTamelyRamifiedWithRespectTo A K1`;
- part `(8)`: `source-facing` classification of canonical `IntermediateField K K1` objects by a
  power of the distinguished radical generator.
-/

section

include hπ hn

local instance : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn)⟩

local instance : Field K1 := by
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn)⟩
  exact uniformizerRootExtensionField_field hπ

local instance : FiniteDimensional K K1 := by
  exact
    uniformizerRootExtensionField_finiteDimensional
      (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn))

local instance : Algebra K K1 :=
  uniformizerRootExtensionField_algebra

local instance : Algebra A K1 :=
  uniformizerRootExtensionField_baseAlgebra

local instance : IsScalarTower A K K1 :=
  uniformizerRootExtensionField_isScalarTower

local instance : Algebra R1 K1 :=
  uniformizerRootExtensionRingToField_algebra

local instance : IsScalarTower A R1 K1 :=
  uniformizerRootExtensionRingToField_isScalarTower

section UniformizerRootExtensionDisplay

/-- The radical extension ring `A[π^(1/n)]` is a domain. -/
instance uniformizerRootExtensionRing_isDomain :
    IsDomain (A[π^(1/n)]) := sorry

-- Proof sketch: once `K1` is realized as `AdjoinRoot (X^n - π)` over the fraction field, its
-- canonical power basis has dimension `n`; equivalently, the quotient by `(X^n - π)` has
-- `FractionRing A`-dimension `n`.
/-- Lemma 15.115.2 (1): adjoining an `n`th root of a uniformizer to `FractionRing A` gives a field
extension of degree `n`. -/
theorem uniformizerRootExtensionField_finrank_eq :
    Module.finrank K (K[π^(1/n)]) = n := sorry

-- Proof sketch: compare the explicit quotient ring `A[X] / (X^n - π)` with the integral closure
-- inside `K1`; the explicit ring is finite over `A`, integrally closed, and contains the chosen
-- root, so it realizes the integral closure.
/-- Lemma 15.115.2 (2): the explicit quotient ring `A[π^(1/n)] = A[X] / (X^n - π)` is the
integral closure of `A` in `K[π^(1/n)]`. -/
theorem uniformizerRootExtensionRing_isIntegralClosure :
    IsIntegralClosure (A[π^(1/n)]) A (K[π^(1/n)]) := sorry

/-- The radical extension field `K[π^(1/n)]` is the fraction field of `A[π^(1/n)]`. -/
instance uniformizerRootExtensionRing_isFractionRing :
    IsFractionRing R1 K1 := by
  sorry

/-- Lemma 15.115.2 (3): the integral-closure ring `A[π^(1/n)]` is a discrete valuation ring. -/
instance uniformizerRootExtensionRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (A[π^(1/n)]) := sorry

/-- The canonical map `A → A[π^(1/n)]` is an extension of discrete valuation rings. -/
instance uniformizerRootExtensionRing_isExtensionOfDiscreteValuationRings :
    IsExtensionOfDiscreteValuationRings A R1 := by
  have hIntegralClosure : IsIntegralClosure R1 A K1 := by
    simpa using
      (uniformizerRootExtensionRing_isIntegralClosure hπ hn :
        IsIntegralClosure (A[π^(1/n)]) A (K[π^(1/n)]))
  have hFinite : Module.Finite A R1 := by
    simpa [uniformizerRootExtensionRing, uniformizerRootPolynomial] using
      (Polynomial.monic_X_pow_sub_C π (by omega)).finite_adjoinRoot
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn)⟩
  letI : Field K1 := uniformizerRootExtensionField_field hπ
  letI : Nontrivial K1 := inferInstance
  letI : Algebra A K1 := uniformizerRootExtensionField_baseAlgebra
  letI : Algebra K K1 := uniformizerRootExtensionField_algebra
  letI : IsScalarTower A K K1 := uniformizerRootExtensionField_isScalarTower
  letI : Algebra R1 K1 := uniformizerRootExtensionRingToField_algebra
  letI : IsScalarTower A R1 K1 := uniformizerRootExtensionRingToField_isScalarTower
  letI : IsIntegralClosure R1 A K1 := hIntegralClosure
  letI : IsFractionRing R1 K1 :=
    uniformizerRootExtensionRing_isFractionRing
  refine
    { toIsLocalHom := ?_
      algebraMap_injective := ?_ }
  · letI : Function.Injective (algebraMap A R1) :=
      algebraMap_injective_of_field_isFractionRing
        A (uniformizerRootExtensionRing π n) (FractionRing A) (uniformizerRootExtensionField π n)
    letI : FaithfulSMul A R1 :=
      (faithfulSMul_iff_algebraMap_injective A R1).2
        (algebraMap_injective_of_field_isFractionRing
          A (uniformizerRootExtensionRing π n) (FractionRing A) (uniformizerRootExtensionField π n))
    letI : Algebra.IsIntegral A R1 :=
      Algebra.IsIntegral.of_finite A R1
    exact Algebra.IsIntegral.isLocalHom A R1
  · exact
      algebraMap_injective_of_field_isFractionRing
        A (uniformizerRootExtensionRing π n) (FractionRing A) (uniformizerRootExtensionField π n)

-- Proof sketch: in the discrete valuation ring `R1 = A[π^(1/n)]`, the adjoined root generates the
-- maximal ideal, and its `n`th power is the image of the uniformizer `π`; comparing generators of
-- the two maximal ideals gives ramification index `n`.
/-- Lemma 15.115.2 (4): the ramification index of `A[π^(1/n)]` over `A` is `n`. -/
theorem ramificationIndex_uniformizerRootExtensionRing :
    ramificationIndex A (A[π^(1/n)]) = n := sorry

end UniformizerRootExtensionDisplay

-- Proof sketch: `R1` is itself a discrete valuation ring, so it has a unique maximal ideal;
-- any maximal ideal lying over `maximalIdeal A` must therefore be that maximal ideal.
/-- Lemma 15.115.2 (5): the quotient ring `A[π^(1/n)]` has a unique maximal ideal lying over the
maximal ideal of `A`. -/
theorem uniformizerRootExtensionRing_unique_maximalIdeal_liesOver
    (P : Ideal R1) (hP : P.IsMaximal) (hPOver : Ideal.LiesOver P (maximalIdeal A)) :
    P = maximalIdeal R1 := by
  letI : P.IsMaximal := hP
  letI : Ideal.LiesOver P (maximalIdeal A) := hPOver
  sorry

-- Proof sketch: reduce `A[X] / (X^n - π)` modulo the maximal ideal generated by the adjoined root;
-- the quotient identifies with the residue field of `A`, so the induced residue-field map is an
-- isomorphism.
private noncomputable abbrev uniformizerRootExtensionRingResidueFieldMap
    (P : Ideal R1) (hP : P.IsMaximal) (hPOver : Ideal.LiesOver P (maximalIdeal A)) :
    Ideal.ResidueField (maximalIdeal A) →+* Ideal.ResidueField P :=
  let _ : P.IsMaximal := hP
  let _ : Ideal.LiesOver P (maximalIdeal A) := hPOver
  Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A R1) (P.over_def (maximalIdeal A))

/-- Lemma 15.115.2 (6): for every maximal ideal of `A[π^(1/n)]` above `maximalIdeal A`, the
induced map on residue fields is bijective. -/
theorem uniformizerRootExtensionRing_residueFieldMap_bijective
    (P : Ideal R1) (hP : P.IsMaximal) (hPOver : Ideal.LiesOver P (maximalIdeal A)) :
    Function.Bijective (uniformizerRootExtensionRingResidueFieldMap P hP hPOver) := by
  sorry

end

end UniformizerRootExtension

section UniformizerRootExtensionTame

variable {π : A} {n : ℕ}

local notation "K" => FractionRing A
local notation "K1" => uniformizerRootExtensionField π n

section

variable (hπ : Irreducible π) (hn : 0 < n)

local instance : NeZero n := ⟨hn.ne'⟩

noncomputable local instance fieldK1 : Field K1 := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact uniformizerRootExtensionField_field hπ

local instance algebraAK1 : Algebra A K1 :=
  uniformizerRootExtensionField_baseAlgebra

local instance algebraKK1 : Algebra K K1 :=
  uniformizerRootExtensionField_algebra

local instance scalarTowerAKK1 : IsScalarTower A K K1 :=
  uniformizerRootExtensionField_isScalarTower

include hπ hn

-- Proof sketch: identify the explicit quotient ring `R1` with the canonical integral closure of
-- `A` in `K1` via part `(2)`, then transport the unique-branch and residue-field-bijectivity
-- statements from parts `(5)` and `(6)` across this canonical equivalence.
/-- The radical extension `K[π^(1/n)] / FractionRing A` is totally ramified with respect to `A`. -/
theorem uniformizerRootExtensionField_isTotallyRamifiedWithRespectTo
    :
    by
      let _ : NeZero n := ⟨hn.ne'⟩
      let _ : Field K1 := uniformizerRootExtensionField_field hπ
      let _ : Algebra A K1 := uniformizerRootExtensionField_baseAlgebra
      let _ : Algebra K K1 := uniformizerRootExtensionField_algebra
      let _ : IsScalarTower A K K1 := uniformizerRootExtensionField_isScalarTower
      exact IsTotallyRamifiedWithRespectTo A K1 := by
  sorry

-- Proof sketch: the residue-field map is trivial by part (6), the ramification index is `n` by
-- part (4), and the hypothesis that `n` is prime to the residue characteristic gives the
-- coprimality condition for the ramification index at every maximal ideal over `maximalIdeal A`.
/-- Lemma 15.115.2 (7): if `n` is prime to the residue characteristic of `A`, then
`K[π^(1/n)] / FractionRing A` is tamely ramified with respect to `A`. -/
theorem uniformizerRootExtensionField_isTamelyRamifiedWithRespectTo
    (hprime : PrimeToResidueCharacteristic A n) :
    by
      let _ : NeZero n := ⟨hn.ne'⟩
      let _ : Field K1 := uniformizerRootExtensionField_field hπ
      let _ : Algebra A K1 := uniformizerRootExtensionField_baseAlgebra
      let _ : Algebra K K1 := uniformizerRootExtensionField_algebra
      let _ : IsScalarTower A K K1 := uniformizerRootExtensionField_isScalarTower
      exact IsTamelyRamifiedWithRespectTo A K1 := by
  sorry

-- Proof sketch: apply Lemma `9.24.3` to the simple extension generated by the distinguished root
-- `α = π^(1/n)`. The equality `α^n = π` places `α^n` in the base field, and the tame hypothesis
-- forces every `n`th root of unity in `K[π^(1/n)]` to come from the base field.
/-- Lemma 15.115.2 (8): if `n` is prime to the residue characteristic of `A`, then every
intermediate field of `K[π^(1/n)] / FractionRing A` is generated by `π^(1/d)` for some divisor
`d` of `n`, realized as the power `α^(n / d)` of the distinguished root `α = π^(1/n)`. -/
theorem exists_intermediateField_eq_adjoin_uniformizerRootPower
    (hprime : PrimeToResidueCharacteristic A n) :
    by
      let _ : NeZero n := ⟨hn.ne'⟩
      let _ : Field K1 := uniformizerRootExtensionField_field hπ
      let _ : Algebra K K1 := uniformizerRootExtensionField_algebra
      exact
        ∀ S : IntermediateField K K1,
          ∃ d : ℕ, d ∣ n ∧
            S = K⟮uniformizerRootExtensionGenerator π n ^ (n / d)⟯ := by
  sorry

end

end UniformizerRootExtensionTame

end

/-! ### Lemma_15_115_3 (from Chap15) -/
open IsLocalRing
open RingHom
open scoped TensorProduct

universe u v w x y

section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

/- Domain-style sampling:
- primary domain: reduced tensor-product base change for extensions of discrete valuation rings,
  together with formal smoothness on the localized branches;
- sampled owner declarations:
  `reducedTensorBaseChangeIntegralClosureMap`,
  `tensorBaseChangeToReducedTensorBaseChangeIntegralClosure`,
  `isExtensionOfDiscreteValuationRings_localizationBranch`,
  `RingHom.formally_smooth_for_adic_baseChange`;
- best owner abstraction: the canonical owner is the reduced tensor-product integral closure
  `B₁ = integralClosure B ((L ⊗[K] K₁)_red)` from Remark `15.115.1`, with the tensor product
  `A₁ ⊗[A] B` only as a source-facing bridge/view;
- primitive vs. derived: the primitive data are the DVR extension `A ⊂ B`, fraction fields
  `K ⊂ L`, and the finite extension `K₁ / K`; the comparison map
  `A₁ ⊗[A] B → B₁` and the formal smoothness of localized branches are derived API.

Source/core/bridge triage:
- `source-facing`: the localized formally smooth branch map, using the tensor-product
  identification from Remark `15.115.1` as the bridge;
- `core/canonical`: `reducedTensorBaseChangeIntegralClosureMap`,
  `tensorBaseChangeIntegralClosureEquivOfFormallySmoothForAdic`, and
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the tensor-product presentation `A₁ ⊗[A] B` of the canonical owner `B₁`.
-/

-- Proof sketch: transport the formal smoothness of the base-changed tensor product
-- `A₁ → A₁ ⊗[A] B` across the identification
-- `tensorBaseChangeIntegralClosureEquivOfFormallySmoothForAdic` from Remark `15.115.1`, then
-- localize at a maximal ideal `m` of `A₁` and a maximal ideal `n` of `B₁` lying over `m`.
-- Formal smoothness for the maximal-ideal adic topology is preserved on these localized branches.
/-- Lemma 15.115.3: let `A → B` be an extension of discrete valuation rings, let `K` and `L` be
the fraction fields of `A` and `B`, and let `K₁ / K` be a finite extension. Writing
`A₁ = integralClosure A K₁` and `B₁ = integralClosure B ((L ⊗[K] K₁)_red)`, every localized branch
`(A₁)_m → (B₁)_n` with `m` a maximal ideal of `A₁` and `n` a maximal ideal of `B₁` lying over
`m` is formally smooth for the maximal-ideal-adic topology on `(B₁)_n`. -/
theorem formallySmoothForAdic_localization_baseChange_integralClosure
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B))
    (m : Ideal A1) [m.IsMaximal]
    (n : Ideal B1) [n.IsMaximal] [n.LiesOver m] :
    (Localization.localRingHom m n (algebraMap A1 B1) (n.over_def m)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime n)) := by
  sorry

end

/-! ### Lemma_15_115_4_Abhyankar_s_lemma (from Chap15) -/
open IsLocalRing
open scoped TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} {K : Type u} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable (hinj : Function.Injective (algebraMap A B))
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "B1" => A1 ⊗[A] B

-- Proof sketch: for a local homomorphism of local rings, the inverse image of the maximal ideal of
-- the target is the maximal ideal of the source; apply this to `algebraMap A B`.
/-- The maximal ideal of the target discrete valuation ring contracts to the maximal ideal of the
source under a local extension of discrete valuation rings. -/
lemma comap_maximalIdeal_of_isLocalHom :
    Ideal.comap (algebraMap A B) (maximalIdeal B) = maximalIdeal A := sorry

/-- The induced map on residue fields for the extension `A ⊂ B` of discrete valuation rings. -/
noncomputable abbrev baseResidueFieldMap :
    Ideal.ResidueField (maximalIdeal A) →+* Ideal.ResidueField (maximalIdeal B) :=
  Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
    comap_maximalIdeal_of_isLocalHom.symm

/-- The canonical algebra structure on the residue field of `B` over the residue field of `A`. -/
noncomputable instance baseResidueFieldAlgebra :
    Algebra (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField (maximalIdeal B)) :=
  baseResidueFieldMap.toAlgebra

/-- The localization of the tensor base change `B1 = A1 ⊗[A] B` at a prime above `m` is naturally
an algebra over the localization of `A1` at `m`. -/
noncomputable instance localizedIntegralClosureTensorBaseChangeAlgebra
    (m : Ideal A1) [m.IsPrime] (n : Ideal B1) [n.IsPrime] [n.LiesOver m] :
    Algebra (Localization.AtPrime m) (Localization.AtPrime n) :=
  (Localization.localRingHom m n (algebraMap A1 B1) Ideal.LiesOver.over).toAlgebra

/-- The canonical local map from `(A1)_m` to `(B1)_n` for a prime `n` of `B1` lying over
`m : Ideal A1`. -/
noncomputable abbrev localizedIntegralClosureTensorBaseChangeMap
    (m : Ideal A1) [m.IsPrime] (n : Ideal B1) [n.IsPrime] [n.LiesOver m] :
    Localization.AtPrime m →+* Localization.AtPrime n :=
  algebraMap (Localization.AtPrime m) (Localization.AtPrime n)

/-- The assertion that the localized tensor-base-change map `(A1)_m → (B1)_n` is formally smooth
for the maximal-ideal-adic topology on `(B1)_n`. -/
abbrev localizedTensorBaseChangeFormallySmoothForAdic
    (m : Ideal A1) [m.IsPrime] (n : Ideal B1) [n.IsPrime] [n.LiesOver m] : Prop :=
  let S := Localization.AtPrime n
  let _ : CommRing S := inferInstance
  RingHom.formally_smooth_for_adic.{w, max v w, max v w}
    (show Localization.AtPrime m →+* S from
      localizedIntegralClosureTensorBaseChangeMap m n)
    (show Ideal S from maximalIdeal S)

-- Proof sketch: after adjoining an `e`th root of a suitable unit, reduce to the Kummer case
-- `K1 = K[π^(1/e)]`. Lemma `15.115.2` identifies the corresponding integral closure of `A` as a
-- totally ramified degree-`e` extension, and the coprimality hypothesis makes the induced
-- extension on the `B`-side finite étale. Then the local factors above `m` are weakly unramified
-- with separable residue field over `(A1)_m`, so Lemma `15.112.5` yields formal smoothness for
-- the maximal-ideal-adic topology.
/-- Lemma 15.115.4 (Abhyankar's lemma): let `A ⊂ B` be an extension of discrete valuation rings,
let `K` be a fraction field of `A`, and let `K1 / K` be a finite extension. Write
`A1 = integralClosure A K1` and `B1 = A1 ⊗[A] B`. Assume the residue-field extension
`ResidueField (maximalIdeal B) / ResidueField (maximalIdeal A)` is separable and that the
ramification index of `A ⊂ B` is prime to the residue characteristic of `A`. If `m` is a maximal
ideal of `A1` above `maximalIdeal A` such that the ramification index of `A ⊂ B` divides the
ramification index of `A ⊂ (A1)_m` (equivalently `Ideal.ramificationIdx (maximalIdeal A) m`),
then every maximal ideal `n` of `B1` lying over `m` yields a formally smooth local extension
`(A1)_m → (B1)_n` for the `maximalIdeal (Localization.AtPrime n)`-adic topology. -/
theorem formallySmoothForAdic_localized_tensorBaseChange_of_tame_and_dvd_ramificationIdx
    (hsep : Algebra.IsSeparable
      (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField (maximalIdeal B)))
    (hprime : ∀ (p : ℕ) [Fact p.Prime] [CharP (Ideal.ResidueField (maximalIdeal A)) p],
      Nat.Coprime (Ideal.ramificationIdx (maximalIdeal A) (maximalIdeal B)) p)
    (m : Ideal A1) [m.IsMaximal] [m.LiesOver (maximalIdeal A)]
    (hmul : Ideal.ramificationIdx (maximalIdeal A) (maximalIdeal B) ∣
      Ideal.ramificationIdx (maximalIdeal A) m) :
    ∀ (n : Ideal B1) [n.IsMaximal] [n.LiesOver m],
      localizedTensorBaseChangeFormallySmoothForAdic m n := sorry

end

/-! ### Lemma_15_115_5 (from Chap15) -/
open Ideal IsLocalRing Algebra

universe u v w

section

variable {A : Type u} {L : Type v} {M : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]
variable [Field M] [Algebra A M] [Algebra L M] [Algebra (FractionRing A) M]
variable [IsScalarTower A L M] [IsScalarTower A (FractionRing A) M]
variable [IsScalarTower (FractionRing A) L M]
variable [FiniteDimensional L M]
variable [Algebra.IsSeparable L M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M
local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/-- The canonical map `B → C` on integral closures induced by the tower map `L → M`. -/
private noncomputable abbrev integralClosureTowerMap : B →ₐ[A] C :=
  (IsScalarTower.toAlgHom A L M).mapIntegralClosure

noncomputable local instance : Algebra B C :=
  integralClosureTowerMap.toAlgebra

local instance : IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

private instance liesOver_maximalIdeal_base (p : Ideal B) [p.IsMaximal] :
    p.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)).symm⟩

private instance liesOver_maximalIdeal_top (P : Ideal C) [P.IsMaximal] :
    P.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩

/- Domain-style sampling for tame ramification in an integral-closure tower:
- primary domain: ramification theory for finite separable extensions over a discrete valuation
  ring, measured on maximal ideals of integral closures;
- owner abstraction: `IsTamelyRamifiedWithRespectTo A L` from
  `Definition_15_112_7`, together with the tower bridge for `Ideal.ramificationIdx` from
  `Lemma_15_112_3`;
- source/core/bridge triage: this file is a `bridge/view` statement, lifting primitive local tame
  branch data on `B ⊆ C` to the global owner on `A ⊆ M`;
- primitive data: for each maximal branch `P` of `C`, the intermediate branch ideal is
  canonically `P.under B`; the primitive local data are that the residue-field extension
  `(P.under B).ResidueField ⊂ P.ResidueField` is separable and the relative ramification index
  `ramificationIdx (P.under B) P` is prime to the residue characteristic of `(P.under B).ResidueField`.

This local branch data is primitive theorem input, not a second packaged owner. -/

-- Proof sketch: for a maximal ideal `P` of `C`, let `p = P ∩ B`. The
-- assumption on `L/K` gives tameness of `p` over `A`, and the assumption on `M/L` gives tameness
-- of `P` over `p`. Use the tower `κ(P)/κ(p)/κA` for separability of residue fields and Lemma
-- `15.112.3` for multiplicativity of ramification indices to conclude that the ramification index
-- of `P` over `A` is still prime to the residue characteristic.
/-- Lemma 15.115.5: let `A` be a discrete valuation ring with fraction field `FractionRing A`, let
`L / FractionRing A` and `M / L` be finite separable extensions, and let `B = integralClosure A L`.
If `L / FractionRing A` is tamely ramified with respect to `A`, and for every maximal ideal
`P : Ideal C` the canonical intermediate branch ideal `P.under B` induces a tame extension on the
localized step `B_(P ∩ B) ⊂ C_P`, then `M / FractionRing A` is tamely ramified with respect to
`A`; the branchwise `LiesOver (maximalIdeal A)` conditions are supplied canonically because every
maximal ideal of an integral closure over the discrete valuation ring `A` contracts to
`maximalIdeal A`. -/
theorem isTamelyRamifiedWithRespectTo_of_tame_of_forall_tame_over_integralClosure
    (hL : IsTamelyRamifiedWithRespectTo A L)
    (hM_sep : ∀ (P : Ideal C) [P.IsMaximal],
      Algebra.IsSeparable (P.under B).ResidueField P.ResidueField)
    (hM_coprime : ∀ (P : Ideal C) [P.IsMaximal]
      (q : ℕ) [Fact q.Prime] [CharP (P.under B).ResidueField q],
        Nat.Coprime (ramificationIdx (P.under B) P) q) :
    IsTamelyRamifiedWithRespectTo A M := by
  let _ : FiniteDimensional (FractionRing A) M :=
    FiniteDimensional.trans (FractionRing A) L M
  let _ : Algebra.IsSeparable (FractionRing A) M :=
    Algebra.IsSeparable.trans (FractionRing A) L M
  sorry

end

/-! ### Lemma_15_115_6 (from Chap15) -/
universe u v w

section

/- Domain-style sampling:
- source-facing owner: `IsTamelyRamifiedWithRespectTo A L` from `Definition_15_112_7`;
- sampled canonical declarations in this domain:
  `IsTamelyRamifiedWithRespectTo`,
  `FiniteDimensional.trans`,
  `Algebra.IsSeparable.trans`,
  `FiniteDimensional.right`,
  `Algebra.isSeparable_tower_top_of_isSeparable`;
- best owner abstraction: the chapter owner `IsTamelyRamifiedWithRespectTo A L`;
- primitive-vs-derived split: the branchwise residue-field separability and ramification-index
  coprimality data stay primitive in `Definition_15_112_7`, while this file only adds the derived
  tower-descent API.

Source/core/bridge triage:
- `source-facing`: the Stacks Project tower-descent statement for tame ramification;
- `core/canonical`: `IsTamelyRamifiedWithRespectTo`, together with the standard tower finiteness
  and separability owners;
- `bridge/view`: this file, which packages those tower hypotheses into the single descended tame
  owner rather than introducing branchwise duplicate local data.
-/

end

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

local notation "K" => FractionRing A

-- Proof sketch: let `B` and `C` be the integral closures of `A` in `L` and `M`. Since `C` is
-- finite over `B`, every maximal ideal of `B` over `maximalIdeal A` is the contraction of some
-- maximal ideal of `C`. For such a pair, multiplicativity of ramification indices shows that the
-- ramification index of `B` over `A` divides the one for `C` over `A`, hence is still prime to
-- the residue characteristic. Separability of the residue-field extension for `B` over `A`
-- descends along the finite separable tower `κ(P) / κ(p) / κA`.
/-- Lemma 15.115.6: let `A` be a discrete valuation ring with fraction field `FractionRing A`. If
`M / L / K` is a tower of finite separable extensions, where `K = FractionRing A`, and `M` is
tamely ramified with respect to `A`, then `L` is tamely ramified with respect to `A`. -/
theorem isTamelyRamifiedWithRespectTo_of_tower
    {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {M : Type w} [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
    (hM : IsTamelyRamifiedWithRespectTo A M) :
    IsTamelyRamifiedWithRespectTo A L := by
  sorry

end

/-! ### Lemma_15_115_7 (from Chap15) -/
open Ideal IsLocalRing Algebra Polynomial
open scoped UniformizerRoot

universe u v

noncomputable section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

/-- Predicate asserting that after adjoining an `e`th root of the chosen uniformizer `π`, the
field `L` embeds over `FractionRing A` into a field that is unramified with respect to the
discrete valuation ring `A[π^(1/e)] = uniformizerRootExtensionRing π e`. The fraction field of
`A[π^(1/e)]` plays the role of `K[π^(1/e)]`. -/
def HasUnramifiedLiftOverUniformizerRootExtensionIndex (L : Type v) [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]
    (π : A) (e : ℕ) : Prop :=
  1 ≤ e ∧ PrimeToResidueCharacteristic A e ∧
    ∃ (_ : IsDomain (A[π^(1/e)]))
      (_ : IsDiscreteValuationRing (A[π^(1/e)])),
      ∃ (L' : Type (max u v)) (_ : Field L')
        (_ : Algebra (A[π^(1/e)]) L')
        (_ : Algebra (FractionRing (A[π^(1/e)])) L')
        (_ : IsScalarTower (A[π^(1/e)]) (FractionRing (A[π^(1/e)])) L')
        (_ : FiniteDimensional (FractionRing (A[π^(1/e)])) L')
        (_ : Algebra.IsSeparable (FractionRing (A[π^(1/e)])) L')
        (_ : Algebra (FractionRing A) (FractionRing (A[π^(1/e)])))
        (_ : Algebra (FractionRing A) L')
        (_ : IsScalarTower (FractionRing A) (FractionRing (A[π^(1/e)])) L')
        (_ : Algebra L L')
        (_ : IsScalarTower (FractionRing A) L L'),
        IsUnramifiedWithRespectTo (A[π^(1/e)]) L'

/-- Predicate asserting that there is a prime-to-residue-characteristic integer `e₀` such that for
every prime-to-residue-characteristic `d ≥ 1`, the index `d * e₀` satisfies the radical-extension
criterion above. -/
def HasEventuallyUnramifiedLiftOverUniformizerRootExtensions (L : Type v) [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]
    (π : A) : Prop :=
  ∃ e₀ : ℕ, 1 ≤ e₀ ∧ PrimeToResidueCharacteristic A e₀ ∧
    ∀ d : ℕ, 1 ≤ d → PrimeToResidueCharacteristic A d →
      HasUnramifiedLiftOverUniformizerRootExtensionIndex L π (d * e₀)

-- Proof sketch: `(2) → (1)` combines Lemma `15.115.2` with Lemmas `15.115.5` and `15.115.6`:
-- `A[π^(1/e)] / A` is tamely ramified when `e` is prime to the residue characteristic, an
-- unramified extension above it stays tame, and tameness descends to the intermediate field `L`.
-- `(3) → (2)` is immediate by taking `d = 1`. For `(1) → (3)`, let `e₀` be the least common
-- multiple of the ramification indices of the branches of the integral closure of `A` in `L`; for
-- each prime-to-residue-characteristic `d`, set `e = d * e₀`, form `A[π^(1/e)]`, decompose
-- `L ⊗_K K[π^(1/e)]` into fields, and apply Abhyankar's lemma together with Lemma `15.112.5` to
-- show that each local factor over `A[π^(1/e)]` is unramified.
/-- Lemma 15.115.7: for a discrete valuation ring `A` with fraction field `FractionRing A`, a
chosen uniformizer `π`, and a finite separable extension `L / FractionRing A`, the following are
equivalent: `L` is tamely ramified with respect to `A`; there exists an integer `e ≥ 1` invertible
in the residue field of `A` such that after adjoining an `e`th root of `π`, the field `L` embeds
into an extension unramified with respect to `A[π^(1/e)]`; and there exists an integer `e₀ ≥ 1`
invertible in the residue field of `A` such that the same conclusion holds for every multiple
`d * e₀` with `d ≥ 1` invertible in the residue field of `A`. -/
theorem isTamelyRamifiedWithRespectTo_tfae_uniformizerRootExtensionCriterion
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) :
    List.TFAE
      [ IsTamelyRamifiedWithRespectTo A L
      , ∃ e : ℕ, HasUnramifiedLiftOverUniformizerRootExtensionIndex L π e
      , HasEventuallyUnramifiedLiftOverUniformizerRootExtensions L π
      ] := sorry

end

/-! ### Lemma_15_115_8 (from Chap15) -/
universe u v w x

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

-- Proof sketch: apply the uniformizer-root criterion for tame ramification to replace `L` by an
-- extension unramified over a radical extension `K[π^(1/e)] / FractionRing A`, take the normal
-- closure over `FractionRing A`, and use the unramified Galois closure result together with the
-- stability of tame ramification under the intermediate and tower steps.
/-- Lemma 15.115.8 (1): if `L / FractionRing A` is a finite separable extension tamely ramified
with respect to the discrete valuation ring `A`, then `L` is contained in a finite Galois
extension of `FractionRing A` that is still tamely ramified with respect to `A`. -/
theorem exists_isGalois_tamelyRamifiedWithRespectTo
    (hL : IsTamelyRamifiedWithRespectTo A L) :
    ∃ (M : Type w) (_ : Field M) (_ : Algebra A M) (_ : Algebra (FractionRing A) M)
      (_ : Algebra L M) (_ : IsScalarTower A (FractionRing A) M)
      (_ : IsScalarTower (FractionRing A) L M)
      (_ : FiniteDimensional (FractionRing A) M)
      (_ : Algebra.IsSeparable (FractionRing A) M),
      IsGalois (FractionRing A) M ∧ IsTamelyRamifiedWithRespectTo A M := sorry

section

variable {L₁ : Type v} [Field L₁] [Algebra A L₁] [Algebra (FractionRing A) L₁]
variable [IsScalarTower A (FractionRing A) L₁]
variable [FiniteDimensional (FractionRing A) L₁]
variable [Algebra.IsSeparable (FractionRing A) L₁]
variable {L₂ : Type w} [Field L₂] [Algebra A L₂] [Algebra (FractionRing A) L₂]
variable [IsScalarTower A (FractionRing A) L₂]
variable [FiniteDimensional (FractionRing A) L₂]
variable [Algebra.IsSeparable (FractionRing A) L₂]

-- Proof sketch: use the uniformizer-root criterion for both `L₁` and `L₂` with a common
-- prime-to-residue-characteristic radical extension of `FractionRing A`, take a common unramified
-- overfield there via the corresponding unramified existence theorem, and then descend tameness
-- back to `FractionRing A`.
/-- Lemma 15.115.8 (2): if `L₁ / FractionRing A` and `L₂ / FractionRing A` are finite separable
extensions tamely ramified with respect to the discrete valuation ring `A`, then they are both
contained in a finite separable extension of `FractionRing A` that is still tamely ramified with
respect to `A`. -/
theorem exists_common_tamelyRamifiedWithRespectTo_extension
    (hL₁ : IsTamelyRamifiedWithRespectTo A L₁)
    (hL₂ : IsTamelyRamifiedWithRespectTo A L₂) :
    ∃ (L : Type x) (_ : Field L) (_ : Algebra A L) (_ : Algebra (FractionRing A) L)
      (_ : Algebra L₁ L) (_ : Algebra L₂ L) (_ : IsScalarTower A (FractionRing A) L)
      (_ : IsScalarTower (FractionRing A) L₁ L)
      (_ : IsScalarTower (FractionRing A) L₂ L)
      (_ : FiniteDimensional (FractionRing A) L) (_ : Algebra.IsSeparable (FractionRing A) L),
      IsTamelyRamifiedWithRespectTo A L := sorry

end

end

/-! ### Lemma_15_115_9 (from Chap15) -/
open scoped TensorProduct

universe u v w

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} {B : Type v} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K1] [Algebra A K1] [Algebra (FractionRing A) K1]
variable [IsScalarTower A (FractionRing A) K1]
variable [FiniteDimensional (FractionRing A) K1]
variable [Algebra.IsSeparable (FractionRing A) K1]

local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "KL" => K1 ⊗[K] L

-- Proof sketch: `K1 / K` is finite separable, so `KL = K1 ⊗[K] L` is a finite étale `L`-algebra
-- and hence a finite product of finite separable field extensions of `L`. Let `A1` be the
-- integral closure of `A` in `K1`. Unramifiedness of `K1 / K` identifies `A1` as finite étale
-- over `A`; base change to `B` preserves finite étaleness, so the integral closure of `B` in each
-- factor of `KL` is étale over `B`, which is exactly unramifiedness with respect to `B`.
/-- Lemma 15.115.9: if `A ⊂ B` is an extension of discrete valuation rings and
`K1 / FractionRing A` is a finite separable extension that is unramified with respect to `A`,
then `K1 ⊗[FractionRing A] FractionRing B` is a finite product of fields, and each field factor
is unramified with respect to `B`. -/
theorem exists_fractionRingTensorProduct_decomposition_with_unramifiedFactors
    (hK1 : IsUnramifiedWithRespectTo A K1) :
    ∃ (ι : Type u) (_ : Fintype ι) (L1 : ι → Type (max u v w))
      (_ : ∀ i, Field (L1 i))
      (_ : ∀ i, Algebra B (L1 i))
      (_ : ∀ i, Algebra L (L1 i))
      (_ : ∀ i, IsScalarTower B L (L1 i))
      (_ : ∀ i, FiniteDimensional L (L1 i))
      (_ : ∀ i, Algebra.IsSeparable L (L1 i)),
      Nonempty (KL ≃ₐ[L] ∀ i, L1 i) ∧
        ∀ i, IsUnramifiedWithRespectTo B (L1 i) := sorry

-- Proof sketch: write `KL = K1 ⊗[K] L` as a finite product of fields as above. By Lemma
-- `15.115.6`, after enlarging `K1` if necessary one reduces to the Kummer description from Lemma
-- `15.115.7`; then Abhyankar's lemma gives tame ramification for the intermediate factors over
-- `B`, and Lemma `15.115.5` passes tameness from the localized branches back to each global field
-- factor of `KL`.
/-- If `K1 / FractionRing A` is tamely ramified with respect to `A`, then the field factors of
`K1 ⊗[FractionRing A] FractionRing B` can be chosen tamely ramified with respect to `B`. -/
theorem exists_fractionRingTensorProduct_decomposition_with_tamelyRamifiedFactors
    (hK1 : IsTamelyRamifiedWithRespectTo A K1) :
    ∃ (ι : Type u) (_ : Fintype ι) (L1 : ι → Type (max u v w))
      (_ : ∀ i, Field (L1 i))
      (_ : ∀ i, Algebra B (L1 i))
      (_ : ∀ i, Algebra L (L1 i))
      (_ : ∀ i, IsScalarTower B L (L1 i))
      (_ : ∀ i, FiniteDimensional L (L1 i))
      (_ : ∀ i, Algebra.IsSeparable L (L1 i)),
      Nonempty (KL ≃ₐ[L] ∀ i, L1 i) ∧
        ∀ i, IsTamelyRamifiedWithRespectTo B (L1 i) := sorry

end
