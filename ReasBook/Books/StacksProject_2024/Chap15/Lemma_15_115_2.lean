import Mathlib
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

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
