import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_116_14 (from Chap15) -/
open Polynomial IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p] {ζ : A}
variable {P : A[X]}
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {ξ : FractionRing A}

local notation "K" => FractionRing A
local notation "B" => integralClosure A L
local notation "κA" => ResidueField A

/- Domain-style sampling:
* primary domain: ramification theory for finite Kummer-type extensions of the fraction field of a
  mixed-characteristic discrete valuation ring;
* sampled owner declarations:
  `IsAlgebraic`,
  `IntermediateField.adjoin.finiteDimensional`,
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension`,
  `IsUnramifiedWithRespectTo`,
  `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`,
  `residueDegree`;
* best owner abstraction: the chapter ramification owners on `L / FractionRing A` and on the
  induced extension `A ⊆ integralClosure A L`, with the Kummer root hypotheses kept as the
  source-facing primitive data;
* primitive data: the quotient-polynomial owner `IsOneSubZetaQuotientPolynomial` and the
  root-generation hypothesis for `P(z) = ξ`;
* derived API: the Galois conclusion, the unramified and totally ramified degree-`p`
  alternatives, and the weakly unramified purely inseparable residue-field alternative.

Layer triage:
* `source-facing`: the Kummer extension statements in this file;
* `core/canonical`: `IsUnramifiedWithRespectTo`, `IsTotallyRamifiedWithRespectTo`, and
  `WeaklyUnramified`;
* `bridge/view`: the separability and local-extension instances derived from the Galois conclusion
  and the integral-closure setup.
-/

private theorem isAlgebraic_of_primitiveRootElimination_generator
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ) :
    IsAlgebraic K z := by
  sorry

private theorem finiteDimensional_of_primitiveRootElimination_generator
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    FiniteDimensional K L := by
  sorry

private theorem finiteDimensional_residueField_of_integralClosure
    [FiniteDimensional K L]
    [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  sorry

section PrimitiveRootEliminationGenerator

variable (hζ : IsPrimitiveRoot ζ p)
variable (hP : IsOneSubZetaQuotientPolynomial p ζ P)
variable (z : L)
variable (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
variable (hgen : K⟮z⟯ = ⊤)

-- Proof sketch: use Lemma `15.116.13` to convert the equation `P(z) = ξ` into a Kummer equation
-- `y ^ p = w ^ p * (1 + ξ)` over `K = FractionRing A`, where `K` already contains a primitive
-- `p`th root of unity `ζ`. Kummer theory shows that adjoining a root produces a finite normal
-- separable extension, hence a Galois extension.
/-- Lemma 15.116.14 (1): let `A` be a mixed-characteristic discrete valuation ring containing a
primitive `p`th root of unity `ζ`, let `P ∈ A[X]` be a polynomial satisfying the conclusion of
Lemma `15.116.13`, let `ξ : K = FractionRing A`, and let `L` be generated over `K` by a root `z`
of `P(z) = ξ`. Then `L / K` is Galois. -/
theorem primitiveRootElimination_extension_isGalois
    (hζ : IsPrimitiveRoot ζ p)
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    IsGalois K L := sorry

local instance : FiniteDimensional K L := by
  sorry

local instance : Algebra.IsSeparable K L :=
  by
    sorry

local instance : Algebra.EssFiniteType A B := by
  sorry

local instance [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  sorry

-- Proof sketch: use the same Kummer-theoretic reduction as in part (1). The classification of
-- degree-`p` Kummer extensions over a mixed-characteristic discrete valuation ring yields the
-- four mutually exclusive possibilities recorded below.
/-- Lemma 15.116.14 (2): in the situation of part (1), either the extension is trivial, or it is
unramified of degree `p`, or it is totally ramified of degree `p`, or the integral closure of `A`
in `L` is a discrete valuation ring such that `A ⊆ integralClosure A L` is weakly unramified and
the residue-field extension is purely inseparable of degree `p`. -/
theorem primitiveRootElimination_has_ramification_case
    :
    Module.finrank K L = 1 ∨
      (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) ∨
      (Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L) ∨
      ∃ (_ : IsDiscreteValuationRing B),
        WeaklyUnramified A B ∧
          IsPurelyInseparable κA (ResidueField B) ∧
          residueDegree A B = p := sorry

-- Proof sketch: when `ξ` lies in `A`, the transformed Kummer equation is defined by a unit on the
-- right-hand side, so the corresponding degree-`p` algebra over `A` is finite étale. Over a
-- discrete valuation ring, this leaves only the trivial case or the unramified degree-`p` case.
/-- If `ξ` lies in `A`, then the extension defined by adjoining a root of `P(z) = ξ` is either
trivial or unramified of degree `p`. -/
theorem primitiveRootElimination_eq_or_unramified_of_mem_ring
    (hξ : ∃ a : A, algebraMap A K a = ξ)
    :
    Module.finrank K L = 1 ∨ (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) := sorry

-- Proof sketch: write the chosen root in a localization of the integral closure and compare
-- valuations in the transformed Kummer equation. If `ξ = a / π^n` with `n > 0` and `p ∤ n`, the
-- valuation of the root forces the ramification index to be divisible by `p`, hence equal to `p`
-- because the extension degree is at most `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∤ n`, and `a` a unit of `A`, then the extension defined by
adjoining a root of `P(z) = ξ` is in the totally ramified degree-`p` case. -/
theorem primitiveRootElimination_totally_ramified_of_uniformizer_denominator
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hndiv : ¬ p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n)
    :
    Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L := sorry

-- Proof sketch: after multiplying the transformed Kummer equation by `π^n` with `p ∣ n`, rewrite
-- it as an integral equation over `A`. The resulting normalization is weakly unramified over `A`,
-- and the non-`p`th-power residue of `a` forces the residue-field extension to be purely
-- inseparable of degree `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∣ n`, and the residue class of the unit `a` is not a `p`th
power, then the extension defined by adjoining a root of `P(z) = ξ` is in the weakly unramified
purely inseparable residue-field case of degree `p`. -/
theorem primitiveRootElimination_weakly_unramified_residue_case_of_uniformizer_denominator
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (ha : ¬ ∃ b : κA, b ^ p = residue A (a : A))
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    ∃ (_ : IsDiscreteValuationRing B),
      WeaklyUnramified A B ∧
        IsPurelyInseparable κA (ResidueField B) ∧
        residueDegree A B = p := sorry

end PrimitiveRootEliminationGenerator

end

/-! ### Lemma_15_116_15 (from Chap15) -/
open scoped TensorProduct
open Polynomial
open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y z

instance integralClosureCarrierAlgebra
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] :
    Algebra ↥(integralClosure R A) A :=
  RingHom.toAlgebra ((integralClosure R A).val.toRingHom)

section

/-- A degree-`p` extension of fraction fields is of finite level when it is generated by a root of
the quotient polynomial from Lemma `15.116.13` attached to a primitive `p`th root of unity in the
valuation ring. -/
def IsDegreePFiniteLevelExtension
    (B : Type u) [CommRing B]
    (L : Type v) [Field L] [Algebra B L]
    (M : Type w) [Field M] [Algebra L M]
    (p : ℕ) [Fact p.Prime] [FiniteDimensional L M] : Prop :=
  ∃ ζ : B, IsPrimitiveRoot ζ p ∧
    ∃ P : B[X], IsOneSubZetaQuotientPolynomial p ζ P ∧
      ∃ ξ : L, ∃ z : M,
        Polynomial.aeval z (P.map (algebraMap B L)) = algebraMap L M ξ ∧
          Algebra.adjoin L ({z} : Set M) = ⊤ ∧
          Module.finrank L M = p

-- Proof sketch: unpack the definition; the last conjunct in a finite-level presentation is
-- exactly the equality asserting that the extension has degree `p`.
/-- A degree-`p` finite-level extension has degree `p`. -/
theorem isDegreePFiniteLevelExtension_finrank_eq
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime] [FiniteDimensional L M]
    (h : IsDegreePFiniteLevelExtension B L M p) :
    Module.finrank L M = p := sorry

end

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable {K : Type x} {K1 : Type y}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "B1" => A1 ⊗[A] B

/-- The canonical algebra structure on a localization of the base-changed ring `A1 ⊗[A] B` at a
prime lying over a prime of `A1`. -/
private noncomputable instance localizedBaseChangeAlgebra
    (m : Ideal A1) [m.IsPrime] (n : Ideal B1) [n.IsPrime] [n.LiesOver m] :
    Algebra (Localization.AtPrime m) (Localization.AtPrime n) :=
  (Localization.localRingHom m n (algebraMap A1 B1) Ideal.LiesOver.over).toAlgebra

/-- A base-changed branch for `A → B` over `K1 / K` is a weak solution when the localized map
between the corresponding discrete valuation rings is weakly unramified. -/
def IsWeakSolutionBranch
    (m : Ideal A1) [m.IsMaximal] (n : Ideal B1) [n.IsMaximal] [n.LiesOver m] : Prop :=
  let _ : Algebra (Localization.AtPrime m) (Localization.AtPrime n) :=
    localizedBaseChangeAlgebra m n
  ∃ (_ : IsDomain (Localization.AtPrime m))
    (_ : IsDiscreteValuationRing (Localization.AtPrime m))
    (_ : IsDomain (Localization.AtPrime n))
    (_ : IsDiscreteValuationRing (Localization.AtPrime n))
    (_ : IsExtensionOfDiscreteValuationRings (Localization.AtPrime m) (Localization.AtPrime n)),
      WeaklyUnramified (Localization.AtPrime m) (Localization.AtPrime n)

/-- A finite extension `K1 / K` is a weak solution for the extension of discrete valuation rings
`A → B` when every branch of the localized base change `A1 ⊗[A] B` over a maximal ideal of
`A1 = integralClosure A K1` is weakly unramified. -/
def IsWeakSolutionFor : Prop :=
  ∀ (m : Ideal A1) [m.IsMaximal] (n : Ideal B1) [n.IsMaximal] [n.LiesOver m],
    IsWeakSolutionBranch m n

end

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
variable [Field M] [Algebra C M] [IsFractionRing C M] [Algebra L M] [Algebra K M]
variable [IsScalarTower K L M]
variable [FiniteDimensional L M] [IsGalois L M]

/-- The finite-level presentation alternative for the scalar extension of `M / L` along a totally
ramified extension `K1 / K`: after choosing field structures on the base changes of `L` and `M`,
the base-changed extension is generated by a root of the quotient polynomial from
Lemma `15.116.13`. -/
def HasFiniteLevelBaseChangeAlternative
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsExtensionOfDiscreteValuationRings A B]
    [IsExtensionOfDiscreteValuationRings B C]
    [IsExtensionOfDiscreteValuationRings A C]
    {p : ℕ} [Fact p.Prime] [MixedCharZero A p]
    {K : Type x} {L : Type y} {M : Type z}
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Field M] [Algebra C M] [IsFractionRing C M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional L M] [IsGalois L M]
    (K1 : Type (max x y z)) [Field K1] [Algebra A K1] [Algebra K K1]
    [IsScalarTower A K K1] : Prop :=
  ∃ (hFieldL1 : Field (TensorProduct K L K1)),
    let _ : Field (TensorProduct K L K1) := hFieldL1
        ∃ (hFieldM1 : Field (TensorProduct K M K1)),
              let _ : Field (TensorProduct K M K1) := hFieldM1
              ∃ (hAlgM1 : Algebra (TensorProduct K L K1) (TensorProduct K M K1)),
                let _ : Algebra (TensorProduct K L K1) (TensorProduct K M K1) := hAlgM1
        ∃ ζ : TensorProduct K L K1, IsPrimitiveRoot ζ p ∧
          ∃ P : (TensorProduct K L K1)[X], IsOneSubZetaQuotientPolynomial p ζ P ∧
              ∃ ξ : TensorProduct K L K1, ∃ z : TensorProduct K M K1,
                Polynomial.aeval z P =
                    algebraMap (TensorProduct K L K1) (TensorProduct K M K1) ξ ∧
                  Algebra.adjoin (TensorProduct K L K1) ({z} : Set (TensorProduct K M K1)) = ⊤

-- Proof sketch: write `M / L` as a Kummer extension using a primitive `p`th root of unity in
-- `B`. If the Kummer parameter has valuation prime to `p`, choose a totally ramified Galois
-- extension `K₁ / K` and use the base-change lemmas for weakly unramified extensions. Otherwise,
-- after normalizing the parameter, either the induced branch for `A → C` is already a weak
-- solution or the transformed equation yields the quotient-polynomial presentation encoded
-- by `IsDegreePFiniteLevelExtension`.
/-- Lemma 15.116.15: if `A ⊆ B ⊆ C` are extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`, `A` has mixed characteristic `(0, p)`, `A ⊆ B` is weakly unramified, `B`
contains a primitive `p`th root of unity, and `M / L` is Galois of degree `p`, then there exists a
finite Galois extension `K₁ / K` totally ramified with respect to `A` such that either `K₁ / K`
is a weak solution for `A → C`, or the base-changed extension
`(M ⊗[K] K₁) / (L ⊗[K] K₁)` admits a finite-level presentation. -/
theorem exists_totallyRamified_galois_extension_weakSolution_or_finiteLevel
    (hAB : WeaklyUnramified A B)
    (hζ : ∃ ζ : B, IsPrimitiveRoot ζ p)
    (hdeg : Module.finrank L M = p) :
    ∃ (K1 : Type (max x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : Algebra (FractionRing A) K1)
      (_ : IsScalarTower A (FractionRing A) K1)
      (_ : FiniteDimensional K K1) (_ : FiniteDimensional (FractionRing A) K1)
      (_ : IsGalois K K1) (_ : Algebra.IsSeparable (FractionRing A) K1)
      (_ : IsTotallyRamifiedWithRespectTo A K1),
      @IsWeakSolutionFor A C _ _ _ K1 _ _ ∨
        ∃ (hFieldL1 : Field (TensorProduct K L K1)),
          let _ : Field (TensorProduct K L K1) := hFieldL1
          ∃ (hFieldM1 : Field (TensorProduct K M K1)),
            let _ : Field (TensorProduct K M K1) := hFieldM1
            ∃ (hAlgM1 : Algebra (TensorProduct K L K1) (TensorProduct K M K1)),
            let _ : Algebra (TensorProduct K L K1) (TensorProduct K M K1) := hAlgM1
              ∃ ζ : TensorProduct K L K1, IsPrimitiveRoot ζ p ∧
                ∃ P : (TensorProduct K L K1)[X], IsOneSubZetaQuotientPolynomial p ζ P ∧
                    ∃ ξ : TensorProduct K L K1, ∃ z : TensorProduct K M K1,
                      Polynomial.aeval z P =
                          algebraMap (TensorProduct K L K1) (TensorProduct K M K1) ξ ∧
                        Algebra.adjoin
                            (TensorProduct K L K1) ({z} : Set (TensorProduct K M K1)) = ⊤ :=
      sorry

end

/-! ### Lemma_15_116_16 (from Chap15) -/
open scoped TensorProduct
open Polynomial
open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y z

instance integralClosureCarrierAlgebra
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] :
    Algebra ↥(integralClosure R A) A :=
  RingHom.toAlgebra ((integralClosure R A).val.toRingHom)

section

/-- A degree-`p` extension has finite level at most `bound` when it is generated by a root of a
quotient polynomial from Lemma `15.116.13`, say `P(z) = a / π^n`, with `n ≤ bound * e₁`, where
`e₁` is the valuation exponent of the distinguished coefficient `1 - ζ` associated to a
uniformizer power `π ^ e₁`. -/
def IsDegreePFiniteLevelExtensionAtMost
    (B : Type u) [CommRing B]
    (L : Type v) [Field L] [Algebra B L]
    (M : Type w) [Field M] [Algebra L M]
    (p bound : ℕ) [Fact p.Prime] [FiniteDimensional L M] : Prop :=
  ∃ ζ : B, IsPrimitiveRoot ζ p ∧
    ∃ π : B, ∃ e₁ n : ℕ,
      Associated (1 - ζ) (π ^ e₁) ∧ n ≤ bound * e₁ ∧
        ∃ P : B[X], IsOneSubZetaQuotientPolynomial p ζ P ∧
          ∃ a : B, ∃ z : M,
            Polynomial.aeval z (P.map (algebraMap B L)) =
                algebraMap L M ((algebraMap B L a) / (algebraMap B L π) ^ n) ∧
              Algebra.adjoin L ({z} : Set M) = ⊤ ∧
              Module.finrank L M = p

-- Proof sketch: unpack the definition; the last conjunct of the bounded finite-level presentation
-- already records that the extension has degree `p`.
/-- A bounded finite-level extension has degree `p`. -/
theorem isDegreePFiniteLevelExtensionAtMost_finrank_eq
    {B : Type u} [CommRing B]
    {L : Type v} [Field L] [Algebra B L]
    {M : Type w} [Field M] [Algebra L M]
    {p bound : ℕ} [Fact p.Prime] [FiniteDimensional L M]
    (h : IsDegreePFiniteLevelExtensionAtMost B L M p bound) :
    Module.finrank L M = p := sorry

end

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable {K : Type x} {K1 : Type y}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "B1" => A1 ⊗[A] B

/-- The canonical algebra structure on a localization of the base-changed ring `A1 ⊗[A] B` at a
prime lying over a prime of `A1`. -/
private noncomputable instance localizedBaseChangeAlgebra
    (m : Ideal A1) [m.IsPrime] (n : Ideal B1) [n.IsPrime] [n.LiesOver m] :
    Algebra (Localization.AtPrime m) (Localization.AtPrime n) :=
  (Localization.localRingHom m n (algebraMap A1 B1) Ideal.LiesOver.over).toAlgebra

/-- A base-changed branch for `A → B` over `K1 / K` is a weak solution when the localized map
between the corresponding discrete valuation rings is weakly unramified. -/
def IsWeakSolutionBranch
    (m : Ideal A1) [m.IsMaximal] (n : Ideal B1) [n.IsMaximal] [n.LiesOver m] : Prop :=
  let _ : Algebra (Localization.AtPrime m) (Localization.AtPrime n) :=
    localizedBaseChangeAlgebra m n
  ∃ (_ : IsDomain (Localization.AtPrime m))
    (_ : IsDiscreteValuationRing (Localization.AtPrime m))
    (_ : IsDomain (Localization.AtPrime n))
    (_ : IsDiscreteValuationRing (Localization.AtPrime n))
    (_ : IsExtensionOfDiscreteValuationRings (Localization.AtPrime m) (Localization.AtPrime n)),
      WeaklyUnramified (Localization.AtPrime m) (Localization.AtPrime n)

/-- A finite extension `K1 / K` is a weak solution for `A → B` when every maximal branch of the
localized base change `A1 ⊗[A] B` over `A1 = integralClosure A K1` is weakly unramified. -/
def IsWeakSolutionFor : Prop :=
  ∀ (m : Ideal A1) [m.IsMaximal] (n : Ideal B1) [n.IsMaximal] [n.LiesOver m],
    IsWeakSolutionBranch m n

end

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
variable [Field M] [Algebra C M] [IsFractionRing C M] [Algebra L M] [Algebra K M]
variable [IsScalarTower K L M]
variable [FiniteDimensional L M]

-- Proof sketch: choose a quotient-polynomial presentation of the given level-`l`
-- extension. Use the congruences `15.116.16.1` and `15.116.16.2` to run the same induction on
-- the residue coefficients as in `Lemma 15.116.12`, but in mixed characteristic and with the
-- Kummer-type polynomial from `Lemma 15.116.13`. The induction produces a finite separable
-- totally ramified extension `K₁ / K` for which either the base change of `A → C` is already a
-- weak solution, or the transformed degree-`p` extension has bounded level
-- `≤ max (0, l - 1, 2 * l - p)`.
/-- Lemma 15.116.16: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`. Assume `A` has mixed characteristic `(0, p)`, `A ⊆ B` is weakly
unramified, `M / L` is a degree-`p` extension of finite level `l > 0`, and the image of
`ResidueField A` in `ResidueField B` is exactly `⋂_{n ≥ 1} (ResidueField B)^(p^n)`. Then there
exists a finite separable extension `K₁ / K`, totally ramified with respect to `A`, such that
either `K₁ / K` is a weak solution for `A → C`, or the base-changed extension
`(M ⊗[K] K₁) / (L ⊗[K] K₁)` is a degree-`p` extension of finite level at most
`max (0, l - 1, 2 * l - p)`. -/
theorem exists_totallyRamified_separable_extension_weakSolution_or_boundedFiniteLevel
    {l : ℕ} (hl : 0 < l)
    (hAB : WeaklyUnramified A B)
    (hLM : IsDegreePFiniteLevelExtensionAtMost B L M p l)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : Algebra (FractionRing A) K1)
      (_ : IsScalarTower A (FractionRing A) K1)
      (_ : FiniteDimensional K K1) (_ : FiniteDimensional (FractionRing A) K1)
      (_ : Algebra.IsSeparable K K1) (_ : Algebra.IsSeparable (FractionRing A) K1)
      (_ : IsTotallyRamifiedWithRespectTo A K1),
      @IsWeakSolutionFor A C _ _ _ K1 _ _ ∨
        ∃ (hFieldL1 : Field (TensorProduct K L K1)),
          let _ : Field (TensorProduct K L K1) := hFieldL1
          ∃ (hAlgBL1 : Algebra B (TensorProduct K L K1)),
            let _ : Algebra B (TensorProduct K L K1) := hAlgBL1
            ∃ (hFieldM1 : Field (TensorProduct K M K1)),
              let _ : Field (TensorProduct K M K1) := hFieldM1
              ∃ (hAlgM1 : Algebra (TensorProduct K L K1) (TensorProduct K M K1)),
                let _ : Algebra (TensorProduct K L K1) (TensorProduct K M K1) := hAlgM1
                ∃ (hIntegralClosureAlg :
                    Algebra ↥(integralClosure B (TensorProduct K L K1))
                      (TensorProduct K L K1)),
                  let _ : Algebra ↥(integralClosure B (TensorProduct K L K1))
                      (TensorProduct K L K1) := hIntegralClosureAlg
                  ∃ ζ : integralClosure B (TensorProduct K L K1),
                    IsPrimitiveRoot ζ p ∧
                      ∃ π : integralClosure B (TensorProduct K L K1), ∃ e₁ n : ℕ,
                        Associated (1 - ζ) (π ^ e₁) ∧
                          n ≤ max (l - 1) (2 * l - p) * e₁ ∧
                            ∃ P : (integralClosure B (TensorProduct K L K1))[X],
                              IsOneSubZetaQuotientPolynomial p ζ P ∧
                                ∃ a : integralClosure B (TensorProduct K L K1),
                                  ∃ z : TensorProduct K M K1,
                                    Polynomial.aeval z
                                        (P.map
                                          (algebraMap
                                            ↥(integralClosure B (TensorProduct K L K1))
                                            (TensorProduct K L K1))) =
                                      algebraMap (TensorProduct K L K1)
                                        (TensorProduct K M K1)
                                        ((algebraMap
                                            ↥(integralClosure B (TensorProduct K L K1))
                                            (TensorProduct K L K1) a) /
                                          (algebraMap
                                            ↥(integralClosure B (TensorProduct K L K1))
                                            (TensorProduct K L K1) π) ^ n) ∧
                                    Algebra.adjoin (TensorProduct K L K1)
                                      ({z} : Set (TensorProduct K M K1)) = ⊤ ∧
                                    Module.rank (TensorProduct K L K1)
                                      (TensorProduct K M K1) = p := sorry

end

/-! ### Lemma_15_116_17 (from Chap15) -/
open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y z

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [IsCompleteLocalRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
variable [Field M] [Algebra C M] [IsFractionRing C M] [Algebra L M] [Algebra K M]
variable [Algebra A M] [IsScalarTower A C M] [IsScalarTower A K M]
variable [IsScalarTower K L M] [FiniteDimensional L M]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p] [IsAlgClosed (ResidueField A)]

-- Proof sketch: replace `M / L` by a finite normal closure and use Lemma `15.116.4` to reduce to
-- the normal case. Filter the resulting extension into purely inseparable degree-`p`, totally
-- ramified degree-`p`, prime-to-`p` cyclic totally ramified, and unramified steps, then induct on
-- the length of this filtration. The four basic cases are handled by Lemmas `15.116.9`,
-- `15.116.12`, `15.116.15`, and `15.116.16`, while completeness and the algebraically closed
-- residue field ensure the intermediate base changes remain in the same setup.
/-- Lemma 15.116.17: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`. Assume the residue field of `A` is algebraically closed of characteristic
`p > 0`, `A` and `B` are complete, `A ⊆ B` is weakly unramified, `M / L` is finite, and the image
of `ResidueField A` in `ResidueField B` is exactly `⋂_{n ≥ 1} (ResidueField B)^(p^n)`. Then there
exists a finite extension `K₁ / K` which is a weak solution for `A → C`. -/
theorem exists_finite_extension_weakSolution_of_complete_of_residueField_pPowerIntersection
    (hAB : WeaklyUnramified A B)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A C K M K1 := sorry

end

/-! ### Theorem_15_116_18_Epp (from Chap15) -/
open IsLocalRing

universe u v w

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type (max u v w)}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

-- Proof sketch: if `ResidueField A` has characteristic `0`, the hypothesis is vacuous and one
-- applies the prime-to-residue-characteristic case handled earlier in the chapter. In positive
-- characteristic, use Lemma `15.116.5` to pass to separably closed residue fields, then the
-- completion and Cohen-structure reductions from the textbook proof reduce the problem to
-- Lemma `15.116.17`, which yields the required finite weak solution.
/-- Theorem 15.116.18 (Epp): let `A ⊆ B` be an extension of discrete valuation rings with
fraction field `K` of `A`. Assume that whenever `ResidueField A` has positive characteristic,
every element of the stable intersection of the `p^n`-power subsets of `ResidueField B` is
separable algebraic over `ResidueField A`, where `p = ringChar (ResidueField A)`. Then there
exists a finite extension `K₁ / K` which is a weak solution for `A → B`. -/
theorem exists_finite_extension_weakSolution_of_epp_hypothesis
    (hsep :
      ringChar (ResidueField A) ≠ 0 →
        ∀ x : ResidueField B,
          x ∈ ⋂ n : ℕ+, Set.range
            (fun y : ResidueField B ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))) →
            IsAlgebraic (ResidueField A) x ∧ IsSeparable (ResidueField A) x) :
    ∃ (K1 : Type (max u v w)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A B K L K1 := sorry

end
