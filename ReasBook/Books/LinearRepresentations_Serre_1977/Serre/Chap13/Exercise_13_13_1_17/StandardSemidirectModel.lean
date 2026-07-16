import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_2_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Serre.Chap08.Exercise_8_8_4_5
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_1_4
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap13.Corollary_13_13_1_2
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_17.AugmentationKernel
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_17.RepresentativeSpan
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_17.RepresentativeIndependence
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_17.JenningsObstruction
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_17.ExponentComparison
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_17.PacketTransport

namespace Serre.Chap13.Exercise_13_13_1_17

open Matrix
open Matrix.GeneralLinearGroup
open scoped MonoidAlgebra
open scoped Pointwise
open scoped Representation
open Representation

noncomputable section

open Polynomial

section Exercise137

variable (p : ℕ) [Fact p.Prime]

section

variable (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))))

local notation "GPrime" =>
  Multiplicative (ZMod (p ^ 2)) ⋊[φ] Multiplicative (ZMod p)

/-- Helper for Exercise 13-13.1-17: the integer `p + 1` is coprime to `p²`, so it defines the
standard unit in `Z / p² Z`. -/
theorem standard_nonabelian_zmodP2_unit_coprime :
    Nat.Coprime (p + 1) (p ^ 2) := by
  -- Consecutive integers are coprime, and coprimeness survives taking powers on the second slot.
  have hcoprime : Nat.Coprime (p + 1) p := by
    rw [Nat.coprime_self_add_left]
    exact Nat.coprime_one_left p
  exact hcoprime.pow_right 2

/-- Helper for Exercise 13-13.1-17: the unit `1 + p` in `Z / p² Z` is the owner of Serre's
standard semidirect action. -/
def standard_nonabelian_zmodP2_unit : (ZMod (p ^ 2))ˣ :=
  ZMod.unitOfCoprime (p + 1) (standard_nonabelian_zmodP2_unit_coprime (p := p))

/-- Helper for Exercise 13-13.1-17: powers of `Multiplicative.ofAdd 1` in `Z / p Z` recover the
corresponding natural-number classes. -/
theorem ofAdd_one_pow_mod_p (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod p)) ^ n =
      Multiplicative.ofAdd ((n : ℕ) : ZMod p) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [pow_succ, ih]

/-- Helper for Exercise 13-13.1-17: the semidirect action is already determined by the image of
the additive generator `1 ∈ Z / p Z`. -/
theorem semidirect_action_trivial_of_generator_eq_one
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod p)) = 1) :
    φ = 1 := by
  ext x y
  -- Every element of `Multiplicative (ZMod p)` is a power of the class of `1`.
  have hxpow :
      (Multiplicative.ofAdd (1 : ZMod p)) ^ x.val =
        Multiplicative.ofAdd x := by
    simpa [ZMod.natCast_val] using (ofAdd_one_pow_mod_p (p := p) x.val)
  calc
    φ (Multiplicative.ofAdd x) y
        = φ ((Multiplicative.ofAdd (1 : ZMod p)) ^ x.val) y := by
            rw [← hxpow]
    _ = ((φ (Multiplicative.ofAdd (1 : ZMod p))) ^ x.val) y := by
          rw [map_pow]
    _ = y := by
          simp [hgen]

/-- Helper for Exercise 13-13.1-17: if the `Z / p Z`-action is trivial, the semidirect product is
just the direct product of two abelian factors. -/
theorem semidirectProduct_isMulCommutative_of_action_trivial
    (htriv : φ = 1) :
    IsMulCommutative GPrime := by
  refine IsMulCommutative.of_comm ?_
  intro a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  ext <;> simp [htriv, mul_comm, mul_assoc]

/-- Helper for Exercise 13-13.1-17: the acting generator has `p`-th power equal to `1` because
the source `Z / p Z` has exponent `p`. -/
theorem semidirect_action_generator_pow_p :
    (φ (Multiplicative.ofAdd (1 : ZMod p))) ^ p = 1 := by
  have hsrc : (Multiplicative.ofAdd (1 : ZMod p)) ^ p = 1 := by
    rw [ofAdd_one_pow_mod_p (p := p) p, ZMod.natCast_self]
    rfl
  simpa using congrArg φ hsrc

/-- Helper for Exercise 13-13.1-17: noncommutativity forces the `Z / p Z`-generator to act
nontrivially. -/
theorem semidirect_action_generator_ne_one_of_noncommutative
    (hφ : ¬ IsMulCommutative GPrime) :
    φ (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 := by
  intro hgen
  apply hφ
  exact semidirectProduct_isMulCommutative_of_action_trivial
    (p := p) (φ := φ) (semidirect_action_trivial_of_generator_eq_one (p := p) (φ := φ) hgen)

/-- Helper for Exercise 13-13.1-17: in the nonabelian case, the acting generator has exact order
`p` inside `Aut(Z / p² Z)`. -/
theorem semidirect_action_generator_orderOf_eq_p
    (hφ : ¬ IsMulCommutative GPrime) :
    orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) = p := by
  -- The previous two lemmas reduce the order computation to the prime-order criterion.
  exact orderOf_eq_prime
    (semidirect_action_generator_pow_p (p := p) (φ := φ))
    (semidirect_action_generator_ne_one_of_noncommutative (p := p) (φ := φ) hφ)

/-- Helper for Exercise 13-13.1-17: Serre's standard unit has order dividing `p`, so the
`Z / p Z`-parameter really factors through the `1 + p` action modulo `p²`. -/
theorem standard_nonabelian_zmodP2_unit_pow_p :
    (standard_nonabelian_zmodP2_unit (p := p)) ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  unfold standard_nonabelian_zmodP2_unit
  rw [ZMod.coe_unitOfCoprime, Nat.cast_add, Nat.cast_one, add_comm]
  have hp : Nat.Prime p := Fact.out
  -- Expand `(1 + p)^p` in characteristic `p`; every nontrivial term is divisible by `p²`.
  obtain ⟨r, hr0⟩ :=
    exists_add_pow_prime_pow_eq hp (1 : ZMod (p ^ 2)) (p : ZMod (p ^ 2)) 1
  have hr :
      ((1 + (p : ZMod (p ^ 2))) ^ p) =
        1 + (p : ZMod (p ^ 2)) ^ p + (p : ZMod (p ^ 2)) * 1 * (p : ZMod (p ^ 2)) * r := by
    simpa [pow_one] using hr0
  rw [hr]
  have hppow : ((p : ZMod (p ^ 2)) ^ p) = 0 := by
    exact ZMod.natCast_pow_eq_zero_of_le p (show 2 ≤ p by exact hp.two_le)
  have hp2 : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by
    exact ZMod.natCast_pow_eq_zero_of_le p (show 2 ≤ 2 by decide)
  rw [hppow]
  ring_nf
  simp [hp2]

/-- Helper for Exercise 13-13.1-17: the standard unit `1 + p` is nontrivial modulo `p²`. -/
theorem standard_nonabelian_zmodP2_unit_ne_one :
    standard_nonabelian_zmodP2_unit (p := p) ≠ 1 := by
  intro hunit
  -- Compare underlying residue classes and isolate the surviving class of `p`.
  apply_fun Units.val at hunit
  unfold standard_nonabelian_zmodP2_unit at hunit
  rw [ZMod.coe_unitOfCoprime, Nat.cast_add, Nat.cast_one] at hunit
  have hp : Nat.Prime p := Fact.out
  have hp_lt : p < p ^ 2 := by
    nlinarith [hp.two_le]
  have hp_cast_ne_zero : ((p : ℕ) : ZMod (p ^ 2)) ≠ 0 := by
    intro hzero
    rw [ZMod.natCast_eq_zero_iff] at hzero
    exact (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt) hzero
  have hp_zero : ((p : ℕ) : ZMod (p ^ 2)) = 0 := by
    have hsub := congrArg (fun x : ZMod (p ^ 2) => x - 1) hunit
    simpa using hsub
  exact hp_cast_ne_zero hp_zero

/-- Helper for Exercise 13-13.1-17: the standard unit `1 + p` has exact order `p`. -/
theorem standard_nonabelian_zmodP2_unit_order :
    orderOf (standard_nonabelian_zmodP2_unit (p := p)) = p := by
  -- The previous two lemmas put `1 + p` in the unique nontrivial `p`-torsion class.
  exact orderOf_eq_prime
    (standard_nonabelian_zmodP2_unit_pow_p (p := p))
    (standard_nonabelian_zmodP2_unit_ne_one (p := p))

/-- Helper for Exercise 13-13.1-17: the unit group of `Z / p² Z` is cyclic for every prime `p`.
The odd-prime case uses the general prime-power theorem, and `p = 2` reduces to `ZMod 4`. -/
theorem zmodP2_units_isCyclic :
    IsCyclic (ZMod (p ^ 2))ˣ := by
  by_cases hp2 : p = 2
  · subst hp2
    simpa using ZMod.isCyclic_units_four
  · exact ZMod.isCyclic_units_of_prime_pow p (Fact.out) hp2 2

/-- Helper for Exercise 13-13.1-17: every order-`p` unit in `(Z / p² Z)ˣ` lies in the subgroup
generated by Serre's standard unit `1 + p`. -/
theorem order_p_unit_mem_standard_zpowers
    (u : (ZMod (p ^ 2))ˣ) (hu_pow : u ^ p = 1) (_hu_ne : u ≠ 1) :
    u ∈ Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) := by
  letI : IsCyclic (ZMod (p ^ 2))ˣ := zmodP2_units_isCyclic (p := p)
  let K : Subgroup ((ZMod (p ^ 2))ˣ) :=
    (powMonoidHom p : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
  have hu_mem : u ∈ K := by
    -- The kernel of the `p`-th-power map is exactly the `p`-torsion layer.
    change u ^ p = 1
    exact hu_pow
  have hs_le : Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) ≤ K := by
    -- The standard unit also lies in that `p`-torsion layer.
    rw [Subgroup.zpowers_le]
    change (standard_nonabelian_zmodP2_unit (p := p)) ^ p = 1
    exact standard_nonabelian_zmodP2_unit_pow_p (p := p)
  have hK_card : Nat.card K = p := by
    -- In the cyclic unit group of cardinal `p (p - 1)`, the `p`-power kernel has cardinal `p`.
    rw [show Nat.card K =
        Nat.card ↥((powMonoidHom p : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker) by
        rfl]
    rw [IsCyclic.card_powMonoidHom_ker ((ZMod (p ^ 2))ˣ) p]
    have hcard_units : Nat.card ((ZMod (p ^ 2))ˣ) = p * (p - 1) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      simpa [pow_succ] using
        Nat.totient_prime_pow (Fact.out) (show 0 < 2 by decide)
    rw [hcard_units, Nat.gcd_comm]
    exact Nat.gcd_eq_left (dvd_mul_right p (p - 1))
  have hz_card :
      Nat.card (Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p))) = p := by
    -- The subgroup generated by `1 + p` has the same cardinality `p`.
    rw [Nat.card_zpowers, standard_nonabelian_zmodP2_unit_order (p := p)]
  have htop_card :
      Nat.card
          ((Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p))).subgroupOf K) =
        Nat.card K := by
    rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hs_le).toEquiv), hz_card, hK_card]
  have htop :
      (Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p))).subgroupOf K = ⊤ := by
    exact (Subgroup.card_eq_iff_eq_top _).mp htop_card
  have hEq : Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) = K := by
    -- Equal cardinality upgrades the inclusion to equality of subgroups.
    exact le_antisymm hs_le (Subgroup.subgroupOf_eq_top.mp htop)
  have hu_mem' : u ∈ Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) := by
    rw [hEq]
    exact hu_mem
  exact hu_mem'

/-- Helper for Exercise 13-13.1-17: the chosen order-`p` unit kills `p` inside the lifted additive
presentation of `Z / p Z`. -/
theorem standard_nonabelian_zmodP2_unit_zmultiples_zero :
    zmultiplesHom (Additive ((ZMod (p ^ 2))ˣ))
        (Additive.ofMul (standard_nonabelian_zmodP2_unit (p := p))) p =
      0 := by
  -- `ZMod.lift` only needs the generator to have `p`-th power equal to `1`.
  change (standard_nonabelian_zmodP2_unit (p := p)) ^ p = 1
  simpa using standard_nonabelian_zmodP2_unit_pow_p (p := p)

/-- Helper for Exercise 13-13.1-17: the `Z / p Z`-parameter maps to powers of the standard
`1 + p` unit in `(Z / p² Z)ˣ`. -/
def standard_nonabelian_zmodP2_units_hom :
    Multiplicative (ZMod p) →* (ZMod (p ^ 2))ˣ :=
  AddMonoidHom.toMultiplicativeLeft <|
    ZMod.lift p
      ⟨zmultiplesHom (Additive ((ZMod (p ^ 2))ˣ))
          (Additive.ofMul (standard_nonabelian_zmodP2_unit (p := p))),
        standard_nonabelian_zmodP2_unit_zmultiples_zero (p := p)⟩

/-- Helper for Exercise 13-13.1-17: Serre's standard `Z/p² ⋊ Z/p` model is governed by the
`1 + p` automorphism of `Z / p² Z`. -/
def standard_nonabelian_zmodP2_action :
    Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))) :=
  ((MulAutMultiplicative (ZMod (p ^ 2))).symm.toMonoidHom).comp <|
    ((ZMod.AddAutEquivUnits (p ^ 2)).symm.toMonoidHom).comp <|
      standard_nonabelian_zmodP2_units_hom (p := p)

local notation "StandardGPrime" =>
  Multiplicative (ZMod (p ^ 2)) ⋊[standard_nonabelian_zmodP2_action (p := p)] Multiplicative
    (ZMod p)

/-- Helper for Exercise 13-13.1-17: the distinguished `Z / p² Z` generator in Serre's standard
semidirect model. -/
def standard_nonabelian_semidirect_inl_one : StandardGPrime :=
  SemidirectProduct.inl (φ := standard_nonabelian_zmodP2_action (p := p))
    (Multiplicative.ofAdd (1 : ZMod (p ^ 2)))

/-- Helper for Exercise 13-13.1-17: the canonical standard semidirect model is finite because its
underlying type is equivalent to a finite product. -/
instance standard_nonabelian_zmod_semidirectProduct_finite : Finite StandardGPrime :=
  Finite.of_equiv
    (Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod p))
    (SemidirectProduct.equivProd
      (N := Multiplicative (ZMod (p ^ 2)))
      (G := Multiplicative (ZMod p))
      (φ := standard_nonabelian_zmodP2_action (p := p))).symm

/-- Helper for Exercise 13-13.1-17: the canonical standard semidirect model has order `p^3`. -/
theorem standard_nonabelian_zmod_semidirectProduct_card_p_cubed :
    Nat.card StandardGPrime = p ^ 3 := by
  -- Forget the multiplication and count the underlying product type.
  rw [SemidirectProduct.card]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (p ^ 2)) ≃ ZMod (p ^ 2))]
  rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p)]
  rw [Nat.card_eq_fintype_card, ZMod.card]
  ring

/-- Helper for Exercise 13-13.1-17: the standard semidirect-model group algebra has `ℚ`-dimension
`p^3`. -/
theorem standard_nonabelian_zmod_semidirectProduct_groupAlgebra_finrank_p_cubed :
    Module.finrank ℚ ℚ[StandardGPrime] = p ^ 3 := by
  -- The semidirect product has the expected order `p^2 * p`.
  rw [groupAlgebra_finrank_eq_natCard (k := ℚ) (G := StandardGPrime),
    standard_nonabelian_zmod_semidirectProduct_card_p_cubed (p := p)]

/-- Helper for Exercise 13-13.1-17: in the canonical standard semidirect model, the `Z / p² Z`
generator still has nontrivial `p`-th power. -/
theorem standard_nonabelian_semidirect_inl_one_pow_p_ne_one :
    (standard_nonabelian_semidirect_inl_one (p := p)) ^ p ≠ 1 := by
  simpa [standard_nonabelian_semidirect_inl_one] using
    semidirect_inl_one_pow_p_ne_one (p := p) (φ := standard_nonabelian_zmodP2_action (p := p))

/-- Helper for Exercise 13-13.1-17: the semidirect Jennings obstruction reads off the coefficient
of the surviving basis element `a^p`. -/
def standard_nonabelian_semidirect_pth_power_coefficient :
    (ZMod p)[StandardGPrime] →ₗ[ZMod p] ZMod p where
  toFun z := z ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p)
  map_add' x y := by
    rfl
  map_smul' c z := by
    rfl

/-- Helper for Exercise 13-13.1-17: the coefficient detector already evaluates to `1` on Serre's
distinguished source-side class `([a] - 1)^p`. -/
theorem standard_nonabelian_semidirect_pth_power_coefficient_yRaw_pow_p :
    standard_nonabelian_semidirect_pth_power_coefficient (p := p)
      (((MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) ^
        p) = 1 := by
  rw [monoidAlgebra_of_sub_one_pow_p (p := p) (G := StandardGPrime)
    (standard_nonabelian_semidirect_inl_one (p := p))]
  have hpow_ne :
      (standard_nonabelian_semidirect_inl_one (p := p)) ^ p ≠ 1 :=
    standard_nonabelian_semidirect_inl_one_pow_p_ne_one (p := p)
  -- Evaluate the surviving basis vector `[(a^p)] - 1` at `a^p`; the scalar part vanishes because
  -- `a^p ≠ 1`.
  unfold standard_nonabelian_semidirect_pth_power_coefficient
  have hone_coeff :
      (1 : (ZMod p)[StandardGPrime])
        ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) = 0 := by
    simp [MonoidAlgebra.one_def, hpow_ne]
  simpa [sub_eq_add_neg, hone_coeff] using
    (show (MonoidAlgebra.of (ZMod p) StandardGPrime
        ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p))
      ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) = 1 by
        simp [MonoidAlgebra.of_apply])

/-- Helper for Exercise 13-13.1-17: on the standard semidirect model, the augmentation generator
coming from the `Z / p² Z` factor has nonzero `p`-th power over `𝔽_p`. -/
theorem standard_nonabelian_semidirect_inl_sub_one_pow_p_ne_zero :
    ((MonoidAlgebra.of (ZMod p) StandardGPrime
        (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) ^ p ≠
      0 := by
  intro hzero
  -- Route correction: package the surviving `a^p` coefficient as a linear functional so the later
  -- graded-quotient detector can reuse the same calculation instead of redoing it ad hoc.
  have hcoeff :
      standard_nonabelian_semidirect_pth_power_coefficient (p := p)
        (((MonoidAlgebra.of (ZMod p) StandardGPrime
            (standard_nonabelian_semidirect_inl_one (p := p)) :
              (ZMod p)[StandardGPrime]) - 1) ^ p) =
        standard_nonabelian_semidirect_pth_power_coefficient (p := p) 0 := by
    exact congrArg (standard_nonabelian_semidirect_pth_power_coefficient (p := p)) hzero
  rw [standard_nonabelian_semidirect_pth_power_coefficient_yRaw_pow_p (p := p)] at hcoeff
  have hzero_coeff :
      standard_nonabelian_semidirect_pth_power_coefficient (p := p) 0 = 0 := rfl
  rw [hzero_coeff] at hcoeff
  have hone_eq_zero : (1 : ZMod p) = 0 := by
    exact hcoeff
  exact one_ne_zero hone_eq_zero

/-- Helper for Exercise 13-13.1-17: the distinguished semidirect `Z / p² Z` generator has
trivial `p²`-th power. -/
theorem standard_nonabelian_semidirect_inl_one_pow_p_sq_eq_one :
    (standard_nonabelian_semidirect_inl_one (p := p)) ^ (p ^ 2) = 1 := by
  -- Compute the full `p²`-power in the normal cyclic factor.
  calc
    (standard_nonabelian_semidirect_inl_one (p := p)) ^ (p ^ 2)
        = (SemidirectProduct.inl
            (φ := standard_nonabelian_zmodP2_action (p := p))
            (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) : StandardGPrime) ^ (p ^ 2) := by
              rfl
    _ = SemidirectProduct.inl
          (φ := standard_nonabelian_zmodP2_action (p := p))
          ((Multiplicative.ofAdd (1 : ZMod (p ^ 2))) ^ (p ^ 2)) := by
            exact
              ((SemidirectProduct.inl
                (φ := standard_nonabelian_zmodP2_action (p := p))).map_pow
                (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) (p ^ 2)).symm
    _ = SemidirectProduct.inl
          (φ := standard_nonabelian_zmodP2_action (p := p))
          (Multiplicative.ofAdd (((p ^ 2 : ℕ) : ZMod (p ^ 2)))) := by
            rw [ofAdd_one_pow (p := p) (p ^ 2)]
    _ = 1 := by
          rw [ZMod.natCast_self]
          rfl

/-- Helper for Exercise 13-13.1-17: the distinguished semidirect augmentation generator is
nilpotent of order at most `p²`. -/
theorem standard_nonabelian_semidirect_inl_sub_one_isNilpotent :
    IsNilpotent
      ((MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) := by
  refine ⟨p ^ 2, ?_⟩
  -- Apply the characteristic-`p` formula twice and then use the `p²`-torsion of the source
  -- generator.
  calc
    (((MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) ^
          (p ^ 2))
        = ((((MonoidAlgebra.of (ZMod p) StandardGPrime
                (standard_nonabelian_semidirect_inl_one (p := p)) :
                  (ZMod p)[StandardGPrime]) - 1) ^ p) ^ p) := by
              simpa [pow_two] using
                (pow_mul
                  ((MonoidAlgebra.of (ZMod p) StandardGPrime
                      (standard_nonabelian_semidirect_inl_one (p := p)) :
                        (ZMod p)[StandardGPrime]) - 1) p p)
    _ = ((MonoidAlgebra.of (ZMod p) StandardGPrime
            ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) :
              (ZMod p)[StandardGPrime]) - 1) ^ p := by
          rw [monoidAlgebra_of_sub_one_pow_p (p := p) (G := StandardGPrime)
            (standard_nonabelian_semidirect_inl_one (p := p))]
    _ = MonoidAlgebra.of (ZMod p) StandardGPrime
          (((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) ^ p) - 1 := by
            rw [monoidAlgebra_of_sub_one_pow_p (p := p) (G := StandardGPrime)
              ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p)]
    _ = 0 := by
          have hpow :
              (((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) ^ p) = 1 := by
            simpa [pow_mul, pow_two, mul_comm] using
              standard_nonabelian_semidirect_inl_one_pow_p_sq_eq_one (p := p)
          rw [hpow]
          ext g
          by_cases hg : g = 1
          · subst hg
            simp [MonoidAlgebra.of, MonoidAlgebra.one_def]
          · simp [MonoidAlgebra.of, MonoidAlgebra.one_def, hg]

/-- Helper for Exercise 13-13.1-17: the canonical standard semidirect model carries the usual
augmentation map to `𝔽_p`. -/
def standard_nonabelian_semidirect_augmentation :
    (ZMod p)[StandardGPrime] →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) StandardGPrime (1 : StandardGPrime →* ZMod p)

/-- Helper for Exercise 13-13.1-17: the standard semidirect augmentation map is surjective. -/
theorem standard_nonabelian_semidirect_augmentation_surjective :
    Function.Surjective (standard_nonabelian_semidirect_augmentation (p := p)) := by
  intro z
  refine ⟨algebraMap (ZMod p) ((ZMod p)[StandardGPrime]) z, ?_⟩
  -- The augmentation sends scalar coefficients to the same scalar in `𝔽_p`.
  simp [standard_nonabelian_semidirect_augmentation]

/-- Helper for Exercise 13-13.1-17: Serre's distinguished semidirect augmentation generator
belongs to the augmentation kernel. -/
theorem standard_nonabelian_semidirect_inl_sub_one_mem_augmentationKernel :
    let yRaw : (ZMod p)[StandardGPrime] :=
      (MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1
    yRaw ∈ RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom := by
  -- The augmentation again sends `[a]` and `1` to the same scalar `1`.
  rw [RingHom.mem_ker]
  simp [standard_nonabelian_semidirect_augmentation]

/-- Helper for Exercise 13-13.1-17: the standard semidirect augmentation kernel is exactly the
span of the standard generators `[g] - 1`. -/
theorem standard_nonabelian_semidirect_augmentationKernel_eq_span_sub_one :
    RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom =
      Ideal.span
        (Set.range fun g : StandardGPrime =>
          (MonoidAlgebra.of (ZMod p) StandardGPrime g : (ZMod p)[StandardGPrime]) - 1) := by
  -- The same finite-group augmentation owner applies unchanged to the standard semidirect model.
  simpa [standard_nonabelian_semidirect_augmentation] using
    (monoidAlgebra_augmentationKernel_eq_span_sub_one (p := p) (G := StandardGPrime))

/-- Helper for Exercise 13-13.1-17: the standard semidirect augmentation kernel is maximal because
the quotient is the field `𝔽_p`. -/
theorem standard_nonabelian_semidirect_augmentationKernel_isMaximal :
    (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom).IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective
    (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom
    (standard_nonabelian_semidirect_augmentation_surjective (p := p))

/-- Helper for Exercise 13-13.1-17: the ring Jacobson radical is always contained in the maximal
standard semidirect augmentation kernel. -/
theorem standard_nonabelian_semidirect_jacobson_le_augmentationKernel :
    Ring.jacobson ((ZMod p)[StandardGPrime]) ≤
      RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom := by
  letI :
      (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom).IsMaximal :=
    standard_nonabelian_semidirect_augmentationKernel_isMaximal (p := p)
  -- The Jacobson radical sits inside every maximal ideal, so it sits inside the augmentation
  -- kernel of the standard model.
  exact Ring.jacobson_le_of_isMaximal _

/-- Helper for Exercise 13-13.1-17: Serre's generator-level Jacobson lemma upgrades the concrete
standard semidirect augmentation kernel to a subideal of the Jacobson radical. -/
theorem standard_nonabelian_semidirect_augmentationKernel_le_jacobson :
    RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom ≤
      Ring.jacobson ((ZMod p)[StandardGPrime]) := by
  have hspan :
      Ideal.span
          (Set.range fun g : StandardGPrime =>
            (MonoidAlgebra.of (ZMod p) StandardGPrime g : (ZMod p)[StandardGPrime]) - 1) ≤
        Ring.jacobson ((ZMod p)[StandardGPrime]) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    have hP : IsPGroup p StandardGPrime :=
      IsPGroup.of_card (standard_nonabelian_zmod_semidirectProduct_card_p_cubed (p := p))
    -- The standard semidirect generators are still augmentation generators of a `p`-group group
    -- algebra, so the same Jacobson owner applies.
    simpa using
      p_group_generator_sub_one_mem_jacobson
        (p := p) (G := StandardGPrime) hP g
  -- Rewrite the augmentation kernel by the span of the standard generators and apply the new
  -- generator-level Jacobson owner.
  rw [standard_nonabelian_semidirect_augmentationKernel_eq_span_sub_one (p := p)]
  exact hspan

/-- Helper for Exercise 13-13.1-17: on the canonical standard semidirect model, the Jacobson
radical is exactly the augmentation kernel. -/
theorem standard_nonabelian_semidirect_jacobson_eq_augmentationKernel :
    Ring.jacobson ((ZMod p)[StandardGPrime]) =
      RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom := by
  -- The easy maximal-ideal inclusion and the new generator-level inclusion meet in the middle.
  exact le_antisymm
    (standard_nonabelian_semidirect_jacobson_le_augmentationKernel (p := p))
    (standard_nonabelian_semidirect_augmentationKernel_le_jacobson (p := p))

/-- Helper for Exercise 13-13.1-17: every nonabelian semidirect product
`(Z / p² Z) ⋊ (Z / p Z)` is multiplicatively equivalent to Serre's standard action model. -/
theorem nonabelian_zmod_semidirectProduct_mulEquiv_standard_action
    (hφ : ¬ IsMulCommutative GPrime) :
    Nonempty (GPrime ≃* StandardGPrime) := by
  -- Route correction: separate the canonical semidirect normalization from the later packet
  -- classification so the remaining blocker is only the standard-model representation theory.
  let toUnits : MulAut (Multiplicative (ZMod (p ^ 2))) →* (ZMod (p ^ 2))ˣ :=
    (ZMod.AddAutEquivUnits (p ^ 2)).toMonoidHom.comp
      (MulAutMultiplicative (ZMod (p ^ 2))).toMonoidHom
  have htoUnits_inj : Function.Injective fun f => toUnits f := by
    intro a b hab
    apply (MulAutMultiplicative (ZMod (p ^ 2))).injective
    apply (ZMod.AddAutEquivUnits (p ^ 2)).injective
    exact hab
  let uφ : (ZMod (p ^ 2))ˣ := toUnits (φ (Multiplicative.ofAdd (1 : ZMod p)))
  have hgenerator_ne_one :
      φ (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 :=
    semidirect_action_generator_ne_one_of_noncommutative (p := p) (φ := φ) hφ
  have hgenerator_order :
      orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) = p :=
    semidirect_action_generator_orderOf_eq_p (p := p) (φ := φ) hφ
  have huφ_pow : uφ ^ p = 1 := by
    -- Transport the order-`p` relation from the acting automorphism to the unit picture.
    unfold uφ
    simpa [MonoidHom.map_pow] using
      congrArg toUnits (semidirect_action_generator_pow_p (p := p) (φ := φ))
  have huφ_ne : uφ ≠ 1 := by
    -- Nontriviality is preserved because the automorphism-to-unit conversion is injective.
    intro huφ_one
    apply hgenerator_ne_one
    apply htoUnits_inj
    simpa [uφ] using huφ_one
  have huφ_order : orderOf uφ = p := by
    -- The same injective conversion preserves the exact order `p`.
    unfold uφ
    rw [orderOf_injective toUnits htoUnits_inj]
    exact hgenerator_order
  have huφ_mem :
      uφ ∈ Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) := by
    -- The acting generator already lands in the unique order-`p` subgroup generated by `1 + p`.
    exact order_p_unit_mem_standard_zpowers (p := p) uφ huφ_pow huφ_ne
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huφ_mem
  let g : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  let s : (ZMod (p ^ 2))ˣ := standard_nonabelian_zmodP2_unit (p := p)
  have hg_zpowers : ∀ x : Multiplicative (ZMod p), x ∈ Subgroup.zpowers g := by
    -- The quotient factor has prime cardinality `p`, so any nontrivial element generates it.
    have htop : Subgroup.zpowers g = ⊤ := by
      apply zpowers_eq_top_of_prime_card (p := p)
      · simpa using (ZMod.card p)
      · intro hg_one
        have : (1 : ZMod p) = 0 := (ofAdd_eq_one).mp hg_one
        exact zero_ne_one this.symm
    intro x
    simpa [g, htop]
  have hg_pow : g ^ p = 1 := by
    -- The additive generator of `Z / p Z` has exact exponent `p`.
    dsimp [g]
    rw [ofAdd_one_pow_mod_p (p := p) p, ZMod.natCast_self]
    rfl
  have hg_ne : g ≠ 1 := by
    -- The class of `1` modulo `p` is still nonzero.
    intro hg_one
    have : (1 : ZMod p) = 0 := (ofAdd_eq_one).mp hg_one
    exact zero_ne_one this.symm
  have hg_order : orderOf g = p := by
    -- Prime-order criterion on the additive generator.
    exact orderOf_eq_prime hg_pow hg_ne
  have hs_on_generator :
      standard_nonabelian_zmodP2_units_hom (p := p) g = s := by
    -- Unfold the additive lift once: the generator `1` is sent to Serre's standard unit `1 + p`.
    dsimp [g, s, standard_nonabelian_zmodP2_units_hom]
    simpa using
      congrArg Additive.toMul
        (ZMod.lift_coe
          (n := p)
          (f := ⟨zmultiplesHom (Additive ((ZMod (p ^ 2))ˣ))
            (Additive.ofMul (standard_nonabelian_zmodP2_unit (p := p))),
            standard_nonabelian_zmodP2_unit_zmultiples_zero (p := p)⟩)
          (1 : ℤ))
  have hgk_image :
      standard_nonabelian_zmodP2_units_hom (p := p) (g ^ k) = uφ := by
    -- The standard model sends `g ^ k` to the prescribed order-`p` unit `uφ`.
    calc
      standard_nonabelian_zmodP2_units_hom (p := p) (g ^ k)
          = (standard_nonabelian_zmodP2_units_hom (p := p) g) ^ k := by
              rw [map_zpow]
      _ = s ^ k := by rw [hs_on_generator]
      _ = uφ := hk
  have hgk_ne : g ^ k ≠ 1 := by
    -- Otherwise its image under the standard unit-valued hom would be trivial, contradicting `uφ ≠ 1`.
    intro hgk_one
    apply huφ_ne
    rw [← hgk_image, hgk_one]
    simp
  have hgk_zpowers : ∀ x : Multiplicative (ZMod p), x ∈ Subgroup.zpowers (g ^ k) := by
    -- A nontrivial element in a group of prime cardinality is again a generator.
    have htop : Subgroup.zpowers (g ^ k) = ⊤ := by
      apply zpowers_eq_top_of_prime_card (p := p)
      · simpa using (ZMod.card p)
      · exact hgk_ne
    intro x
    simpa [htop]
  have hgk_order : orderOf (g ^ k) = p := by
    -- Since `g ^ k` lies in the cyclic group generated by `g`, its order divides `p`; nontriviality
    -- rules out the divisor `1`.
    have hdvd : orderOf (g ^ k) ∣ p := by
      have hdvd' : orderOf (g ^ k) ∣ orderOf g :=
        orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
      rwa [hg_order] at hdvd'
    rcases (Nat.dvd_prime (Fact.out)).1 hdvd with h_one | h_p
    · exfalso
      exact hgk_ne ((orderOf_eq_one_iff.mp h_one) : g ^ k = 1)
    · exact h_p
  let β : Multiplicative (ZMod p) ≃* Multiplicative (ZMod p) :=
    mulEquivOfOrderOfEq hg_zpowers hgk_zpowers (hg_order.trans hgk_order.symm)
  have hβ_generator : β g = g ^ k := by
    -- The cyclic-group equivalence is defined by sending the chosen generator to `g ^ k`.
    simpa [β] using
      (mulEquivOfOrderOfEq_apply_gen hg_zpowers hgk_zpowers (hg_order.trans hgk_order.symm))
  have h_units :
      (standard_nonabelian_zmodP2_units_hom (p := p)).comp β.toMonoidHom = toUnits.comp φ := by
    -- Both unit-valued homomorphisms are determined by the generator `g`.
    exact
      (MonoidHom.eq_iff_eq_on_generator hg_zpowers _ _).2 <|
        calc
          ((standard_nonabelian_zmodP2_units_hom (p := p)).comp β.toMonoidHom) g
              = standard_nonabelian_zmodP2_units_hom (p := p) (β g) := rfl
          _ = standard_nonabelian_zmodP2_units_hom (p := p) (g ^ k) := by rw [hβ_generator]
          _ = uφ := hgk_image
          _ = toUnits (φ g) := by rfl
          _ = (toUnits.comp φ) g := rfl
  have h_action :
      ((standard_nonabelian_zmodP2_action (p := p)).comp β.toMonoidHom) = φ := by
    -- Apply the injective automorphism-to-unit conversion pointwise.
    refine MonoidHom.ext ?_
    intro x
    apply htoUnits_inj
    have hx := congrArg (fun f : Multiplicative (ZMod p) →* (ZMod (p ^ 2))ˣ => f x) h_units
    calc
      toUnits (((standard_nonabelian_zmodP2_action (p := p)).comp β.toMonoidHom) x)
          = (standard_nonabelian_zmodP2_units_hom (p := p)) (β x) := by
              ext
              change ((standard_nonabelian_zmodP2_units_hom (p := p)) (β x) : ZMod (p ^ 2)) •
                  (1 : ZMod (p ^ 2)) =
                ↑((standard_nonabelian_zmodP2_units_hom (p := p)) (β x))
              simp
      _ = toUnits (φ x) := hx
  refine ⟨SemidirectProduct.congr (MulEquiv.refl _) β ?_⟩
  intro x
  -- The semidirect-product compatibility is exactly the action equality established above.
  have hx := congrArg
    (fun f : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))) => f x) h_action
  simpa using hx.symm

end

end Exercise137

end

end Exercise_13_13_1_17

end Chap13

end Serre
