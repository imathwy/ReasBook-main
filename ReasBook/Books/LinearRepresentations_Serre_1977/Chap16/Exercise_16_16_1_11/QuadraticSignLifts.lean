import Serre.Chap16.Exercise_16_16_1_11.RationalSignCharacters

noncomputable section

open CategoryTheory
open Representation
open scoped Representation SubgroupInduction

namespace Exercise_16_16_1_11

section

variable {G : Type} [Group G]

variable {A : Type} [CommRing A] [IsLocalRing A] [Algebra A ℚ] [IsFractionRing A ℚ]

local notation "k" => IsLocalRing.ResidueField A

variable [CharP (IsLocalRing.ResidueField A) 5]
variable [Finite G] [IsCyclic G] (hG : Nat.card G = 4)

local instance quadraticSignLiftsFintype : Fintype G := Fintype.ofFinite G
local instance quadraticSignLiftsCommGroup : CommGroup G := IsCyclic.commGroup
local instance quadraticSignLiftsIsDomain : IsDomain A := (IsFractionRing.injective A ℚ).isDomain
attribute [local instance] Classical.decEq Classical.propDecidable

local notation "d₂" => cyclicOrderFourDivisorIndexTwo hG
local prefix:max "G_ " => cyclicSubgroupOfIndex

/-- Helper for Exercise 16-16.1-11: the fraction-field map on units is injective. -/
theorem units_map_to_rational_injective :
    Function.Injective (Units.map (algebraMap A ℚ).toMonoidHom) := by
  intro u v huv
  apply Units.ext
  exact
    IsFractionRing.injective A ℚ <|
      by simpa using congrArg (fun x : ℚˣ ↦ (x : ℚ)) huv

/-- Helper for Exercise 16-16.1-11: the sign-valued `Aˣ`-character on `ZMod 2` is
multiplicative. -/
theorem zmod2_sign_units_mul
    (a b : ZMod 2) :
    (-1 : Aˣ) ^ (a + b).val =
      (-1 : Aˣ) ^ a.val * (-1 : Aˣ) ^ b.val := by
  fin_cases a
  · fin_cases b
    · change (-1 : Aˣ) ^ 0 = (-1 : Aˣ) ^ 0 * (-1 : Aˣ) ^ 0
      norm_num
    · change (-1 : Aˣ) ^ 1 = (-1 : Aˣ) ^ 0 * (-1 : Aˣ) ^ 1
      norm_num
  · fin_cases b
    · change (-1 : Aˣ) ^ 1 = (-1 : Aˣ) ^ 1 * (-1 : Aˣ) ^ 0
      norm_num
    · change (-1 : Aˣ) ^ 0 = (-1 : Aˣ) ^ 1 * (-1 : Aˣ) ^ 1
      norm_num

/-- Helper for Exercise 16-16.1-11: the unit-valued sign character on
`Multiplicative (ZMod 2)` over `A`. -/
theorem zmod2_sign_units_map_one :
    ((fun z : Multiplicative (ZMod 2) ↦ (-1 : Aˣ) ^ (Multiplicative.toAdd z).val) 1) = 1 := by
  simp

/-- Helper for Exercise 16-16.1-11: the unit-valued sign character on
`Multiplicative (ZMod 2)` respects multiplication. -/
theorem zmod2_sign_units_map_mul
    (a b : Multiplicative (ZMod 2)) :
    (fun z : Multiplicative (ZMod 2) ↦ (-1 : Aˣ) ^ (Multiplicative.toAdd z).val) (a * b) =
      (fun z : Multiplicative (ZMod 2) ↦ (-1 : Aˣ) ^ (Multiplicative.toAdd z).val) a *
        (fun z : Multiplicative (ZMod 2) ↦ (-1 : Aˣ) ^ (Multiplicative.toAdd z).val) b := by
  simpa using zmod2_sign_units_mul (A := A) (Multiplicative.toAdd a) (Multiplicative.toAdd b)

/-- Helper for Exercise 16-16.1-11: the sign character on the cyclic group of order `2`, now
valued in `Aˣ`. -/
def zmod2SignUnits : Multiplicative (ZMod 2) →* Aˣ :=
  { toFun := fun z ↦ (-1 : Aˣ) ^ (Multiplicative.toAdd z).val
    map_one' := zmod2_sign_units_map_one (A := A)
    map_mul' := zmod2_sign_units_map_mul (A := A) }

/-- Helper for Exercise 16-16.1-11: the parity sign character on `Multiplicative (ZMod 4)`,
valued in `Aˣ`. -/
def zmod4SignUnits : Multiplicative (ZMod 4) →* Aˣ :=
  zmod2SignUnits.comp zmod4Parity

/-- Helper for Exercise 16-16.1-11: the explicit quadratic sign character lifts from `ℚˣ` to an
`Aˣ`-valued character with the same values `±1`. -/
def quadraticSignUnitCharacter : G →* Aˣ :=
  let g0 : G := Classical.choose (IsCyclic.exists_generator (α := G))
  let hg0_gen : ∀ x : G, x ∈ Subgroup.zpowers g0 :=
    Classical.choose_spec (IsCyclic.exists_generator (α := G))
  let eG : Multiplicative (ZMod 4) ≃* G := zmodMulEquivOfGenerator hg0_gen hG
  zmod4SignUnits.comp eG.symm.toMonoidHom

/-- Helper for Exercise 16-16.1-11: after mapping to `ℚˣ`, the lifted quadratic sign character is
exactly the explicit rational sign character. -/
theorem quadraticSignUnitCharacter_map_to_rational :
    ((Units.map (algebraMap A ℚ).toMonoidHom).comp
      (quadraticSignUnitCharacter (A := A) (G := G) hG)) =
      quadraticSignCharacter (G := G) hG := by
  ext g
  simp [quadraticSignUnitCharacter, quadraticSignCharacter, zmod4SignUnits, zmod2SignUnits,
    zmod4Sign, zmod2Sign]

/-- Helper for Exercise 16-16.1-11: the lifted quadratic sign character already takes the values
`±1` in `A`. -/
theorem quadraticSignUnitCharacter_apply
    (g : G) :
    (quadraticSignUnitCharacter (A := A) (G := G) hG g : A) =
      if g ∈ G_ d₂ then 1 else -1 := by
  have hmap :=
    congrArg
      (fun φ : G →* ℚˣ ↦ φ g)
      (quadraticSignUnitCharacter_map_to_rational (A := A) (G := G) (hG := hG))
  by_cases hg : g ∈ G_ d₂
  · have hq_unit : quadraticSignCharacter (G := G) hG g = 1 := by
      apply Units.ext
      simpa [quadraticSignCharacter_apply, hg] using
        quadraticSignCharacter_apply (G := G) (hG := hG) g
    have hA_unit : quadraticSignUnitCharacter (A := A) (G := G) hG g = 1 := by
      apply units_map_to_rational_injective (A := A)
      simpa [hq_unit] using hmap
    simpa [hg] using congrArg (fun u : Aˣ ↦ (u : A)) hA_unit
  · have hq_unit : quadraticSignCharacter (G := G) hG g = (-1 : ℚˣ) := by
      apply Units.ext
      simpa [quadraticSignCharacter_apply, hg] using
        quadraticSignCharacter_apply (G := G) (hG := hG) g
    have hA_unit :
        quadraticSignUnitCharacter (A := A) (G := G) hG g = (-1 : Aˣ) := by
      apply units_map_to_rational_injective (A := A)
      calc
        (Units.map (algebraMap A ℚ).toMonoidHom)
            (quadraticSignUnitCharacter (A := A) (G := G) hG g)
          = quadraticSignCharacter (G := G) hG g := by
              simpa using hmap
        _ = (-1 : ℚˣ) := hq_unit
        _ = (Units.map (algebraMap A ℚ).toMonoidHom) (-1 : Aˣ) := by
              ext
              simp
    simpa [hg] using congrArg (fun u : Aˣ ↦ (u : A)) hA_unit

/-- Helper for Exercise 16-16.1-11: reducing the lifted quadratic sign character modulo the
maximal ideal gives the expected characteristic-`5` values `±1`. -/
theorem quadraticSignUnitCharacter_residue_apply
    (g : G) :
    ((((Units.map (algebraMap A k).toMonoidHom).comp
      (quadraticSignUnitCharacter (A := A) (G := G) hG)) g : kˣ) : k) =
      if g ∈ G_ d₂ then 1 else -1 := by
  by_cases hg : g ∈ G_ d₂
  · have happly :
      (quadraticSignUnitCharacter (A := A) (G := G) hG g : A) = 1 := by
        simpa [hg] using quadraticSignUnitCharacter_apply (A := A) (G := G) (hG := hG) g
    simp [hg, happly]
  · have happly :
      (quadraticSignUnitCharacter (A := A) (G := G) hG g : A) = -1 := by
        simpa [hg] using quadraticSignUnitCharacter_apply (A := A) (G := G) (hG := hG) g
    simp [hg, happly]

end

end Exercise_16_16_1_11
