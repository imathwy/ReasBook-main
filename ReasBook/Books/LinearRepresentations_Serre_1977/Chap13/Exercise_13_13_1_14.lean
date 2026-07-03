import Mathlib
import Serre.Chap07.Proposition_7_7_2_1
import Serre.Chap12.CharacterRingOverFieldScalarExtension
import Serre.Chap12.Proposition_12_12_1_1
import Serre.Chap13.Exercise_13_13_1_14.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Representation
open scoped Quaternion

namespace Representation

section

local notation "Q8" => QuaternionGroup 2
local notation "C3" => Multiplicative (ZMod 3)
local notation "G0" => Q8 × C3
local notation "ρ" => quaternionCyclicWitnessRepresentation

local instance : Fintype Q8 := inferInstance
local instance : Fintype C3 := inferInstance
local instance : DecidableEq Q8 := inferInstance
local instance : DecidableEq C3 := inferInstance
local instance : Finite G0 := inferInstance
local instance : Fintype G0 := inferInstance
local instance : DecidableEq G0 := inferInstance
local instance : DecidableEq ℍ[ℚ] := by
  intro a b
  by_cases hre : a.re = b.re
  · by_cases himI : a.imI = b.imI
    · by_cases himJ : a.imJ = b.imJ
      · by_cases himK : a.imK = b.imK
        · exact isTrue (by ext <;> assumption)
        · exact isFalse (by
            intro h
            exact himK (congrArg QuaternionAlgebra.imK h))
      · exact isFalse (by
          intro h
          exact himJ (congrArg QuaternionAlgebra.imJ h))
    · exact isFalse (by
        intro h
        exact himI (congrArg QuaternionAlgebra.imI h))
  · exact isFalse (by
      intro h
      exact hre (congrArg QuaternionAlgebra.re h))
local instance : DecidableEq (Units ℍ[ℚ]) := fun a b =>
  if h : (a : ℍ[ℚ]) = (b : ℍ[ℚ]) then
    isTrue (Units.ext h)
  else
    isFalse fun hab ↦ h (congrArg Units.val hab)
local instance : Finite (ULift.{u} G0) := inferInstance
local instance (H : Subgroup G0) : Fintype H := Fintype.ofFinite H
local instance (H : Subgroup (ULift.{u} G0)) : Fintype H := Fintype.ofFinite H
local instance (H : Subgroup G0) : DecidablePred fun x : G0 ↦ x ∈ H := Classical.decPred _
local instance : DecidableEq (Subgroup G0) := Classical.decEq _

-- Proof sketch: the images of `a 1` and `xa 0` are the distinct units `i` and `j`, and the eight
-- resulting unit products are pairwise distinct in `ℍ[ℚ]`.
/-- Exercise 13-13.1-14: the map `quaternionGroupTwoToQuaternionUnits` realizes `QuaternionGroup
2` as a subgroup of `ℍ[ℚ]ˣ`. -/
theorem quaternionGroupTwoToQuaternionUnits_injective :
    Function.Injective quaternionGroupTwoToQuaternionUnits := by
  -- The explicit `Q8` table is finite, so Lean can check the eight quaternion-unit values are
  -- pairwise distinct directly.
  native_decide

-- Proof sketch: the generator is sent to a unit of order `3`, so the resulting monoid hom from
-- the cyclic group of order `3` is injective.
/-- Exercise 13-13.1-14: the map `cyclicOrderThreeToQuaternionUnits` realizes the cyclic group of
order `3` as a subgroup of `ℍ[ℚ]ˣ`. -/
theorem cyclicOrderThreeToQuaternionUnits_injective :
    Function.Injective cyclicOrderThreeToQuaternionUnits := by
  -- The cyclic factor has only three elements, so injectivity reduces to a finite computation.
  native_decide

-- Proof sketch: identify `ℍ[ℚ]` as a simple bimodule for the commuting left action of the cubic
-- root of unity field and the right action of `Q₈`, then use the double-centralizer description of
-- the constructed action.
/-- Exercise 13-13.1-14: the witness representation `ρ` is irreducible over `ℚ`. -/
theorem quaternionCyclicWitnessRepresentation_isIrreducible :
    (ρ).IsIrreducible := by
  exact quaternion_cyclic_witness_isIrreducible

/-- Helper for Exercise 13-13.1-14: the witness irreducibility theorem promoted to an instance. -/
instance : (ρ).IsIrreducible :=
  quaternionCyclicWitnessRepresentation_isIrreducible

-- Proof sketch: both factors embed faithfully into `ℍ[ℚ]ˣ`, and commuting left and right
-- multiplication determine the pair of group elements uniquely.
/-- Exercise 13-13.1-14: the witness representation `ρ` is faithful. -/
theorem quaternionCyclicWitnessRepresentation_faithful :
    Function.Injective ρ := by
  -- Evaluating at `1` turns a kernel computation into an explicit equality in `ℍ[ℚ]`, where the
  -- `24` possibilities can be checked directly.
  intro g h hgh
  have hker : quaternionCyclicWitnessRepresentation (g * h⁻¹) = 1 := by
    calc
      quaternionCyclicWitnessRepresentation (g * h⁻¹)
          = quaternionCyclicWitnessRepresentation g *
              quaternionCyclicWitnessRepresentation h⁻¹ := by
              simp [map_mul]
      _ = quaternionCyclicWitnessRepresentation h *
            quaternionCyclicWitnessRepresentation h⁻¹ := by
            rw [hgh]
      _ = 1 := by
            simpa using (quaternionCyclicWitnessRepresentation.map_mul h h⁻¹).symm
  have hkernel_eval :
      quaternionCyclicWitnessRepresentation (g * h⁻¹) (1 : ℍ[ℚ]) = 1 := by
    simpa using LinearMap.congr_fun hker (1 : ℍ[ℚ])
  have hkernel :
      g * h⁻¹ = 1 := by
    let hdetect :
        ∀ x : G0, quaternionCyclicWitnessRepresentation x (1 : ℍ[ℚ]) = 1 → x = 1 := by
      native_decide
    exact hdetect (g * h⁻¹) hkernel_eval
  have hmul := congrArg (fun x : G0 ↦ x * h) hkernel
  simpa [mul_assoc] using hmul

-- Proof sketch: `Q8 × C3` is Hamiltonian; equivalently, every subgroup is normal.
/-- Exercise 13-13.1-14: every subgroup of `Q8 × C3` is normal. -/
theorem quaternionCyclicWitnessGroup_allSubgroups_normal
    (H : Subgroup G0) :
    H.Normal := by
  -- Split each subgroup element into its `Q8` and `C3` coordinates; the second factor is central,
  -- and conjugation in `Q8` preserves each cyclic order-`4` subgroup up to inversion.
  refine ⟨?_⟩
  rintro ⟨q, c⟩ hn ⟨a, b⟩
  have hsnd : (1, c) ∈ H := by
    have hpow : ((q, c) : G0) ^ 4 = (1, c) := by
      simpa using quaternion_cyclic_pow_four (n := (q, c))
    exact hpow ▸ H.pow_mem hn 4
  have hfst : (q, 1) ∈ H := by
    have hmul : (q, c) * (1, c)⁻¹ = (q, 1) := by
      ext <;> simp
    exact hmul ▸ H.mul_mem hn (H.inv_mem hsnd)
  have hconj_fst : (a * q * a⁻¹, 1) ∈ H := by
    -- In `Q8`, conjugation fixes each cyclic order-`4` subgroup setwise, so the conjugate of
    -- `(q, 1)` is either itself or its inverse.
    cases q with
    | a i =>
        cases a with
        | a j =>
            fin_cases i <;> fin_cases j <;>
              first | simpa using hfst | simpa using H.inv_mem hfst
        | xa j =>
            fin_cases i <;> fin_cases j <;>
              first | simpa using hfst | simpa using H.inv_mem hfst
    | xa i =>
        cases a with
        | a j =>
            fin_cases i <;> fin_cases j <;>
              first | simpa using hfst | simpa using H.inv_mem hfst
        | xa j =>
            fin_cases i <;> fin_cases j <;>
              first | simpa using hfst | simpa using H.inv_mem hfst
  have hmul : (a * q * a⁻¹, 1) * (1, c) = (a, b) * (q, c) * (a, b)⁻¹ := by
    ext <;> simp [mul_assoc]
  exact hmul ▸ H.mul_mem hconj_fst hsnd


-- Proof sketch: the simple algebra attached to this rational irreducible representation is the
-- range of the canonical action homomorphism `ℚ[Q8 × C3] →ₐ[ℚ] Endℚ(ℍ[ℚ])`; compute its center as
-- the cubic-root-of-unity field and its degree over that center as `2`.
/-- Helper for Exercise 13-13.1-14: the cubic coefficient field is exactly the cyclotomic field
generated by a primitive cube root of unity. -/
theorem quaternion_cubic_subfield_algEquiv_cyclotomicField3_exists :
    Nonempty (↥quaternion_cubic_subfield ≃ₐ[ℚ] CyclotomicField 3 ℚ) := by
  let ω : quaternion_cubic_subfield :=
    ⟨quaternionCubeRootOfUnity, quaternion_cube_root_mem_cubic_subfield⟩
  have hω3 : quaternionCubeRootOfUnity ^ 3 = (1 : ℍ[ℚ]) := by
    -- Compute the third power through the explicit square `ω²`.
    rw [pow_succ, pow_two, ← quaternion_cube_root_squared_eq]
    ext <;> norm_num [quaternionCubeRootOfUnity, quaternion_cube_root_squared]
  have hω2ne : ω ^ 2 ≠ (1 : quaternion_cubic_subfield) := by
    -- The square still has nonzero `i`-coordinate, so it cannot be `1`.
    intro h
    have h' : quaternionCubeRootOfUnity * quaternionCubeRootOfUnity = (1 : ℍ[ℚ]) := by
      simpa [pow_two, ω] using congrArg Subtype.val h
    rw [← quaternion_cube_root_squared_eq] at h'
    have hi := congrArg QuaternionAlgebra.imI h'
    norm_num [ω, quaternionCubeRootOfUnity, quaternion_cube_root_squared] at hi
  have hω1ne : ω ≠ (1 : quaternion_cubic_subfield) := by
    -- The generator itself has nonzero `i`-coordinate, so it is not the unit element.
    intro h
    have h' := congrArg Subtype.val h
    have hi := congrArg QuaternionAlgebra.imI h'
    norm_num [ω, quaternionCubeRootOfUnity] at hi
  have hω : IsPrimitiveRoot ω 3 := by
    -- The explicit quaternion `ω` has order exactly `3`, so it gives the primitive generator
    -- required by the cyclotomic-field characterization.
    rw [IsPrimitiveRoot.iff (by decide : 0 < 3)]
    constructor
    · exact Subtype.ext hω3
    · intro l hl hk hpow
      interval_cases l
      · exact hω1ne (by simpa using hpow)
      · exact hω2ne (by simpa using hpow)
  have htop : IntermediateField.adjoin ℚ {ω} = ⊤ := by
    -- Every cubic-subfield element is an affine-linear combination of `1` and `ω`, so the simple
    -- adjoin already contains the whole field.
    rw [eq_top_iff]
    intro x _
    have hcoords : (x : ℍ[ℚ]).imI = (x : ℍ[ℚ]).imJ ∧ (x : ℍ[ℚ]).imJ = (x : ℍ[ℚ]).imK :=
      (commutes_with_quaternion_cube_root_iff_equal_im_coordinates (q := (x : ℍ[ℚ]))).1
        x.property
    have hxpair :
        (x : ℍ[ℚ]) =
          quaternion_cubic_pair_to_quaternion ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI) :=
      quaternion_eq_cubic_pair_of_equal_im_coordinates (q := (x : ℍ[ℚ])) hcoords.1 hcoords.2
    let q : quaternion_cubic_subfield :=
      (((x : ℍ[ℚ]).re + (x : ℍ[ℚ]).imI : ℚ) • (1 : quaternion_cubic_subfield) +
        (2 * (x : ℍ[ℚ]).imI : ℚ) • ω)
    have hqval :
        (q : ℍ[ℚ]) =
          quaternion_cubic_pair_to_quaternion ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI) := by
      change
        ((x : ℍ[ℚ]).re + (x : ℍ[ℚ]).imI : ℚ) • (1 : ℍ[ℚ]) +
            (2 * (x : ℍ[ℚ]).imI : ℚ) • quaternionCubeRootOfUnity =
          quaternion_cubic_pair_to_quaternion ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI)
      symm
      exact quaternion_cubic_pair_eq_smul_one_add_smul_cube_root
        ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI)
    have hxexpr : x = q := by
      apply Subtype.ext
      exact hxpair.trans hqval.symm
    rw [hxexpr]
    refine IntermediateField.add_mem _ ?_ ?_
    · simpa using IntermediateField.algebraMap_mem (IntermediateField.adjoin ℚ {ω})
        ((x : ℍ[ℚ]).re + (x : ℍ[ℚ]).imI)
    · exact IntermediateField.smul_mem _
        (IntermediateField.mem_adjoin_simple_self ℚ ω)
  have hcycloTop :
      IsCyclotomicExtension {3} ℚ
        ↥(⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      3 ℚ ↥quaternion_cubic_subfield
      (⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) hω).2 htop.symm
  letI :
      IsCyclotomicExtension {3} ℚ
        ↥(⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) :=
    hcycloTop
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  refine
    ⟨(IntermediateField.topEquiv :
        (⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) ≃ₐ[ℚ]
          ↥quaternion_cubic_subfield).symm.trans ?_⟩
  exact
    IsCyclotomicExtension.algEquiv
      {3} ℚ ↥(⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) (CyclotomicField 3 ℚ)

/-- Helper for Exercise 13-13.1-14: a chosen algebra equivalence from the cubic coefficient field
to the cubic cyclotomic field. -/
noncomputable def quaternion_cubic_subfield_algEquiv_cyclotomicField3 :
    ↥quaternion_cubic_subfield ≃ₐ[ℚ] CyclotomicField 3 ℚ :=
  Classical.choice quaternion_cubic_subfield_algEquiv_cyclotomicField3_exists

/-- Exercise 13-13.1-14: the simple `ℚ`-algebra attached to `ρ`, realized as the range of its
canonical group-algebra action on `ℍ[ℚ]`, is isomorphic to `M₂(CyclotomicField 3 ℚ)`. -/
theorem quaternionCyclicWitnessRepresentation_imageSubalgebra_equiv_matrix_over_cyclotomicField3 :
    Nonempty
      ((ρ).asAlgebraHom.range ≃ₐ[ℚ]
        Matrix (Fin 2) (Fin 2) (CyclotomicField 3 ℚ)) := by
  -- Route correction: use Serre's exact chain `A ≃ End_K(H_Q) ≃ M₂(K)`, with the middle arrow
  -- cached above so the final composition is just coefficient transport to `CyclotomicField 3`.
  let e1 :
      quaternion_cyclic_imageSubalgebra ≃ₐ[ℚ]
        Matrix (Fin 2) (Fin 2) ↥quaternion_cubic_subfield :=
    quaternion_cyclic_imageSubalgebra_algEquiv_matrix_over_cubic_subfield
  let e2 :
      Matrix (Fin 2) (Fin 2) ↥quaternion_cubic_subfield ≃ₐ[ℚ]
        Matrix (Fin 2) (Fin 2) (CyclotomicField 3 ℚ) :=
    AlgEquiv.mapMatrix quaternion_cubic_subfield_algEquiv_cyclotomicField3
  exact ⟨e1.trans e2⟩

-- Proof sketch: the Artin-Wedderburn component `M₂(K)` has matrix size `2`, with
-- `K = CyclotomicField 3 ℚ`. Equivalently, the raw regular intertwining multiplicity divided by
-- `dimℚ End_G(ρ)` is `2`.
/-- Exercise 13-13.1-14: the Artin-Wedderburn matrix-size parameter attached to `ρ` is `2`. -/
theorem quaternionCyclicWitnessRepresentation_matrixSize_two :
    Module.finrank ℚ
        ((leftRegular ℚ G0).IntertwiningMap (ρ)) /
      Module.finrank ℚ
        ((ρ).IntertwiningMap (ρ)) =
      2 := by
  -- Route correction: compute the numerator and denominator separately. The numerator is the
  -- regular multiplicity `dimℚ ℍ[ℚ] = 4`, and the denominator is the explicit cubic-plane
  -- self-intertwiner dimension `2`.
  have hnum :
      Module.finrank ℚ ((leftRegular ℚ G0).IntertwiningMap ρ) = 4 := by
    calc
      Module.finrank ℚ ((leftRegular ℚ G0).IntertwiningMap ρ)
          = Module.finrank ℚ ℍ[ℚ] := by
              simpa using (Representation.leftRegularMapEquiv ρ).finrank_eq
      _ = 4 := rational_quaternion_finrank_eq_four
  have hden :
      Module.finrank ℚ ((ρ).IntertwiningMap (ρ)) = 2 :=
    quaternion_cyclic_self_intertwining_finrank_eq_two
  rw [hnum, hden]

-- Proof sketch: the explicit witness character satisfies Serre's four central-value test, and the
-- obstruction theorem above excludes every element of the subgroup-permutation span.
/-- Exercise 13-13.1-14: the irreducible rational character of
`quaternionCyclicWitnessRepresentation` is not an integral linear combination of the subgroup
permutation characters `ℓ_H^G`. -/
theorem
    quaternionCyclicWitnessRepresentation_character_not_mem_subgroupPermutationCharacterSpanOverQ
    :
    χ_ ρ ∉ subgroupPermutationCharacterSpanOverQ G0 := by
  -- Route correction: the broken upstream import chain is replaced here by a local four-point
  -- obstruction theorem tailored to the central values of Serre's quaternionic witness.
  refine quaternion_cyclic_obstruction_of_central_values ?_ ?_ ?_ ?_
  · -- The character value at the identity is the dimension `4`.
    change LinearMap.trace ℚ ℍ[ℚ] (ρ ((1 : Q8), (1 : C3))) = 4
    rw [quaternion_witness_apply_identity]
    change
      LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
        (LinearMap.mulLeft ℚ (1 : ℍ[ℚ])) = 4
    have h := rational_quaternion_left_mul_trace_eq_four_mul_re (1 : ℍ[ℚ])
    norm_num at h ⊢
    exact h
  · -- The central involution acts with trace `-4`.
    change
      LinearMap.trace ℚ ℍ[ℚ]
        (quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_two) = -4
    rw [quaternionCyclicWitnessRepresentation_apply_central_order_two]
    change
      LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
        (LinearMap.mulLeft ℚ (-1 : ℍ[ℚ])) = -4
    have h := rational_quaternion_left_mul_trace_eq_four_mul_re (-1 : ℍ[ℚ])
    norm_num at h ⊢
    exact h
  · -- The central order-`3` element acts with trace `-2`.
    change
      LinearMap.trace ℚ ℍ[ℚ]
        (quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_three) = -2
    rw [quaternionCyclicWitnessRepresentation_apply_central_order_three]
    exact trace_mulLeft_quaternion_cube_root_of_unity_eq_neg_two
  · -- The central order-`6` element acts with trace `2`.
    change
      LinearMap.trace ℚ ℍ[ℚ]
        (quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_six) = 2
    rw [quaternionCyclicWitnessRepresentation_apply_central_order_six]
    change
      LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
        (LinearMap.mulLeft ℚ (-quaternionCubeRootOfUnity)) = 2
    have h := rational_quaternion_left_mul_trace_eq_four_mul_re (-quaternionCubeRootOfUnity)
    norm_num [quaternionCubeRootOfUnity] at h ⊢
    exact h

end

end Representation
