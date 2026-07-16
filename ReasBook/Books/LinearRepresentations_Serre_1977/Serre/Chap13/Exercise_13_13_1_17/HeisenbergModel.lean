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

/-- Helper for Exercise 13-13.1-17: every Sylow `p`-subgroup of `GL₃(𝔽_p)` is isomorphic to the
canonical upper-unitriangular model. -/
theorem sylowGL3_mulEquiv_upperUnitriangularSubgroup
    (P : Sylow p (GL (Fin 3) (ZMod p))) :
    Nonempty (P ≃* upperUnitriangularSubgroup (ZMod p) 3) := by
  -- Use the chapter-8 canonical Sylow owner and Sylow conjugacy to freeze the source group.
  rcases upperUnitriangularSubgroup_isSylow (k := ZMod p) (n := 3) (p := p) with ⟨Q, hQ⟩
  exact ⟨(P.equiv Q).trans (MulEquiv.subgroupCongr hQ)⟩

/-- Helper for Exercise 13-13.1-17: the canonical upper-unitriangular model has order `p^3`. -/
theorem upperUnitriangularSubgroup_card_p_cubed :
    Nat.card (upperUnitriangularSubgroup (ZMod p) 3) = p ^ 3 := by
  rcases upperUnitriangularSubgroup_isSylow (k := ZMod p) (n := 3) (p := p) with ⟨P, hP⟩
  rw [← hP, P.card_eq_multiplicity]
  have hcard :
      Nat.card (GL (Fin 3) (ZMod p)) = p ^ 3 * ((p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rw [Matrix.card_GL_field (n := 3) (𝔽 := ZMod p), Fin.prod_univ_three, ZMod.card]
    have hp_cube_sub_p :
        p ^ 3 - p = p * (p ^ 2 - 1) := by
      simp [pow_succ, Nat.mul_assoc, Nat.mul_sub_left_distrib]
    have hp_cube_sub_p_sq :
        p ^ 3 - p ^ 2 = p ^ 2 * (p - 1) := by
      simp [pow_succ, Nat.mul_assoc, Nat.mul_sub_left_distrib]
    -- The three `GL₃` factors are `(p^3 - 1)`, `p (p^2 - 1)`, and `p^2 (p - 1)`.
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, Nat.one_mod, pow_one,
      Nat.mod_succ]
    rw [hp_cube_sub_p, hp_cube_sub_p_sq]
    ring
  have hp : Nat.Prime p := Fact.out
  have hcoprime_p_minus_one : Nat.Coprime p (p - 1) := by
    refine hp.coprime_iff_not_dvd.2 ?_
    exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos (by decide))
  have hcoprime_p_sq_minus_one : Nat.Coprime p (p ^ 2 - 1) := by
    refine hp.coprime_iff_not_dvd.2 ?_
    intro hdiv
    have hp2 : p ∣ p ^ 2 := by
      simp [pow_two]
    have hp_dvd_one : p ∣ 1 := by
      have hsub : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub hp2 hdiv
      have hcalc : 1 + (p ^ 2 - 1) = p ^ 2 := by
        have hp2pos : 0 < p ^ 2 := by
          have hp0 : 0 < p := hp.pos
          positivity
        simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one, Nat.add_comm] using
          Nat.succ_pred_eq_of_pos hp2pos
      exact (Nat.eq_sub_of_add_eq hcalc).symm ▸ hsub
    exact hp.not_dvd_one hp_dvd_one
  have hcoprime_p_cube_minus_one : Nat.Coprime p (p ^ 3 - 1) := by
    refine hp.coprime_iff_not_dvd.2 ?_
    intro hdiv
    have hp3 : p ∣ p ^ 3 := by
      exact dvd_pow_self p (show 3 ≠ 0 by decide)
    have hp_dvd_one : p ∣ 1 := by
      have hsub : p ∣ p ^ 3 - (p ^ 3 - 1) := Nat.dvd_sub hp3 hdiv
      have hcalc : 1 + (p ^ 3 - 1) = p ^ 3 := by
        have hp3pos : 0 < p ^ 3 := by
          have hp0 : 0 < p := hp.pos
          positivity
        simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one, Nat.add_comm] using
          Nat.succ_pred_eq_of_pos hp3pos
      exact (Nat.eq_sub_of_add_eq hcalc).symm ▸ hsub
    exact hp.not_dvd_one hp_dvd_one
  have hcoprime : Nat.Coprime p ((p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)) := by
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right hcoprime_p_minus_one hcoprime_p_sq_minus_one)
      hcoprime_p_cube_minus_one
  have hm0 : ((p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)) ≠ 0 := by
    intro hmz
    have : Nat.Coprime p 0 := by
      simpa [hmz] using hcoprime
    exact hp.ne_one <| by simpa [Nat.coprime_zero_right] using this
  have hfactorization :
      (Nat.card (GL (Fin 3) (ZMod p))).factorization p = 3 := by
    rw [hcard]
    have hmul := Nat.factorization_mul (a := p ^ 3)
        (b := (p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)) (pow_ne_zero _ hp.ne_zero) hm0
    have hfactorization_m : (((p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)).factorization p) = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdiv
      exact (hp.coprime_iff_not_dvd.mp hcoprime) hdiv
    rw [hmul]
    simp [hp.factorization_pow, hfactorization_m]
  rw [hfactorization]

/-- Helper for Exercise 13-13.1-17: the upper-unitriangular group algebra has `ℚ`-dimension
`p^3`. -/
theorem upperUnitriangularSubgroup_groupAlgebra_finrank_p_cubed :
    Module.finrank ℚ ℚ[upperUnitriangularSubgroup (ZMod p) 3] = p ^ 3 := by
  -- Combine the general group-algebra dimension formula with the explicit order of the canonical
  -- Heisenberg model.
  rw [groupAlgebra_finrank_eq_natCard (k := ℚ) (G := upperUnitriangularSubgroup (ZMod p) 3),
    upperUnitriangularSubgroup_card_p_cubed (p := p)]

/-- Helper for Exercise 13-13.1-17: the canonical Heisenberg model has exponent `p`. -/
theorem upperUnitriangularSubgroup_pow_p_eq_one
    (hp2 : p ≠ 2) (x : upperUnitriangularSubgroup (ZMod p) 3) :
    x ^ p = 1 := by
  rcases upperUnitriangularSubgroup_isSylow (k := ZMod p) (n := 3) (p := p) with ⟨P, hP⟩
  let e : upperUnitriangularSubgroup (ZMod p) 3 ≃* P := MulEquiv.subgroupCongr hP.symm
  have hxP : (e x) ^ p = 1 := sylowGL3_pow_p_eq_one (p := p) hp2 P (e x)
  -- Transport the exponent-`p` relation back from the chosen Sylow owner.
  exact e.injective (by simpa using hxP)

/-- Helper for Exercise 13-13.1-17: on the Heisenberg model, every augmentation generator
`[g] - 1` has zero `p`-th power over `𝔽_p`. -/
theorem upperUnitriangularSubgroup_of_sub_one_pow_p_eq_zero
    (hp2 : p ≠ 2) (g : upperUnitriangularSubgroup (ZMod p) 3) :
    ((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
        (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ^ p = 0 := by
  -- Rewrite the `p`-th power in the group algebra, then use the exponent-`p` calculation.
  rw [monoidAlgebra_of_sub_one_pow_p (p := p) (G := upperUnitriangularSubgroup (ZMod p) 3) g,
    upperUnitriangularSubgroup_pow_p_eq_one (p := p) hp2 g]
  ext h
  by_cases hh : h = 1
  · subst hh
    simp [MonoidAlgebra.of, MonoidAlgebra.one_def]
  · simp [MonoidAlgebra.of, MonoidAlgebra.one_def, hh]

/-- Helper for Exercise 13-13.1-17: the canonical Heisenberg model carries the usual augmentation
map to `𝔽_p`. -/
def upperUnitriangularSubgroup_augmentation :
    (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3] →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3)
    (1 : upperUnitriangularSubgroup (ZMod p) 3 →* ZMod p)

/-- Helper for Exercise 13-13.1-17: the Heisenberg augmentation map is surjective. -/
theorem upperUnitriangularSubgroup_augmentation_surjective :
    Function.Surjective (upperUnitriangularSubgroup_augmentation (p := p)) := by
  intro z
  refine ⟨algebraMap (ZMod p) ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) z, ?_⟩
  -- The augmentation sends scalar coefficients to the same scalar in `𝔽_p`.
  simp [upperUnitriangularSubgroup_augmentation]

/-- Helper for Exercise 13-13.1-17: each Heisenberg augmentation generator `[g] - 1` lies in the
kernel of the augmentation map. -/
theorem upperUnitriangularSubgroup_of_sub_one_mem_augmentationKernel
    (g : upperUnitriangularSubgroup (ZMod p) 3) :
    ((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
        (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ∈
      RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom := by
  -- The augmentation sends both `[g]` and `1` to `1`, so their difference is killed.
  rw [RingHom.mem_ker]
  simp [upperUnitriangularSubgroup_augmentation]

/-- Helper for Exercise 13-13.1-17: the Heisenberg augmentation kernel is exactly the span of the
standard generators `[g] - 1`. -/
theorem upperUnitriangularSubgroup_augmentationKernel_eq_span_sub_one :
    RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom =
      Ideal.span
        (Set.range fun g : upperUnitriangularSubgroup (ZMod p) 3 =>
          (MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
              (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) := by
  -- The generic augmentation-kernel owner already identifies finite-group kernels with the span of
  -- the differences `[g] - 1`.
  simpa [upperUnitriangularSubgroup_augmentation] using
    (monoidAlgebra_augmentationKernel_eq_span_sub_one
      (p := p) (G := upperUnitriangularSubgroup (ZMod p) 3))

/-- Helper for Exercise 13-13.1-17: the `(1,2)` root subgroup on the canonical `UT₃(𝔽_p)`
model. -/
private def upperUnitriangularSubgroupU12 (a : ZMod p) :
    upperUnitriangularSubgroup (ZMod p) 3 := by
  refine ⟨Matrix.GeneralLinearGroup.mk'' !![1, a, 0; 0, 1, 0; 0, 0, 1] ?_, ?_⟩
  · refine ⟨1, ?_⟩
    simp [Matrix.det_fin_three]
  · rw [mem_upperUnitriangularSubgroup_iff]
    change (!![1, a, 0; 0, 1, 0; 0, 0, 1]).BlockTriangular id ∧
        (!![1, a, 0; 0, 1, 0; 0, 0, 1]).diag = 1
    constructor
    · intro i j hij
      -- The only potentially nonzero off-diagonal entry is the strict-upper `(0,1)` slot.
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · ext i
      -- The diagonal entries are visibly all `1`.
      fin_cases i <;> simp

/-- Helper for Exercise 13-13.1-17: the `(2,3)` root subgroup on the canonical `UT₃(𝔽_p)`
model. -/
private def upperUnitriangularSubgroupU23 (b : ZMod p) :
    upperUnitriangularSubgroup (ZMod p) 3 := by
  refine ⟨Matrix.GeneralLinearGroup.mk'' !![1, 0, 0; 0, 1, b; 0, 0, 1] ?_, ?_⟩
  · refine ⟨1, ?_⟩
    simp [Matrix.det_fin_three]
  · rw [mem_upperUnitriangularSubgroup_iff]
    change (!![1, 0, 0; 0, 1, b; 0, 0, 1]).BlockTriangular id ∧
        (!![1, 0, 0; 0, 1, b; 0, 0, 1]).diag = 1
    constructor
    · intro i j hij
      -- The only potentially nonzero off-diagonal entry is the strict-upper `(1,2)` slot.
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · ext i
      -- The diagonal entries are again all `1`.
      fin_cases i <;> simp

/-- Helper for Exercise 13-13.1-17: the central `(1,3)` root subgroup on the canonical
`UT₃(𝔽_p)` model. -/
private def upperUnitriangularSubgroupU13 (c : ZMod p) :
    upperUnitriangularSubgroup (ZMod p) 3 := by
  refine ⟨Matrix.GeneralLinearGroup.mk'' !![1, 0, c; 0, 1, 0; 0, 0, 1] ?_, ?_⟩
  · refine ⟨1, ?_⟩
    simp [Matrix.det_fin_three]
  · rw [mem_upperUnitriangularSubgroup_iff]
    change (!![1, 0, c; 0, 1, 0; 0, 0, 1]).BlockTriangular id ∧
        (!![1, 0, c; 0, 1, 0; 0, 0, 1]).diag = 1
    constructor
    · intro i j hij
      -- The only potentially nonzero off-diagonal entry is the strict-upper `(0,2)` slot.
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · ext i
      -- The diagonal entries are visibly fixed.
      fin_cases i <;> simp

/-- Helper for Exercise 13-13.1-17: the `(1,2)` root subgroup is additive in its parameter. -/
private theorem upperUnitriangularSubgroupU12_add (a b : ZMod p) :
    upperUnitriangularSubgroupU12 (p := p) (a + b) =
      upperUnitriangularSubgroupU12 (p := p) a * upperUnitriangularSubgroupU12 (p := p) b := by
  ext i j
  -- Compare the two explicit matrices entrywise.
  fin_cases i <;> fin_cases j <;> simp [upperUnitriangularSubgroupU12, Matrix.mul_apply,
    Fin.sum_univ_three, add_comm]

/-- Helper for Exercise 13-13.1-17: the `(2,3)` root subgroup is additive in its parameter. -/
private theorem upperUnitriangularSubgroupU23_add (a b : ZMod p) :
    upperUnitriangularSubgroupU23 (p := p) (a + b) =
      upperUnitriangularSubgroupU23 (p := p) a * upperUnitriangularSubgroupU23 (p := p) b := by
  ext i j
  -- Compare the two explicit matrices entrywise.
  fin_cases i <;> fin_cases j <;> simp [upperUnitriangularSubgroupU23, Matrix.mul_apply,
    Fin.sum_univ_three, add_comm]

/-- Helper for Exercise 13-13.1-17: every element of the canonical `UT₃(𝔽_p)` model factors into
the two simple root subgroups followed by the central root subgroup. -/
private theorem upperUnitriangularSubgroup_word_coordinates
    (g : upperUnitriangularSubgroup (ZMod p) 3) :
    g =
      upperUnitriangularSubgroupU12 (p := p) (((g : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1) *
      upperUnitriangularSubgroupU23 (p := p) (((g : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2) *
      upperUnitriangularSubgroupU13 (p := p)
        ((((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2) -
          (((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1) *
            (((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2)) := by
  ext i j
  have hmem :=
    (mem_upperUnitriangularSubgroup_iff (k := ZMod p) (n := 3)
      ((g : upperUnitriangularSubgroup (ZMod p) 3) : GL (Fin 3) (ZMod p))).1 g.property
  rcases hmem with ⟨htri, hdiag⟩
  -- Freeze the three visible coordinates of `g` and check the matrix identity entrywise.
  fin_cases i <;> fin_cases j
  · simpa [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three] using congrFun hdiag 0
  · simp [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three]
  · have h10 := htri (show (1 : Fin 3) > 0 by decide)
    simpa [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three] using h10
  · simpa [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three] using congrFun hdiag 1
  · simp [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three]
  · have h20 := htri (show (2 : Fin 3) > 0 by decide)
    simpa [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three] using h20
  · have h21 := htri (show (2 : Fin 3) > 1 by decide)
    simpa [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three] using h21
  · simpa [upperUnitriangularSubgroupU12, upperUnitriangularSubgroupU23,
      upperUnitriangularSubgroupU13, Matrix.mul_apply, Fin.sum_univ_three] using congrFun hdiag 2

/-- Helper for Exercise 13-13.1-17: commuting the two noncentral root subgroups produces the
central root subgroup. -/
private theorem upperUnitriangularSubgroup_u12_mul_u23
    (c : ZMod p) :
    upperUnitriangularSubgroupU12 (p := p) 1 * upperUnitriangularSubgroupU23 (p := p) c =
      upperUnitriangularSubgroupU23 (p := p) c * upperUnitriangularSubgroupU12 (p := p) 1 *
        upperUnitriangularSubgroupU13 (p := p) c := by
  ext i j
  -- This is the standard Heisenberg commutator relation checked on the explicit matrices.
  fin_cases i <;> fin_cases j <;> simp [upperUnitriangularSubgroupU12,
    upperUnitriangularSubgroupU23, upperUnitriangularSubgroupU13, Matrix.mul_apply,
    Fin.sum_univ_three]

/-- Helper for Exercise 13-13.1-17: this additive cancellation packages the right-hand
linearization step in the Heisenberg commutator calculation. -/
private theorem addSub_add_sub_eq_sub_add {R : Type*} [Ring R] (a b c d : R) :
    (a - (b + c)) + (b - d) = a - (d + c) := by
  -- This is a pure additive rearrangement, so `abel_nf` is the stable normalizer.
  abel_nf

/-- Helper for Exercise 13-13.1-17: subtracting two linearizations with the same leading term
leaves only the new degree-`1` contribution. -/
private theorem sub_sub_sub_eq {R : Type*} [Ring R] (a b d : R) :
    (a - b) - (a - (b + d)) = d := by
  -- Again, the proof is purely additive and should not trigger any group-algebra unfolding.
  abel_nf

/-- Helper for Exercise 13-13.1-17: the central root subgroup already lands in the square of the
augmentation kernel. -/
private theorem upperUnitriangularSubgroup_central_sub_one_mem_augmentationKernel_sq
    (c : ZMod p) :
    let I : Ideal (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3] :=
      RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom
    ((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3)
        (upperUnitriangularSubgroupU13 (p := p) c) :
          (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ∈ I ^ 2 := by
  let G := upperUnitriangularSubgroup (ZMod p) 3
  let A := (ZMod p)[G]
  let I : Ideal A := RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom
  let e12 : A :=
    (MonoidAlgebra.of (ZMod p) G (upperUnitriangularSubgroupU12 (p := p) 1) : A) - 1
  let e23 : A :=
    (MonoidAlgebra.of (ZMod p) G (upperUnitriangularSubgroupU23 (p := p) c) : A) - 1
  let e13 : A :=
    (MonoidAlgebra.of (ZMod p) G (upperUnitriangularSubgroupU13 (p := p) c) : A) - 1
  let leftRaw : A :=
    (MonoidAlgebra.of (ZMod p) G
        (upperUnitriangularSubgroupU12 (p := p) 1 *
          upperUnitriangularSubgroupU23 (p := p) c) : A) - 1
  let middleRaw : A :=
    (MonoidAlgebra.of (ZMod p) G
        (upperUnitriangularSubgroupU23 (p := p) c *
          upperUnitriangularSubgroupU12 (p := p) 1) : A) - 1
  let rightRaw : A :=
    (MonoidAlgebra.of (ZMod p) G
        ((upperUnitriangularSubgroupU23 (p := p) c *
            upperUnitriangularSubgroupU12 (p := p) 1) *
          upperUnitriangularSubgroupU13 (p := p) c) : A) - 1
  -- Work entirely in the fixed spelling `A` with the fixed augmentation ideal `I`.
  change e13 ∈ I ^ 2
  -- Linearize the left-hand side of the Heisenberg commutator relation modulo `I²`.
  have hleft :
      leftRaw - (e12 + e23) ∈ I ^ 2 := by
    simpa [A, I, G, leftRaw, e12, e23] using
      monoidAlgebra_of_mul_sub_one_sub_add_mem_augmentationKernel_sq
        (p := p) (G := G)
        (upperUnitriangularSubgroupU12 (p := p) 1)
        (upperUnitriangularSubgroupU23 (p := p) c)
  -- Linearize the two factors on the right-hand side separately before combining them.
  have hrightFirst :
      rightRaw - (middleRaw + e13) ∈ I ^ 2 := by
    simpa [A, I, G, rightRaw, middleRaw, e13, mul_assoc] using
      monoidAlgebra_of_mul_sub_one_sub_add_mem_augmentationKernel_sq
        (p := p) (G := G)
        (upperUnitriangularSubgroupU23 (p := p) c *
          upperUnitriangularSubgroupU12 (p := p) 1)
        (upperUnitriangularSubgroupU13 (p := p) c)
  have hrightSecond :
      middleRaw - (e23 + e12) ∈ I ^ 2 := by
    simpa [A, I, G, middleRaw, e23, e12] using
      monoidAlgebra_of_mul_sub_one_sub_add_mem_augmentationKernel_sq
        (p := p) (G := G)
        (upperUnitriangularSubgroupU23 (p := p) c)
        (upperUnitriangularSubgroupU12 (p := p) 1)
  have hright :
      rightRaw - ((e23 + e12) + e13) ∈ I ^ 2 := by
    -- Adding the two linearization errors eliminates the intermediate product term.
    have hsum :
        (rightRaw - (middleRaw + e13)) + (middleRaw - (e23 + e12)) ∈ I ^ 2 :=
      add_mem hrightFirst hrightSecond
    exact
      (addSub_add_sub_eq_sub_add
        (a := rightRaw) (b := middleRaw) (c := e13) (d := e23 + e12)) ▸ hsum
  have hcomm :
      upperUnitriangularSubgroupU12 (p := p) 1 * upperUnitriangularSubgroupU23 (p := p) c =
        (upperUnitriangularSubgroupU23 (p := p) c *
            upperUnitriangularSubgroupU12 (p := p) 1) *
          upperUnitriangularSubgroupU13 (p := p) c :=
    upperUnitriangularSubgroup_u12_mul_u23 (p := p) c
  have hright' :
      leftRaw - ((e23 + e12) + e13) ∈ I ^ 2 := by
    -- Rewrite the right-hand linearization back to the left-hand product via the group relation.
    simpa [A, G, leftRaw, rightRaw, hcomm] using hright
  have hright'' :
      leftRaw - ((e12 + e23) + e13) ∈ I ^ 2 := by
    -- Reorder the degree-`1` linear part once before the final subtraction step.
    have hswap : ((e23 + e12) + e13) = ((e12 + e23) + e13) := by
      rw [add_comm e23 e12]
    exact hswap ▸ hright'
  have hcentral :
      e13 ∈ I ^ 2 := by
    -- Subtract the two linearizations; the degree-`1` terms cancel and only the central class remains.
    have hdiff :
        (leftRaw - (e12 + e23)) - (leftRaw - ((e12 + e23) + e13)) ∈ I ^ 2 :=
      sub_mem hleft hright''
    exact (sub_sub_sub_eq (a := leftRaw) (b := e12 + e23) (d := e13)) ▸ hdiff
  exact hcentral

/-- Helper for Exercise 13-13.1-17: the Heisenberg augmentation kernel is maximal because the
quotient is the field `𝔽_p`. -/
theorem upperUnitriangularSubgroup_augmentationKernel_isMaximal :
    (RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom).IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective
    (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom
    (upperUnitriangularSubgroup_augmentation_surjective (p := p))

/-- Helper for Exercise 13-13.1-17: the ring Jacobson radical is always contained in the maximal
Heisenberg augmentation kernel. -/
theorem upperUnitriangularSubgroup_jacobson_le_augmentationKernel :
    Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) ≤
      RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom := by
  letI :
      (RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom).IsMaximal :=
    upperUnitriangularSubgroup_augmentationKernel_isMaximal (p := p)
  -- The Jacobson radical is contained in every maximal ideal, in particular in the augmentation
  -- kernel.
  exact Ring.jacobson_le_of_isMaximal _

/-- Helper for Exercise 13-13.1-17: Serre's generator-level Jacobson lemma upgrades the concrete
Heisenberg augmentation kernel to a subideal of the Jacobson radical. -/
theorem upperUnitriangularSubgroup_augmentationKernel_le_jacobson :
    RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom ≤
      Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) := by
  have hspan :
      Ideal.span
          (Set.range fun g : upperUnitriangularSubgroup (ZMod p) 3 =>
            (MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
                (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ≤
        Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    have hP :
        IsPGroup p (upperUnitriangularSubgroup (ZMod p) 3) :=
      IsPGroup.of_card (upperUnitriangularSubgroup_card_p_cubed (p := p))
    -- Each standard augmentation generator already lies in the Jacobson radical.
    simpa using
      p_group_generator_sub_one_mem_jacobson
        (p := p) (G := upperUnitriangularSubgroup (ZMod p) 3) hP g
  -- Rewrite the augmentation kernel by the span of the standard generators and apply the new
  -- generator-level Jacobson owner.
  rw [upperUnitriangularSubgroup_augmentationKernel_eq_span_sub_one (p := p)]
  exact hspan

/-- Helper for Exercise 13-13.1-17: on the canonical Heisenberg model, the Jacobson radical is
exactly the augmentation kernel. -/
theorem upperUnitriangularSubgroup_jacobson_eq_augmentationKernel :
    Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) =
      RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom := by
  -- The easy maximal-ideal inclusion and the new generator-level inclusion meet in the middle.
  exact le_antisymm
    (upperUnitriangularSubgroup_jacobson_le_augmentationKernel (p := p))
    (upperUnitriangularSubgroup_augmentationKernel_le_jacobson (p := p))

end Exercise137

end

end Exercise_13_13_1_17

end Chap13

end Serre
