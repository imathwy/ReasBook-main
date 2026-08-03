import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.Algebra.Module.Equiv
import BauschkeLean.Chap13.Text_13_18_1
import BauschkeLean.Chap21.Example_21_3
import BauschkeLean.Chap23.Definition_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProduct InnerProductSpace Pointwise SetValuedOperator
open ERealFunction
open SetValuedOperator

universe u v

namespace ContinuousLinearMap

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- `source-facing`: Example 23.5 identifies the resolvent of the scaled skew block operator.
-- `core/canonical`: Chapter 23 names that resolvent `J[(γ : ℝ) • A]`.
-- `bridge/view`: the reusable explicit coordinate formulas are the `*_apply` lemmas below.

noncomputable section

/-- The skew block operator associated with `L`, acting on the product space by
`(x, v) ↦ (L† v, -L x)`. -/
def skewCouplingMap (L : H →L[ℝ] K) : H × K →L[ℝ] H × K :=
  (L† ∘L ContinuousLinearMap.snd ℝ H K).prod
    (((-1 : ℝ) • L) ∘L ContinuousLinearMap.fst ℝ H K)

/-- Applying `skewCouplingMap` gives the source's skew block formula. -/
@[simp] theorem skewCouplingMap_apply (L : H →L[ℝ] K) (x : H) (v : K) :
    skewCouplingMap L (x, v) = ((L†) v, -L x) := by
  simp [skewCouplingMap]

/-- The closed-form resolvent candidate for the skew block operator associated with `L`. -/
def skewCouplingResolvent (L : H →L[ℝ] K) (γ : PosReal) : H × K →L[ℝ] H × K :=
  ((((1 : H →L[ℝ] H) + (γ : ℝ) ^ (2 : ℕ) • (L† ∘L L)).inverse) ∘L
      ((ContinuousLinearMap.fst ℝ H K) -
        (γ : ℝ) • (L† ∘L ContinuousLinearMap.snd ℝ H K))).prod
    ((((1 : K →L[ℝ] K) + (γ : ℝ) ^ (2 : ℕ) • (L ∘L L†)).inverse) ∘L
      ((ContinuousLinearMap.snd ℝ H K) +
        (γ : ℝ) • (L ∘L ContinuousLinearMap.fst ℝ H K)))

/-- Applying `skewCouplingResolvent` recovers the textbook closed formula for `J_{γA}`. -/
@[simp] theorem skewCouplingResolvent_apply (L : H →L[ℝ] K) (γ : PosReal)
    (x : H) (v : K) :
    skewCouplingResolvent L γ (x, v) =
      ( ((1 + (γ : ℝ) ^ (2 : ℕ) • (L† ∘L L)).inverse)
          (x - (γ : ℝ) • ((L†) v))
      , ((1 + (γ : ℝ) ^ (2 : ℕ) • (L ∘L L†)).inverse)
          (v + (γ : ℝ) • (L x)) ) := by
  simp [skewCouplingResolvent]

/-- Helper for Example 23.5: the explicit first coordinate appearing in the closed resolvent
formula for the skew block operator. -/
def skewCouplingFirstCoordinate (L : H →L[ℝ] K) (γ : PosReal) (x : H) (v : K) : H :=
  (((1 : H →L[ℝ] H) + (γ : ℝ) ^ (2 : ℕ) • (L† ∘L L)).inverse)
    (x - (γ : ℝ) • ((L†) v))

/-- Helper for Example 23.5: the explicit second coordinate appearing in the closed resolvent
formula for the skew block operator. -/
def skewCouplingSecondCoordinate (L : H →L[ℝ] K) (γ : PosReal) (x : H) (v : K) : K :=
  (((1 : K →L[ℝ] K) + (γ : ℝ) ^ (2 : ℕ) • (L ∘L L†)).inverse)
    (v + (γ : ℝ) • (L x))

/-- Helper for Example 23.5: scaling a bounded operator scales its Gram operator quadratically. -/
lemma smul_adjoint_comp_smul
    (L : H →L[ℝ] K) (γ : ℝ) :
    ((γ • L)† ∘L (γ • L)) =
      γ ^ (2 : ℕ) • (L† ∘L L) := by
  -- Rewrite the scaled Gram operator by pulling the scalar through both compositions.
  calc
    (γ • L)† ∘L (γ • L) = (γ • L†) ∘L (γ • L) := by
      simp
    _ = γ • (L† ∘L (γ • L)) := by
      rw [ContinuousLinearMap.smul_comp]
    _ = γ • (γ • (L† ∘L L)) := by
      rw [ContinuousLinearMap.comp_smul]
    _ = γ ^ (2 : ℕ) • (L† ∘L L) := by
      simp [pow_two, smul_smul]

/-- Helper for Example 23.5: the first inverse operator in the closed resolvent formula is
invertible because it is `Id + (γL)†(γL)`. -/
lemma id_add_square_smul_adjoint_comp_isUnit
    (L : H →L[ℝ] K) (γ : PosReal) :
    IsUnit ((1 : H →L[ℝ] H) + (γ : ℝ) ^ (2 : ℕ) • (L† ∘L L)) := by
  -- Rewrite the operator as `Id + (γL)†(γL)` and reuse the generic invertibility lemma.
  simpa [smul_adjoint_comp_smul, pow_two, smul_smul, mul_assoc] using
    one_add_adjoint_comp_isUnit ((γ : ℝ) • L)

/-- Helper for Example 23.5: the second inverse operator in the closed resolvent formula is
invertible because it is `Id + (γL†)†(γL†)`. -/
lemma id_add_square_smul_comp_adjoint_isUnit
    (L : H →L[ℝ] K) (γ : PosReal) :
    IsUnit ((1 : K →L[ℝ] K) + (γ : ℝ) ^ (2 : ℕ) • (L ∘L L†)) := by
  -- Apply the same `Id + A†A` invertibility argument to the adjoint operator.
  simpa [smul_adjoint_comp_smul, pow_two, smul_smul, mul_assoc] using
    one_add_adjoint_comp_isUnit ((γ : ℝ) • L†)

/-- Helper for Example 23.5: belonging to `Id + γA` for the skew block map is exactly the
textbook pair of block equations. -/
lemma mem_id_add_smul_skewCouplingMap_iff
    (L : H →L[ℝ] K) (γ : PosReal) (x p : H) (v q : K) :
    (x, v) ∈
        (((id : H × K → H × K).toSetValuedOperator) +
          ((γ : ℝ) • (skewCouplingMap L).toSetValuedOperator)) (p, q) ↔
      x = p + (γ : ℝ) • ((L†) q) ∧ v = q - (γ : ℝ) • (L p) := by
  constructor
  · intro h
    rcases Set.mem_add.mp h with ⟨u, hu, w, hw, huw⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu
    simp [Function.toSetValuedOperator_apply, skewCouplingMap_apply, Prod.smul_mk] at hw
    subst u
    subst w
    have hx : p + (γ : ℝ) • ((L†) q) = x := by
      simpa using congrArg Prod.fst huw
    have hv : q + (γ : ℝ) • (-L p) = v := by
      simpa using congrArg Prod.snd huw
    constructor
    · simpa [add_comm] using hx.symm
    · simpa [sub_eq_add_neg, smul_neg] using hv.symm
  · rintro ⟨hx, hv⟩
    apply Set.mem_add.2
    refine ⟨(p, q), ?_, ((γ : ℝ) • ((L†) q), (γ : ℝ) • (-L p)), ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · simp [Function.toSetValuedOperator_apply, skewCouplingMap_apply, Prod.smul_mk]
    · exact Prod.ext (by simpa [add_comm] using hx.symm)
        (by simpa [sub_eq_add_neg, smul_neg, add_comm, add_left_comm, add_assoc] using hv.symm)

/-- Helper for Example 23.5: resolvent membership for the scaled skew block operator is exactly
the textbook pair of block equations. -/
lemma mem_resolvent_smul_skewCouplingMap_iff
    (L : H →L[ℝ] K) (γ : PosReal) (x p : H) (v q : K) :
    (p, q) ∈ J[((γ : ℝ) • (skewCouplingMap L).toSetValuedOperator)] (x, v) ↔
      x = p + (γ : ℝ) • ((L†) q) ∧ v = q - (γ : ℝ) • (L p) := by
  -- Unfold the resolvent as the inverse of `Id + γA` and reuse the direct block-equation rewrite.
  rw [SetValuedOperator.resolvent_def, SetValuedOperator.mem_inverse_iff]
  exact mem_id_add_smul_skewCouplingMap_iff L γ x p v q

/-- Helper for Example 23.5: the textbook block equations determine the first coordinate via the
inverse of `Id + γ²L†L`. -/
lemma block_equations_resolve_first_coordinate
    (L : H →L[ℝ] K) (γ : PosReal) {x p : H} {v q : K}
    (hx : x = p + (γ : ℝ) • ((L†) q))
    (hv : v = q - (γ : ℝ) • (L p)) :
    p = (((1 : H →L[ℝ] H) + (γ : ℝ) ^ (2 : ℕ) • (L† ∘L L)).inverse)
      (x - (γ : ℝ) • ((L†) v)) := by
  let T : H →L[ℝ] H := (1 : H →L[ℝ] H) + (γ : ℝ) ^ (2 : ℕ) • (L† ∘L L)
  have hT_unit : IsUnit T := id_add_square_smul_adjoint_comp_isUnit L γ
  have hqv : q - v = (γ : ℝ) • (L p) := by
    -- Rearranging the second block equation isolates the `γLp` term.
    calc
      q - v = q - (q - (γ : ℝ) • (L p)) := by rw [hv]
      _ = (γ : ℝ) • (L p) := by abel_nf
  have hTp : T p = x - (γ : ℝ) • ((L†) v) := by
    -- Substitute the second block equation into the first exactly as in the textbook proof.
    calc
      T p = p + (γ : ℝ) ^ (2 : ℕ) • ((L† ∘L L) p) := by
        simp [T, ContinuousLinearMap.comp_apply]
      _ = p + (γ : ℝ) • ((L†) (q - v)) := by
        rw [hqv, ContinuousLinearMap.comp_apply]
        simp [pow_two, smul_smul]
      _ = p + ((γ : ℝ) • ((L†) q) - (γ : ℝ) • ((L†) v)) := by
        rw [(L†).map_sub, smul_sub]
      _ = x - (γ : ℝ) • ((L†) v) := by
        simp [hx, sub_eq_add_neg, add_assoc]
  -- Cancel `T` on the left to recover the explicit inverse formula for `p`.
  calc
    p = T.inverse (T p) := by
      symm
      simpa [T, ← ContinuousLinearMap.ringInverse_eq_inverse] using
        congrArg (fun S : H →L[ℝ] H ↦ S p) (Ring.inverse_mul_cancel T hT_unit)
    _ = T.inverse (x - (γ : ℝ) • ((L†) v)) := by rw [hTp]

/-- Helper for Example 23.5: the textbook block equations determine the second coordinate via the
inverse of `Id + γ²LL†`. -/
lemma block_equations_resolve_second_coordinate
    (L : H →L[ℝ] K) (γ : PosReal) {x p : H} {v q : K}
    (hx : x = p + (γ : ℝ) • ((L†) q))
    (hv : v = q - (γ : ℝ) • (L p)) :
    q = (((1 : K →L[ℝ] K) + (γ : ℝ) ^ (2 : ℕ) • (L ∘L L†)).inverse)
      (v + (γ : ℝ) • (L x)) := by
  let T : K →L[ℝ] K := (1 : K →L[ℝ] K) + (γ : ℝ) ^ (2 : ℕ) • (L ∘L L†)
  have hT_unit : IsUnit T := id_add_square_smul_comp_adjoint_isUnit L γ
  have hxp : x - p = (γ : ℝ) • ((L†) q) := by
    -- Rearranging the first block equation isolates the `γL†q` term.
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hx)
  have hTq : T q = v + (γ : ℝ) • (L x) := by
    -- Substitute the first block equation into the second and collect the `LL†` term.
    calc
      T q = q + (γ : ℝ) ^ (2 : ℕ) • ((L ∘L L†) q) := by
        simp [T, ContinuousLinearMap.comp_apply]
      _ = q + (γ : ℝ) • (L (x - p)) := by
        rw [hxp, ContinuousLinearMap.comp_apply]
        simp [pow_two, smul_smul]
      _ = q + ((γ : ℝ) • (L x) - (γ : ℝ) • (L p)) := by
        rw [L.map_sub, smul_sub]
      _ = v + (γ : ℝ) • (L x) := by
        simp [hv, sub_eq_add_neg, add_left_comm, add_comm]
  -- Cancel `T` on the left to recover the explicit inverse formula for `q`.
  calc
    q = T.inverse (T q) := by
      symm
      simpa [T, ← ContinuousLinearMap.ringInverse_eq_inverse] using
        congrArg (fun S : K →L[ℝ] K ↦ S q) (Ring.inverse_mul_cancel T hT_unit)
    _ = T.inverse (v + (γ : ℝ) • (L x)) := by rw [hTq]

/-- Helper for Example 23.5: normalizing the affine update `v + γLp` through the adjoint produces
the `γL†v + γ²L†Lp` term from the textbook block computation. -/
lemma affine_update_adjoint_normalization
    (L : H →L[ℝ] K) (γ : PosReal) (p : H) (v : K) :
    (γ : ℝ) • ((L†) (v + (γ : ℝ) • (L p))) =
      (γ : ℝ) • ((L†) v) + (γ : ℝ) ^ (2 : ℕ) • ((L† ∘L L) p) := by
  -- Expand the affine update once so the `γ²L†Lp` term appears in canonical form.
  calc
    (γ : ℝ) • ((L†) (v + (γ : ℝ) • (L p)))
        = (γ : ℝ) • ((L†) v + (L†) ((γ : ℝ) • (L p))) := by
            rw [(L†).map_add]
    _ = (γ : ℝ) • ((L†) v + (γ : ℝ) • ((L†) (L p))) := by
          rw [(L†).map_smul]
    _ = (γ : ℝ) • ((L†) v) + (γ : ℝ) • ((γ : ℝ) • ((L†) (L p))) := by
          rw [smul_add]
    _ = (γ : ℝ) • ((L†) v) + (γ : ℝ) ^ (2 : ℕ) • ((L† ∘L L) p) := by
          simp [ContinuousLinearMap.comp_apply, pow_two, smul_smul]

/-- Helper for Example 23.5: the explicit first coordinate reassembles the first block equation
from the textbook proof while the second coordinate is still kept as the affine update
`v + γLp₀`. -/
lemma first_coordinate_reassembles_block_equation
    (L : H →L[ℝ] K) (γ : PosReal) (x : H) (v : K) :
    x = skewCouplingFirstCoordinate L γ x v +
      (γ : ℝ) •
        ((L†)
          (v + (γ : ℝ) • (L (skewCouplingFirstCoordinate L γ x v)))) := by
  let T : H →L[ℝ] H := (1 : H →L[ℝ] H) + (γ : ℝ) ^ (2 : ℕ) • (L† ∘L L)
  let p₀ : H := skewCouplingFirstCoordinate L γ x v
  have hT_unit : IsUnit T := id_add_square_smul_adjoint_comp_isUnit L γ
  have hp₀_inverse_eq : T p₀ = x - (γ : ℝ) • ((L†) v) := by
    -- Cancel the inverse in the closed formula for `p₀`.
    simpa [T, p₀, skewCouplingFirstCoordinate, ← ContinuousLinearMap.ringInverse_eq_inverse] using
      congrArg (fun S : H →L[ℝ] H ↦ S (x - (γ : ℝ) • ((L†) v)))
        (Ring.mul_inverse_cancel T hT_unit)
  -- Route correction: keep `q₀ := v + γLp₀` implicit here and only normalize the affine update.
  calc
    x = (x - (γ : ℝ) • ((L†) v)) + (γ : ℝ) • ((L†) v) := by
      abel_nf
    _ = T p₀ + (γ : ℝ) • ((L†) v) := by rw [hp₀_inverse_eq]
    _ = p₀ + ((γ : ℝ) ^ (2 : ℕ) • ((L† ∘L L) p₀) + (γ : ℝ) • ((L†) v)) := by
          simp [T, ContinuousLinearMap.comp_apply, add_assoc]
    _ = p₀ + ((γ : ℝ) • ((L†) v) + (γ : ℝ) ^ (2 : ℕ) • ((L† ∘L L) p₀)) := by
          abel_nf
    _ = p₀ + (γ : ℝ) • ((L†) (v + (γ : ℝ) • (L p₀))) := by
          congr 1
          exact (affine_update_adjoint_normalization (L := L) (γ := γ) (p := p₀) (v := v)).symm
    _ = skewCouplingFirstCoordinate L γ x v +
          (γ : ℝ) •
            ((L†)
              (v + (γ : ℝ) • (L (skewCouplingFirstCoordinate L γ x v)))) := by
          simp [p₀]

/-- Helper for Example 23.5: the affine-update second coordinate `v + γLp₀` agrees with the
closed second coordinate obtained from the inverse of `Id + γ²LL†`. -/
lemma affine_update_eq_skewCouplingSecondCoordinate
    (L : H →L[ℝ] K) (γ : PosReal) (x : H) (v : K) :
    v + (γ : ℝ) • (L (skewCouplingFirstCoordinate L γ x v)) =
      skewCouplingSecondCoordinate L γ x v := by
  let p₀ : H := skewCouplingFirstCoordinate L γ x v
  let q₀ : K := v + (γ : ℝ) • (L p₀)
  have hx : x = p₀ + (γ : ℝ) • ((L†) q₀) := by
    -- Reuse the first block equation with the affine-update coordinate named explicitly.
    simpa [p₀, q₀] using first_coordinate_reassembles_block_equation L γ x v
  have hv : v = q₀ - (γ : ℝ) • (L p₀) := by
    -- The second block equation is tautological from the definition of `q₀`.
    dsimp [q₀]
    abel_nf
  -- Feed the block system into the solved second-coordinate formula.
  simpa [p₀, q₀, skewCouplingSecondCoordinate] using
    (block_equations_resolve_second_coordinate (L := L) (γ := γ) (x := x) (v := v)
      (p := p₀) (q := q₀) hx hv)

/-- Helper for Example 23.5: the explicit coordinate pair from the closed formula satisfies the
resolvent block equations, hence belongs to the resolvent graph. -/
lemma explicit_coordinates_mem_resolvent
    (L : H →L[ℝ] K) (γ : PosReal) (x : H) (v : K) :
    (skewCouplingFirstCoordinate L γ x v, skewCouplingSecondCoordinate L γ x v) ∈
      J[((γ : ℝ) • (skewCouplingMap L).toSetValuedOperator)] (x, v) := by
  let p₀ : H := skewCouplingFirstCoordinate L γ x v
  have hq₀ : v + (γ : ℝ) • (L p₀) = skewCouplingSecondCoordinate L γ x v := by
    -- Identify the affine-update coordinate with the explicit inverse formula for the second slot.
    simpa [p₀] using affine_update_eq_skewCouplingSecondCoordinate L γ x v
  have hx : x = p₀ + (γ : ℝ) • ((L†) (skewCouplingSecondCoordinate L γ x v)) := by
    -- Rewrite the first block equation through the identified second coordinate.
    simpa [p₀, hq₀] using first_coordinate_reassembles_block_equation L γ x v
  have hv : v = skewCouplingSecondCoordinate L γ x v - (γ : ℝ) • (L p₀) := by
    -- The same affine-update identity gives the second block equation.
    simpa [p₀, hq₀, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (show v = (v + (γ : ℝ) • (L p₀)) - (γ : ℝ) • (L p₀) by
        abel_nf)
  -- Membership in the resolvent is exactly the pair of block equations.
  rw [mem_resolvent_smul_skewCouplingMap_iff]
  exact ⟨hx, hv⟩

/-- Example 23.5: for the skew block operator `A(x, v) = (L† v, -L x)`, the resolvent
`J_{γA} = (Id + γ A)⁻¹` is the singleton-valued operator induced by the explicit closed formula
`((Id + γ^2 L†L)⁻¹ (x - γ L†v), (Id + γ^2 LL†)⁻¹ (v + γ Lx))`. -/
theorem inverse_id_add_smul_skewCouplingMap_eq_skewCouplingResolvent
    (L : H →L[ℝ] K) (γ : PosReal) :
    J[((γ : ℝ) • (skewCouplingMap L).toSetValuedOperator)] =
      (skewCouplingResolvent L γ).toSetValuedOperator := by
  -- Compare both operators pointwise and reduce set equality to point membership of a pair.
  funext xv
  rcases xv with ⟨x, v⟩
  ext y
  rcases y with ⟨p, q⟩
  constructor
  · intro hy
    have hblock := (mem_resolvent_smul_skewCouplingMap_iff L γ x p v q).mp hy
    rcases hblock with ⟨hx, hv⟩
    -- The forward direction is exactly the solved coordinate recovery from the block equations.
    have hpair :
        (p, q) =
          (skewCouplingFirstCoordinate L γ x v, skewCouplingSecondCoordinate L γ x v) := by
      exact Prod.ext
        (block_equations_resolve_first_coordinate (L := L) (γ := γ) hx hv)
        (block_equations_resolve_second_coordinate (L := L) (γ := γ) hx hv)
    simpa [Function.toSetValuedOperator_apply, skewCouplingResolvent_apply,
      skewCouplingFirstCoordinate, skewCouplingSecondCoordinate] using hpair
  · intro hy
    have hy_pair : (p, q) = skewCouplingResolvent L γ (x, v) := by
      simpa [Function.toSetValuedOperator_apply] using hy
    have hp : p = skewCouplingFirstCoordinate L γ x v := by
      simpa [skewCouplingResolvent_apply, skewCouplingFirstCoordinate, skewCouplingSecondCoordinate]
        using congrArg Prod.fst hy_pair
    have hq : q = skewCouplingSecondCoordinate L γ x v := by
      simpa [skewCouplingResolvent_apply, skewCouplingFirstCoordinate, skewCouplingSecondCoordinate]
        using congrArg Prod.snd hy_pair
    -- Route correction: use the explicit resolvent-membership lemma instead of normalizing the
    -- reverse direction inline.
    rw [hp, hq]
    exact explicit_coordinates_mem_resolvent L γ x v

end

end ContinuousLinearMap
