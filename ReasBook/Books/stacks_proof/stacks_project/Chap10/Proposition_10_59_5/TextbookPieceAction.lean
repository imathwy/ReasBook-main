import Mathlib
import StacksProject_2024.Chap10.Definition_10_58_3
import StacksProject_2024.Chap10.Definition_10_59_1
import StacksProject_2024.Chap10.Lemma_10_52_8
import StacksProject_2024.Chap10.Lemma_10_58_5
import StacksProject_2024.Chap10.Lemma_10_59_2
import StacksProject_2024.Chap10.Proposition_10_58_7
import StacksProject_2024.Chap10.Proposition_10_59_5.RingGrading

universe u v

open Filter
open HomogeneousIdeal
open IsLocalRing
open scoped BigOperators Ideal

noncomputable section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Ideal

variable (I : Ideal R)

/-- Helper for Proposition 10.59.5: viewing an ideal multiple of a submodule inside the ambient
module agrees with the intrinsic ideal multiple in the submodule itself. -/
lemma submoduleOf_smul_eq_smul_top
    (J : Ideal R) (N : Submodule R M) :
    (J • N).submoduleOf N = (J • (⊤ : Submodule R N)) := by
  -- Pull the ambient scalar multiple back along the subtype of `N`.
  simpa [Submodule.range_subtype] using
    (Submodule.comap_smul'' (f := N.subtype) N.subtype_injective
      (p := N) (I := J) (by simpa [Submodule.range_subtype]))

/-- Helper for Proposition 10.59.5: multiplying the stage `I^n M` by `I^d` shifts the filtration
index by `d`. -/
lemma idealAssociatedGradedStage_pow_smul_eq
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ) :
    ((I ^ d) • RingTheory.Sequence.idealAssociatedGradedStage I N n : Submodule R N) =
      RingTheory.Sequence.idealAssociatedGradedStage I N (n + d) := by
  -- Rewrite the shifted stage as `I^d • (I^n M)` and then collect the powers of `I`.
  calc
    ((I ^ d) • RingTheory.Sequence.idealAssociatedGradedStage I N n : Submodule R N)
        = ((I ^ d) • ((I ^ n) • (⊤ : Submodule R N)) : Submodule R N) := rfl
    _ = (((I ^ d) * (I ^ n)) • (⊤ : Submodule R N) : Submodule R N) := by
          rw [← mul_smul]
    _ = ((I ^ (d + n)) • (⊤ : Submodule R N) : Submodule R N) := by
          rw [← pow_add]
    _ = RingTheory.Sequence.idealAssociatedGradedStage I N (n + d) := by
          simp [RingTheory.Sequence.idealAssociatedGradedStage, Nat.add_comm]

/-- Helper for Proposition 10.59.5: multiplying the denominator `I (I^n M)` by `I^d` gives the
denominator inside the shifted stage `I^(n + d) M`. -/
lemma idealAssociatedGradedDenominator_pow_smul_eq
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ) :
    ((I ^ d) • (I • RingTheory.Sequence.idealAssociatedGradedStage I N n) :
        Submodule R N) =
      I • RingTheory.Sequence.idealAssociatedGradedStage I N (n + d) := by
  -- Commute the extra `I`-factor to the front and then reuse the stage-shift identity.
  calc
    ((I ^ d) • (I • RingTheory.Sequence.idealAssociatedGradedStage I N n) :
        Submodule R N)
        = (((I ^ d) * I) • RingTheory.Sequence.idealAssociatedGradedStage I N n :
            Submodule R N) := by
              rw [← mul_smul]
    _ = ((I * I ^ d) • RingTheory.Sequence.idealAssociatedGradedStage I N n :
          Submodule R N) := by
            rw [Ideal.mul_comm]
    _ = (I • ((I ^ d) • RingTheory.Sequence.idealAssociatedGradedStage I N n) :
          Submodule R N) := by
            rw [mul_smul]
    _ = I • RingTheory.Sequence.idealAssociatedGradedStage I N (n + d) := by
          rw [idealAssociatedGradedStage_pow_smul_eq (R := R) (N := N) I d n]

/-- Helper for Proposition 10.59.5: multiplying a representative in the degree-`d` ring stage by
one in the degree-`n` module stage lands in the shifted stage `I^(d + n)N`. -/
lemma idealAssociatedGradedPiece_smul_mem_stage
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R d)
    (y : RingTheory.Sequence.idealAssociatedGradedStage I N n) :
    (x : R) • (y : N) ∈ RingTheory.Sequence.idealAssociatedGradedStage I N (d + n) := by
  -- Put the target stage back in the source form `(I ^ d) • (I ^ n N)`.
  rw [Nat.add_comm, ← idealAssociatedGradedStage_pow_smul_eq (R := R) (N := N) I d n]
  have hx : (x : R) ∈ I ^ d := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using x.2
  exact Submodule.smul_mem_smul hx y.2

/-- Helper for Proposition 10.59.5: a degree-`d` stage representative acts linearly on the
degree-`n` stage by multiplication. -/
def idealAssociatedGradedPiece_smulOnStage
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R d) :
    RingTheory.Sequence.idealAssociatedGradedStage I N n →ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedStage I N (d + n) :=
  LinearMap.codRestrict
    (RingTheory.Sequence.idealAssociatedGradedStage I N (d + n))
    ((x : R) • (RingTheory.Sequence.idealAssociatedGradedStage I N n).subtype)
    (fun y ↦ idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := N) I d n x y)

/-- Helper for Proposition 10.59.5: the stage action sends the denominator `I^(n + 1)N` into the
shifted denominator `I^(d + n + 1)N`. -/
lemma idealAssociatedGradedPiece_smulOnStage_denominator_le
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R d) :
    (RingTheory.Sequence.idealAssociatedGradedStage I N (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage I N n) ≤
      Submodule.comap
        (idealAssociatedGradedPiece_smulOnStage (R := R) (N := N) I d n x)
        ((RingTheory.Sequence.idealAssociatedGradedStage I N (d + n + 1)).submoduleOf
          (RingTheory.Sequence.idealAssociatedGradedStage I N (d + n))) := by
  intro y hy
  -- View the denominator element as a representative in degree `n + 1`.
  change
    (x : R) • ((y : RingTheory.Sequence.idealAssociatedGradedStage I N n) : N) ∈
      RingTheory.Sequence.idealAssociatedGradedStage I N (d + n + 1)
  let y' : RingTheory.Sequence.idealAssociatedGradedStage I N (n + 1) := ⟨y, hy⟩
  simpa [Nat.add_assoc] using
    (idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := N) I d (n + 1) x y')

/-- Helper for Proposition 10.59.5: fixing a degree-`d` stage representative gives a descended
map on the degree-`n` quotient piece. -/
def idealAssociatedGradedPiece_smulMapFromStage
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R d) :
    RingTheory.Sequence.idealAssociatedGradedPiece I N n →ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece I N (d + n) :=
  Submodule.mapQ
    ((RingTheory.Sequence.idealAssociatedGradedStage I N (n + 1)).submoduleOf
      (RingTheory.Sequence.idealAssociatedGradedStage I N n))
    ((RingTheory.Sequence.idealAssociatedGradedStage I N (d + n + 1)).submoduleOf
      (RingTheory.Sequence.idealAssociatedGradedStage I N (d + n)))
    (idealAssociatedGradedPiece_smulOnStage (R := R) (N := N) I d n x)
    (idealAssociatedGradedPiece_smulOnStage_denominator_le (R := R) (N := N) I d n x)

/-- Helper for Proposition 10.59.5: on a quotient representative, the descended stage action is
just multiplication of representatives. -/
lemma idealAssociatedGradedPiece_smulMapFromStage_mk
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R d)
    (y : RingTheory.Sequence.idealAssociatedGradedStage I N n) :
    idealAssociatedGradedPiece_smulMapFromStage (R := R) (N := N) I d n x
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨(x : R) • (y : N),
          idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := N) I d n x y⟩ := by
  -- Unfold `Submodule.mapQ` only on the chosen quotient representative.
  rw [idealAssociatedGradedPiece_smulMapFromStage, Submodule.mapQ_apply]
  rfl

/-- Helper for Proposition 10.59.5: the stage-level action is linear in the ring-stage
representative. -/
def idealAssociatedGradedPiece_smulLinearOnStage
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage I R d →ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece I N n →ₗ[R]
        RingTheory.Sequence.idealAssociatedGradedPiece I N (d + n) where
  toFun := idealAssociatedGradedPiece_smulMapFromStage (R := R) (N := N) I d n
  map_add' x y := by
    -- Compute on quotient representatives so the identity reduces to `add_smul`.
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro m
    rw [idealAssociatedGradedPiece_smulMapFromStage_mk]
    simpa [idealAssociatedGradedPiece_smulMapFromStage_mk, add_smul] using
      (Submodule.Quotient.mk_add
        (p := (RingTheory.Sequence.idealAssociatedGradedStage I N (d + n + 1)).submoduleOf
          (RingTheory.Sequence.idealAssociatedGradedStage I N (d + n)))
        (x := ⟨(x : R) • (m : N),
          idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := N) I d n x m⟩)
        (y := ⟨(y : R) • (m : N),
          idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := N) I d n y m⟩))
  map_smul' r x := by
    -- Compute on quotient representatives so the identity reduces to `smul_assoc`.
    apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro m
    rw [idealAssociatedGradedPiece_smulMapFromStage_mk]
    simpa [idealAssociatedGradedPiece_smulMapFromStage_mk, mul_smul] using
      (Submodule.Quotient.mk_smul
        (p := (RingTheory.Sequence.idealAssociatedGradedStage I N (d + n + 1)).submoduleOf
          (RingTheory.Sequence.idealAssociatedGradedStage I N (d + n)))
        r
        ⟨(x : R) • (m : N),
          idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := N) I d n x m⟩)

/-- Helper for Proposition 10.59.5: a stage representative from `I^(d + 1)` acts trivially on
the degree-`n` quotient piece. -/
lemma idealAssociatedGradedPiece_smulLinearOnStage_denominator_le
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ) :
  (RingTheory.Sequence.idealAssociatedGradedStage I R (d + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage I R d) ≤
      LinearMap.ker
        (idealAssociatedGradedPiece_smulLinearOnStage (R := R) (N := N) I d n) := by
  intro x hx
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro m
  let x' : RingTheory.Sequence.idealAssociatedGradedStage I R (d + 1) := ⟨x, hx⟩
  have hzero :
      (x' : R) • (m : N) ∈ RingTheory.Sequence.idealAssociatedGradedStage I N (d + n + 1) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := N) I (d + 1) n x' m)
  -- The target class is zero exactly because its representative lands in the next stage.
  change
    idealAssociatedGradedPiece_smulMapFromStage (R := R) (N := N) I d n x
        (Submodule.Quotient.mk m) = 0
  rw [idealAssociatedGradedPiece_smulMapFromStage_mk]
  simpa using hzero

/-- Helper for Proposition 10.59.5: the degree-`d` associated graded ring piece acts on the
degree-`n` associated graded module piece by multiplying representatives and descending to the
quotients. -/
def idealAssociatedGradedPiece_smulLinear
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedPiece I R d →ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece I N n →ₗ[R]
        RingTheory.Sequence.idealAssociatedGradedPiece I N (d + n) :=
  Submodule.liftQ
    ((RingTheory.Sequence.idealAssociatedGradedStage I R (d + 1)).submoduleOf
      (RingTheory.Sequence.idealAssociatedGradedStage I R d))
    (idealAssociatedGradedPiece_smulLinearOnStage (R := R) (N := N) I d n)
    (idealAssociatedGradedPiece_smulLinearOnStage_denominator_le (R := R) (N := N) I d n)

/-- Helper for Proposition 10.59.5: the ring multiplication on quotient pieces is the special case
`N = R` of the descended quotient-piece action. -/
def idealAssociatedGradedPiece_mulLinear
    (I : Ideal R) (d e : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedPiece I R d →ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece I R e →ₗ[R]
        RingTheory.Sequence.idealAssociatedGradedPiece I R (d + e) :=
  idealAssociatedGradedPiece_smulLinear (R := R) (N := R) I d e

/-- Helper for Proposition 10.59.5: on quotient representatives, the descended quotient-piece
action is still represented by ordinary multiplication in the ambient module. -/
lemma idealAssociatedGradedPiece_smulLinear_apply_mk_mk
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (d n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R d)
    (y : RingTheory.Sequence.idealAssociatedGradedStage I N n) :
    idealAssociatedGradedPiece_smulLinear (R := R) (N := N) I d n
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨(x : R) • (y : N),
          idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := N) I d n x y⟩ := by
  -- First descend through the quotient on the ring side, then evaluate the stage-level formula.
  rw [idealAssociatedGradedPiece_smulLinear, Submodule.liftQ_apply]
  exact idealAssociatedGradedPiece_smulMapFromStage_mk (R := R) (N := N) I d n x y

/-- Helper for Proposition 10.59.5: transporting a stage representative across an equality of
indices does not change its underlying module element. -/
lemma idealAssociatedGradedStage_cast_coe_eq
    {N : Type*} [AddCommGroup N] [Module R N]
    {n n' : ℕ} (h : n = n')
    (x : RingTheory.Sequence.idealAssociatedGradedStage I N n) :
    (((cast (congrArg (fun k ↦ ↥(RingTheory.Sequence.idealAssociatedGradedStage I N k)) h) x :
      RingTheory.Sequence.idealAssociatedGradedStage I N n') : N)) = x := by
  -- After identifying the indices, the cast is definitionally the identity on the subtype.
  cases h
  rfl

/-- Helper for Proposition 10.59.5: transporting the quotient class of a stage representative
across an equality of indices is the same class of the recast representative. -/
lemma idealAssociatedGradedPiece_mk_cast_eq
    {N : Type*} [AddCommGroup N] [Module R N]
    {n n' : ℕ} (h : n = n')
    (z : RingTheory.Sequence.idealAssociatedGradedStage I N n') :
    h ▸
      (Submodule.Quotient.mk z :
        RingTheory.Sequence.idealAssociatedGradedPiece I N n') =
      (Submodule.Quotient.mk
        (cast
          (congrArg (fun k ↦ ↥(RingTheory.Sequence.idealAssociatedGradedStage I N k))
            h.symm) z) :
        RingTheory.Sequence.idealAssociatedGradedPiece I N n) := by
  -- After identifying the two indices, both quotient classes are definitionally the same.
  cases h
  rfl

/-- Helper for Proposition 10.59.5: transporting the quotient class of a stage representative
across `Nat.add_assoc` is the same class of the recast representative. -/
lemma idealAssociatedGradedPiece_mk_cast_add_assoc
    {N : Type*} [AddCommGroup N] [Module R N]
    (d e n : ℕ)
    (z : RingTheory.Sequence.idealAssociatedGradedStage I N (d + (e + n))) :
    Nat.add_assoc d e n ▸
      (Submodule.Quotient.mk z :
        RingTheory.Sequence.idealAssociatedGradedPiece I N (d + (e + n))) =
      (Submodule.Quotient.mk
        (cast
          (congrArg (fun k ↦ ↥(RingTheory.Sequence.idealAssociatedGradedStage I N k))
            (Nat.add_assoc d e n).symm) z) :
        RingTheory.Sequence.idealAssociatedGradedPiece I N ((d + e) + n)) := by
  -- This is the generic quotient-cast lemma specialized to the associativity equality of degrees.
  simpa using idealAssociatedGradedPiece_mk_cast_eq (R := R) (I := I)
    (N := N) (h := Nat.add_assoc d e n) z

/-- Helper for Proposition 10.59.5: on the textbook quotient pieces, multiplication in
`gr_I(R)` acts associatively on `gr_I(M)` before any owner-level transport. -/
lemma idealAssociatedGradedPiece_smulLinear_assoc
    (I : Ideal R) (d e n : ℕ)
    (a : RingTheory.Sequence.idealAssociatedGradedPiece I R d)
    (b : RingTheory.Sequence.idealAssociatedGradedPiece I R e)
    (m : RingTheory.Sequence.idealAssociatedGradedPiece I M n) :
    Nat.add_assoc d e n ▸
      idealAssociatedGradedPiece_smulLinear (R := R) (N := M) I d (e + n) a
        (idealAssociatedGradedPiece_smulLinear (R := R) (N := M) I e n b m) =
      idealAssociatedGradedPiece_smulLinear (R := R) (N := M) I (d + e) n
        ((idealAssociatedGradedPiece_mulLinear (R := R) I d e) a b) m := by
  -- Compute both sides on quotient representatives so the remaining comparison lives on the
  -- underlying stage elements.
  refine Submodule.Quotient.induction_on _ a ?_
  intro x
  refine Submodule.Quotient.induction_on _ b ?_
  intro y
  refine Submodule.Quotient.induction_on _ m ?_
  intro z
  have hyz_mem :
      (y : R) • (z : M) ∈ RingTheory.Sequence.idealAssociatedGradedStage I M (e + n) := by
    exact idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := M) I e n y z
  let yz : RingTheory.Sequence.idealAssociatedGradedStage I M (e + n) :=
    ⟨(y : R) • (z : M), hyz_mem⟩
  have hxy_mem :
      (x : R) • (y : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage I R (d + e) := by
    exact idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := R) I d e x y
  let xy : RingTheory.Sequence.idealAssociatedGradedStage I R (d + e) :=
    ⟨(x : R) • (y : R), hxy_mem⟩
  have hleft_mem :
      (x : R) • ((y : R) • (z : M)) ∈
        RingTheory.Sequence.idealAssociatedGradedStage I M (d + (e + n)) := by
    simpa [yz] using
      idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := M) I d (e + n) x yz
  let leftStage : RingTheory.Sequence.idealAssociatedGradedStage I M (d + (e + n)) :=
    ⟨(x : R) • ((y : R) • (z : M)), hleft_mem⟩
  have hright_mem :
      ((x : R) • (y : R)) • (z : M) ∈
        RingTheory.Sequence.idealAssociatedGradedStage I M ((d + e) + n) := by
    simpa [xy] using
      idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := M) I (d + e) n xy z
  let rightStage : RingTheory.Sequence.idealAssociatedGradedStage I M ((d + e) + n) :=
    ⟨((x : R) • (y : R)) • (z : M), hright_mem⟩
  -- Each descended action is defined by multiplication on representatives modulo the next stage.
  rw [idealAssociatedGradedPiece_smulLinear_apply_mk_mk]
  rw [idealAssociatedGradedPiece_smulLinear_apply_mk_mk]
  rw [idealAssociatedGradedPiece_mulLinear, idealAssociatedGradedPiece_smulLinear_apply_mk_mk]
  rw [idealAssociatedGradedPiece_smulLinear_apply_mk_mk]
  -- Rewrite the sole index transport on the left into a cast on the stage representative.
  rw [idealAssociatedGradedPiece_mk_cast_add_assoc (R := R) (I := I) (N := M) d e n leftStage]
  have hcast :
      cast
          (congrArg (fun k ↦ ↥(RingTheory.Sequence.idealAssociatedGradedStage I M k))
            (Nat.add_assoc d e n).symm)
          leftStage =
        rightStage := by
    apply Subtype.ext
    calc
      (((cast
            (congrArg (fun k ↦ ↥(RingTheory.Sequence.idealAssociatedGradedStage I M k))
              (Nat.add_assoc d e n).symm)
            leftStage :
          RingTheory.Sequence.idealAssociatedGradedStage I M ((d + e) + n)) : M)) = leftStage := by
            exact idealAssociatedGradedStage_cast_coe_eq (R := R) (I := I)
              (N := M) (Nat.add_assoc d e n).symm leftStage
      _ = rightStage := by
            change (x : R) • ((y : R) • (z : M)) = ((x : R) • (y : R)) • (z : M)
            simpa [smul_smul] using (mul_smul (x : R) (y : R) (z : M)).symm
  rw [hcast]

/-- Helper for Proposition 10.59.5: a representative in the stage `I^n` defines the degree-`n`
monomial in the quotient-Rees presentation of `gr_I(R)`. -/
lemma ideal_associated_graded_stage_monomial_mem
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    Polynomial.monomial n (x : R) ∈ reesAlgebra I := by
  -- The stage condition is exactly the coefficient condition for a Rees monomial.
  apply reesAlgebra.monomial_mem.mpr
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using x.2

/-- Helper for Proposition 10.59.5: the degree-`n` class of a stage element in the quotient-Rees
presentation of `gr_I(R)`. -/
noncomputable def idealAssociatedGradedStageClass
    (I : Ideal R) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage I R n → idealAssociatedGradedRing I :=
  fun x ↦
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
      ⟨Polynomial.monomial n (x : R), ideal_associated_graded_stage_monomial_mem (R := R) I n x⟩

/-- Helper for Proposition 10.59.5: the degree-`n` monomial representative of a stage element
already lies in the degree-`n` Rees piece. -/
lemma ideal_associated_graded_stage_mem_grade
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    (⟨Polynomial.monomial n (x : R),
        ideal_associated_graded_stage_monomial_mem (R := R) I n x⟩ :
      reesAlgebra I) ∈ reesAlgebraGrade I n := by
  -- The chosen monomial has the canonical degree-`n` shape defining `reesAlgebraGrade`.
  refine ⟨⟨(x : R), ?_⟩, rfl⟩
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using x.2

/-- Helper for Proposition 10.59.5: the stage class map lands in the degree-`n` owner piece of
the associated graded ring. -/
lemma idealAssociatedGradedStageClass_mem_grade
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedStageClass (R := R) I n x ∈ idealAssociatedGradedRingGrade I n := by
  -- The owner-grade witness is the same degree-`n` monomial representative used to define the
  -- stage class.
  refine ⟨⟨Polynomial.monomial n (x : R),
      ideal_associated_graded_stage_monomial_mem (R := R) I n x⟩,
    ideal_associated_graded_stage_mem_grade (R := R) I n x, rfl⟩

/-- Helper for Proposition 10.59.5: multiplying two stage representatives and then taking the
stage class agrees with multiplying the two corresponding stage classes in `gr_I(R)`. -/
lemma idealAssociatedGradedStageClass_mul_local
    (I : Ideal R) {m n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R m)
    (y : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedStageClass (R := R) I (m + n)
        ⟨(x : R) * (y : R),
          idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := R) I m n x y⟩ =
      idealAssociatedGradedStageClass (R := R) I m x *
        idealAssociatedGradedStageClass (R := R) I n y := by
  -- Compare both sides on the explicit quotient classes of the corresponding Rees monomials.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        (⟨Polynomial.monomial (m + n) ((x : R) * (y : R)), _⟩ : reesAlgebra I) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        ((⟨Polynomial.monomial m (x : R), _⟩ : reesAlgebra I) *
          (⟨Polynomial.monomial n (y : R), _⟩ : reesAlgebra I))
  congr 1
  -- The two Rees representatives are the same monomial with multiplied coefficient.
  apply Subtype.ext
  simp [Polynomial.monomial_mul_monomial]

/-- Helper for Proposition 10.59.5: the stage-to-Rees monomial construction is linear before
passing to the associated graded quotient. -/
noncomputable def idealAssociatedGradedStageToReesLinear
    (I : Ideal R) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage I R n →ₗ[R] reesAlgebra I :=
  LinearMap.codRestrict ((reesAlgebra I).toSubmodule)
    ((Polynomial.monomial n).comp
      (show RingTheory.Sequence.idealAssociatedGradedStage I R n →ₗ[R] R from
        (RingTheory.Sequence.idealAssociatedGradedStage I R n).subtype))
    (fun x ↦ ideal_associated_graded_stage_monomial_mem (R := R) I n x)

/-- Helper for Proposition 10.59.5: the linear stage map to `gr_I(R)` lands in the degree-`n`
owner subtype. -/
noncomputable def idealAssociatedGradedStageClassLinear
    (I : Ideal R) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage I R n →ₗ[R] idealAssociatedGradedRingGrade I n :=
  LinearMap.codRestrict (idealAssociatedGradedRingGrade I n)
    (((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I)).toLinearMap).comp
      (idealAssociatedGradedStageToReesLinear (R := R) I n))
    (fun x ↦ by
      simpa [idealAssociatedGradedStageToReesLinear, idealAssociatedGradedStageClass,
        LinearMap.comp_apply] using
        idealAssociatedGradedStageClass_mem_grade (R := R) I n x)

/-- Helper for Proposition 10.59.5: forgetting the grade subtype turns the linear stage-to-grade
map back into the ordinary stage class. -/
lemma idealAssociatedGradedStageClassLinear_apply
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    ((idealAssociatedGradedStageClassLinear (R := R) I n x :
      idealAssociatedGradedRingGrade I n) : idealAssociatedGradedRing I) =
      idealAssociatedGradedStageClass (R := R) I n x := by
  -- Compare both definitions on the common Rees representative before quotienting.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        ((idealAssociatedGradedStageToReesLinear (R := R) I n) x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        ⟨Polynomial.monomial n (x : R),
          ideal_associated_graded_stage_monomial_mem (R := R) I n x⟩
  congr 1

/-- Helper for Proposition 10.59.5: every element of the degree-`n` owner piece is represented by
some stage element in `I^n`. -/
lemma idealAssociatedGradedStageClassLinear_surjective
    (I : Ideal R) (n : ℕ) :
    Function.Surjective (idealAssociatedGradedStageClassLinear (R := R) I n) := by
  intro x
  rcases x.2 with ⟨y, hy, hxy⟩
  rcases hy with ⟨a, rfl⟩
  refine ⟨⟨a.1, ?_⟩, ?_⟩
  · -- A homogeneous Rees generator in degree `n` is exactly an element of `I ^ n`.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using a.2
  · -- The chosen representative is already the canonical monomial image of that stage element.
    exact Subtype.ext <| by
      simpa [idealAssociatedGradedStageClassLinear, idealAssociatedGradedStageToReesLinear] using
        hxy

/-- Helper for Proposition 10.59.5: taking the `n`-th coefficient of a denominator element in the
quotient-Rees presentation lands one step deeper in the `I`-adic filtration. -/
lemma rees_algebra_coeff_mem_pow_succ_of_mem_denominator
    (I : Ideal R) (n : ℕ)
    {y : reesAlgebra I}
    (hy : y ∈ Ideal.map (algebraMap R (reesAlgebra I)) I) :
    y.1.coeff n ∈ I ^ (n + 1) := by
  have hy' : y ∈ I • (⊤ : Submodule R (reesAlgebra I)) := by
    -- Rewrite the denominator ideal as the stage-one scalar multiple.
    simpa [Ideal.smul_top_eq_map] using hy
  -- Check the coefficient condition first on generators, then extend by additivity.
  refine Submodule.smul_induction_on hy' ?_ ?_
  · intro r hr z hz
    have hzcoeff : z.1.coeff n ∈ I ^ n := z.2 n
    change (r • z.1).coeff n ∈ I ^ (n + 1)
    simpa [Polynomial.coeff_smul, smul_eq_mul, pow_succ', Ideal.mul_comm] using
      Ideal.mul_mem_mul hr hzcoeff
  · intro x y hx hy
    simpa [Polynomial.coeff_add] using Ideal.add_mem (I ^ (n + 1)) hx hy

/-- Helper for Proposition 10.59.5: if a degree-`n` coefficient lies in `I^(n + 1)`, then the
corresponding monomial lies in the denominator ideal of the quotient-Rees presentation. -/
lemma monomial_mem_denominator_of_mem_pow_succ
    (I : Ideal R) (n : ℕ) {a : R}
    (ha : a ∈ I ^ (n + 1)) :
    (⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
      reesAlgebra I) ∈ Ideal.map (algebraMap R (reesAlgebra I)) I := by
  have hsmul :
      (⟨Polynomial.monomial n a,
          reesAlgebra.monomial_mem.mpr
            ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
        reesAlgebra I) ∈ I • (⊤ : Submodule R (reesAlgebra I)) := by
    let x : reesAlgebra I :=
      ⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩
    let φ : R →ₗ[R] Polynomial R := Polynomial.monomial n
    have ha' : a ∈ I • (I ^ n : Submodule R R) := by
      -- This is the source identity `I * I^n = I^(n+1)`.
      simpa [Ideal.smul_eq_mul, pow_succ, Ideal.mul_comm] using ha
    let RI : Submodule R (Polynomial R) := Subalgebra.toSubmodule (reesAlgebra I)
    have hmap0 :
        (Submodule.map φ (I ^ n : Submodule R R) : Submodule R (Polynomial R)) ≤ RI := by
      intro p hp
      rcases hp with ⟨b, hb, rfl⟩
      exact reesAlgebra.monomial_mem.mpr hb
    have hmap :
        (Submodule.map φ (I • (I ^ n : Submodule R R)) : Submodule R (Polynomial R)) ≤
          (I • RI : Submodule R (Polynomial R)) := by
      rw [Submodule.map_smul'']
      refine Submodule.smul_le.mpr ?_
      intro r hr p hp
      exact Submodule.smul_mem_smul hr (hmap0 hp)
    have hambient : (x : Polynomial R) ∈ I • RI := by
      have hxmap : φ a ∈ Submodule.map φ (I • (I ^ n : Submodule R R)) := by
        exact Submodule.mem_map_of_mem ha'
      exact hmap <| by
        simpa [φ, x] using hxmap
    exact (Submodule.mem_smul_top_iff (I := I) (N := RI) (x := x)).2 hambient
  simpa [Ideal.smul_top_eq_map] using hsmul

/-- Helper for Proposition 10.59.5: the degree-`n` stage class vanishes exactly when the
representative lies in the next `I`-adic stage. -/
lemma associated_graded_stage_class_zero_iff
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedStageClass (R := R) I n x = 0 ↔
      (x : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage I R (n + 1) := by
  constructor
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
          ⟨Polynomial.monomial n (x : R),
            ideal_associated_graded_stage_monomial_mem (R := R) I n x⟩ = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    -- A vanishing class means the monomial representative lies in the denominator ideal.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using
      rees_algebra_coeff_mem_pow_succ_of_mem_denominator (R := R) I n hx
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
          ⟨Polynomial.monomial n (x : R),
            ideal_associated_graded_stage_monomial_mem (R := R) I n x⟩ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hx' : (x : R) ∈ I ^ (n + 1) := by
      -- Re-express the next stage as the pure power ideal `I^(n+1)`.
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using hx
    simpa using monomial_mem_denominator_of_mem_pow_succ (R := R) I n hx'

/-- Helper for Proposition 10.59.5: the kernel of the stage-to-owner-piece map is the next
filtration stage. -/
lemma idealAssociatedGradedStageClassLinear_ker_eq
    (I : Ideal R) (n : ℕ) :
    LinearMap.ker (idealAssociatedGradedStageClassLinear (R := R) I n) =
      (RingTheory.Sequence.idealAssociatedGradedStage I R (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage I R n) := by
  ext x
  constructor
  · intro hx
    have hx' :
        (((idealAssociatedGradedStageClassLinear (R := R) I n x :
          idealAssociatedGradedRingGrade I n) : idealAssociatedGradedRing I)) = 0 := by
      exact congrArg
        (fun z : idealAssociatedGradedRingGrade I n ↦ (z : idealAssociatedGradedRing I)) hx
    -- Forgetting the grade subtype reduces kernel membership to vanishing of the stage class.
    change idealAssociatedGradedStageClass (R := R) I n x = 0 at hx'
    exact (associated_graded_stage_class_zero_iff (R := R) I n x).1 hx'
  · intro hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    -- The zero criterion identifies the next stage with the kernel.
    change idealAssociatedGradedStageClass (R := R) I n x = 0
    exact (associated_graded_stage_class_zero_iff (R := R) I n x).2 hx

/-- Helper for Proposition 10.59.5: the owner degree-`n` piece of `gr_I(R)` is canonically
equivalent to the textbook quotient `I^n / I^(n + 1)`. -/
noncomputable def idealAssociatedGradedRingGrade_pieceLinearEquiv
    (I : Ideal R) (n : ℕ) :
    idealAssociatedGradedRingGrade I n ≃ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece I R n :=
  ((idealAssociatedGradedStageClassLinear (R := R) I n).quotKerEquivOfSurjective
      (idealAssociatedGradedStageClassLinear_surjective (R := R) I n)).symm.trans
    (Submodule.quotEquivOfEq _ _
      (idealAssociatedGradedStageClassLinear_ker_eq (R := R) I n))

/-- Helper for Proposition 10.59.5: under the owner-piece/textbook-piece equivalence, the class of
an explicit stage representative is still the obvious quotient class of that same representative.
-/
lemma idealAssociatedGradedRingGrade_pieceLinearEquiv_apply_stageClassLinear
    (I : Ideal R) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R n) :
    idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I n
        (idealAssociatedGradedStageClassLinear (R := R) I n x) =
      (Submodule.Quotient.mk x : RingTheory.Sequence.idealAssociatedGradedPiece I R n) := by
  -- First recover the kernel quotient class of `x`, then rewrite the kernel identification.
  simp [idealAssociatedGradedRingGrade_pieceLinearEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk]

/-- Helper for Proposition 10.59.5: the owner-piece/textbook-piece comparison preserves
multiplication of homogeneous ring classes. -/
lemma idealAssociatedGradedRingGrade_pieceLinearEquiv_mul
    (I : Ideal R) {d e : ℕ}
    (x : idealAssociatedGradedRingGrade I d)
    (y : idealAssociatedGradedRingGrade I e) :
    idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I (d + e)
        ⟨(x : idealAssociatedGradedRing I) * (y : idealAssociatedGradedRing I),
          SetLike.mul_mem_graded x.2 y.2⟩ =
      idealAssociatedGradedPiece_mulLinear (R := R) I d e
        (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I d x)
        (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I e y) := by
  rcases idealAssociatedGradedStageClassLinear_surjective (R := R) I d x with ⟨x₀, rfl⟩
  rcases idealAssociatedGradedStageClassLinear_surjective (R := R) I e y with ⟨y₀, rfl⟩
  have hxy_mem :
      (x₀ : R) * (y₀ : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage I R (d + e) := by
    -- Multiply the chosen stage representatives before descending to the quotient piece.
    exact idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := R) I d e x₀ y₀
  let xy : RingTheory.Sequence.idealAssociatedGradedStage I R (d + e) :=
    ⟨(x₀ : R) * (y₀ : R), hxy_mem⟩
  have hxy :
      (⟨((idealAssociatedGradedStageClassLinear (R := R) I d x₀ :
            idealAssociatedGradedRingGrade I d) : idealAssociatedGradedRing I) *
          ((idealAssociatedGradedStageClassLinear (R := R) I e y₀ :
            idealAssociatedGradedRingGrade I e) : idealAssociatedGradedRing I),
        SetLike.mul_mem_graded
          (idealAssociatedGradedStageClass_mem_grade (R := R) I d x₀)
          (idealAssociatedGradedStageClass_mem_grade (R := R) I e y₀)⟩ :
        idealAssociatedGradedRingGrade I (d + e)) =
        idealAssociatedGradedStageClassLinear (R := R) I (d + e) xy := by
    apply Subtype.ext
    -- The quotient-Rees product of stage classes is the class of the multiplied representative.
    change
      idealAssociatedGradedStageClass (R := R) I d x₀ *
          idealAssociatedGradedStageClass (R := R) I e y₀ =
        idealAssociatedGradedStageClass (R := R) I (d + e) xy
    symm
    exact idealAssociatedGradedStageClass_mul_local (R := R) I x₀ y₀
  rw [hxy]
  rw [idealAssociatedGradedRingGrade_pieceLinearEquiv_apply_stageClassLinear]
  rw [idealAssociatedGradedRingGrade_pieceLinearEquiv_apply_stageClassLinear]
  rw [idealAssociatedGradedRingGrade_pieceLinearEquiv_apply_stageClassLinear]
  -- After reducing to quotient representatives, the comparison is the defining multiplication
  -- formula on the textbook associated graded pieces.
  simpa [xy, idealAssociatedGradedPiece_mulLinear] using
    (idealAssociatedGradedPiece_smulLinear_apply_mk_mk (R := R) (N := R) I d e x₀ y₀).symm

/-- Helper for Proposition 10.59.5: under the owner-piece/textbook-piece comparison, the degree-zero
owner unit class is the textbook class of `1 ∈ R = I^0`. -/
lemma idealAssociatedGradedRingGrade_pieceLinearEquiv_one
    (I : Ideal R) :
    idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I 0
        (⟨1, SetLike.one_mem_graded (idealAssociatedGradedRingGrade (R := R) I)⟩ :
          idealAssociatedGradedRingGrade I 0) =
      (Submodule.Quotient.mk
        (⟨1, by simp [RingTheory.Sequence.idealAssociatedGradedStage]⟩ :
          RingTheory.Sequence.idealAssociatedGradedStage I R 0) :
        RingTheory.Sequence.idealAssociatedGradedPiece I R 0) := by
  -- Realize the owner unit as the degree-zero stage class of `1`, then evaluate the comparison
  -- map on that explicit homogeneous representative.
  have hunit :
      (⟨1, SetLike.one_mem_graded (idealAssociatedGradedRingGrade (R := R) I)⟩ :
        idealAssociatedGradedRingGrade I 0) =
        idealAssociatedGradedStageClassLinear (R := R) I 0
          (⟨1, by simp [RingTheory.Sequence.idealAssociatedGradedStage]⟩ :
            RingTheory.Sequence.idealAssociatedGradedStage I R 0) := by
    apply Subtype.ext
    change idealAssociatedGradedStageClass (R := R) I 0
        ⟨1, by simp [RingTheory.Sequence.idealAssociatedGradedStage]⟩ = 1
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
          (⟨Polynomial.monomial 0 (1 : R),
            ideal_associated_graded_stage_monomial_mem (R := R) I 0
              ⟨1, by simp [RingTheory.Sequence.idealAssociatedGradedStage]⟩⟩ :
            reesAlgebra I) =
        1
    congr 1
  rw [hunit]
  exact idealAssociatedGradedRingGrade_pieceLinearEquiv_apply_stageClassLinear (R := R) I 0
    (⟨1, by simp [RingTheory.Sequence.idealAssociatedGradedStage]⟩ :
      RingTheory.Sequence.idealAssociatedGradedStage I R 0)

/-- Helper for Proposition 10.59.5: each homogeneous owner ring piece carries its inherited
additive commutative monoid structure explicitly, so graded direct-sum instance search stays on
the subtype route instead of unfolding ambient coercions. -/
instance idealAssociatedGradedRingGrade_addCommMonoid
    (I : Ideal R) (n : ℕ) :
    AddCommMonoid ↥(idealAssociatedGradedRingGrade I n) := by
  infer_instance

/-- Helper for Proposition 10.59.5: each homogeneous owner ring piece also carries its inherited
additive commutative group structure explicitly for the direct-sum ring/module instances. -/
instance idealAssociatedGradedRingGrade_addCommGroup
    (I : Ideal R) (n : ℕ) :
    AddCommGroup ↥(idealAssociatedGradedRingGrade I n) := by
  infer_instance

/-- Helper for Proposition 10.59.5: each textbook associated graded quotient piece carries its
inherited additive commutative group structure explicitly for the graded direct-sum action. -/
instance idealAssociatedGradedPiece_addCommGroup
    (I : Ideal R) (n : ℕ) :
    AddCommGroup (RingTheory.Sequence.idealAssociatedGradedPiece I M n) := by
  infer_instance

/-- Helper for Proposition 10.59.5: package the additive structures on the homogeneous owner ring
pieces as a family instance so the graded direct-sum action can use them without expensive search.
-/
instance idealAssociatedGradedRingGrade_familyAddCommMonoid
    (I : Ideal R) :
    ∀ d : ℕ, AddCommMonoid ↥(idealAssociatedGradedRingGrade I d) :=
  fun d ↦ idealAssociatedGradedRingGrade_addCommMonoid (R := R) I d

/-- Helper for Proposition 10.59.5: package the additive group structures on the homogeneous owner
ring pieces as a family instance, matching the direct-sum ring/module searches used later. -/
instance idealAssociatedGradedRingGrade_familyAddCommGroup
    (I : Ideal R) :
    ∀ d : ℕ, AddCommGroup ↥(idealAssociatedGradedRingGrade I d) :=
  fun d ↦ idealAssociatedGradedRingGrade_addCommGroup (R := R) I d

/-- Helper for Proposition 10.59.5: package the additive structures on the textbook associated
graded quotient pieces as a family instance for the graded direct-sum action. -/
instance idealAssociatedGradedPiece_familyAddCommGroup
    (I : Ideal R) :
    ∀ n : ℕ, AddCommGroup (RingTheory.Sequence.idealAssociatedGradedPiece I M n) :=
  fun n ↦ idealAssociatedGradedPiece_addCommGroup (R := R) (M := M) I n

/-- Helper for Proposition 10.59.5: give each owner ring piece the trivial topological structure
explicitly so graded direct-sum elaboration does not search for unrelated topology instances. -/
instance idealAssociatedGradedRingGrade_familyTopologicalSpace
    (I : Ideal R) :
    ∀ d : ℕ, TopologicalSpace ↥(idealAssociatedGradedRingGrade I d) :=
  fun _ ↦ ⊥

/-- Helper for Proposition 10.59.5: package the internal grading on `gr_I(R)` as a graded ring so
the later graded-module transport does not rediscover this structure through repeated search. -/
instance idealAssociatedGradedRingGrade_gradedRing
    (I : Ideal R) :
    GradedRing (idealAssociatedGradedRingGrade (R := R) I) := by
  infer_instance

/-- Helper for Proposition 10.59.5: every ring element lies in the zeroth stage of the
`I`-adic filtration. -/
lemma idealAssociatedGradedStage_zero_mem
    (I : Ideal R) (r : R) :
    r ∈ RingTheory.Sequence.idealAssociatedGradedStage I R 0 := by
  -- The zeroth stage is `I^0 R = R`, so every ring element is admitted.
  simp [RingTheory.Sequence.idealAssociatedGradedStage]

/-- Helper for Proposition 10.59.5: the degree-zero stage class is the same as the ambient
algebra-map image in the associated graded ring. -/
lemma idealAssociatedGradedStageClass_zero_eq_algebraMap
    (I : Ideal R) (r : R) :
    idealAssociatedGradedStageClass (R := R) I 0
        ⟨r, idealAssociatedGradedStage_zero_mem (R := R) I r⟩ =
      algebraMap R (idealAssociatedGradedRing I) r := by
  -- Both sides are the quotient class of the same constant Rees polynomial.
  rfl

/-- Helper for Proposition 10.59.5: when a homogeneous owner ring class comes from an explicit
stage representative, the translated action on a textbook associated graded piece is computed by
ordinary multiplication of representatives. -/
lemma idealAssociatedGradedPiece_owner_action_apply_stageClass
    (I : Ideal R) (d n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage I R d)
    (y : RingTheory.Sequence.idealAssociatedGradedStage I M n) :
    idealAssociatedGradedPiece_smulLinear (R := R) (N := M) I d n
        (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I d
          (idealAssociatedGradedStageClassLinear (R := R) I d x))
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨(x : R) • (y : M),
          idealAssociatedGradedPiece_smul_mem_stage (R := R) (N := M) I d n x y⟩ := by
  -- Translate the owner homogeneous class to the textbook quotient piece, then evaluate the
  -- descended quotient action on the chosen representative.
  rw [idealAssociatedGradedRingGrade_pieceLinearEquiv_apply_stageClassLinear]
  exact idealAssociatedGradedPiece_smulLinear_apply_mk_mk (R := R) (N := M) I d n x y

/-- Helper for Proposition 10.59.5: after translating owner ring classes to textbook quotient
pieces, the homogeneous action on `gr_I(M)` is associative. -/
lemma idealAssociatedGradedPiece_owner_action_assoc
    (I : Ideal R) (d e n : ℕ)
    (x : idealAssociatedGradedRingGrade I d)
    (y : idealAssociatedGradedRingGrade I e)
    (m : RingTheory.Sequence.idealAssociatedGradedPiece I M n) :
    Nat.add_assoc d e n ▸
      idealAssociatedGradedPiece_smulLinear (R := R) (N := M) I d (e + n)
        (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I d x)
        (idealAssociatedGradedPiece_smulLinear (R := R) (N := M) I e n
          (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I e y) m) =
      idealAssociatedGradedPiece_smulLinear (R := R) (N := M) I (d + e) n
        (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I (d + e)
          ⟨(x : idealAssociatedGradedRing I) * (y : idealAssociatedGradedRing I),
            SetLike.mul_mem_graded x.2 y.2⟩)
        m := by
  -- This is exactly the textbook quotient-piece associativity, after rewriting the product of the
  -- two owner classes through the owner-piece/textbook-piece comparison.
  rw [idealAssociatedGradedRingGrade_pieceLinearEquiv_mul (R := R) I x y]
  exact idealAssociatedGradedPiece_smulLinear_assoc (R := R) I d e n
    (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I d x)
    (idealAssociatedGradedRingGrade_pieceLinearEquiv (R := R) I e y)
    m

end Ideal

end
