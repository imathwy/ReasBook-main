import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic
import StacksProject_2024.Chap22.Definition_22_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]

namespace DifferentialGradedModule

variable {A : CochainDGAlgebra R}

/-- Reassociate the target degree of the shifted differential. -/
private theorem shift_d_index (n k : ℤ) :
    n + k + 1 = (n + 1) + k := by
  omega

private theorem shift_smul_index (p i k : ℤ) :
    (p + k) + i = (p + i) + k := by
  omega

private theorem negOnePow_sq (k : ℤ) :
    ((k.negOnePow : R) * (k.negOnePow : R)) = 1 := by
  -- Proof comment: `k.negOnePow` is always `1` or `-1`, so its square is `1`.
  rcases Int.even_or_odd k with hEven | hOdd
  · simp [Int.negOnePow_even, hEven]
  · simp [Int.negOnePow_odd, hOdd]

private theorem negOnePow_add_cast (i j : ℤ) :
    ((i + j).negOnePow : R) = (j.negOnePow : R) * (i.negOnePow : R) := by
  -- Proof comment: first split the integer sign, then cast the product into `R`.
  rw [Int.negOnePow_add]
  simpa [Int.cast_mul, mul_comm, mul_left_comm, mul_assoc]

private theorem negOnePow_shift_cancel (p k : ℤ) :
    (k.negOnePow : R) * ((p + k).negOnePow : R) = (p.negOnePow : R) := by
  -- Proof comment: rewrite `(-1)^(p + k)` as `(-1)^k * (-1)^p` and cancel the extra square.
  rw [negOnePow_add_cast]
  rw [← mul_assoc, negOnePow_sq, one_mul]

/-- Helper for Definition 22.4.3: two transports to the same graded piece agree. -/
private theorem gradedPieceCast_eq {M : ℤ → ModuleCat.{v} R} {i j : ℤ}
    (h h' : i = j) (x : ((M i) : Type _)) :
    cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) x =
      cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h') x := by
  -- Proof comment: after substituting both equality proofs, the two casts are definitionally
  -- identical.
  cases h
  cases h'
  rfl

/-- Helper for Definition 22.4.3: successive transports collapse to the composite transport. -/
private theorem gradedPieceCast_trans_eq {M : ℤ → ModuleCat.{v} R} {i j k : ℤ}
    (h : i = j) (h' : j = k) (x : ((M i) : Type _)) :
    cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h')
      (cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) x) =
      cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) (h.trans h')) x := by
  -- Proof comment: transport composition is definitional once both equalities are reduced.
  cases h
  cases h'
  rfl

/-- Helper for Definition 22.4.3: transport commutes with scalar multiplication on graded pieces. -/
private theorem gradedPieceCast_smul_eq {M : ℤ → ModuleCat.{v} R} {i j : ℤ}
    (h : i = j) (r : R) (x : ((M i) : Type _)) :
    cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) x := by
  -- Proof comment: the transported module structure is definitionally the original one.
  cases h
  rfl

/-- Helper for Definition 22.4.3: transport commutes with addition on graded pieces. -/
private theorem gradedPieceCast_add_eq {M : ℤ → ModuleCat.{v} R} {i j : ℤ}
    (h : i = j) (x y : ((M i) : Type _)) :
    cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) (x + y) =
      cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) x +
        cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) y := by
  -- Proof comment: additive transport is also definitional after eliminating the index equality.
  cases h
  rfl

/-- Helper for Definition 22.4.3: transport sends the zero element to zero. -/
private theorem gradedPieceCast_zero_eq {M : ℤ → ModuleCat.{v} R} {i j : ℤ}
    (h : i = j) :
    cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) (0 : ((M i) : Type _)) = 0 := by
  -- Proof comment: after eliminating the index equality, this is the identity `0 = 0`.
  cases h
  rfl

/-- Helper for Definition 22.4.3: evaluating a transported linear map transports the value. -/
private theorem linearMapCast_apply_eq
    {S : ModuleCat.{w} R} {M : ℤ → ModuleCat.{v} R} {i j : ℤ}
    (h : i = j) (f : (S : Type _) →ₗ[R] (M i : Type _)) (x : S) :
    cast (congrArg (fun n : ℤ ↦ (((S : Type _) →ₗ[R] (M n : Type _)) : Type _)) h) f x =
      cast (congrArg (fun n : ℤ ↦ ((M n) : Type _)) h) (f x) := by
  -- Proof comment: after reducing the equality proof, both sides are the same evaluation.
  cases h
  rfl

/-- Helper for Definition 22.4.3: the differential commutes with transport in the degree index. -/
private theorem d_apply_cast_eq (M : DifferentialGradedModule A) {i j : ℤ}
    (h : i = j) (x : ((M.X i) : Type _)) :
    cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _))
      (congrArg (fun n : ℤ ↦ n + 1) h)) (M.d i x) =
      M.d j (cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) h) x) := by
  -- Proof comment: the degree-shifted differential is definitional after substituting the index.
  cases h
  rfl

/-- Helper for Definition 22.4.3: a morphism commutes with transport in the degree index. -/
private theorem hom_apply_cast_eq {M N : DifferentialGradedModule A} (f : M ⟶ N) {i j : ℤ}
    (h : i = j) (x : ((M.X i) : Type _)) :
    cast (congrArg (fun n : ℤ ↦ ((N.X n) : Type _)) h) (f.hom i x) =
      f.hom j (cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) h) x) := by
  -- Proof comment: degree-preserving components of a morphism transport definitionally.
  cases h
  rfl

/-- Helper for Definition 22.4.3: the right action commutes with transport in the source degree. -/
private theorem smul_apply_cast_eq (M : DifferentialGradedModule A) {p p' i : ℤ}
    (h : p = p') (x : ((M.X p) : Type _)) (a : A.X i) :
    cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _))
      (congrArg (fun n : ℤ ↦ n + i) h)) (M.smul p i x a) =
      M.smul p' i (cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) h) x) a := by
  -- Proof comment: reindexing the source degree of the action only transports its output degree.
  cases h
  rfl

/-- Helper for Definition 22.4.3: the twice-shifted differential lands in the expected degree. -/
private theorem shift_d_index_step (n k : ℤ) :
    n + k + 1 + 1 = (n + 1 + k) + 1 := by
  -- Proof comment: this is the first transport needed before the final shift reindexing.
  omega

/-- Helper for Definition 22.4.3: the twice-shifted differential lands in the expected degree. -/
private theorem shift_d_index_twice (n k : ℤ) :
    n + k + 1 + 1 = (n + 1 + 1) + k := by
  -- Proof comment: both sides are the same integer after associativity rebracketing.
  omega

/-- Helper for Definition 22.4.3: the shifted differential still squares to zero. -/
private theorem shiftDsq (M : DifferentialGradedModule A) (k n : ℤ) (x : M.X (n + k)) :
    castLinearMap
      (congrArg M.X (shift_d_index (n + 1) k))
      ((k.negOnePow : R) • M.d (n + 1 + k))
      (castLinearMap
        (congrArg M.X (shift_d_index n k))
        ((k.negOnePow : R) • M.d (n + k)) x) = 0 := by
  -- Proof comment: remove the two transport layers, then only the square of `(-1)^k` remains.
  rw [castLinearMap_apply, LinearMap.smul_apply, castLinearMap_apply, LinearMap.smul_apply]
  rw [gradedPieceCast_smul_eq]
  have hInnerCast :
      cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index n k))
          ((k.negOnePow : R) • M.d (n + k) x) =
        (k.negOnePow : R) •
          cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index n k))
            (M.d (n + k) x) := by
    -- Proof comment: transport across the first reindexing preserves scalar multiplication.
    simpa using gradedPieceCast_smul_eq
      (M := M.X)
      (h := shift_d_index n k)
      (r := (k.negOnePow : R))
      (x := M.d (n + k) x)
  rw [hInnerCast]
  rw [LinearMap.map_smul]
  rw [gradedPieceCast_smul_eq]
  rw [smul_smul, negOnePow_sq, one_smul]
  have hd :
      cast
        (congrArg (fun m : ℤ ↦ ((M.X (m + 1)) : Type _)) (shift_d_index n k))
        (M.d (n + k + 1) (M.d (n + k) x)) =
      M.d (n + 1 + k)
        (cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index n k))
          (M.d (n + k) x)) := by
    -- Proof comment: this is the stable transport formula for `d` across the shifted index.
    simpa [add_assoc] using
      d_apply_cast_eq (M := M) (h := shift_d_index n k) (x := M.d (n + k) x)
  rw [← hd]
  have hTrans :
      cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index (n + 1) k))
          (cast
            (congrArg (fun m : ℤ ↦ ((M.X (m + 1)) : Type _)) (shift_d_index n k))
            (M.d (n + k + 1) (M.d (n + k) x))) =
        cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index_twice n k))
          (M.d (n + k + 1) (M.d (n + k) x)) := by
    -- Proof comment: collapse the two successive codomain transports to the direct reindexing.
    have hStep :
        cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index (n + 1) k))
            (cast
              (congrArg (fun m : ℤ ↦ ((M.X (m + 1)) : Type _)) (shift_d_index n k))
              (M.d (n + k + 1) (M.d (n + k) x))) =
          cast
            (congrArg (fun m : ℤ ↦ ((M.X m) : Type _))
              ((congrArg (fun m : ℤ ↦ m + 1) (shift_d_index n k)).trans
                (shift_d_index (n + 1) k)))
            (M.d (n + k + 1) (M.d (n + k) x)) := by
      simpa using gradedPieceCast_trans_eq
        (M := M.X)
        (h := congrArg (fun m : ℤ ↦ m + 1) (shift_d_index n k))
        (h' := shift_d_index (n + 1) k)
        (x := M.d (n + k + 1) (M.d (n + k) x))
    simpa using gradedPieceCast_eq
      (M := M.X)
      (h := (congrArg (fun m : ℤ ↦ m + 1) (shift_d_index n k)).trans (shift_d_index (n + 1) k))
      (h' := shift_d_index_twice n k)
      (x := M.d (n + k + 1) (M.d (n + k) x))
  -- Proof comment: transport the original square-zero identity to the shifted target degree.
  have hZero :
      cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index_twice n k))
          (M.d (n + k + 1) (M.d (n + k) x)) =
        cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index_twice n k))
          (0 : M.X (n + k + 1 + 1)) := by
    exact congrArg
      (fun y : M.X (n + k + 1 + 1) ↦
        cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index_twice n k)) y)
      (M.d_sq (n + k) x)
  have hZero' :
      cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index_twice n k))
          (M.d (n + k + 1) (M.d (n + k) x)) =
        (0 : M.X ((n + 1 + 1) + k)) := by
    calc
      cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index_twice n k))
          (M.d (n + k + 1) (M.d (n + k) x)) =
        cast (congrArg (fun m : ℤ ↦ ((M.X m) : Type _)) (shift_d_index_twice n k))
          (0 : M.X (n + k + 1 + 1)) := hZero
      _ = 0 := by
        simpa using gradedPieceCast_zero_eq (M := M.X) (h := shift_d_index_twice n k)
  exact hTrans.trans hZero'
  all_goals omega

/-- Helper for Definition 22.4.3: the shifted right action still satisfies the unit law. -/
private theorem shiftSmulOne (M : DifferentialGradedModule A) (k : ℤ)
    (r : R) (p : ℤ) (x : M.X (p + k)) :
    castLinearMap
      (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X 0 →ₗ[R] M.X n)) (shift_smul_index p 0 k))
      (M.smul (p + k) 0) x (r • A.one) =
      cast (rightDGModuleZeroTargetEq (M := fun n : ℤ ↦ M.X (n + k)) p) (r • x) := by
  -- Proof comment: the shifted action is the original action in degree `p + k`, with only the
  -- target cast changed by reindexing.
  -- Route correction: evaluate the transported action first, then simplify the resulting cast.
  rw [castLinearMap_apply]
  have hApply :
      (cast
        (congrArg (fun n : ℤ ↦ (((A.X 0 : Type _) →ₗ[R] (M.X n : Type _)) : Type _))
          (shift_smul_index p 0 k))
        ((M.smul (p + k) 0) x)) (r • A.one) =
      cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) (shift_smul_index p 0 k))
        (M.smul (p + k) 0 x (r • A.one)) := by
    simpa using linearMapCast_apply_eq
      (h := shift_smul_index p 0 k)
      (f := (M.smul (p + k) 0) x)
      (x := r • A.one)
  rw [hApply]
  rw [M.smul_one r (p + k) x]
  simp

/-- Helper for Definition 22.4.3: the shifted right action still respects multiplication in `A`.
-/
private theorem shiftSmulMul (M : DifferentialGradedModule A) (k p i j : ℤ)
    (x : M.X (p + k)) (a : A.X i) (b : A.X j) :
    castLinearMap
      (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X (i + j) →ₗ[R] M.X n))
        (shift_smul_index p (i + j) k))
      (M.smul (p + k) (i + j)) x (A.mul i j a b) =
      cast (rightDGModuleMulTargetEq (M := fun n : ℤ ↦ M.X (n + k)) p i j)
        (castLinearMap
          (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X j →ₗ[R] M.X n))
            (shift_smul_index (p + i) j k))
          (M.smul ((p + i) + k) j)
          (castLinearMap
            (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n))
              (shift_smul_index p i k))
            (M.smul (p + k) i) x a) b) := by
  -- Proof comment: after normalizing the three reindexings, this is exactly the unshifted
  -- associativity axiom at degree `p + k`.
  -- Route correction: rewrite every transported action to a cast on values before comparing
  -- the two codomain transports.
  rw [castLinearMap_apply]
  have hLeft :
      (cast
        (congrArg (fun n : ℤ ↦ (((A.X (i + j) : Type _) →ₗ[R] (M.X n : Type _)) : Type _))
          (shift_smul_index p (i + j) k))
        ((M.smul (p + k) (i + j)) x)) (((A.mul i j) a) b) =
      cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) (shift_smul_index p (i + j) k))
        (M.smul (p + k) (i + j) x (A.mul i j a b)) := by
    simpa using linearMapCast_apply_eq
      (h := shift_smul_index p (i + j) k)
      (f := (M.smul (p + k) (i + j)) x)
      (x := A.mul i j a b)
  rw [hLeft]
  rw [M.smul_mul (p + k) i j x a b]
  rw [castLinearMap_apply]
  rw [castLinearMap_apply]
  have hInner :
      (cast
        (congrArg (fun n : ℤ ↦ (((A.X i : Type _) →ₗ[R] (M.X n : Type _)) : Type _))
          (shift_smul_index p i k))
        ((M.smul (p + k) i) x)) a =
      cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) (shift_smul_index p i k))
        (M.smul (p + k) i x a) := by
    simpa using linearMapCast_apply_eq
      (h := shift_smul_index p i k)
      (f := (M.smul (p + k) i) x)
      (x := a)
  rw [hInner]
  have hOuter :
      (cast
        (congrArg (fun n : ℤ ↦ (((A.X j : Type _) →ₗ[R] (M.X n : Type _)) : Type _))
          (shift_smul_index (p + i) j k))
        ((M.smul (p + i + k) j)
          (cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) (shift_smul_index p i k))
            (M.smul (p + k) i x a)))) b =
      cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) (shift_smul_index (p + i) j k))
        (M.smul (p + i + k) j
          (cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) (shift_smul_index p i k))
            (M.smul (p + k) i x a)) b) := by
    simpa using linearMapCast_apply_eq
      (h := shift_smul_index (p + i) j k)
      (f := (M.smul (p + i + k) j)
        (cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) (shift_smul_index p i k))
          (M.smul (p + k) i x a)))
      (x := b)
  rw [hOuter]
  rw [← smul_apply_cast_eq
    (M := M)
    (h := shift_smul_index p i k)
    (x := M.smul (p + k) i x a)
    (a := b)]
  simpa [rightDGModuleMulTargetEq] using gradedPieceCast_trans_eq
    (M := M.X)
    (h := congrArg (fun m : ℤ ↦ m + j) (shift_smul_index p i k))
    (h' := shift_smul_index (p + i) j k)
    (x := M.smul ((p + k) + i) j (M.smul (p + k) i x a) b)

/-- Helper for Definition 22.4.3: the shifted differential satisfies the graded Leibniz rule. -/
private theorem shiftCommD (M : DifferentialGradedModule A) (k p i : ℤ)
    (x : M.X (p + k)) (a : A.X i) :
    castLinearMap
      (congrArg M.X (shift_d_index (p + i) k))
      ((k.negOnePow : R) • M.d (p + i + k))
      (castLinearMap
        (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n))
          (shift_smul_index p i k))
        (M.smul (p + k) i) x a) =
      cast (rightDGModuleDLeftTargetEq (M := fun n : ℤ ↦ M.X (n + k)) p i)
        (castLinearMap
          (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n))
            (shift_smul_index (p + 1) i k))
          (M.smul (p + 1 + k) i)
          (castLinearMap
            (congrArg M.X (shift_d_index p k))
            ((k.negOnePow : R) • M.d (p + k)) x) a) +
        (p.negOnePow : R) •
          cast (rightDGModuleDRightTargetEq (M := fun n : ℤ ↦ M.X (n + k)) p i)
            (castLinearMap
              (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X (i + 1) →ₗ[R] M.X n))
                (shift_smul_index p (i + 1) k))
              (M.smul (p + k) (i + 1)) x (A.d i a)) := by
  -- Proof comment: strip the shift transports, rewrite by the original Leibniz rule, and then
  -- move the extra factor `(-1)^k` through the two branches.
  -- Route correction: transporting `M.comm_d (p + k) i x a` to the shifted target degree is the
  -- right skeleton, but the proof still needs explicit branch-normalization lemmas that identify
  -- the transported left and right Leibniz summands with the shifted action branches.
  -- TODO: prove separate left- and right-branch transport lemmas for the target equality
  -- `(p + k) + i + 1 = (p + i + 1) + k`, then assemble them with `M.comm_d (p + k) i x a` and
  -- `negOnePow_shift_cancel p k`.
  sorry

/-- Helper for Definition 22.4.3: a shifted morphism still commutes with the differential. -/
private theorem shiftMapCommD {M N : DifferentialGradedModule A} (f : M ⟶ N) (k n : ℤ)
    (x : M.X (n + k)) :
    f.hom (n + 1 + k)
      (castLinearMap
        (congrArg M.X (shift_d_index n k))
        ((k.negOnePow : R) • M.d (n + k)) x) =
      castLinearMap
        (congrArg N.X (shift_d_index n k))
        ((k.negOnePow : R) • N.d (n + k))
        (f.hom (n + k) x) := by
  -- Proof comment: after removing the shared reindexing cast, both sides are `(-1)^k` times the
  -- original compatibility with `d`.
  -- Route correction: move the transport across `f.hom` instead of destructing the degree
  -- equality.
  rw [castLinearMap_apply]
  rw [LinearMap.smul_apply]
  rw [← hom_apply_cast_eq
    (f := f)
    (h := shift_d_index n k)
    (x := (k.negOnePow : R) • M.d (n + k) x)]
  rw [LinearMap.map_smul]
  rw [f.comm_d (n + k) x]
  rw [castLinearMap_apply]
  rw [LinearMap.smul_apply]

/-- Helper for Definition 22.4.3: a shifted morphism still commutes with the right action. -/
private theorem shiftMapCommSmul {M N : DifferentialGradedModule A} (f : M ⟶ N)
    (k p i : ℤ) (x : M.X (p + k)) (a : A.X i) :
    f.hom (p + i + k)
      (castLinearMap
        (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n)) (shift_smul_index p i k))
        (M.smul (p + k) i) x a) =
      castLinearMap
        (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] N.X n)) (shift_smul_index p i k))
        (N.smul (p + k) i)
        (f.hom (p + k) x) a := by
  -- Proof comment: the shifted action is degreewise unchanged, so after reindexing this is the
  -- original right-linearity axiom.
  -- Route correction: rewrite both transported actions to casts on elements and use `f.comm_smul`.
  rw [castLinearMap_apply]
  have hLeft :
      (cast
        (congrArg (fun n : ℤ ↦ (((A.X i : Type _) →ₗ[R] (M.X n : Type _)) : Type _))
          (shift_smul_index p i k))
        ((M.smul (p + k) i) x)) a =
      cast (congrArg (fun n : ℤ ↦ ((M.X n) : Type _)) (shift_smul_index p i k))
        (M.smul (p + k) i x a) := by
    simpa using linearMapCast_apply_eq
      (h := shift_smul_index p i k)
      (f := (M.smul (p + k) i) x)
      (x := a)
  rw [hLeft]
  rw [← hom_apply_cast_eq (f := f) (h := shift_smul_index p i k)]
  rw [f.comm_smul (p + k) i x a]
  rw [castLinearMap_apply]
  have hRight :
      (cast
        (congrArg (fun n : ℤ ↦ (((A.X i : Type _) →ₗ[R] (N.X n : Type _)) : Type _))
          (shift_smul_index p i k))
        ((N.smul (p + k) i) (f.hom (p + k) x))) a =
      cast (congrArg (fun n : ℤ ↦ ((N.X n) : Type _)) (shift_smul_index p i k))
        (N.smul (p + k) i (f.hom (p + k) x) a) := by
    simpa using linearMapCast_apply_eq
      (h := shift_smul_index p i k)
      (f := (N.smul (p + k) i) (f.hom (p + k) x))
      (x := a)
  rw [hRight]

/-- The shift of a right differential graded `A`-module by an integer `k`. -/
def shift (M : DifferentialGradedModule A) (k : ℤ) : DifferentialGradedModule A where
  X n := M.X (n + k)
  d n :=
    castLinearMap (congrArg M.X (shift_d_index n k)) ((k.negOnePow : R) • M.d (n + k))
  smul p i :=
    castLinearMap
      (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n)) (shift_smul_index p i k))
      (M.smul (p + k) i)
  d_sq := shiftDsq M k
  smul_one := shiftSmulOne M k
  smul_mul := shiftSmulMul M k
  comm_d := shiftCommD M k

/-- Shift a morphism of right differential graded modules degreewise. -/
def shiftMap {M N : DifferentialGradedModule A} (f : M ⟶ N) (k : ℤ) :
    shift M k ⟶ shift N k where
  hom n := f.hom (n + k)
  comm_d := shiftMapCommD f k
  comm_smul := shiftMapCommSmul f k

@[inherit_doc shift]
scoped[DifferentialGradedModule] notation:max M:max "[" k:max "]" => shift M k

open scoped DifferentialGradedModule

/-- Definition 22.4.3: right differential graded modules admit the canonical shift object notation
`M[k]`; its degree-`n` term is `M^(n + k)`. -/
@[stacks 09JL, simp] theorem shift_X (M : DifferentialGradedModule A) (k n : ℤ) :
    (M[k]).X n = M.X (n + k) :=
  rfl

/-- Companion for Definition 22.4.3: the shifted differential is `(-1)^k d_M` after reindexing. -/
@[simp] theorem shift_d (M : DifferentialGradedModule A) (k n : ℤ) :
    (M[k]).d n =
      castLinearMap
        (congrArg M.X (shift_d_index n k))
        ((k.negOnePow : R) • M.d (n + k)) :=
  rfl

/-- The shifted right action is the original action after reindexing the target degree. -/
@[simp] theorem shift_smul (M : DifferentialGradedModule A) (k p i : ℤ) :
    (M[k]).smul p i =
      castLinearMap
        (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n)) (shift_smul_index p i k))
        (M.smul (p + k) i) :=
  rfl

/-- The shifted morphism is the original degreewise linear map after reindexing. -/
@[simp] theorem shift_map_hom {M N : DifferentialGradedModule A} (f : M ⟶ N) (k n : ℤ) :
    (shiftMap f k).hom n = f.hom (n + k) :=
  rfl

/-- The shifted morphism acts by the original degreewise map after reindexing. -/
@[simp] theorem shift_map_apply {M N : DifferentialGradedModule A} (f : M ⟶ N) (k n : ℤ)
    (x : (M[k]).X n) :
    (shiftMap f k).hom n x = f.hom (n + k) x :=
  rfl

/-- Shifting preserves identity morphisms. -/
@[simp] theorem shiftMap_id (M : DifferentialGradedModule A) (k : ℤ) :
    shiftMap (𝟙 M) k = 𝟙 (M[k]) := by
  apply hom_ext
  intro n x
  rfl

/-- Shifting preserves composition of morphisms. -/
@[simp] theorem shiftMap_comp {L M N : DifferentialGradedModule A} (f : L ⟶ M) (g : M ⟶ N)
    (k : ℤ) :
    shiftMap (f ≫ g) k = shiftMap f k ≫ shiftMap g k := by
  apply hom_ext
  intro n x
  rfl

end DifferentialGradedModule

end
