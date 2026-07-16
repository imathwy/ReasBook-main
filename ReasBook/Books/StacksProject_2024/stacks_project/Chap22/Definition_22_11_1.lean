import StacksProject_2024.stacks_project.Chap22.Definition_22_3_1

universe u

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R

namespace CochainDGAlgebra

/-- The Koszul sign used in the opposite differential graded algebra. -/
def oppositeSign (R : Type u) [CommRing R] (i j : ℤ) : R :=
  ((i * j).negOnePow : R)

@[simp] theorem oppositeSign_zero_left (j : ℤ) :
    oppositeSign R 0 j = (1 : R) := by
  simp [oppositeSign]

@[simp] theorem oppositeSign_zero_right (i : ℤ) :
    oppositeSign R i 0 = (1 : R) := by
  simp [oppositeSign]

@[simp] theorem oppositeSign_comm (i j : ℤ) :
    oppositeSign R i j = oppositeSign R j i := by
  simp [oppositeSign, mul_comm]

@[simp] theorem oppositeSign_mul_self (i j : ℤ) :
    oppositeSign R i j * oppositeSign R i j = (1 : R) := by
  rcases Int.even_or_odd (i * j) with hEven | hOdd
  · rw [show oppositeSign R i j = (1 : R) by
        simp [oppositeSign, Int.negOnePow_even, hEven]]
    norm_num
  · rw [show oppositeSign R i j = (-1 : R) by
        simp [oppositeSign, Int.negOnePow_odd, hOdd]]
    ring

@[simp] theorem oppositeSign_smul_oppositeSign {M : Type u} [AddCommMonoid M] [Module R M]
    (i j : ℤ) (x : M) :
    oppositeSign R i j • (oppositeSign R i j • x) = x := by
  rw [smul_smul, oppositeSign_mul_self]
  simp

theorem oppositeSign_add_right (p q r : ℤ) :
    oppositeSign R p (q + r) = oppositeSign R p q * oppositeSign R p r := by
  calc
    oppositeSign R p (q + r) = (((p * q + p * r).negOnePow : ℤ) : R) := by
      simp [oppositeSign]
      congr 1
      ring_nf
    _ = oppositeSign R p q * oppositeSign R p r := by
      rw [Int.negOnePow_add]
      change ((↑(((p * q).negOnePow * (p * r).negOnePow : ℤ)) : R)) =
        oppositeSign R p q * oppositeSign R p r
      simp [oppositeSign, Int.cast_mul]

theorem oppositeSign_add_left (p q r : ℤ) :
    oppositeSign R (p + q) r = oppositeSign R p r * oppositeSign R q r := by
  calc
    oppositeSign R (p + q) r = (((p * r + q * r).negOnePow : ℤ) : R) := by
      simp [oppositeSign]
      congr 1
      ring_nf
    _ = oppositeSign R p r * oppositeSign R q r := by
      rw [Int.negOnePow_add]
      change ((↑(((p * r).negOnePow * (q * r).negOnePow : ℤ)) : R)) =
        oppositeSign R p r * oppositeSign R q r
      simp [oppositeSign, Int.cast_mul]

theorem oppositeSign_add_one_left (i j : ℤ) :
    oppositeSign R (i + 1) j = oppositeSign R i j * (j.negOnePow : R) := by
  rw [oppositeSign_add_left]
  simp [oppositeSign]

theorem oppositeSign_add_one_right (i j : ℤ) :
    oppositeSign R i (j + 1) = oppositeSign R i j * (i.negOnePow : R) := by
  rw [oppositeSign_add_right]
  simp [oppositeSign]

theorem oppositeSign_assoc (i j k : ℤ) :
    oppositeSign R (i + j) k * oppositeSign R i j =
      oppositeSign R i (j + k) * oppositeSign R j k := by
  rw [oppositeSign_add_left, oppositeSign_add_right]
  ring

private theorem x_cast_add (A : DGA) {i i' : ℤ} (h : i = i') (x y : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) (x + y) =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) x +
        cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) y := by
  cases h
  rfl

private theorem x_cast_smul (A : DGA) {i i' : ℤ} (h : i = i') (r : R) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) x := by
  cases h
  rfl

/-- Helper for Definition 22.11.1: transport across degree equalities commutes with integer
scalar multiplication on homogeneous pieces. -/
private theorem x_cast_zsmul (A : DGA) {i i' : ℤ} (h : i = i') (z : ℤ) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) (z • x) =
      z • cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) x := by
  -- Rewrite the integer scalar through the ambient `R`-module structure before transporting.
  rw [← Int.cast_smul_eq_zsmul R z x]
  rw [x_cast_smul A h (z : R) x]
  simpa using Int.cast_smul_eq_zsmul R z
    (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) x)

private theorem x_cast_add_comm_cancel (A : DGA) (i j : ℤ) (x : A.X (i + j)) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm j i))
      (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm i j)) x) = x := by
  rw [cast_cast]
  simp

private theorem x_cast_congr (A : DGA) {i j : ℤ} (h h' : i = j) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h) x =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h') x := by
  cases h
  cases h'
  rfl

private theorem x_cast_cast_smul (A : DGA) {i j k : ℤ} (h₁ : i = j) (h₂ : j = k)
    (r : R) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h₂)
      (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h₁) (r • x)) =
      r • cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (h₁.trans h₂)) x := by
  cases h₁
  cases h₂
  rfl

private theorem x_cast_cast_cast_cast_smul (A : DGA) {i j k l m : ℤ}
    (h₁ : i = j) (h₂ : j = k) (h₃ : k = l) (h₄ : l = m) (r : R) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h₄)
      (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h₃)
        (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h₂)
          (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) h₁) (r • x)))) =
      r • cast
        (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (((h₁.trans h₂).trans h₃).trans h₄)) x := by
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  rfl

private theorem mul_cast_right (A : DGA) (i : ℤ) {j j' : ℤ} (h : j = j')
    (a : A.toCochainComplex.X i) (b : A.toCochainComplex.X j) :
    cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X (i + n) : Type u)) h) (A.mul i j a b) =
      A.mul i j' a (cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) h) b) := by
  cases h
  rfl

private theorem mul_cast_left (A : DGA) {i i' : ℤ} (h : i = i') (j : ℤ)
    (a : A.toCochainComplex.X i) (b : A.toCochainComplex.X j) :
    cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X (n + j) : Type u)) h) (A.mul i j a b) =
      A.mul i' j (cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) h) a) b := by
  cases h
  rfl

private theorem d_cast (A : DGA) {i i' : ℤ} (h : i = i') (a : A.toCochainComplex.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X (n + 1) : Type u)) h)
      (A.toCochainComplex.d i (i + 1) a) =
    A.toCochainComplex.d i' (i' + 1)
      (cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) h) a) := by
  cases h
  rfl

private def oppositeMul (A : DGA) (i j : ℤ) :
    A.toCochainComplex.X i →ₗ[R] A.toCochainComplex.X j →ₗ[R] A.toCochainComplex.X (i + j) :=
  { toFun := fun a ↦
      { toFun := fun b ↦
          cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) (add_comm j i))
            (oppositeSign R i j • A.mul j i b a)
        map_add' := by
          intro b₁ b₂
          rw [LinearMap.map_add, LinearMap.add_apply, smul_add]
          let x : A.toCochainComplex.X (j + i) := oppositeSign R i j • ((A.mul j i) b₁) a
          let y : A.toCochainComplex.X (j + i) := oppositeSign R i j • ((A.mul j i) b₂) a
          simpa [x, y] using x_cast_add A (add_comm j i) x y
        map_smul' := by
          intro r b
          rw [LinearMap.map_smul, LinearMap.smul_apply]
          let x : A.toCochainComplex.X (j + i) := oppositeSign R i j • ((A.mul j i) b) a
          simpa [x, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
            x_cast_smul A (add_comm j i) r x }
    map_add' := by
      intro a₁ a₂
      ext b
      change cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) (add_comm j i))
          (oppositeSign R i j • ((A.mul j i) b) (a₁ + a₂)) =
        cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) (add_comm j i))
            (oppositeSign R i j • ((A.mul j i) b) a₁) +
          cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) (add_comm j i))
            (oppositeSign R i j • ((A.mul j i) b) a₂)
      rw [show ((A.mul j i) b) (a₁ + a₂) = ((A.mul j i) b) a₁ + ((A.mul j i) b) a₂ by
            exact LinearMap.map_add ((A.mul j i) b) a₁ a₂,
        smul_add]
      let x : A.toCochainComplex.X (j + i) := oppositeSign R i j • ((A.mul j i) b) a₁
      let y : A.toCochainComplex.X (j + i) := oppositeSign R i j • ((A.mul j i) b) a₂
      simpa [x, y] using x_cast_add A (add_comm j i) x y
    map_smul' := by
      intro r a
      ext b
      change cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) (add_comm j i))
          (oppositeSign R i j • ((A.mul j i) b) (r • a)) =
        (RingHom.id R) r •
          cast (congrArg (fun n : ℤ ↦ (A.toCochainComplex.X n : Type u)) (add_comm j i))
            (oppositeSign R i j • ((A.mul j i) b) a)
      rw [LinearMap.map_smul]
      let x : A.toCochainComplex.X (j + i) := oppositeSign R i j • ((A.mul j i) b) a
      simpa [x, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
        x_cast_smul A (add_comm j i) r x }

private theorem oppositeMul_apply (A : DGA) (i j : ℤ) (a : A.X i) (b : A.X j) :
    oppositeMul A i j a b =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm j i))
        (oppositeSign R i j • A.mul j i b a) := by
  rfl

/-- Helper for Definition 22.11.1: the signed reversed multiplication is associative on
homogeneous elements. -/
private theorem oppositeMul_assoc_apply (A : DGA) (i j k : ℤ)
    (a : A.X i) (b : A.X j) (c : A.X k) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_assoc i j k))
      (oppositeMul A (i + j) k (oppositeMul A i j a b) c) =
      oppositeMul A i (j + k) a (oppositeMul A j k b c) := by
  -- Route correction: normalize both opposite products to the underlying multiplication and
  -- then compare them through `A.mul_assoc` with the Koszul sign identity.
  let core : A.X ((k + j) + i) := A.mul (k + j) i (A.mul k j c b) a
  rw [oppositeMul_apply, oppositeMul_apply, oppositeMul_apply, oppositeMul_apply]
  rw [← mul_cast_right A k (add_comm j i) c (oppositeSign R i j • A.mul j i b a)]
  rw [LinearMap.map_smul]
  rw [← A.mul_assoc_apply k j i c b a]
  rw [x_cast_smul A (add_comm k (i + j)) (oppositeSign R (i + j) k)
    (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (congrArg (HAdd.hAdd k) (add_comm j i)))
      (oppositeSign R i j • cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_assoc k j i))
        core))]
  rw [x_cast_smul A (add_assoc i j k) (oppositeSign R (i + j) k)
    (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm k (i + j)))
      (cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (congrArg (HAdd.hAdd k) (add_comm j i)))
        (oppositeSign R i j • cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_assoc k j i))
          core)))]
  rw [← x_cast_smul A (add_assoc k j i) (oppositeSign R i j) core]
  rw [x_cast_cast_cast_cast_smul A (add_assoc k j i)
    (congrArg (HAdd.hAdd k) (add_comm j i)) (add_comm k (i + j)) (add_assoc i j k)
    (oppositeSign R i j) core]
  rw [← mul_cast_left A (add_comm k j) i (oppositeSign R j k • A.mul k j c b) a]
  rw [LinearMap.map_smul]
  rw [LinearMap.smul_apply]
  rw [x_cast_smul A (add_comm (j + k) i) (oppositeSign R i (j + k))
    (cast (congrArg (fun n : ℤ ↦ (A.X (n + i) : Type u)) (add_comm k j))
      (oppositeSign R j k • core))]
  rw [x_cast_cast_smul A (congrArg (fun n : ℤ ↦ n + i) (add_comm k j))
    (add_comm (j + k) i) (oppositeSign R j k) core]
  rw [x_cast_congr A
    ((((add_assoc k j i).trans (congrArg (HAdd.hAdd k) (add_comm j i))).trans
        (add_comm k (i + j))).trans
      (add_assoc i j k))
    (by omega : (k + j) + i = i + (j + k)) core]
  rw [x_cast_congr A
    ((congrArg (fun n : ℤ ↦ n + i) (add_comm k j)).trans (add_comm (j + k) i))
    (by omega : (k + j) + i = i + (j + k)) core]
  rw [smul_smul, smul_smul, oppositeSign_assoc]

/-- Helper for Definition 22.11.1: the transported `b * d(a)` branch from `A.leibniz m n b a`
is the left-hand Leibniz summand for the opposite multiplication. -/
private theorem oppositeMulLeibnizMulDaSummand (A : DGA) (n m : ℤ)
    (a : A.X n) (b : A.X m) :
    oppositeSign R n m •
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
          (congrArg (fun i : ℤ ↦ i + 1) (add_comm m n)))
          (m.negOnePow •
            cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
              (cochainDGAlgebra_rightLeibniz_index m n))
              (A.mul m (n + 1) b (A.d n a))) =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
        (cochainDGAlgebra_leftLeibniz_index n m))
        (oppositeMul A (n + 1) m (A.d n a) b) := by
  -- Expand the opposite product and rewrite both sides to the same transported core term.
  let core : A.X (m + (n + 1)) := A.mul m (n + 1) b (A.d n a)
  have hinner :
      m.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
            (cochainDGAlgebra_rightLeibniz_index m n)) core =
        ((m.negOnePow : R) •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
            (cochainDGAlgebra_rightLeibniz_index m n)) core) := by
    simpa using (Int.cast_smul_eq_zsmul R (m.negOnePow)
      (cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
        (cochainDGAlgebra_rightLeibniz_index m n)) core)).symm
  have hscalar :
      oppositeSign R n m * (m.negOnePow : R) = oppositeSign R m (n + 1) := by
    calc
      oppositeSign R n m * (m.negOnePow : R) = oppositeSign R (n + 1) m := by
        rw [oppositeSign_add_one_left]
      _ = oppositeSign R m (n + 1) := by
        rw [oppositeSign_comm]
  rw [oppositeMul_apply]
  rw [x_cast_cast_smul A (add_comm m (n + 1))
    (cochainDGAlgebra_leftLeibniz_index n m) (oppositeSign R (n + 1) m) core]
  rw [hinner]
  rw [x_cast_smul A (congrArg (fun i : ℤ ↦ i + 1) (add_comm m n)) (m.negOnePow : R)
    (cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
      (cochainDGAlgebra_rightLeibniz_index m n)) core)]
  rw [cast_cast]
  rw [x_cast_congr A
    ((cochainDGAlgebra_rightLeibniz_index m n).trans
      (congrArg (fun i : ℤ ↦ i + 1) (add_comm m n)))
    ((add_comm m (n + 1)).trans (cochainDGAlgebra_leftLeibniz_index n m)) core]
  rw [smul_smul]
  rw [hscalar]
  simpa [oppositeSign_comm]

/-- Helper for Definition 22.11.1: the transported `d(b) * a` branch from `A.leibniz m n b a`
is the right-hand Leibniz summand for the opposite multiplication. -/
private theorem oppositeMulLeibnizDMulASummand (A : DGA) (n m : ℤ)
    (a : A.X n) (b : A.X m) :
    oppositeSign R n m •
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
        (congrArg (fun i : ℤ ↦ i + 1) (add_comm m n)))
        (cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
          (cochainDGAlgebra_leftLeibniz_index m n))
          (A.mul (m + 1) n (A.d m b) a)) =
      (n.negOnePow •
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
          (cochainDGAlgebra_rightLeibniz_index n m))
          (oppositeMul A n (m + 1) a (A.d m b))) := by
  -- Expand the opposite product and fold the shifted sign back to the original Koszul sign.
  let core : A.X ((m + 1) + n) := A.mul (m + 1) n (A.d m b) a
  have hsquare : ((n.negOnePow : R) * (n.negOnePow : R)) = (1 : R) := by
    simpa [oppositeSign] using (oppositeSign_mul_self (R := R) n 1)
  rw [oppositeMul_apply]
  rw [cast_cast]
  rw [x_cast_congr A
    ((cochainDGAlgebra_leftLeibniz_index m n).trans
      (congrArg (fun i : ℤ ↦ i + 1) (add_comm m n)))
    ((add_comm (m + 1) n).trans (cochainDGAlgebra_rightLeibniz_index n m)) core]
  rw [x_cast_cast_smul A (add_comm (m + 1) n)
    (cochainDGAlgebra_rightLeibniz_index n m) (oppositeSign R n (m + 1)) core]
  rw [show oppositeSign R n m =
      (n.negOnePow : R) * oppositeSign R n (m + 1) by
      calc
        oppositeSign R n m = oppositeSign R n m * ((n.negOnePow : R) * (n.negOnePow : R)) := by
          rw [hsquare]
          ring
        _ = (n.negOnePow : R) * (oppositeSign R n m * (n.negOnePow : R)) := by ring
        _ = (n.negOnePow : R) * oppositeSign R n (m + 1) := by
          rw [oppositeSign_add_one_right]]
  calc
    ((n.negOnePow : R) * oppositeSign R n (m + 1)) •
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
          ((add_comm (m + 1) n).trans (cochainDGAlgebra_rightLeibniz_index n m))) core =
      ((n.negOnePow : R)) •
        (oppositeSign R n (m + 1) •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
            ((add_comm (m + 1) n).trans (cochainDGAlgebra_rightLeibniz_index n m))) core) := by
      rw [smul_smul]
    _ = n.negOnePow •
        (oppositeSign R n (m + 1) •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
            ((add_comm (m + 1) n).trans (cochainDGAlgebra_rightLeibniz_index n m))) core) := by
      simpa using Int.cast_smul_eq_zsmul R (n.negOnePow)
        (oppositeSign R n (m + 1) •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
            ((add_comm (m + 1) n).trans (cochainDGAlgebra_rightLeibniz_index n m))) core)
private theorem oppositeMul_leibniz_apply (A : DGA) (n m : ℤ)
    (a : A.X n) (b : A.X m) :
    A.d (n + m) (oppositeMul A n m a b) =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
        (cochainDGAlgebra_leftLeibniz_index n m))
        (oppositeMul A (n + 1) m (A.d n a) b) +
      (n.negOnePow •
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
          (cochainDGAlgebra_rightLeibniz_index n m))
          (oppositeMul A n (m + 1) a (A.d m b))) := by
  -- Route correction: rewrite the opposite differential to the original Leibniz rule on `b * a`
  -- and then normalize the two transported branches separately.
  rw [oppositeMul_apply]
  rw [← d_cast A (add_comm m n) (oppositeSign R n m • A.mul m n b a)]
  rw [LinearMap.map_smul]
  rw [x_cast_smul A (congrArg (fun i : ℤ ↦ i + 1) (add_comm m n)) (oppositeSign R n m)
    (A.d (m + n) (A.mul m n b a))]
  rw [A.leibniz_apply m n b a]
  rw [x_cast_add A (congrArg (fun i : ℤ ↦ i + 1) (add_comm m n))
    (cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
      (cochainDGAlgebra_leftLeibniz_index m n))
      (A.mul (m + 1) n (A.d m b) a))
    (m.negOnePow •
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type u))
        (cochainDGAlgebra_rightLeibniz_index m n))
        (A.mul m (n + 1) b (A.d n a)))]
  rw [smul_add]
  rw [oppositeMulLeibnizDMulASummand A n m a b]
  rw [oppositeMulLeibnizMulDaSummand A n m a b]
  simpa [add_comm]

/-- Definition 22.11.1: on the canonical Chapter 22 owner `CochainDGAlgebra R`, the opposite
cochain differential graded algebra keeps the same graded pieces and differential and reverses
homogeneous multiplication with the Koszul sign `(-1)^(deg a * deg b)`. -/
@[stacks 09JG]
def opposite (A : DGA) : DGA where
  toCochainComplex := A.toCochainComplex
  one := A.one
  mul := oppositeMul A
  mul_assoc := by
    -- The helper theorem packages all cast and sign bookkeeping for associativity.
    exact oppositeMul_assoc_apply A
  one_mul := by
    intro n a
    rw [oppositeMul_apply]
    simpa using A.mul_one n a
  mul_one := by
    intro n a
    rw [oppositeMul_apply]
    simpa using A.one_mul n a
  leibniz := by
    intro n m a b
    -- The helper theorem packages the opposite Leibniz normalization once and for all.
    exact oppositeMul_leibniz_apply A n m a b

/-- The opposite cochain differential graded algebra has the same underlying cochain complex. -/
@[simp] theorem opposite_toCochainComplex (A : DGA) :
    A.opposite.toCochainComplex = A.toCochainComplex :=
  rfl

/-- The multiplication in the opposite differential graded algebra is the Koszul-twisted reverse
product. -/
@[simp] theorem opposite_mul_apply (A : DGA) (i j : ℤ) (a : A.X i) (b : A.X j) :
    A.opposite.mul i j a b =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm j i))
        (oppositeSign R i j • A.mul j i b a) :=
  rfl

/-- The degree-`n` term of the opposite differential graded algebra is the original degree-`n`
term. -/
@[simp] theorem opposite_X (A : DGA) (n : ℤ) :
    A.opposite.X n = A.X n :=
  rfl

/-- The differential of the opposite differential graded algebra is the original differential. -/
@[simp] theorem opposite_d (A : DGA) (n : ℤ) :
    A.opposite.d n = A.d n :=
  rfl

/-- The unit of the opposite differential graded algebra is the original unit. -/
@[simp] theorem opposite_one (A : DGA) :
    A.opposite.one = A.one :=
  rfl

/-- Helper for Definition 22.11.1: taking the opposite multiplication twice recovers the original
homogeneous multiplication. -/
private theorem opposite_opposite_mul_apply (A : DGA) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    A.opposite.opposite.mul i j a b = A.mul i j a b := by
  -- Expand the opposite multiplication twice, cancel the transport along the two commutativity
  -- casts, and use the involutivity of the Koszul sign.
  rw [opposite_mul_apply, opposite_mul_apply]
  change
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm j i))
        (oppositeSign R i j •
          cast (congrArg (fun n : ℤ ↦ (A.X n : Type u)) (add_comm i j))
            (oppositeSign R j i • A.mul i j a b)) =
      A.mul i j a b
  rw [x_cast_smul A (add_comm j i)]
  rw [x_cast_add_comm_cancel A i j (oppositeSign R j i • A.mul i j a b)]
  rw [oppositeSign_comm i j]
  exact oppositeSign_smul_oppositeSign j i (A.mul i j a b)

/-- Taking the opposite differential graded algebra twice recovers the original algebra; this is
the involutive companion used by downstream left/right module bridge files. -/
@[simp] theorem opposite_opposite (A : DGA) :
    A.opposite.opposite = A := by
  -- Destruct the structure and simplify the double-opposite multiplication field directly.
  cases A with
  | mk toCochainComplex mul one mul_assoc one_mul mul_one leibniz =>
      let B : DGA := {
        toCochainComplex := toCochainComplex
        mul := mul
        one := one
        mul_assoc := mul_assoc
        one_mul := one_mul
        mul_one := mul_one
        leibniz := leibniz
      }
      rw [CochainDGAlgebra.mk.injEq]
      constructor
      · rfl
      constructor
      · exact heq_of_eq <| by
          funext i j
          ext a b
          simpa [B] using opposite_opposite_mul_apply B i j a b
      · rfl

end CochainDGAlgebra

end
