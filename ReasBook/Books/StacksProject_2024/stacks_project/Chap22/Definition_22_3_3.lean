import StacksProject_2024.Chap22.Definition_22_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [CommRing R]

namespace CochainDGAlgebra

/-- Definition 22.3.3 (1): a differential graded algebra is commutative if homogeneous elements
`a` of degree `n` and `b` of degree `m` satisfy `ab = (-1)^(nm) ba`. The chapter's downstream
owner is `CochainDGAlgebra R`, so the sign rule is stated on its degreewise multiplication maps.
-/
@[stacks 061W, mk_iff isCommutative_iff]
class IsCommutative (A : CochainDGAlgebra R) : Prop where
  mul_comm {n m : ℤ} (a : A.X n) (b : A.X m) :
      A.mul n m a b =
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type u)) (add_comm m n))
          (((n * m).negOnePow : R) • A.mul m n b a)

/-- In a commutative differential graded algebra, homogeneous multiplication picks up the Koszul
sign when the two factors are swapped. -/
theorem mul_comm_apply (A : CochainDGAlgebra R) [h : A.IsCommutative]
    {n m : ℤ} (a : A.X n) (b : A.X m) :
    A.mul n m a b =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type u)) (add_comm m n))
        (((n * m).negOnePow : R) • A.mul m n b a) :=
  h.mul_comm a b

/-- Definition 22.3.3 (2): a differential graded algebra is strictly commutative if it is
commutative and every odd-degree homogeneous element squares to zero. -/
@[stacks 061W, mk_iff isStrictlyCommutative_iff]
class IsStrictlyCommutative (A : CochainDGAlgebra R) : Prop extends IsCommutative A where
  sq_eq_zero_of_odd {n : ℤ} (hn : Odd n) (a : A.X n) : A.mul n n a a = 0

/-- In a strictly commutative differential graded algebra, every odd-degree homogeneous element
squares to zero. -/
theorem mul_self_eq_zero_of_odd (A : CochainDGAlgebra R) [h : A.IsStrictlyCommutative]
    {n : ℤ} (hn : Odd n) (a : A.X n) :
    A.mul n n a a = 0 :=
  h.sq_eq_zero_of_odd hn a

end CochainDGAlgebra
