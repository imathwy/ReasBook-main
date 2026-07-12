import Mathlib
import StacksProject_2024.Chap15.Definition_15_61_1
import StacksProject_2024.Chap23.Lemma_23_6_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u

section

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

-- Semantic search note: `lean_leansearch` was unavailable in this runner. Local precedent fixes
-- the Tor owner as `CategoryTheory.Tor`, while Chapter 23 supplies the compatible
-- divided-power/Tate-resolution layer used in the source proof.

/-- The degree-`n` piece of the graded object `Tor_*^R(S, T)`. -/
abbrev torGradedPiece (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (n : ℕ) : ModuleCat R :=
  Tor[R, n](S, T)

/-- Unfolding the Tor graded piece gives the canonical `CategoryTheory.Tor` object. -/
theorem torGradedPiece_def (n : ℕ) :
    torGradedPiece R S T n = Tor[R, n](S, T) := sorry

/-- The positive degree obtained by multiplying two positive integer degrees. -/
def positiveMulDegree (m d : ℕ+) : ℕ+ :=
  ⟨(m : ℕ) * (d : ℕ), Nat.mul_pos m.2 d.2⟩

/-- Coercing `positiveMulDegree` to `ℕ` gives the ordinary product of the two degrees. -/
theorem positiveMulDegree_coe (m d : ℕ+) :
    (positiveMulDegree m d : ℕ) = (m : ℕ) * (d : ℕ) := sorry

/-- The zeroth divided power of a degree-`2d` class lands in degree `0`. -/
theorem torEvenTargetDegree_zero (d : ℕ+) :
    2 * (0 * (d : ℕ)) = 0 := sorry

/-- The first divided power of a degree-`2d` class lands back in degree `2d`. -/
theorem torEvenTargetDegree_one (d : ℕ+) :
    2 * (1 * (d : ℕ)) = 2 * (d : ℕ) := sorry

/-- Multiplying divided powers of the same degree has the expected target degree. -/
theorem torEvenTargetDegree_add (n m : ℕ) (d : ℕ+) :
    2 * (n * (d : ℕ)) + 2 * (m * (d : ℕ)) =
      2 * ((n + m) * (d : ℕ)) := sorry

/-- The degree identity used in the divided-power additivity formula. -/
theorem torEvenTargetDegree_add_sub {i n : ℕ} (hi : i ≤ n) (d : ℕ+) :
    2 * (i * (d : ℕ)) + 2 * ((n - i) * (d : ℕ)) =
      2 * (n * (d : ℕ)) := sorry

/-- The degree identity used for iterated divided powers. -/
theorem torEvenTargetDegree_comp (n m d : ℕ+) :
    2 * ((n : ℕ) * ((m : ℕ) * (d : ℕ))) =
      2 * (((n : ℕ) * (m : ℕ)) * (d : ℕ)) := sorry

/-- A strictly graded-commutative graded `R`-algebra structure with divided powers on
`Tor_*^R(S, T)`, written directly on the canonical Tor objects. -/
@[stacks 09PQ]
structure TorStrictlyGradedCommutativeDividedPowerAlgebra
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] where
  /-- The product on homogeneous Tor groups. -/
  product :
    ∀ p q : ℕ,
      ModuleCat.of R ((torGradedPiece R S T p : Type u) ⊗[R]
        (torGradedPiece R S T q : Type u)) ⟶
        torGradedPiece R S T (p + q)
  /-- The unit in degree zero. -/
  unit : torGradedPiece R S T 0
  /-- The structural `R`-linear map into the degree-zero Tor group. -/
  algebraMap₀ : ModuleCat.of R R ⟶ torGradedPiece R S T 0
  /-- The unit is the image of `1 ∈ R` under the degree-zero structural map. -/
  unit_eq_algebraMap₀_one : unit = algebraMap₀.hom 1
  /-- The degree-zero structural map is multiplicative for the Tor product. -/
  algebraMap₀_mul :
    ∀ r s : R,
      (product 0 0).hom (algebraMap₀.hom r ⊗ₜ[R] algebraMap₀.hom s) =
        algebraMap₀.hom (r * s)
  /-- The divided power maps on positive even homogeneous Tor degrees. -/
  dividedPower :
    ∀ n : ℕ, ∀ d : ℕ+,
      torGradedPiece R S T (2 * (d : ℕ)) ⟶
        torGradedPiece R S T (2 * (n * (d : ℕ)))
  /-- Associativity of the homogeneous Tor product. -/
  product_assoc :
    ∀ p q r : ℕ,
      ∀ x : torGradedPiece R S T p,
      ∀ y : torGradedPiece R S T q,
      ∀ z : torGradedPiece R S T r,
        cast (congrArg (fun n : ℕ ↦ (torGradedPiece R S T n : Type u))
          (Nat.add_assoc p q r))
          ((product (p + q) r).hom (((product p q).hom (x ⊗ₜ[R] y)) ⊗ₜ[R] z)) =
            (product p (q + r)).hom (x ⊗ₜ[R] ((product q r).hom (y ⊗ₜ[R] z)))
  /-- The degree-zero unit acts on the left. -/
  one_product :
    ∀ p : ℕ, ∀ x : torGradedPiece R S T p,
      cast (congrArg (fun n : ℕ ↦ (torGradedPiece R S T n : Type u)) (Nat.zero_add p))
        ((product 0 p).hom (unit ⊗ₜ[R] x)) = x
  /-- The degree-zero unit acts on the right. -/
  product_one :
    ∀ p : ℕ, ∀ x : torGradedPiece R S T p,
      cast (congrArg (fun n : ℕ ↦ (torGradedPiece R S T n : Type u)) (Nat.add_zero p))
        ((product p 0).hom (x ⊗ₜ[R] unit)) = x
  /-- The product is graded commutative with the Koszul sign. -/
  graded_comm :
    ∀ p q : ℕ,
      ∀ x : torGradedPiece R S T p,
      ∀ y : torGradedPiece R S T q,
        cast (congrArg (fun n : ℕ ↦ (torGradedPiece R S T n : Type u)) (Nat.add_comm p q))
          ((product p q).hom (x ⊗ₜ[R] y)) =
            ((-1 : R) ^ (p * q)) • ((product q p).hom (y ⊗ₜ[R] x))
  /-- Odd-degree homogeneous classes square to zero. -/
  product_self_eq_zero_of_odd :
    ∀ p : ℕ, Odd p → ∀ x : torGradedPiece R S T p,
      (product p p).hom (x ⊗ₜ[R] x) = 0
  /-- The zeroth divided power is the unit. -/
  dividedPower_zero :
    ∀ d : ℕ+, ∀ x : torGradedPiece R S T (2 * (d : ℕ)),
      cast (congrArg (fun n : ℕ ↦ (torGradedPiece R S T n : Type u))
        (torEvenTargetDegree_zero d))
        ((dividedPower 0 d).hom x) = unit
  /-- The first divided power is the identity on each positive even homogeneous degree. -/
  dividedPower_one :
    ∀ d : ℕ+, ∀ x : torGradedPiece R S T (2 * (d : ℕ)),
      cast (congrArg (fun n : ℕ ↦ (torGradedPiece R S T n : Type u))
        (torEvenTargetDegree_one d))
        ((dividedPower 1 d).hom x) = x
  /-- Products of divided powers of one class satisfy the usual binomial coefficient formula. -/
  dividedPower_mul :
    ∀ n m : ℕ, ∀ d : ℕ+, ∀ x : torGradedPiece R S T (2 * (d : ℕ)),
      cast (congrArg (fun k : ℕ ↦ (torGradedPiece R S T k : Type u))
        (torEvenTargetDegree_add n m d))
        ((product (2 * (n * (d : ℕ))) (2 * (m * (d : ℕ)))).hom
          (((dividedPower n d).hom x) ⊗ₜ[R] ((dividedPower m d).hom x))) =
            (((n + m).factorial / (n.factorial * m.factorial) : ℕ) : R) •
              ((dividedPower (n + m) d).hom x)
  /-- Divided powers turn sums into the standard convolution formula. -/
  dividedPower_add :
    ∀ n : ℕ, ∀ d : ℕ+,
      ∀ x y : torGradedPiece R S T (2 * (d : ℕ)),
        (dividedPower n d).hom (x + y) =
          Finset.univ.sum fun i : Fin (n + 1) ↦
            cast
              (congrArg (fun k : ℕ ↦ (torGradedPiece R S T k : Type u))
                (torEvenTargetDegree_add_sub (Nat.lt_succ_iff.mp i.isLt) d))
              ((product (2 * (i.1 * (d : ℕ))) (2 * ((n - i.1) * (d : ℕ)))).hom
                (((dividedPower i.1 d).hom x) ⊗ₜ[R]
                  ((dividedPower (n - i.1) d).hom y)))
  /-- Iterated divided powers satisfy the standard composition formula. -/
  dividedPower_comp :
    ∀ n m d : ℕ+, ∀ x : torGradedPiece R S T (2 * (d : ℕ)),
      cast (congrArg (fun k : ℕ ↦ (torGradedPiece R S T k : Type u))
        (torEvenTargetDegree_comp n m d))
        ((dividedPower (n : ℕ) (positiveMulDegree m d)).hom
          ((dividedPower (m : ℕ) d).hom x)) =
            ((((n : ℕ) * (m : ℕ)).factorial /
                ((n : ℕ).factorial * (m : ℕ).factorial ^ (n : ℕ)) : ℕ) : R) •
              ((dividedPower ((n : ℕ) * (m : ℕ)) d).hom x)

/-- A Tor divided-power algebra can be evaluated as its homogeneous product family. -/
instance :
    CoeFun (TorStrictlyGradedCommutativeDividedPowerAlgebra R S T)
      (fun _ ↦
        ∀ p q : ℕ,
          ModuleCat.of R ((torGradedPiece R S T p : Type u) ⊗[R]
            (torGradedPiece R S T q : Type u)) ⟶
            torGradedPiece R S T (p + q)) where
  coe A := A.product

/-- Evaluating a Tor divided-power algebra as a function recovers its product map. -/
theorem TorStrictlyGradedCommutativeDividedPowerAlgebra.coe_product
    (A : TorStrictlyGradedCommutativeDividedPowerAlgebra R S T) (p q : ℕ) :
    A p q = A.product p q := sorry

/-- Lemma 23.6.12. Let `R` be a commutative ring and let `S` and `T` be commutative
`R`-algebras. Then `Tor_*^R(S, T)` carries a canonical strictly graded-commutative
`R`-algebra structure with divided powers. -/
@[stacks 09PQ]
theorem exists_torStrictlyGradedCommutativeDividedPowerAlgebra :
    Nonempty (TorStrictlyGradedCommutativeDividedPowerAlgebra R S T) := sorry

end
