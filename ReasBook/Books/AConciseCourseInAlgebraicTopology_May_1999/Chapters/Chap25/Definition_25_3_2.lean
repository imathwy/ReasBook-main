import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.SmashProductCoherence
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_2

open CategoryTheory
open scoped BasedSpace

noncomputable section

universe u w

-- Semantic recall via `lean_leansearch`: no canonical ring-prespectrum owner surfaced in the
-- current environment. This file therefore keeps the source-facing owner `RingPrespectrum`, built
-- on the repository's canonical `BasedSpace` owner from Chapter 2, the local `Prespectrum`,
-- and the upstream smash-product coherence API.

namespace Prespectrum

/-- The `n`th term of a prespectrum, viewed as a based topological space so that it can be used
with the smash-product API from Chapter 8. -/
abbrev basedSpace (T : Prespectrum.{u, w}) (n : ℕ) : BasedSpace :=
  PointedCompactlyGenerated.toBasedSpace (T n)

/-- The equality-induced based map between two indexed terms of the same prespectrum. -/
abbrev basedSpaceCast (T : Prespectrum.{u, w}) {m n : ℕ} (h : m = n) :
    T.basedSpace m ⟶ T.basedSpace n :=
  eqToHom (congrArg (fun k ↦ T.basedSpace k) h)

/-- Reindexing a prespectrum term along the reflexive equality is the identity based map. -/
@[simp] theorem basedSpaceCast_rfl (T : Prespectrum.{u, w}) (n : ℕ) :
    T.basedSpaceCast (rfl : n = n) = 𝟙 (T.basedSpace n) := by
  simp [Prespectrum.basedSpaceCast]

end Prespectrum

/-- Definition 25.3.2: a ring prespectrum is a prespectrum equipped with a unit `S^0 ⟶ T 0`
and product maps `T m ∧ T n ⟶ T (m + n)` that are associative and unital up to based homotopy.
Here `sphereZero` is the Chapter 11 two-point model of `S⁰`, viewed through the based-space
bridge from `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.SmashProductCoherence`, and the products are formed on the
underlying based topological spaces of the prespectrum terms. -/
structure RingPrespectrum extends Prespectrum.{u, w} where
  unit : sphereZero ⟶ toPrespectrum.basedSpace 0
  mul :
    ∀ m n : ℕ,
      (toPrespectrum.basedSpace m ∧ toPrespectrum.basedSpace n) ⟶
        toPrespectrum.basedSpace (m + n)
  mul_assoc :
    ∀ l m n : ℕ,
      basedHomotopyRel
        (smashProductMap (mul l m) (𝟙 (toPrespectrum.basedSpace n)) ≫ mul (l + m) n)
        (smashProductAssoc
            (toPrespectrum.basedSpace l)
            (toPrespectrum.basedSpace m)
            (toPrespectrum.basedSpace n) ≫
          smashProductMap (𝟙 (toPrespectrum.basedSpace l)) (mul m n) ≫
            mul l (m + n) ≫
              toPrespectrum.basedSpaceCast (Nat.add_assoc l m n).symm)
  one_mul :
    ∀ n : ℕ,
      basedHomotopyRel
        (smashProductMap unit (𝟙 (toPrespectrum.basedSpace n)) ≫ mul 0 n)
        (smashProductLeftUnit (toPrespectrum.basedSpace n) ≫
          toPrespectrum.basedSpaceCast (Nat.zero_add n).symm)
  mul_one :
    ∀ n : ℕ,
      basedHomotopyRel
        (smashProductMap (𝟙 (toPrespectrum.basedSpace n)) unit ≫ mul n 0)
        (smashProductRightUnit (toPrespectrum.basedSpace n) ≫
          toPrespectrum.basedSpaceCast (Nat.add_zero n).symm)

namespace RingPrespectrum

/-- A ring prespectrum can be evaluated at `n` to recover its `n`th pointed compactly generated
space. -/
instance : CoeFun (RingPrespectrum.{u, w}) (fun _ ↦ ℕ → PointedCompactlyGenerated.{u, w}) where
  coe T := T.toPrespectrum

/-- Evaluating a ring prespectrum as a function returns its underlying sequence of spaces. -/
@[simp] theorem coe_apply (T : RingPrespectrum.{u, w}) (n : ℕ) :
    T n = T.toPrespectrum n := rfl

/-- The source associativity law of a ring prespectrum. -/
theorem mul_assoc_spec (T : RingPrespectrum.{u, w}) (l m n : ℕ) :
    basedHomotopyRel
      (smashProductMap (T.mul l m) (𝟙 (T.basedSpace n)) ≫ T.mul (l + m) n)
      (smashProductAssoc (T.basedSpace l) (T.basedSpace m) (T.basedSpace n) ≫
        smashProductMap (𝟙 (T.basedSpace l)) (T.mul m n) ≫
          T.mul l (m + n) ≫ T.basedSpaceCast (Nat.add_assoc l m n).symm) :=
  T.mul_assoc l m n

/-- The source left-unit law of a ring prespectrum. -/
theorem one_mul_spec (T : RingPrespectrum.{u, w}) (n : ℕ) :
    basedHomotopyRel
      (smashProductMap T.unit (𝟙 (T.basedSpace n)) ≫ T.mul 0 n)
      (smashProductLeftUnit (T.basedSpace n) ≫ T.basedSpaceCast (Nat.zero_add n).symm) :=
  T.one_mul n

/-- The source right-unit law of a ring prespectrum. -/
theorem mul_one_spec (T : RingPrespectrum.{u, w}) (n : ℕ) :
    basedHomotopyRel
      (smashProductMap (𝟙 (T.basedSpace n)) T.unit ≫ T.mul n 0)
      (smashProductRightUnit (T.basedSpace n) ≫ T.basedSpaceCast (Nat.add_zero n).symm) :=
  T.mul_one n

/-- The defining unit and multiplication laws of a ring prespectrum are exactly the associativity,
left-unit, and right-unit homotopy conditions recorded in the structure. -/
theorem spec (T : RingPrespectrum.{u, w}) :
    (∀ l m n : ℕ,
      basedHomotopyRel
        (smashProductMap (T.mul l m) (𝟙 (T.basedSpace n)) ≫ T.mul (l + m) n)
        (smashProductAssoc (T.basedSpace l) (T.basedSpace m) (T.basedSpace n) ≫
          smashProductMap (𝟙 (T.basedSpace l)) (T.mul m n) ≫
            T.mul l (m + n) ≫ T.basedSpaceCast (Nat.add_assoc l m n).symm)) ∧
      (∀ n : ℕ,
        basedHomotopyRel
          (smashProductMap T.unit (𝟙 (T.basedSpace n)) ≫ T.mul 0 n)
          (smashProductLeftUnit (T.basedSpace n) ≫ T.basedSpaceCast (Nat.zero_add n).symm)) ∧
      (∀ n : ℕ,
        basedHomotopyRel
          (smashProductMap (𝟙 (T.basedSpace n)) T.unit ≫ T.mul n 0)
          (smashProductRightUnit (T.basedSpace n) ≫ T.basedSpaceCast (Nat.add_zero n).symm)) :=
  ⟨T.mul_assoc_spec, T.one_mul_spec, T.mul_one_spec⟩

end RingPrespectrum
