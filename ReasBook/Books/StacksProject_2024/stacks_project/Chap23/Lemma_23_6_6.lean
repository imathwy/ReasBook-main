import StacksProject_2024.Chap23.Definition_23_6_1
import StacksProject_2024.Chap23.Lemma_23_6_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe uR uA uB

namespace DifferentialGradedAlgebra

section

variable {R : Type uR} [CommRing R]

/- Source/core/bridge triage:
- `source-facing`: Lemma 23.6.6 itself, namely that a surjective compatible morphism from an
  acyclic graded divided-power differential graded `R`-algebra induces divided powers on the
  graded homology algebra of the target.
- `core/canonical`: the Chapter 23 bundled owners
  `GradedDividedPowerDGAlgebra R`, `GradedDividedPowerDGAlgebraHom R A B`,
  `GradedDividedPowerDGAlgebra.PositiveHomologyVanishes`, and
  `DividedPowerStructure R HB`.
- `bridge/view`: a chosen realization `HB : ParitySplitGradedAlgebra R` of the graded homology
  algebra `H(B)`, encoded through class maps from closed homogeneous elements of `B` into the
  graded pieces of `HB` and the induction predicate asserting that `B.gamma` descends to `HB`.
-/

/-- Closed homogeneous elements of degree `n` in a differential graded `R`-algebra presentation
`(A, grading, d)`. -/
abbrev Cycles
    (A : GradedDividedPowerDGAlgebra.{uR, uA} R) (n : ℕ) :=
  {x : A // x ∈ A.grading n ∧ A.d x = 0}

namespace Cycles

variable {A : GradedDividedPowerDGAlgebra.{uR, uA} R}

/-- The zero element is a cycle in every degree. -/
def zeroCycle (A : GradedDividedPowerDGAlgebra.{uR, uA} R) (n : ℕ) : Cycles A n :=
  ⟨0, (A.grading n).zero_mem, by simpa using A.d.map_zero⟩

/-- Scalar multiples of cycles remain cycles in the same degree. -/
def smulCycle {n : ℕ} (r : R) (x : Cycles A n) : Cycles A n :=
  ⟨r • x.1, (A.grading n).smul_mem r x.2.1, by
    simpa [x.2.2] using A.d.map_smul r x.1⟩

/-- Sums of cycles remain cycles in the same degree. -/
def addCycle {n : ℕ} (x y : Cycles A n) : Cycles A n :=
  ⟨x.1 + y.1, (A.grading n).add_mem x.2.1 y.2.1, by
    simpa [x.2.2, y.2.2] using A.d.map_add x.1 y.1⟩

/-- The unit of a graded differential algebra is a closed degree-zero cycle. -/
def oneCycle (A : GradedDividedPowerDGAlgebra.{uR, uA} R) : Cycles A 0 :=
  let h1 : (1 : A) ∈ A.grading 0 := by
    simpa using A.algebraMap_mem (1 : R)
  ⟨1, h1, A.d_zero h1⟩

/-- Products of homogeneous cycles remain cycles in the sum of the degrees. -/
def mulCycle {m n : ℕ} (x : Cycles A m) (y : Cycles A n) : Cycles A (m + n) :=
  ⟨x.1 * y.1, A.mul_mem x.2.1 y.2.1, by
    simpa [x.2.2, y.2.2] using A.d.map_mul x.1 y.1⟩

end Cycles

/-- A chosen graded `R`-algebra realization of `H(A)` is represented here by class maps from
closed homogeneous elements to the graded pieces, with every class having a cycle representative
and equality of classes detected by boundaries. The structure also records that these class maps
realize the additive, `R`-linear, and multiplicative graded-algebra operations on `H(A)`, so the
chosen realization is genuinely a graded `R`-algebra rather than only a quotient set of cycles. -/
structure IsHomologyGradedAlgebra
    (A : GradedDividedPowerDGAlgebra.{uR, uA} R)
    (HA : ParitySplitGradedAlgebra R)
    (classOf : ∀ n : ℕ, Cycles A n → HA.piece n) : Prop where
  surjective : ∀ n : ℕ, Function.Surjective (classOf n)
  eq_iff_exists_boundary :
    ∀ n : ℕ, ∀ x y : Cycles A n,
      classOf n x = classOf n y ↔
        ∃ z : A, z ∈ A.grading (n + 1) ∧ A.d z = y.1 - x.1
  map_zero :
    ∀ n : ℕ, classOf n (Cycles.zeroCycle A n) = 0
  map_add :
    ∀ n : ℕ, ∀ x y : Cycles A n,
      classOf n (Cycles.addCycle x y) = classOf n x + classOf n y
  map_smul :
    ∀ n : ℕ, ∀ r : R, ∀ x : Cycles A n,
      classOf n (Cycles.smulCycle r x) = r • classOf n x
  map_one :
    classOf 0 (Cycles.oneCycle A) = (GradedMonoid.GOne.one : HA.piece 0)
  map_mul :
    ∀ m n : ℕ, ∀ x : Cycles A m, ∀ y : Cycles A n,
      classOf (m + n) (Cycles.mulCycle x y) =
        GradedMonoid.GMul.mul (classOf m x) (classOf n y)

/-- A divided power structure on a chosen graded-algebra realization `HB` of `H(B)` is induced by
`γ` if, for every positive even cycle, the class of `γ_n(x)` is exactly the value of the induced
operation on the class of `x`. The target cycle representative is kept explicit so the statement
stays source-facing and does not hide the descent behind an opaque chosen witness. -/
def DividedPowerStructure.IsInducedOnHomology
    {B : GradedDividedPowerDGAlgebra.{uR, uB} R}
    {HB : ParitySplitGradedAlgebra R}
    (ΓH : DividedPowerStructure R HB)
    (γ : ℕ → B → B)
    (classOf : ∀ n : ℕ, Cycles B n → HB.piece n) : Prop :=
  ∀ n m : ℕ, ∀ x : Cycles B (2 * (m + 1)),
    ∃ y : Cycles B (2 * (n * (m + 1))),
      y.1 = γ n x.1 ∧
        ΓH n (HB.evenPositiveHom m (classOf (2 * (m + 1)) x)) =
          HB.evenHom (n * (m + 1)) (classOf (2 * (n * (m + 1))) y)

namespace DividedPowerStructure.IsInducedOnHomology

variable {B : GradedDividedPowerDGAlgebra.{uR, uB} R}
variable {HB : ParitySplitGradedAlgebra R}
variable {ΓH : DividedPowerStructure R HB}
variable {γ : ℕ → B → B}
variable {classOf : ∀ n : ℕ, Cycles B n → HB.piece n}

/-- An induced divided power on homology sends the class of a positive even cycle to the class of
the original chain-level divided power of that cycle. -/
theorem exists_cycleRepresentative
    (hΓH : DividedPowerStructure.IsInducedOnHomology ΓH γ classOf)
    (n m : ℕ) (x : Cycles B (2 * (m + 1))) :
    ∃ y : Cycles B (2 * (n * (m + 1))),
      y.1 = γ n x.1 ∧
        ΓH n (HB.evenPositiveHom m (classOf (2 * (m + 1)) x)) =
          HB.evenHom (n * (m + 1)) (classOf (2 * (n * (m + 1))) y) :=
  hΓH n m x

end DividedPowerStructure.IsInducedOnHomology

/-- Lemma 23.6.6 (Tag 09PK): let `(A, d, γ)` and `(B, d, γ)` be differential graded
`R`-algebras as in Definition 23.6.5, let `f : A → B` be a surjective morphism compatible with the
respective divided powers, and assume `H_k(A) = 0` for every positive integer `k`. Then `γ`
induces a divided power structure on the graded `R`-algebra `H(B)`.

The theorem is stated on the Chapter 23 bundled owners
`GradedDividedPowerDGAlgebra R` and `GradedDividedPowerDGAlgebraHom R A B`, together with a chosen
realization `HB` of `H(B)` by its graded pieces and class maps. The main conclusion is the
source-facing existence of a chapter-level owner `ΓH : DividedPowerStructure R HB` satisfying the
explicit induction formula `DividedPowerStructure.IsInducedOnHomology ΓH B.gamma classOf`. -/
@[stacks 09PK]
theorem inducesDividedPowersOnHomology
    (A : GradedDividedPowerDGAlgebra.{uR, uA} R)
    (B : GradedDividedPowerDGAlgebra.{uR, uB} R)
    (f : GradedDividedPowerDGAlgebraHom R A B)
    (hA : A.PositiveHomologyVanishes)
    (hf_surjective : Function.Surjective f)
    (HB : ParitySplitGradedAlgebra R)
    (classOf : ∀ n : ℕ, Cycles B n → HB.piece n)
    (hHB : IsHomologyGradedAlgebra B HB classOf) :
    ∃ ΓH : DividedPowerStructure R HB,
      DividedPowerStructure.IsInducedOnHomology ΓH B.gamma classOf := by
  let _ := A
  let _ := f
  let _ := hA
  let _ := hf_surjective
  let _ := hHB
  sorry

end

end DifferentialGradedAlgebra
