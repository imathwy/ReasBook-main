import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Lemma_24_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ProjectiveBundleNotation

noncomputable section

-- Semantic recall via `lean_leansearch` only surfaced unrelated projectivization declarations.
-- Local Chapter 23/24 precedent already fixes the relevant owners as `ComplexPlaneBundle`,
-- `ChernClassFamily`, `P(E)`, and `projectiveBundleCohomologyPullbackMap`.

section

variable {X : Type} [TopologicalSpace X]
variable {n : ℕ} {E : ComplexPlaneBundle n X}
variable [FiberBundle (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
variable [VectorBundle ℂ (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]

local notation "XTop" => TopCat.of X
local notation "PTop" => TopCat.of (P(E))

-- Local instance justification (defeq pin): the theorem statements below use `∑`, `•`, and `0`
-- in `singularCohomologyClasses ℤ PTop q`, and elaboration does not recover the exact degreewise
-- additive-group instance for `P(E)` from the global owner alone.
local instance projectiveBundleTotalTopCatCohomologyAddCommGroup (q : ℕ) :
    AddCommGroup (singularCohomologyClasses ℤ PTop q) :=
  singularCohomologyClassesAddCommGroup PTop q

/-- The degree-`2 * i` Chern class of the ambient bundle `E`, computed in ordinary integral
singular cohomology using the chosen Chern theory `c`. -/
abbrev projectiveBundleBaseChernClass
    (E : ComplexPlaneBundle n X)
    (c : ChernClassFamily singularCohomologyClassesTheory) (i : ℕ) :
    singularCohomologyClasses ℤ (TopCat.of X) (2 * i) :=
  @ComplexCharacteristicClass.value
    n (2 * i) singularCohomologyClassesTheory.cohomology (c n i) (TopCat.of X)
    (ComplexPlaneBundle.classOf E)

/-- The degree-`2` tautological generator `x` on `P(E)`, defined as the first
Chern class of the tautological complex line bundle. -/
abbrev projectiveBundleTautologicalFirstChernClass
    (E : ComplexPlaneBundle n X)
    [FiberBundle (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    [VectorBundle ℂ (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    (c : ChernClassFamily singularCohomologyClassesTheory) :
    singularCohomologyClasses ℤ (TopCat.of (P(E))) 2 :=
  @ComplexCharacteristicClass.value
    1 2 singularCohomologyClassesTheory.cohomology (c 1 1) (TopCat.of (P(E)))
    (projectiveBundleTautologicalLineBundleClass E)

/-- The degree bookkeeping identity used in the recursive definition of the powers of the
tautological class. -/
theorem projectiveBundleTautologicalFirstChernClassPower_degree_succ (i : ℕ) :
    2 * i + 2 = 2 * (i + 1) := by
  simp [Nat.mul_add, Nat.add_comm]

/-- The target cohomology groups in the successor step of
`projectiveBundleTautologicalFirstChernClassPower` agree by the degree identity
`2 * i + 2 = 2 * (i + 1)`. -/
theorem projectiveBundleTautologicalFirstChernClassPower_type_eq
    (E : ComplexPlaneBundle n X) (i : ℕ) :
    singularCohomologyClasses ℤ (TopCat.of (P(E))) (2 * i + 2) =
      singularCohomologyClasses ℤ (TopCat.of (P(E))) (2 * (i + 1)) := by
  simpa using
    congrArg
      (fun m ↦ ((singularCohomologyClasses ℤ (TopCat.of (P(E))) m) : Type))
      (projectiveBundleTautologicalFirstChernClassPower_degree_succ i)

/-- The cup-product powers `1, x, x^2, ...` of the tautological first Chern class
`x = projectiveBundleTautologicalFirstChernClass c`. -/
def projectiveBundleTautologicalFirstChernClassPower
    (E : ComplexPlaneBundle n X)
    [FiberBundle (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    [VectorBundle ℂ (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    (c : ChernClassFamily singularCohomologyClassesTheory) :
    ∀ i : ℕ, singularCohomologyClasses ℤ (TopCat.of (P(E))) (2 * i)
  | 0 => singularCohomologyOneClass ℤ (TopCat.of (P(E)))
  | i + 1 =>
      cast
        (projectiveBundleTautologicalFirstChernClassPower_type_eq E i)
        (singularCohomologyCup ℤ (TopCat.of (P(E)))
          (2 * i) 2
          (projectiveBundleTautologicalFirstChernClassPower E c i)
          (projectiveBundleTautologicalFirstChernClass E c))

/-- The index set of monomials `x^i` that can contribute to degree-`q` cohomology of
`P(E)`. -/
abbrev ProjectiveBundleCohomologyBasisIndex (n q : ℕ) :=
  { i : Fin n // 2 * (i : ℕ) ≤ q }

/-- For a valid basis index `i` in degree `q`, cupping a degree-`q - 2 * i` pullback class with
`x^i` lands back in degree `q`. -/
theorem projectiveBundleCohomologyBasisIndex_degree
    (q : ℕ) (i : ProjectiveBundleCohomologyBasisIndex n q) :
    (q - 2 * (i : ℕ)) + 2 * (i : ℕ) = q := by
  exact Nat.sub_add_cancel i.2

/-- The target cohomology groups in the monomial `π^*(α) ∪ x^i` agree by the degree identity
attached to the valid basis index `i`. -/
theorem projectiveBundleCohomologyBasisMonomial_type_eq
    (E : ComplexPlaneBundle n X) (q : ℕ) (i : ProjectiveBundleCohomologyBasisIndex n q) :
    singularCohomologyClasses ℤ (TopCat.of (P(E)))
        ((q - 2 * (i : ℕ)) + 2 * (i : ℕ)) =
      singularCohomologyClasses ℤ (TopCat.of (P(E))) q := by
  simpa using
    congrArg
      (fun m ↦ ((singularCohomologyClasses ℤ (TopCat.of (P(E))) m) : Type))
      (projectiveBundleCohomologyBasisIndex_degree q i)

/-- The degree-`q` monomial `π^*(α) ∪ x^i` attached to a valid index `i` and a coefficient class
`α ∈ H^(q - 2 * i)(X; ℤ)`. -/
def projectiveBundleCohomologyBasisMonomial
    (E : ComplexPlaneBundle n X)
    [FiberBundle (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    [VectorBundle ℂ (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    (c : ChernClassFamily singularCohomologyClassesTheory) (q : ℕ)
    (i : ProjectiveBundleCohomologyBasisIndex n q)
    (α : singularCohomologyClasses ℤ (TopCat.of X) (q - 2 * (i : ℕ))) :
    singularCohomologyClasses ℤ (TopCat.of (P(E))) q :=
  cast
    (projectiveBundleCohomologyBasisMonomial_type_eq E q i)
    (singularCohomologyCup ℤ (TopCat.of (P(E)))
      (q - 2 * (i : ℕ)) (2 * (i : ℕ))
      (projectiveBundleCohomologyPullbackMap E (q - 2 * (i : ℕ)) α)
      (projectiveBundleTautologicalFirstChernClassPower E c (i : ℕ)))

/-- The degree bookkeeping identity for the `i`th Chern-class coefficient in the projective-bundle
relation. -/
theorem projectiveBundleCohomologyRelationTerm_degree (i : Fin (n + 1)) :
    2 * (i : ℕ) + 2 * (n - (i : ℕ)) = 2 * n := by
  have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.2
  calc
    2 * (i : ℕ) + 2 * (n - (i : ℕ)) = 2 * ((i : ℕ) + (n - (i : ℕ))) := by
      rw [← Nat.mul_add]
    _ = 2 * n := by rw [Nat.add_sub_of_le hi]

/-- The target cohomology groups in the `i`th relation term agree by the degree identity
`2 * i + 2 * (n - i) = 2 * n`. -/
theorem projectiveBundleCohomologyRelationTerm_type_eq
    (E : ComplexPlaneBundle n X) (i : Fin (n + 1)) :
    singularCohomologyClasses ℤ (TopCat.of (P(E)))
        (2 * (i : ℕ) + 2 * (n - (i : ℕ))) =
      singularCohomologyClasses ℤ (TopCat.of (P(E))) (2 * n) := by
  simpa using
    congrArg
      (fun m ↦ ((singularCohomologyClasses ℤ (TopCat.of (P(E))) m) : Type))
      (projectiveBundleCohomologyRelationTerm_degree i)

/-- The `i`th term `π^*(c_i(E)) ∪ x^(n - i)` in the degree-`2 * n` projective-bundle relation. -/
def projectiveBundleCohomologyRelationTerm
    (E : ComplexPlaneBundle n X)
    [FiberBundle (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    [VectorBundle ℂ (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    (c : ChernClassFamily singularCohomologyClassesTheory) (i : Fin (n + 1)) :
    singularCohomologyClasses ℤ (TopCat.of (P(E))) (2 * n) :=
  cast
    (projectiveBundleCohomologyRelationTerm_type_eq E i)
    (singularCohomologyCup ℤ (TopCat.of (P(E)))
      (2 * (i : ℕ)) (2 * (n - (i : ℕ)))
      (projectiveBundleCohomologyPullbackMap E (2 * (i : ℕ))
        (projectiveBundleBaseChernClass E c (i : ℕ)))
      (projectiveBundleTautologicalFirstChernClassPower E c (n - (i : ℕ))))

variable [Fact (0 < n)]

/-- Theorem 24.3.5 (1): for a rank-`n` complex vector bundle `E`, the ordinary integral
cohomology of `P(E)` is freely generated over `H^*(X; ℤ)` by
`1, x, ..., x^(n - 1)`, where `x` is the first Chern class of the tautological line bundle.
Concretely, every degree-`q` class on `P(E)` admits a unique expression as a sum
of pullbacks of classes on `X` multiplied by the admissible powers of `x`. -/
theorem projectiveBundleCohomology_existsUnique_decomposition
    (normalizationData : StandardIntegralChernNormalization)
    (c : ChernClassFamily singularCohomologyClassesTheory)
    (hchern :
      IsChernTheory
        singularCohomologyClassesTheory normalizationData.toChernNormalization c)
    (q : ℕ)
    (α : singularCohomologyClasses ℤ PTop q) :
    ∃! coeff :
        ∀ i : ProjectiveBundleCohomologyBasisIndex n q,
          singularCohomologyClasses ℤ XTop (q - 2 * (i : ℕ)),
      α =
        ∑ i : ProjectiveBundleCohomologyBasisIndex n q,
          projectiveBundleCohomologyBasisMonomial E c q i (coeff i) :=
      sorry

/-- Theorem 24.3.5 (2): if `x` denotes the first Chern class of the tautological line bundle on
`P(E)`, then `x` satisfies the degree-`2 * n` relation
`∑ i = 0..n, (-1)^i π^*(c_i(E)) ∪ x^(n - i) = 0`, where the coefficients are the actual Chern
classes of `E` in ordinary integral singular cohomology. -/
theorem projectiveBundleCohomology_tautologicalFirstChernClass_relation
    (normalizationData : StandardIntegralChernNormalization)
    (c : ChernClassFamily singularCohomologyClassesTheory)
    (hchern :
      IsChernTheory
        singularCohomologyClassesTheory normalizationData.toChernNormalization c) :
    ∑ i : Fin (n + 1),
        ((-1 : ℤ) ^ (i : ℕ)) •
          projectiveBundleCohomologyRelationTerm E c i =
      (0 : singularCohomologyClasses ℤ PTop (2 * n)) := sorry

end
