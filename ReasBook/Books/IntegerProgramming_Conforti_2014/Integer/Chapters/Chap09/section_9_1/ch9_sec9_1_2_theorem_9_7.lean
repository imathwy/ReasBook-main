import Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9
import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix IntegerVectorNotation

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch` in this environment, so this file follows the local Chapter 9 conventions:
-- convex bodies are represented by `ConvexBody`, their source-facing hypotheses use the bridge
-- predicates `ConvexBody.FullDimensional` and `ConvexBody.ContainsIntegralPoint`, and rational
-- inequality systems use an explicit matrix presentation over `Fin n → ℝ`.

section Theorem97

variable {m n : ℕ}

/-- A subset `K ⊆ ℝ^n` contains an integral point when it meets the canonical integer-vector
owner `ℤ^n`. -/
def contains_integral_point (K : Set (Fin n → ℝ)) : Prop :=
  (K ∩ ℤ^n).Nonempty

/-- `contains_integral_point K` means that `K` contains the real coercion of some integer vector.
-/
theorem contains_integral_point_iff
    {K : Set (Fin n → ℝ)} :
    contains_integral_point K ↔
      ∃ z : Fin n → ℤ, Int.cast ∘ z ∈ K := by
  constructor
  · rintro ⟨x, hxK, hxZ⟩
    rcases mem_integerVectors_iff.mp hxZ with ⟨z, rfl⟩
    exact ⟨z, hxK⟩
  · rintro ⟨z, hzK⟩
    exact ⟨Int.cast ∘ z, hzK, mem_integerVectors_iff.mpr ⟨z, rfl⟩⟩

namespace ConvexBody

/-- A convex body is full dimensional when its interior is nonempty. -/
def FullDimensional (K : ConvexBody (Fin n → ℝ)) : Prop :=
  (interior K.carrier).Nonempty

/-- `K.FullDimensional` means that the convex body `K` has nonempty interior. -/
theorem fullDimensional_iff
    {K : ConvexBody (Fin n → ℝ)} :
    K.FullDimensional ↔ (interior K.carrier).Nonempty :=
  Iff.rfl

/-- A convex body contains an integral point when its underlying set does. -/
def ContainsIntegralPoint (K : ConvexBody (Fin n → ℝ)) : Prop :=
  _root_.contains_integral_point (K : Set (Fin n → ℝ))

/-- `K.ContainsIntegralPoint` means that `K` contains the real coercion of some integer vector. -/
theorem containsIntegralPoint_iff
    {K : ConvexBody (Fin n → ℝ)} :
    K.ContainsIntegralPoint ↔
      ∃ z : Fin n → ℤ, Int.cast ∘ z ∈ K := by
  change _root_.contains_integral_point (K : Set (Fin n → ℝ)) ↔
      ∃ z : Fin n → ℤ, Int.cast ∘ z ∈ K
  exact _root_.contains_integral_point_iff

end ConvexBody

/-- The linear functional on `ℝ^n` induced by an integral direction `d ∈ ℤ^n`. -/
def integral_direction_linear_form (d : Fin n → ℤ) : (Fin n → ℝ) → ℝ :=
  fun x ↦ (Int.cast ∘ d) ⬝ᵥ x

/-- The width of a subset `K ⊆ ℝ^n` in the integral direction `d ∈ ℤ^n`. -/
noncomputable def directional_width
    (K : Set (Fin n → ℝ))
    (d : Fin n → ℤ) : ℝ :=
  sSup (integral_direction_linear_form d '' K) -
    sInf (integral_direction_linear_form d '' K)

namespace DirectionalWidthNotation

/- Textbook notation for directional width: `w_{d}(K)` is the width of `K` in the integral
direction `d`. -/
scoped notation:max "w_{" d "}(" K ")" => directional_width K d

end DirectionalWidthNotation

open scoped DirectionalWidthNotation

/-- The lattice width of a convex body is the infimum of its directional widths over all nonzero
integral directions, that is, of the values `w_{d}(K)`. -/
noncomputable def lattice_width
    (K : ConvexBody (Fin n → ℝ)) : ℝ :=
  sInf
    ((fun d : {d : Fin n → ℤ // d ≠ 0} ↦
        w_{d.1}(K)) '' Set.univ)

/-- The explicit flatness bound `n (n + 1) 2^{n (n - 1) / 4}` appearing in the rational-polytope
algorithmic consequence of the flatness theorem. -/
noncomputable def flat_direction_bound (n : ℕ) : ℝ :=
  (n * (n + 1) : ℝ) * Real.rpow 2 (((n * (n - 1) : ℕ) : ℝ) / 4)

/-- A certified integral point of a set `P ⊆ ℝ^n`, represented by an integer vector whose real
embedding lies in `P`. -/
def IntegralPointCertificate (P : Set (Fin n → ℝ)) :=
  {z : Fin n → ℤ // Int.cast ∘ z ∈ P}

namespace IntegralPointCertificate

variable {P : Set (Fin n → ℝ)}

/-- The real embedding of an integral-point certificate lies in the target set. -/
theorem mem (point : IntegralPointCertificate P) :
    Int.cast ∘ point.1 ∈ P :=
  point.2

/-- An integral-point certificate yields the corresponding `contains_integral_point` witness. -/
theorem contains_integral_point (point : IntegralPointCertificate P) :
    _root_.contains_integral_point P :=
  ⟨Int.cast ∘ point.1, point.mem, mem_integerVectors_iff.mpr ⟨point.1, rfl⟩⟩

end IntegralPointCertificate

/-- A certified flat direction of a set `P ⊆ ℝ^n`, represented by a nonzero integer vector whose
directional width `w_{d}(P)` is bounded by `flat_direction_bound n`. -/
def FlatDirectionCertificate (P : Set (Fin n → ℝ)) :=
  {d : Fin n → ℤ // d ≠ 0 ∧ _root_.directional_width P d ≤ _root_.flat_direction_bound n}

namespace FlatDirectionCertificate

variable {P : Set (Fin n → ℝ)}

/-- The underlying integer direction of a flat-direction certificate is nonzero. -/
theorem ne_zero (direction : FlatDirectionCertificate P) :
    direction.1 ≠ 0 :=
  direction.2.1

/-- A flat-direction certificate carries the promised width bound. -/
theorem width_le (direction : FlatDirectionCertificate P) :
    _root_.directional_width P direction.1 ≤ _root_.flat_direction_bound n :=
  direction.2.2

end FlatDirectionCertificate

/-- The concrete solver data for the rational-polytope consequence of the flatness theorem. The
certification predicate `RationalPolytopeFlatnessAlgorithm.Certified` records the polynomial-time
bound and the guaranteed output on full-dimensional compact inputs. -/
structure RationalPolytopeFlatnessAlgorithm (m n : ℕ) where
  run
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ) :
      Option
        (Sum (IntegralPointCertificate (rational_matrix_polyhedron A b))
          (FlatDirectionCertificate (rational_matrix_polyhedron A b)))
  runTime
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ) :
      ℕ

/-- Evaluate a rational-polytope flatness algorithm via its solver map. -/
instance rationalPolytopeFlatnessAlgorithmCoeFun (m n : ℕ) :
    CoeFun (RationalPolytopeFlatnessAlgorithm m n) (fun _ ↦
      (A : Matrix (Fin m) (Fin n) ℚ) →
      (b : Fin m → ℚ) →
        Option
          (Sum (IntegralPointCertificate (rational_matrix_polyhedron A b))
            (FlatDirectionCertificate (rational_matrix_polyhedron A b)))) where
  coe algorithm := algorithm.run

namespace RationalPolytopeFlatnessAlgorithm

/-- `Certified algorithm` means that `algorithm` satisfies the explicit polynomial-time bound from
Theorem 9.7 (2) and returns the promised Chapter 9 flatness output on every full-dimensional
compact rational polyhedron. -/
structure Certified
    {m n : ℕ} (algorithm : RationalPolytopeFlatnessAlgorithm m n) : Prop where
  polynomial_time :
    ∃ π : Polynomial ℕ,
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        algorithm.runTime A b ≤ π.eval (n + rational_linear_system_encoding_size A b)
  correct
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ)
      (hfull : (interior (rational_matrix_polyhedron A b)).Nonempty)
      (hcompact : IsCompact (rational_matrix_polyhedron A b)) :
      ∃ out,
        algorithm A b = some out

/-- A rational-polytope flatness algorithm satisfies its explicit polynomial running-time bound. -/
theorem runTime_le
    {m n : ℕ}
    (algorithm : RationalPolytopeFlatnessAlgorithm m n)
    (hcert : Certified algorithm) :
    ∃ π : Polynomial ℕ,
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        algorithm.runTime A b ≤ π.eval (n + rational_linear_system_encoding_size A b) :=
  hcert.polynomial_time

/-- On a full-dimensional compact rational polyhedron, a rational-polytope flatness algorithm
returns an explicit output in the canonical Chapter 9 flatness format. -/
theorem output_spec
    {m n : ℕ}
    (algorithm : RationalPolytopeFlatnessAlgorithm m n)
    (hcert : Certified algorithm)
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hfull : (interior (rational_matrix_polyhedron A b)).Nonempty)
    (hcompact : IsCompact (rational_matrix_polyhedron A b)) :
    ∃ out,
      algorithm A b = some out :=
  hcert.correct A b hfull hcompact

end RationalPolytopeFlatnessAlgorithm

/-- Theorem 9.7 (1) (Flatness Theorem). There exists a function `k : ℕ → ℝ` depending only on the
dimension such that every full-dimensional convex body `K ⊆ ℝ^n` with no integral point has
lattice width, equivalently the infimum of the widths `w_{d}(K)` over nonzero integral
directions, at most `k n`. Here full dimensionality is represented by `K.FullDimensional`, i.e.
nonempty interior. -/
theorem exists_flatness_constant_for_lattice_width :
    ∃ k : ℕ → ℝ,
      ∀ {n : ℕ}, ∀ K : ConvexBody (Fin n → ℝ),
        K.FullDimensional →
        ¬ K.ContainsIntegralPoint →
        lattice_width K ≤ k n := sorry

/-- Theorem 9.7 (2). For rational polytopes given by rational linear inequalities, there is a
polynomial-time algorithm that, on every full-dimensional compact input `P = {x ∈ ℝ^n | A x ≤ b}`,
returns either an integral point of `P` or a flat direction `d ∈ ℤ^n` with
`w_{d}(P) ≤ n (n + 1) 2^{n (n - 1) / 4}`. -/
theorem exists_rational_polytope_flatness_algorithm
    (m n : ℕ) :
    ∃ algorithm : RationalPolytopeFlatnessAlgorithm m n,
      RationalPolytopeFlatnessAlgorithm.Certified algorithm := sorry

end Theorem97
