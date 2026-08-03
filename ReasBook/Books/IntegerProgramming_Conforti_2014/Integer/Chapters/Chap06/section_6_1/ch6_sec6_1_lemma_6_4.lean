import Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_definition_6_1_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_15

open scoped Matrix

section Lemma64

variable {n : ℕ}

/-- A lower inequality `δ ≤ γ ⬝ᵥ x` is nontrivial for `P` when it is valid on `P`, but does not
already hold on the whole nonnegative orthant. The companion theorem
`isNontrivialValidGeInequality_iff_is_valid_inequality_neg` rewrites this source-facing condition
into the Chapter 3 owner `is_valid_inequality`. -/
def IsNontrivialValidGeInequality
    (P : Set (Fin n → ℝ)) (γ : Fin n → ℝ) (δ : ℝ) : Prop :=
  (∀ ⦃x : Fin n → ℝ⦄, x ∈ P → δ ≤ γ ⬝ᵥ x) ∧
    ¬ ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x

/-- `IsNontrivialValidGeInequality P γ δ` means validity of `δ ≤ γ ⬝ᵥ x` on `P` together with
failure of validity on the whole nonnegative orthant. -/
theorem isNontrivialValidGeInequality_iff
    {P : Set (Fin n → ℝ)} {γ : Fin n → ℝ} {δ : ℝ} :
    IsNontrivialValidGeInequality P γ δ ↔
      (∀ ⦃x : Fin n → ℝ⦄, x ∈ P → δ ≤ γ ⬝ᵥ x) ∧
        ¬ ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x :=
  Iff.rfl

/-- `IsNontrivialValidGeInequality P γ δ` is equivalent to the Chapter 3 valid-inequality owner
for `(-γ) ⬝ᵥ x ≤ -δ`, together with failure of the original lower inequality on the whole
nonnegative orthant. -/
theorem isNontrivialValidGeInequality_iff_is_valid_inequality_neg
    {P : Set (Fin n → ℝ)} {γ : Fin n → ℝ} {δ : ℝ} :
    IsNontrivialValidGeInequality P γ δ ↔
      is_valid_inequality P (-γ) (-δ) ∧
        ¬ ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x := by
  rw [isNontrivialValidGeInequality_iff, valid_ge_inequality_iff_is_valid_inequality_neg]

namespace IsNontrivialValidGeInequality

variable {P : Set (Fin n → ℝ)} {γ : Fin n → ℝ} {δ : ℝ}

/-- A nontrivial valid lower inequality is valid on the target set. -/
theorem valid
    (h : IsNontrivialValidGeInequality P γ δ) :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ P → δ ≤ γ ⬝ᵥ x :=
  h.1

/-- A nontrivial valid lower inequality does not already hold on the whole nonnegative orthant. -/
theorem not_validOnNonnegativeOrthant
    (h : IsNontrivialValidGeInequality P γ δ) :
    ¬ ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x :=
  h.2

/-- The Chapter 3 valid-inequality owner attached to a nontrivial valid lower inequality. -/
theorem isValidInequalityNeg
    (h : IsNontrivialValidGeInequality P γ δ) :
    is_valid_inequality P (-γ) (-δ) :=
  valid_ge_inequality_iff_is_valid_inequality_neg.mp h.valid

end IsNontrivialValidGeInequality

/-- A normalized lower valid inequality on `C` rescales `δ ≤ γ ⬝ᵥ x` to
`γ' ⬝ᵥ x ≥ 1`, with `γ' = δ⁻¹ • γ` and coordinatewise nonnegative coefficients. -/
class IsNormalizedValidGeInequality
    (C : Set (Fin n → ℝ)) (γ : Fin n → ℝ) (δ : ℝ) (γ' : Fin n → ℝ) : Prop where
  eq_smul : γ' = δ⁻¹ • γ
  valid : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → 1 ≤ γ' ⬝ᵥ x
  coeff_nonneg : ∀ j : Fin n, 0 ≤ γ' j

variable (C : Set (Fin n → ℝ))
variable
  (hC_nonneg : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ j : Fin n, 0 ≤ x j)
  (hC_coordinate_ray :
    ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
      x + a • Pi.single j (1 : ℝ) ∈ C)
variable (hC_nonempty : C.Nonempty)

/-- Lemma 6.4. Assume `corner(B)` is nonempty. Every nontrivial valid inequality for `corner(B)`
can be rewritten in the form `γ' ⬝ᵥ x ≥ 1` using only the nonbasic coordinates, with
nonnegative coefficients on the nonbasic index set `N = corner_nonbasic_indices hp B`. The
normalization witness is recorded by `IsNormalizedValidGeInequality`. -/
theorem corner_polyhedron_nontrivial_valid_inequality_normal_form
    {p : ℕ}
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    (hcorner_nonempty : (corner_polyhedron hp B barA barb).Nonempty)
    (γ : Fin n → ℝ)
    (δ : ℝ)
    (hineq : IsNontrivialValidGeInequality (corner_polyhedron hp B barA barb) γ δ) :
    ∃ γ' : Fin n → ℝ,
      (∀ j ∉ corner_nonbasic_indices hp B, γ' j = 0) ∧
        IsNormalizedValidGeInequality (corner_polyhedron hp B barA barb) γ δ γ' := sorry

/-- Helper for Lemma 6.4: if all points of `C` are coordinatewise nonnegative, every coordinate
unit ray remains in `C`, and `C` is nonempty, then every nontrivial valid inequality
`δ ≤ γ ⬝ᵥ x` for `C` has positive right-hand side. -/
theorem corner_nontrivial_valid_inequality_rhs_pos
    (hC_nonneg : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ j : Fin n, 0 ≤ x j)
    (hC_coordinate_ray :
      ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
        x + a • Pi.single j (1 : ℝ) ∈ C)
    (hC_nonempty : C.Nonempty)
    (γ : Fin n → ℝ)
    (δ : ℝ)
    (hineq : IsNontrivialValidGeInequality C γ δ) :
    0 < δ := sorry

/-- Helper for Lemma 6.4: if all points of `C` are coordinatewise nonnegative, every coordinate
unit ray remains in `C`, and `C` is nonempty, then every nontrivial valid inequality for `C` can
be rescaled to the valid inequality `(δ⁻¹ • γ) ⬝ᵥ x ≥ 1`. -/
theorem corner_nontrivial_valid_inequality_normalized
    (hC_nonneg : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ j : Fin n, 0 ≤ x j)
    (hC_coordinate_ray :
      ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
        x + a • Pi.single j (1 : ℝ) ∈ C)
    (hC_nonempty : C.Nonempty)
    (γ : Fin n → ℝ)
    (δ : ℝ)
    (hineq : IsNontrivialValidGeInequality C γ δ) :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → 1 ≤ (δ⁻¹ • γ) ⬝ᵥ x := sorry

/-- Helper for Lemma 6.4: under the same hypotheses, if `C` is nonempty, every coefficient of the
rescaled vector `δ⁻¹ • γ` is nonnegative. -/
theorem corner_nontrivial_valid_inequality_normalized_nonneg
    (hC_nonneg : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ j : Fin n, 0 ≤ x j)
    (hC_coordinate_ray :
      ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
        x + a • Pi.single j (1 : ℝ) ∈ C)
    (hC_nonempty : C.Nonempty)
    (γ : Fin n → ℝ)
    (δ : ℝ)
    (hineq : IsNontrivialValidGeInequality C γ δ) :
    ∀ j : Fin n, 0 ≤ (δ⁻¹ • γ) j := sorry

end Lemma64
