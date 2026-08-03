import Mathlib
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap16.Proposition_16_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u v

namespace Function

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Helper for Proposition 20.10: the field-notation bridge expressing monotonicity for a
set-valued operator `X → Set X`. -/
abbrev IsMonotone (A : X → Set X) : Prop :=
  ∀ ⦃x u y v : X⦄, u ∈ A x → v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ

end Function

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: rewrite membership in `A⁻¹` with `SetValuedOperator.mem_inverse_iff`. The
-- monotonicity inequality for `A⁻¹` is then exactly the monotonicity inequality for `A`
-- with the graph coordinates exchanged.
/-- First part of Proposition 20.10: the inverse of a monotone set-valued operator on a real
Hilbert space
is monotone. -/
theorem IsMonotone.inverse {A : SetValuedOperator H H} (hA : A.IsMonotone) :
    A⁻¹.IsMonotone := by
  -- Translate inverse membership back to `A`.
  intro x u y v hx hy
  rw [SetValuedOperator.mem_inverse_iff] at hx hy
  -- Apply monotonicity of `A` to the swapped graph points and commute the real inner product.
  simpa [real_inner_comm] using hA hx hy

/-- Helper for Proposition 20.10: pulling a common nonnegative scalar out of the second slot of
the monotonicity pairing. -/
private theorem inner_sub_smul_sub_eq {x y u v : H} (γ : NNReal) :
    ⟪x - y, γ • u - γ • v⟫_ℝ = (γ : ℝ) * ⟪x - y, u - v⟫_ℝ := by
  -- Factor the scalar through the difference before using linearity of the inner product.
  calc
    ⟪x - y, γ • u - γ • v⟫_ℝ = ⟪x - y, γ • (u - v)⟫_ℝ := by
      rw [smul_sub]
    _ = (γ : ℝ) * ⟪x - y, u - v⟫_ℝ := by
      simpa using real_inner_smul_right (x - y) (u - v) (γ : ℝ)

-- Proof sketch: unpack membership in the scaled operator `γ • A`. The witnesses are scaled by
-- the nonnegative scalar `(γ : ℝ)`, so the monotonicity pairing is the original pairing for `A`
-- multiplied by `(γ : ℝ)`.
/-- Second part of Proposition 20.10: every nonnegative scalar multiple of a monotone
set-valued operator on a real Hilbert space is monotone. -/
theorem IsMonotone.smul {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : NNReal) :
    (γ • A).IsMonotone := by
  -- Unpack the scaled-set witnesses pointwise.
  intro x u y v hu hv
  rcases Set.mem_smul_set.mp hu with ⟨u', hu', rfl⟩
  rcases Set.mem_smul_set.mp hv with ⟨v', hv', rfl⟩
  have hmono : 0 ≤ ⟪x - y, u' - v'⟫_ℝ := hA hu' hv'
  -- Normalize the scaled pairing so monotonicity of `A` can be multiplied by `γ`.
  rw [inner_sub_smul_sub_eq]
  exact mul_nonneg γ.2 hmono

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Helper for Proposition 20.10: the mixed pairing for `a + L.adjoint p` and `b + L.adjoint q`
splits into the `A`-part and the transported `B`-part. -/
private theorem inner_sub_add_adjoint_sub_eq
    [CompleteSpace H] [CompleteSpace K]
    (L : H →L[ℝ] K) {x y a b : H} {p q : K} :
    ⟪x - y, (a + L.adjoint p) - (b + L.adjoint q)⟫_ℝ =
      ⟪x - y, a - b⟫_ℝ + ⟪L x - L y, p - q⟫_ℝ := by
  have hsplit :
      (a + L.adjoint p) - (b + L.adjoint q) = (a - b) + L.adjoint (p - q) := by
    -- Rearrange the pointwise difference and use linearity of the adjoint.
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Split the pairing into its `A` contribution and the adjoint-transported `B` contribution.
  calc
    ⟪x - y, (a + L.adjoint p) - (b + L.adjoint q)⟫_ℝ
        = ⟪x - y, a - b⟫_ℝ + ⟪x - y, L.adjoint (p - q)⟫_ℝ := by
            rw [hsplit, inner_add_right]
    _ = ⟪x - y, a - b⟫_ℝ + ⟪L (x - y), p - q⟫_ℝ := by
          rw [(ContinuousLinearMap.adjoint_inner_right L (x - y) (p - q)).symm]
    _ = ⟪x - y, a - b⟫_ℝ + ⟪L x - L y, p - q⟫_ℝ := by
          simp [ContinuousLinearMap.map_sub]

/-- Helper for Proposition 20.10: membership in `L.adjointImage B x` is witnessed by an element
of `B (L x)` whose adjoint image is the given vector. -/
private theorem mem_adjointImage_iff_exists
    [CompleteSpace H] [CompleteSpace K]
    (L : H →L[ℝ] K) {B : SetValuedOperator K K} {x : H} {u : H} :
    u ∈ L.adjointImage B x ↔ ∃ p ∈ B (L x), L.adjoint p = u := by
  -- Expand `adjointImage` pointwise and then unpack set membership in the image.
  rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image]

-- Proof sketch: write elements of the sum operator as `uA + L.adjoint uB` and
-- `vA + L.adjoint vB`, with `uA ∈ A x`, `vA ∈ A y`, `uB ∈ B (L x)`, and `vB ∈ B (L y)`. Expand
-- the monotonicity pairing and use the adjoint identity
-- `⟪x - y, L.adjoint (uB - vB)⟫_ℝ = ⟪L x - L y, uB - vB⟫_ℝ` together with monotonicity of `A`
-- and `B`.
/-- Third part of Proposition 20.10: if `A` and `B` are monotone set-valued operators on real
Hilbert spaces and `L : H →L[ℝ] K` is bounded linear, then `A + L^* ∘ B ∘ L`, realized as
`A + L.adjointImage B`, is monotone. -/
theorem IsMonotone.add_adjointImage
    [CompleteSpace H] [CompleteSpace K]
    {A : SetValuedOperator H H} (hA : A.IsMonotone)
    (L : H →L[ℝ] K) {B : SetValuedOperator K K} (hB : B.IsMonotone) :
    (A + L.adjointImage B).IsMonotone := by
  -- Decompose the pointwise sum into witnesses from `A` and `B`.
  intro x u y v hu hv
  rcases Set.mem_add.mp hu with ⟨a, ha, uL, huL, rfl⟩
  rcases Set.mem_add.mp hv with ⟨b, hb, vL, hvL, rfl⟩
  -- Replace adjoint-image membership by explicit witnesses in `B`.
  rw [mem_adjointImage_iff_exists (L := L)] at huL hvL
  rcases huL with ⟨p, hp, rfl⟩
  rcases hvL with ⟨q, hq, rfl⟩
  have hmonoA : 0 ≤ ⟪x - y, a - b⟫_ℝ := hA ha hb
  have hmonoB : 0 ≤ ⟪L x - L y, p - q⟫_ℝ := hB hp hq
  -- Rewrite the combined pairing as the sum of the monotonicity pairings for `A` and `B`.
  rw [inner_sub_add_adjoint_sub_eq (L := L)]
  exact add_nonneg hmonoA hmonoB

/-- Proposition 20.10. If `A` and `B` are monotone set-valued operators on real Hilbert spaces,
then `A⁻¹`, `γ • A`, and `A + L.adjointImage B` are monotone. -/
theorem IsMonotone.inverse_smul_add_adjointImage
    [CompleteSpace H] [CompleteSpace K]
    {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : NNReal)
    (L : H →L[ℝ] K) {B : SetValuedOperator K K} (hB : B.IsMonotone) :
    A⁻¹.IsMonotone ∧ (γ • A).IsMonotone ∧ (A + L.adjointImage B).IsMonotone := by
  -- Assemble the three clause theorems into the single textbook statement for this item.
  constructor
  · exact SetValuedOperator.IsMonotone.inverse hA
  constructor
  · exact SetValuedOperator.IsMonotone.smul hA γ
  · exact SetValuedOperator.IsMonotone.add_adjointImage hA L hB

end SetValuedOperator
