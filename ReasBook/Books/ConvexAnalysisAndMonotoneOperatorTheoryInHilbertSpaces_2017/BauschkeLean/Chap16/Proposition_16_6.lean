import Mathlib
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u v

namespace ContinuousLinearMap

section SetValuedOperatorCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The set-valued operator `L^* ∘ B ∘ L`, sending `x` to the adjoint image of `B (L x)`. -/
def adjointImage
    (L : H →L[ℝ] K) (B : SetValuedOperator K K) : SetValuedOperator H H :=
  fun x ↦ L.adjoint '' (B (L x))

/-- Evaluating `ContinuousLinearMap.adjointImage L B` gives the adjoint image of `B (L x)`. -/
@[simp] theorem adjointImage_apply
    (L : H →L[ℝ] K) (B : SetValuedOperator K K) (x : H) :
    L.adjointImage B x = L.adjoint '' (B (L x)) :=
  rfl

end SetValuedOperatorCalculus

end ContinuousLinearMap

namespace ERealFunction

noncomputable section

section SubdifferentialBasicProperties

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 16 6: the reciprocal of a positive real is still positive. -/
private theorem posReal_inv_pos (γ : PosReal) : 0 < (γ : ℝ)⁻¹ := by
  -- The reciprocal of a strictly positive real stays strictly positive.
  exact inv_pos.mpr γ.2

/-- Helper for Proposition 16 6: the auxiliary reciprocal positive real used to undo positive
scaling. -/
private def posRealInv (γ : PosReal) : PosReal :=
  ⟨(γ : ℝ)⁻¹, posReal_inv_pos γ⟩

/-- Helper for Proposition 16 6: the auxiliary reciprocal cancels `γ` on the left. -/
@[simp] private theorem posRealInv_mul (γ : PosReal) :
    ((posRealInv γ : ℝ) * (γ : ℝ)) = 1 := by
  -- Rewrite the auxiliary reciprocal to the ordinary real inverse.
  simpa [posRealInv] using inv_mul_cancel₀ γ.2.ne'

/-- Helper for Proposition 16 6: the auxiliary reciprocal cancels `γ` on the right. -/
@[simp] private theorem mul_posRealInv (γ : PosReal) :
    ((γ : ℝ) * (posRealInv γ : ℝ)) = 1 := by
  -- This is the commuted real inverse identity.
  simpa [posRealInv] using mul_inv_cancel₀ γ.2.ne'

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16 6: scaling by `γ` and then by its reciprocal recovers the original
function. -/
@[simp] private theorem posRealInv_smul_posReal_smul
    (γ : PosReal) (f : H → Set.Ioi (⊥ : EReal)) :
    (posRealInv γ • (γ • f) : H → Set.Ioi (⊥ : EReal)) = f := by
  funext x
  apply Subtype.ext
  -- Rewrite both positive-real actions to ordinary `EReal` multiplication and cancel the scalar.
  calc
    (((posRealInv γ) • (γ • f)) x : EReal)
        = (posRealInv γ : EReal) * ((γ : EReal) * (f x : EReal)) := by
            rw [posReal_smul_apply, posReal_smul_apply]
    _ = (((posRealInv γ : ℝ) * (γ : ℝ) : ℝ) : EReal) * (f x : EReal) := by
          rw [← mul_assoc, ← EReal.coe_mul]
    _ = (f x : EReal) := by
          simp [posRealInv_mul]

/-- Helper for Proposition 16 6: positive scaling sends a subgradient of `f` at `x` to a
subgradient of `γ • f` at `x`. -/
private theorem smul_mem_subdifferential_posReal_smul
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) {x u : H}
    (hu : u ∈ (∂ f) x) :
    (γ : ℝ) • u ∈ (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) x := by
  rw [mem_subdifferential_iff] at hu ⊢
  intro y
  have hγ_nonneg : (0 : EReal) ≤ (γ : EReal) := EReal.coe_nonneg.mpr γ.2.le
  have hγ_ne_top : (γ : EReal) ≠ ⊤ := EReal.coe_ne_top (γ : ℝ)
  have hscaled :
      (γ : EReal) * ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) ≤
        (γ : EReal) * (f y : EReal) := by
    -- Multiply the defining affine-minorant inequality by the positive scalar.
    exact mul_le_mul_of_nonneg_left (hu y) hγ_nonneg
  calc
    (⟪y - x, (γ : ℝ) • u⟫_ℝ : EReal) + ((γ • f) x : EReal)
        = (γ : EReal) * ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) := by
            -- Normalize the scaled inner product and the scaled function value.
            rw [inner_smul_right, posReal_smul_apply, EReal.coe_mul]
            rw [← EReal.left_distrib_of_nonneg_of_ne_top hγ_nonneg hγ_ne_top]
    _ ≤ (γ : EReal) * (f y : EReal) := hscaled
    _ = ((γ • f) y : EReal) := by
          rw [posReal_smul_apply]

-- Proof sketch: unfold membership in both subdifferentials and rewrite the affine-minorant
-- inequality for the canonical positive-real scalar action on `]-∞,+∞]`-valued functions;
-- dividing by the positive scalar identifies witnesses on the two sides.
/-- Proposition 16 6 (1): the subdifferential of a positive scalar multiple is the corresponding
positive scalar multiple of the subdifferential. -/
theorem subdifferential_posReal_smul_eq_smul
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) :
    ∂ ((γ • f : H → Set.Ioi (⊥ : EReal))) = (γ : ℝ) • (∂ f : SetValuedOperator H H) := by
  ext x u
  constructor
  · intro hu
    have hscaledBack :
        ((posRealInv γ : ℝ) • u) ∈ (∂ f) x := by
      -- Apply the forward-scaling lemma to the reciprocal scalar and cancel the function scaling.
      have hscaled :=
        smul_mem_subdifferential_posReal_smul
          (f := (γ • f : H → Set.Ioi (⊥ : EReal))) (γ := posRealInv γ) (u := u) (x := x) hu
      rw [posRealInv_smul_posReal_smul] at hscaled
      exact hscaled
    -- Rewrite scalar-set membership through inverse scaling instead of repackaging a witness.
    change u ∈ (γ : ℝ) • ((∂ f) x)
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne']
    simpa [posRealInv] using hscaledBack
  · intro hu
    change u ∈ (γ : ℝ) • ((∂ f) x) at hu
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hu
    -- The forward scaling helper closes the remaining direction after undoing the scalar.
    simpa [smul_smul, posRealInv, mul_inv_cancel₀ γ.2.ne'] using
      (smul_mem_subdifferential_posReal_smul
        (f := f) (γ := γ) (u := ((γ : ℝ)⁻¹ • u)) (x := x) hu)

end SubdifferentialBasicProperties

namespace ContinuousLinearMap

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The set-valued operator `L^* ∘ (∂ g) ∘ L`, sending `x` to the adjoint image of the
subdifferential of `g` at `L x`. This is the specialization of
`ContinuousLinearMap.adjointImage` to the subdifferential of `g`. -/
abbrev adjointImageSubdifferential
    (L : H →L[ℝ] K) (g : K → Set.Ioi (⊥ : EReal)) : SetValuedOperator H H :=
  L.adjointImage (∂ g)

/-- Evaluating `ContinuousLinearMap.adjointImageSubdifferential L g` gives the adjoint image of
the subdifferential of `g` at `L x`. -/
@[simp] theorem adjointImageSubdifferential_apply
    (L : H →L[ℝ] K) (g : K → Set.Ioi (⊥ : EReal)) (x : H) :
    ContinuousLinearMap.adjointImageSubdifferential L g x = L.adjoint '' ((∂ g) (L x)) :=
  _root_.ContinuousLinearMap.adjointImage_apply L (∂ g) x

/-- Helper for Proposition 16 6: the inner product against a subtracted image under `L`
rewrites through the adjoint of `L`. -/
theorem adjoint_inner_sub_eq
    (L : H →L[ℝ] K) (x y : H) (v : K) :
    ⟪L y - L x, v⟫_ℝ = ⟪y - x, L.adjoint v⟫_ℝ := by
  -- Rewrite the image difference as `L (y - x)` and apply the adjoint identity once.
  simpa [ContinuousLinearMap.map_sub] using
    (ContinuousLinearMap.adjoint_inner_right L (y - x) v).symm

end SubdifferentialCalculus

end ContinuousLinearMap

section SubdifferentialBasicProperties

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for Proposition 16 6: adding a subgradient of `f` at `x` to the adjoint of a
subgradient of `g` at `L x` yields a subgradient of `f + g ∘ L` at `x`. -/
private theorem add_adjoint_subgradient_mem_subdifferential_add_comp
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (x u : H) (v : K)
    (hu : u ∈ (∂ f) x) (hv : v ∈ (∂ g) (L x)) :
    u + L.adjoint v ∈ (∂ (f + g ∘ L)) x := by
  rw [mem_subdifferential_iff] at hu hv ⊢
  intro y
  have hfy : (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := hu y
  have hgy :
      (⟪y - x, L.adjoint v⟫_ℝ : EReal) + (g (L x) : EReal) ≤ (g (L y) : EReal) := by
    -- Evaluate the subgradient inequality for `g` at `L y` and transport it back with the adjoint.
    simpa [Function.comp_apply,
      ContinuousLinearMap.adjoint_inner_sub_eq (L := L) (x := x) (y := y) (v := v)] using hv (L y)
  have hsum := add_le_add hfy hgy
  -- Normalize the left side to the sum of the two affine-minorant inequalities.
  calc
    (⟪y - x, u + L.adjoint v⟫_ℝ : EReal) + ((f + g ∘ L) x : EReal)
        = (((⟪y - x, u⟫_ℝ : EReal) + (⟪y - x, L.adjoint v⟫_ℝ : EReal)) +
            ((f x : EReal) + (g (L x) : EReal))) := by
              rw [inner_add_right, EReal.coe_add, add_apply, Function.comp_apply]
    _ = ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) +
          ((⟪y - x, L.adjoint v⟫_ℝ : EReal) + (g (L x) : EReal)) := by
            simp [add_assoc, add_left_comm, add_comm]
    _ ≤ (f y : EReal) + (g (L y) : EReal) := hsum
    _ = ((f + g ∘ L) y : EReal) := by
          simp [add_apply, Function.comp_apply]

-- Proof sketch: if `u ∈ (∂ f) x` and `v ∈ (∂ g) (L x)`, combine the two subgradient inequalities;
-- rewrite the second one with the adjoint identity
-- `⟪L y - L x, v⟫ = ⟪y - x, L.adjoint v⟫` to obtain the defining inequality for
-- `u + L.adjoint v ∈ ∂ (f + g ∘ L) x`.
/-- Part (2) of Proposition 16 6: if the effective domain of `g` meets the image under `L` of the
effective domain of `f`, then every sum of a subgradient of `f` at `x` and the adjoint image of a
subgradient of `g` at `L x` is a subgradient of `f + g ∘ L` at `x`. -/
theorem subdifferential_add_adjoint_image_subset_subdifferential_add_comp
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (x : H) :
    (∂ f) x + ContinuousLinearMap.adjointImageSubdifferential L g x ⊆
      (∂ (f + g ∘ L)) x := by
  intro w hw
  rcases Set.mem_add.mp hw with ⟨u, hu, w', hw', rfl⟩
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image] at hw'
  rcases hw' with ⟨v, hv, rfl⟩
  -- The pointwise closing helper is exactly the desired inclusion after unpacking the witnesses.
  exact add_adjoint_subgradient_mem_subdifferential_add_comp f g L x u v hu hv

end SubdifferentialBasicProperties

end

end ERealFunction
