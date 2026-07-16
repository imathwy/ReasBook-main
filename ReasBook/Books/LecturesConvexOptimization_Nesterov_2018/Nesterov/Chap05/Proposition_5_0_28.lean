import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Remark_3_1_2_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.FenchelPrimalExtension
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.RealProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient WithTopConvexAnalysis

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd

local notation "P" => ℝ × ℝ
local notation "Q" => (perspectiveCone ℝ : Set P)
local notation "perspectiveSquare" =>
  perspectiveTransform (fun y : ℝ ↦ y ^ (2 : ℕ))

/- Proposition 5.0.28 lies in the chapter's perspective-transform / effective-domain /
explicit-gradient-image domain.

Primary domain:
- the perspective transform of the scalar square function, viewed through the chapter's canonical
  `+∞`-extension owner, and the explicit image of its gradient.

Relevant owner-style declarations sampled before refinement:
- `perspectiveCone` in `Remark_3_1_2_3`, the chapter owner for the cone `τ > 0` together with the
  origin;
- `mem_perspectiveCone_iff`, the canonical membership bridge for that owner;
- `perspectiveTransform`, the chapter owner for the perspective transform on `ℝ × E`;
- `fenchelPrimalExtension` in `Chap05/FenchelPrimalExtension`, the chapter owner for extending a
  real-valued function by `⊤` away from a feasible set;
- `dom` / `withTopRealPart` from `Definition_3_3`, the chapter owners for the finite-value domain
  and its real representative;
- `Chap05RealProdL2.instInnerProductSpaceRealProd`, the chapter owner bridge that equips the raw
  pair model `ℝ × ℝ` with the canonical `L²` inner-product structure;
- mathlib `∇` / `HasGradientAt`, the canonical ambient gradient owner on the genuine
  differentiability region.

Best owner abstraction:
- source-facing: the specific perspective-square specialization of the chapter owner
  `fenchelPrimalExtension` and the explicit parabola theorem for its gradient image;
- core/canonical: `fenchelPrimalExtension`, `perspectiveCone ℝ`, `perspectiveTransform`, `dom`,
  `withTopRealPart`, and the ambient gradient on the raw pair owner `P` equipped with the
  chapter `RealProdL2` structure;
- bridge/view: the pointwise formulas on the positive cone and the effective-domain
  identification carrying the origin.

Primitive data:
- the chapter owner cone `perspectiveCone ℝ : ConvexCone ℝ P`;
- the chapter owner perspective transform specialized to `fun y : ℝ ↦ y ^ (2 : ℕ)`.

Derived API:
- the specialization `F := fenchelPrimalExtension (perspectiveCone ℝ)
    (perspectiveTransform (fun y : ℝ ↦ y ^ (2 : ℕ)))`;
- the effective-domain identification `dom F = perspectiveCone ℝ`;
- the interior-domain bridge `interior (dom F) = {z | 0 < z.1}`;
- the displayed formula for the ambient gradient on the raw pair owner `P`;
- the parabola image theorem for that actual gradient on the positive cone.

The previous version exposed a bespoke local `+∞`-extension and a totalized gradient map,
assigning an arbitrary value at the origin. That is not mathematically faithful because the origin
belongs to the effective domain but not to the differentiability region. This refinement keeps the
same textbook semantics, deletes the redundant local wrapper, reuses the chapter owners
`fenchelPrimalExtension`, `perspectiveCone`, `perspectiveTransform`, `dom`, and
`withTopRealPart`, and states the source-facing gradient theorems directly on the raw pair owner
`P` via the chapter `RealProdL2` bridge instead of exposing explicit `WithLp` transport, with the
origin appearing only in the effective-domain bridge. -/

local notation "F" =>
  fenchelPrimalExtension Q perspectiveSquare

/-- The origin belongs to the effective domain of the perspective-square extension. -/
theorem zero_mem_dom_perspectiveSquare : (0 : P) ∈ dom F := by
  exact
    ((mem_dom_fenchelPrimalExtension_iff :
      (0 : P) ∈ dom F ↔ (0 : P) ∈ Q).2 ((mem_perspectiveCone_iff).2 (Or.inr rfl)))

/-- On pairs with positive first coordinate, the canonical perspective-square extension is given
by the usual perspective formula `y² / τ`. -/
theorem perspectiveSquare_apply_of_positive_fst {z : P} (hz : 0 < z.1) :
    F z = (((z.2 ^ (2 : ℕ) / z.1 : ℝ)) : WithTop ℝ) := by
  rw [fenchelPrimalExtension_apply_of_mem]
  · have hsq :
        perspectiveSquare z = z.2 ^ (2 : ℕ) / z.1 := by
      have hz0 : z.1 ≠ 0 := hz.ne'
      rw [perspectiveTransform_apply_of_pos _ hz]
      calc
        z.1 * ((z.1⁻¹ • z.2) ^ (2 : ℕ))
            = z.1 * ((z.1⁻¹ * z.2) ^ (2 : ℕ)) := by rfl
        _ = z.1 * (z.1⁻¹ ^ (2 : ℕ) * z.2 ^ (2 : ℕ)) := by rw [mul_pow]
        _ = (z.1 * z.1⁻¹ ^ (2 : ℕ)) * z.2 ^ (2 : ℕ) := by ring
        _ = z.1⁻¹ * z.2 ^ (2 : ℕ) := by
          congr 1
          calc
            z.1 * z.1⁻¹ ^ (2 : ℕ) = (z.1 * z.1⁻¹) * z.1⁻¹ := by
              simp [pow_two]
              ring
            _ = z.1⁻¹ := by simp [hz0]
        _ = z.2 ^ (2 : ℕ) / z.1 := by rw [div_eq_mul_inv, mul_comm]
    simp [hsq]
  · exact (mem_perspectiveCone_iff).2 (Or.inl hz)

/-- The finite-value domain of the canonical perspective-square extension is exactly the chapter
owner cone `perspectiveCone ℝ`. -/
theorem perspectiveSquare_effectiveDomain :
    dom F = perspectiveCone ℝ := by
  change dom F = Q
  exact dom_fenchelPrimalExtension

/-- The differentiability region of the finite real part of the canonical perspective-square
extension is exactly the open positive cone `τ > 0`. The origin remains in `dom F`, but only as a
boundary point of the effective domain. -/
theorem perspectiveSquare_interior_effectiveDomain :
    interior (dom F) = {z : P | 0 < z.1} := by
  rw [perspectiveSquare_effectiveDomain]
  have hzero_not_mem :
      (0 : P) ∉ interior (perspectiveCone ℝ : Set P) := by
    intro hzero
    have himage :
        Prod.fst '' (perspectiveCone ℝ : Set P) = Set.Ici (0 : ℝ) := by
      ext τ
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases z with ⟨τ, x⟩
        rcases (mem_perspectiveCone_iff).1 hz with hτ | hz0
        · exact le_of_lt hτ
        · cases hz0
          have h0 : (0 : ℝ) ≤ 0 := le_rfl
          exact h0
      · intro hτ
        by_cases hτ0 : τ = 0
        · refine ⟨0, (mem_perspectiveCone_iff).2 (Or.inr rfl), ?_⟩
          simp [hτ0]
        · have hτ_pos : 0 < τ := lt_of_le_of_ne hτ (Ne.symm hτ0)
          refine ⟨(τ, 0), (mem_perspectiveCone_iff).2 (Or.inl hτ_pos), ?_⟩
          simp
    have hzero_image :
        (0 : ℝ) ∈ interior (Prod.fst '' (perspectiveCone ℝ : Set P)) :=
      isOpenMap_fst.image_interior_subset (perspectiveCone ℝ : Set P) ⟨0, hzero, rfl⟩
    rw [himage] at hzero_image
    simp at hzero_image
  have hpos_mem :
      {z : P | 0 < z.1} ⊆ interior (perspectiveCone ℝ : Set P) := by
    refine (isOpen_lt continuous_const continuous_fst).subset_interior_iff.2 ?_
    intro z hz
    exact (mem_perspectiveCone_iff).2 (Or.inl hz)
  refine subset_antisymm ?_ hpos_mem
  intro z hz
  rcases (mem_perspectiveCone_iff).1 (interior_subset hz) with hz1 | hz0
  · exact hz1
  · subst z
    exact (hzero_not_mem hz).elim

/-- On pairs with positive first coordinate, the canonical ambient gradient of the finite real
part of the perspective-square extension on the raw pair owner `P` is given by the displayed
rational formula. -/
theorem perspectiveSquare_gradient_eq_formula_of_positive_fst
    {z : P} (hz : 0 < z.1) :
    ∇ (withTopRealPart F) z =
      (-((z.2 / z.1) ^ (2 : ℕ)), (2 : ℝ) * (z.2 / z.1)) := sorry

/-- Proposition 5.0.28: the image of the gradient of the perspective-square function is the
parabola in `ℝ × ℝ` cut out by `g₁ = -(g₂)² / 4`, where the gradient is taken on the genuine
differentiability region `τ > 0`. -/
theorem perspectiveSquare_gradient_image_eq_parabola :
    (fun z : P ↦ ∇ (withTopRealPart F) z) '' {z : P | 0 < z.1} =
      {g : P | g.1 = -(g.2 ^ (2 : ℕ)) / 4} := sorry

end
