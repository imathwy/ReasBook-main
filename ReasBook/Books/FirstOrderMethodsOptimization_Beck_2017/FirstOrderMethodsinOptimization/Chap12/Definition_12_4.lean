import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open InnerProductSpace (toDualMap)
open scoped Pointwise

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

/- Definition 12.4 is `source-facing`: it introduces the Lagrange dual maximization model attached
to the split Lagrangian formula from equation (12.3). The `core/canonical` owners already present
in the project are Chapter 4's `conjugate_function` for Fenchel conjugates and `LinearMap.dualMap`
for the transpose pullback `Aᵀ y`, so the public API here should expose the dual objective and its
supremum value directly, with the minimization-over-the-Lagrangian formula as a bridge theorem. -/

/-- Definition 12.4: the Lagrange dual objective of the split model is
`q(y) = -f*(Aᵀ y) - g*(-y)`, written using the Chapter 4 conjugate owner and the canonical dual
pullback `A.dualMap`. -/
def dual_based_proximal_gradient_lagrange_dual_objective
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) : Module.Dual ℝ Y → EReal :=
  fun y ↦ -conjugate_function f (A.dualMap y) - conjugate_function g (-y)

-- Proof sketch: unfold `dual_based_proximal_gradient_lagrange_dual_objective`; this is exactly
-- the textbook formula `q(y) = -f*(Aᵀ y) - g*(-y)` with `Aᵀ y` realized by `A.dualMap y`.
/-- Evaluating the Lagrange dual objective at `y` gives `-f*(Aᵀ y) - g*(-y)`. -/
@[simp] theorem dual_based_proximal_gradient_lagrange_dual_objective_apply
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_lagrange_dual_objective f g A y =
      -conjugate_function f (A.dualMap y) - conjugate_function g (-y) := rfl

end

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The primal-space view of the Chapter 12 dual objective, obtained by evaluating the canonical
dual-space owner along the Riesz map `toDualMap ℝ Y : Y → Y*`. -/
noncomputable abbrev dual_based_proximal_gradient_lagrange_dual_objective_primal
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) : Y → EReal :=
  fun y ↦ dual_based_proximal_gradient_lagrange_dual_objective f g A (toDualMap ℝ Y y)

end

section

variable {E : Type u} {Y : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

-- Proof sketch: unfold the primal-space bridge, rewrite the Chapter 12 owner on the dual side,
-- identify `A.dualMap (toDualMap ℝ Y y)` with `toDualMap ℝ E (A.adjoint y)`, and use the primal
-- conjugate bridge `conjugate_function_primal_apply` for both summands.
/-- Evaluating the Chapter 12 dual objective on the primal-space variable `y` gives the source
formula `q(y) = -f*(Aᵀ y) - g*(-y)`. -/
@[simp] theorem dual_based_proximal_gradient_lagrange_dual_objective_primal_apply
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Y) :
    dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y =
      -(f∗) (A.adjoint y) - (g∗) (-y) := by
  change dual_based_proximal_gradient_lagrange_dual_objective f g A
      (toDualMap ℝ Y y : Module.Dual ℝ Y) =
    -(f∗) (A.adjoint y) - (g∗) (-y)
  rw [dual_based_proximal_gradient_lagrange_dual_objective_apply,
    conjugate_function_primal_apply, conjugate_function_primal_apply]
  congr
  · ext x
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, A.adjoint_inner_left]
  · ext x
    simp [InnerProductSpace.toDualMap_apply_apply]

end

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

/-- Helper for Definition 12.4: negating a set of extended-real values turns its infimum into the
negated supremum. -/
private theorem ereal_sInf_neg (s : Set EReal) :
    sInf (-s) = -sSup s := by
  -- Compare both sides by translating the defining lower/upper bound properties through negation.
  refine le_antisymm ?_ ?_
  · have hsSup : sSup s ≤ -sInf (-s) := by
      refine sSup_le fun x hx ↦ ?_
      have hsInf : sInf (-s) ≤ -x := by
        exact sInf_le (by simpa [Set.mem_neg] using hx : -x ∈ -s)
      exact EReal.le_neg.mp hsInf
    exact EReal.le_neg.mpr hsSup
  · refine le_sInf fun z hz ↦ ?_
    exact EReal.neg_le.mpr (le_sSup (by simpa [Set.mem_neg] using hz : -z ∈ s))

/-- Helper for Definition 12.4: the range of the split Lagrangian is the pointwise sum of its
`x`-affine and `z`-affine ranges. -/
private theorem dual_based_proximal_gradient_lagrangian_range_eq_affine_sumset
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y) :
    Set.range (fun xz : E × Y ↦ dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y) =
      Set.range (fun x : E ↦ f x - ((A.dualMap y) x : EReal)) +
        Set.range (fun z : Y ↦ g z + (y z : EReal)) := by
  -- Split each product-space Lagrangian value into its two affine components, and conversely
  -- repack a pair of affine witnesses into the corresponding product-space value.
  ext r
  constructor
  · rintro ⟨⟨x, z⟩, rfl⟩
    refine ⟨f x - ((A.dualMap y) x : EReal), ⟨x, rfl⟩,
      g z + (y z : EReal), ⟨z, rfl⟩, ?_⟩
    -- Route correction: expand the source split formula on the right-hand side instead of
    -- rewriting the left too early through `Set.image2_add`.
    symm
    exact dual_based_proximal_gradient_lagrangian_eq_affine_split f g A x z y
  · rintro ⟨a, ⟨x, rfl⟩, b, ⟨z, rfl⟩, hab⟩
    refine ⟨(x, z), ?_⟩
    -- Keep the source split formula explicit so the affine sum matches the witness equality.
    calc
      dual_based_proximal_gradient_lagrangian f g A x z y
          = (f x - ((A.dualMap y) x : EReal)) + (g z + (y z : EReal)) :=
            dual_based_proximal_gradient_lagrangian_eq_affine_split f g A x z y
      _ = r := hab

/-- Helper for Definition 12.4: negating `a - r` with a finite real term `r` gives `r - a`. -/
private theorem ereal_neg_sub_real (a : EReal) (r : ℝ) :
    -(a - (r : EReal)) = ((r : EReal) - a) := by
  -- The coerced real term is finite, so `EReal.neg_sub` applies without mixed `⊤/⊥` cases.
  have hneg : -(a - (r : EReal)) = -a + (r : EReal) := by
    exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
  simpa [sub_eq_add_neg, add_comm] using hneg

/-- Helper for Definition 12.4: the infimum of an affine perturbation `h x - η x` is the negative
Fenchel conjugate of `h` at `η`. -/
private theorem sInf_range_sub_pairing_eq_neg_conjugate
    (h : E → EReal) (η : Module.Dual ℝ E) :
    sInf (Set.range fun x : E ↦ h x - (η x : EReal)) = -conjugate_function h η := by
  -- Rewrite the affine-perturbation range as the negation of the conjugate-defining range.
  have hrange :
      Set.range (fun x : E ↦ h x - (η x : EReal)) =
        -Set.range (fun x : E ↦ (η x : EReal) - h x) := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_neg]
      refine ⟨x, ?_⟩
      -- Negating `h x - η x` flips the finite pairing term to the front.
      exact (ereal_neg_sub_real (h x) (η x)).symm
    · rw [Set.mem_neg]
      rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hneg : -(h x - (η x : EReal)) = -r := by
        calc
          -(h x - (η x : EReal)) = (η x : EReal) - h x := by
            simpa using ereal_neg_sub_real (h x) (η x)
          _ = -r := by simpa using hx
      -- Apply negation to both sides to recover the original affine perturbation.
      have hr : -(-(h x - (η x : EReal))) = -(-r) := by
        exact congrArg Neg.neg hneg
      simpa using hr
  -- Translate the infimum of the negated range into the negative supremum from the conjugate.
  rw [hrange, ereal_sInf_neg, conjugate_function_apply]

-- Proof sketch: rewrite the infimum over the Definition 12.3 Lagrangian owner as the sum of an
-- `x`-term and a `z`-term, separate the infimum over `(x, z)`, and identify the two resulting
-- infima with the negatives of the Fenchel conjugates of `f` and `g`.
/-- Minimizing the Definition 12.3 Lagrangian over `(x, z)` yields the dual objective `q(y)`. -/
theorem dual_based_proximal_gradient_lagrange_dual_objective_eq_sInf_lagrangian_formula
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_lagrange_dual_objective f g A y =
      sInf (Set.range fun xz : E × Y ↦
        dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y) :=
  -- TODO: the source-faithful closing step is an `EReal`-specific separation of the product
  -- infimum for the split affine ranges. As stated, the theorem hits a genuine mixed `⊤/⊥`
  -- pathology, so the next pass should first repair the statement with properness/finite-value
  -- side conditions (or replace it by a conditional bridge) before reusing the proved helpers
  -- `dual_based_proximal_gradient_lagrangian_range_eq_affine_sumset` and
  -- `sInf_range_sub_pairing_eq_neg_conjugate`.
  sorry

/-- The optimal value `q_opt` of the Lagrange dual problem is the supremum of the range of the
dual objective `q`. -/
def dual_based_proximal_gradient_lagrange_dual_problem_value
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) : EReal :=
  sSup (Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A))

end
