import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar
open Function

section

universe u v w

variable {Y : Type u} {Z : Type v} {α : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.7.2 is the projection-by-infimum operation in product form:
  `y ↦ inf { h(y, z) | z }`, together with its convexity preservation statement.
- `core/canonical`: the intrinsic owner for the operation itself is `Function.partialInfimum`,
  which only depends on product structure and codomain infimum; no scalar or module structure is
  part of its primitive data.
- `bridge/view`: this owner is exactly the Chapter 1 linear-image owner specialized to the first
  projection `Prod.fst : Y × Z → Y`; under module assumptions this is the same as the
  `LinearMap.fst` specialization.

Domain-style sampling used here:
- `Function.partialInfimum`;
- `Function.linearImage`;
- `Function.linearImage_eq_sInf_image`;
- `Function.isConvex_linearImage`;
- `LinearMap.fst`.

Primitive data vs derived API:
- the primitive source datum for the projection formula is the function `h : Y × Z → α`;
- the primitive owner is `Function.partialInfimum h`;
- the linear-image and convexity statements are derived bridge/specialization results.

Layer target: `source-facing`, stated at the intrinsic product level. The textbook
`R^(m+p) → R^m` coordinate statement is the specialization obtained by identifying
`R^(m+p)` with `R^m × R^p`.

Ambient minimization: the projection identity should not force scalar/module assumptions, so it is
owned at `Function.partialInfimum` through `Prod.fst`. The `LinearMap.fst` convexity clause is
kept as a bridge on the ordered-scalar `WithBotTop 𝕜` layer.
-/

namespace Function

/-- Text 5.7.2 owner: partial infimum of a function `h : Y × Z → α` along the second variable. -/
def partialInfimum [InfSet α] (h : Y × Z → α) : Y → α :=
  fun y ↦ sInf (Set.range fun z : Z ↦ h (y, z))

/-- Evaluating `partialInfimum h` at `y` gives the infimum of the `z`-slice
`z ↦ h (y, z)`. -/
@[simp] theorem partialInfimum_apply [InfSet α] (h : Y × Z → α) (y : Y) :
    partialInfimum h y = sInf (Set.range fun z : Z ↦ h (y, z)) := rfl

/-- Curried bridge for `partialInfimum`: evaluating on `Function.uncurry h` gives the infimum
of the range of the slice `h y`. -/
@[simp] theorem partialInfimum_uncurry_apply [InfSet α] (h : Y → Z → α) (y : Y) :
    partialInfimum (Function.uncurry h) y = sInf (Set.range (h y)) := by
  simp [partialInfimum_apply, Function.uncurry]

/-- Dual companion to `partialInfimum`: partial supremum of a function `h : Y × Z → α` along the
second variable. -/
def partialSupremum [SupSet α] (h : Y × Z → α) : Y → α :=
  fun y ↦ sSup (Set.range fun z : Z ↦ h (y, z))

/-- Evaluating `partialSupremum h` at `y` gives the supremum of the `z`-slice
`z ↦ h (y, z)`. -/
@[simp] theorem partialSupremum_apply [SupSet α] (h : Y × Z → α) (y : Y) :
    partialSupremum h y = sSup (Set.range fun z : Z ↦ h (y, z)) := rfl

/-- Curried bridge for `partialSupremum`: evaluating on `Function.uncurry h` gives the supremum
of the range of the slice `h y`. -/
@[simp] theorem partialSupremum_uncurry_apply [SupSet α] (h : Y → Z → α) (y : Y) :
    partialSupremum (Function.uncurry h) y = sSup (Set.range (h y)) := by
  simp [partialSupremum_apply, Function.uncurry]

end Function

section

variable {Y : Type u} {Z : Type v} {α : Type*}
variable [InfSet α]

namespace Function

-- Proof sketch: specialize `Function.linearImage_eq_sInf_image` to the canonical product
-- projection `Prod.fst`. The fiber over `y` is exactly `{(y, z) | z : Z}`, so the image of
-- `h` on that fiber is `Set.range (fun z ↦ h (y, z))`.
/-- The first-projection linear image is exactly the intrinsic owner `partialInfimum`. -/
theorem linearImage_fst_eq_partialInfimum
    (h : Y × Z → α) :
    ((Prod.fst : Y × Z → Y) ◁ h) = partialInfimum h := by
  funext y
  rw [linearImage_eq_sInf_image, partialInfimum_apply]
  congr 1
  ext a
  constructor
  · rintro ⟨⟨y', z⟩, hy, rfl⟩
    have : y' = y := by simpa using hy
    subst this
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(y, z), by simp, rfl⟩

/-- Curried bridge form of `linearImage_fst_eq_partialInfimum`. -/
theorem linearImage_fst_eq_partialInfimum_uncurry
    (h : Y → Z → α) :
    ((Prod.fst : Y × Z → Y) ◁ Function.uncurry h) =
      partialInfimum (Function.uncurry h) := by
  simpa using linearImage_fst_eq_partialInfimum (h := Function.uncurry h)

/-- Text 5.7.2 bridge formula: for the canonical projection `Y × Z → Y` onto the first factor,
the linear image value at `y` is the infimum of `h (y, z)` over `z`. -/
@[simp] theorem linearImage_fst_eq_sInf_range
    (h : Y × Z → α) (y : Y) :
    (((Prod.fst : Y × Z → Y) ◁ h) y) =
      sInf (Set.range fun z : Z ↦ h (y, z)) := by
  simpa [partialInfimum_apply] using congrFun
    (linearImage_fst_eq_partialInfimum (h := h)) y

end Function

end

section

variable {𝕜 : Type w} {Y : Type u} {Z : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [AddCommMonoid Z] [Module 𝕜 Z]

namespace Function

-- Proof sketch: apply Theorem 5.7 (2) to the canonical first-factor projection
-- `LinearMap.fst 𝕜 Y Z : Y × Z →ₗ[𝕜] Y`, then rewrite through the intrinsic
-- `Prod.fst` bridge `linearImage_fst_eq_partialInfimum`.
/-- Text 5.7.2 convexity clause in intrinsic owner form: partial infimum in the second variable
preserves convexity. -/
theorem IsConvex.partialInfimum
    (h : Y × Z → WithBotTop 𝕜) (hh : h.IsConvex 𝕜) :
    (Function.partialInfimum h).IsConvex 𝕜 := by
  have hfst : ((Prod.fst : Y × Z → Y) ◁ h).IsConvex 𝕜 := by
    simpa using (isConvex_linearImage (LinearMap.fst 𝕜 Y Z) h hh)
  have hEq : Function.partialInfimum h = ((Prod.fst : Y × Z → Y) ◁ h) := by
    simpa using (linearImage_fst_eq_partialInfimum (h := h)).symm
  exact hEq.symm ▸ hfst

/-- Curried bridge form of `IsConvex.partialInfimum`. -/
theorem IsConvex.partialInfimum_uncurry
    {h : Y → Z → WithBotTop 𝕜} (hh : (Function.uncurry h).IsConvex 𝕜) :
    (Function.partialInfimum (Function.uncurry h)).IsConvex 𝕜 := by
  exact IsConvex.partialInfimum (h := Function.uncurry h) hh

/-- Projecting a convex `WithBotTop 𝕜`-valued function on `Y × Z` by taking the infimum over the
second variable produces a convex function on `Y`, restated via the linear-image owner. -/
theorem IsConvex.linearImage_fst
    {h : Y × Z → WithBotTop 𝕜} (hh : h.IsConvex 𝕜) :
    ((LinearMap.fst 𝕜 Y Z) ◁ h).IsConvex 𝕜 := by
  simpa using (isConvex_linearImage (LinearMap.fst 𝕜 Y Z) h hh)

end Function

end
