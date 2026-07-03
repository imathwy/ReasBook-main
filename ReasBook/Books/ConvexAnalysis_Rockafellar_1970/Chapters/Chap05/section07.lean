import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_5_7_1 (from Chap01) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.7.1 names the function `Ah` from Theorem 5.7 as the image of `h`
  under `A`, and names `gA` as the inverse image of `g` under `A`.
- `core/canonical`: the chapter owner declaration for `Ah` is `Function.linearImage`; the
  inverse-image operation on functions is ordinary precomposition, written on theorem surfaces as
  `g ∘ A`.
- `bridge/view`: the only bridge needed is the direct identification of the textbook notation
  `gA` with ordinary precomposition (`(g ∘ A) x = g (A x)` via `Function.comp_apply`), together
  with the source-facing defining formula `Function.linearImage_eq_sInf_image` for `Ah`.
- Primitive data vs derived API: the primitive objects are `A`, `g`, and `h`; this item should
  reuse the existing chapter declaration and ordinary function composition rather than introduce
  a parallel alias.
- Domain-style sampling used here: `Function.linearImage`, `Function.linearImage_eq_sInf_image`,
  and `Function.comp_apply`.
- Ambient minimization: these declarations already live at the codomain-generic
  `InfSet` layer for `Ah` and the plain function-composition layer for `gA`,
  so this recall item should not reintroduce Euclidean coordinates, dimension parameters, or an
  `ℝ`-specific presentation.
- Abstraction checks:
  - codomain/ambient layer: `Ah` is already at the intrinsic `InfSet` codomain layer, so no
    `EReal`/`ℝ` specialization is introduced here;
  - scalar/ambient structure: no scalar or module assumptions are needed for this recall item;
  - owner/model choice: keep the intrinsic chapter owner `Function.linearImage` and standard
    precomposition surface `g ∘ A`, not a coordinate or model-specific wrapper;
  - topology language: not applicable for this algebraic naming item;
  - owner naming / notation: use textbook-primary notation `g ∘ A` on the source-facing bridge,
    while reusing the canonical owner theorem `Function.comp_apply`.
- Layer target: `core/canonical` plus direct source bridge; this item should recall both owners
  and defining formulas on canonical theorem surfaces rather than keep a local theorem wrapper.
-/

/- Text 5.7.1: in Theorem 5.7, the function `Ah` is the chapter declaration
`Function.linearImage A h`, called the image of `h` under `A`. -/
recall Function.linearImage

/- Text 5.7.1 also records the defining formula
`Ah(y) = inf { h(x) | A x = y }`, exposed canonically by
`Function.linearImage_eq_sInf_image`. -/
recall Function.linearImage_eq_sInf_image

/- The defining pointwise formula for that inverse image is the canonical bridge
`Function.comp_apply : (g ∘ A) x = g (A x)`. -/
recall Function.comp_apply

/-! ### Text_5_7_2 (from Chap01) -/
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

/-! ### Text_5_7_3 (from Chap01) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.7.3 states that when the linear transformation `A` is nonsingular, the
  textbook image operation `Ah` reduces to ordinary composition with the inverse map.
- `core/canonical`: the owner theorem is the chapter declaration
  `Function.linearImage_eq_comp_symm`, attached directly to `Function.linearImage`.
- `bridge/view`: nonsingularity is represented canonically by a `LinearEquiv`, and the textbook
  term `hA^{-1}` is the composite `h ∘ A.symm`.
- Primitive data vs derived API: the primitive objects are the invertible linear map `A` and the
  function `h`; the displayed equality is derived owner-level API and should be reused directly
  rather than reproved in coordinates.

Domain-style sampling used here:
- `Function.linearImage`;
- `Function.linearImage_eq_sInf_image`;
- `Function.linearImage_eq_comp_symm`;
- `LinearEquiv.apply_eq_iff_eq_symm_apply`.
- Ambient minimization: the owner theorem already lives on arbitrary modules through the
  `LinearEquiv` interface and works for any conditionally complete lattice codomain of `h`.
- Abstraction checks:
  - codomain/ambient layer: already at the canonical conditionally-complete-lattice layer;
  - scalar/space structure: no extra concrete structure beyond module data;
  - owner choice: direct reuse of `Function.linearImage_eq_comp_symm` as the canonical owner;
  - topology language: not applicable for this algebraic item;
  - notation surface: reuse the existing chapter notation/owner layer without local wrappers.
- Layer target: `core/canonical`; Text 5.7.3 is an exact owner-level identity already provided by
  the chapter theorem `Function.linearImage_eq_comp_symm`, so the main entry should stay a direct
  `recall` rather than a duplicate local theorem.
-/

/- Text 5.7.3: for an invertible linear map `A`, the textbook image operation `Ah` coincides
with composition by the inverse map, i.e. `Ah = hA^{-1}`; the owner theorem is already codomain-
generic at the conditionally-complete-lattice level. -/
recall Function.linearImage_eq_comp_symm

/-! ### Text_5_7_4 (from Chap01) -/
noncomputable section

section

variable {Y : Type*} {Z : Type*} {𝕜 : Type*}
variable [InfSet 𝕜] [Add 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.7.4 uses infimal convolution of bifunction slices
  `f y, g y : Z → 𝕜`, i.e. convolution in the `Z` variable with `y` fixed.
- `core/canonical`: the owner abstraction is the chapter declaration `infimal_convolution` on
  one-variable functions; the bifunction formulas are direct slice specializations of this owner.
- `bridge/view`: evaluation at `(y, z)` is the one-variable evaluation of
  `((f y) □ (g y)) z`, with decomposition and one-parameter formulas inherited directly from
  `Text_5_4_0`.

Domain-style sampling used here:
- the chapter owner `infimal_convolution` from `Text_5_4_0`;
- its evaluation theorem `infimal_convolution_apply`;
- its left-substitution companion `infimal_convolution_apply_neg_add`;
- its decomposition companion `infimal_convolution_eq_sInf_decompositions`;
- the codomain-level infimum `⨅ u, ...` used throughout the surrounding section;
- ordinary one-variable slices `f y` and `g y` at fixed `y`.
- Abstraction checks:
  - codomain/ambient layer: owner-generic `InfSet`/`Add` layer, not specialized to `EReal`/`ℝ`;
  - scalar/space structure: only additive structure on `Z` for the primitive layer;
  - owner choice: use canonical owner `□` on slices, with no parallel wrapper owner;
  - topology language: not applicable for this algebraic item;
  - notation surface: reuse existing chapter notation `□` directly on theorem surfaces.
- Layer target: direct slice-level reuse of `infimal_convolution`.
-/

/-- Helper for Text 5.7.4: the decomposition-value owner at `z` collects all values
`f z₁ + g z₂` coming from additive decompositions `z₁ + z₂ = z`. -/
def infimalConvolutionDecompositionValues [Add Z]
    (f g : Z → 𝕜) (z : Z) : Set 𝕜 :=
  (fun p : Z × Z ↦ f p.1 + g p.2) '' {p : Z × Z | p.1 + p.2 = z}

/-- Helper for Text 5.7.4: the one-variable infimal convolution of `f` and `g` sends `z` to the
infimum of the decomposition-value owner at `z`. -/
def infimal_convolution [Add Z] (f g : Z → 𝕜) : Z → 𝕜 :=
  fun z ↦ sInf (infimalConvolutionDecompositionValues f g z)

infixl:70 " □ " => infimal_convolution

/-- Helper for Text 5.7.4: evaluating the one-variable infimal convolution at `z` is, by
definition, the infimum of its decomposition-value owner. -/
theorem infimal_convolution_eq_sInf_decompositionValues [Add Z]
    (f g : Z → 𝕜) (z : Z) :
    (f □ g) z = sInf (infimalConvolutionDecompositionValues f g z) := rfl

/-- Helper for Text 5.7.4: under additive-group structure on `Z`, evaluating the one-variable
infimal convolution at `z` gives the one-parameter infimum `⨅ u, f u + g (-u + z)`. -/
theorem infimal_convolution_apply_neg_add [AddGroup Z]
    (f g : Z → 𝕜) (z : Z) :
    (f □ g) z = ⨅ u : Z, f u + g (-u + z) := by
  rw [infimal_convolution_eq_sInf_decompositionValues, show
    infimalConvolutionDecompositionValues f g z = Set.range (fun u : Z ↦ f u + g (-u + z)) by
      ext a
      constructor
      · rintro ⟨⟨u, v⟩, hp, rfl⟩
        refine ⟨u, ?_⟩
        have hv : v = -u + z := eq_neg_add_of_add_eq hp
        simp [hv]
      · rintro ⟨u, rfl⟩
        refine ⟨(u, -u + z), ?_, rfl⟩
        simp, sInf_range]

/-- Helper for Text 5.7.4: under additive-commutative-group structure on `Z`, evaluating the
one-variable infimal convolution at `z` gives the textbook one-parameter infimum
`⨅ u, f u + g (z - u)`. -/
@[simp] theorem infimal_convolution_apply [AddCommGroup Z]
    (f g : Z → 𝕜) (z : Z) :
    (f □ g) z = ⨅ u : Z, f u + g (z - u) := by
  simpa [sub_eq_add_neg, add_comm] using
    (infimal_convolution_apply_neg_add (f := f) (g := g) (z := z))

section DecompositionFormula

variable [Add Z]

-- Proof sketch: specialize the owner-level decomposition formula
-- `infimal_convolution_eq_sInf_decompositionValues` to the fixed slice `y`.
/-- Helper for Text 5.7.4: evaluating the slice infimal convolution at `(y, z)` is the infimum of
the canonical decomposition-value owner for the fixed slice pair `(f y, g y)`. -/
theorem infimal_convolution_slice_eq_sInf_decompositionValues
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z = sInf (infimalConvolutionDecompositionValues (f y) (g y) z) := by
  simpa using
    (infimal_convolution_eq_sInf_decompositionValues (f := f y) (g := g y) (z := z))

/-- Helper for Text 5.7.4: evaluating slice infimal convolution at `(y, z)` gives the infimum over
all decompositions `z = z₁ + z₂` of the `z`-coordinate while `y` is held fixed. -/
theorem infimal_convolution_slice_eq_sInf_decompositions
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z =
      sInf ((fun p : Z × Z ↦ f y p.1 + g y p.2) '' {p : Z × Z | p.1 + p.2 = z}) := by
  simpa [infimalConvolutionDecompositionValues] using
    (infimal_convolution_slice_eq_sInf_decompositionValues (f := f) (g := g) (y := y) (z := z))

end DecompositionFormula

section LeftSubFormula

variable [AddGroup Z]

-- Proof sketch: specialize the one-variable owner theorem
-- `infimal_convolution_apply_neg_add` to the fixed-`y` slices.
/-- Helper for Text 5.7.4: under additive-group structure on `Z`, evaluating slice infimal
convolution at `(y, z)` gives `⨅ u, f y u + g y (-u + z)`. -/
theorem infimal_convolution_slice_apply_neg_add
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z = ⨅ u : Z, f y u + g y (-u + z) := by
  simpa using infimal_convolution_apply_neg_add (f y) (g y) z

end LeftSubFormula

section SubtractionFormula

variable [AddCommGroup Z]

-- Proof sketch: this is the commutative-group specialization of the slice owner formula.
/-- Helper for Text 5.7.4: under additive-commutative-group structure on `Z`, evaluating slice
infimal convolution at `(y, z)` gives the one-parameter infimum `⨅ u, f y u + g y (z - u)`. -/
@[simp] theorem infimal_convolution_slice_apply
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z = ⨅ u : Z, f y u + g y (z - u) := by
  exact infimal_convolution_apply (f y) (g y) z

end SubtractionFormula

section PartialInfimalConvolution

variable [Add Z]

/-- Text 5.7.4: the partial infimal convolution of `f` and `g` with respect to the `z`-variable
freezes `y` and takes the ordinary infimal convolution of the corresponding `Z`-slices. -/
abbrev partial_infimal_convolution (f g : Y → Z → 𝕜) : Y → Z → 𝕜 :=
  fun y ↦ (f y) □ (g y)

/-- Helper for Text 5.7.4: evaluating the source-facing owner at a fixed `y` recovers the
canonical slice infimal convolution. -/
@[simp] theorem partial_infimal_convolution_eq_slice_owner
    (f g : Y → Z → 𝕜) (y : Y) :
    partial_infimal_convolution f g y = (f y) □ (g y) := by
  rfl

end PartialInfimalConvolution

section PartialInfimalConvolutionFormula

variable [AddCommGroup Z]

/-- Helper for Text 5.7.4: reindexing the slice infimal convolution by `u ↦ z - u` puts the
one-parameter infimum into the textbook order `f y (z - u) + g y u`. -/
theorem infimal_convolution_slice_apply_sub_right
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z = ⨅ u : Z, f y (z - u) + g y u := by
  -- Freeze `y` and start from the canonical slice formula already proved above.
  calc
    ((f y) □ (g y)) z = ⨅ u : Z, f y u + g y (z - u) := by
      exact infimal_convolution_slice_apply (f := f) (g := g) (y := y) (z := z)
    _ = ⨅ u : Z, f y (z - u) + g y u := by
      -- Reindex the infimum by the involution `u ↦ z - u`.
      let e : Z ≃ Z :=
        { toFun := fun u ↦ z - u
          invFun := fun u ↦ z - u
          left_inv := sub_sub_cancel z
          right_inv := sub_sub_cancel z }
      exact Equiv.iInf_congr e fun u ↦ by
        simp [e]

/-- Text 5.7.4: evaluating the partial infimal convolution at `(y, z)` gives the infimum over
`u` of `f y (z - u) + g y u`, i.e. infimal convolution in the `z`-variable with `y` fixed. -/
@[simp] theorem partial_infimal_convolution_apply
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    partial_infimal_convolution f g y z = ⨅ u : Z, f y (z - u) + g y u := by
  -- Unfold the source-facing owner once, then reuse the reindexed slice formula.
  rw [partial_infimal_convolution_eq_slice_owner]
  exact infimal_convolution_slice_apply_sub_right (f := f) (g := g) (y := y) (z := z)

end PartialInfimalConvolutionFormula

end

/-! ### Theorem_5_7 (from Chap01) -/
noncomputable section

universe u v w

section

variable {E : Type u} {F : Type v} {α : Type*}
variable [InfSet α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.7 has two clauses. The first says that precomposition of a convex
  function with a linear transformation preserves convexity. The second says that the textbook
  image operation `Ah`, defined by taking the infimum of `h` over the fiber `A x = y`, is convex.
- `core/canonical`: the chapter owner declarations already live upstream: `Function.IsConvex` in
  Theorem 4.2, the chapter epigraph owner `epi` from Definition 4.1, and
  `Function.verticalInfimum` together with `Function.isConvex_verticalInfimum` in Theorem 5.3.
- `bridge/view`: the second clause is proved by identifying the source-facing fiberwise infimum
  `Function.linearImage A h` with the vertical infimum of the linear image of the scalar epigraph
  of `h` under `(x, μ) ↦ (A x, μ)`.
- Primitive data vs derived API: the map `A` and the functions `g`, `h` are primitive, and
  the source-facing function `Function.linearImage A h` and the bridge set
  `Function.linearImageEpigraph A h` are the new public objects here; the convexity assertions
  and the owner-side identification with `Function.verticalInfimum` are derived consequences of
  the upstream owner declarations.
- Ambient minimization: the owner `Function.linearImage` itself lives on arbitrary maps with only
  codomain infimum structure, while the convexity clauses keep the linear/module assumptions they
  actually use. No coordinates, Euclidean structure, or finite dimensionality enter these public
  declarations, and the textbook `R^n → R^m` presentation is treated as a specialization.

Domain-style sampling used here:
- `Function.IsConvex`;
- `epi`;
- `Function.verticalInfimum`;
- `Function.linearImageEpigraph`;
- `Function.IsConvex.comp_linearMap`;
- `Convex.linear_preimage`;
- `Convex.linear_image`;
- `LinearMap.prodMap`;
- `Function.isConvex_verticalInfimum`.
- Layer target: `source-facing` for the public declarations `Function.linearImage`,
  `Function.IsConvex.comp_linearMap`, and `Function.isConvex_linearImage`; `bridge/view` for the
  public set `Function.linearImageEpigraph A h` and the identification of `Function.linearImage A h`
  with the owner-side `Function.verticalInfimum` of that image set.
-/

namespace Function

/-- The textbook operation `Ah` attached to a map `A : E → F` and a function `h` on `E`,
obtained by taking the infimum of `h` along each fiber `{x | A x = y}`.
The source's extended-real-valued `R^n → R^m` case is a specialization.
Empty fibers contribute `sInf ∅` in the codomain. -/
def linearImage (A : E → F) (h : E → α) : F → α :=
  fun y ↦ sInf (h '' {x : E | A x = y})

end Function

end

scoped[Rockafellar] infixr:65 " ◁ " => Function.linearImage

open scoped Rockafellar
open Function

section

variable {𝕜 : Type w} {E : Type u} {F : Type v}
variable [LE 𝕜]

namespace Function

/-- Intrinsic epigraph-side relation for `Function.linearImage A h`: a pair `(y, μ)` belongs to
`linearImageEpigraph A h` iff some fiber point `x` with `A x = y` satisfies `h x ≤ μ`. -/
def linearImageEpigraph (A : E → F) (h : E → WithBotTop 𝕜) : Set (F × 𝕜) :=
  {p : F × 𝕜 | ∃ x : E, A x = p.1 ∧ h x ≤ (p.2 : WithBotTop 𝕜)}

/-- Membership in `linearImageEpigraph A h` means that some point of the fiber `A x = y`
has `h`-value at most the displayed scalar height. -/
theorem mem_linearImageEpigraph_iff
    (A : E → F) (h : E → WithBotTop 𝕜) {y : F} {μ : 𝕜} :
    (y, μ) ∈ linearImageEpigraph A h ↔ ∃ x : E, A x = y ∧ h x ≤ (μ : WithBotTop 𝕜) :=
  Iff.rfl

/-- Bridge to the concrete map-image view: `linearImageEpigraph A h` is exactly the image of
`epi h` under `(x, μ) ↦ (A x, μ)`. -/
theorem linearImageEpigraph_eq_image_epi_map
    (A : E → F) (h : E → WithBotTop 𝕜) :
    linearImageEpigraph A h = (fun p : E × 𝕜 ↦ (A p.1, p.2)) '' epi h := by
  ext p
  rcases p with ⟨y, μ⟩
  constructor
  · rintro ⟨x, hAy, hxμ⟩
    refine ⟨(x, μ), ?_, ?_⟩
    · exact mem_epi_restrict_iff.mpr ⟨by simp, hxμ⟩
    simp [hAy]
  · rintro ⟨⟨x, r⟩, hp, hxy⟩
    rcases mem_epi_restrict_iff.mp hp with ⟨_, hxr⟩
    rcases Prod.mk.inj hxy with ⟨hAy, hrμ⟩
    subst hrμ
    exact ⟨x, hAy, hxr⟩

section LinearMapBridge

variable [Semiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

/-- Linear-map specialization of `linearImageEpigraph_eq_image_epi_map`. -/
theorem linearImageEpigraph_eq_image_epi
    (A : E →ₗ[𝕜] F) (h : E → WithBotTop 𝕜) :
    linearImageEpigraph A h = (A.prodMap LinearMap.id) '' epi h := by
  simpa [LinearMap.prodMap_apply] using
    (linearImageEpigraph_eq_image_epi_map (A := (A : E → F)) (h := h))

end LinearMapBridge

end Function

end

section

variable {E : Type u} {F : Type v} {α : Type*}
variable [InfSet α]

namespace Function

-- Proof sketch: unfold `Function.linearImage` and `Function.verticalInfimum`. A point `(y, μ)` lies
-- in the displayed image exactly when there exists `x` with `A x = y` and `(x, μ)` in the scalar
-- epigraph of `h`, i.e. `h x ≤ μ`. Taking the infimum over those heights is the same as taking
-- the infimum of the fiber values `h x`.
/-- The value of `Function.linearImage A h` at `y` is the infimum of the values `h x` over the
fiber `A x = y`, in the textbook sense of `Ah(y) = inf {h(x) | A x = y}`. -/
theorem linearImage_eq_sInf_image (A : E → F) (h : E → α) (y : F) :
    (A ◁ h) y = sInf (h '' {x : E | A x = y}) := rfl

end Function

end

section

variable {E : Type u} {F : Type v} {α : Type*}
variable [ConditionallyCompleteLattice α]

namespace Function

-- Proof sketch: for an equivalence `A`, the fiber `{x | A x = y}` is the singleton
-- `{A.symm y}`. The source-facing fiberwise infimum defining `Function.linearImage` therefore
-- collapses to the singleton infimum `h (A.symm y)`, which is exactly composition by `A.symm`.
/-- For an invertible map `A`, the textbook image operation `Ah` is just composition with
the inverse map. -/
theorem linearImage_eq_comp_symm
    (A : E ≃ F) (h : E → α) :
    (A ◁ h) = h ∘ A.symm := by
  funext y
  rw [linearImage_eq_sInf_image]
  have hfiber : {x : E | A x = y} = {A.symm y} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    simpa using (A.apply_eq_iff_eq_symm_apply : A x = y ↔ x = A.symm y)
  rw [hfiber, Set.image_singleton, csInf_singleton]
  simp [Function.comp]

end Function

end

section

variable {𝕜 : Type w} {E : Type u} {F : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

-- Proof sketch: view the scalar epigraph of `g ∘ A` as the preimage of the scalar epigraph of `g`
-- under the linear map `(x, μ) ↦ (A x, μ)`. Since linear preimages of convex sets are convex, the
-- epigraph criterion from Theorem 4.2 gives convexity of `g ∘ A`.
namespace Function

/-- Theorem 5.7 (1): if `A : E → F` is linear and `g` is convex on `F`, then the composite `gA`,
defined by `x ↦ g (A x)`, is convex on `E`. The textbook `R^n → R^m` statement is the Euclidean
specialization. -/
theorem IsConvex.comp_linearMap
    {g : F → WithBotTop 𝕜} (hg : g.IsConvex 𝕜) (A : E →ₗ[𝕜] F) :
    (g ∘ A).IsConvex 𝕜 := by
  rw [isConvex_iff_convex_epigraph]
  simpa [LinearMap.prodMap_apply] using
    hg.convex_epigraph.linear_preimage (A.prodMap LinearMap.id)

end Function

end

section

variable {𝕜 : Type w} {E : Type u} {F : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [NoBotOrder 𝕜]

/-- The image function `Ah` is the vertical-infimum function of the image of the scalar epigraph
of `h` under `(x, μ) ↦ (A x, μ)`. -/
theorem Function.linearImage_eq_verticalInfimum_linearImageEpigraph
    (A : E → F) (h : E → WithBotTop 𝕜) :
    A ◁ h = verticalInfimum (linearImageEpigraph A h) := by
  ext y
  rw [Function.linearImage_eq_sInf_image, verticalInfimum_eq_sInf]
  set T : Set (WithBotTop 𝕜) :=
    (((↑) : 𝕜 → WithBotTop 𝕜) '' {μ : 𝕜 | (y, μ) ∈ linearImageEpigraph A h})
  apply le_antisymm
  · refine le_sInf ?_
    rintro _ ⟨μ, hμ, rfl⟩
    rcases (mem_linearImageEpigraph_iff A h).1 hμ with ⟨x, hAy, hxμ⟩
    exact
      (sInf_le (show h x ∈ h '' {x : E | A x = y} from ⟨x, hAy, rfl⟩)).trans hxμ
  · refine le_sInf ?_
    rintro _ ⟨x, hAy, rfl⟩
    by_cases hbot : h x = (⊥ : WithBotTop 𝕜)
    · have hall : ∀ μ : 𝕜, (μ : WithBotTop 𝕜) ∈ T := by
        intro μ
        exact ⟨μ, (mem_linearImageEpigraph_iff A h).2 ⟨x, hAy, by simp [hbot]⟩, rfl⟩
      have hlt :
          ∀ a : 𝕜, sInf T < a := by
        intro a
        letI : NoMinOrder 𝕜 := NoBotOrder.to_noMinOrder 𝕜
        rcases exists_lt a with ⟨b, hb⟩
        exact lt_of_le_of_lt
          (sInf_le (hall b))
          (WithBotTop.coe_lt_coe_iff.mpr hb)
      have hsInf_eq_bot :
          sInf T = (⊥ : WithBotTop 𝕜) :=
        (WithBotTop.eq_bot_iff_forall_lt (x := sInf T)).2 hlt
      simpa [hbot] using hsInf_eq_bot.le
    · by_cases htop : h x = (⊤ : WithBotTop 𝕜)
      · simp [htop]
      · lift h x to 𝕜 using ⟨htop, hbot⟩ with r hr
        have hyr : (r : WithBotTop 𝕜) ∈ T := by
          exact ⟨r, (mem_linearImageEpigraph_iff A h).2 ⟨x, hAy, by simp [hr]⟩, rfl⟩
        have hsInf_le : sInf T ≤ r := sInf_le hyr
        simpa [hr] using hsInf_le

namespace Function

section

variable {𝕜 : Type w} {E : Type u} {F : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

-- Proof sketch: take the scalar epigraph `{(x, μ) | h x ≤ μ}` of `h` and apply the linear map
-- `(x, μ) ↦ (A x, μ)`. Its image is convex by `Convex.linear_image`, and
-- `Function.linearImage A h` agrees pointwise with the resulting vertical-infimum function. Then
-- apply `Function.isConvex_verticalInfimum`.
/-- Theorem 5.7 (2): if `A : E → F` is linear and `h` is convex on `E`, then the function `Ah`,
defined by `Ah(y) = inf {h(x) | A x = y}`, is convex on `F`. The textbook `R^n → R^m` statement
is the Euclidean specialization. -/
theorem isConvex_linearImage
    (A : E →ₗ[𝕜] F) (h : E → WithBotTop 𝕜) (hh : h.IsConvex 𝕜) :
    (A ◁ h).IsConvex 𝕜 := by
  rw [Function.linearImage_eq_verticalInfimum_linearImageEpigraph]
  have hlin : Convex 𝕜 (linearImageEpigraph A h) := by
    simpa [linearImageEpigraph_eq_image_epi, epi_univ_eq_setOf_le] using
      hh.convex_epigraph.linear_image (A.prodMap LinearMap.id)
  exact Function.isConvex_verticalInfimum hlin

end

end Function

end
