import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_3_4_0 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 3.4.0 introduces the image `AC` and inverse image `A⁻¹D` of subsets under
  a map (in the source text, a linear transformation).
- `core/canonical`: the owner abstraction is the ordinary function-level set API `Set.image` and
  `Set.preimage`; a linear map is used only through its coercion to a function.
- `bridge/view`: the textbook formulas `AC = {Ax | x ∈ C}` and `A⁻¹D = {x | Ax ∈ D}` are exactly
  the standard notations `A '' C` and `A ⁻¹' D`, together with the canonical membership bridge
  theorems `Set.mem_image` and `Set.mem_preimage`.
- Primitive data vs derived API: the map `A` and the sets `C` and `D` are primitive; image and
  inverse image are direct canonical set constructions.
- Domain-style sampling: the sampled owner declarations are `Set.image`, `Set.preimage`,
  `Set.mem_image`, and `Set.mem_preimage` from `Mathlib.Data.Set.Operations`. On the project side,
  `Text_1_2`, `Text_3_1_4`, and `Text_3_1_6` show the same exact-recall owner-reuse pattern,
  while `Theorem_3_4` and `Text_3_4_2` consume this file through the same canonical set
  image/preimage notation.
- Layer target: `core/canonical`; the source text is only recalling the standard image/preimage
  constructions, so the main public entries remain direct `recall`s of the owner declarations and
  their atomic membership bridges.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the codomain fully generic (`α → β`), since only set image/preimage
  is used.
- Scalar/ambient-structure check: no scalar/topological/linear structure is mathematically
  primitive in this item, so none is exposed.
- Owner check: keep canonical `Set.image` and `Set.preimage`; linear maps are downstream
  specializations via coercions to functions.
- Topology check: this item is not topology-facing, so no intrinsic/relative topology refactor is
  applicable.
- Owner-name and notation check: use short canonical owners and textbook-primary notation
  (`f '' C`, `f ⁻¹' D`) directly on the owner theorems.
-/

/- Text 3.4.0: for a map `f` (hence in particular for linear transformations via coercion),
the textbook formulas `f(C) = {f x | x ∈ C}` and `f⁻¹(D) = {x | f x ∈ D}` are the canonical set
image and preimage constructions, written `f '' C` and `f ⁻¹' D`; the owner declarations are
`Set.image` and `Set.preimage`. -/
recall Set.image

/- The inverse-image notation `f⁻¹(D) = {x | f x ∈ D}` is the canonical set preimage
`Set.preimage`, written `f ⁻¹' D`. -/
recall Set.preimage

/- The textbook set-builder description `{f x | x ∈ C}` is the canonical membership bridge theorem
`Set.mem_image`. -/
recall Set.mem_image

/- The textbook set-builder description `{x | f x ∈ D}` is the canonical membership bridge theorem
`Set.mem_preimage`. -/
recall Set.mem_preimage

/-! ### Corollary_3_4_1 (from Chap01) -/
universe u v w x

section LinearImageCompatibleSmul

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {𝕜 : Type v} [Semiring 𝕜]
variable {E : Type w} [AddCommMonoid E] [Module 𝕜 E] [SMul R E]
variable {F : Type x} [AddCommMonoid F] [Module 𝕜 F] [SMul R F]
variable [LinearMap.CompatibleSMul E F R 𝕜]

/-- A convex set stays `R`-convex under a `𝕜`-linear map compatible with the `R`-action. -/
theorem Convex.linear_image_of_compatibleSMul
    {C : Set E} (hC : Convex R C) (f : E →ₗ[𝕜] F) :
    Convex R (f '' C) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  refine ⟨a • x' + b • y', hC hx' hy' ha hb hab, ?_⟩
  simp [map_add]

end LinearImageCompatibleSmul

section OrthogonalProjection

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Corollary 3.4.1: the orthogonal projection of an `R`-convex subset of an inner-product space
onto a subspace is again `R`-convex. -/
theorem Convex.orthogonalProjection_image [SMul R E] {C : Set E} (hC : Convex R C)
    (L : Submodule 𝕜 E) [L.HasOrthogonalProjection] [SMul R L]
    [LinearMap.CompatibleSMul E L R 𝕜] :
    Convex R (L.orthogonalProjection '' C) := by
  simpa using hC.linear_image_of_compatibleSMul (f := L.orthogonalProjection.toLinearMap)

end OrthogonalProjection

/-! ### Text_3_4_2 (from Chap01) -/
open Set
open scoped Pointwise Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 3.4.2 identifies inverse-image/image formulas for a translated positive cone
  and for the positive cone itself.
- `core/canonical`: the owner layer is the general positive-cone API
  `orthant[R](E)` with `ge_iff_sub_mem_orthant`, together with canonical
  `Set.preimage`/`Set.image` and pointwise translation on sets.
- `bridge/view`: concrete matrix/coordinate orthant readings are downstream specializations of the
  abstract owners in this file.
- Primitive data vs derived API: positive-cone membership and set image/preimage are primitive; any
  coordinate-model rendering is derived.
- Layer target: `core/canonical` first, then `bridge/view`.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: no special extended-codomain layer is needed here; the canonical target
  is the ordered additive module positive-cone API.
- Scalar/ambient check: remove concrete coordinate-model bridge surfaces from this source item;
  keep only the abstraction layer needed by the mathematics.
- Owner check: keep `orthant[R](E)` and `Set.image`/`Set.preimage` as the primary owners.
- Topology check: this item is not topology-facing, so no intrinsic/relative topology owner is
  applicable.
- Notation check: no new notation owner is needed; theorem surfaces stay in canonical set/order
  notation.
-/

section Owner

section Preimage

/-- Text 3.4.2 (1), owner-level form: the preimage of a translated orthant is exactly a
pointwise order-inequality set. -/
theorem preimage_vadd_orthant_eq_setOf_ge
    {R X F : Type*}
    [AddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
    [Semiring R] [PartialOrder R] [Module R F] [PosSMulMono R F]
    (f : X → F) (a : F) :
    f ⁻¹' (a +ᵥ orthant[R](F)) = {x : X | f x ≥ a} := by
  -- Reduce the set equality to the source proof's pointwise membership equivalence.
  ext x
  -- Translate membership in the shifted orthant into a difference-in-orthant condition.
  rw [mem_preimage, mem_setOf_eq, mem_vadd_set_iff_neg_vadd_mem]
  rw [vadd_eq_add, add_comm, ← sub_eq_add_neg]
  exact sub_mem_orthant_iff (R := R) (x := f x) (x' := a)

end Preimage

section Image

variable {R E F : Type*}

/-- Text 3.4.2 (2), owner-level form: the image of the orthant is exactly the existential
nonnegativity witness view `∃ x ≥ 0, f x = y`. -/
theorem image_orthant_eq_setOf_exists_nonneg
    [Semiring R] [PartialOrder R]
    [AddCommMonoid E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]
    (f : E → F) :
    f '' orthant[R](E) =
      {y : F | ∃ x : E, x ≥ 0 ∧ f x = y} := by
  -- Compare both sets by unpacking and repackaging the image witness.
  ext y
  constructor
  · intro hy
    -- A point in the image comes with a preimage witness already lying in the orthant.
    rcases (Set.mem_image (f := f) (s := orthant[R](E)) (y := y)).1 hy with
      ⟨x, hx, hxy⟩
    exact ⟨x, (mem_orthant_iff (𝕜 := R) (M := E) (x := x)).1 hx, hxy⟩
  · rintro ⟨x, hx0, hxy⟩
    -- Conversely, a nonnegative witness packages directly into image membership.
    exact (Set.mem_image (f := f) (s := orthant[R](E)) (y := y)).2
      ⟨x, (mem_orthant_iff (𝕜 := R) (M := E) (x := x)).2 hx0, hxy⟩

end Image

end Owner

/-! ### Theorem_3_4 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.4 states two closure properties for convex subsets under a linear
  map `A : E →ₗ[𝕜] F`: the image `A '' C` of a convex set `C` is convex, and the inverse image
  `A ⁻¹' D` of a convex set `D` is convex.
- `core/canonical`: the owner abstraction is the predicate `Convex 𝕜 s` on sets; after the
  standard image/preimage bridge, the exact owner theorems are `Convex.linear_image` and
  `Convex.linear_preimage`.
- `bridge/view`: by Text 3.4.0, the textbook notations `AC` and `A⁻¹D` are exactly the standard
  set image `A '' C` and preimage `A ⁻¹' D`.
- Primitive data vs derived API: the linear map `A` and the sets `C` and `D` are primitive; the
  theorem records only the derived convexity of their image and inverse image.
- Scalar/ambient minimization check: keep the linear-map owner layer. Moving to affine maps would
  strengthen assumptions (`Ring`, `AddCommGroup`) and is not needed for this item's primitive
  data.
- Domain-style sampling: the four declarations checked first are the project bridge
  `Text_3_4_0` for `Set.image`/`Set.preimage`, the nearby project exact-recall pattern
  `Theorem_3_1` for `Convex.add`, and the mathlib owner theorems `Convex.linear_image` and
  `Convex.linear_preimage`. They show that this item has no extra source-facing data beyond the
  standard set image/preimage constructions and their derived convexity closures.
- Layer target: `core/canonical`; after the notation bridge of Text 3.4.0, each clause is exact
  owner-side reuse, so the main entries should remain direct `recall`s rather than local wrapper
  theorems.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient layer over-concrete? `No`: this item is codomain-generic and already stated at
  the canonical `Convex 𝕜` owner layer.
- Scalar/ambient structure stronger than needed? `No`: `Convex.linear_image` and
  `Convex.linear_preimage` already sit at the minimal ordered-semiring/module layer used by the
  chapter's convex APIs.
- Concrete-model owner instead of intrinsic owner? `No`: the owner is the intrinsic set predicate
  `Convex 𝕜`, not a model-specific wrapper.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: Theorem 3.4 is not a topology-facing
  closure/interior statement.
- Owner-name or notation mismatch? `No`: the canonical owners are short (`Convex.linear_image`,
  `Convex.linear_preimage`) and the theorem surface uses the textbook-primary set notation
  `A '' C`, `A ⁻¹' D`.
- Upstream over-specialization forcing downstream noise? `No`: there is no over-concrete upstream
  bridge to repair; direct owner recalls are already the correct public API surface for this item.
-/

/- Theorem 3.4 (1): for a linear map `A`, the image `A '' C` of a convex set `C` is convex; this
is the canonical theorem `Convex.linear_image`. -/
recall Convex.linear_image

/- Theorem 3.4 (2): for a linear map `A`, the inverse image `A ⁻¹' D` of a convex set `D` is
convex; this is the canonical theorem `Convex.linear_preimage`. -/
recall Convex.linear_preimage
