import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {𝕜 : Type u} {E : Type v} {F : Type w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 4.8 introduces the positive-homogeneity property of a function.
- `core/canonical`: the owner abstraction is the function-side property
  `Function.PositivelyHomogeneous 𝕜` on `f : E → F`, matching the chapter owner pattern
  `f.IsProper` / `f.IsConvex`; its primitive content is the textbook pointwise scaling law for
  positive scalars, expressed intrinsically over the primitive positive subtype.
- `bridge/view`: concrete model specializations belong downstream; this file keeps only the
  codomain-agnostic owner for positive-scalar homogeneity and exposes textbook `0 < c` binder
  form through a thin theorem-level bridge.
- Primitive data vs derived API: the primitive owner quantifies over intrinsic positive scalars
  `a : 𝕜⁺` with pointwise law
  `f (a • x) = a • f x`; the theorem
  `Function.PositivelyHomogeneous.iff_forall_pos_scalar` gives the explicit-binder bridge, and
  `Function.PositivelyHomogeneous.map_smul` is its pointwise consequence. This owner layer matches
  the later degree-`p` generalization at `f.PositivelyHomogeneousOfDegree 1`.
- Domain-style sampling used here: the project owners `Function.IsProper`,
  `Function.IsConvex`, and the later generalization `Function.PositivelyHomogeneousOfDegree` all
  use short unbundled `Prop` owners with theorem-level companion API. Mathlib does not expose an
  exact owner for positive-scalar homogeneity with this interface, so this file remains the
  canonical chapter owner rather than a wrapper around an upstream declaration.
-/

namespace Function

/-- Intrinsic owner for positive scalars in `𝕜`. -/
abbrev PositiveScalars (𝕜 : Type u) [LT 𝕜] [Zero 𝕜] : Type u := {c : 𝕜 // 0 < c}

/-- Textbook shorthand for the intrinsic positive-scalar owner `Function.PositiveScalars`. -/
scoped notation:max 𝕜 "⁺" => PositiveScalars 𝕜

/-- Canonical action of intrinsic positive scalars via coercion to the ambient scalar type. -/
instance instSMulPositiveScalars [LT 𝕜] [Zero 𝕜] (β : Type*) [SMul 𝕜 β] :
    SMul (𝕜⁺) β where
  smul a x := (a : 𝕜) • x

/-- Canonical coercion from intrinsic positive scalars to nonnegative scalars. -/
instance instCoePositiveScalarsToIci [Zero 𝕜] [Preorder 𝕜] :
    CoeTC (𝕜⁺) (Set.Ici (0 : 𝕜)) where
  coe a := ⟨(a : 𝕜), le_of_lt a.2⟩

/-- Coercing a positive scalar to the nonnegative subtype preserves its underlying value. -/
@[simp] theorem coe_positiveScalars_toIci [Zero 𝕜] [Preorder 𝕜] (a : 𝕜⁺) :
    ((a : Set.Ici (0 : 𝕜)) : 𝕜) = (a : 𝕜) :=
  rfl

/-- Bridge lemma for the intrinsic positive-scalar action back to ambient scalar action. -/
@[simp] theorem positiveScalars_smul_eq_coe_smul [LT 𝕜] [Zero 𝕜] {β : Type*}
    [SMul 𝕜 β] (a : 𝕜⁺) (x : β) :
    a • x = (a : 𝕜) • x :=
  rfl

/-- Definition 4.8: a function is positively homogeneous of degree `1` if scaling its argument by
a positive scalar scales its value by the same scalar. -/
def PositivelyHomogeneous (𝕜 : Type u) [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E] [SMul 𝕜 F]
    (f : E → F) : Prop :=
  ∀ a : 𝕜⁺, ∀ x : E, f (a • x) = a • f x

variable [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E] [SMul 𝕜 F]
variable {f : E → F}

/-- The Chapter 1 positive-homogeneity owner can be read intrinsically over positive scalars. -/
theorem PositivelyHomogeneous.iff_forall_pos :
    f.PositivelyHomogeneous 𝕜 ↔
      ∀ a : 𝕜⁺, ∀ x : E, f (a • x) = a • f x :=
  Iff.rfl

/-- Bridge from the intrinsic positive-scalar owner to the textbook scalar-plus-positivity
binder form. -/
theorem PositivelyHomogeneous.iff_forall_pos_scalar :
    f.PositivelyHomogeneous 𝕜 ↔
      ∀ c : 𝕜, 0 < c → ∀ x : E, f (c • x) = c • f x := by
  constructor
  · intro hf c hc x
    exact hf ⟨c, hc⟩ x
  · intro hf a x
    exact hf a a.2 x

/-- A positively homogeneous function carries intrinsic positive scalar multiples to the
corresponding scalar multiples of its value. -/
theorem PositivelyHomogeneous.map_smul_pos (hf : f.PositivelyHomogeneous 𝕜)
    (a : 𝕜⁺) (x : E) :
    f (a • x) = a • f x :=
  hf a x

/-- A positively homogeneous function carries every positive scalar multiple of an argument to the
corresponding scalar multiple of its value, in the textbook scalar-plus-positivity form. -/
theorem PositivelyHomogeneous.map_smul (hf : f.PositivelyHomogeneous 𝕜) {c : 𝕜}
    (hc : 0 < c) (x : E) :
    f (c • x) = c • f x :=
  (PositivelyHomogeneous.iff_forall_pos_scalar.mp hf) c hc x

end Function

end
