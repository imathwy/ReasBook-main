import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Function

variable {E : Type u} {F : Type v} [SMul ℝ E] [SMul ℝ F]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.21 introduces the degree-`p` positive-homogeneity predicate
  `f.PositivelyHomogeneousOfDegree p`.
- `core/canonical`: the existing chapter owner for the degree-`1` case is
  `f.PositivelyHomogeneous ℝ`, so the degree-`p` owner should live in the same `Function`
  namespace rather than as a parallel global predicate.
- `bridge/view`: the degree-`1` specialization theorem `one_iff` identifies the new source-facing
  predicate with the Chapter 1 owner.

Domain-style sampling used here:
- the chapter owner `Function.PositivelyHomogeneous` from `Definition_4_8`;
- its companion theorem `Function.PositivelyHomogeneous.map_smul`;
- the neighboring chapter owners `Function.IsConvex` and `Function.IsProper`, which use the same
  short unbundled `Prop`-owner pattern for function properties;
- mathlib's scalar-power API `Real.rpow` and `Real.rpow_one` for the degree factor.

Mathlib does not expose this exact real degree-`p` positive-homogeneity owner interface, so this
file remains the canonical chapter owner for the source-facing degree-`p` notion rather than a
wrapper around an upstream declaration.

Primitive data vs derived API:
- primitive inputs: the exponent `p`, the function `f`, and the intrinsic positive-scalar law on
  `ℝ⁺`;
- derived API: the textbook binder bridge `iff_forall_pos_scalar`, the intrinsic theorem
  `iff_forall_pos`, the pointwise scaling theorems `map_smul_pos` / `map_smul`, and the degree-`1`
  bridge `one_iff`.

Layer target: `source-facing`, with the degree-`1` identification as the minimal bridge back to
the earlier chapter owner. Concrete coordinate and extended-codomain specializations are
downstream views rather than part of this owner file.
-/

namespace Function

/-- Text 15.0.21: a function is positively homogeneous of degree `p` when scaling its argument by
an intrinsic positive real scalar scales its value by the `p`th power of that scalar. Any extra
side conditions on `p` belong in downstream theorems rather than in this owner predicate, since
they do not affect the defining scaling law. -/
def PositivelyHomogeneousOfDegree (p : ℝ) (f : E → F) : Prop :=
  ∀ a : ℝ⁺, ∀ x : E, f (a • x) = (a : ℝ).rpow p • f x

variable {p : ℝ} {f : E → F}

namespace PositivelyHomogeneousOfDegree

/-- The degree-`p` owner can be read intrinsically over positive real scalars. -/
theorem iff_forall_pos :
    f.PositivelyHomogeneousOfDegree p ↔
      ∀ a : ℝ⁺, ∀ x : E, f (a • x) = (a : ℝ).rpow p • f x :=
  Iff.rfl

/-- The intrinsic positive-scalar owner is equivalent to the textbook binder form over `ℝ`. -/
theorem iff_forall_pos_scalar :
    f.PositivelyHomogeneousOfDegree p ↔
      ∀ ⦃a : ℝ⦄, 0 < a → ∀ x : E, f (a • x) = a.rpow p • f x := by
  constructor
  · intro hf a ha x
    exact hf ⟨a, ha⟩ x
  · intro hf a x
    exact hf (a := a.1) a.2 x

/-- A positively homogeneous function of degree `p` carries intrinsic positive scalar multiples to
the corresponding `p`th-power scalar multiples of its value. -/
theorem map_smul_pos (hf : f.PositivelyHomogeneousOfDegree p)
    (a : ℝ⁺) (x : E) :
    f (a • x) = (a : ℝ).rpow p • f x :=
  hf a x

/-- A positively homogeneous function of degree `p` carries each positive scalar multiple of an
argument to the corresponding `p`th-power scalar multiple of its value. -/
theorem map_smul (hf : f.PositivelyHomogeneousOfDegree p)
    {c : ℝ} (hc : 0 < c) (x : E) :
    f (c • x) = c.rpow p • f x :=
  hf ⟨c, hc⟩ x

/-- Coercing a real-valued degree-`p` positively homogeneous function to `WithTopBot ℝ` preserves
the same degree-`p` homogeneity law. -/
theorem toWithTopBot {f : E → ℝ} (hf : f.PositivelyHomogeneousOfDegree p) :
    f.toWithTopBot.PositivelyHomogeneousOfDegree p := by
  intro a x
  change ((f (a • x) : ℝ) : WithTopBot ℝ) =
      (((a : ℝ).rpow p • f x : ℝ) : WithTopBot ℝ)
  exact congrArg (fun t : ℝ ↦ (t : WithTopBot ℝ)) (hf a x)

/-- Degree-`1` positive homogeneity is exactly the Chapter 1 owner predicate
`Function.PositivelyHomogeneous`. -/
@[simp] theorem one_iff :
    f.PositivelyHomogeneousOfDegree 1 ↔ f.PositivelyHomogeneous ℝ := by
  rw [Function.PositivelyHomogeneous.iff_forall_pos, iff_forall_pos]
  constructor
  · intro hf a x
    simpa [Real.rpow_one] using hf a x
  · intro hf a x
    simpa [Real.rpow_one] using hf a x

end PositivelyHomogeneousOfDegree

end Function

end
