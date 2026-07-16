import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_6_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.9.1 describes the directions along which a proper convex function
  has constant translation profiles.
- `core/canonical`: the chapter already owns exactly that direction space as
  `lineal f` from Definition 8.9.0.
- `bridge/view`: the genuinely new content attached to this numbered item is the comparison with
  the epigraph lineality condition from Theorem 8.8 at slope `0`.
- Primitive data vs derived API: this file introduces no new primitive owner data. The owner is the
  existing function-facing `lineal`; the zero-slope epigraph-pair formulation is derived
  scalar-generic bridge API.
- Minimality note for the ambient layer: `lineal` itself is already defined on the generalized
  `WithTopBot α` layer in Definition 8.9.0. Correspondingly, the primitive bridge between profile
  constancy and zero translation slope is stated here on the weaker `SMulWithZero` action layer,
  while the owner-level `lin(f)` criterion and epigraph-lineality bridge are imported at the
  scalar-generic Chapter 8 layers from Corollary 8.6.1 and Theorem 8.8.
- Layer target: scalar-general `core/canonical` recall/bridge for the owner and scalar-general
  `bridge/view` theorems for the zero-slope epigraph-lineality formulation.

Domain-style sampling used here:
- `Function.lineal` and `Function.mem_lineal_iff` from Definition 8.9.0;
- `Function.forall_translate_profile_constant_iff_mem_constancySpace` from Corollary 8.6.1;
- `Function.HasTranslationSlope` from Theorem 8.8;
- `ConvexERealFunction.recessionFunction` from the nearby Chapter 2 API;
- `translation_formula_epigraph_lineality_recession_value_tfae` from Theorem 8.8;
- the set-side owner `Set.lineal`, used through `lin[𝕜](epi f)`.
-/

/- Definition 8.9.1: the source's affine-direction owner is the already owned
`Function.lineal`. -/
recall Function.lineal

/- The source-facing membership wording for that owner remains `mem_lineal_iff`. -/
recall Function.mem_lineal_iff

namespace Function

section

variable {𝕜 : Type*} [Zero 𝕜]
variable {α : Type*} [AddMonoid α] [SMulWithZero 𝕜 α]
variable {E : Type*} [AddMonoid E] [SMulWithZero 𝕜 E]

/-- A translate profile is constant in its scalar parameter exactly when its translation slope is
`0`. -/
theorem forall_translate_profile_constant_iff_hasTranslationSlope_zero
    {f : E → WithTopBot α} {y : E} :
    (∀ x : E, ∀ s t : 𝕜, f (x + s • y) = f (x + t • y)) ↔
      f.HasTranslationSlope 𝕜 y (0 : α) := by
  constructor
  · intro h x τ
    have hxt : f (x + τ • y) = f (x + (0 : 𝕜) • y) := h x τ (0 : 𝕜)
    calc
      f (x + τ • y) = f (x + (0 : 𝕜) • y) := hxt
      _ = f x := by simp
      _ = f x + ((τ • (0 : α) : α) : WithTopBot α) := by simp
  · intro h x s τ
    have hs : f (x + s • y) = f x := by
      calc
        f (x + s • y) = f x + ((s • (0 : α) : α) : WithTopBot α) := h x s
        _ = f x := by simp
    have hτ : f (x + τ • y) = f x := by
      calc
        f (x + τ • y) = f x + ((τ • (0 : α) : α) : WithTopBot α) := h x τ
        _ = f x := by simp
    exact hs.trans hτ.symm

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- For a proper convex function, `y ∈ lin(f)` means exactly that every translate profile
`t ↦ f (x + t • y)` is constant in `t`. -/
@[simp] theorem mem_lineal_iff_forall_translate_profile_constant
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    y ∈ lin(f) ↔
      ∀ x : E, ∀ s t : 𝕜, f (x + s • y) = f (x + t • y) := by
  exact
    (Function.forall_translate_profile_constant_iff_mem_constancySpace
      f hf_convex hf_proper y).symm

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- For a proper convex function, membership in `lin(f)` is equivalent to the owner-level zero
translation slope condition. -/
theorem mem_lineal_iff_hasTranslationSlope_zero
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    y ∈ lin(f) ↔ f.HasTranslationSlope 𝕜 y (0 : α) :=
  (mem_lineal_iff_forall_translate_profile_constant
      (f := f) hf_convex hf_proper (y := y)).trans
    forall_translate_profile_constant_iff_hasTranslationSlope_zero

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [SMul 𝕜 α]
variable {E : Type*} [AddCommGroup E] [SMul 𝕜 E]

/-- For a proper convex function, zero translation slope is equivalent to epigraph lineality at
zero slope, i.e. to membership of `(y, 0)` in `lin[𝕜](epi f)`. -/
theorem hasTranslationSlope_zero_iff_zero_mem_lin_epi
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    f.HasTranslationSlope 𝕜 y (0 : α) ↔ (y, (0 : α)) ∈ lin[𝕜](epi f) := by
  have h_tfae :=
    translation_formula_epigraph_lineality_recession_value_tfae
      (f := f) hf_convex hf_proper (y := y) (v := (0 : α))
  exact h_tfae
    (f.HasTranslationSlope 𝕜 y (0 : α))
    (by simp)
    ((y, (0 : α)) ∈ lin[𝕜](epi f))
    (by simp)

end

section

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- For a proper convex function, membership in `lin(f)` is equivalent to epigraph lineality at
zero slope, i.e. to membership of `(y, 0)` in `lin[𝕜](epi f)`. -/
@[simp] theorem mem_lineal_iff_zero_mem_lin_epi
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    y ∈ lin(f) ↔ (y, (0 : α)) ∈ lin[𝕜](epi f) := by
  exact (mem_lineal_iff_hasTranslationSlope_zero
      (f := f) hf_convex hf_proper (y := y)).trans
    (hasTranslationSlope_zero_iff_zero_mem_lin_epi
      (f := f) hf_convex hf_proper (y := y))

/-- Any lineality direction gives the canonical zero-slope epigraph-lineality vector. -/
theorem zero_mem_lin_epi_of_mem_lineal
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    y ∈ lin(f) → (y, (0 : α)) ∈ lin[𝕜](epi f) := by
  intro hy
  exact (mem_lineal_iff_zero_mem_lin_epi hf_convex hf_proper).1 hy

/-- Zero-slope epigraph-lineality membership recovers the canonical owner `lin(f)`. -/
theorem mem_lineal_of_zero_mem_lin_epi
    {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) {y : E} :
    (y, (0 : α)) ∈ lin[𝕜](epi f) → y ∈ lin(f) := by
  intro hy
  exact (mem_lineal_iff_zero_mem_lin_epi hf_convex hf_proper).2 hy

end

end Function

end
