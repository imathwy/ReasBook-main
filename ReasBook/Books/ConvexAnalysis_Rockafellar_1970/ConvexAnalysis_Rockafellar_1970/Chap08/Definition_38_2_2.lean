import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_3

noncomputable section

open scoped Pointwise
open Function

universe u v

namespace Bifunction

section

variable {U : Type u} {X : Type v} {𝕜 : Type*} {α : Type*}
variable [CommSemiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [ConditionallyCompleteLinearOrder α]
variable [SMul 𝕜 X] [SMul 𝕜 α]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 38.2.2 introduces the scalar multiple `F λ` of a convex bifunction
  `F`, with the slicewise formula `((F λ) u) x = λ (F u) (λ⁻¹ x)` for positive `λ`.
- `core/canonical`: the owner abstraction already present upstream is the Chapter 5 slice owner
  `Function.rightScalarMul`, together with its positive-parameter evaluation theorem
  `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`.
- `bridge/view`: the bifunction scalar multiple is just the slicewise lift of that owner to
  curried two-variable functions, not a second scalar-rescaling mechanism.

Domain-style sampling used here:
- `Function.rightScalarMul` and the notation `λ •ʳ f` from `Chap01.Text_5_4_2`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` from `Chap01.Text_5_4_3`;
- `Function.IsConvex.rightScalarMul` from `Chap01.Text_5_4_2`, showing the chapter already treats
  scalar rescaling as slice-level derived API.

Primitive data vs derived API:
- primitive source-facing owner: `Bifunction.rightScalarMul`;
- primitive bridge data: for each `u`, the slice `rightScalarMul F λ u` is the Chapter 5 owner
  `(⟨(λ : 𝕜), λ.2.le⟩ : Set.Ici (0 : 𝕜)) •ʳ F u`;
- derived API: the slice-bridge theorem and the pointwise positive-scalar formula below.

Notation decision:
- no new bifunction notation is introduced here. The chapter already uses `•ʳ` for the canonical
  slice owner, while the textbook juxtaposition `F λ` does not translate to an inference-stable
  Lean notation distinct from ordinary function application.

Redundant-source-assumption elimination:
- the source says “let `F` be a convex bifunction”, but the scalar-rescaling construction itself
  depends only on the bifunction and the positive scalar. Convexity belongs in later theorems
  about preservation of convexity, not in this defining owner.

Layer target: `source-facing`, implemented as a thin bridge to the existing `core/canonical`
slice owner.
-/

/-- Definition 38.2.2: for a positive scalar `λ`, the scalar multiple of a bifunction `F` is
obtained by taking the Chapter 5 right scalar multiple of each slice `F u`. -/
abbrev rightScalarMul (F : U → X → WithBotTop α) (lam : Set.Ioi (0 : 𝕜)) :
    U → X → WithBotTop α :=
  fun u ↦ ((⟨(lam : 𝕜), lam.2.le⟩ : 𝕜≥0) •ʳ F u)

/-- Each slice of the bifunction scalar multiple is exactly the Chapter 5 right scalar multiple of
the corresponding slice of `F`. -/
@[simp] theorem rightScalarMul_slice
    (F : U → X → WithBotTop α) (lam : Set.Ioi (0 : 𝕜)) (u : U) :
    rightScalarMul F lam u = (⟨(lam : 𝕜), lam.2.le⟩ : 𝕜≥0) •ʳ F u :=
  rfl

end

section

variable {U : Type u} {X : Type v} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [MulAction 𝕜 X]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- For each `u`, the scalar multiple of the slice `F u` is given pointwise by
`x ↦ λ (F u) (λ⁻¹ • x)`. -/
theorem rightScalarMul_apply
    (F : U → X → WithBotTop 𝕜) (lam : Set.Ioi (0 : 𝕜)) (u : U) (x : X) :
    rightScalarMul F lam u x = (lam : WithBotTop 𝕜) * F u ((lam : 𝕜)⁻¹ • x) := by
  simpa using
    rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos (F u) (a := (lam : 𝕜)) lam.2 x

end

end Bifunction
