import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_4

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 34.1 says that the lower closure `K̲ := cl₂ (cl₁ K)` is lower closed
  and the upper closure `K̅ := cl₁ (cl₂ K)` is upper closed.
- `core/canonical`: the primitive Chapter 34 one-variable closure operators are
  `Bifunction.closure1` and `Bifunction.closure2`, with textbook surface notation `cl₁` and
  `cl₂`, already owned by `Definition33_0_4`.
- `bridge/view`: the opposite-variance formulas are obtained by swapping the variables with
  `Function.swap`, applying the same owner closures, and swapping back.

Domain-style sampling used here:
- `Bifunction.closure1`, `Bifunction.closure2` from `Definition33_0_4`;
- `Bifunction.closure1_idem`, `Bifunction.closure2_idem` from `Definition33_0_4`;
- `Function.swap` as the canonical variable-exchange bridge.

Primitive data vs derived API:
- primitive datum: a bifunction `K : U → X → WithTopBot 𝕜`;
- primitive owner API reused from upstream: the partial closures `cl₁ K` and `cl₂ K`;
- primitive source-facing operators introduced here: `lowerClosure K := cl₂ (cl₁ K)` and
  `upperClosure K := cl₁ (cl₂ K)`;
- derived API: the theorem-level owner statements saying `lowerClosure K` is convex-side closed
  and `upperClosure K` is concave-side closed, together with closure-equation bridge forms and
  the swapped formulas below.

Layer target:
- `source-facing` for `lowerClosure`, `upperClosure`, and the 34.1 owner-level closedness theorems;
- `bridge/view` for the swapped formulas.
-/

section Owners

variable [ConditionallyCompleteLattice 𝕜] [Neg 𝕜]

/-- Section 34's lower closure `K̲` of a saddle-function is `cl₂ (cl₁ K)`. -/
def lowerClosure (K : U → X → WithTopBot 𝕜) : U → X → WithTopBot 𝕜 :=
  cl₂ (cl₁ K)

/-- Section 34's upper closure `K̅` of a saddle-function is `cl₁ (cl₂ K)`. -/
def upperClosure (K : U → X → WithTopBot 𝕜) : U → X → WithTopBot 𝕜 :=
  cl₁ (cl₂ K)

/-- Textbook postfix notation for the Chapter 34 lower closure owner `K ↦ K̲`. -/
scoped[Rockafellar] postfix:max "̲" => Bifunction.lowerClosure

/-- Textbook postfix notation for the Chapter 34 upper closure owner `K ↦ K̅`. -/
scoped[Rockafellar] postfix:max "̅" => Bifunction.upperClosure

end Owners

section Closedness

section Lower

variable [ConditionallyCompleteLinearOrder 𝕜] [Neg 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [NoBotOrder 𝕜]

/-- Bridge/view: the lower closure `K̲` is fixed by the second-variable closure operator `cl₂`. -/
@[simp] theorem lowerClosure_closure2_eq (K : U → X → WithTopBot 𝕜) :
    cl₂ K̲ = K̲ := by
  change cl₂ (cl₂ (cl₁ K)) = cl₂ (cl₁ K)
  exact closure2_idem (cl₁ K)

/-- Theorem 34.1: the lower closure `K̲` is convex-side closed. -/
theorem lowerClosure_isConvexClosed (K : U → X → WithTopBot 𝕜) :
    IsConvexClosed K̲ := by
  exact (isConvexClosed_iff_closure2_eq K̲).2 (lowerClosure_closure2_eq K)

end Lower

section UpperFixedPoint

variable [ConditionallyCompleteLinearOrder 𝕜] [AddGroup 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [NoBotOrder 𝕜]

/-- Bridge/view: the upper closure `K̅` is fixed by the first-variable closure operator `cl₁`. -/
@[simp] theorem upperClosure_closure1_eq (K : U → X → WithTopBot 𝕜) :
    cl₁ K̅ = K̅ := by
  change cl₁ (cl₁ (cl₂ K)) = cl₁ (cl₂ K)
  exact closure1_idem (cl₂ K)

end UpperFixedPoint

section UpperClosedness

variable [ConditionallyCompleteLinearOrder 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [IsOrderedAddMonoid 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [AddCommGroup 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]

/-- Theorem 34.1: the upper closure `K̅` is concave-side closed. -/
theorem upperClosure_isConcaveClosed (K : U → X → WithTopBot 𝕜) :
    IsConcaveClosed K̅ := by
  exact (isConcaveClosed_iff_closure1_eq K̅).2 (upperClosure_closure1_eq K)

end UpperClosedness

end Closedness

section OwnersApply

variable [ConditionallyCompleteLattice 𝕜] [Neg 𝕜]

@[simp] theorem lowerClosure_apply (K : U → X → WithTopBot 𝕜) (u : U) (x : X) :
    K̲ u x = cl(fun x' ↦ concaveClosure (fun u' ↦ K u' x') u) x := by
  rfl

@[simp] theorem upperClosure_apply (K : U → X → WithTopBot 𝕜) (u : U) (x : X) :
    K̅ u x = concaveClosure (fun u' ↦ cl(K u') x) u := by
  rfl

/-- Bridge/view: swapping variables turns the same owner closures into the convex-concave form of
Definition 34.1. -/
@[simp] theorem lowerClosure_swap_apply (K : U → X → WithTopBot 𝕜) (u : U) (x : X) :
    Function.swap ((Function.swap K)̲) u x =
      cl(fun u' ↦ concaveClosure (fun x' ↦ K u' x') x) u := by
  rfl

/-- Bridge/view: swapping variables turns the same owner closures into the convex-concave form of
Definition 34.1. -/
@[simp] theorem upperClosure_swap_apply (K : U → X → WithTopBot 𝕜) (u : U) (x : X) :
    Function.swap ((Function.swap K)̅) u x =
      concaveClosure (fun x' ↦ cl(fun u' ↦ K u' x') u) x := by
  rfl

end OwnersApply

end

end Bifunction
