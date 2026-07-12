import Mathlib.Data.Setoid.Basic
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_4

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLattice 𝕜] [Neg 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `core/canonical`: the primitive one-variable closure operators `cl₁` and `cl₂` were already
  introduced upstream in Definition 33.0.4 and are reused here unchanged.
- `source-facing`: Definition 34.4 introduces the equivalence relation on saddle-functions saying
  that two bifunctions have the same partial closures `cl₁` and `cl₂`.
- `bridge/view`: the source relation `K ∼ L` is owned directly by equality of those two primitive
  closures, rather than by an auxiliary closure-pair wrapper.

Domain-style sampling used here:
- `Setoid` from core Lean.
- upstream chapter owners `cl₁` / `cl₂` from `Chap07.Definition33_0_4`.

Primitive data vs derived API:
- primitive source datum: a bifunction `K : U → X → WithTopBot 𝕜`;
- primitive owner API in this file: the setoid owner with relation
  `K ∼ L :↔ cl₁ K = cl₁ L ∧ cl₂ K = cl₂ L`;
- derived API: source notation `K ∼ L`, definitionally exposed by `equivalent_iff`.

Layer target: `source-facing` equivalence relation on top of the upstream closure owners.
-/

/-- Definition 34.4: two saddle-functions are equivalent when they have the same Chapter 34
closure pair `(cl₁ K, cl₂ K)`. -/
def equivalence : Setoid (U → X → WithTopBot 𝕜) where
  r K L := cl₁ K = cl₁ L ∧ cl₂ K = cl₂ L
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro K
      exact ⟨rfl, rfl⟩
    · intro K L hKL
      exact ⟨hKL.1.symm, hKL.2.symm⟩
    · intro K L M hKL hLM
      exact ⟨hKL.1.trans hLM.1, hKL.2.trans hLM.2⟩

scoped[Rockafellar] infix:50 " ∼ " => Bifunction.equivalence.r

/-- The source relation `K ∼ L` is exactly equality of the two Chapter 34 partial closures. -/
theorem equivalent_iff (K L : U → X → WithTopBot 𝕜) :
    K ∼ L ↔ cl₁ K = cl₁ L ∧ cl₂ K = cl₂ L :=
  Iff.rfl

end

end Bifunction
