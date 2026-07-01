import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v w

open scoped Rockafellar

namespace SaddleFunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddGroup 𝕜]
variable [TopologicalSpace U] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.10 says that closedness of a saddle-function depends only on its
  Chapter 34 equivalence class.
- `core/canonical`: the natural owner level is exactly the upstream Chapter 34 API
  `SaddleFunction.IsClosed` and `Bifunction.equivalence` from `Defn_34_2` / `Defn_34_4`, already
  stated on the codomain layer `WithBotTop 𝕜`.
- `bridge/view`: this item is a direct invariance theorem on that canonical owner layer, not a
  local redefinition of partial closures, closure pairs, or equivalence.

Primary mathematical domain:
- saddle-functions, partial closures, and equivalence classes in minimax theory.

Domain-style sampling used here:
- `Bifunction.equivalent_iff` and notation `K ∼ L` from `Chap07.Defn_34_4`;
- `SaddleFunction.IsClosed` from `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive source data: two bifunctions `K, L : U → X → WithBotTop 𝕜`;
- primitive owner layer reused from upstream: `∼` and `SaddleFunction.IsClosed`;
- derived API in this item: the equivalence-class invariance
  `SaddleFunction.IsClosed K ↔ SaddleFunction.IsClosed L`.

Layer target: `bridge/view`. The theorem compares the source-facing closedness predicate through
the canonical equivalence relation at the existing owner layer, without introducing local owner
duplicates.
-/

/-- Text 34.1.10: closedness of a saddle-function depends only on its Chapter 34 equivalence
class. -/
theorem IsClosed.of_equivalent {K L : U → X → WithBotTop 𝕜}
    (hK : IsClosed K) (hKL : K ∼ L) :
    IsClosed L := by
  rcases (Bifunction.equivalent_iff K L).1 hKL with ⟨hcl₁, hcl₂⟩
  rcases (Bifunction.equivalent_iff (cl₁ K) K).1 hK.1 with ⟨h₁₁, h₁₂⟩
  rcases (Bifunction.equivalent_iff (cl₂ K) K).1 hK.2 with ⟨h₂₁, h₂₂⟩
  exact ⟨
    (Bifunction.equivalent_iff (cl₁ L) L).2 ⟨
      by simpa [hcl₁] using h₁₁,
      by simpa [hcl₁, hcl₂] using h₁₂
    ⟩,
    (Bifunction.equivalent_iff (cl₂ L) L).2 ⟨
      by simpa [hcl₁, hcl₂] using h₂₁,
      by simpa [hcl₂] using h₂₂
    ⟩
  ⟩

/-- Text 34.1.10: closedness is invariant along the Chapter 34 equivalence relation. -/
theorem IsClosed.iff_of_equivalent {K L : U → X → WithBotTop 𝕜} (hKL : K ∼ L) :
    IsClosed K ↔ IsClosed L := by
  constructor
  · intro hK
    exact hK.of_equivalent hKL
  · intro hL
    have hLK : L ∼ K := by
      rcases (Bifunction.equivalent_iff K L).1 hKL with ⟨hcl₁, hcl₂⟩
      exact (Bifunction.equivalent_iff L K).2 ⟨hcl₁.symm, hcl₂.symm⟩
    exact hL.of_equivalent hLK

end

end SaddleFunction
