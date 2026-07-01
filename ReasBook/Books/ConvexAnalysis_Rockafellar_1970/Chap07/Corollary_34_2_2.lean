import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_43

noncomputable section

universe u v

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 34.2.2 says that lower closed, upper closed, and fully closed
  saddle-functions are closed, and that each closed equivalence class has a unique lower closed
  least member and a unique upper closed greatest member.
- `core/canonical`: the owner layer is the canonical Chapter 34 API already provided upstream:
  `SaddleFunction.IsClosed`, `SaddleFunction.IsLowerClosed`,
  `SaddleFunction.IsUpperClosed`, `Bifunction.IsFullyClosed`, together with
  `Bifunction.IsClosedConvex`, `Bifunction.lowerPairing XStar F`,
  `Bifunction.upperPairing XStar F`, and `Bifunction.omega XStar F` / `Ω(F)`.
- `bridge/view`: this file keeps only source-facing corollary clauses on those owners and avoids
  rebuilding local `EReal`-specific wrappers.

Primary mathematical domain:
- Chapter 34 saddle-function closedness and the canonical interval class `Ω(F)`.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvex.closure1_closed` and
  `SaddleFunction.IsConcaveConvex.closure2_closed` from `Corollary33_1_1`;
- `SaddleFunction.isFullyClosed_iff` from `Lemma33_0_43`;
- `Bifunction.isConcaveClosed_iff_closure1_eq` and `Bifunction.isConvexClosed_iff_closure2_eq`
  from `Definition33_0_4`;
- `Bifunction.lowerPairing_mem_omega`, `Bifunction.upperPairing_mem_omega`, and
  `Bifunction.mem_omega_iff_equivalent_lowerPairing` from `Theorem_34_2`;
- `Bifunction.lowerPairing`, `Bifunction.upperPairing`, and `Bifunction.omega` from
  `Defn_34_2`.

Primitive data vs derived API:
- primitive source data: a saddle-function `K`, or a closed convex bifunction `F`;
- primitive owner objects reused here: `IsClosed`, `IsLowerClosed`, `IsUpperClosed`,
  `Bifunction.IsFullyClosed`, `lowerPairing XStar F`, `upperPairing XStar F`, and `Ω(F)`;
- derived API: the seven corollary clauses below, especially the least/greatest representative
  characterizations inside `Ω(F)`.

Layer target: `source-facing`, stated directly on the existing Chapter 34 owners.
-/

namespace SaddleFunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [NoMaxOrder 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜]
variable [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [TopologicalSpace U] [TopologicalSpace X]

-- Proof sketch: the owner equation `K̲ = K` gives `cl₂ K = K` by applying `cl₂` and using
-- idempotence, so the two mixed closure identities in `isClosed_iff` become immediate.
/-- Corollary 34.2.2 (1): a lower closed saddle-function is closed. -/
theorem isClosed_of_isLowerClosed
    {K : U → X → WithBotTop 𝕜}
    (hK_closed : IsLowerClosed K) :
    IsClosed K := by
  have hLower : cl₂ (cl₁ K) = K := by
    simpa [SaddleFunction.IsLowerClosed, Bifunction.lowerClosure] using hK_closed
  have hcl₂ : cl₂ K = K := by
    calc
      cl₂ K = cl₂ (cl₁ K) := by
        simpa using (congrArg (fun L ↦ cl₂ L) hLower).symm
      _ = K := hLower
  exact (SaddleFunction.isClosed_iff K).2 ⟨by simpa [hcl₂], by simpa [hcl₂] using hLower⟩

-- Proof sketch: symmetrically, `K̅ = K` forces `cl₁ K = K` by applying `cl₁` and using
-- idempotence, so `isClosed_iff` closes the argument.
/-- Corollary 34.2.2 (2): an upper closed saddle-function is closed. -/
theorem isClosed_of_isUpperClosed
    {K : U → X → WithBotTop 𝕜}
    (hK_closed : IsUpperClosed K) :
    IsClosed K := by
  have hUpper : cl₁ (cl₂ K) = K := by
    simpa [SaddleFunction.IsUpperClosed, Bifunction.upperClosure] using hK_closed
  have hcl₁ : cl₁ K = K := by
    calc
      cl₁ K = cl₁ (cl₂ K) := by
        simpa using (congrArg (fun L ↦ cl₁ L) hUpper).symm
      _ = K := hUpper
  exact (SaddleFunction.isClosed_iff K).2
    ⟨by simpa [hcl₁] using hUpper, by simpa [hcl₁]⟩

-- Proof sketch: use the owner bridge `IsFullyClosed.isLowerClosed` from Lemma 33.0.43 and then
-- apply part (1).
/-- Corollary 34.2.2 (3): a fully closed saddle-function is closed. -/
theorem isClosed_of_isFullyClosed
    {K : U → X → WithBotTop 𝕜}
    [IsOrderedAddMonoid 𝕜]
    (hK_closed : Bifunction.IsFullyClosed K) :
    IsClosed K := by
  exact
    isClosed_of_isLowerClosed
      hK_closed.isLowerClosed

end

end SaddleFunction

namespace Bifunction

section

open SaddleFunction

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable {XStar : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [TopologicalSpace X] [TopologicalSpace XStar]
variable [AddCommMonoid U] [SMul 𝕜 U] [Neg U] [HasPairing U U 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid XStar] [SMul 𝕜 XStar] [HasPairing X XStar 𝕜] [HasPairing XStar X 𝕜]

-- Proof sketch: use Theorem 34.2 (`lowerPairing X F ∈ Ω(F)`) together with the lower-closed
-- representative clause to obtain lower-closedness and leastness.
/-- Corollary 34.2.2 (4): for a closed convex bifunction `F`, the canonical lower representative
is lower closed and is the least member of the class `Ω(F)`. -/
theorem lowerPairing_isLowerClosed_and_isLeast_in_omega
    (F : U → X → WithBotTop 𝕜) (hF : IsClosedConvex F) :
    IsLowerClosed (lowerPairing XStar F) ∧
      IsLeast (Ω(F)) (lowerPairing XStar F) := by
  sorry

-- Proof sketch: from leastness of `lowerPairing X F` in `Ω(F)`, any other lower-closed member of
-- `Ω(F)` is the same lower representative.
/-- Corollary 34.2.2 (5): a lower closed member of `Ω(F)` is the canonical lower representative.
-/
theorem eq_lowerPairing_of_mem_omega_of_isLowerClosed
    (F : U → X → WithBotTop 𝕜) (hF : IsClosedConvex F)
    {K : U → XStar → WithBotTop 𝕜} (hK_mem : K ∈ Ω(F))
    (hK_closed : IsLowerClosed K) :
    K = lowerPairing XStar F := by
  sorry

-- Proof sketch: use Theorem 34.2 (`upperPairing X F ∈ Ω(F)`) together with the upper-closed
-- representative clause to obtain upper-closedness and greatestness.
/-- Corollary 34.2.2 (6): for a closed convex bifunction `F`, the canonical upper representative
is upper closed and is the greatest member of the class `Ω(F)`. -/
theorem upperPairing_isUpperClosed_and_isGreatest_in_omega
    (F : U → X → WithBotTop 𝕜) (hF : IsClosedConvex F) :
    IsUpperClosed (upperPairing XStar F) ∧
      IsGreatest (Ω(F)) (upperPairing XStar F) := by
  sorry

-- Proof sketch: from greatestness of `upperPairing X F` in `Ω(F)`, any other upper-closed member
-- of
-- `Ω(F)` is the same upper representative.
/-- Corollary 34.2.2 (7): an upper closed member of `Ω(F)` is the canonical upper representative.
-/
theorem eq_upperPairing_of_mem_omega_of_isUpperClosed
    (F : U → X → WithBotTop 𝕜) (hF : IsClosedConvex F)
    {K : U → XStar → WithBotTop 𝕜} (hK_mem : K ∈ Ω(F))
    (hK_closed : IsUpperClosed K) :
    K = upperPairing XStar F := by
  sorry

end

end Bifunction
