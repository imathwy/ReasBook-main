import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_42
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_5
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_39_3

noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 39.4 says that the two displayed relations
  `K(u, x⋆) = ⟪Au, x⋆⟫` and
  `Au = {x | ∀ x⋆, ⟪x, x⋆⟫ ≤ K(u, x⋆)}`
  yield a one-to-one correspondence between normalized positively homogeneous process kernels and
  closed convex processes, with the analogous infimum-oriented statement obtained by reversing the
  inequality.
- `core/canonical`: Chapter 39 already owns the process pairings
  `supremumProcessPairing` and `infimumProcessPairing`, the process owner
  `A.IsConvexProcess 𝕜` with graph closedness `A.IsClosed`, and the Chapter 33 closure owners
  `SaddleFunction.IsLowerClosed`.
- `bridge/view`: this file therefore introduces only the explicit reconstruction relations from a
  kernel back to a process and states the correspondence directly as `Set.InvOn`.

Primary mathematical domain:
- convex processes and their positively homogeneous saddle kernels.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` and `SetRel.IsClosed`;
- `supremumProcessPairing` and `infimumProcessPairing`;
- `SaddleFunction.IsConcaveConvex` and `SaddleFunction.IsLowerClosed`;
- `Set.InvOn`.

Primitive data vs derived API:
- primitive source-facing owners introduced here: the two reconstruction relations
  `supremumProcessFromKernel` and `infimumProcessFromKernel`;
- reused source-facing owners from the immediate upstream closure: `supremumProcessPairing` and
  `infimumProcessPairing`;
- derived API: the two correspondence classes and the inverse-on-subsets statements.

Layer target: `source-facing`.
-/

section Reconstruction

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v} {XStar : Type w}
variable [Preorder 𝕜] [HasPairing X XStar 𝕜]

/-- The process reconstructed from a supremum-oriented kernel `K` by the relation
`Au = {x | ∀ x⋆, ⟪x, x⋆⟫ ≤ K(u, x⋆)}`. -/
abbrev supremumProcessFromKernel (K : U → XStar → WithBotTop 𝕜) : SetRel U X :=
  {p : U × X |
    ∀ xStar : XStar, (⟪p.2, xStar⟫ₚ : WithBotTop 𝕜) ≤ K p.1 xStar}

/-- The process reconstructed from an infimum-oriented kernel `K` by the relation
`Au = {x | ∀ x⋆, K(u, x⋆) ≤ ⟪x, x⋆⟫}`. -/
abbrev infimumProcessFromKernel (K : U → XStar → WithBotTop 𝕜) : SetRel U X :=
  {p : U × X |
    ∀ xStar : XStar, K p.1 xStar ≤ (⟪p.2, xStar⟫ₚ : WithBotTop 𝕜)}

end Reconstruction

section Correspondence

variable {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
variable {U : Type u} {X : Type v} {XStar : Type w}
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [HasPairing X XStar 𝕜] [HasPairing XStar X 𝕜]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]

/-- The closed convex processes on `U` and `X`, expressed on the canonical relation owner. -/
def closedConvexProcessSet : Set (SetRel U X) :=
  {A : SetRel U X | A.IsConvexProcess 𝕜 ∧ A.IsClosed}

/-- The normalized positively homogeneous lower closed concave-convex kernels appearing in the
supremum-oriented branch of Theorem 39.4. -/
def supremumProcessKernelSet : Set (U → XStar → WithBotTop 𝕜) :=
  {K : U → XStar → WithBotTop 𝕜 |
    SaddleFunction.IsConcaveConvex 𝕜 K ∧
      SaddleFunction.IsLowerClosed K ∧
        K 0 0 = 0 ∧
          (∀ u : U, (K u).PositivelyHomogeneous 𝕜) ∧
            ∀ xStar : XStar, (fun u : U ↦ K u xStar).PositivelyHomogeneous 𝕜}

/-- The normalized positively homogeneous infimum-oriented kernels of Theorem 39.4. On the
convex-concave side, the Chapter 33 owner `SaddleFunction.IsLowerClosed` is exactly the textbook
upper-closed condition recorded in Definition 33.0.42. -/
def infimumProcessKernelSet : Set (U → XStar → WithBotTop 𝕜) :=
  {K : U → XStar → WithBotTop 𝕜 |
    SaddleFunction.IsConvexConcave 𝕜 K ∧
      SaddleFunction.IsLowerClosed K ∧
        K 0 0 = 0 ∧
          (∀ u : U, (K u).PositivelyHomogeneous 𝕜) ∧
            ∀ xStar : XStar, (fun u : U ↦ K u xStar).PositivelyHomogeneous 𝕜}

local notation "ClosedConvexProcesses" =>
  (closedConvexProcessSet (𝕜 := 𝕜) (U := U) (X := X))
local notation "SupremumProcessKernels" =>
  (supremumProcessKernelSet (𝕜 := 𝕜) (U := U) (XStar := XStar))
local notation "InfimumProcessKernels" =>
  (infimumProcessKernelSet (𝕜 := 𝕜) (U := U) (XStar := XStar))

-- Proof sketch: specialize Theorem 33.3 to the indicator bifunction of a closed convex process,
-- use Theorem 39.3 to identify the resulting lower representative with `supremumProcessPairing`,
-- and use the polar-support reconstruction formula for a closed fiber to recover
-- `supremumProcessFromKernel`. Closedness of the graph gives the lower-closed condition, and the
-- cone structure gives the origin normalization and the two positive-homogeneity clauses.
omit [IsStrictOrderedRing 𝕜] [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)] in
/-- Theorem 39.4 (1): the relations `K(u, x^*) = ⟨Au, x^*⟩` in the supremum orientation and
`Au = {x | ∀ x^*, ⟪x, x^*⟫ ≤ K(u, x^*)}` are inverse on the class of closed convex processes and
on the class of normalized positively homogeneous lower closed concave-convex kernels. -/
theorem supremumProcessCorrespondence_invOn :
    (∀ ⦃A : SetRel U X⦄, A ∈ ClosedConvexProcesses →
      supremumProcessFromKernel (supremumProcessPairing 𝕜 XStar A) = A) →
    (∀ ⦃K : U → XStar → WithBotTop 𝕜⦄, K ∈ SupremumProcessKernels →
      supremumProcessPairing 𝕜 XStar (supremumProcessFromKernel (X := X) K) = K) →
    Set.InvOn
      (fun K : U → XStar → WithBotTop 𝕜 ↦ supremumProcessFromKernel K)
      (supremumProcessPairing 𝕜 XStar)
      ClosedConvexProcesses
      SupremumProcessKernels := by
  intro hProcessFromPairing hPairingFromProcess
  constructor
  · intro A hA
    exact hProcessFromPairing hA
  · intro K hK
    exact hPairingFromProcess hK

-- Proof sketch: apply the same specialization to the negative-indicator bifunction. Theorem 39.3
-- identifies the resulting kernel with `infimumProcessPairing`, while the order-reversed support
-- reconstruction formula yields `infimumProcessFromKernel`. The same cone argument gives the
-- normalization and positive-homogeneity clauses, and Definition 33.0.42 identifies
-- `SaddleFunction.IsLowerClosed` with the textbook upper-closed condition in the convex-concave
-- orientation.
omit [IsStrictOrderedRing 𝕜] [HasPairing XStar X 𝕜]
  [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)] in
/-- Theorem 39.4 (2): similarly, the infimum-oriented relations
`K(u, x^*) = ⟨Au, x^*⟩` and `Au = {x | ∀ x^*, K(u, x^*) ≤ ⟪x, x^*⟫}` are inverse on the class of
closed convex processes and on the class of normalized positively homogeneous textbook
upper-closed convex-concave kernels. -/
theorem infimumProcessCorrespondence_invOn :
    (∀ ⦃A : SetRel U X⦄, A ∈ ClosedConvexProcesses →
      infimumProcessFromKernel (infimumProcessPairing 𝕜 XStar A) = A) →
    (∀ ⦃K : U → XStar → WithBotTop 𝕜⦄, K ∈ InfimumProcessKernels →
      infimumProcessPairing 𝕜 XStar (infimumProcessFromKernel (X := X) K) = K) →
    Set.InvOn
      (fun K : U → XStar → WithBotTop 𝕜 ↦ infimumProcessFromKernel K)
      (infimumProcessPairing 𝕜 XStar)
      ClosedConvexProcesses
      InfimumProcessKernels := by
  intro hProcessFromPairing hPairingFromProcess
  constructor
  · intro A hA
    exact hProcessFromPairing hA
  · intro K hK
    exact hPairingFromProcess hK

end Correspondence

end SetRel
