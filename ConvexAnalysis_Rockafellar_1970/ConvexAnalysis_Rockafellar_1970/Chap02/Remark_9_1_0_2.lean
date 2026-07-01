import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_1
import ConvexAnalysis_Rockafellar_1970.Chap02.ParaboloidEpigraph

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Rockafellar

local notation "fstₗ[" 𝕜 "]" => (LinearMap.fst 𝕜 𝕜 𝕜 : (𝕜 × 𝕜) →ₗ[𝕜] 𝕜)

/-
Source/core/bridge triage:
- `source-facing`: this remark records a concrete counterexample showing that the recession cone of
  a linear image need not equal the image of the recession cone, even when both the source set and
  its image are closed.
- `core/canonical`: the owner abstraction in this domain is the Chapter 8 recession-cone API
  centered on `recessionCone`, together with the linear-image theorem
  `LinearMap.recessionCone_image_closure_eq_image_recessionCone` from Theorem 9.1. The linear
  map in the present concrete example is the canonical owner `LinearMap.fst 𝕜 𝕜 𝕜`.
- `bridge/view`: the set image under `LinearMap.fst 𝕜 𝕜 𝕜` is definitionally the first-coordinate
  projection image, so `Prod.fst` remains only an internal coercion view and not a second public
  owner for this file.
- Primitive data vs derived API: the primitive source datum `paraboloidEpigraph` and its basic
  owner-side facts `mem_paraboloidEpigraph_iff`, `paraboloidEpigraph_isClosed`, and
  `paraboloidEpigraph_convex` now live in the shared owner file. This remark keeps only the image
  and recession-cone calculations derived from that owner. The closedness of the image is not kept
  as a separate owner theorem here, because it is an immediate corollary of the image calculation
  `= univ`.
- Domain-style sampling used here: `recessionCone`, `0⁺`, `Set.mem_recessionCone_iff`,
  `LinearMap.recessionCone_image_closure_eq_image_recessionCone`, and
  `LinearMap.isClosed_image_of_recessionKernelTrivial`.
- Layer target: the public main entry stays `source-facing` as a concrete counterexample to the
  naive closed-image formula, rather than a second owner theorem parallel to Theorem 9.1.
  at the owner layer, while the closure-level counterexample is exposed first with the primitive
  closedness datum `IsClosed paraboloidEpigraph`; the stronger Theorem-9.1 ambient assumptions are
  used only in the downstream bridge that instantiates this datum via
  `paraboloidEpigraph_isClosed`.
-/

section Ordered

variable {𝕜 : Type*} [Semiring 𝕜] [Preorder 𝕜]

/-- The first-coordinate image of the paraboloid epigraph is all of `𝕜`. -/
-- Proof sketch: for any `η : 𝕜`, the point with coordinates `(η, η^2)` lies in the epigraph and
-- maps to `η`, so the image contains every scalar.
theorem paraboloidEpigraph_fst_image_eq_univ :
    fstₗ[𝕜] '' paraboloidEpigraph = (univ : Set 𝕜) := by
  ext η
  constructor
  · intro _
    simp
  · intro _
    refine ⟨(η, η ^ 2), ?_, rfl⟩
    simp

/-- The recession cone of the first-coordinate image of the paraboloid epigraph is all of `𝕜`. -/
-- Proof sketch: rewrite the image as `Set.univ`, and then observe that every forward ray stays in
-- `Set.univ`, so its recession cone is again `Set.univ`.
theorem recessionCone_paraboloidEpigraph_fst_image_eq_univ :
    0⁺[𝕜] (fstₗ[𝕜] '' paraboloidEpigraph) = (univ : Set 𝕜) := by
  rw [paraboloidEpigraph_fst_image_eq_univ, Set.recessionCone_univ]

end Ordered

section OrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The first-coordinate image of the recession cone of the paraboloid epigraph is exactly
`{0}`. -/
-- Proof sketch: if `z ∈ 0⁺[𝕜] paraboloidEpigraph`, the inequality
-- `ξ₂ + t z₂ ≥ (ξ₁ + t z₁)^2` for all `t ≥ 0` forces `z₁ = 0`; conversely, every vertical
-- direction with nonnegative second coordinate lies in the recession cone, so the projection image
-- is the singleton `{0}`.
theorem fst_image_recessionCone_paraboloidEpigraph_eq_singleton_zero :
    fstₗ[𝕜] '' 0⁺[𝕜] paraboloidEpigraph = ({0} : Set 𝕜) := by
  ext η
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Set.mem_recessionCone_iff] at hz
    by_cases hz1 : z.1 = 0
    · simp [hz1]
    · let ξ : 𝕜 := (z.2 - z.1 ^ 2 + 1) / (2 * z.1)
      have hξ_mem : (ξ, ξ ^ 2) ∈ paraboloidEpigraph := by
        simp
      have hmem := hz (ξ, ξ ^ 2) hξ_mem 1 zero_le_one
      have hquad : (ξ + z.1) ^ 2 ≤ ξ ^ 2 + z.2 := by
        simpa [mem_paraboloidEpigraph_iff] using hmem
      have hineq : z.2 ≥ 2 * ξ * z.1 + z.1 ^ 2 := by
        nlinarith [hquad]
      have hξ_eval : 2 * ξ * z.1 + z.1 ^ 2 = z.2 + 1 := by
        dsimp [ξ]
        field_simp [hz1]
        ring
      nlinarith [hineq, hξ_eval]
  · intro hη
    have hzero_mem : ((0 : 𝕜), (0 : 𝕜)) ∈ 0⁺[𝕜] paraboloidEpigraph := by
      rw [Set.mem_recessionCone_iff]
      intro x hx t ht
      rcases x with ⟨x₁, x₂⟩
      simpa [zero_smul, add_zero] using hx
    refine ⟨((0 : 𝕜), (0 : 𝕜)), hzero_mem, ?_⟩
    simpa using hη.symm

/-- Remark 9.1.0.2 in source-facing form on scalar `𝕜`:
for `C = {(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` and `A (ξ₁, ξ₂) = ξ₁`, one has
`0⁺[𝕜] (A '' C) ≠ A '' 0⁺[𝕜] C`. -/
theorem recessionCone_fst_image_ne_fst_image_recessionCone_paraboloidEpigraph :
    0⁺[𝕜] (fstₗ[𝕜] '' paraboloidEpigraph) ≠
      fstₗ[𝕜] '' 0⁺[𝕜] paraboloidEpigraph := by
  rw [recessionCone_paraboloidEpigraph_fst_image_eq_univ,
    fst_image_recessionCone_paraboloidEpigraph_eq_singleton_zero]
  intro h
  have h1 : (1 : 𝕜) ∈ ({0} : Set 𝕜) := by
    simpa [h] using (show (1 : 𝕜) ∈ (univ : Set 𝕜) from trivial)
  simp at h1

end OrderedField

section Counterexample

variable {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜]

/-- Remark 9.1.0.2 on the Theorem-9.1 owner surface: even after writing the formula in closure
form, the paraboloid/projection example violates
`0⁺[𝕜] (A '' closure C) = A '' 0⁺[𝕜] (closure C)`. -/
theorem recessionCone_fst_image_closure_ne_fst_image_recessionCone_closure_paraboloidEpigraph :
    IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) →
    0⁺[𝕜] (fstₗ[𝕜] '' closure paraboloidEpigraph) ≠
      fstₗ[𝕜] '' 0⁺[𝕜] (closure paraboloidEpigraph) := by
  intro hClosed
  rw [hClosed.closure_eq]
  exact recessionCone_fst_image_ne_fst_image_recessionCone_paraboloidEpigraph (𝕜 := 𝕜)

/-- Source-facing existential counterexample form on the Theorem-9.1 owner surface:
there exist a closed convex set `C` and linear map `A` such that `A '' C` is closed but
`0⁺[𝕜] (A '' closure C) ≠ A '' 0⁺[𝕜] (closure C)`. -/
theorem exists_closed_convex_set_with_closed_linearImage_recessionCone_closure_image_ne :
    IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) →
    ∃ (C : Set (𝕜 × 𝕜)) (A : (𝕜 × 𝕜) →ₗ[𝕜] 𝕜),
      IsClosed C ∧ Convex 𝕜 C ∧ IsClosed (A '' C) ∧
        0⁺[𝕜] (A '' closure C) ≠ A '' 0⁺[𝕜] (closure C) := by
  intro hClosed
  refine ⟨paraboloidEpigraph, fstₗ[𝕜],
    hClosed, paraboloidEpigraph_convex, ?_, ?_⟩
  · rw [paraboloidEpigraph_fst_image_eq_univ]
    simp
  · exact recessionCone_fst_image_closure_ne_fst_image_recessionCone_closure_paraboloidEpigraph
      (𝕜 := 𝕜) hClosed

/-- Source-facing existential counterexample form of Remark 9.1.0.2:
there exist a closed convex set `C` and linear map `A` such that `A '' C` is closed and
`0⁺[𝕜] (A '' C) ≠ A '' 0⁺[𝕜] C`. -/
theorem exists_closed_convex_set_with_closed_linearImage_recessionCone_image_ne :
    IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) →
    ∃ (C : Set (𝕜 × 𝕜)) (A : (𝕜 × 𝕜) →ₗ[𝕜] 𝕜),
      IsClosed C ∧ Convex 𝕜 C ∧ IsClosed (A '' C) ∧ 0⁺[𝕜] (A '' C) ≠ A '' 0⁺[𝕜] C := by
  intro hClosed
  refine ⟨paraboloidEpigraph, fstₗ[𝕜],
    hClosed, paraboloidEpigraph_convex, ?_, ?_⟩
  · rw [paraboloidEpigraph_fst_image_eq_univ]
    simp
  · exact recessionCone_fst_image_ne_fst_image_recessionCone_paraboloidEpigraph

end Counterexample

section KernelLineality

variable {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsTopologicalRing 𝕜]

/-- The kernel-lineality hypothesis in Theorem 9.1 cannot hold for the
paraboloid/projection counterexample. -/
theorem not_recession_kernel_lineality_for_fst_paraboloidEpigraph :
    ¬ (fstₗ[𝕜].recessionKernelLeLineality (closure paraboloidEpigraph)) := by
  intro hkernel_lineality
  have hClosed : IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) := paraboloidEpigraph_isClosed
  have hCne : (paraboloidEpigraph : Set (𝕜 × 𝕜)).Nonempty := by
    exact ⟨(0, 0), by simp⟩
  have hEq :
      0⁺[𝕜] (fstₗ[𝕜] '' closure paraboloidEpigraph) =
        fstₗ[𝕜] '' 0⁺[𝕜] (closure paraboloidEpigraph) :=
    LinearMap.recessionCone_image_closure_eq_image_recessionCone
      (A := fstₗ[𝕜]) paraboloidEpigraph_convex hkernel_lineality hCne
  exact
    (recessionCone_fst_image_closure_ne_fst_image_recessionCone_closure_paraboloidEpigraph
      (𝕜 := 𝕜) hClosed) hEq

end KernelLineality
