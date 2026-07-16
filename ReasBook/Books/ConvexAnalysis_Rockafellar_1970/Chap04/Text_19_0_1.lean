import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped Rockafellar

section OwnerLayer

variable {𝕜 : Type v} {E : Type u}
variable [Preorder 𝕜]

namespace Set

/-- Owner-primary finite bridge: a set is polyhedral iff it is cut out by a finite family of weak
pairing inequalities, encoded by a finite subset of `(Y × 𝕜)` and the canonical chapter owner
`solutionSet[·]`. -/
theorem isPolyhedral_iff_exists_pairing_le {Y : Type w} [HasPairing E Y 𝕜]
    {s : Set E} :
    s.IsPolyhedral 𝕜 Y ↔
      ∃ S : Finset (Y × 𝕜), s = solutionSet[(S : Set (Y × 𝕜))] := by
  constructor
  · rintro ⟨S, rfl⟩
    refine ⟨S, ?_⟩
    ext x
    simp [linearInequalitySolutionSet_eq_iInter_closedHalfSpaceLE]
  · rintro ⟨S, rfl⟩
    refine ⟨S, ?_⟩
    ext x
    simp [linearInequalitySolutionSet_eq_iInter_closedHalfSpaceLE]

/-- Set-builder companion of `Set.isPolyhedral_iff_exists_pairing_le`. -/
theorem isPolyhedral_iff_exists_pairing_le_setOf {Y : Type w} [HasPairing E Y 𝕜]
    {s : Set E} :
    s.IsPolyhedral 𝕜 Y ↔
      ∃ S : Finset (Y × 𝕜), s = {x : E | ∀ y ∈ S, ⟪x, y.1⟫ₚ ≤ y.2} := by
  constructor
  · intro hs
    rcases (isPolyhedral_iff_exists_pairing_le (Y := Y) (s := s)).1 hs with ⟨S, hsS⟩
    refine ⟨S, ?_⟩
    rw [hsS]
    ext x
    simp
  · rintro ⟨S, hsS⟩
    refine (isPolyhedral_iff_exists_pairing_le (Y := Y) (s := s)).2 ?_
    refine ⟨S, ?_⟩
    rw [hsS]
    ext x
    simp

/-- Finite-index owner corollary: any finite weak pairing system defines a polyhedral set. -/
theorem isPolyhedral_setOf_forall_pairing_le {Y : Type w} [HasPairing E Y 𝕜]
    {I : Type*} [Finite I] (b : I → Y) (β : I → 𝕜) :
    ({x : E | ∀ i, ⟪x, b i⟫ₚ ≤ β i}).IsPolyhedral 𝕜 Y := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  refine (isPolyhedral_iff_exists_pairing_le_setOf
    (Y := Y) (s := ({x : E | ∀ i, ⟪x, b i⟫ₚ ≤ β i} : Set E))).2 ?_
  refine ⟨Finset.univ.image (fun i : I ↦ (b i, β i)), ?_⟩
  ext x
  constructor
  · intro hx
    change ∀ y ∈ Finset.univ.image (fun i : I ↦ (b i, β i)), ⟪x, y.1⟫ₚ ≤ y.2
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, -, rfl⟩
    exact hx i
  · intro hx
    change ∀ i : I, ⟪x, b i⟫ₚ ≤ β i
    intro i
    exact hx (b i, β i) (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)

section LinearSpecialization

variable [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-- Linear-functional owner-primary finite bridge:
`Y := E →ₗ[𝕜] 𝕜` in `Set.isPolyhedral_iff_exists_pairing_le_setOf`. -/
theorem isPolyhedral_iff_exists_linear_le {s : Set E} :
    s.IsPolyhedral 𝕜 (E →ₗ[𝕜] 𝕜) ↔
      ∃ S : Finset ((E →ₗ[𝕜] 𝕜) × 𝕜),
        s = {x : E | ∀ y ∈ S, y.1 x ≤ y.2} := by
  simpa using
    (isPolyhedral_iff_exists_pairing_le_setOf
      (Y := E →ₗ[𝕜] 𝕜) (s := s))

/-- Finite-index linear-functional specialization of
`Set.isPolyhedral_setOf_forall_pairing_le` (`Y := E →ₗ[𝕜] 𝕜`). -/
theorem isPolyhedral_setOf_forall_linear_le {I : Type*} [Finite I] (ℓ : I → E →ₗ[𝕜] 𝕜)
    (β : I → 𝕜) :
    ({x : E | ∀ i, ℓ i x ≤ β i}).IsPolyhedral 𝕜 (E →ₗ[𝕜] 𝕜) := by
  simpa using
    (isPolyhedral_setOf_forall_pairing_le (Y := E →ₗ[𝕜] 𝕜) (I := I) ℓ β)

end LinearSpecialization

end Set

end OwnerLayer
