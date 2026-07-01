import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {k : Type v} {E : Type u} [Ring k] [LE k]
  [AddCommGroup E] [Module k E]

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 8.1.1 identifies the recession directions of a nonempty affine set
  with its parallel linear subspace.
- `core/canonical`: the chapter owner is `recessionCone`, and the affine owner is
  `AffineSubspace.direction`.
- `bridge/view`: `Set.mem_recessionCone_iff` expands recession-cone membership into the source ray
  condition, while `AffineSubspace.vadd_mem_iff_mem_direction` is the canonical affine-owner
  bridge between translated-point membership and direction membership. The source-facing parallel
  submodule phrasing is exposed below as a thin bridge theorem derived from
  `AffineSubspace.Parallel.direction_eq` and `Submodule.toAffineSubspace_direction`.
- Domain-style sampling used here: `Set.mem_recessionCone_iff`,
  `AffineSubspace.vadd_mem_iff_mem_direction`,
  `AffineSubspace.Parallel.direction_eq`, and `Submodule.toAffineSubspace_direction`.
- Primitive data vs derived API: the primitive data are just the affine subspace `M` and its
  intrinsic nonemptiness datum `[Nonempty M]`. Any equality with a separately named parallel
  submodule is derived API from the owner theorem below, and the submodule bridge theorem derives
  this nonemptiness from parallelism to `D.toAffineSubspace`.
- Layer target: this refinement is `core/canonical`; the source wording is recovered from the
  owner theorem through the thin parallel bridge theorem below.
-/

namespace AffineSubspace

variable [ZeroLEOneClass k]

/-- Corollary 8.1.1, owner form: the recession cone of a nonempty affine set is exactly its
direction subspace. The proof uses only affine-module algebra and the scalar-side fact `0 ≤ 1`,
so the owner theorem is kept at this weaker ordered-scalar layer; specializing to `ℝ` recovers
the textbook statement `0⁺[k] M = (M.direction : Set E)`. -/
theorem recessionCone_eq_direction
    (M : AffineSubspace k E) [Nonempty M] :
    0⁺[k] M = (M.direction : Set E) := by
  ext y
  rw [Set.mem_recessionCone_iff]
  constructor
  · intro hy
    rcases (show Nonempty M from inferInstance) with ⟨⟨x, hx⟩⟩
    have hxy : y +ᵥ x ∈ M := by
      simpa [vadd_eq_add, add_comm] using hy x hx 1 zero_le_one
    exact (M.vadd_mem_iff_mem_direction y hx).1 hxy
  · intro hy x hx a ha
    have haxy : a • y +ᵥ x ∈ M :=
      M.vadd_mem_of_mem_direction (M.direction.smul_mem a hy) hx
    simpa [vadd_eq_add, add_comm] using haxy

/-- Corollary 8.1.1, source-facing bridge: if `M` is nonempty and parallel to `N`, then the
recession cone of `M` is exactly the direction of `N`. -/
theorem recessionCone_eq_direction_of_parallel
    (M N : AffineSubspace k E) (hMN : M.Parallel N) (hM : Nonempty M) :
    0⁺[k] M = (N.direction : Set E) := by
  letI : Nonempty M := hM
  calc
    0⁺[k] (M : Set E) = (M.direction : Set E) := M.recessionCone_eq_direction
    _ = (N.direction : Set E) := by
      simpa using congrArg (fun S : Submodule k E => (S : Set E)) hMN.direction_eq

/-- Corollary 8.1.1, source-facing bridge: if an affine subspace `M` is parallel to a
submodule `D`, then the recession cone of `M` is exactly `D`. -/
theorem recessionCone_eq_of_parallel
    (M : AffineSubspace k E) (D : Submodule k E)
    (hMD : M.Parallel D.toAffineSubspace) :
    0⁺[k] M = (D : Set E) := by
  have hD : Nonempty D.toAffineSubspace := by
    refine ⟨⟨0, ?_⟩⟩
    simp [Submodule.mem_toAffineSubspace]
  have hM : Nonempty M := by
    rcases hMD.symm with ⟨v, rfl⟩
    rcases hD with ⟨⟨x, hx⟩⟩
    refine ⟨⟨v +ᵥ x, ?_⟩⟩
    exact AffineSubspace.mem_map_of_mem
      (f := (AffineEquiv.constVAdd k E v : E →ᵃ[k] E)) hx
  calc
    0⁺[k] (M : Set E) = (D.toAffineSubspace.direction : Set E) :=
      recessionCone_eq_direction_of_parallel (M := M) (N := D.toAffineSubspace) hMD hM
    _ = (D : Set E) := by simp

end AffineSubspace

end
