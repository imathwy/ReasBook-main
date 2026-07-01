import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixGroups UpperHalfPlane

universe u

-- Semantic search note: the requested `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was checked directly against mathlib's `UpperHalfPlane`/`PGL(2, ℝ)` action
-- API and the existing stabilizer lemma formalized in the previous item.

/-- Theorem 4: if `AutP` is the full automorphism group of the half-plane, acting on
`UpperHalfPlane`, and `ρ : PGL(2, ℝ) →* AutP` is the homographic subgroup map, then the source's
reduction is valid: once the stabilizer of `i`, formalized as `UpperHalfPlane.I`, is contained in
the homographic subgroup `ρ.range`, that subgroup already contains all automorphisms of the
half-plane. -/
theorem homographic_subgroup_eq_top_of_stabilizer_le
    {AutP : Type u} [Group AutP] [MulAction AutP ℍ]
    (ρ : PGL(2, ℝ) →* AutP)
    (hcompat : ∀ g : PGL(2, ℝ), ∀ z : ℍ, ρ g • z = g • z)
    (hstab : MulAction.stabilizer AutP UpperHalfPlane.I ≤ ρ.range) :
    ρ.range = ⊤ := by
  letI : MulAction.IsPretransitive ρ.range ℍ :=
    MulAction.IsPretransitive.of_smul_eq
      (fun g : PGL(2, ℝ) ↦ ⟨ρ g, ⟨g, rfl⟩⟩)
      (fun {g z} ↦ hcompat g z)
  apply le_antisymm le_top
  intro σ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ρ.range UpperHalfPlane.I (σ • UpperHalfPlane.I)
  rcases g with ⟨g, ⟨γ, rfl⟩⟩
  have hg' : ρ γ • UpperHalfPlane.I = σ • UpperHalfPlane.I := by
    simpa using hg
  have hfix : (ρ γ)⁻¹ * σ ∈ MulAction.stabilizer AutP UpperHalfPlane.I := by
    change ((ρ γ)⁻¹ * σ) • UpperHalfPlane.I = UpperHalfPlane.I
    calc
      ((ρ γ)⁻¹ * σ) • UpperHalfPlane.I = (ρ γ)⁻¹ • (σ • UpperHalfPlane.I) := by
        rw [mul_smul]
      _ = (ρ γ)⁻¹ • (ρ γ • UpperHalfPlane.I) := by rw [← hg']
      _ = UpperHalfPlane.I := inv_smul_smul _ _
  have hfix' : (ρ γ)⁻¹ * σ ∈ ρ.range := hstab hfix
  exact by
    have hγ : ρ γ ∈ ρ.range := ⟨γ, rfl⟩
    simpa using ρ.range.mul_mem hγ hfix'
