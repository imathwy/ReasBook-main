import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap03.Definition_3_3_3_1
import LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_3_6
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap08.Definition_8_8_3_2
import LinearRepresentations_Serre_1977.Chap08.Exercise_8_8_3_9
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.MonomialCharacter

noncomputable section

namespace Representation

open CategoryTheory Rep
open scoped Representation SubgroupInduction
open scoped BigOperators Pointwise

section

variable {G : Type} [Group G] [Finite G]

/- Source/core/bridge triage:
* `source-facing`: `IsMonomialCharacter`, LinearRepresentations_Serre_1977's character-level notion of being induced from a
  degree-`1` complex character of a subgroup.
* `core/canonical`: the owner now lives in `LinearRepresentations_Serre_1977.Chap10.MonomialCharacter`.
* `bridge/view`: `MonoidHom.toCharacterRing` together with
  `Subgroup.characterRingInduction`, which move degree-`1` subgroup characters into the character
  ring.

Sampled owner declarations in this domain:
* `Representation.IsMonomial`
* `Representation.IsMonomialCharacter`
* `MonoidHom.toCharacterRing`
* `Subgroup.characterRingInduction`

Primitive data versus derived API:
the primitive source-facing data here is the subgroup `H` and degree-`1` character `α`.
Membership in `R(H)` is derived from the canonical owner `MonoidHom.toCharacterRing α`, and
membership in `R(G)` is then derived from the Chapter 9 induction owner. The representation-level
owner `Representation.IsMonomial` comes directly from Chapter 3, and the submodule owner
`monomialCharacterSpan` is defined from `IsMonomialCharacter` itself rather than repeating the
same witness data. -/

/-- Helper for Theorem 10-10.5-2: a one-dimensional finite-dimensional complex representation is
afforded by a linear character. -/
theorem exists_linear_character_of_fdRep_finrank_one
    {G : Type} [Group G]
    (V : FDRep ℂ G) (hV : Module.finrank ℂ V = 1) :
    ∃ α : G →* ℂˣ, V.character = α.toRepresentation.character := by
  let scalarEquiv : ℂ ≃ₗ[ℂ] (V →ₗ[ℂ] V) := LinearEquiv.smul_id_of_finrank_eq_one hV
  have hscalar (c : ℂ) : scalarEquiv c = c • LinearMap.id := by
    -- The finrank-one endomorphism space is identified with scalar multiplication.
    exact LinearEquiv.smul_id_of_finrank_eq_one_apply hV c
  let α₀ : G → ℂ := fun g ↦ scalarEquiv.symm (V.ρ g)
  have hα₀_eq (g : G) : V.ρ g = α₀ g • LinearMap.id := by
    -- Each action map on a one-dimensional space is scalar multiplication by a unique scalar.
    calc
      V.ρ g = scalarEquiv (α₀ g) := by
        simp [α₀]
      _ = α₀ g • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    -- The identity group element acts by the identity endomorphism.
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = V.ρ 1 := by
        simp [α₀]
      _ = (1 : V →ₗ[ℂ] V) := by
        simp
      _ = scalarEquiv 1 := by
        simpa using (hscalar (1 : ℂ)).symm
  have hα₀_mul (g h : G) : α₀ (g * h) = α₀ g * α₀ h := by
    -- Multiplicativity of the representation turns the scalar assignment into a character.
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (g * h)) = V.ρ (g * h) := by
        simp [α₀]
      _ = V.ρ g * V.ρ h := by
        simp
      _ = (α₀ g * α₀ h) • LinearMap.id := by
        rw [hα₀_eq, hα₀_eq]
        ext x
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ g * α₀ h) := (hscalar _).symm
  have hα₀_ne_zero (g : G) : α₀ g ≠ 0 := by
    -- Every representation operator is invertible, so its scalar on a nonzero line is nonzero.
    have hpos : 0 < Module.finrank ℂ V := by
      simp [hV]
    letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    intro hg0
    have hzero : V.ρ g = 0 := by
      simp [hα₀_eq, hg0]
    have hone : (1 : V →ₗ[ℂ] V) ≠ 0 := one_ne_zero
    have hmul : V.ρ g * V.ρ g⁻¹ = (1 : V →ₗ[ℂ] V) := by
      simpa using (V.ρ.map_mul g g⁻¹).symm
    have hidzero : (1 : V →ₗ[ℂ] V) = 0 := by
      calc
        (1 : V →ₗ[ℂ] V) = V.ρ g * V.ρ g⁻¹ := hmul.symm
        _ = 0 := by
          rw [hzero]
          simp
    exact hone hidzero
  let α : G →* ℂˣ :=
    { toFun := fun g ↦ Units.mk0 (α₀ g) (hα₀_ne_zero g)
      map_one' := by
        ext
        exact hα₀_one
      map_mul' g h := by
        ext
        exact hα₀_mul g h }
  refine ⟨α, ?_⟩
  ext g
  -- Taking traces of the scalar action recovers the original character.
  rw [MonoidHom.toRepresentation_character_apply]
  calc
    V.character g = LinearMap.trace ℂ V (V.ρ g) := by
      rfl
    _ = LinearMap.trace ℂ V (α₀ g • LinearMap.id) := by
      rw [hα₀_eq]
    _ = α₀ g * LinearMap.trace ℂ V LinearMap.id := by
      simp [smul_eq_mul]
    _ = α₀ g * Module.finrank ℂ V := by
      simp [LinearMap.trace_id]
    _ = α₀ g := by
      simp [hV]
    _ = (α g : ℂ) := rfl

/-- Helper for isMonomialCharacter_of_isMonomial: once a representation is identified with the
standard induced model attached to a one-dimensional subrepresentation, its character is
monomial. -/
theorem isMonomialCharacter_of_equiv_induced_finrank_one
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V}
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (hWfinrank : Module.finrank ℂ W.toSubmodule = 1)
    (eInd : ρ.Equiv ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ)) :
    IsMonomialCharacter ρ.character := by
  letI : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨α, hαchar⟩ :=
    exists_linear_character_of_fdRep_finrank_one (FDRep.of W.toRepresentation) hWfinrank
  have hWchar : W.toRepresentation.character = α.toRepresentation.character := by
    -- Rebundle the one-dimensional source representation as the character of a linear character.
    simpa using hαchar
  refine ⟨H, α, ?_⟩
  -- Compare `ρ` with the canonical induced model, then rewrite the inducing character.
  calc
    Ind[H](α.toRepresentation.character) = Ind[H](W.toRepresentation.character) := by
      rw [hWchar]
    _ = ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ).character := by
      simpa using
        (Subgroup.inducedClassFunction_eq_character_ind
          (H := H) (K := ℂ) (θ := W.toRepresentation))
    _ = ρ.character := by
      simpa using (Representation.char_iso eInd).symm
end

end Representation
