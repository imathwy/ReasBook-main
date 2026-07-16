import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1

noncomputable section

universe u v w x

namespace Representation

section

variable {K : Type v} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Theorem 12-12.6-2: any finite-dimensional `K`-representation contributes an honest
character-ring element even when its carrier lives in a larger universe. -/
private theorem rep_character_mem_characterRingOverField_universe_bridge_local
    {H : Type w} [Group H] [Finite H]
    {V : Type x} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K H V) :
    ρ.character ∈ R[K](H) := by
  let e := (Module.finBasis K V).equivFun
  let ρfin : Representation K H (Fin (Module.finrank K V) → K) :=
    { toFun := fun h ↦ e.conj (ρ h)
      map_one' := by
        calc
          e.conj (ρ 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id e
      map_mul' := by
        intro g h
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let τρ : Representation K H (ULift.{max w v} (Fin (Module.finrank K V) → K)) :=
    { toFun := fun h ↦
        { toFun := fun x ↦ ⟨ρfin h x.down⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro a x
            ext
            simp }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [map_mul] }
  let τ : Rep K H := Rep.of τρ
  have hfin : ρ.character = ρfin.character := by
    -- Conjugation preserves trace, so the finite coordinate model has the same character.
    ext h
    symm
    simpa [τ, ρfin, Representation.character] using
      (LinearMap.trace_conj' (ρ h) e)
  have hulift : τ.ρ.character = ρfin.character := by
    -- `ULift` does not change trace values.
    ext h
    change
      LinearMap.trace K (ULift.{max w v} (Fin (Module.finrank K V) → K))
          ((ULift.moduleEquiv.symm : (Fin (Module.finrank K V) → K) ≃ₗ[K]
            ULift.{max w v} (Fin (Module.finrank K V) → K)).conj (ρfin h)) =
        LinearMap.trace K (Fin (Module.finrank K V) → K) (ρfin h)
    simpa [τ, τρ] using
      (LinearMap.trace_conj' (ρfin h)
        (ULift.moduleEquiv.symm : (Fin (Module.finrank K V) → K) ≃ₗ[K]
          ULift.{max w v} (Fin (Module.finrank K V) → K)))
  have hchar : ρ.character = τ.ρ.character := by
    exact hfin.trans hulift.symm
  exact hchar ▸ rep_character_mem_characterRingOverField (K := K) (G := H) τ

/-- Helper for Theorem 12-12.6-2: precomposing a virtual `K`-character with a multiplicative
equivalence preserves membership in the corresponding character ring. -/
theorem mem_characterRingOverField_of_precomp_mulEquiv_local
    {H : Type w} [Group H] [Finite H]
    (e : H ≃* G) {χ : G → K} (hχ : χ ∈ R[K](G)) :
    (fun h : H ↦ χ (e h)) ∈ R[K](H) := by
  -- Transport each honest character generator through the multiplicative equivalence `e`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    let τ : Representation K H ρ := ρ.ρ.comp e.toMonoidHom
    letI : FiniteDimensional K ρ := hρfd
    -- The transported representation has the expected precomposed character.
    simpa [τ] using
      rep_character_mem_characterRingOverField_universe_bridge_local
        (K := K) (H := H) (ρ := τ)
  · intro n
    exact (R[K](H)).algebraMap_mem n
  · intro f g _ _ hf hg
    simpa using (R[K](H)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa using (R[K](H)).mul_mem hf hg

/-- Helper for Theorem 12-12.6-2: transport `R_K(G)` to the same-universe copy
`R_K(Shrink G)` by precomposition with `Shrink.mulEquiv`. -/
noncomputable def characterRingOverField_shrink_transport_linearEquiv_local :
    R[K](G) ≃ₗ[ℤ] R[K](Shrink.{v} G) where
  toFun χ :=
    ⟨fun g : Shrink.{v} G ↦ (χ : G → K) (Shrink.mulEquiv g),
      mem_characterRingOverField_of_precomp_mulEquiv_local
        (K := K) (G := G) (e := (Shrink.mulEquiv : Shrink.{v} G ≃* G)) χ.property⟩
  invFun χ :=
    ⟨fun g : G ↦ (χ : Shrink.{v} G → K) ((Shrink.mulEquiv : Shrink.{v} G ≃* G).symm g),
      mem_characterRingOverField_of_precomp_mulEquiv_local
        (K := K) (G := Shrink.{v} G) (H := G)
        (e := (Shrink.mulEquiv : Shrink.{v} G ≃* G).symm) χ.property⟩
  left_inv χ := by
    ext g
    simp
  right_inv χ := by
    ext g
    simp
  map_add' χ ψ := by
    ext g
    rfl
  map_smul' n χ := by
    ext g
    rfl

/-- Helper for Theorem 12-12.6-2: the shrink transport is pointwise precomposition with
`Shrink.mulEquiv`. -/
@[simp] theorem characterRingOverField_shrink_transport_linearEquiv_local_apply
    (χ : R[K](G)) (g : Shrink.{v} G) :
    characterRingOverField_shrink_transport_linearEquiv_local (K := K) (G := G) χ g =
      (χ : G → K) (Shrink.mulEquiv g) :=
  by
    change (fun g' : Shrink.{v} G ↦ (χ : G → K) (Shrink.mulEquiv g')) g =
      (χ : G → K) (Shrink.mulEquiv g)
    rfl

/-- Helper for Theorem 12-12.6-2: the inverse shrink transport is pointwise precomposition with
`Shrink.mulEquiv.symm`. -/
@[simp] theorem characterRingOverField_shrink_transport_linearEquiv_local_symm_apply
    (χ : R[K](Shrink.{v} G)) (g : G) :
    (characterRingOverField_shrink_transport_linearEquiv_local
        (K := K) (G := G)).symm χ g =
      (χ : Shrink.{v} G → K) ((Shrink.mulEquiv : Shrink.{v} G ≃* G).symm g) :=
  by
    change (fun g' : G ↦
      (χ : Shrink.{v} G → K) ((Shrink.mulEquiv : Shrink.{v} G ≃* G).symm g')) g =
        (χ : Shrink.{v} G → K) ((Shrink.mulEquiv : Shrink.{v} G ≃* G).symm g)
    rfl

end

end Representation
