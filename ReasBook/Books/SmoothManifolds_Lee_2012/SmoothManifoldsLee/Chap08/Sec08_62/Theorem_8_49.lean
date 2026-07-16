import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Semisimple.Basic
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_62.Definition_8_62_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this runner; the owner abstraction for finite-dimensional
-- Lie-algebra representations in this section is the canonical `LieModule` / `LieModule.IsFaithful`
-- surface recalled in `Definition_8_62_extra_1`.

universe u𝕜 u𝔤

section

variable (𝕜 : Type u𝕜) [Field 𝕜]
variable (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra 𝕜 𝔤]

/-- Helper for Theorem 8.49: an injective matrix-valued Lie algebra homomorphism yields a faithful
pulled-back action on the standard module `Fin n → 𝕜`. -/
lemma faithfulPullbackOfInjectiveMatrixHom
    {n : ℕ} (ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜) (hρ : Function.Injective ρ) :
    letI : LieRingModule 𝔤 (Fin n → 𝕜) := LieRingModule.compLieHom (Fin n → 𝕜) ρ
    letI : LieModule 𝕜 𝔤 (Fin n → 𝕜) := LieModule.compLieHom (Fin n → 𝕜) ρ
    LieModule.IsFaithful 𝕜 𝔤 (Fin n → 𝕜) := by
  letI : LieRingModule 𝔤 (Fin n → 𝕜) := LieRingModule.compLieHom (Fin n → 𝕜) ρ
  letI : LieModule 𝕜 𝔤 (Fin n → 𝕜) := LieModule.compLieHom (Fin n → 𝕜) ρ
  refine LieModule.IsFaithful.mk ?_
  intro x y hxy
  apply hρ
  -- Compare the pulled-back action with the canonical faithful matrix action on `Fin n → 𝕜`.
  have hMatrix :
      Function.Injective
        (LieModule.toEnd 𝕜 (Matrix (Fin n) (Fin n) 𝕜) (Fin n → 𝕜)) :=
    (LieModule.isFaithful_iff 𝕜 (Matrix (Fin n) (Fin n) 𝕜) (Fin n → 𝕜)).mp inferInstance
  apply hMatrix
  apply LinearMap.ext
  intro v
  change ⁅ρ x, v⁆ = ⁅ρ y, v⁆
  simpa [LieRingModule.compLieHom_apply] using
    congrArg (fun f : Module.End 𝕜 (Fin n → 𝕜) ↦ f v) hxy

/-- Helper for Theorem 8.49: an injective matrix representation provides faithful action data on
the standard finite-dimensional module `Fin n → 𝕜`. -/
lemma faithfulRepresentationDataOfInjectiveMatrixHom
    (h :
      ∃ n : ℕ, ∃ ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜, Function.Injective ρ) :
    ∃ n : ℕ, ∃ (_ : FiniteDimensional 𝕜 (Fin n → 𝕜))
      (_ : LieRingModule 𝔤 (Fin n → 𝕜)) (_ : LieModule 𝕜 𝔤 (Fin n → 𝕜)),
        LieModule.IsFaithful 𝕜 𝔤 (Fin n → 𝕜) := by
  obtain ⟨n, ρ, hρ⟩ := h
  letI : LieRingModule 𝔤 (Fin n → 𝕜) := LieRingModule.compLieHom (Fin n → 𝕜) ρ
  letI : LieModule 𝕜 𝔤 (Fin n → 𝕜) := LieModule.compLieHom (Fin n → 𝕜) ρ
  -- Package the standard module together with the pulled-back action and the faithfulness bridge.
  refine ⟨n, inferInstance, inferInstance, inferInstance, ?_⟩
  exact faithfulPullbackOfInjectiveMatrixHom 𝕜 𝔤 ρ hρ

/-- Helper for Theorem 8.49: a faithful finite-dimensional `LieModule` witness already has the
exact existential shape required by the theorem. -/
lemma faithfulRepresentationPack
    (h :
      ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
        (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
          LieModule.IsFaithful 𝕜 𝔤 V) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
        LieModule.IsFaithful 𝕜 𝔤 V := by
  -- Unpack and repack the faithful module data without changing its structure.
  simpa using h

/-- Helper for Theorem 8.49: injectivity of `LieModule.toEnd 𝕜 𝔤 V` upgrades finite-dimensional
representation data to a faithful representation witness. -/
lemma faithfulRepresentationPackOfInjectiveToEnd
    (h :
      ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
        (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
          Function.Injective (LieModule.toEnd 𝕜 𝔤 V)) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
        LieModule.IsFaithful 𝕜 𝔤 V := by
  obtain ⟨V, hVAdd, hVModule, hVFinite, hVRingModule, hVLieModule, htoEnd⟩ := h
  letI : AddCommGroup V := hVAdd
  letI : Module 𝕜 V := hVModule
  letI : FiniteDimensional 𝕜 V := hVFinite
  letI : LieRingModule 𝔤 V := hVRingModule
  letI : LieModule 𝕜 𝔤 V := hVLieModule
  -- Promote the injective endomorphism-valued representation to faithfulness.
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact LieModule.IsFaithful.mk htoEnd

variable [CharZero 𝕜] [FiniteDimensional 𝕜 𝔤]

omit [CharZero 𝕜] in
/-- Helper for Theorem 8.49: if `𝔤` has trivial radical, then its adjoint self-action already gives
a faithful finite-dimensional `LieModule`. -/
lemma existsFaithfulFiniteDimensionalLieModuleOfHasTrivialRadical
    [LieAlgebra.HasTrivialRadical 𝕜 𝔤] :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V) (_ : FiniteDimensional 𝕜 V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V), LieModule.IsFaithful 𝕜 𝔤 V := by
  let e : ULift.{u𝕜} 𝔤 ≃ₗ[𝕜] 𝔤 := ULift.moduleEquiv
  let eLie := e.lieConj.symm
  let ρ : 𝔤 →ₗ⁅𝕜⁆ Module.End 𝕜 (ULift.{u𝕜} 𝔤) :=
    eLie.toLieHom.comp (LieModule.toEnd 𝕜 𝔤 𝔤)
  letI : FiniteDimensional 𝕜 (ULift.{u𝕜} 𝔤) :=
    FiniteDimensional.of_injective (e : ULift.{u𝕜} 𝔤 →ₗ[𝕜] 𝔤) e.injective
  letI : LieRingModule 𝔤 (ULift.{u𝕜} 𝔤) := LieRingModule.compLieHom (ULift.{u𝕜} 𝔤) ρ
  letI : LieModule 𝕜 𝔤 (ULift.{u𝕜} 𝔤) := LieModule.compLieHom (ULift.{u𝕜} 𝔤) ρ
  have hρ : Function.Injective ρ := by
    letI : LieModule.IsFaithful 𝕜 𝔤 𝔤 := inferInstance
    -- Conjugating the faithful self-representation preserves injectivity.
    exact eLie.injective.comp LieModule.IsFaithful.injective_toEnd
  have htoEnd_eq : LieModule.toEnd 𝕜 𝔤 (ULift.{u𝕜} 𝔤) = ρ := rfl
  have htoEnd : Function.Injective (LieModule.toEnd 𝕜 𝔤 (ULift.{u𝕜} 𝔤)) := by
    -- Rewrite the pulled-back action map to the conjugated representation `ρ`.
    rw [htoEnd_eq]
    exact hρ
  -- Package the transported self-representation as the required witness in the larger universe.
  refine ⟨ULift.{u𝕜} 𝔤, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  exact LieModule.IsFaithful.mk htoEnd

/-- Theorem 8.49 (Ado's Theorem): every finite-dimensional real Lie algebra admits a faithful
finite-dimensional representation, formalized as a finite-dimensional real vector space carrying a
faithful `LieModule` structure for `𝔤`. The corresponding Lie algebra homomorphism into an
endomorphism Lie algebra is the derived canonical map `LieModule.toEnd ℝ 𝔤 V`. -/
theorem exists_faithful_finite_dimensional_representation
    (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [FiniteDimensional ℝ 𝔤] :
    ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : FiniteDimensional ℝ V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule ℝ 𝔤 V), LieModule.IsFaithful ℝ 𝔤 V := sorry

end
