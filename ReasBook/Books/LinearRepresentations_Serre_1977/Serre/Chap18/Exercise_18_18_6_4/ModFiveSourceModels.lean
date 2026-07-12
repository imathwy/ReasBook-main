import Mathlib
import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.SymmetricBaseChangeFinrank
import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.ScalarSymmetricPowers
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_9
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_5_3

noncomputable section

open CategoryTheory
open Representation
open scoped MatrixGroups
open scoped TensorProduct

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-4: once `A₅ ≃ PSL₂(𝔽₅)` is available, the even symmetric powers
of the natural `SL₂(𝔽₅)`-module descend through the center and transport to simple `A₅`-modules
of degrees `3` and `5`. -/
theorem alternatingGroup_fin5_modFive_degree_three_and_five_source_models
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5]
    (hA5PSL : Nonempty (A5 ≃* PSL(2, ZMod 5))) :
    ∃ E3 E5 : FDRep k A5,
      Simple E3 ∧ Simple E5 ∧
        Module.finrank k E3.V = 3 ∧ Module.finrank k E5.V = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Algebra (ZMod 5) k := ZMod.algebra k 5
  obtain ⟨e⟩ := hA5PSL
  let eSL : SL(2, ZMod 5) ≃* SpecialLinearGroup (ZMod 5) (Fin 2 → ZMod 5) :=
    Matrix.SpecialLinearGroup.toLin'_equiv (R := ZMod 5) (n := Fin 2)
  let Vk := k ⊗[ZMod 5] (Fin 2 → ZMod 5)
  let W2 := SymmetricPower k (Fin 2) Vk
  let W4 := SymmetricPower k (Fin 4) Vk
  -- Record finite-dimensionality of the base-changed carrier `Vk` once, as a local instance.
  -- Otherwise each symmetric-power dimension lemma re-runs the expensive base-change instance
  -- search against the `let`-bound `Vk`, which alone exhausts the per-declaration heartbeat budget.
  haveI : FiniteDimensional k Vk :=
    Module.Finite.base_change (ZMod 5) k (Fin 2 → ZMod 5)
  let ρSLₖ :
      Representation k
        (SpecialLinearGroup (ZMod 5) (Fin 2 → ZMod 5))
        Vk :=
    scalarExtension
      (Representation.ofDistribMulAction (ZMod 5)
        (SpecialLinearGroup (ZMod 5) (Fin 2 → ZMod 5)) (Fin 2 → ZMod 5))
  let ρstd :
      Representation k
        (SL(2, ZMod 5))
        Vk :=
    ρSLₖ.comp eSL.toMonoidHom
  let Z :
      Subgroup (SL(2, ZMod 5)) :=
    Subgroup.center (SL(2, ZMod 5))
  have hρstd_center_scalar (z : Z) :
      ∃ ν : k, ν ^ 2 = 1 ∧ ρstd z = ν • LinearMap.id := by
    let z' : Subgroup.center (SpecialLinearGroup (ZMod 5) (Fin 2 → ZMod 5)) :=
      (Subgroup.centerCongr eSL) z
    let μ : ZMod 5 := (SpecialLinearGroup.centerEquivRootsOfUnity z' : (ZMod 5)ˣ)
    have hz_linear :
        ((eSL z : SpecialLinearGroup (ZMod 5) (Fin 2 → ZMod 5)) :
            (Fin 2 → ZMod 5) →ₗ[ZMod 5] (Fin 2 → ZMod 5)) =
          μ • LinearMap.id := by
      simpa [μ] using SpecialLinearGroup.centerEquivRootsOfUnity_apply z'
    have hμ2 : μ ^ 2 = 1 := by
      have hμ :
          (SpecialLinearGroup.centerEquivRootsOfUnity z' : (ZMod 5)ˣ) ^ 2 = 1 := by
        simpa [rootsOfUnity] using (SpecialLinearGroup.centerEquivRootsOfUnity z').property
      simpa [μ] using congrArg Units.val hμ
    let ν : k := algebraMap (ZMod 5) k μ
    refine ⟨ν, ?_, ?_⟩
    · simpa [ν] using congrArg (algebraMap (ZMod 5) k) hμ2
    · apply TensorProduct.AlgebraTensorModule.ext
      intro a v
      change (LinearMap.baseChange k (eSL z))
          (a ⊗ₜ[ZMod 5] v) = ν • (a ⊗ₜ[ZMod 5] v)
      rw [LinearMap.baseChange_tmul, hz_linear]
      simp [ν, μ, TensorProduct.tmul_smul]
  letI : Representation.IsTrivial ((nthSymmetricPower ρstd 2).comp Z.subtype) := by
    refine ⟨?_⟩
    intro z
    rcases hρstd_center_scalar z with ⟨ν, hν2, hzν⟩
    calc
      (nthSymmetricPower ρstd 2) z = SymmetricPower.map 2 (ρstd z) := rfl
      _ = SymmetricPower.map 2 (ν • (LinearMap.id : _ →ₗ[k] _)) := by rw [hzν]
      _ = ν ^ 2 • (LinearMap.id : SymmetricPower k (Fin 2) _ →ₗ[k] SymmetricPower k (Fin 2) _) :=
            Representation.symmetricPower_map_smul_id 2 ν
      _ = 1 := by simp [hν2, Module.End.one_eq_id]
  letI : Representation.IsTrivial ((nthSymmetricPower ρstd 4).comp Z.subtype) := by
    refine ⟨?_⟩
    intro z
    rcases hρstd_center_scalar z with ⟨ν, hν2, hzν⟩
    have hν4 : ν ^ 4 = 1 := by
      calc
        ν ^ 4 = (ν ^ 2) ^ 2 := by ring_nf
        _ = 1 := by simp [hν2]
    calc
      (nthSymmetricPower ρstd 4) z = SymmetricPower.map 4 (ρstd z) := rfl
      _ = SymmetricPower.map 4 (ν • (LinearMap.id : _ →ₗ[k] _)) := by rw [hzν]
      _ = ν ^ 4 • (LinearMap.id : SymmetricPower k (Fin 4) _ →ₗ[k] SymmetricPower k (Fin 4) _) :=
            Representation.symmetricPower_map_smul_id 4 ν
      _ = 1 := by simp [hν4, Module.End.one_eq_id]
  let τ2 :
      Representation k (PSL(2, ZMod 5)) W2 := by
    simpa [Matrix.ProjectiveSpecialLinearGroup] using
      (nthSymmetricPower ρstd 2).ofQuotient Z
  let τ4 :
      Representation k (PSL(2, ZMod 5)) W4 := by
    simpa [Matrix.ProjectiveSpecialLinearGroup] using
      (nthSymmetricPower ρstd 4).ofQuotient Z
  have hsymm2_irreducible : Representation.IsIrreducible (nthSymmetricPower ρstd 2) := by
    letI : Representation.IsIrreducible (nthSymmetricPower ρSLₖ 2) := by
      exact
        Representation.specialLinearNthSymmetricPower_isAbsolutelyIrreducible_of_finrank_eq_two
        (p := 5) (K := k) (V := Fin 2 → ZMod 5)
        (by simp) (i := 2) (by decide)
    simpa [ρstd, ρSLₖ, eSL] using
      Representation.isIrreducible_comp_of_mulEquiv_local_c16 eSL
        (nthSymmetricPower ρSLₖ 2)
  have hsymm4_irreducible : Representation.IsIrreducible (nthSymmetricPower ρstd 4) := by
    letI : Representation.IsIrreducible (nthSymmetricPower ρSLₖ 4) := by
      exact
        Representation.specialLinearNthSymmetricPower_isAbsolutelyIrreducible_of_finrank_eq_two
        (p := 5) (K := k) (V := Fin 2 → ZMod 5)
        (by simp) (i := 4) (by decide)
    simpa [ρstd, ρSLₖ, eSL] using
      Representation.isIrreducible_comp_of_mulEquiv_local_c16 eSL
        (nthSymmetricPower ρSLₖ 4)
  have hτ2_irreducible : τ2.IsIrreducible := by
    letI : Representation.IsIrreducible (nthSymmetricPower ρstd 2) := hsymm2_irreducible
    simpa [τ2] using
      Representation.isIrreducible_of_ofQuotient_of_isTrivial_e1853
        (σ := nthSymmetricPower ρstd 2) Z
  have hτ4_irreducible : τ4.IsIrreducible := by
    letI : Representation.IsIrreducible (nthSymmetricPower ρstd 4) := hsymm4_irreducible
    simpa [τ4] using
      Representation.isIrreducible_of_ofQuotient_of_isTrivial_e1853
        (σ := nthSymmetricPower ρstd 4) Z
  let ρ3 : Representation k A5 W2 :=
    τ2.comp e.toMonoidHom
  let ρ5 : Representation k A5 W4 :=
    τ4.comp e.toMonoidHom
  let E3 : FDRep k A5 := FDRep.of ρ3
  let E5 : FDRep k A5 := FDRep.of ρ5
  have hE3_simple : Simple E3 := by
    have hρ3_irreducible : Representation.IsIrreducible ρ3 := by
      simpa [τ2] using Representation.isIrreducible_comp_of_mulEquiv_local_c16 e τ2
    letI : Representation.IsIrreducible ((FDRep.of ρ3).ρ) := by
      simpa using hρ3_irreducible
    change Simple (FDRep.of ρ3)
    exact FDRep.simple_of_isIrreducible (FDRep.of ρ3)
  have hE5_simple : Simple E5 := by
    have hρ5_irreducible : Representation.IsIrreducible ρ5 := by
      simpa [τ4] using Representation.isIrreducible_comp_of_mulEquiv_local_c16 e τ4
    letI : Representation.IsIrreducible ((FDRep.of ρ5).ρ) := by
      simpa using hρ5_irreducible
    change Simple (FDRep.of ρ5)
    exact FDRep.simple_of_isIrreducible (FDRep.of ρ5)
  have hbase : Module.finrank k Vk = 2 := by
    change Module.finrank k (TensorProduct (ZMod 5) k (Fin 2 → ZMod 5)) = 2
    rw [Module.finrank_baseChange (R := k) (S := ZMod 5) (M' := Fin 2 → ZMod 5)]
    simp
  have hE3_finrank : Module.finrank k E3.V = 3 := by
    have hsymm : Module.finrank k W2 = 3 := by
      rw [Representation.finrank_symmetricPower_eq_multichoose (k := k) (V := Vk) (n := 1), hbase]
      norm_num
    change Module.finrank k W2 = 3
    exact hsymm
  have hE5_finrank : Module.finrank k E5.V = 5 := by
    -- State the symmetric-power dimension in the lemma's exact `Fin (n + 1)` shape so the rewrite
    -- matches syntactically instead of forcing an expensive `isDefEq` against the `let`-bound `W4`.
    have hsymm : Module.finrank k (SymmetricPower k (Fin (3 + 1)) Vk) = 5 := by
      rw [Representation.finrank_symmetricPower_eq_multichoose (k := k) (V := Vk) (n := 3), hbase]
      norm_num
    exact hsymm
  exact ⟨E3, E5, hE3_simple, hE5_simple, hE3_finrank, hE5_finrank⟩
