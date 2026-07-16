import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u

namespace Representation

section FieldTransport

/-- Helper for Exercise 18-18.3-2: finite generation of a vector space is preserved when the
coefficient field is transported across a ring equivalence. -/
theorem moduleFinite_compHom_ringEquiv
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    (M : Type u) [AddCommGroup M] [Module K M] [Module.Finite K M] :
    letI : Module F M := Module.compHom M e.toRingHom
    Module.Finite F M := by
  letI : Module F M := Module.compHom M e.toRingHom
  let bK : Module.Basis (Module.Free.ChooseBasisIndex K M) K M :=
    Module.Free.chooseBasis K M
  letI : Finite (Module.Free.ChooseBasisIndex K M) :=
    Module.Finite.finite_basis bK
  let bF : Module.Basis (Module.Free.ChooseBasisIndex K M) F M :=
    bK.mapCoeffs e.symm (by
      intro c x
      change e (e.symm c) • x = c • x
      simp)
  exact Module.Finite.of_basis bF

/-- Helper for Exercise 18-18.3-2: replacing a field by an isomorphic coefficient field does not
change finite dimension. -/
theorem finrank_compHom_ringEquiv_eq
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    (M : Type u) [AddCommGroup M] [Module K M] [FiniteDimensional K M] :
    @Module.finrank F M _ _ (Module.compHom M e.toRingHom) = Module.finrank K M := by
  classical
  letI : Module F M := Module.compHom M e.toRingHom
  let bK : Module.Basis (Module.Free.ChooseBasisIndex K M) K M := Module.Free.chooseBasis K M
  let bF : Module.Basis (Module.Free.ChooseBasisIndex K M) F M :=
    bK.mapCoeffs e.symm (by
      intro c x
      change e (e.symm c) • x = c • x
      simp)
  rw [Module.finrank_eq_card_basis bF, Module.finrank_eq_card_basis bK]

/-- Helper for Exercise 18-18.3-2: transport a `K`-representation to an isomorphic coefficient
field, keeping the same underlying additive group and group action. -/
noncomputable def repOverRingEquiv
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    {G : Type u} [Group G] (S : FDRep K G) :
    letI : Module F S := Module.compHom S e.toRingHom
    Representation F G S := by
  letI : Module F S := Module.compHom S e.toRingHom
  exact
    { toFun := fun g ↦
        { toFun := fun x ↦ S.ρ g x
          map_add' := by
            intro x y
            exact (S.ρ g).map_add x y
          map_smul' := by
            intro a x
            change S.ρ g (e a • x) = e a • S.ρ g x
            exact (S.ρ g).map_smul (e a) x }
      map_one' := by
        ext x
        change S.ρ 1 x = x
        simp
      map_mul' := by
        intro g h
        ext x
        change S.ρ (g * h) x = S.ρ g (S.ρ h x)
        simp }

/-- Helper for Exercise 18-18.3-2: irreducibility is preserved by transport across an isomorphic
coefficient field. -/
theorem transported_irreducible_of_ringEquiv
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    {G : Type u} [Group G] (S : FDRep K G) [Simple S] :
    letI : Module F S := Module.compHom S e.toRingHom
    Representation.IsIrreducible (repOverRingEquiv e S) := by
  classical
  letI : Module F S := Module.compHom S e.toRingHom
  change Representation.IsIrreducible (repOverRingEquiv e S)
  have hSK : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  have hS_nontriv : Nontrivial S := by
    by_contra h
    letI : Subsingleton S := not_nontrivial_iff_subsingleton.mp h
    have hzero : (𝟙 S : S ⟶ S) = 0 := by
      ext x
      simp
    exact CategoryTheory.id_nonzero S hzero
  let ρF : Representation F G S := repOverRingEquiv e S
  have hbot_ne_top : (⊥ : Subrepresentation ρF) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    have hsub := congrArg Subrepresentation.toSubmodule h
    have hxbot : x ∈ (⊥ : Submodule F S) := by
      change x ∈ (⊥ : Subrepresentation ρF).toSubmodule
      rw [hsub]
      exact Submodule.mem_top
    exact hx (by simpa using hxbot)
  letI : Nontrivial (Subrepresentation ρF) := ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro N
  let NK : Subrepresentation S.ρ :=
    { toSubmodule :=
        { carrier := N.toSubmodule
          zero_mem' := N.toSubmodule.zero_mem'
          add_mem' := N.toSubmodule.add_mem'
          smul_mem' := by
            intro c x hx
            have hx' : (e.symm c) • x ∈ N.toSubmodule := N.toSubmodule.smul_mem (e.symm c) hx
            convert hx' using 1
            change c • x = e (e.symm c) • x
            simp }
      apply_mem_toSubmodule := by
        intro g x hx
        exact N.apply_mem_toSubmodule g hx }
  rcases IsSimpleOrder.eq_bot_or_eq_top NK with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ N.toSubmodule ↔ x ∈ (⊥ : Subrepresentation ρF).toSubmodule
    have hmem : x ∈ NK.toSubmodule ↔ x ∈ (⊥ : Subrepresentation S.ρ).toSubmodule := by
      rw [hbot]
    exact hmem
  · right
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ N.toSubmodule ↔ x ∈ (⊤ : Subrepresentation ρF).toSubmodule
    have hmem : x ∈ NK.toSubmodule ↔ x ∈ (⊤ : Subrepresentation S.ρ).toSubmodule := by
      rw [htop]
    exact hmem

/-- Helper for Exercise 18-18.3-2: transport self-intertwining maps across an isomorphic
coefficient field. -/
noncomputable def intertwiningMap_ringEquiv_linearEquiv
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    {G : Type u} [Group G] (S : FDRep K G) :
    letI : Module F S := Module.compHom S e.toRingHom
    let ρF : Representation F G S := repOverRingEquiv e S
    letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
      Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
    Representation.IntertwiningMap ρF ρF ≃ₗ[F]
      Representation.IntertwiningMap S.ρ S.ρ := by
  classical
  letI : Module F S := Module.compHom S e.toRingHom
  let ρF : Representation F G S := repOverRingEquiv e S
  letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
    Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
  exact
    { toFun := fun f ↦
        { toLinearMap :=
            { toFun := fun x ↦ f x
              map_add' := by
                intro x y
                exact f.map_add x y
              map_smul' := by
                intro c x
                have h := f.toLinearMap.map_smul (e.symm c) x
                change f (e (e.symm c) • x) = e (e.symm c) • f x at h
                simpa using h }
          isIntertwining' := by
            intro g
            ext x
            simpa [ρF, repOverRingEquiv] using
              (Representation.IntertwiningMap.isIntertwining
                (repOverRingEquiv e S) (repOverRingEquiv e S) f g x) }
      invFun := fun f ↦
        { toLinearMap :=
            { toFun := fun x ↦ f x
              map_add' := by
                intro x y
                exact f.map_add x y
              map_smul' := by
                intro a x
                change f (e a • x) = e a • f x
                exact f.map_smul (e a) x }
          isIntertwining' := by
            intro g
            ext x
            simpa [ρF, repOverRingEquiv] using
              (Representation.IntertwiningMap.isIntertwining S.ρ S.ρ f g x) }
      left_inv := by
        intro f
        apply Representation.IntertwiningMap.ext
        rfl
      right_inv := by
        intro f
        apply Representation.IntertwiningMap.ext
        rfl
      map_add' := by
        intro f g
        apply Representation.IntertwiningMap.ext
        rfl
      map_smul' := by
        intro a f
        apply Representation.IntertwiningMap.ext
        ext x
        rfl }

/-- Helper for Exercise 18-18.3-2: transport a finite-dimensional representation to an isomorphic
coefficient field as an `FDRep`. -/
noncomputable def fdRepOverRingEquiv
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    {G : Type u} [Group G] (S : FDRep K G) : FDRep F G := by
  letI : Module F S := Module.compHom S e.toRingHom
  letI : Module.Finite F S := moduleFinite_compHom_ringEquiv e S
  exact FDRep.of (repOverRingEquiv e S)

end FieldTransport

end Representation
