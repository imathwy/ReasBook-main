import Mathlib
import LinearRepresentations_Serre_1977.GroupTheory.ConjClassesPower
import LinearRepresentations_Serre_1977.Serre.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Serre.Chap06.Exercise_6_6_3_3
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_15
import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_16.Index
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1

open CategoryTheory
open IsCyclotomicExtension.Rat
open scoped IsMulCommutative MonoidAlgebra Representation TensorProduct
open Representation

noncomputable section

universe u

section ExerciseClauses

variable {G : Type u} [Group G] [Finite G]
variable {K : Type u} [Field K] [NumberField K]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ K]

section CyclotomicSplitSchur

private theorem hasEnoughRootsOfUnity_of_cyclotomic :
    HasEnoughRootsOfUnity K (Monoid.exponent G) := by
  classical
  letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  refine
    { prim := ?_
      cyc := rootsOfUnity.isCyclic _ _ }
  simpa using
    (IsCyclotomicExtension.exists_isPrimitiveRoot
      (S := {Monoid.exponent G}) (A := ℚ) (B := K)
      (n := Monoid.exponent G) (by simp)
      (show Monoid.exponent G ≠ 0 by exact NeZero.ne _))

private theorem hasEnoughRootsOfUnity_laurentSeries
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) := by
  classical
  letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent G)
  have hprim : (primitiveRoots (Monoid.exponent G) K).Nonempty := by
    refine ⟨ζ, ?_⟩
    rw [mem_primitiveRoots (NeZero.pos (Monoid.exponent G))]
    exact hζ
  exact
    MulEquiv.hasEnoughRootsOfUnity
      (rootsOfUnityEquivOfPrimitiveRoots
        (S := LaurentSeries K)
        (f := algebraMap K (LaurentSeries K))
        (algebraMap K (LaurentSeries K)).injective
        hprim)

private theorem finrank_compHom_ringEquiv_eq
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    (M : Type u) [AddCommGroup M] [Module K' M] [FiniteDimensional K' M] :
    @Module.finrank F M _ _ (Module.compHom M e.toRingHom) = Module.finrank K' M := by
  classical
  letI : Module F M := Module.compHom M e.toRingHom
  let bK : Module.Basis (Module.Free.ChooseBasisIndex K' M) K' M :=
    Module.Free.chooseBasis K' M
  let bF : Module.Basis (Module.Free.ChooseBasisIndex K' M) F M :=
    bK.mapCoeffs e.symm (by
      intro c x
      change e (e.symm c) • x = c • x
      simp)
  rw [Module.finrank_eq_card_basis bF, Module.finrank_eq_card_basis bK]

private theorem finiteDimensional_compHom_ringEquiv
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    (M : Type u) [AddCommGroup M] [Module K' M] [FiniteDimensional K' M] :
    letI : Module F M := Module.compHom M e.toRingHom
    FiniteDimensional F M := by
  classical
  letI : Module F M := Module.compHom M e.toRingHom
  let bK : Module.Basis (Module.Free.ChooseBasisIndex K' M) K' M :=
    Module.Free.chooseBasis K' M
  let bF : Module.Basis (Module.Free.ChooseBasisIndex K' M) F M :=
    bK.mapCoeffs e.symm (by
      intro c x
      change e (e.symm c) • x = c • x
      simp)
  exact Module.Basis.finiteDimensional_of_finite bF

private theorem trace_compHom_ringEquiv_eq
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    (M : Type u) [AddCommGroup M] [Module K' M] [FiniteDimensional K' M]
    (f : M →ₗ[K'] M) :
    letI : Module F M := Module.compHom M e.toRingHom
    let fF : M →ₗ[F] M :=
      { toFun := fun x ↦ f x
        map_add' := by intro x y; exact f.map_add x y
        map_smul' := by
          intro a x
          change f (e a • x) = e a • f x
          exact f.map_smul (e a) x }
    LinearMap.trace F M fF = e.symm (LinearMap.trace K' M f) := by
  classical
  letI : Module F M := Module.compHom M e.toRingHom
  let fF : M →ₗ[F] M :=
    { toFun := fun x ↦ f x
      map_add' := by intro x y; exact f.map_add x y
      map_smul' := by
        intro a x
        change f (e a • x) = e a • f x
        exact f.map_smul (e a) x }
  let bK : Module.Basis (Module.Free.ChooseBasisIndex K' M) K' M :=
    Module.Free.chooseBasis K' M
  let bF : Module.Basis (Module.Free.ChooseBasisIndex K' M) F M :=
    bK.mapCoeffs e.symm (by
      intro c x
      change e (e.symm c) • x = c • x
      simp)
  change (LinearMap.trace F M) fF = e.symm ((LinearMap.trace K' M) f)
  rw [LinearMap.trace_eq_matrix_trace F bF fF, LinearMap.trace_eq_matrix_trace K' bK f]
  change ((LinearMap.toMatrix bF bF) fF).trace =
    e.symm.toAddMonoidHom (((LinearMap.toMatrix bK bK) f).trace)
  rw [AddMonoidHom.map_trace e.symm.toAddMonoidHom]
  have hbF_repr : ∀ (x : M) (i : Module.Free.ChooseBasisIndex K' M),
      bF.repr x i = e.symm (bK.repr x i) := by
    intro x i
    change (Module.compHom.toLinearEquiv e).symm ((bK.repr x) i) =
      e.symm ((bK.repr x) i)
    rw [Module.compHom.toLinearEquiv_symm_apply]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  rw [hbF_repr]
  simp [LinearMap.toMatrix_apply, bF, fF]

private noncomputable def repOverRingEquiv
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    {G : Type u} [Group G] (S : FDRep K' G) :
    letI : Module F S := Module.compHom S e.toRingHom
    Representation F G S := by
  letI : Module F S := Module.compHom S e.toRingHom
  exact
    { toFun := fun g ↦
        { toFun := fun x ↦ S.ρ g x
          map_add' := by intro x y; exact (S.ρ g).map_add x y
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

private theorem transported_irreducible_of_ringEquiv
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    {G : Type u} [Group G] (S : FDRep K' G) [Simple S] :
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
            have hx' : (e.symm c) • x ∈ N.toSubmodule :=
              N.toSubmodule.smul_mem (e.symm c) hx
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

private noncomputable def intertwiningMap_ringEquiv_linearEquiv
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    {G : Type u} [Group G] (S : FDRep K' G) :
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
              map_add' := by intro x y; exact f.map_add x y
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
              map_add' := by intro x y; exact f.map_add x y
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

private theorem simple_selfIntertwining_finrank_eq_one_of_hasEnoughRoots
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep K G) [Simple S] :
    Module.finrank K (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
  classical
  let F := IsLocalRing.ResidueField (PowerSeries K)
  let e : F ≃+* K := PowerSeries.residueFieldOfPowerSeries
  -- `K` is a number field, hence characteristic zero, and the residue field of `K⟦X⟧` is `K`;
  -- so the residue field is characteristic zero and therefore perfect, as the DVR theorem needs.
  haveI : CharZero (IsLocalRing.ResidueField (PowerSeries K)) :=
    (RingHom.charZero_iff e.toRingHom.injective).2 inferInstance
  letI : Module F S := Module.compHom S e.toRingHom
  let ρF : Representation F G S := repOverRingEquiv e S
  haveI : FiniteDimensional F S := by
    let bK : Module.Basis (Module.Free.ChooseBasisIndex K S) K S :=
      Module.Free.chooseBasis K S
    let bF : Module.Basis (Module.Free.ChooseBasisIndex K S) F S :=
      bK.mapCoeffs e.symm (by
        intro c x
        change e (e.symm c) • x = c • x
        simp)
    exact bF.finiteDimensional_of_finite
  let SF : FDRep F G := FDRep.of ρF
  haveI : Representation.IsIrreducible SF.ρ := by
    simpa [SF, ρF] using transported_irreducible_of_ringEquiv e S
  haveI : Simple SF := FDRep.simple_of_isIrreducible SF
  have hroots : HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) :=
    hasEnoughRootsOfUnity_laurentSeries (K := K) (G := G)
  have hHom : Module.finrank F (SF ⟶ SF) = 1 := by
    letI : HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) := hroots
    exact
      Representation.simple_finiteRep_endomorphism_finrank_eq_one_of_sufficiently_large
        (A := PowerSeries K) (K := LaurentSeries K) (G := G) SF
  let eHom : (SF ⟶ SF) ≃ₗ[F] Representation.IntertwiningMap ρF ρF :=
    ((FDRep.forget₂HomLinearEquiv SF SF).symm).trans
      (Rep.homLinearEquiv
        ((forget₂ (FDRep F G) (Rep F G)).obj SF)
        ((forget₂ (FDRep F G) (Rep F G)).obj SF))
  have hIF : Module.finrank F (Representation.IntertwiningMap ρF ρF) = 1 := by
    simpa [hHom] using (LinearEquiv.finrank_eq eHom).symm
  letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
    Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
  have hIKF : Module.finrank F (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
    let E := intertwiningMap_ringEquiv_linearEquiv e S
    simpa [hIF, ρF] using (LinearEquiv.finrank_eq E).symm
  have hfinrank_eq :
      Module.finrank F (Representation.IntertwiningMap S.ρ S.ρ) =
        Module.finrank K (Representation.IntertwiningMap S.ρ S.ρ) := by
    exact finrank_compHom_ringEquiv_eq e (Representation.IntertwiningMap S.ρ S.ρ)
  rw [← hfinrank_eq]
  exact hIKF

end CyclotomicSplitSchur

/-- Helper for Exercise 13-13.1-16: an equivariant equivalence of raw `MulAction` types gives an
isomorphism of the corresponding `Action` objects. -/
lemma action_ofMulAction_isomorphic_of_equivariant_equiv
    {M : Type v} {α β : Type u} [Monoid M] [MulAction M α] [MulAction M β]
    (e : α ≃ β) (he : ∀ (m : M) (a : α), e (m • a) = m • e a) :
    IsIsomorphic (Action.ofMulAction M α) (Action.ofMulAction M β) := by
  refine ⟨Action.mkIso e.toIso ?_⟩
  intro m
  ext a
  exact he m a

/-- Helper for Exercise 13-13.1-16: an isomorphism of bundled finite `G`-sets gives an
isomorphism of the corresponding raw `Type`-valued actions. -/
lemma action_ofMulAction_isomorphic_of_fintypeCat_isomorphic
    {M : Type v} {α β : Type u} [Monoid M] [Fintype α] [Fintype β]
    [MulAction M α] [MulAction M β]
    (h : IsIsomorphic
      (Action.FintypeCat.ofMulAction M (FintypeCat.of α))
      (Action.FintypeCat.ofMulAction M (FintypeCat.of β))) :
    IsIsomorphic (Action.ofMulAction M α) (Action.ofMulAction M β) := by
  classical
  rcases h with ⟨e⟩
  let f : α ≃ β :=
    { toFun := fun a ↦ e.hom.hom a
      invFun := fun b ↦ e.inv.hom b
      left_inv := by
        intro a
        exact ConcreteCategory.congr_hom (Action.hom_inv_hom e) a
      right_inv := by
        intro b
        exact ConcreteCategory.congr_hom (Action.inv_hom_hom e) b }
  refine action_ofMulAction_isomorphic_of_equivariant_equiv f ?_
  intro m a
  simpa [f] using ConcreteCategory.congr_hom (e.hom.comm m) a

lemma irreducible_character_index_eq_of_character_eq
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    {i j : ι} (hchar : (π i).ρ.character = (π j).ρ.character) :
    i = j := by
  have hlin :
      LinearIndependent K (fun i ↦ (π i).ρ.character) :=
    character_linearIndependent_of_complete_pairwise_nonisomorphic_rep
      (G := G) (K := K) π hπ_pairwise hπ_complete
  exact hlin.injective hchar

lemma exists_galois_conjugate_irreducible_index
    {ι : Type u} [Fintype ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (t : Γ_ℚ(G)) (i : ι) :
    ∃ j, ∀ g : G, (π j).ρ.character g = t • (π i).ρ.character g := by
  classical
  let σ : K ≃ₐ[ℚ] K := (galEquivZMod (Monoid.exponent G) K).symm t
  let e : K ≃+* K := σ.symm.toRingEquiv
  let S : FDRep K G := FDRep.of (π i).ρ
  let χi : G → K := (π i).ρ.character
  haveI : FiniteDimensional K S := by infer_instance
  letI : Simple S := hπ_complete.isSimple i
  let πfd : ι → FDRep K G := fun i ↦ FDRep.of (π i).ρ
  have hπ_complete_fd : IsCompleteIrreducibleFamily πfd := by
    simpa [πfd] using hπ_complete
  have hS_fd :
      letI : Module K S := Module.compHom S e.toRingHom
      FiniteDimensional K S :=
    finiteDimensional_compHom_ringEquiv e S
  have hρt_irr_transport :
      letI : Module K S := Module.compHom S e.toRingHom
      Representation.IsIrreducible (repOverRingEquiv e S) :=
    transported_irreducible_of_ringEquiv e S
  have htrace :
      ∀ g : G,
        letI : Module K S := Module.compHom S e.toRingHom
        let ρt : Representation K G S := repOverRingEquiv e S
        ρt.character g = σ (χi g) := by
    intro g
    let fK : S →ₗ[K] S := S.ρ g
    have h :=
      trace_compHom_ringEquiv_eq (e := e) (M := S) (f := fK)
    letI : Module K S := Module.compHom S e.toRingHom
    let ρt : Representation K G S := repOverRingEquiv e S
    simpa [ρt, Representation.character, fK, S, χi, e, σ] using h
  have htrans : ∃ j, ∀ g : G, (π j).ρ.character g = σ (χi g) := by
    letI : Module K S := Module.compHom S e.toRingHom
    let ρt : Representation K G S := repOverRingEquiv e S
    haveI : FiniteDimensional K S := hS_fd
    have hρt_irr : ρt.IsIrreducible := by
      simpa [ρt] using hρt_irr_transport
    rcases IsCompleteIrreducibleFamily.exists_iso_of_representation
        (π := πfd) hπ_complete_fd ρt hρt_irr with ⟨j, ⟨ej⟩⟩
    refine ⟨j, ?_⟩
    intro g
    have hchar_iso :
        ρt.character g = (π j).ρ.character g := by
      simpa [ρt, πfd] using congrFun (FDRep.char_iso ej) g
    calc
      (π j).ρ.character g = ρt.character g := hchar_iso.symm
      _ = σ (χi g) := htrace g
  rcases htrans with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro g
  calc
    (π j).ρ.character g = σ (χi g) := hj g
    _ = t • (π i).ρ.character g := by
          rfl

noncomputable def galoisConjugateIrreducibleIndex
    {ι : Type u} [Fintype ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (t : Γ_ℚ(G)) (i : ι) : ι :=
  Classical.choose
    (exists_galois_conjugate_irreducible_index
      (G := G) (K := K) π hπ_complete t i)

theorem galoisConjugateIrreducibleIndex_spec
    {ι : Type u} [Fintype ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (t : Γ_ℚ(G)) (i : ι) (g : G) :
    (π (galoisConjugateIrreducibleIndex
      (G := G) (K := K) π hπ_complete t i)).ρ.character g =
      t • (π i).ρ.character g :=
  Classical.choose_spec
    (exists_galois_conjugate_irreducible_index
      (G := G) (K := K) π hπ_complete t i) g

@[reducible]
noncomputable def irreducibleCharacterIndexMulActionOfComplete
    {ι : Type u} [Fintype ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    MulAction (Γ_ℚ(G)) ι where
  smul t i :=
    galoisConjugateIrreducibleIndex (G := G) (K := K) π hπ_complete t i
  one_smul := by
    intro i
    apply irreducible_character_index_eq_of_character_eq
      (G := G) (K := K) π hπ_pairwise hπ_complete
    ext g
    change (π (galoisConjugateIrreducibleIndex
      (G := G) (K := K) π hπ_complete (1 : Γ_ℚ(G)) i)).ρ.character g =
        (π i).ρ.character g
    rw [galoisConjugateIrreducibleIndex_spec
      (G := G) (K := K) π hπ_complete (1 : Γ_ℚ(G)) i g]
    simp
  mul_smul := by
    intro t u i
    apply irreducible_character_index_eq_of_character_eq
      (G := G) (K := K) π hπ_pairwise hπ_complete
    ext g
    change (π (galoisConjugateIrreducibleIndex
      (G := G) (K := K) π hπ_complete (t * u) i)).ρ.character g =
        (π (galoisConjugateIrreducibleIndex
          (G := G) (K := K) π hπ_complete t
          (galoisConjugateIrreducibleIndex
            (G := G) (K := K) π hπ_complete u i))).ρ.character g
    rw [galoisConjugateIrreducibleIndex_spec
      (G := G) (K := K) π hπ_complete (t * u) i g]
    rw [galoisConjugateIrreducibleIndex_spec
      (G := G) (K := K) π hπ_complete t
        (galoisConjugateIrreducibleIndex (G := G) (K := K) π hπ_complete u i) g]
    rw [galoisConjugateIrreducibleIndex_spec
      (G := G) (K := K) π hπ_complete u i g]
    simp [mul_smul]

theorem irreducibleCharacterIndexGaloisCompatible_of_complete_pairwise
    {ι : Type u} [Fintype ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    letI : MulAction (Γ_ℚ(G)) ι :=
      irreducibleCharacterIndexMulActionOfComplete
        (G := G) (K := K) π hπ_pairwise hπ_complete
    IrreducibleCharacterIndexGaloisCompatible π := by
  classical
  letI : MulAction (Γ_ℚ(G)) ι :=
    irreducibleCharacterIndexMulActionOfComplete
      (G := G) (K := K) π hπ_pairwise hπ_complete
  intro t i g
  exact galoisConjugateIrreducibleIndex_spec
    (G := G) (K := K) π hπ_complete t i g

section PartA

variable {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
variable (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]

/-- Exercise 13-13.1-16 (1): source part (a). If `ι` indexes the irreducible `K`-characters of
`G` for a cyclotomic realization `K` of `ℚ(m)` with `m = exp(G)`, and the `Γ_ℚ`-action on `ι`
matches Galois conjugation of characters, then the `Γ_ℚ`-sets of irreducible characters and
conjugacy classes are weakly isomorphic in the sense of Exercise `13-13.1-15`. -/
theorem irreducible_character_index_weaklyIsomorphic_conjClasses
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π) :
    let _ : Fintype G := Fintype.ofFinite G
    let _ : Finite ι := by
      exact finite_index_of_complete_pairwise_nonisomorphic_rep
        (π := π) hπ_pairwise hπ_complete
    let _ : Fintype ι := Fintype.ofFinite ι
    Action.WeaklyIsomorphic
      (Action.FintypeCat.ofMulAction (Γ_ℚ(G)) (FintypeCat.of ι))
      (Action.FintypeCat.ofMulAction (Γ_ℚ(G)) (FintypeCat.of (ConjClasses G))) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Finite ι :=
    finite_index_of_complete_pairwise_nonisomorphic_rep
      (G := G) (K := K) (π := π) hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let X : Action FintypeCat (Γ_ℚ(G)) :=
    Action.FintypeCat.ofMulAction (Γ_ℚ(G)) (FintypeCat.of ι)
  let Y : Action FintypeCat (Γ_ℚ(G)) :=
    Action.FintypeCat.ofMulAction (Γ_ℚ(G)) (FintypeCat.of (ConjClasses G))
  change Action.WeaklyIsomorphic X Y
  refine
    (Action.weaklyIsomorphic_iff_card_orbitQuotient_eq_forall_isCyclic
      (X := X) (Y := Y)).2 ?_
  intro H hH
  change
    Nat.card (MulAction.orbitRel.Quotient H ι) =
      Nat.card (MulAction.orbitRel.Quotient H (ConjClasses G))
  simpa [GaloisPowerClass] using
    nat_card_irreducible_orbitQuotient_eq_nat_card_galoisPowerClass
      (G := G) (K := K) (π := π) hπ_pairwise hπ_complete hπ_galois H

end PartA

section FullFieldClassFunctions

lemma gammaSubgroup_top_eq_bot :
    Γ[(⊤ : IntermediateField ℚ K)](G) = ⊥ := by
  unfold Representation.gammaSubgroup
  rw [IntermediateField.fixingSubgroup_top]
  simp

lemma orbitRel_bot_eq
    {M : Type v} {α : Type u} [Group M] [MulAction M α]
    {a b : α} (h : (MulAction.orbitRel (⊥ : Subgroup M) α) a b) :
    a = b := by
  rw [MulAction.orbitRel_apply] at h
  rcases h with ⟨t, ht⟩
  have ht1 : (t : M) = 1 := Subgroup.mem_bot.mp t.2
  change (t : M) • b = a at ht
  have hba : b = a := by
    simpa [ht1] using ht
  exact hba.symm

/-- Helper for Exercise 13-13.1-16: quotienting a group action by the trivial subgroup does not
identify any points. -/
noncomputable def orbitRelBotQuotientEquiv
    {M : Type v} {α : Type u} [Group M] [MulAction M α] :
    MulAction.orbitRel.Quotient (⊥ : Subgroup M) α ≃ α where
  toFun q := Quotient.lift (fun a : α ↦ a)
    (fun _ _ h ↦ orbitRel_bot_eq h) q
  invFun a := Quotient.mk'' a
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    rfl
  right_inv := by
    intro a
    rfl

noncomputable def galoisPowerClassBotEquivConjClasses :
    GaloisPowerClass (G := G) (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) ≃
      ConjClasses G where
  toFun q := Quotient.lift (fun c : ConjClasses G ↦ c)
    (fun _ _ h ↦ orbitRel_bot_eq h) q
  invFun c := Quotient.mk'' c
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro c
    rfl
  right_inv := by
    intro c
    rfl

lemma classFunction_of_mem_characterRingOverFieldAlgebraScalarExtension_self
    {f : G → K} (hf : f ∈ K ⊗R[K](G)) :
    _root_.IsClassFunction f := by
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      exact Representation.isClassFunction_of_mem_characterRingOverField ψ (by simpa using hψ)
  | zero =>
      simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K)))
  | add f g _ _ hf hg =>
      letI : _root_.IsClassFunction f := hf
      letI : _root_.IsClassFunction g := hg
      simpa using (inferInstance : _root_.IsClassFunction (f + g))
  | smul a f _ hf =>
      letI : _root_.IsClassFunction f := hf
      simpa using (inferInstance : _root_.IsClassFunction (a • f))

lemma mem_characterRingOverFieldAlgebraScalarExtension_self_of_isClassFunction
    {f : G → K} (hf : _root_.IsClassFunction f) :
    f ∈ K ⊗R[K](G) := by
  let Ktop : IntermediateField ℚ K := ⊤
  let eTop : Ktop ≃ₐ[ℚ] K := IntermediateField.topEquiv
  let fTop : G → Ktop := fun g ↦ eTop.symm (f g)
  letI : Module Ktop Ktop := Semiring.toModule
  have hfTopClass : _root_.IsClassFunction fTop := by
    refine ⟨?_⟩
    intro s t hst
    simpa [fTop] using congrArg eTop.symm (hf.eq_of_mk_eq hst)
  have hconstTop : IsConstantOnGaloisPowerClasses (Γ[Ktop](G)) fTop := by
    have hGamma : Γ[Ktop](G) = (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
      simpa [Ktop] using gammaSubgroup_top_eq_bot (G := G) (K := K)
    rw [hGamma]
    refine ⟨?_⟩
    intro s t hst
    have hrel :
        (MulAction.orbitRel (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ)
          (ConjClasses G)) (ConjClasses.mk s) (ConjClasses.mk t) :=
      Quotient.exact hst
    exact hfTopClass.eq_of_mk_eq (orbitRel_bot_eq hrel)
  have hmemTop : fTop ∈ Ktop ⊗R[Ktop](G) := by
    exact
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := K) (K := Ktop)).2 hconstTop
  let STop : Set (G → Ktop) :=
    (((R[Ktop](G)).toSubmodule : Submodule ℤ (G → Ktop)) : Set (G → Ktop))
  let SK : Set (G → K) :=
    (((R[K](G)).toSubmodule : Submodule ℤ (G → K)) : Set (G → K))
  have hmemTop' : fTop ∈ Submodule.span Ktop STop := by
    simpa [STop, characterRingOverFieldAlgebraScalarExtension] using hmemTop
  change f ∈ (Submodule.span K SK : Submodule K (G → K))
  let p : ∀ x : G → Ktop, x ∈ Submodule.span Ktop STop → Prop :=
    fun x _ ↦ (fun g ↦ eTop (x g)) ∈ Submodule.span K SK
  have hp : p fTop hmemTop' := by
    refine Submodule.span_induction (s := STop) (p := p) ?_ ?_ ?_ ?_ hmemTop'
    · intro ψ hψ
      dsimp [p]
      change (fun g ↦ eTop (ψ g)) ∈ Submodule.span K SK
      exact Submodule.subset_span (by
        change (fun g ↦ algebraMap Ktop K (ψ g)) ∈ SK
        exact map_mem_characterRingOverField_of_mem_intermediateField_characterRing
          (G := G) (K := K) Ktop (by simpa [STop] using hψ))
    · dsimp [p]
      change (0 : G → K) ∈ Submodule.span K SK
      exact Submodule.zero_mem _
    · intro x y _ _ hxmem hymem
      dsimp [p] at hxmem hymem ⊢
      convert (Submodule.add_mem _ hxmem hymem) using 1
    · intro a x _ hxmem
      dsimp [p] at hxmem ⊢
      convert (Submodule.smul_mem _ (eTop a) hxmem) using 1
  dsimp [p] at hp
  convert hp using 1

noncomputable def characterRingOverFieldAlgebraScalarExtensionSubalgebra_self_algEquiv_conjClasses :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ≃ₐ[K]
      (ConjClasses G → K) := by
  let B := characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G
  let eLin : B ≃ₗ[K] (ConjClasses G → K) :=
    { toFun := fun φ ↦
        (classFunction_of_mem_characterRingOverFieldAlgebraScalarExtension_self
          (G := G) (K := K) (f := (φ : G → K)) (by simpa [B] using φ.2)).lift
      invFun := fun F ↦
        ⟨F ∘ ConjClasses.mk,
          (by
            change F ∘ ConjClasses.mk ∈ K ⊗R[K](G)
            exact mem_characterRingOverFieldAlgebraScalarExtension_self_of_isClassFunction
              (G := G) (K := K) (f := F ∘ ConjClasses.mk) inferInstance :
            F ∘ ConjClasses.mk ∈ B)⟩
      left_inv := by
        intro φ
        ext g
        simp [B]
      right_inv := by
        intro F
        ext c
        obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
        simp [B]
      map_add' := by
        intro φ ψ
        ext c
        obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
        rfl
      map_smul' := by
        intro a φ
        ext c
        obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
        rfl }
  refine AlgEquiv.ofLinearEquiv eLin ?_ ?_
  · ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    rfl
  · intro φ ψ
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    rfl

@[simp] theorem
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_self_algEquiv_conjClasses_apply_mk
    (φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) (g : G) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_self_algEquiv_conjClasses
      (G := G) (K := K) φ (ConjClasses.mk g) =
      (φ : G → K) g := by
  rfl

end FullFieldClassFunctions

section RationalCenterBaseChange

/-- Helper for Exercise 13-13.1-16: coefficientwise scalar extension of a rational central
group-algebra element has class-function coefficients over the cyclotomic field. -/
lemma centerRatToCyclotomicCenter_mem_classFunctionSubmodule
    (u : Subalgebra.center ℚ (ℚ[G])) :
    (fun g ↦ algebraMap ℚ K ((u : ℚ[G]) g)) ∈ _root_.classFunctionSubmodule K G := by
  let hclass : _root_.IsClassFunction fun g ↦ (u : ℚ[G]) g :=
    Representation.coeff_isClassFunction_of_mem_center u
  exact (_root_.mem_classFunctionSubmodule_iff K _).2 (hclass.comp (algebraMap ℚ K))

/-- Helper for Exercise 13-13.1-16: coefficientwise scalar extension sends the rational center of
`ℚ[G]` into the cyclotomic center of `K[G]`. -/
lemma centerRatToCyclotomicCenter_mem_center
    (u : Subalgebra.center ℚ (ℚ[G])) :
    MonoidAlgebra.mapAlgHom G (Algebra.ofId ℚ K) (u : ℚ[G]) ∈
      Subalgebra.center K (K[G]) := by
  let f : _root_.classFunctionSubmodule K G :=
    ⟨fun g ↦ algebraMap ℚ K ((u : ℚ[G]) g),
      centerRatToCyclotomicCenter_mem_classFunctionSubmodule (G := G) (K := K) u⟩
  have hmap :
      MonoidAlgebra.mapAlgHom G (Algebra.ofId ℚ K) (u : ℚ[G]) =
        Finsupp.equivFunOnFinite.symm (f : G → K) := by
    ext g
    simp [f]
  rw [hmap]
  exact mem_center_of_classFunction K f

/-- Helper for Exercise 13-13.1-16: coefficientwise scalar extension from the rational center to
the cyclotomic center. -/
noncomputable def centerRatToCyclotomicCenter :
    Subalgebra.center ℚ (ℚ[G]) →ₐ[ℚ] Subalgebra.center K (K[G]) :=
  AlgHom.codRestrict
    ((MonoidAlgebra.mapAlgHom G (Algebra.ofId ℚ K)).comp
      (Subalgebra.center ℚ (ℚ[G])).val)
    ((Subalgebra.center K (K[G])).restrictScalars ℚ)
    (centerRatToCyclotomicCenter_mem_center (G := G) (K := K))

/-- Helper for Exercise 13-13.1-16: coefficientwise scalar extension preserves coefficients. -/
@[simp] lemma centerRatToCyclotomicCenter_apply
    (u : Subalgebra.center ℚ (ℚ[G])) (g : G) :
    (centerRatToCyclotomicCenter (G := G) (K := K) u : K[G]) g =
      algebraMap ℚ K ((u : ℚ[G]) g) := by
  change ((MonoidAlgebra.mapAlgHom G (Algebra.ofId ℚ K)) (u : ℚ[G])) g =
    algebraMap ℚ K ((u : ℚ[G]) g)
  simp

/-- Helper for Exercise 13-13.1-16: after coefficientwise scalar extension, a rational class sum
is the corresponding cyclotomic class sum. -/
@[simp] lemma centerRatToCyclotomicCenter_conjugacyClassSumInCenter
    (c : ConjClasses G) :
    centerRatToCyclotomicCenter (G := G) (K := K) (conjugacyClassSumInCenter ℚ c) =
      conjugacyClassSumInCenter K c := by
  ext g
  by_cases hg : g ∈ c.carrier
  · simp [conjugacyClassSum_apply, ConjClasses.indicator, hg]
  · simp [conjugacyClassSum_apply, ConjClasses.indicator, hg]

/-- Helper for Exercise 13-13.1-16: base-changing the rational center to `K` maps to the
cyclotomic center. -/
noncomputable def centerBaseChangeToCyclotomicCenter :
    TensorProduct ℚ K (Subalgebra.center ℚ (ℚ[G])) →ₐ[K]
      Subalgebra.center K (K[G]) :=
  (AlgHom.liftEquiv ℚ K (Subalgebra.center ℚ (ℚ[G]))
      (Subalgebra.center K (K[G])))
    (centerRatToCyclotomicCenter (G := G) (K := K))

/-- Helper for Exercise 13-13.1-16: the center base-change map on pure tensors reads
coefficients coefficientwise. -/
@[simp] theorem centerBaseChangeToCyclotomicCenter_one_tmul_apply
    (u : Subalgebra.center ℚ (ℚ[G])) (g : G) :
    ((centerBaseChangeToCyclotomicCenter (G := G) (K := K)
      (1 ⊗ₜ[ℚ] u) : K[G]) g) = algebraMap ℚ K ((u : ℚ[G]) g) := by
  have hmap :
      centerBaseChangeToCyclotomicCenter (G := G) (K := K) (1 ⊗ₜ[ℚ] u) =
        centerRatToCyclotomicCenter (G := G) (K := K) u := by
    symm
    simpa [centerBaseChangeToCyclotomicCenter] using
      (AlgHom.liftEquiv_symm_apply
        (centerBaseChangeToCyclotomicCenter (G := G) (K := K)) u)
  rw [hmap]
  simp

/-- Helper for Exercise 13-13.1-16: the center base-change map sends the tensor class-sum basis
to the cyclotomic class-sum basis. -/
@[simp] theorem centerBaseChangeToCyclotomicCenter_basis_apply
    (c : ConjClasses G) :
    centerBaseChangeToCyclotomicCenter (G := G) (K := K)
        ((Algebra.TensorProduct.basis K
          (conjugacyClassSumBasis (G := G) (k := ℚ))) c) =
      conjugacyClassSumBasis (G := G) (k := K) c := by
  ext g
  by_cases hg : g ∈ c.carrier
  · simp [conjugacyClassSumBasis_apply, conjugacyClassSum_apply,
      ConjClasses.indicator, hg]
  · simp [conjugacyClassSumBasis_apply, conjugacyClassSum_apply,
      ConjClasses.indicator, hg]

/-- Helper for Exercise 13-13.1-16: the rational center becomes the full cyclotomic center after
base change to `K`. -/
theorem centerBaseChangeToCyclotomicCenter_injective :
    Function.Injective (centerBaseChangeToCyclotomicCenter (G := G) (K := K)) := by
  classical
  let bQ := conjugacyClassSumBasis (G := G) (k := ℚ)
  let bK := conjugacyClassSumBasis (G := G) (k := K)
  let bt := Algebra.TensorProduct.basis K bQ
  let φ := centerBaseChangeToCyclotomicCenter (G := G) (K := K)
  intro x y hxy
  let δ := x - y
  have hδφ : φ δ = 0 := by
    change φ (x - y) = 0
    rw [map_sub, hxy, sub_self]
  let c : ConjClasses G → K := bt.repr δ
  have hδ_expand :
      ∑ q, c q • bK q = φ δ := by
    calc
      ∑ q, c q • bK q =
          ∑ q, c q • φ (bt q) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            rw [centerBaseChangeToCyclotomicCenter_basis_apply (G := G) (K := K) q]
      _ = φ (∑ q, c q • bt q) := by
            simp [map_sum, map_smul]
      _ = φ δ := by
            have hsum : (∑ q, c q • bt q) = δ := by
              simpa [c] using (bt.sum_repr δ)
            rw [hsum]
  have hsum_zero : ∑ q, c q • bK q = 0 := by
    rw [hδ_expand, hδφ]
  have hc_finsupp :
      Finsupp.equivFunOnFinite.symm c = (0 : ConjClasses G →₀ K) := by
    have hlincomb :
        Finsupp.linearCombination K bK (Finsupp.equivFunOnFinite.symm c) = 0 := by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype] using hsum_zero
    simpa using congrArg bK.repr hlincomb
  have hc_zero : c = 0 := by
    funext q
    have hq := congrArg (fun f : ConjClasses G →₀ K ↦ f q) hc_finsupp
    simpa using hq
  have hrepr : bt.repr δ = 0 := by
    ext q
    simpa [c] using congrFun hc_zero q
  have hδ : δ = 0 := bt.repr.injective hrepr
  exact sub_eq_zero.mp (by simpa [δ] using hδ)

/-- Helper for Exercise 13-13.1-16: every cyclotomic central element descends from the
base-changed rational center. -/
theorem centerBaseChangeToCyclotomicCenter_surjective :
    Function.Surjective (centerBaseChangeToCyclotomicCenter (G := G) (K := K)) := by
  classical
  let bQ := conjugacyClassSumBasis (G := G) (k := ℚ)
  let bK := conjugacyClassSumBasis (G := G) (k := K)
  let bt := Algebra.TensorProduct.basis K bQ
  let φ := centerBaseChangeToCyclotomicCenter (G := G) (K := K)
  intro z
  let c : ConjClasses G → K := bK.repr z
  refine ⟨∑ q, c q • bt q, ?_⟩
  calc
    φ (∑ q, c q • bt q) = ∑ q, c q • φ (bt q) := by
      simp [map_sum, map_smul]
    _ = ∑ q, c q • bK q := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rw [centerBaseChangeToCyclotomicCenter_basis_apply (G := G) (K := K) q]
    _ = z := by
      simpa [c] using (bK.sum_repr z)

/-- Helper for Exercise 13-13.1-16: base change identifies the rational center with the
cyclotomic center as a `K`-algebra. -/
noncomputable def centerBaseChangeAlgEquivCyclotomicCenter :
    TensorProduct ℚ K (Subalgebra.center ℚ (ℚ[G])) ≃ₐ[K]
      Subalgebra.center K (K[G]) :=
  AlgEquiv.ofBijective (centerBaseChangeToCyclotomicCenter (G := G) (K := K))
    ⟨centerBaseChangeToCyclotomicCenter_injective (G := G) (K := K),
      centerBaseChangeToCyclotomicCenter_surjective (G := G) (K := K)⟩

end RationalCenterBaseChange

section RationalCharacterRingBaseChange

noncomputable def tensorCharacterRingOverFieldToRationalSubalgebra :
    TensorProduct ℤ ℚ (R[K](G)) →ₐ[ℚ]
      characterRingOverFieldScalarExtensionSubalgebra K G :=
  (AlgHom.liftEquiv ℤ ℚ (R[K](G))
      (characterRingOverFieldScalarExtensionSubalgebra K G))
    { toFun := fun χ ↦
        ⟨(χ : G → K),
          mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
            (K := K) (G := G) χ.property⟩
      map_one' := by
        ext g
        rfl
      map_mul' := by
        intro χ ψ
        ext g
        rfl
      map_zero' := by
        ext g
        rfl
      map_add' := by
        intro χ ψ
        ext g
        rfl
      commutes' := by
        intro a
        ext g
        simp }

theorem tensorCharacterRingOverFieldToRationalSubalgebra_surjective :
    Function.Surjective (tensorCharacterRingOverFieldToRationalSubalgebra (G := G) (K := K)) := by
  intro f
  rcases (R[K](G)).toSubmodule.surjective_tensorToSpan ℚ ⟨(f : G → K), f.2⟩ with
    ⟨χ, hχ⟩
  refine ⟨χ, ?_⟩
  ext g
  have h :=
    congrArg
      (fun z : Representation.characterRingOverFieldScalarExtension K G ↦ (z : G → K) g) hχ
  simpa [tensorCharacterRingOverFieldToRationalSubalgebra] using h

theorem tensorCharacterRingOverFieldToRationalSubalgebra_injective
    {ι : Type u} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Function.Injective (tensorCharacterRingOverFieldToRationalSubalgebra (G := G) (K := K)) := by
  classical
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let bt := Algebra.TensorProduct.basis ℚ b
  let φ := tensorCharacterRingOverFieldToRationalSubalgebra (G := G) (K := K)
  let πRep : ι → Rep K G := fun i ↦ Rep.of (π i).ρ
  have hπRep_pairwise : PairwiseNonisomorphic πRep := by
    intro i j hij hIso
    apply hπ_pairwise hij
    rcases hIso with ⟨e⟩
    exact ⟨by simpa [πRep] using (Representation.equivOfIso e).toFDRepIso⟩
  have hπRep_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (πRep i).ρ) := by
    simpa [πRep] using hπ_complete
  have hlin_charK : LinearIndependent K (fun i ↦ (π i).character) := by
    simpa [πRep] using
      character_linearIndependent_of_complete_pairwise_nonisomorphic_rep
        (G := G) (K := K) (π := πRep) hπRep_pairwise hπRep_complete
  have hlin_char : LinearIndependent ℚ (fun i ↦ (π i).character) :=
    hlin_charK.restrict_scalars' ℚ
  intro x y hxy
  let δ := x - y
  have hδφ : φ δ = 0 := by
    change φ (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hzero_fun :
      ((φ δ : characterRingOverFieldScalarExtensionSubalgebra K G) : G → K) = 0 := by
    exact
      congrArg (fun z : characterRingOverFieldScalarExtensionSubalgebra K G ↦ (z : G → K)) hδφ
  let c : ι → ℚ := bt.repr δ
  have hbt_apply (i : ι) :
      ((φ (bt i) : characterRingOverFieldScalarExtensionSubalgebra K G) : G → K) =
        (π i).character := by
    ext g
    simp [φ, tensorCharacterRingOverFieldToRationalSubalgebra, bt, b,
      irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply]
  have hδ_expand :
      ∑ i, c i • (π i).character =
        ((φ δ : characterRingOverFieldScalarExtensionSubalgebra K G) : G → K) := by
    calc
      ∑ i, c i • (π i).character =
          ∑ i, c i •
            ((φ (bt i) : characterRingOverFieldScalarExtensionSubalgebra K G) : G → K) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hbt_apply i]
      _ = ((φ (∑ i, c i • bt i) :
            characterRingOverFieldScalarExtensionSubalgebra K G) : G → K) := by
            simp [map_sum, map_smul]
      _ = ((φ δ : characterRingOverFieldScalarExtensionSubalgebra K G) : G → K) := by
            have hsum : (∑ i, c i • bt i) = δ := by
              simpa [c] using (bt.sum_repr δ)
            rw [hsum]
  have hc_zero : c = 0 := by
    ext i
    exact (linearIndependent_iff'.mp hlin_char)
      Finset.univ c (by simpa [hzero_fun] using hδ_expand) i (Finset.mem_univ i)
  have hrepr : bt.repr δ = 0 := by
    ext i
    simpa [c] using congrFun hc_zero i
  have hδ : δ = 0 := bt.repr.injective hrepr
  exact sub_eq_zero.mp (by simpa [δ] using hδ)

noncomputable def tensorCharacterRingOverFieldAlgEquivRationalSubalgebra
    {ι : Type u} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    TensorProduct ℤ ℚ (R[K](G)) ≃ₐ[ℚ]
      characterRingOverFieldScalarExtensionSubalgebra K G :=
  AlgEquiv.ofBijective (tensorCharacterRingOverFieldToRationalSubalgebra (G := G) (K := K))
    ⟨tensorCharacterRingOverFieldToRationalSubalgebra_injective
        (G := G) (K := K) π hπ_pairwise hπ_complete,
      tensorCharacterRingOverFieldToRationalSubalgebra_surjective (G := G) (K := K)⟩

lemma mem_characterRingOverFieldAlgebraScalarExtension_self_of_mem_scalarExtension
    {f : G → K} (hf : f ∈ ℚ⊗R[K](G)) :
    f ∈ K ⊗R[K](G) := by
  change f ∈ Submodule.span K (((R[K](G)).toSubmodule : Submodule ℤ (G → K)) : Set (G → K))
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      exact Submodule.subset_span hψ
  | zero =>
      exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
      exact Submodule.add_mem _ hf hg
  | smul q f _ hf =>
      convert Submodule.smul_mem _ (algebraMap ℚ K q) hf using 1
      ext x
      simp [Algebra.smul_def]

noncomputable def rationalCharacterRingInclusionSelf :
    characterRingOverFieldScalarExtensionSubalgebra K G →ₐ[ℚ]
      characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G where
  toFun a := ⟨(a : G → K),
    mem_characterRingOverFieldAlgebraScalarExtension_self_of_mem_scalarExtension
      (G := G) (K := K) a.2⟩
  map_one' := by
    ext g
    rfl
  map_mul' := by
    intro a b
    ext g
    rfl
  map_zero' := by
    ext g
    rfl
  map_add' := by
    intro a b
    ext g
    rfl
  commutes' := by
    intro q
    ext g
    rfl

noncomputable def rationalCharacterRingBaseChangeToSelfSubalgebra :
    TensorProduct ℚ K (characterRingOverFieldScalarExtensionSubalgebra K G) →ₐ[K]
      characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G :=
  (AlgHom.liftEquiv ℚ K (characterRingOverFieldScalarExtensionSubalgebra K G)
    (characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G))
      (rationalCharacterRingInclusionSelf (G := G) (K := K))

@[simp] theorem rationalCharacterRingBaseChangeToSelfSubalgebra_one_tmul_apply
    (a : characterRingOverFieldScalarExtensionSubalgebra K G) (g0 : G) :
    ((rationalCharacterRingBaseChangeToSelfSubalgebra (G := G) (K := K)
      (1 ⊗ₜ[ℚ] a) : G → K) g0) = (a : G → K) g0 := by
  simp [rationalCharacterRingBaseChangeToSelfSubalgebra, rationalCharacterRingInclusionSelf]

theorem rationalCharacterRingBaseChangeToSelfSubalgebra_injective
    {ι : Type u} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Function.Injective (rationalCharacterRingBaseChangeToSelfSubalgebra (G := G) (K := K)) := by
  classical
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let btRat := Algebra.TensorProduct.basis ℚ b
  let eRat :=
    tensorCharacterRingOverFieldAlgEquivRationalSubalgebra
      (G := G) (K := K) π hπ_pairwise hπ_complete
  let bA : Module.Basis ι ℚ (characterRingOverFieldScalarExtensionSubalgebra K G) :=
    btRat.map eRat.toLinearEquiv
  let bt := Algebra.TensorProduct.basis K bA
  let φ := rationalCharacterRingBaseChangeToSelfSubalgebra (G := G) (K := K)
  let πRep : ι → Rep K G := fun i ↦ Rep.of (π i).ρ
  have hπRep_pairwise : PairwiseNonisomorphic πRep := by
    intro i j hij hIso
    apply hπ_pairwise hij
    rcases hIso with ⟨e⟩
    exact ⟨by simpa [πRep] using (Representation.equivOfIso e).toFDRepIso⟩
  have hπRep_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (πRep i).ρ) := by
    simpa [πRep] using hπ_complete
  have hlin_char : LinearIndependent K (fun i ↦ (π i).character) := by
    simpa [πRep] using
      character_linearIndependent_of_complete_pairwise_nonisomorphic_rep
        (G := G) (K := K) (π := πRep) hπRep_pairwise hπRep_complete
  intro x y hxy
  let δ := x - y
  have hδφ : φ δ = 0 := by
    change φ (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hzero_fun :
      ((φ δ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) = 0 := by
    exact
      congrArg
        (fun z : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ↦ (z : G → K))
        hδφ
  let c : ι → K := bt.repr δ
  have hbA_apply (i : ι) :
      ((bA i : characterRingOverFieldScalarExtensionSubalgebra K G) : G → K) =
        (π i).character := by
    ext g
    simp [bA, eRat, tensorCharacterRingOverFieldAlgEquivRationalSubalgebra,
      tensorCharacterRingOverFieldToRationalSubalgebra, btRat, b,
      irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply]
  have hbt_apply (i : ι) :
      ((φ (bt i) : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) =
        (π i).character := by
    ext g
    simp [bt, φ, rationalCharacterRingBaseChangeToSelfSubalgebra,
      rationalCharacterRingInclusionSelf, hbA_apply i]
  have hδ_expand :
      ∑ i, c i • (π i).character =
        ((φ δ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) := by
    calc
      ∑ i, c i • (π i).character =
          ∑ i, c i •
            ((φ (bt i) :
              characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hbt_apply i]
      _ = ((φ (∑ i, c i • bt i) :
            characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) := by
            simp [map_sum, map_smul]
      _ = ((φ δ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) := by
            have hsum : (∑ i, c i • bt i) = δ := by
              simpa [c] using (bt.sum_repr δ)
            rw [hsum]
  have hc_zero : c = 0 := by
    ext i
    exact (linearIndependent_iff'.mp hlin_char)
      Finset.univ c (by simpa [hzero_fun] using hδ_expand) i (Finset.mem_univ i)
  have hrepr : bt.repr δ = 0 := by
    ext i
    simpa [c] using congrFun hc_zero i
  have hδ : δ = 0 := bt.repr.injective hrepr
  exact sub_eq_zero.mp (by simpa [δ] using hδ)

theorem rationalCharacterRingBaseChangeToSelfSubalgebra_surjective :
    Function.Surjective (rationalCharacterRingBaseChangeToSelfSubalgebra (G := G) (K := K)) := by
  intro f
  let S : Set (G → K) := (((R[K](G)).toSubmodule : Submodule ℤ (G → K)) : Set (G → K))
  have hfmem : (f : G → K) ∈ Submodule.span K S := by
    simpa [S, characterRingOverFieldAlgebraScalarExtension] using f.2
  let p : ∀ x : G → K, x ∈ Submodule.span K S → Prop :=
    fun x _ ↦ ∃ y, rationalCharacterRingBaseChangeToSelfSubalgebra (G := G) (K := K) y =
      (⟨x, by simpa [S, characterRingOverFieldAlgebraScalarExtension]⟩ :
        characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G)
  have hp : p (f : G → K) hfmem := by
    refine Submodule.span_induction (s := S) (p := p) ?_ ?_ ?_ ?_ hfmem
    · intro ψ hψ
      let a : characterRingOverFieldScalarExtensionSubalgebra K G :=
        ⟨ψ, mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
          (K := K) (G := G) (by simpa [S] using hψ)⟩
      refine ⟨1 ⊗ₜ[ℚ] a, ?_⟩
      ext g
      simp [rationalCharacterRingBaseChangeToSelfSubalgebra,
        rationalCharacterRingInclusionSelf, a]
    · refine ⟨0, ?_⟩
      ext g
      simp
    · intro x y hx hy hxmem hymem
      rcases hxmem with ⟨x', hx'⟩
      rcases hymem with ⟨y', hy'⟩
      refine ⟨x' + y', ?_⟩
      rw [map_add, hx', hy']
      ext g
      rfl
    · intro a x hx hxmem
      rcases hxmem with ⟨x', hx'⟩
      refine ⟨a • x', ?_⟩
      rw [map_smul, hx']
      ext g
      rfl
  rcases hp with ⟨y, hy⟩
  exact ⟨y, by simpa using hy⟩

noncomputable def rationalCharacterRingBaseChangeAlgEquivSelfSubalgebra
    {ι : Type u} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    TensorProduct ℚ K (characterRingOverFieldScalarExtensionSubalgebra K G) ≃ₐ[K]
      characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G :=
  AlgEquiv.ofBijective (rationalCharacterRingBaseChangeToSelfSubalgebra (G := G) (K := K))
    ⟨rationalCharacterRingBaseChangeToSelfSubalgebra_injective
        (G := G) (K := K) π hπ_pairwise hπ_complete,
      rationalCharacterRingBaseChangeToSelfSubalgebra_surjective (G := G) (K := K)⟩

theorem characterRingOverFieldScalarExtension_gammaRat_power_compatible
    {χ : G → K} (hχ : χ ∈ ℚ⊗R[K](G)) :
    ∀ (s : G) (t : Γ_ℚ(G)), t • χ s = χ (s ^ t) := by
  induction hχ using Submodule.span_induction with
  | mem ψ hψ =>
      exact
        characterRingOverField_gammaRat_power_compatible
          (G := G) (K := K) (χ := ψ) (by simpa using hψ)
  | zero =>
      intro s t
      simp
  | add f g _ _ hf hg =>
      intro s t
      change t • (f s + g s) = f (s ^ t) + g (s ^ t)
      simp [map_add, hf s t, hg s t]
  | smul q f _ hf =>
      intro s t
      have hq :
          ((galEquivZMod (Monoid.exponent G) K).symm t) (algebraMap ℚ K q) =
            algebraMap ℚ K q := by
        exact ((galEquivZMod (Monoid.exponent G) K).symm t).commutes q
      simp only [Pi.smul_apply, Algebra.smul_def]
      change
        ((galEquivZMod (Monoid.exponent G) K).symm t)
            (algebraMap ℚ K q * f s) =
          algebraMap ℚ K q * f (s ^ t)
      have hf' :
          ((galEquivZMod (Monoid.exponent G) K).symm t) (f s) = f (s ^ t) := by
        simpa using hf s t
      rw [map_mul, hq, hf']

noncomputable def rationalCharacterRingAlgHomPointEquiv
    {κ : Type u} [Fintype κ]
    (π : κ → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    ConjClasses G ≃ (characterRingOverFieldScalarExtensionSubalgebra K G →ₐ[ℚ] K) := by
  let A := characterRingOverFieldScalarExtensionSubalgebra K G
  let eBase : TensorProduct ℚ K A ≃ₐ[K]
      characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G :=
    rationalCharacterRingBaseChangeAlgEquivSelfSubalgebra
      (G := G) (K := K) π hπ_pairwise hπ_complete
  let eClass :
      characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ≃ₐ[K]
        (ConjClasses G → K) :=
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_self_algEquiv_conjClasses
      (G := G) (K := K)
  let eFun : TensorProduct ℚ K A ≃ₐ[K] (ConjClasses G → K) := eBase.trans eClass
  let liftE := AlgHom.liftEquiv ℚ K A K
  let points := finite_function_algHom_points_equiv (α := ConjClasses G) (k := K)
  exact
    { toFun := fun c ↦ liftE.symm ((points c).comp eFun.toAlgHom)
      invFun := fun φ ↦ points.symm ((liftE φ).comp eFun.symm.toAlgHom)
      left_inv := by
        intro c
        apply points.injective
        ext F
        simp [liftE, points, eFun]
      right_inv := by
        intro φ
        apply liftE.injective
        ext x
        simp [liftE, points, eFun] }

@[simp] theorem rationalCharacterRingAlgHomPointEquiv_apply_mk
    {κ : Type u} [Fintype κ]
    (π : κ → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (g : G) (a : characterRingOverFieldScalarExtensionSubalgebra K G) :
    rationalCharacterRingAlgHomPointEquiv
      (G := G) (K := K) π hπ_pairwise hπ_complete (ConjClasses.mk g) a =
      (a : G → K) g := by
  simp [rationalCharacterRingAlgHomPointEquiv, rationalCharacterRingBaseChangeAlgEquivSelfSubalgebra,
    rationalCharacterRingBaseChangeToSelfSubalgebra, rationalCharacterRingInclusionSelf]

end RationalCharacterRingBaseChange

/-- Helper for Exercise 13-13.1-16: the underlying equivalence of types attached to an isomorphism
of bundled actions. -/
noncomputable def equivOfActionIso
    {M : Type v} [Monoid M] {α β : Type u} [MulAction M α] [MulAction M β]
    (e : Action.ofMulAction M α ≅ Action.ofMulAction M β) : α ≃ β where
  toFun := fun a ↦ e.hom.hom a
  invFun := fun b ↦ e.inv.hom b
  left_inv := by
    intro a
    exact ConcreteCategory.congr_hom (Action.hom_inv_hom e) a
  right_inv := by
    intro b
    exact ConcreteCategory.congr_hom (Action.inv_hom_hom e) b

/-- Helper for Exercise 13-13.1-16: the underlying equivalence of an action isomorphism is
equivariant. -/
theorem equivOfActionIso_smul
    {M : Type v} [Monoid M] {α β : Type u} [MulAction M α] [MulAction M β]
    (e : Action.ofMulAction M α ≅ Action.ofMulAction M β) (m : M) (a : α) :
    equivOfActionIso e (m • a) = m • equivOfActionIso e a := by
  exact ConcreteCategory.congr_hom (e.hom.comm m) a

/-- Helper for Exercise 13-13.1-16: Galois acts on a scalar extension tensor product through the
cyclotomic scalar factor. -/
noncomputable def tensorGaloisAlgHom
    {C : Type u} [CommRing C] [Algebra ℚ C] (σ : Gal(K / ℚ)) :
    K ⊗[ℚ] C →ₐ[ℚ] K ⊗[ℚ] C :=
  Algebra.TensorProduct.map (R := ℚ) (S := ℚ) σ.toAlgHom (AlgHom.id ℚ C)

/-- Helper for Exercise 13-13.1-16: the tensor Galois action on pure tensors. -/
@[simp] theorem tensorGaloisAlgHom_tmul
    {C : Type u} [CommRing C] [Algebra ℚ C]
    (σ : Gal(K / ℚ)) (a : K) (c : C) :
    tensorGaloisAlgHom (K := K) (C := C) σ (a ⊗ₜ[ℚ] c) = σ a ⊗ₜ[ℚ] c := by
  simp [tensorGaloisAlgHom]

/-- Helper for Exercise 13-13.1-16: elements coming from the rational factor are fixed by the
tensor Galois action. -/
@[simp] theorem tensorGaloisAlgHom_includeRight
    {C : Type u} [CommRing C] [Algebra ℚ C]
    (σ : Gal(K / ℚ)) (c : C) :
    tensorGaloisAlgHom (K := K) (C := C) σ
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) c) =
      Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) c := by
  simp [Algebra.TensorProduct.includeRight_apply]

/-- Helper for Exercise 13-13.1-16: coordinates of the tensor Galois action in a finite
`ℚ`-basis. -/
theorem repr_tensorGaloisAlgHom_apply
    {C : Type u} [CommRing C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    (σ : Gal(K / ℚ)) (x : K ⊗[ℚ] C) (i : Fin (Module.finrank ℚ C)) :
    ((Algebra.TensorProduct.basis K (Module.finBasis ℚ C)).repr
      (tensorGaloisAlgHom (K := K) (C := C) σ x)) i =
      σ (((Algebra.TensorProduct.basis K (Module.finBasis ℚ C)).repr x) i) := by
  let b := Module.finBasis ℚ C
  let bt := Algebra.TensorProduct.basis K b
  change (bt.repr (tensorGaloisAlgHom (K := K) (C := C) σ x)) i = σ ((bt.repr x) i)
  refine TensorProduct.induction_on x ?hz ?ht ?ha
  · simp [tensorGaloisAlgHom]
  · intro a m
    simp [tensorGaloisAlgHom, bt, b, Algebra.TensorProduct.basis_repr_tmul, map_mul]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Exercise 13-13.1-16: a tensor fixed by every Galois automorphism descends to the
right tensor factor. -/
theorem tensor_fixed_exists_includeRight
    {C : Type u} [CommRing C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (x : K ⊗[ℚ] C)
    (hfix : ∀ σ : Gal(K / ℚ), tensorGaloisAlgHom (K := K) (C := C) σ x = x) :
    ∃ c : C, Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) c = x := by
  classical
  let b := Module.finBasis ℚ C
  let bt := Algebra.TensorProduct.basis K b
  let coeff : Fin (Module.finrank ℚ C) → K := fun i ↦ bt.repr x i
  have hcoeff_fixed : ∀ i, ∀ σ : Gal(K / ℚ), σ (coeff i) = coeff i := by
    intro i σ
    have h := congrArg (fun y : K ⊗[ℚ] C ↦ bt.repr y i) (hfix σ)
    have h2 := repr_tensorGaloisAlgHom_apply (K := K) (C := C) σ x i
    change σ (bt.repr x i) = bt.repr x i
    exact h2.symm.trans h
  have hcoeff_range : ∀ i, coeff i ∈ Set.range (algebraMap ℚ K) := by
    intro i
    exact (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (E := K) (coeff i)).2
      (hcoeff_fixed i)
  choose q hq using hcoeff_range
  refine ⟨∑ i, q i • b i, ?_⟩
  calc
    Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) (∑ i, q i • b i)
        = ∑ i, Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C)
            (q i • b i) := by
            simp [map_sum]
    _ = ∑ i, (algebraMap ℚ K (q i)) • bt i := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C)
                  (q i • b i)
                  = (1 : K) ⊗ₜ[ℚ] (q i • b i) := by
                      rw [Algebra.TensorProduct.includeRight_apply]
              _ = (q i • (1 : K)) ⊗ₜ[ℚ] b i := by
                      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
              _ = (algebraMap ℚ K (q i)) • bt i := by
                      simp [bt, b, Algebra.TensorProduct.basis_apply, Algebra.smul_def]
    _ = ∑ i, coeff i • bt i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hq i]
    _ = x := by
            simpa [coeff, bt] using (bt.sum_repr x)

/-- Helper for Exercise 13-13.1-16: existence of the descended value of an equivariant
base-changed algebra map. -/
theorem descendedElement_exists_of_equivariantBaseChange
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ B] [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (e : K ⊗[ℚ] A ≃ₐ[K] K ⊗[ℚ] B)
    (he : ∀ σ : Gal(K / ℚ), ∀ x : K ⊗[ℚ] A,
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x))
    (a : A) :
    ∃ b : B, Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B) b =
      e (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a) := by
  classical
  let inclA := Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A)
  let inclB := Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B)
  apply tensor_fixed_exists_includeRight (K := K) (C := B)
  intro σ
  rw [he σ]
  simp [inclA]

/-- Helper for Exercise 13-13.1-16: the descended value of an equivariant base-changed algebra
map. -/
noncomputable def descendedElementOfEquivariantBaseChange
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ B] [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (e : K ⊗[ℚ] A ≃ₐ[K] K ⊗[ℚ] B)
    (he : ∀ σ : Gal(K / ℚ), ∀ x : K ⊗[ℚ] A,
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x))
    (a : A) : B :=
  Classical.choose (descendedElement_exists_of_equivariantBaseChange
    (K := K) (A := A) (B := B) e he a)

/-- Helper for Exercise 13-13.1-16: the descended value includes back to the prescribed
base-changed value. -/
theorem descendedElementOfEquivariantBaseChange_includeRight
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ B] [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (e : K ⊗[ℚ] A ≃ₐ[K] K ⊗[ℚ] B)
    (he : ∀ σ : Gal(K / ℚ), ∀ x : K ⊗[ℚ] A,
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x))
    (a : A) :
    Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B)
      (descendedElementOfEquivariantBaseChange (K := K) (A := A) (B := B) e he a) =
        e (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a) :=
  Classical.choose_spec (descendedElement_exists_of_equivariantBaseChange
    (K := K) (A := A) (B := B) e he a)

/-- Helper for Exercise 13-13.1-16: an equivariant base-changed algebra equivalence descends to an
algebra homomorphism over `ℚ`. -/
noncomputable def descendedAlgHomOfEquivariantBaseChange
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ B] [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (e : K ⊗[ℚ] A ≃ₐ[K] K ⊗[ℚ] B)
    (he : ∀ σ : Gal(K / ℚ), ∀ x : K ⊗[ℚ] A,
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x)) :
    A →ₐ[ℚ] B := by
  classical
  let inclA := Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A)
  let inclB := Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B)
  have hinjB : Function.Injective inclB :=
    Algebra.TensorProduct.includeRight_injective (R := ℚ) (A := K) (B := B)
      (FaithfulSMul.algebraMap_injective ℚ K)
  let f : A → B := descendedElementOfEquivariantBaseChange (K := K) (A := A) (B := B) e he
  have hf_spec : ∀ a, inclB (f a) = e (inclA a) :=
    descendedElementOfEquivariantBaseChange_includeRight (K := K) (A := A) (B := B) e he
  refine
    { toFun := f
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · apply hinjB
    calc
      inclB (f 1) = e (inclA 1) := hf_spec 1
      _ = e 1 := by simp [inclA, Algebra.TensorProduct.one_def]
      _ = 1 := map_one e
      _ = inclB 1 := by simp [inclB, Algebra.TensorProduct.one_def]
  · intro a a'
    apply hinjB
    calc
      inclB (f (a * a')) = e (inclA (a * a')) := hf_spec (a * a')
      _ = e (inclA a * inclA a') := by simp [inclA]
      _ = e (inclA a) * e (inclA a') := by rw [map_mul]
      _ = inclB (f a) * inclB (f a') := by rw [← hf_spec a, ← hf_spec a']
      _ = inclB (f a * f a') := by simp [inclB]
  · apply hinjB
    rw [hf_spec]
    simp [inclA, inclB]
  · intro a a'
    apply hinjB
    calc
      inclB (f (a + a')) = e (inclA (a + a')) := hf_spec (a + a')
      _ = e (inclA a + inclA a') := by simp [inclA, TensorProduct.tmul_add]
      _ = e (inclA a) + e (inclA a') := by rw [map_add]
      _ = inclB (f a) + inclB (f a') := by rw [← hf_spec a, ← hf_spec a']
      _ = inclB (f a + f a') := by simp [inclB, TensorProduct.tmul_add]
  · intro q
    apply hinjB
    calc
      inclB (f (algebraMap ℚ A q)) = e (inclA (algebraMap ℚ A q)) :=
        hf_spec (algebraMap ℚ A q)
      _ = e (algebraMap K (K ⊗[ℚ] A) (algebraMap ℚ K q)) := by simp [inclA]
      _ = algebraMap K (K ⊗[ℚ] B) (algebraMap ℚ K q) := by
        simpa using e.commutes (algebraMap ℚ K q)
      _ = inclB (algebraMap ℚ B q) := by simp [inclB]

/-- Helper for Exercise 13-13.1-16: the descended algebra homomorphism includes back to the
base-changed map. -/
theorem descendedAlgHomOfEquivariantBaseChange_includeRight
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ B] [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (e : K ⊗[ℚ] A ≃ₐ[K] K ⊗[ℚ] B)
    (he : ∀ σ : Gal(K / ℚ), ∀ x : K ⊗[ℚ] A,
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x))
    (a : A) :
    Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B)
      (descendedAlgHomOfEquivariantBaseChange (K := K) (A := A) (B := B) e he a) =
        e (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a) :=
  descendedElementOfEquivariantBaseChange_includeRight (K := K) (A := A) (B := B) e he a

/-- Helper for Exercise 13-13.1-16: equivariance also holds for the inverse base-changed
equivalence. -/
theorem equivariant_baseChange_symm
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (e : K ⊗[ℚ] A ≃ₐ[K] K ⊗[ℚ] B)
    (he : ∀ σ : Gal(K / ℚ), ∀ x : K ⊗[ℚ] A,
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x)) :
    ∀ σ : Gal(K / ℚ), ∀ y : K ⊗[ℚ] B,
      tensorGaloisAlgHom (K := K) (C := A) σ (e.symm y) =
        e.symm (tensorGaloisAlgHom (K := K) (C := B) σ y) := by
  intro σ y
  have h := congrArg e.symm (he σ (e.symm y))
  simpa using h.symm

/-- Helper for Exercise 13-13.1-16: an equivariant base-changed algebra equivalence descends to an
algebra equivalence over `ℚ`. -/
noncomputable def algEquivOfEquivariantBaseChange
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B] [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (e : K ⊗[ℚ] A ≃ₐ[K] K ⊗[ℚ] B)
    (he : ∀ σ : Gal(K / ℚ), ∀ x : K ⊗[ℚ] A,
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x)) :
    A ≃ₐ[ℚ] B := by
  classical
  let f := descendedAlgHomOfEquivariantBaseChange (K := K) (A := A) (B := B) e he
  let g := descendedAlgHomOfEquivariantBaseChange (K := K) (A := B) (B := A) e.symm
    (equivariant_baseChange_symm (K := K) (A := A) (B := B) e he)
  let inclA := Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A)
  let inclB := Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B)
  have hinjA : Function.Injective inclA :=
    Algebra.TensorProduct.includeRight_injective (R := ℚ) (A := K) (B := A)
      (FaithfulSMul.algebraMap_injective ℚ K)
  have hinjB : Function.Injective inclB :=
    Algebra.TensorProduct.includeRight_injective (R := ℚ) (A := K) (B := B)
      (FaithfulSMul.algebraMap_injective ℚ K)
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · ext b
    apply hinjB
    calc
      inclB (f (g b)) = e (inclA (g b)) :=
        descendedAlgHomOfEquivariantBaseChange_includeRight
          (K := K) (A := A) (B := B) e he (g b)
      _ = e (e.symm (inclB b)) := by
        rw [descendedAlgHomOfEquivariantBaseChange_includeRight
          (K := K) (A := B) (B := A) e.symm
          (equivariant_baseChange_symm (K := K) (A := A) (B := B) e he) b]
      _ = inclB b := e.apply_symm_apply (inclB b)
  · ext a
    apply hinjA
    calc
      inclA (g (f a)) = e.symm (inclB (f a)) :=
        descendedAlgHomOfEquivariantBaseChange_includeRight
          (K := K) (A := B) (B := A) e.symm
          (equivariant_baseChange_symm (K := K) (A := A) (B := B) e he) (f a)
      _ = e.symm (e (inclA a)) := by
        rw [descendedAlgHomOfEquivariantBaseChange_includeRight
          (K := K) (A := A) (B := B) e he a]
      _ = inclA a := e.symm_apply_apply (inclA a)

/-- Helper for Exercise 13-13.1-16: the point equivalence attached to a split base-change model. -/
noncomputable def pointsEquivOfBaseChangeAlgEquiv
    {C : Type u} [CommRing C] [Algebra ℚ C]
    {α : Type u} [Finite α]
    (eFun : K ⊗[ℚ] C ≃ₐ[K] (α → K)) :
    α ≃ (C →ₐ[ℚ] K) := by
  let liftE := AlgHom.liftEquiv ℚ K C K
  let points := finite_function_algHom_points_equiv (α := α) (k := K)
  exact
    { toFun := fun i ↦ liftE.symm ((points i).comp eFun.toAlgHom)
      invFun := fun φ ↦ points.symm ((liftE φ).comp eFun.symm.toAlgHom)
      left_inv := by
        intro i
        apply points.injective
        ext F
        simp [liftE, points]
      right_inv := by
        intro φ
        apply liftE.injective
        ext x
        simp [liftE, points] }

/-- Helper for Exercise 13-13.1-16: evaluating a split-model point on the rational factor. -/
theorem pointsEquivOfBaseChangeAlgEquiv_apply
    {C : Type u} [CommRing C] [Algebra ℚ C]
    {α : Type u} [Finite α]
    (eFun : K ⊗[ℚ] C ≃ₐ[K] (α → K))
    (i : α) (c : C) :
    pointsEquivOfBaseChangeAlgEquiv (K := K) eFun i c =
      eFun (1 ⊗ₜ[ℚ] c) i := by
  classical
  simp [pointsEquivOfBaseChangeAlgEquiv]

/-- Helper for Exercise 13-13.1-16: split-model evaluation on a pure tensor. -/
theorem baseChangeAlgEquiv_apply_tmul
    {C : Type u} [CommRing C] [Algebra ℚ C]
    {α : Type u} [Finite α]
    (eFun : K ⊗[ℚ] C ≃ₐ[K] (α → K))
    (i : α) (a : K) (c : C) :
    eFun (a ⊗ₜ[ℚ] c) i =
      a * pointsEquivOfBaseChangeAlgEquiv (K := K) eFun i c := by
  classical
  calc
    eFun (a ⊗ₜ[ℚ] c) i = eFun (a • (1 ⊗ₜ[ℚ] c : K ⊗[ℚ] C)) i := by
          congr
          simp [TensorProduct.smul_tmul']
    _ = (a • eFun (1 ⊗ₜ[ℚ] c : K ⊗[ℚ] C)) i := by
          rw [map_smul]
    _ = a * eFun (1 ⊗ₜ[ℚ] c) i := by
          rfl
    _ = a * pointsEquivOfBaseChangeAlgEquiv (K := K) eFun i c := by
          rw [pointsEquivOfBaseChangeAlgEquiv_apply]

/-- Helper for Exercise 13-13.1-16: the tensor Galois action becomes the expected semilinear
action in a split function-algebra model. -/
theorem baseChangeAlgEquiv_tensorGalois_apply
    {C : Type u} [CommRing C] [Algebra ℚ C]
    {α : Type u} [Finite α] [MulAction ((ZMod (Monoid.exponent G))ˣ) α]
    (eFun : K ⊗[ℚ] C ≃ₐ[K] (α → K))
    (hEquiv : ∀ (t : Γ_ℚ(G)) (i : α),
      pointsEquivOfBaseChangeAlgEquiv (K := K) eFun (t • i) =
        t • pointsEquivOfBaseChangeAlgEquiv (K := K) eFun i)
    (σ : Gal(K / ℚ)) (x : K ⊗[ℚ] C) (i : α) :
    eFun (tensorGaloisAlgHom (K := K) (C := C) σ x) i =
      σ (eFun x (((galEquivZMod (Monoid.exponent G) K σ)⁻¹ :
        (ZMod (Monoid.exponent G))ˣ) • i)) := by
  classical
  let t : Γ_ℚ(G) := galEquivZMod (Monoid.exponent G) K σ
  have hσ : (galEquivZMod (Monoid.exponent G) K).symm t = σ := by
    simpa [t] using (MulEquiv.symm_apply_apply (galEquivZMod (Monoid.exponent G) K) σ)
  refine TensorProduct.induction_on x ?hz ?ht ?ha
  · simp [tensorGaloisAlgHom]
  · intro a c
    have hpt :
        pointsEquivOfBaseChangeAlgEquiv (K := K) eFun i c =
          σ (pointsEquivOfBaseChangeAlgEquiv (K := K) eFun (t⁻¹ • i) c) := by
      have h := hEquiv t (t⁻¹ • i)
      have hi : t • (t⁻¹ • i) = i := by simp [← mul_smul]
      rw [hi] at h
      have hc := congrArg (fun φ : C →ₐ[ℚ] K ↦ φ c) h
      change pointsEquivOfBaseChangeAlgEquiv (K := K) eFun i c =
        ((galEquivZMod (Monoid.exponent G) K).symm t)
          (pointsEquivOfBaseChangeAlgEquiv (K := K) eFun (t⁻¹ • i) c) at hc
      simpa [hσ] using hc
    simp only [tensorGaloisAlgHom_tmul]
    rw [baseChangeAlgEquiv_apply_tmul, baseChangeAlgEquiv_apply_tmul]
    simp [map_mul, hpt, t]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Exercise 13-13.1-16: a split base-change model indexed by the actual
`K`-valued points is equivariant for the cyclotomic action. -/
theorem baseChangeAlgEquiv_algHomPoints_equivariant
    {C : Type u} [CommRing C] [Algebra ℚ C]
    [Finite (C →ₐ[ℚ] K)]
    (eFun : TensorProduct ℚ K C ≃ₐ[K] ((C →ₐ[ℚ] K) → K))
    (hIncl : ∀ (φ : C →ₐ[ℚ] K) (c : C),
      eFun (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) c) φ =
        φ c) :
    ∀ (t : Γ_ℚ(G)) (φ : C →ₐ[ℚ] K),
      pointsEquivOfBaseChangeAlgEquiv (K := K) eFun (t • φ) =
        t • pointsEquivOfBaseChangeAlgEquiv (K := K) eFun φ := by
  intro t φ
  ext c
  rw [pointsEquivOfBaseChangeAlgEquiv_apply]
  change eFun (1 ⊗ₜ[ℚ] c) (t • φ) =
    ((galEquivZMod (Monoid.exponent G) K).symm t)
      (pointsEquivOfBaseChangeAlgEquiv (K := K) eFun φ c)
  rw [pointsEquivOfBaseChangeAlgEquiv_apply]
  rw [show (1 : K) ⊗ₜ[ℚ] c =
      Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) c by
      rw [Algebra.TensorProduct.includeRight_apply]]
  rw [hIncl, hIncl]
  rfl

/-- Helper for Exercise 13-13.1-16: equivariantly reindexing the `K`-points of two split
base-change models gives an equivariant base-change algebra equivalence. -/
theorem baseChangeAlgEquiv_reindex_algHomPoints_equivariant
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    [Finite (A →ₐ[ℚ] K)] [Finite (B →ₐ[ℚ] K)]
    (eA : TensorProduct ℚ K A ≃ₐ[K] ((A →ₐ[ℚ] K) → K))
    (eB : TensorProduct ℚ K B ≃ₐ[K] ((B →ₐ[ℚ] K) → K))
    (hInclA : ∀ (φ : A →ₐ[ℚ] K) (a : A),
      eA (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a) φ = φ a)
    (hInclB : ∀ (ψ : B →ₐ[ℚ] K) (b : B),
      eB (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B) b) ψ = ψ b)
    (ePts : (A →ₐ[ℚ] K) ≃ (B →ₐ[ℚ] K))
    (hePts : ∀ (t : Γ_ℚ(G)) (φ : A →ₐ[ℚ] K), ePts (t • φ) = t • ePts φ) :
    let eCoord : ((A →ₐ[ℚ] K) → K) ≃ₐ[K] ((B →ₐ[ℚ] K) → K) :=
      AlgEquiv.piCongrLeft' K (fun _ : (A →ₐ[ℚ] K) ↦ K) ePts
    let e : TensorProduct ℚ K A ≃ₐ[K] TensorProduct ℚ K B :=
      eA.trans (eCoord.trans eB.symm)
    ∀ (σ : Gal(K / ℚ)) (x : TensorProduct ℚ K A),
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x) := by
  intro eCoord e σ x
  apply eB.injective
  ext ψ
  let t : Γ_ℚ(G) := galEquivZMod (Monoid.exponent G) K σ
  have hInv (ψ : B →ₐ[ℚ] K) :
      ePts.symm ((t⁻¹ : Γ_ℚ(G)) • ψ) = (t⁻¹ : Γ_ℚ(G)) • ePts.symm ψ := by
    apply ePts.injective
    rw [ePts.apply_symm_apply, hePts, ePts.apply_symm_apply]
  calc
    eB (tensorGaloisAlgHom (K := K) (C := B) σ (e x)) ψ
        = σ (eB (e x) (((galEquivZMod (Monoid.exponent G) K σ)⁻¹ :
            (ZMod (Monoid.exponent G))ˣ) • ψ)) := by
          rw [baseChangeAlgEquiv_tensorGalois_apply (G := G) (K := K) eB
            (baseChangeAlgEquiv_algHomPoints_equivariant (G := G) (K := K) eB hInclB)]
    _ = σ (eA x (ePts.symm ((t⁻¹ : Γ_ℚ(G)) • ψ))) := by
          simp [e, eCoord, t, AlgEquiv.piCongrLeft']
    _ = σ (eA x ((t⁻¹ : Γ_ℚ(G)) • ePts.symm ψ)) := by
          rw [hInv]
    _ = eA (tensorGaloisAlgHom (K := K) (C := A) σ x) (ePts.symm ψ) := by
          rw [baseChangeAlgEquiv_tensorGalois_apply (G := G) (K := K) eA
            (baseChangeAlgEquiv_algHomPoints_equivariant (G := G) (K := K) eA hInclA)]
    _ = eB (e (tensorGaloisAlgHom (K := K) (C := A) σ x)) ψ := by
          simp [e, eCoord, AlgEquiv.piCongrLeft']

/-- Helper for Exercise 13-13.1-16: reindex a split base-change model by the actual `K`-points
of the rational algebra. -/
noncomputable def baseChangeAlgEquivAlgHomPoints
    {C : Type u} [CommRing C] [Algebra ℚ C]
    {α : Type u} [Finite α]
    (eFun : TensorProduct ℚ K C ≃ₐ[K] (α → K)) :
    TensorProduct ℚ K C ≃ₐ[K] ((C →ₐ[ℚ] K) → K) :=
  eFun.trans
    (AlgEquiv.piCongrLeft' K (fun _ : α ↦ K)
      (pointsEquivOfBaseChangeAlgEquiv (K := K) eFun))

/-- Helper for Exercise 13-13.1-16: the reindexed split model evaluates rational-factor tensors
by the corresponding `K`-point. -/
theorem baseChangeAlgEquivAlgHomPoints_includeRight
    {C : Type u} [CommRing C] [Algebra ℚ C]
    {α : Type u} [Finite α]
    (eFun : TensorProduct ℚ K C ≃ₐ[K] (α → K))
    (φ : C →ₐ[ℚ] K) (c : C) :
    baseChangeAlgEquivAlgHomPoints (K := K) eFun
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) c) φ =
      φ c := by
  classical
  let eIndex := pointsEquivOfBaseChangeAlgEquiv (K := K) eFun
  calc
    baseChangeAlgEquivAlgHomPoints (K := K) eFun
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) c) φ
        = eFun (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := C) c)
            (eIndex.symm φ) := by
              simp [baseChangeAlgEquivAlgHomPoints, eIndex, AlgEquiv.piCongrLeft']
    _ = eIndex (eIndex.symm φ) c := by
          rw [Algebra.TensorProduct.includeRight_apply]
          rw [pointsEquivOfBaseChangeAlgEquiv_apply]
    _ = φ c := by
          rw [eIndex.apply_symm_apply]

/-- Helper for Exercise 13-13.1-16: for two rational algebras split by their `K`-points, an
isomorphism of the cyclotomic `Γ_ℚ`-sets of points descends to a `ℚ`-algebra equivalence. -/
theorem algEquiv_of_isomorphic_algHom_actions_of_split_baseChange
    {A B : Type u} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    [Finite (A →ₐ[ℚ] K)] [Finite (B →ₐ[ℚ] K)]
    (eA : TensorProduct ℚ K A ≃ₐ[K] ((A →ₐ[ℚ] K) → K))
    (eB : TensorProduct ℚ K B ≃ₐ[K] ((B →ₐ[ℚ] K) → K))
    (hInclA : ∀ (φ : A →ₐ[ℚ] K) (a : A),
      eA (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a) φ = φ a)
    (hInclB : ∀ (ψ : B →ₐ[ℚ] K) (b : B),
      eB (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B) b) ψ = ψ b)
    (hPts : IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) (A →ₐ[ℚ] K))
      (Action.ofMulAction (Γ_ℚ(G)) (B →ₐ[ℚ] K))) :
    Nonempty (A ≃ₐ[ℚ] B) := by
  classical
  rcases hPts with ⟨eIso⟩
  let ePts : (A →ₐ[ℚ] K) ≃ (B →ₐ[ℚ] K) := equivOfActionIso eIso
  have hePts : ∀ (t : Γ_ℚ(G)) (φ : A →ₐ[ℚ] K), ePts (t • φ) = t • ePts φ := by
    intro t φ
    exact equivOfActionIso_smul eIso t φ
  let eCoord : ((A →ₐ[ℚ] K) → K) ≃ₐ[K] ((B →ₐ[ℚ] K) → K) :=
    AlgEquiv.piCongrLeft' K (fun _ : (A →ₐ[ℚ] K) ↦ K) ePts
  let e : TensorProduct ℚ K A ≃ₐ[K] TensorProduct ℚ K B :=
    eA.trans (eCoord.trans eB.symm)
  have he : ∀ (σ : Gal(K / ℚ)) (x : TensorProduct ℚ K A),
      tensorGaloisAlgHom (K := K) (C := B) σ (e x) =
        e (tensorGaloisAlgHom (K := K) (C := A) σ x) := by
    -- The point-set equivariance is exactly the semilinear compatibility needed for descent.
    simpa [e, eCoord] using
      baseChangeAlgEquiv_reindex_algHomPoints_equivariant
        (G := G) (K := K) eA eB hInclA hInclB ePts hePts
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ K
  exact ⟨algEquivOfEquivariantBaseChange (K := K) (A := A) (B := B) e he⟩

section SplitCentralCharacters

attribute [local instance] Classical.decEq

-- An imported file (`Serre.Chap14.Remark_14_14_1_2`) declares `private instance`s for the
-- `K`-module / scalar-tower structure on a `K[G]`-submodule via `Submodule.restrictScalars`.
-- `private` only hides the *name*; the instances still activate globally and shadow Mathlib's
-- canonical `Submodule.module'`/`Submodule.isScalarTower`, whose absence here derails downstream
-- `IsScalarTower`/`FiniteDimensional` synthesis (and the `Representation.ofModule'` instance
-- arguments). Re-instate the canonical instances at high priority so they win, restoring the
-- automatic synthesis this section relies on.
noncomputable local instance (priority := 10000) splitSubmoduleModuleOverField
    {M : Type u} [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M]
    (S : Submodule K[G] M) : Module K ↥S :=
  Submodule.module' S

local instance (priority := 10000) splitSubmoduleIsScalarTower
    {M : Type u} [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M]
    (S : Submodule K[G] M) : IsScalarTower K K[G] ↥S :=
  Submodule.isScalarTower S

/-- Helper for Exercise 13-13.1-16: for `Representation.ofModule'`, the group-algebra action is
the original scalar action on the module. -/
lemma ofModule'_asAlgebraHom_apply_split
    (M : Type u) [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M]
    (r : K[G]) (m : M) :
    ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r) m = r • m := by
  refine MonoidAlgebra.induction_on (p := fun r : K[G] =>
    ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r) m = r • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Exercise 13-13.1-16: `Representation.ofModule'` has the same `K[G]`-module owner
as the original module. -/
lemma nonempty_ofModule'_asModuleLinearEquiv_split
    (M : Type u) [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M] :
    Nonempty ((Representation.ofModule' (k := K) (G := G) M).asModule ≃ₗ[K[G]] M) := by
  let toFun : (Representation.ofModule' (k := K) (G := G) M).asModule → M :=
    fun x => (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := K) (G := G) M).asModule :=
    fun x => (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : K[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    calc
      (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := K) (G := G) M).asModuleEquiv x) := by
                simpa using
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := K) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv x := by
            simp [ofModule'_asAlgebraHom_apply_split]
  exact
    ⟨{ toFun := toFun
       invFun := invFun
       left_inv := hleft
       right_inv := hright
       map_add' := hadd
       map_smul' := hsmul }⟩

/-- Helper for Exercise 13-13.1-16: a simple left ideal, viewed as `Representation.ofModule'`, is
irreducible. -/
lemma ofModule'_isIrreducible_of_isSimpleModule_split
    (S : Submodule K[G] K[G]) (hS : IsSimpleModule K[G] S) :
    (Representation.ofModule' (k := K) (G := G) S).IsIrreducible := by
  rcases nonempty_ofModule'_asModuleLinearEquiv_split (K := K) (G := G) S with ⟨eS⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := K) (G := G) S)).2
      (@IsSimpleModule.congr (K[G]) inferInstance
        ((Representation.ofModule' (k := K) (G := G) S).asModule)
        (Representation.ofModule' (k := K) (G := G) S).instAddCommGroupAsModule
        (Representation.ofModule' (k := K) (G := G) S).instModuleMonoidAlgebraAsModule
        S S.addCommGroup S.module eS hS)

/-- Helper for Exercise 13-13.1-16: an isomorphism of `Rep` objects gives an equivalence of the
underlying representations. -/
lemma nonempty_equiv_of_nonempty_iso_of_rep_split
    {V : Type u} [AddCommGroup V] [Module K V]
    {W : Type u} [AddCommGroup W] [Module K W]
    (τ : Representation K G V) (σ : Representation K G W)
    (h : Nonempty (Rep.of τ ≅ Rep.of σ)) :
    Nonempty (τ.Equiv σ) := by
  rcases h with ⟨e⟩
  refine ⟨Representation.Equiv.mk ?_ ?_⟩
  · refine
      { toLinearMap := e.hom.hom.toLinearMap
        invFun := e.inv.hom.toLinearMap
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      exact Iso.hom_inv_id_apply e x
    · intro x
      exact Iso.inv_hom_id_apply e x
  · intro g
    ext x
    exact congrArg (fun m : V →ₗ[K] W => m x) (e.hom.hom.2 g)

/-- Helper for Exercise 13-13.1-16: an equivalence from `Representation.ofModule' S` gives the
corresponding `K[G]`-linear equivalence of owner modules. -/
lemma nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'_split
    {W : Type u} [AddCommGroup W] [Module K W]
    (τ : Representation K G W) (S : Submodule K[G] K[G])
    (h : Nonempty ((Representation.ofModule' (k := K) (G := G) S).Equiv τ)) :
    Nonempty (S ≃ₗ[K[G]] τ.asModule) := by
  letI : Module K[G] τ.asModule := τ.instModuleMonoidAlgebraAsModule
  rcases h with ⟨e⟩
  let toFunS : (Representation.ofModule' (k := K) (G := G) S).asModule → S :=
    fun x => (Representation.ofModule' (k := K) (G := G) S).asModuleEquiv x
  let invFunS : S → (Representation.ofModule' (k := K) (G := G) S).asModule :=
    fun x => (Representation.ofModule' (k := K) (G := G) S).asModuleEquiv.symm x
  have hleftS : Function.LeftInverse invFunS toFunS := by
    intro x
    simp [toFunS, invFunS]
  have hrightS : Function.RightInverse invFunS toFunS := by
    intro x
    simp [toFunS, invFunS]
  have haddS : ∀ x y, toFunS (x + y) = toFunS x + toFunS y := by
    intro x y
    rfl
  have hsmulS : ∀ (r : K[G]) x, toFunS (r • x) = r • toFunS x := by
    intro r x
    calc
      (Representation.ofModule' (k := K) (G := G) S).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := K) (G := G) S).asAlgebraHom r)
              ((Representation.ofModule' (k := K) (G := G) S).asModuleEquiv x) := by
                simpa using
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := K) (G := G) S) r x)
      _ = r • (Representation.ofModule' (k := K) (G := G) S).asModuleEquiv x := by
            simpa [ofModule'_asAlgebraHom_apply_split]
  let eS : (Representation.ofModule' (k := K) (G := G) S).asModule ≃ₗ[K[G]] S :=
    { toFun := toFunS
      invFun := invFunS
      left_inv := hleftS
      right_inv := hrightS
      map_add' := haddS
      map_smul' := hsmulS }
  let f : (Representation.ofModule' (k := K) (G := G) S).asModule →ₗ[K[G]] τ.asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.ofModule' (k := K) (G := G) S) (σ := τ)) e.toIntertwiningMap
  have hf_bij : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact e.injective hxy
    · intro w
      refine ⟨eS.symm (e.symm (τ.asModuleEquiv w)), ?_⟩
      change (e ((Representation.ofModule' (k := K) (G := G) S).asModuleEquiv
        (eS.symm (e.symm (τ.asModuleEquiv w)))) : W) = (τ.asModuleEquiv w : W)
      have htransport :
          (Representation.ofModule' (k := K) (G := G) S).asModuleEquiv
              (eS.symm (e.symm (τ.asModuleEquiv w))) =
            e.symm (τ.asModuleEquiv w) := by
        rfl
      rw [htransport]
      exact e.apply_symm_apply (τ.asModuleEquiv w)
  exact ⟨eS.symm.trans (LinearEquiv.ofBijective f hf_bij)⟩

/-- Helper for Exercise 13-13.1-16: the previous owner equivalence as a `ModuleCat` isomorphism. -/
lemma nonempty_moduleIso_of_nonempty_equiv_ofModule'_split
    {W : Type u} [AddCommGroup W] [Module K W]
    (τ : Representation K G W) (S : Submodule K[G] K[G])
    (h : Nonempty ((Representation.ofModule' (k := K) (G := G) S).Equiv τ)) :
    Nonempty (ModuleCat.of K[G] S ≅ Rep.toModuleMonoidAlgebra.obj (Rep.of τ)) := by
  rcases nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'_split
      (K := K) (G := G) τ S h with ⟨e⟩
  exact ⟨by simpa using e.toModuleIso⟩

/-- Helper for Exercise 13-13.1-16: a simple left ideal is isomorphic to a member of a complete
irreducible family. -/
lemma exists_moduleIso_of_simple_submodule_of_complete_family_split
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (S : Submodule K[G] K[G]) (hS : IsSimpleModule K[G] S) :
    ∃ i, Nonempty (ModuleCat.of K[G] S ≅ Rep.toModuleMonoidAlgebra.obj (Rep.of (π i).ρ)) := by
  let τS : Representation K G S := Representation.ofModule' (k := K) (G := G) S
  have hτS : τS.IsIrreducible := by
    simpa [τS] using
      ofModule'_isIrreducible_of_isSimpleModule_split (K := K) (G := G) S hS
  letI : τS.IsIrreducible := hτS
  rcases IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := fun i ↦ FDRep.of (π i).ρ) hπ_complete τS inferInstance with ⟨i, hi⟩
  have hi_rep : Nonempty (Rep.of τS ≅ Rep.of (π i).ρ) := by
    rcases hi with ⟨eFD⟩
    exact ⟨(forget₂ (FDRep K G) (Rep K G)).mapIso eFD⟩
  have hi_equiv : Nonempty (τS.Equiv (π i).ρ) :=
    nonempty_equiv_of_nonempty_iso_of_rep_split (K := K) (G := G) τS (π i).ρ hi_rep
  exact ⟨i, nonempty_moduleIso_of_nonempty_equiv_ofModule'_split
    (K := K) (G := G) (π i).ρ S hi_equiv⟩

/-- Helper for Exercise 13-13.1-16: a zero Wedderburn-family component annihilates each member
of the family. -/
lemma family_member_smul_eq_zero_of_familyEndAlgHom_eq_zero_split
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    {x : K[G]} (hx : (ρ̃[π]) x = 0) (i : ι)
    (z : Rep.toModuleMonoidAlgebra.obj (Rep.of (π i).ρ)) :
    x • z = 0 := by
  have hxi : ((ρ̃[π]) x) i = 0 := by
    simpa using congrFun hx i
  simpa using LinearMap.congr_fun hxi z

/-- Helper for Exercise 13-13.1-16: a group-algebra element killed by a complete family
annihilates every simple left ideal. -/
lemma simple_submodule_smul_eq_zero_of_familyEndAlgHom_eq_zero_split
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    {x : K[G]} (hx : (ρ̃[π]) x = 0)
    (S : Submodule K[G] K[G]) (hS : IsSimpleModule K[G] S)
    {y : K[G]} (hy : y ∈ S) :
    x * y = 0 := by
  rcases exists_moduleIso_of_simple_submodule_of_complete_family_split
      (π := π) hπ_complete S hS with ⟨i, ⟨e⟩⟩
  have hz : x • ModuleCat.Hom.hom e.hom ⟨y, hy⟩ = 0 :=
    family_member_smul_eq_zero_of_familyEndAlgHom_eq_zero_split
      (π := π) hx i (ModuleCat.Hom.hom e.hom ⟨y, hy⟩)
  have hz' := congrArg (ModuleCat.Hom.hom e.inv) hz
  rw [LinearMap.map_smul] at hz'
  simp only [LinearMap.map_zero] at hz'
  have hid : (ModuleCat.Hom.hom e.inv) ((ModuleCat.Hom.hom e.hom) ⟨y, hy⟩) = ⟨y, hy⟩ := by
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun f => f ⟨y, hy⟩) (congrArg ModuleCat.Hom.hom e.hom_inv_id)
  rw [hid] at hz'
  exact Subtype.ext_iff.mp hz'

/-- Helper for Exercise 13-13.1-16: if an element kills all simple left ideals, left
multiplication by it is zero. -/
lemma left_mul_eq_zero_of_zero_on_all_simple_submodules_split
    {x : K[G]}
    (hx : ∀ (S : Submodule K[G] K[G]), IsSimpleModule K[G] S →
      ∀ ⦃y : K[G]⦄, y ∈ S → x * y = 0) :
    Algebra.lmul K (K[G]) x = 0 := by
  letI : Fintype G := Fintype.ofFinite G
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  letI : IsSemisimpleModule K[G] K[G] := inferInstance
  have htop :
      (⨆ (S : Submodule K[G] K[G]) (_ : IsSimpleModule K[G] S), S) = ⊤ := by
    simpa [sSup_eq_iSup] using
      (IsSemisimpleModule.sSup_simples_eq_top (R := K[G]) (M := K[G]))
  have htopK :
      (⨆ (S : Submodule K[G] K[G]) (_ : IsSimpleModule K[G] S), S.restrictScalars K) = ⊤ := by
    simpa using congrArg (Submodule.restrictScalars K) htop
  have hspan :
      Submodule.span K
          (Set.iUnion fun S : Submodule K[G] K[G] ↦
            Set.iUnion fun _ : IsSimpleModule K[G] S ↦
              ((S.restrictScalars K : Submodule K K[G]) : Set K[G])) =
        ⊤ := by
    rw [← Submodule.iSup_eq_span'
      (p := fun S : Submodule K[G] K[G] ↦ S.restrictScalars K)
      (h := fun S ↦ IsSimpleModule K[G] S)]
    exact htopK
  apply LinearMap.ext
  intro y
  have hy_span :
      y ∈ Submodule.span K
        (Set.iUnion fun S : Submodule K[G] K[G] ↦
          Set.iUnion fun _ : IsSimpleModule K[G] S ↦
            ((S.restrictScalars K : Submodule K K[G]) : Set K[G])) := by
    rw [hspan]
    simp
  refine Submodule.span_induction
    (p := fun z _ ↦ (Algebra.lmul K (K[G]) x) z = 0) ?_ ?_ ?_ ?_ hy_span
  · intro z hz
    rcases Set.mem_iUnion.1 hz with ⟨S, hz⟩
    rcases Set.mem_iUnion.1 hz with ⟨hS, hz⟩
    simpa using hx S hS hz
  · simp
  · intro z w hz hw hzh hwh
    calc
      ((Algebra.lmul K (K[G]) x) (z + w))
          = ((Algebra.lmul K (K[G]) x) z) + ((Algebra.lmul K (K[G]) x) w) := by
              exact LinearMap.map_add (Algebra.lmul K (K[G]) x) z w
      _ = 0 := by
            rw [hzh, hwh]
            simp
  · intro a z hz hzh
    calc
      ((Algebra.lmul K (K[G]) x) (a • z)) = a • ((Algebra.lmul K (K[G]) x) z) := by
        exact LinearMap.map_smul (Algebra.lmul K (K[G]) x) a z
      _ = 0 := by
            rw [hzh]
            simp

/-- Helper for Exercise 13-13.1-16: the Wedderburn-family map is injective for a complete
irreducible family over the cyclotomic splitting field. -/
lemma familyEndAlgHom_injective_of_complete_family_split
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Function.Injective (ρ̃[π]) := by
  intro x y hxy
  have hxy_zero : (ρ̃[π]) (x - y) = 0 := by
    simpa [map_sub, hxy]
  have hleft_zero : Algebra.lmul K (K[G]) (x - y) = 0 :=
    left_mul_eq_zero_of_zero_on_all_simple_submodules_split (K := K) (G := G)
      (fun S hS {y} hy ↦
        simple_submodule_smul_eq_zero_of_familyEndAlgHom_eq_zero_split
          (π := π) hπ_complete hxy_zero S hS hy)
  exact sub_eq_zero.mp <|
    (Algebra.lmul_injective (R := K) (A := K[G])) (by simpa using hleft_zero)

/-- Helper for Exercise 13-13.1-16: a central group-algebra element acts by an intertwining
endomorphism. -/
lemma asAlgebraHom_isIntertwining_of_mem_center_split
    {V : Type u} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (u : Subalgebra.center K (K[G])) :
    ρ.IsIntertwiningMap ρ (ρ.asAlgebraHom u) := by
  rw [isIntertwiningMap_iff]
  intro g v
  have h :=
    congrArg (ρ.asAlgebraHom)
      (((Subalgebra.mem_center_iff.mp u.2) (MonoidAlgebra.of K G g)).symm)
  simpa [Representation.asAlgebraHom_of, Module.End.mul_apply] using LinearMap.congr_fun h v

/-- Helper for Exercise 13-13.1-16: the central action map into the self-intertwining algebra. -/
noncomputable def splitCenterToIntertwining
    {V : Type u} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) :
    Subalgebra.center K (K[G]) →ₐ[K] ρ.IntertwiningMap ρ where
  toFun u :=
    (ρ.asAlgebraHom u).intertwiningMap_of_isIntertwiningMap ρ ρ
      (asAlgebraHom_isIntertwining_of_mem_center_split (G := G) ρ u).isIntertwining
  map_zero' := by
    ext v
    rfl
  map_one' := by
    ext v
    simp
  map_add' u v := by
    ext w
    simp
  map_mul' u v := by
    ext w
    simp [Module.End.mul_apply]
  commutes' c := by
    ext v
    simp

/-- Helper for Exercise 13-13.1-16: Schur's lemma over the cyclotomic splitting field identifies
the self-intertwining algebra of a simple representation with the base field. -/
noncomputable def splitSchurAlgEquiv (S : FDRep K G) [Simple S] :
    K ≃ₐ[K] Representation.IntertwiningMap S.ρ S.ρ := by
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    hasEnoughRootsOfUnity_of_cyclotomic (G := G) (K := K)
  have hfin :
      Module.finrank K (Representation.IntertwiningMap S.ρ S.ρ) = 1 :=
    simple_selfIntertwining_finrank_eq_one_of_hasEnoughRoots (G := G) (K := K) S
  have hbij :
      Function.Bijective
        ⇑(Algebra.ofId K (Representation.IntertwiningMap S.ρ S.ρ)) := by
    let E := Representation.IntertwiningMap S.ρ S.ρ
    have hEpos : 0 < Module.finrank K E := by
      rw [hfin]
      norm_num
    letI : Nontrivial E := Module.finrank_pos_iff.mp hEpos
    have hinj : Function.Injective (Algebra.linearMap K E) := by
      intro a b hab
      apply sub_eq_zero.mp
      have hsub : (a - b) • (1 : E) = 0 := by
        change (Algebra.linearMap K E) (a - b) = 0
        rw [map_sub, hab, sub_self]
      exact (smul_eq_zero.mp hsub).resolve_right one_ne_zero
    have hdim : Module.finrank K K = Module.finrank K E := by
      rw [show Module.finrank K K = 1 by simp,
        show Module.finrank K E = 1 by simpa [E] using hfin]
    have hsurj : Function.Surjective (Algebra.linearMap K E) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := Algebra.linearMap K E) hdim).1 hinj
    constructor
    · intro a b hab
      exact hinj hab
    · intro y
      rcases hsurj y with ⟨a, ha⟩
      exact ⟨a, by simpa [Algebra.ofId, Algebra.linearMap] using ha⟩
  exact
    AlgEquiv.ofBijective (Algebra.ofId K (Representation.IntertwiningMap S.ρ S.ρ))
      hbij

/-- Helper for Exercise 13-13.1-16: the central character of a simple representation over the
cyclotomic splitting field. -/
noncomputable def splitCentralCharacter (S : FDRep K G) [Simple S] :
    Subalgebra.center K (K[G]) →ₐ[K] K :=
  (splitSchurAlgEquiv (G := G) (K := K) S).symm.toAlgHom.comp
    (splitCenterToIntertwining (G := G) S.ρ)

/-- Helper for Exercise 13-13.1-16: a central element acts by the scalar given by its split
central character. -/
theorem asAlgebraHom_center_eq_splitCentralCharacter_smul_id
    (S : FDRep K G) [Simple S] (u : Subalgebra.center K (K[G])) :
    Representation.asAlgebraHom S.ρ u =
      splitCentralCharacter (G := G) (K := K) S u • LinearMap.id := by
  have h :
      splitSchurAlgEquiv (G := G) (K := K) S (splitCentralCharacter (G := G) (K := K) S u) =
        splitCenterToIntertwining (G := G) S.ρ u := by
    simp [splitCentralCharacter, splitSchurAlgEquiv]
  simpa [splitCenterToIntertwining, Representation.IntertwiningMap.algebraMap_apply] using
    (congrArg Representation.IntertwiningMap.toLinearMap h).symm

/-- Helper for Exercise 13-13.1-16: a simple finite-dimensional representation has positive
degree. -/
lemma simple_fdRep_finrank_pos_split (S : FDRep K G) [Simple S] :
    0 < Module.finrank K S := by
  have hS_nontriv : Nontrivial S := by
    by_contra hS_sub
    letI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS_sub
    have hzero : (𝟙 S : S ⟶ S) = 0 := by
      ext x
      simp
    exact CategoryTheory.id_nonzero S hzero
  letI : Nontrivial S := hS_nontriv
  exact Module.finrank_pos

/-- Helper for Exercise 13-13.1-16: the trace of a group-algebra element acting on a
representation is its coefficient-character sum. -/
theorem trace_asAlgebraHom_eq_sum_character_split
    (S : FDRep K G) (u : K[G]) :
    LinearMap.trace K S (Representation.asAlgebraHom S.ρ u) =
      ∑ g : G, u g * Representation.character S.ρ g := by
  letI : Fintype G := Fintype.ofFinite G
  have hcoeff :
      u = ∑ g : G, u g • MonoidAlgebra.of K G g := by
    rw [← Finsupp.sum_single u]
    rw [Finsupp.sum_fintype]
    · apply Finset.sum_congr rfl
      intro g hg
      ext x
      by_cases hx : x = g
      · subst x
        simp [MonoidAlgebra.of]
      · simp [MonoidAlgebra.of, hx]
    · intro i
      simp
  calc
    LinearMap.trace K S (Representation.asAlgebraHom S.ρ u)
        = LinearMap.trace K S
            (Representation.asAlgebraHom S.ρ (∑ g : G, u g • MonoidAlgebra.of K G g)) := by
            exact congrArg
              (fun a : K[G] ↦ LinearMap.trace K S (Representation.asAlgebraHom S.ρ a))
              hcoeff
    _ = LinearMap.trace K S (∑ g : G, u g • S.ρ g) := by
            congr 1
            simp
    _ = ∑ g : G, u g * Representation.character S.ρ g := by
          simp [Representation.character, smul_eq_mul]

/-- Helper for Exercise 13-13.1-16: the split central character is the normalized
coefficient-character sum. -/
theorem splitCentralCharacter_apply_eq_sum_character
    (S : FDRep K G) [Simple S] (u : Subalgebra.center K (K[G]))
    (hfinrank : (Module.finrank K S : K) ≠ 0) :
    splitCentralCharacter (G := G) (K := K) S u =
      (Module.finrank K S : K)⁻¹ *
        ∑ g : G, (u : K[G]) g * Representation.character S.ρ g := by
  let c : K := splitCentralCharacter (G := G) (K := K) S u
  have hscalar :
      Representation.asAlgebraHom S.ρ u = c • LinearMap.id := by
    simpa [c] using asAlgebraHom_center_eq_splitCentralCharacter_smul_id (G := G) (K := K) S u
  have htrace :
      c * (Module.finrank K S : K) =
        ∑ g : G, (u : K[G]) g * Representation.character S.ρ g := by
    calc
      c * (Module.finrank K S : K) = LinearMap.trace K S (c • (LinearMap.id : S →ₗ[K] S)) := by
        simp [LinearMap.trace_id, smul_eq_mul]
      _ = LinearMap.trace K S (Representation.asAlgebraHom S.ρ u) := by rw [← hscalar]
      _ = ∑ g : G, (u : K[G]) g * Representation.character S.ρ g := by
            simpa using trace_asAlgebraHom_eq_sum_character_split (G := G) (K := K) S (u : K[G])
  apply mul_right_cancel₀ hfinrank
  calc
    c * (Module.finrank K S : K) =
        ∑ g : G, (u : K[G]) g * Representation.character S.ρ g := htrace
    _ = (((Module.finrank K S : K)⁻¹ *
            ∑ g : G, (u : K[G]) g * Representation.character S.ρ g) *
          (Module.finrank K S : K)) := by
            symm
            rw [mul_assoc,
              mul_comm (∑ g : G, (u : K[G]) g * Representation.character S.ρ g)
              (Module.finrank K S : K), ← mul_assoc, inv_mul_cancel₀ hfinrank, one_mul]

/-- Helper for Exercise 13-13.1-16: the product of split central characters attached to a complete
family. -/
noncomputable def splitCentralCharacterFamilyAlgHom
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Subalgebra.center K (K[G]) →ₐ[K] (ι → K) :=
  Pi.algHom K (fun _ : ι ↦ K) fun i ↦
    letI : Simple (FDRep.of (π i).ρ) := hπ_complete.isSimple i
    splitCentralCharacter (G := G) (K := K) (FDRep.of (π i).ρ)

/-- Helper for Exercise 13-13.1-16: the split central-character family is injective. -/
theorem splitCentralCharacterFamilyAlgHom_injective
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Function.Injective (splitCentralCharacterFamilyAlgHom (G := G) (K := K) π hπ_complete) := by
  intro u v huv
  apply Subtype.ext
  apply familyEndAlgHom_injective_of_complete_family_split (G := G) (K := K) π hπ_complete
  ext i x
  letI : Simple (FDRep.of (π i).ρ) := hπ_complete.isSimple i
  have hcoord :
      splitCentralCharacterFamilyAlgHom (G := G) (K := K) π hπ_complete u i =
        splitCentralCharacterFamilyAlgHom (G := G) (K := K) π hπ_complete v i := by
    simpa using congrFun huv i
  have hu :=
    asAlgebraHom_center_eq_splitCentralCharacter_smul_id
      (G := G) (K := K) (FDRep.of (π i).ρ) u
  have hv :=
    asAlgebraHom_center_eq_splitCentralCharacter_smul_id
      (G := G) (K := K) (FDRep.of (π i).ρ) v
  have hmaps :
      Representation.asAlgebraHom (FDRep.of (π i).ρ).ρ u =
        Representation.asAlgebraHom (FDRep.of (π i).ρ).ρ v := by
    have hcoord' :
        splitCentralCharacter (G := G) (K := K) (FDRep.of (π i).ρ) u =
          splitCentralCharacter (G := G) (K := K) (FDRep.of (π i).ρ) v := by
      simpa [splitCentralCharacterFamilyAlgHom] using hcoord
    rw [hu, hv, hcoord']
  simpa using congrArg (fun f : Module.End K (π i) ↦ f x) hmaps

/-- Helper for Exercise 13-13.1-16: the index set and conjugacy classes have the same cardinality
after taking trivial rational-power orbits. -/
lemma fintype_card_index_eq_conjClasses_of_galois
    {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι] [Finite ι] [Fintype ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π) :
    Fintype.card ι = Fintype.card (ConjClasses G) := by
  classical
  have h :=
    nat_card_irreducible_orbitQuotient_eq_nat_card_galoisPowerClass
      (G := G) (K := K) (π := π) hπ_pairwise hπ_complete hπ_galois
      (⊥ : Subgroup (Γ_ℚ(G)))
  have hleft :
      Nat.card (MulAction.orbitRel.Quotient (⊥ : Subgroup (Γ_ℚ(G))) ι) = Nat.card ι :=
    Nat.card_congr (orbitRelBotQuotientEquiv (M := Γ_ℚ(G)) (α := ι))
  have hright :
      Nat.card (GaloisPowerClass (G := G) (⊥ : Subgroup (Γ_ℚ(G)))) =
        Nat.card (ConjClasses G) :=
    Nat.card_congr (galoisPowerClassBotEquivConjClasses (G := G))
  rw [hleft, hright] at h
  simpa [Nat.card_eq_fintype_card] using h

/-- Helper for Exercise 13-13.1-16: any complete pairwise family over the cyclotomic splitting
field has one member for each conjugacy class. -/
lemma fintype_card_index_eq_conjClasses_of_complete_pairwise
    {ι : Type u} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Fintype.card ι = Fintype.card (ConjClasses G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  letI : Module.Free ℤ (R[K](G)) := Module.Free.of_basis b
  letI : Module.Finite ℤ (R[K](G)) := Module.Finite.of_basis b
  let eRat :=
    tensorCharacterRingOverFieldAlgEquivRationalSubalgebra
      (G := G) (K := K) π hπ_pairwise hπ_complete
  let eBase :=
    rationalCharacterRingBaseChangeAlgEquivSelfSubalgebra
      (G := G) (K := K) π hπ_pairwise hπ_complete
  let eClass :=
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_self_algEquiv_conjClasses
      (G := G) (K := K)
  calc
    Fintype.card ι = Module.finrank ℤ (R[K](G)) := by
      symm
      simpa using Module.finrank_eq_card_basis b
    _ = Module.finrank ℚ (TensorProduct ℤ ℚ (R[K](G))) := by
      symm
      rw [Module.finrank_tensorProduct]
      simp
    _ = Module.finrank ℚ (characterRingOverFieldScalarExtensionSubalgebra K G) := by
      simpa [eRat] using eRat.toLinearEquiv.finrank_eq
    _ = Module.finrank K
        (TensorProduct ℚ K (characterRingOverFieldScalarExtensionSubalgebra K G)) := by
      symm
      rw [Module.finrank_tensorProduct]
      simp
    _ = Module.finrank K
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) := by
      simpa [eBase] using eBase.toLinearEquiv.finrank_eq
    _ = Module.finrank K (ConjClasses G → K) := by
      exact eClass.toLinearEquiv.finrank_eq
    _ = Fintype.card (ConjClasses G) := by
      rw [Module.finrank_fintype_fun_eq_card (R := K) (η := ConjClasses G)]

/-- Helper for Exercise 13-13.1-16: the split central-character family is an algebra equivalence
onto the finite product indexed by any complete irreducible family. -/
noncomputable def splitCentralCharacterFamilyAlgEquivOfComplete
    {ι : Type u} [Fintype ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Subalgebra.center K (K[G]) ≃ₐ[K] (ι → K) := by
  classical
  let f := splitCentralCharacterFamilyAlgHom (G := G) (K := K) π hπ_complete
  have hinj : Function.Injective f :=
    splitCentralCharacterFamilyAlgHom_injective (G := G) (K := K) π hπ_complete
  let πfd : ι → FDRep K G := fun i ↦ FDRep.of (π i).ρ
  have hπfd_pairwise : PairwiseNonisomorphic πfd :=
    pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise
  have hcard :
      Fintype.card ι = Fintype.card (ConjClasses G) :=
    fintype_card_index_eq_conjClasses_of_complete_pairwise
      (G := G) (K := K) (π := πfd) hπfd_pairwise hπ_complete
  have hdim :
      Module.finrank K (Subalgebra.center K (K[G])) =
        Module.finrank K (ι → K) := by
    calc
      Module.finrank K (Subalgebra.center K (K[G]))
          = Fintype.card (ConjClasses G) := by
              simpa using
                Module.finrank_eq_card_basis
                  (conjugacyClassSumBasis (G := G) (k := K))
      _ = Fintype.card ι := by rw [hcard]
      _ = Module.finrank K (ι → K) := by
            symm
            exact Module.finrank_fintype_fun_eq_card K
  have hsurj : Function.Surjective f := by
    have hlin_inj : Function.Injective f.toLinearMap := hinj
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) hdim).1
      hlin_inj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- Helper for Exercise 13-13.1-16: the split central-character family is an algebra equivalence
onto the finite product indexed by irreducible characters. -/
noncomputable def splitCentralCharacterFamilyAlgEquiv
    {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π) :
    Subalgebra.center K (K[G]) ≃ₐ[K] (ι → K) := by
  classical
  letI : Finite ι := finite_index_of_complete_pairwise_nonisomorphic_rep
    (G := G) (K := K) (π := π) hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  let f := splitCentralCharacterFamilyAlgHom (G := G) (K := K) π hπ_complete
  have hinj : Function.Injective f :=
    splitCentralCharacterFamilyAlgHom_injective (G := G) (K := K) π hπ_complete
  have hcard :
      Fintype.card ι = Fintype.card (ConjClasses G) :=
    fintype_card_index_eq_conjClasses_of_galois
      (G := G) (K := K) (π := π) hπ_pairwise hπ_complete hπ_galois
  have hdim :
      Module.finrank K (Subalgebra.center K (K[G])) =
        Module.finrank K (ι → K) := by
    calc
      Module.finrank K (Subalgebra.center K (K[G]))
          = Fintype.card (ConjClasses G) := by
              simpa using
                Module.finrank_eq_card_basis
                  (conjugacyClassSumBasis (G := G) (k := K))
      _ = Fintype.card ι := by rw [hcard]
      _ = Module.finrank K (ι → K) := by
            symm
            exact Module.finrank_fintype_fun_eq_card K
  have hsurj : Function.Surjective f := by
    have hlin_inj : Function.Injective f.toLinearMap := hinj
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) hdim).1
      hlin_inj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- Helper for Exercise 13-13.1-16: `K`-points of the rational center are indexed by irreducible
characters via split central characters. -/
noncomputable def centerAlgHomPointEquiv
    {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π) :
    ι ≃ (Subalgebra.center ℚ (ℚ[G]) →ₐ[ℚ] K) := by
  classical
  letI : Finite ι := finite_index_of_complete_pairwise_nonisomorphic_rep
    (G := G) (K := K) (π := π) hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  let eBase := centerBaseChangeAlgEquivCyclotomicCenter (G := G) (K := K)
  let eCent :=
    splitCentralCharacterFamilyAlgEquiv
      (G := G) (K := K) π hπ_pairwise hπ_complete hπ_galois
  let eFun : TensorProduct ℚ K (Subalgebra.center ℚ (ℚ[G])) ≃ₐ[K] (ι → K) :=
    eBase.trans eCent
  let liftE := AlgHom.liftEquiv ℚ K (Subalgebra.center ℚ (ℚ[G])) K
  let points := finite_function_algHom_points_equiv (α := ι) (k := K)
  exact
    { toFun := fun i ↦ liftE.symm ((points i).comp eFun.toAlgHom)
      invFun := fun φ ↦ points.symm ((liftE φ).comp eFun.symm.toAlgHom)
      left_inv := by
        intro i
        apply points.injective
        ext F
        simp [liftE, points, eFun]
      right_inv := by
        intro φ
        apply liftE.injective
        ext x
        simp [liftE, points, eFun] }

/-- Helper for Exercise 13-13.1-16: the `K`-points of the rational center are indexed by any
complete irreducible family, without requiring a chosen Galois action on that family. -/
noncomputable def centerAlgHomPointEquivOfComplete
    {ι : Type u} [Fintype ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    ι ≃ (Subalgebra.center ℚ (ℚ[G]) →ₐ[ℚ] K) := by
  classical
  let eBase := centerBaseChangeAlgEquivCyclotomicCenter (G := G) (K := K)
  let eCent :=
    splitCentralCharacterFamilyAlgEquivOfComplete
      (G := G) (K := K) π hπ_pairwise hπ_complete
  let eFun : TensorProduct ℚ K (Subalgebra.center ℚ (ℚ[G])) ≃ₐ[K] (ι → K) :=
    eBase.trans eCent
  let liftE := AlgHom.liftEquiv ℚ K (Subalgebra.center ℚ (ℚ[G])) K
  let points := finite_function_algHom_points_equiv (α := ι) (k := K)
  exact
    { toFun := fun i ↦ liftE.symm ((points i).comp eFun.toAlgHom)
      invFun := fun φ ↦ points.symm ((liftE φ).comp eFun.symm.toAlgHom)
      left_inv := by
        intro i
        apply points.injective
        ext F
        simp [liftE, points, eFun]
      right_inv := by
        intro φ
        apply liftE.injective
        ext x
        simp [liftE, points, eFun] }

@[simp] theorem centerAlgHomPointEquiv_apply
    {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (i : ι) (u : Subalgebra.center ℚ (ℚ[G])) :
    centerAlgHomPointEquiv
        (G := G) (K := K) π hπ_pairwise hπ_complete hπ_galois i u =
      (letI : Simple (FDRep.of (π i).ρ) := hπ_complete.isSimple i
       splitCentralCharacter (G := G) (K := K) (FDRep.of (π i).ρ)
        (centerRatToCyclotomicCenter (G := G) (K := K) u)) := by
  letI : Finite ι := finite_index_of_complete_pairwise_nonisomorphic_rep
    (G := G) (K := K) (π := π) hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Simple (FDRep.of (π i).ρ) := hπ_complete.isSimple i
  simp [centerAlgHomPointEquiv, splitCentralCharacterFamilyAlgEquiv,
    splitCentralCharacterFamilyAlgHom, centerBaseChangeAlgEquivCyclotomicCenter,
    centerBaseChangeToCyclotomicCenter]

end SplitCentralCharacters

section PartB

variable {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
variable (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]

/-- Exercise 13-13.1-16 (2): source part (b). The `Γ_ℚ`-set of irreducible `K`-characters can be
identified with the `Γ_ℚ`-set of `ℚ`-algebra homomorphisms from the center of `ℚ[G]` to the
cyclotomic field `K`, provided the given `Γ_ℚ`-action on the index set matches Galois
conjugation of irreducible characters. -/
theorem irreducible_character_index_isomorphic_center_algHom
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π) :
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) ι)
      (Action.ofMulAction (Γ_ℚ(G)) (Subalgebra.center ℚ (ℚ[G]) →ₐ[ℚ] K)) := by
  classical
  letI : Finite ι := finite_index_of_complete_pairwise_nonisomorphic_rep
    (G := G) (K := K) (π := π) hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  let e := centerAlgHomPointEquiv (G := G) (K := K) π hπ_pairwise hπ_complete hπ_galois
  refine action_ofMulAction_isomorphic_of_equivariant_equiv e ?_
  intro t i
  ext u
  let σ : K ≃ₐ[ℚ] K := (galEquivZMod (Monoid.exponent G) K).symm t
  let uK : Subalgebra.center K (K[G]) := centerRatToCyclotomicCenter (G := G) (K := K) u
  let Si : FDRep K G := FDRep.of (π i).ρ
  let Sti : FDRep K G := FDRep.of (π (t • i)).ρ
  letI : Simple Si := hπ_complete.isSimple i
  letI : Simple Sti := hπ_complete.isSimple (t • i)
  have hfin_i : (Module.finrank K Si : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (simple_fdRep_finrank_pos_split (G := G) (K := K) Si)
  have hfin_ti : (Module.finrank K Sti : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (simple_fdRep_finrank_pos_split (G := G) (K := K) Sti)
  have hdim :
      (Module.finrank K Sti : K) = (Module.finrank K Si : K) := by
    have hchar := hπ_galois t i (1 : G)
    have hfixed :
        t • (π i).ρ.character (1 : G) = (π i).ρ.character (1 : G) := by
      change σ ((π i).ρ.character (1 : G)) = (π i).ρ.character (1 : G)
      simp [σ, Representation.character]
    have hchar' : (π (t • i)).ρ.character (1 : G) = (π i).ρ.character (1 : G) := by
      rw [hchar, hfixed]
    simpa [Si, Sti, Representation.character] using hchar'
  have hcoeff_fixed (g : G) : σ ((uK : K[G]) g) = (uK : K[G]) g := by
    simp [σ, uK]
  have hchar_galois (g : G) :
      Representation.character Sti.ρ g = σ (Representation.character Si.ρ g) := by
    simpa [Si, Sti, σ] using hπ_galois t i g
  have hleft :
      splitCentralCharacter (G := G) (K := K) Sti uK =
        (Module.finrank K Sti : K)⁻¹ *
          ∑ g : G, (uK : K[G]) g * Representation.character Sti.ρ g :=
    splitCentralCharacter_apply_eq_sum_character (G := G) (K := K) Sti uK hfin_ti
  have hright :
      splitCentralCharacter (G := G) (K := K) Si uK =
        (Module.finrank K Si : K)⁻¹ *
          ∑ g : G, (uK : K[G]) g * Representation.character Si.ρ g :=
    splitCentralCharacter_apply_eq_sum_character (G := G) (K := K) Si uK hfin_i
  change e (t • i) u = σ (e i u)
  rw [show e (t • i) u = splitCentralCharacter (G := G) (K := K) Sti uK by
      simpa [e, Sti, uK] using
        centerAlgHomPointEquiv_apply (G := G) (K := K) π hπ_pairwise hπ_complete
          hπ_galois (t • i) u,
    show e i u = splitCentralCharacter (G := G) (K := K) Si uK by
      simpa [e, Si, uK] using
        centerAlgHomPointEquiv_apply (G := G) (K := K) π hπ_pairwise hπ_complete
          hπ_galois i u,
    hleft, hright]
  calc
    (Module.finrank K Sti : K)⁻¹ *
        ∑ g : G, (uK : K[G]) g * Representation.character Sti.ρ g
        =
      (Module.finrank K Si : K)⁻¹ *
        ∑ g : G, (uK : K[G]) g * σ (Representation.character Si.ρ g) := by
          rw [hdim]
          congr 1
          apply Finset.sum_congr rfl
          intro g hg
          rw [hchar_galois g]
    _ =
      σ ((Module.finrank K Si : K)⁻¹ *
        ∑ g : G, (uK : K[G]) g * Representation.character Si.ρ g) := by
          symm
          rw [map_mul, map_inv₀]
          congr 1
          · simp [σ]
          · rw [map_sum]
            apply Finset.sum_congr rfl
            intro g hg
            rw [map_mul, hcoeff_fixed g]

/-- Exercise 13-13.1-16 (3): source part (b). The `Γ_ℚ`-set of conjugacy classes of `G` can be
identified with the `Γ_ℚ`-set of `ℚ`-algebra homomorphisms from `ℚ ⊗ R_K(G)`, where `K` is the
cyclotomic splitting field `ℚ(m)` from the source statement. Using the `ℚ`-valued owner here
instead packages rational-power orbit data and is false for examples such as `C₄`. -/
theorem conjClasses_isomorphic_rationalCharacterRing_algHom :
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G))
      (Action.ofMulAction (Γ_ℚ(G))
        (characterRingOverFieldScalarExtensionSubalgebra K G →ₐ[ℚ] K)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  obtain ⟨κ, hκ, σ, hσ_pairwise, hσ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := K) (G := G)
  letI : Fintype κ := hκ
  let e :=
    rationalCharacterRingAlgHomPointEquiv
      (G := G) (K := K) σ hσ_pairwise hσ_complete
  refine action_ofMulAction_isomorphic_of_equivariant_equiv e ?_
  intro t c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  ext a
  have hcompat :=
    characterRingOverFieldScalarExtension_gammaRat_power_compatible
      (G := G) (K := K) (χ := (a : G → K)) a.2 g t
  change
    e (ConjClasses.mk (g ^ galoisPowerExponentUnit t)) a =
      smulCyclotomicAlgHom (G := G) (K := K) t (e (ConjClasses.mk g)) a
  simpa [e, smulCyclotomicAlgHom] using hcompat.symm

/-- Exercise 13-13.1-16 (4): source part (b). Once the two source sets are identified with the
corresponding cyclotomic character sets of `Subalgebra.center ℚ (ℚ[G])` and the split-field
character algebra `characterRingOverFieldScalarExtensionSubalgebra K G`, the `Γ_ℚ`-sets of
irreducible characters and conjugacy classes are isomorphic if and only if those two `ℚ`-algebras
are isomorphic. -/
theorem
    irreducible_character_index_isomorphic_to_conjClasses_iff_center_algEquiv_rationalCharacterRing
    {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
    (hX : IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) ι)
      (Action.ofMulAction (Γ_ℚ(G)) (Subalgebra.center ℚ (ℚ[G]) →ₐ[ℚ] K)))
    (hY : IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G))
      (Action.ofMulAction (Γ_ℚ(G))
        (characterRingOverFieldScalarExtensionSubalgebra K G →ₐ[ℚ] K))) :
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) ι)
      (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G)) ↔
      Nonempty
        (Subalgebra.center ℚ (ℚ[G]) ≃ₐ[ℚ]
          characterRingOverFieldScalarExtensionSubalgebra K G) := by
  constructor
  · intro hE
    classical
    let A := Subalgebra.center ℚ (ℚ[G])
    let B := characterRingOverFieldScalarExtensionSubalgebra K G
    letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ K
    rcases hX with ⟨eX⟩
    rcases hY with ⟨eY⟩
    rcases hE with ⟨eI⟩
    let ePtsIso : Action.ofMulAction (Γ_ℚ(G)) (A →ₐ[ℚ] K) ≅
        Action.ofMulAction (Γ_ℚ(G)) (B →ₐ[ℚ] K) :=
      eX.symm.trans (eI.trans eY)
    let ePts : (A →ₐ[ℚ] K) ≃ (B →ₐ[ℚ] K) := equivOfActionIso ePtsIso
    have hePts : ∀ (t : Γ_ℚ(G)) (φ : A →ₐ[ℚ] K), ePts (t • φ) = t • ePts φ := by
      intro t φ
      exact equivOfActionIso_smul ePtsIso t φ
    obtain ⟨κA, hκA, πA, hπA_pairwise, hπA_complete⟩ :=
      exists_complete_pairwise_nonisomorphic_simple_family_local (K := K) (G := G)
    letI : Fintype κA := hκA
    let πARep : κA → Rep K G := fun i ↦ Rep.of (πA i).ρ
    have hπARep_pairwise : PairwiseNonisomorphic πARep := by
      intro i j hij hij_iso
      apply hπA_pairwise hij
      rcases hij_iso with ⟨e⟩
      simpa [πARep] using ⟨(Representation.equivOfIso e).toFDRepIso⟩
    have hπARep_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (πARep i).ρ) := by
      simpa [πARep] using hπA_complete
    let eA0 := centerBaseChangeAlgEquivCyclotomicCenter (G := G) (K := K)
    let eA1 := splitCentralCharacterFamilyAlgEquivOfComplete
      (G := G) (K := K) πARep hπARep_pairwise hπARep_complete
    let eAFun : TensorProduct ℚ K A ≃ₐ[K] (κA → K) := eA0.trans eA1
    let eAIndex : κA ≃ (A →ₐ[ℚ] K) := pointsEquivOfBaseChangeAlgEquiv (K := K) eAFun
    letI : Finite (A →ₐ[ℚ] K) := Finite.of_equiv κA eAIndex
    let eA : TensorProduct ℚ K A ≃ₐ[K] ((A →ₐ[ℚ] K) → K) :=
      eAFun.trans (AlgEquiv.piCongrLeft' K (fun _ : κA ↦ K) eAIndex)
    have hInclA : ∀ (φ : A →ₐ[ℚ] K) (a : A),
        eA (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a) φ =
          φ a := by
      intro φ a
      change
        (AlgEquiv.piCongrLeft' K (fun _ : κA ↦ K) eAIndex
          (eAFun (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a)))
            φ = φ a
      rw [show
        (AlgEquiv.piCongrLeft' K (fun _ : κA ↦ K) eAIndex
          (eAFun (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a)))
            φ =
          eAFun (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := A) a)
            (eAIndex.symm φ) by simp [AlgEquiv.piCongrLeft']]
      rw [Algebra.TensorProduct.includeRight_apply]
      rw [← pointsEquivOfBaseChangeAlgEquiv_apply (K := K) eAFun (eAIndex.symm φ) a]
      simp [eAIndex]
    obtain ⟨κB, hκB, πB, hπB_pairwise, hπB_complete⟩ :=
      exists_complete_pairwise_nonisomorphic_simple_family_local (K := K) (G := G)
    letI : Fintype κB := hκB
    let eB0 := rationalCharacterRingBaseChangeAlgEquivSelfSubalgebra
      (G := G) (K := K) πB hπB_pairwise hπB_complete
    let eB1 := characterRingOverFieldAlgebraScalarExtensionSubalgebra_self_algEquiv_conjClasses
      (G := G) (K := K)
    let eBFun : TensorProduct ℚ K B ≃ₐ[K] (ConjClasses G → K) := eB0.trans eB1
    let eBIndex : ConjClasses G ≃ (B →ₐ[ℚ] K) :=
      pointsEquivOfBaseChangeAlgEquiv (K := K) eBFun
    letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
    letI : Finite (B →ₐ[ℚ] K) := Finite.of_equiv (ConjClasses G) eBIndex
    let eB : TensorProduct ℚ K B ≃ₐ[K] ((B →ₐ[ℚ] K) → K) :=
      eBFun.trans (AlgEquiv.piCongrLeft' K (fun _ : ConjClasses G ↦ K) eBIndex)
    have hInclB : ∀ (ψ : B →ₐ[ℚ] K) (b : B),
        eB (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B) b) ψ =
          ψ b := by
      intro ψ b
      change
        (AlgEquiv.piCongrLeft' K (fun _ : ConjClasses G ↦ K) eBIndex
          (eBFun (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B) b)))
            ψ = ψ b
      rw [show
        (AlgEquiv.piCongrLeft' K (fun _ : ConjClasses G ↦ K) eBIndex
          (eBFun (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B) b)))
            ψ =
          eBFun (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := B) b)
            (eBIndex.symm ψ) by simp [AlgEquiv.piCongrLeft']]
      rw [Algebra.TensorProduct.includeRight_apply]
      rw [← pointsEquivOfBaseChangeAlgEquiv_apply (K := K) eBFun (eBIndex.symm ψ) b]
      simp [eBIndex]
    let eCoord : ((A →ₐ[ℚ] K) → K) ≃ₐ[K] ((B →ₐ[ℚ] K) → K) :=
      AlgEquiv.piCongrLeft' K (fun _ : (A →ₐ[ℚ] K) ↦ K) ePts
    let eBC : TensorProduct ℚ K A ≃ₐ[K] TensorProduct ℚ K B :=
      eA.trans (eCoord.trans eB.symm)
    have heBC : ∀ (σ : Gal(K / ℚ)) (x : TensorProduct ℚ K A),
        tensorGaloisAlgHom (K := K) (C := B) σ (eBC x) =
          eBC (tensorGaloisAlgHom (K := K) (C := A) σ x) := by
      simpa [eCoord, eBC] using
        baseChangeAlgEquiv_reindex_algHomPoints_equivariant
          (G := G) (K := K) (A := A) (B := B) eA eB hInclA hInclB ePts hePts
    exact ⟨algEquivOfEquivariantBaseChange (K := K) (A := A) (B := B) eBC heBC⟩
  · intro hE
    rcases hX with ⟨eX⟩
    rcases hY with ⟨eY⟩
    rcases hE with ⟨e⟩
    rcases algHom_action_isomorphic_of_algEquiv (G := G) (K := K) e with ⟨eAB⟩
    exact ⟨eX.trans (eAB.trans eY.symm)⟩

end PartB

/-- Helper for Exercise 13-13.1-16: if `G` is a finite `p`-group with `p ≠ 2`, then the rational
power automorphism group `Γ_ℚ(G)` is cyclic. -/
theorem gammaRat_isCyclic_of_isPGroup_and_prime_ne_two
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) (hp2 : p ≠ 2) :
    IsCyclic (Γ_ℚ(G)) := by
  rcases (IsPGroup.iff_card (p := p) (G := G)).1 hG with ⟨n, hn⟩
  by_cases hexp1 : Monoid.exponent G = 1
  · rw [hexp1]
    simpa using ZMod.isCyclic_units_one
  · have hdiv : Monoid.exponent G ∣ p ^ n := by
      have hcard : Fintype.card G = p ^ n := by
        simpa [Nat.card_eq_fintype_card] using hn
      simpa [hcard] using (Group.exponent_dvd_nat_card (G := G))
    obtain ⟨k, _, hkexp⟩ := (Nat.dvd_prime_pow Fact.out).1 hdiv
    rw [hkexp]
    simpa using ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 k

/-- Helper for Exercise 13-13.1-16: rational power exponents multiply modulo the group
exponent. -/
private theorem gammaRatExponent_mul_modEq
    (t u : Γ_ℚ(G)) :
    galoisPowerExponentUnit (t * u) ≡
      galoisPowerExponentUnit t * galoisPowerExponentUnit u [MOD Monoid.exponent G] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp [galoisPowerExponentUnit, Nat.cast_mul]

/-- Helper for Exercise 13-13.1-16: a unit-valued character has exponent dividing the group
exponent. -/
private theorem dualCharacter_value_pow_exponent
    (χ : G →* Kˣ) (g : G) :
    (χ g) ^ Monoid.exponent G = 1 := by
  rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]

/-- Helper for Exercise 13-13.1-16: the rational Galois group acts on the character group by
powering values. -/
@[reducible]
private noncomputable def dualCharacterGammaMulAction :
    MulAction (Γ_ℚ(G)) (G →* Kˣ) where
  smul t χ := χ ^ galoisPowerExponentUnit t
  one_smul := by
    intro χ
    ext g
    have hmod :
        galoisPowerExponentUnit (1 : Γ_ℚ(G)) ≡ 1 [MOD Monoid.exponent G] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simp [galoisPowerExponentUnit]
    -- First compare powers modulo the exponent, then remove the final `^ 1`.
    have hunit_pow :
        (χ g) ^ galoisPowerExponentUnit (1 : Γ_ℚ(G)) = (χ g) ^ 1 :=
      pow_eq_pow_of_modEq hmod
        (dualCharacter_value_pow_exponent (G := G) (K := K) χ g)
    have hunit : (χ g) ^ galoisPowerExponentUnit (1 : Γ_ℚ(G)) = χ g := by
      simpa using hunit_pow
    simpa [MonoidHom.pow_apply] using congrArg (fun z : Kˣ ↦ (z : K)) hunit
  mul_smul := by
    intro t u χ
    ext g
    have hpow := dualCharacter_value_pow_exponent (G := G) (K := K) χ g
    have hunit :
        (χ g) ^ galoisPowerExponentUnit (t * u) =
          ((χ g) ^ galoisPowerExponentUnit u) ^ galoisPowerExponentUnit t := by
      calc
        (χ g) ^ galoisPowerExponentUnit (t * u)
            = (χ g) ^ (galoisPowerExponentUnit t * galoisPowerExponentUnit u) := by
                exact pow_eq_pow_of_modEq (gammaRatExponent_mul_modEq (G := G) t u) hpow
        _ = (χ g) ^ (galoisPowerExponentUnit u * galoisPowerExponentUnit t) := by
                rw [Nat.mul_comm]
        _ = ((χ g) ^ galoisPowerExponentUnit u) ^ galoisPowerExponentUnit t := by
                rw [pow_mul]
    simpa [MonoidHom.pow_apply] using congrArg (fun z : Kˣ ↦ (z : K)) hunit

/-- Helper for Exercise 13-13.1-16: one-dimensional representations are irreducible. -/
private theorem oneDimensionalRepresentation_isIrreducible
    {H : Type u} [Group H] (χ : H →* Kˣ) :
    (oneDimensionalRepresentation χ).IsIrreducible := by
  have hfinrank : Module.finrank K K = 1 := by
    simp
  letI : Nontrivial (Subrepresentation (oneDimensionalRepresentation χ)) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule K K) :=
    (isSimpleModule_iff K K).1 ((isSimpleModule_iff_finrank_eq_one).2 hfinrank)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim
        (hσ (Subrepresentation.toSubmodule_injective (by simpa using hσbot)))
    · exact hσtop
  -- Equality of subrepresentations follows from equality of their underlying submodules.
  apply Subrepresentation.toSubmodule_injective
  rw [hσtop]
  ext x
  constructor
  · intro _
    change x ∈ (⊤ : Subrepresentation (oneDimensionalRepresentation χ))
    exact trivial
  · intro _
    exact Submodule.mem_top

/-- Helper for Exercise 13-13.1-16: every simple representation of a finite abelian group is
isomorphic to a one-dimensional character representation. -/
private theorem simple_commutative_representation_iso_oneDimensional
    [IsMulCommutative G] (S : FDRep K G) [Simple S] :
    ∃ χ : G →* Kˣ,
      Nonempty (Representation.Equiv S.ρ (oneDimensionalRepresentation χ)) := by
  classical
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := mul_comm }
  letI : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  have hposS : 0 < Module.finrank K S :=
    simple_fdRep_finrank_pos_split (G := G) (K := K) S
  letI : Nontrivial S := Module.nontrivial_of_finrank_pos hposS
  let u : G → Subalgebra.center K (K[G]) := fun g ↦
    ⟨MonoidAlgebra.of K G g, by
      rw [Subalgebra.mem_center_iff]
      intro z
      exact mul_comm _ _⟩
  have hu_one : u 1 = 1 := by
    apply Subtype.ext
    change MonoidAlgebra.of K G (1 : G) = (1 : K[G])
    rw [MonoidAlgebra.of_apply]
    exact (MonoidAlgebra.one_def (R := K) (M := G)).symm
  have hu_mul (g h : G) : u (g * h) = u g * u h := by
    apply Subtype.ext
    change MonoidAlgebra.of K G (g * h) =
      MonoidAlgebra.of K G g * MonoidAlgebra.of K G h
    simp
  have hasAlgebraHom_u (g : G) :
      Representation.asAlgebraHom S.ρ (u g : K[G]) = S.ρ g := by
    change Representation.asAlgebraHom S.ρ (MonoidAlgebra.of K G g) = S.ρ g
    simpa [MonoidAlgebra.of_apply] using
      Representation.asAlgebraHom_single S.ρ g (1 : K)
  have hscalar (g : G) :
      S.ρ g = splitCentralCharacter (G := G) (K := K) S (u g) • LinearMap.id := by
    exact (hasAlgebraHom_u g).symm.trans
      (asAlgebraHom_center_eq_splitCentralCharacter_smul_id (G := G) (K := K) S (u g))
  have hscalar_ne_zero (g : G) :
      splitCentralCharacter (G := G) (K := K) S (u g) ≠ 0 := by
    -- A zero scalar would make the invertible operator `S.ρ g` vanish.
    intro hzero
    have hzeroMap : S.ρ g = 0 := by
      rw [hscalar g, hzero]
      simp
    have hmul : S.ρ g * S.ρ g⁻¹ = (1 : S →ₗ[K] S) := by
      simpa using (S.ρ.map_mul g g⁻¹).symm
    have hidzero : (1 : S →ₗ[K] S) = 0 := by
      calc
        (1 : S →ₗ[K] S) = S.ρ g * S.ρ g⁻¹ := hmul.symm
        _ = 0 := by
          rw [hzeroMap]
          simp
    exact one_ne_zero hidzero
  let χ : G →* Kˣ :=
    { toFun := fun g ↦
        Units.mk0 (splitCentralCharacter (G := G) (K := K) S (u g))
          (hscalar_ne_zero g)
      map_one' := by
        ext
        change splitCentralCharacter (G := G) (K := K) S (u 1) = 1
        simpa [hu_one] using
          map_one (splitCentralCharacter (G := G) (K := K) S)
      map_mul' := by
        intro g h
        ext
        change
          splitCentralCharacter (G := G) (K := K) S (u (g * h)) =
            splitCentralCharacter (G := G) (K := K) S (u g) *
              splitCentralCharacter (G := G) (K := K) S (u h)
        simpa [hu_mul g h] using
          map_mul (splitCentralCharacter (G := G) (K := K) S) (u g) (u h) }
  obtain ⟨x, hx⟩ := exists_ne (0 : S)
  have hscalar_apply (g : G) : S.ρ g x = ((χ g : Kˣ) : K) • x := by
    change S.ρ g x = splitCentralCharacter (G := G) (K := K) S (u g) • x
    rw [hscalar g]
    rfl
  let W : Subrepresentation S.ρ :=
    { toSubmodule := K ∙ x
      apply_mem_toSubmodule := by
        intro g y hy
        rcases Submodule.mem_span_singleton.mp hy with ⟨a, rfl⟩
        rw [map_smul, hscalar_apply g, smul_smul]
        exact Submodule.mem_span_singleton.mpr ⟨a * ((χ g : Kˣ) : K), rfl⟩ }
  have hW_ne_bot : W ≠ ⊥ := by
    intro hWbot
    have hxW : x ∈ W.toSubmodule := Submodule.mem_span_singleton_self x
    have hxbot : x ∈ (⊥ : Subrepresentation S.ρ).toSubmodule := by
      simpa [hWbot] using hxW
    have hxzero : x = 0 := by
      simpa using hxbot
    exact hx hxzero
  have hW_top : W = ⊤ := by
    rcases eq_bot_or_eq_top W with hbot | htop
    · exact False.elim (hW_ne_bot hbot)
    · exact htop
  have hspan_top : K ∙ x = ⊤ := by
    have hsub : K ∙ x = (⊤ : Subrepresentation S.ρ).toSubmodule := by
      simpa [W] using congrArg Subrepresentation.toSubmodule hW_top
    ext y
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      have hytop : y ∈ (⊤ : Subrepresentation S.ρ).toSubmodule := by
        change y ∈ (⊤ : Subrepresentation S.ρ)
        exact trivial
      simpa [hsub] using hytop
  have hdimS : Module.finrank K S = 1 := by
    calc
      Module.finrank K S = Module.finrank K (⊤ : Submodule K S) := (finrank_top K S).symm
      _ = Module.finrank K (K ∙ x) := by rw [hspan_top]
      _ = 1 := finrank_span_singleton hx
  let e : S ≃ₗ[K] K := LinearEquiv.ofFinrankEq S K (by simpa using hdimS)
  refine ⟨χ, ?_⟩
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro h
  ext x
  change e (S.ρ h x) = (oneDimensionalRepresentation χ h) (e x)
  calc
    e (S.ρ h x) = e (((χ h : Kˣ) : K) • x) := by
      rw [hscalar h]
      rfl
    _ = ((χ h : Kˣ) : K) • e x := by
      rw [map_smul]
    _ = (oneDimensionalRepresentation χ h) (e x) := by
      change ((χ h : Kˣ) : K) * e x = ((χ h : Kˣ) : K) * e x
      rfl

/-- Helper for Exercise 13-13.1-16: distinct unit-valued characters give nonisomorphic
one-dimensional representations. -/
private theorem oneDimensionalCharacter_pairwiseNonisomorphic :
    PairwiseNonisomorphic
      (fun χ : G →* Kˣ ↦ Rep.of (oneDimensionalRepresentation χ)) := by
  intro χ ψ hχψ hIso
  apply hχψ
  ext g
  rcases hIso with ⟨e⟩
  have hchar := Representation.char_iso (Representation.equivOfIso e)
  simpa [oneDimensionalRepresentation_character_apply] using congrFun hchar g

/-- Helper for Exercise 13-13.1-16: over a finite abelian group, the one-dimensional characters
form a complete irreducible family. -/
private theorem oneDimensionalCharacter_complete_of_isMulCommutative
    [IsMulCommutative G] :
    IsCompleteIrreducibleFamily
      (fun χ : G →* Kˣ ↦ FDRep.of (oneDimensionalRepresentation χ)) where
  isSimple χ := by
    letI : Representation.IsIrreducible (FDRep.of (oneDimensionalRepresentation χ)).ρ := by
      change (oneDimensionalRepresentation χ).IsIrreducible
      exact oneDimensionalRepresentation_isIrreducible (H := G) (K := K) χ
    exact FDRep.simple_of_isIrreducible (FDRep.of (oneDimensionalRepresentation χ))
  exists_iso S hS := by
    letI : Simple S := hS
    rcases simple_commutative_representation_iso_oneDimensional
        (G := G) (K := K) S with ⟨χ, ⟨e⟩⟩
    exact ⟨χ, ⟨e.toFDRepIso⟩⟩

/-- Helper for Exercise 13-13.1-16: the one-dimensional character family is compatible with
cyclotomic Galois conjugation. -/
private theorem oneDimensionalCharacter_galoisCompatible :
    letI : MulAction (Γ_ℚ(G)) (G →* Kˣ) :=
      dualCharacterGammaMulAction (G := G) (K := K)
    IrreducibleCharacterIndexGaloisCompatible
      (fun χ : G →* Kˣ ↦ Rep.of (oneDimensionalRepresentation χ)) := by
  classical
  letI : MulAction (Γ_ℚ(G)) (G →* Kˣ) :=
    dualCharacterGammaMulAction (G := G) (K := K)
  intro t χ g
  let σ : K ≃ₐ[ℚ] K := (galEquivZMod (Monoid.exponent G) K).symm t
  have hpow_units : (χ g) ^ Monoid.exponent G = 1 :=
    dualCharacter_value_pow_exponent (G := G) (K := K) χ g
  have hpow : (((χ g : Kˣ) : K) ^ Monoid.exponent G) = 1 := by
    simpa using congrArg (fun z : Kˣ ↦ (z : K)) hpow_units
  have hσ :
      σ (((χ g : Kˣ) : K)) =
        (((χ g : Kˣ) : K) ^ galoisPowerExponentUnit t) := by
    have h :=
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
        (n := Monoid.exponent G) (K := K) σ (x := ((χ g : Kˣ) : K)) hpow
    have ht : galEquivZMod (Monoid.exponent G) K σ = t := by
      dsimp [σ]
      exact (galEquivZMod (Monoid.exponent G) K).apply_symm_apply t
    rw [ht] at h
    simpa [σ, galoisPowerExponentUnit] using h
  change
    (oneDimensionalRepresentation (t • χ)).character g =
      σ ((oneDimensionalRepresentation χ).character g)
  rw [oneDimensionalRepresentation_character_apply,
    oneDimensionalRepresentation_character_apply, hσ]
  change (((χ ^ galoisPowerExponentUnit t) g : Kˣ) : K) =
    (((χ g : Kˣ) : K) ^ galoisPowerExponentUnit t)
  have hunit :
      (χ ^ galoisPowerExponentUnit t) g = (χ g) ^ galoisPowerExponentUnit t := by
    simp [MonoidHom.pow_apply]
  have hunitK :
      (((χ ^ galoisPowerExponentUnit t) g : Kˣ) : K) =
        (((χ g) ^ galoisPowerExponentUnit t : Kˣ) : K) :=
    congrArg (fun z : Kˣ ↦ (z : K)) hunit
  exact hunitK.trans (Units.val_pow_eq_pow_val (χ g) (galoisPowerExponentUnit t))

/-- Helper for Exercise 13-13.1-16: in an abelian group, the quotient map to conjugacy classes is
injective. -/
private theorem conjClasses_mk_injective_of_isMulCommutative
    [IsMulCommutative G] :
    Function.Injective (ConjClasses.mk : G → ConjClasses G) := by
  intro x y hxy
  exact (isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hxy))

/-- Helper for Exercise 13-13.1-16: in an abelian group, elements and conjugacy classes are
canonically equivalent. -/
private theorem conjClasses_mk_bijective_of_isMulCommutative
    [IsMulCommutative G] :
    Function.Bijective (ConjClasses.mk : G → ConjClasses G) := by
  exact ⟨conjClasses_mk_injective_of_isMulCommutative (G := G), ConjClasses.mk_surjective⟩

/-- Helper for Exercise 13-13.1-16: in an abelian group, `G` is equivalent to its conjugacy
classes. -/
private noncomputable def conjClassesEquivOfIsMulCommutative
    [IsMulCommutative G] :
    G ≃ ConjClasses G := by
  exact
    Equiv.ofBijective (ConjClasses.mk : G → ConjClasses G)
      (conjClasses_mk_bijective_of_isMulCommutative (G := G))

/-- Helper for Exercise 13-13.1-16: finite abelian duality identifies linear characters with
conjugacy classes as rational-power `Γ_ℚ`-sets. -/
private theorem dualCharacters_isomorphic_conjClasses_of_isMulCommutative
    [IsMulCommutative G] :
    letI : MulAction (Γ_ℚ(G)) (G →* Kˣ) :=
      dualCharacterGammaMulAction (G := G) (K := K)
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) (G →* Kˣ))
      (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G)) := by
  classical
  letI : MulAction (Γ_ℚ(G)) (G →* Kˣ) :=
    dualCharacterGammaMulAction (G := G) (K := K)
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    hasEnoughRootsOfUnity_of_cyclotomic (G := G) (K := K)
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := mul_comm }
  rcases CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G := G) (M := K) with
    ⟨eDual⟩
  let eConj := conjClassesEquivOfIsMulCommutative (G := G)
  let e : (G →* Kˣ) ≃ ConjClasses G := eDual.toEquiv.trans eConj
  refine action_ofMulAction_isomorphic_of_equivariant_equiv e ?_
  intro t χ
  let n := galoisPowerExponentUnit t
  have hmap : eDual (t • χ) = (eDual χ) ^ n := by
    change eDual (χ ^ n) = (eDual χ) ^ n
    exact map_pow eDual χ n
  calc
    e (t • χ) = ConjClasses.mk (eDual (t • χ)) := by
      rfl
    _ = ConjClasses.mk ((eDual χ) ^ n) := by
      rw [hmap]
    _ = t • e χ := by
      change
        ConjClasses.mk ((eDual χ) ^ n) =
          ConjClasses.pow n (ConjClasses.mk (eDual χ))
      rw [ConjClasses.pow_mk]

/-- Exercise 13-13.1-16 (5): source part `(c₁)`. If `G` is abelian, then the center of `ℚ[G]` is
isomorphic, as a `ℚ`-algebra, to the split cyclotomic character algebra `ℚ ⊗ R_K(G)`, realized
here as `characterRingOverFieldScalarExtensionSubalgebra K G`. -/
theorem center_groupAlgebra_algEquiv_rationalCharacterRing_of_isMulCommutative
    [IsMulCommutative G] :
    Nonempty
      (Subalgebra.center ℚ (ℚ[G]) ≃ₐ[ℚ]
        characterRingOverFieldScalarExtensionSubalgebra K G) := by
  classical
  letI : MulAction (Γ_ℚ(G)) (G →* Kˣ) :=
    dualCharacterGammaMulAction (G := G) (K := K)
  let π : (G →* Kˣ) → Rep K G :=
    fun χ ↦ Rep.of (oneDimensionalRepresentation χ)
  have hπ_pairwise : PairwiseNonisomorphic π :=
    oneDimensionalCharacter_pairwiseNonisomorphic (G := G) (K := K)
  have hπ_complete :
      IsCompleteIrreducibleFamily (fun χ ↦ FDRep.of (π χ).ρ) := by
    simpa [π] using
      oneDimensionalCharacter_complete_of_isMulCommutative (G := G) (K := K)
  have hπ_galois : IrreducibleCharacterIndexGaloisCompatible π := by
    simpa [π] using oneDimensionalCharacter_galoisCompatible (G := G) (K := K)
  have hIndexConj :
      IsIsomorphic
        (Action.ofMulAction (Γ_ℚ(G)) (G →* Kˣ))
        (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G)) :=
    dualCharacters_isomorphic_conjClasses_of_isMulCommutative (G := G) (K := K)
  have hX :=
    irreducible_character_index_isomorphic_center_algHom
      (G := G) (K := K) π hπ_pairwise hπ_complete hπ_galois
  have hY := conjClasses_isomorphic_rationalCharacterRing_algHom (G := G) (K := K)
  exact
    (irreducible_character_index_isomorphic_to_conjClasses_iff_center_algEquiv_rationalCharacterRing
      (G := G) (K := K) (ι := G →* Kˣ) hX hY).1 hIndexConj

/-- Exercise 13-13.1-16 (6): source part `(c₂)`. If `G` is a finite `p`-group with `p ≠ 2`, then
the center of `ℚ[G]` is isomorphic, as a `ℚ`-algebra, to the split cyclotomic character algebra
`ℚ ⊗ R_K(G)`, realized here as `characterRingOverFieldScalarExtensionSubalgebra K G`. -/
theorem center_groupAlgebra_algEquiv_rationalCharacterRing_of_isPGroup_and_prime_ne_two
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) (hp2 : p ≠ 2) :
    Nonempty
      (Subalgebra.center ℚ (ℚ[G]) ≃ₐ[ℚ]
        characterRingOverFieldScalarExtensionSubalgebra K G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨κ, hκ, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := K) (G := G)
  letI : Fintype κ := hκ
  let πRep : κ → Rep K G := fun i ↦ Rep.of (π i).ρ
  have hπRep_pairwise : PairwiseNonisomorphic πRep := by
    intro i j hij hij_iso
    apply hπ_pairwise hij
    rcases hij_iso with ⟨e⟩
    simpa [πRep] using ⟨(Representation.equivOfIso e).toFDRepIso⟩
  have hπRep_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (πRep i).ρ) := by
    simpa [πRep] using hπ_complete
  letI : MulAction (Γ_ℚ(G)) κ :=
    irreducibleCharacterIndexMulActionOfComplete
      (G := G) (K := K) πRep hπRep_pairwise hπRep_complete
  have hπRep_galois : IrreducibleCharacterIndexGaloisCompatible πRep :=
    irreducibleCharacterIndexGaloisCompatible_of_complete_pairwise
      (G := G) (K := K) πRep hπRep_pairwise hπRep_complete
  have hWeak :=
    irreducible_character_index_weaklyIsomorphic_conjClasses
      (G := G) (K := K) πRep hπRep_pairwise hπRep_complete hπRep_galois
  let X : Action FintypeCat (Γ_ℚ(G)) :=
    Action.FintypeCat.ofMulAction (Γ_ℚ(G)) (FintypeCat.of κ)
  let Y : Action FintypeCat (Γ_ℚ(G)) :=
    Action.FintypeCat.ofMulAction (Γ_ℚ(G)) (FintypeCat.of (ConjClasses G))
  have hCyclic : IsCyclic (Γ_ℚ(G)) :=
    gammaRat_isCyclic_of_isPGroup_and_prime_ne_two (G := G) p hG hp2
  letI : IsCyclic (Γ_ℚ(G)) := hCyclic
  have hIsoFinite : IsIsomorphic X Y := by
    exact (Action.isomorphic_iff_weaklyIsomorphic_of_isCyclic (X := X) (Y := Y)).2 hWeak
  have hIndexConj :
      IsIsomorphic
        (Action.ofMulAction (Γ_ℚ(G)) κ)
        (Action.ofMulAction (Γ_ℚ(G)) (ConjClasses G)) :=
    action_ofMulAction_isomorphic_of_fintypeCat_isomorphic
      (M := Γ_ℚ(G)) (α := κ) (β := ConjClasses G) hIsoFinite
  have hX :=
    irreducible_character_index_isomorphic_center_algHom
      (G := G) (K := K) πRep hπRep_pairwise hπRep_complete hπRep_galois
  have hY := conjClasses_isomorphic_rationalCharacterRing_algHom (G := G) (K := K)
  exact
    (irreducible_character_index_isomorphic_to_conjClasses_iff_center_algEquiv_rationalCharacterRing
      (G := G) (K := K) (ι := κ) hX hY).1 hIndexConj

end ExerciseClauses

end
