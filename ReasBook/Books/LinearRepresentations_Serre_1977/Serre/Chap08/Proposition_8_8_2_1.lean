import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1.Index
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1
import LinearRepresentations_Serre_1977.Chap08.Remark_8_8_1_2

open CategoryTheory
open scoped BigOperators Representation

universe w x

namespace Representation

noncomputable section

section SemidirectAbelian

variable {A : Type} [CommGroup A]
variable {H : Type} [Group H]
variable (φ : H →* MulAut A)

attribute [local instance] Fintype.ofFinite

/-!
Serre, Proposition 25 (Section 8.2).

The file records the source-facing parts of the little-groups construction already isolated in
`Proposition_8_8_2_1/*`.  The Mackey disjointness needed for part (a) lives in
`MackeyWeights`; this file exposes the transport from the induced model to `θ`.  Part (b) follows
the text by restricting a packet isomorphism to the distinguished `χ_i`-weight space.
-/

/-- Proposition 8-8.2-1(a), transport step: once Mackey's criterion has proved the explicit
induced subgroup model irreducible, the packet `θ[φ; χ, ρ]` is irreducible as well. -/
theorem theta_isIrreducible_of_induction_model [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ])
    (hInd :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible) :
    (Representation.theta φ χ ρ).ρ.IsIrreducible := by
  letI :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible :=
    hInd
  exact
    isIrreducible_of_nonempty_equiv
      (ρ := (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ)
      (σ := (Representation.theta φ χ ρ).ρ)
      ⟨(theta_equiv_ind_character_stabilizer_subgroup (φ := φ) χ ρ).symm⟩

/-- Helper for Proposition 8-8.2-1: a semidirect product of finite groups is finite. -/
private theorem semidirectProduct_finite [Finite A] [Finite H] :
    Finite (A ⋊[φ] H) := by
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype H := Fintype.ofFinite H
  let eprod : A ⋊[φ] H ≃ A × H :=
    { toFun := fun x ↦ (x.1, x.2)
      invFun := fun p ↦ ⟨p.1, p.2⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  letI : Fintype (A ⋊[φ] H) := Fintype.ofEquiv (A × H) eprod.symm
  exact inferInstance

/-- Helper for Proposition 8-8.2-1: the semidirect-product cardinal is nonzero in `ℂ`. -/
private theorem semidirect_product_card_ne_zero_complex [Finite A] [Finite H] :
    NeZero (Nat.card (A ⋊[φ] H) : ℂ) := by
  let _ : Finite (A ⋊[φ] H) := semidirectProduct_finite (φ := φ)
  exact ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- Helper for Proposition 8-8.2-1: the explicit packet source already satisfies the subgroup-side
inputs of Mackey's irreducibility criterion. -/
private theorem theta_reverse_mackey_hypothesis [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    Representation.IsIrreducible (theta_packet_source (φ := φ) χ ρ).ρ ∧
      (∀ s ∉ character_stabilizer_subgroup (φ := φ) χ,
        ∀ f :
          localMackeyTwist (φ := φ)
              (character_stabilizer_subgroup (φ := φ) χ)
              (character_stabilizer_subgroup (φ := φ) χ)
              (theta_packet_source (φ := φ) χ ρ) s ⟶
            Rep.res
              (localMackeySubgroup (φ := φ)
                (character_stabilizer_subgroup (φ := φ) χ)
                (character_stabilizer_subgroup (φ := φ) χ) s).subtype
              (theta_packet_source (φ := φ) χ ρ),
          f = 0) := by
  constructor
  · -- The explicit stabilizer-side model is already irreducible before induction.
    simpa [theta_packet_source] using
      character_stabilizer_subgroup_source_isIrreducible (φ := φ) χ ρ
  · intro s hs f
    -- Serre's source route kills off-subgroup intertwiners by the character mismatch on `A`.
    exact theta_local_mackey_disjoint (φ := φ) (χ := χ) (ρ := ρ) hs f

/-- Helper for Proposition 8-8.2-1: Mackey's criterion makes the explicit induced packet model
irreducible. -/
private theorem theta_packet_induction_model_isIrreducible [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (Rep.ind
      (character_stabilizer_subgroup (φ := φ) χ).subtype
      (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible := by
  let _ : Finite (A ⋊[φ] H) := semidirectProduct_finite (φ := φ)
  let _ : NeZero (Nat.card (A ⋊[φ] H) : ℂ) :=
    semidirect_product_card_ne_zero_complex (φ := φ)
  -- Feed the packet source irreducibility and the off-subgroup vanishing into Proposition 7-7.4-1.
  refine
    (ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
      (k := ℂ)
      (G := A ⋊[φ] H)
      (H := character_stabilizer_subgroup (φ := φ) χ)
      (ρ := (theta_packet_source (φ := φ) χ ρ).ρ)).2 ?_
  simpa [localMackeySubgroup, localMackeyTwist] using
    theta_reverse_mackey_hypothesis (φ := φ) χ ρ

/-- Proposition 8-8.2-1(a): Serre's packet `θ[φ; χ, ρ]` is irreducible. -/
theorem theta_isIrreducible [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (Representation.theta φ χ ρ).ρ.IsIrreducible := by
  -- Route correction: rather than searching for a later completeness theorem, we follow the
  -- source proof directly through Mackey's criterion on the stabilizer-side packet model.
  have hInd :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible :=
    theta_packet_induction_model_isIrreducible (φ := φ) χ ρ
  -- Transport irreducibility back across the canonical `θ ≃ Ind` comparison.
  exact theta_isIrreducible_of_induction_model (φ := φ) χ ρ hInd

/-- Proposition 8-8.2-1(b): an isomorphism between packets attached to orbit representatives
forces the representatives to be equal and identifies the stabilizer-side irreducible
representations. -/
theorem theta_iso_imp_eq_and_iso [Finite H]
    {ι : Type*} (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
    {i i' : ι}
    (ρ : Rep.{w} ℂ H_[φ; χ i]) (ρ' : Rep.{w} ℂ H_[φ; χ i'])
    [ρ.ρ.IsIrreducible] [ρ'.ρ.IsIrreducible]
    (e :
      Representation.theta φ (χ i) ρ ≅
        Representation.theta φ (χ i') ρ') :
    ∃ h : i = i', Nonempty (ρ ≅ h ▸ ρ') := by
  let eθ :
      (Representation.theta φ (χ i) ρ).ρ.Equiv
        (Representation.theta φ (χ i') ρ').ρ :=
    Representation.equivOfIso e
  let eWeight :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ.Equiv
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i') ρ') (χ i)).ρ :=
    character_weight_subrepresentation_equiv_of_equiv (φ := φ) eθ (χ i)
  have hsource_weight_irreducible :
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ).IsIrreducible := by
    -- The distinguished `χ_i`-weight space of the source packet recovers `ρ`.
    exact theta_character_weight_subrepresentation_isIrreducible (φ := φ) (χ i) ρ
  letI :
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ).IsIrreducible :=
    hsource_weight_irreducible
  letI :
      Nontrivial
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).V :=
    nontrivial_of_isIrreducible
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ)
  obtain ⟨x, hx⟩ := exists_ne
    (0 :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).V)
  let y :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i') ρ') (χ i)).V :=
    eWeight x
  have hy : y ≠ 0 := by
    intro hy
    exact hx <| eWeight.injective <| by simpa [y] using hy
  have htarget_weight_ne_bot :
      character_weight_submodule
        (φ := φ) (Representation.theta φ (χ i') ρ') (χ i) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨y.1, y.2, ?_⟩
    intro hy0
    exact hy <| Subtype.ext hy0
  let _ := characterMulAction φ
  rcases theta_weight_nonzero_imp_mem_orbit
      (φ := φ) (χ := χ i') (ρ := ρ') (ψ := χ i) htarget_weight_ne_bot with
    ⟨h, hh⟩
  have horbit :
      (Quotient.mk'' (χ i) : MulAction.orbitRel.Quotient H (A →* ℂˣ)) =
        Quotient.mk'' (χ i') := by
    apply Quotient.sound
    refine ⟨h, ?_⟩
    simpa [transportedCharacter] using hh
  have hii : i = i' := hχ.injective horbit
  subst hii
  let eWeight' :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ.Equiv
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i) ρ') (χ i)).ρ :=
    character_weight_subrepresentation_equiv_of_equiv (φ := φ)
      (Representation.equivOfIso e) (χ i)
  let eρ :
      ρ.ρ.Equiv ρ'.ρ :=
    (theta_character_weight_subrepresentation_equiv (φ := φ) (χ i) ρ).symm.trans
      (eWeight'.trans
        (theta_character_weight_subrepresentation_equiv (φ := φ) (χ i) ρ'))
  have hρ_iso : ρ ≅ ρ' := by
    exact Rep.mkIso eρ
  exact ⟨rfl, ⟨hρ_iso⟩⟩

/-- Helper for Proposition 8-8.2-1: the normal factor `A` is canonically identified with its
copy inside the semidirect product. -/
private def inl_range_equiv :
    A ≃* ((SemidirectProduct.inl (φ := φ) : A →* A ⋊[φ] H).range) :=
  { toFun := fun a ↦ ⟨SemidirectProduct.inl (φ := φ) a, ⟨a, rfl⟩⟩
    invFun := fun s ↦ s.1.left
    left_inv := by
      intro a
      rfl
    right_inv := by
      intro s
      rcases s.property with ⟨a, ha⟩
      apply Subtype.ext
      ext
      · simpa using congrArg SemidirectProduct.left ha
      · simpa using congrArg SemidirectProduct.right ha
    map_mul' := by
      intro a b
      apply Subtype.ext
      ext <;> simp }

/-- Helper for Proposition 8-8.2-1: `Representation.ofModule'` acts on a module through the
original owner scalar action. -/
private theorem ofModule'_asAlgebraHom_apply
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    [Module (MonoidAlgebra ℂ G') V'] [IsScalarTower ℂ (MonoidAlgebra ℂ G') V']
    (r : MonoidAlgebra ℂ G') (x : V') :
    ((Representation.ofModule' (k := ℂ) (G := G') V').asAlgebraHom r) x = r • x := by
  -- Compare the owner action coming from `ofModule'` with the original module structure.
  refine MonoidAlgebra.induction_on
    (p := fun r : MonoidAlgebra ℂ G' =>
      ((Representation.ofModule' (k := ℂ) (G := G') V').asAlgebraHom r) x = r • x) r ?_ ?_ ?_
  · intro a
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro r s hr hs
    simp [hr, hs, add_smul]
  · intro c s hs
    simp [hs]

/-- Helper for Proposition 8-8.2-1: a simple constituent of the restriction to the `inl(A)` copy
already lies in an ambient character weight space. -/
private theorem simple_submodule_of_inl_restriction_le_character_weight [Finite A] [Finite H]
    (τ : Rep.{x} ℂ (A ⋊[φ] H))
    (N : Submodule
      (MonoidAlgebra ℂ ((SemidirectProduct.inl (φ := φ) : A →* A ⋊[φ] H).range))
      (Rep.res ((SemidirectProduct.inl (φ := φ) : A →* A ⋊[φ] H).range).subtype τ).ρ.asModule)
    (hN : IsSimpleModule
      (MonoidAlgebra ℂ ((SemidirectProduct.inl (φ := φ) : A →* A ⋊[φ] H).range)) N) :
    ∃ ψ : A →* ℂˣ,
      N.restrictScalars ℂ ≤ character_weight_submodule (φ := φ) τ ψ := by
  let S : Subgroup (A ⋊[φ] H) :=
    (SemidirectProduct.inl (φ := φ) : A →* A ⋊[φ] H).range
  let eInl : A ≃* S := inl_range_equiv (φ := φ)
  have hNSimple : IsSimpleModule (MonoidAlgebra ℂ S) N := by
    simpa [S] using hN
  letI : IsSimpleModule (MonoidAlgebra ℂ S) N := hNSimple
  letI : CommGroup S :=
    Function.Injective.commGroup eInl.symm eInl.symm.injective
      (by simp)
      (by intro x y; simp)
      (by intro x; simp)
      (by intro x y; simp)
      (by intro x n; simp)
      (by intro x n; simp)
  let τS := Rep.res S.subtype τ
  letI : Finite S := Finite.of_equiv A eInl
  letI : Fintype S := Fintype.ofFinite S
  letI : Module (MonoidAlgebra ℂ S) ↑τ := τS.ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ (MonoidAlgebra ℂ S) ↑τ :=
    IsScalarTower.of_algebraMap_smul fun c x ↦ by
      change (τS.ρ.asAlgebraHom (MonoidAlgebra.single 1 c)) x = c • x
      simp [Representation.asAlgebraHom_single]
  let Nτ : Submodule (MonoidAlgebra ℂ S) ↑τ := N
  have hNτSimple : IsSimpleModule (MonoidAlgebra ℂ S) Nτ := by
    simpa [Nτ, S] using hN
  letI : IsSimpleModule (MonoidAlgebra ℂ S) Nτ := hNτSimple
  obtain ⟨ψS, hψS⟩ :=
    character_of_simple_owner_submodule (A := S) (V := ↑τ) Nτ
  let ψ : A →* ℂˣ := ψS.comp eInl.toMonoidHom
  refine ⟨ψ, ?_⟩
  intro x hx a
  let xN : Nτ := ⟨x, hx⟩
  have hx_char :
      (((Representation.ofModule' (k := ℂ) (G := S) Nτ) (eInl a)) xN : ↑τ) =
        (ψ a : ℂ) • xN := by
    -- The extracted simple character already controls the restricted `S`-action on `N`.
    have hx0 := LinearMap.congr_fun (hψS (eInl a)) xN
    simpa [ψ] using congrArg (fun y : Nτ ↦ (y : ↑τ)) hx0
  have hx_action :
      (((Representation.ofModule' (k := ℂ) (G := S) Nτ) (eInl a)) xN : ↑τ) =
        τ.ρ ⟨a, 1⟩ (xN : ↑τ) := by
    -- Reinterpret the same owner action as the ambient operator `τ.ρ ⟨a,1⟩`.
    have hx1 :
        ((Representation.ofModule' (k := ℂ) (G := S) Nτ).asAlgebraHom
          (MonoidAlgebra.single (eInl a) (1 : ℂ))) xN =
          (MonoidAlgebra.single (eInl a) (1 : ℂ)) • xN := by
      rw [ofModule'_asAlgebraHom_apply]
    have hx1' :
        (((Representation.ofModule' (k := ℂ) (G := S) Nτ) (eInl a)) xN : ↑τ) =
          (((MonoidAlgebra.single (eInl a) (1 : ℂ)) • xN : Nτ) : ↑τ) := by
      simpa [Representation.asAlgebraHom_single] using
        congrArg (fun y : Nτ ↦ (y : ↑τ)) hx1
    have hx2 :
        (((MonoidAlgebra.single (eInl a) (1 : ℂ)) • xN : Nτ) : ↑τ) =
          τ.ρ ⟨a, 1⟩ (xN : ↑τ) := by
      change (((MonoidAlgebra.single (eInl a) (1 : ℂ)) : MonoidAlgebra ℂ S) • (xN : ↑τ)) =
        τ.ρ ⟨a, 1⟩ (xN : ↑τ)
      change (τS.ρ.asAlgebraHom (MonoidAlgebra.single (eInl a) (1 : ℂ))) (xN : ↑τ) =
        τ.ρ ⟨a, 1⟩ (xN : ↑τ)
      simp [Representation.asAlgebraHom_single, τS, eInl, inl_range_equiv]
    exact hx1'.trans hx2
  exact hx_action.symm.trans hx_char

/-- Helper for Proposition 8-8.2-1: an irreducible ambient representation has some nonzero
`A`-character weight space. -/
private theorem exists_character_with_nonzero_character_weight [Finite A] [Finite H]
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) [τ.ρ.IsIrreducible] :
    ∃ ψ : A →* ℂˣ, character_weight_submodule (φ := φ) τ ψ ≠ ⊥ := by
  -- Route correction: isolate a simple constituent of the restriction to the `inl(A)` subgroup
  -- first, then identify that constituent with an ambient `A`-weight space.
  let S : Subgroup (A ⋊[φ] H) :=
    (SemidirectProduct.inl (φ := φ) : A →* A ⋊[φ] H).range
  let eInl : A ≃* S := inl_range_equiv (φ := φ)
  let τS := Rep.res S.subtype τ
  letI : Finite S := Finite.of_equiv A eInl
  letI : Fintype S := Fintype.ofFinite S
  letI : Module (MonoidAlgebra ℂ S) ↑τ := τS.ρ.instModuleMonoidAlgebraAsModule
  letI : NeZero (Nat.card S : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI : IsSemisimpleModule (MonoidAlgebra ℂ S) ↑τ := by infer_instance
  letI : Nontrivial ↑τ := nontrivial_of_isIrreducible τ.ρ
  have htop :
      (⊤ : Submodule (MonoidAlgebra ℂ S) ↑τ) ≠ ⊥ := by
    exact top_ne_bot
  -- Choose a nonzero simple owner constituent of the restriction to `inl(A)`.
  obtain ⟨N, -, hNsimple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (R := MonoidAlgebra ℂ S) (M := ↑τ)
      (⊤ : Submodule (MonoidAlgebra ℂ S) ↑τ)).resolve_left htop
  obtain ⟨ψ, hNle⟩ :=
    simple_submodule_of_inl_restriction_le_character_weight (φ := φ) τ N hNsimple
  have hN_ne_bot : N ≠ ⊥ := by
    letI : IsSimpleModule (MonoidAlgebra ℂ S) N := hNsimple
    exact
      Submodule.nontrivial_iff_ne_bot.mp
        (IsSimpleModule.nontrivial (MonoidAlgebra ℂ S) N)
  rcases (Submodule.ne_bot_iff _).mp hN_ne_bot with ⟨x, hx, hx0⟩
  -- A nonzero vector of the simple constituent stays nonzero in the ambient `ψ`-weight space.
  refine ⟨ψ, (Submodule.ne_bot_iff _).2 ?_⟩
  exact ⟨x, hNle hx, hx0⟩

/-- Helper for Proposition 8-8.2-1: move a nonzero ambient weight space to the chosen orbit
representative `χ i`. -/
private theorem exists_orbit_representative_with_nonzero_character_weight [Finite A] [Finite H]
    {ι : Type*} (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) [τ.ρ.IsIrreducible] :
    ∃ i : ι, character_weight_submodule (φ := φ) τ (χ i) ≠ ⊥ := by
  let _ := characterMulAction φ
  rcases exists_character_with_nonzero_character_weight (φ := φ) τ with ⟨ψ, hψ⟩
  obtain ⟨i, hi⟩ := hχ.surjective (Quotient.mk'' ψ)
  rcases Quotient.exact hi with ⟨h, hh⟩
  rcases (Submodule.ne_bot_iff _).mp hψ with ⟨x, hx, hx0⟩
  let e := character_weight_submodule_transport_equiv (φ := φ) τ ψ h
  let y :
      character_weight_submodule
        (φ := φ) τ (transportedCharacter (φ := φ) h ψ) :=
    e ⟨x, hx⟩
  have hy0 : ((y : _) : τ) ≠ 0 := by
    intro hy
    have hy' : y = 0 := by
      apply Subtype.ext
      exact hy
    have hx' : (⟨x, hx⟩ : character_weight_submodule (φ := φ) τ ψ) = 0 := by
      apply e.injective
      simpa [y] using hy'
    exact hx0 <| congrArg Subtype.val hx'
  have htransport : transportedCharacter (φ := φ) h ψ = χ i := by
    simpa [transportedCharacter] using hh
  -- Transport the nonzero `ψ`-weight vector to the chosen orbit representative.
  refine ⟨i, (Submodule.ne_bot_iff _).2 ?_⟩
  refine ⟨y.1, ?_, hy0⟩
  simpa [htransport] using y.2

/-- Helper for Proposition 8-8.2-1: the owner action on the intrinsic module of
`Subrepresentation.ofSubmodule' N` agrees with the original owner action on `N`. -/
private theorem subrepresentation_ofSubmodule'_asAlgebraHom_apply
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G' V') (N : Submodule (MonoidAlgebra ℂ G') ρ.asModule)
    (r : MonoidAlgebra ℂ G') (x : N) :
    (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
  -- Compare the intrinsic and ambient owner actions on the same subtype carrier.
  apply Subtype.ext
  induction r using MonoidAlgebra.induction_linear with
  | zero =>
      rfl
  | add a b ha hb =>
      rw [map_add, LinearMap.add_apply, Submodule.coe_add, add_smul, Submodule.coe_add, ha, hb]
      rfl
  | single g a =>
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Proposition 8-8.2-1: a simple owner submodule yields an irreducible bundled
subrepresentation. -/
private theorem irreducible_of_simple_owner_submodule
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G' V') (N : Submodule (MonoidAlgebra ℂ G') ρ.asModule)
    (hN : IsSimpleModule (MonoidAlgebra ℂ G') N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  let ρN : Representation ℂ G' N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra ℂ G') ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  let e :
      ((Subrepresentation.ofSubmodule' N).toRepresentation).asModule ≃ₗ[MonoidAlgebra ℂ G'] N :=
    { toFun := fun x ↦ ρN.asModuleEquiv x
      invFun := fun x ↦ ρN.asModuleEquiv.symm x
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro r x
        calc
          ρN.asModuleEquiv (r • x) = (ρN.asAlgebraHom r) (ρN.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρN) r x
          _ = r • ρN.asModuleEquiv x := by
            exact subrepresentation_ofSubmodule'_asAlgebraHom_apply ρ N r (ρN.asModuleEquiv x) }
  -- Transport simplicity across the intrinsic-module identification of `ofSubmodule'`.
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (MonoidAlgebra ℂ G') inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module e hN)

/-- Helper for Proposition 8-8.2-1: a nonzero distinguished weight space contains an irreducible
stabilizer subrepresentation. -/
private theorem exists_irreducible_subrepresentation_of_nonzero_character_weight
    [Finite A] [Finite H]
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ)
    (hψ : character_weight_submodule (φ := φ) τ ψ ≠ ⊥) :
    ∃ U : Subrepresentation (character_weight_subrepresentation (φ := φ) τ ψ).ρ,
      U.toSubmodule ≠ ⊥ ∧ U.toRepresentation.IsIrreducible := by
  let τψ := character_weight_subrepresentation (φ := φ) τ ψ
  let ρψ := (character_weight_subrepresentation (φ := φ) τ ψ).ρ
  letI : NeZero (Nat.card H_[φ; ψ] : ℂ) := by
    exact ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  letI : Module (MonoidAlgebra ℂ H_[φ; ψ]) τψ :=
    ρψ.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra ℂ H_[φ; ψ]) τψ := by
    infer_instance
  have htop :
      (⊤ : Submodule (MonoidAlgebra ℂ H_[φ; ψ]) τψ) ≠ ⊥ := by
    letI : Nontrivial τψ := by
      change Nontrivial (character_weight_submodule (φ := φ) τ ψ)
      exact Submodule.nontrivial_iff_ne_bot.mpr hψ
    exact top_ne_bot
  -- Choose a simple owner submodule of the nonzero `ψ`-weight space.
  obtain ⟨N, -, hNsimple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (R := MonoidAlgebra ℂ H_[φ; ψ]) (M := τψ)
      (⊤ : Submodule (MonoidAlgebra ℂ H_[φ; ψ]) τψ)).resolve_left htop
  let N' : Submodule (MonoidAlgebra ℂ H_[φ; ψ]) ρψ.asModule :=
    N.restrictScalars (MonoidAlgebra ℂ H_[φ; ψ])
  have hNsimple' : IsSimpleModule (MonoidAlgebra ℂ H_[φ; ψ]) N' := by
    simpa [N'] using hNsimple
  let U : Subrepresentation ρψ := Subrepresentation.ofSubmodule' N'
  refine ⟨U, ?_, ?_⟩
  · -- Forgetting the owner structure keeps the chosen constituent nonzero.
    intro hU
    have hN'_ne_bot : N' ≠ ⊥ := by
      letI : IsSimpleModule (MonoidAlgebra ℂ H_[φ; ψ]) N' := hNsimple'
      exact
        Submodule.nontrivial_iff_ne_bot.mp
          (IsSimpleModule.nontrivial (MonoidAlgebra ℂ H_[φ; ψ]) N')
    apply hN'_ne_bot
    ext v
    have hU' :
        (Subrepresentation.ofSubmodule' N').toSubmodule =
          (⊥ : Submodule ℂ τψ) := by
      simpa [U] using hU
    simpa [N'] using congrArg (fun S : Submodule ℂ τψ ↦ v ∈ S) hU'
  · -- The simple owner submodule becomes an irreducible stabilizer representation.
    exact irreducible_of_simple_owner_submodule ρψ N' hNsimple'

/-- Helper for Proposition 8-8.2-1: a nonzero constituent of the distinguished weight space gives
exactly the subgroup morphism needed for Frobenius reciprocity. -/
private theorem theta_packet_source_hom_of_character_weight_constituent_ne_zero
    [Finite A] [Finite H]
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) (ψ : A →* ℂˣ)
    (U : Subrepresentation (character_weight_subrepresentation (φ := φ) τ ψ).ρ)
    (hU : U.toSubmodule ≠ ⊥) :
    ∃ f : theta_packet_source (φ := φ) ψ (Rep.of U.toRepresentation) ⟶
      Rep.res (character_stabilizer_subgroup (φ := φ) ψ).subtype τ,
      f ≠ 0 := by
  let f₀ :=
    stabilizer_representation_hom_of_character_weight_constituent
      (φ := φ) (τ := τ) ψ U
  have hf₀ :
      f₀ ≠ 0 :=
    stabilizer_representation_hom_of_character_weight_constituent_ne_zero
      (φ := φ) (τ := τ) ψ U hU
  let f :
      theta_packet_source (φ := φ) ψ (Rep.of U.toRepresentation) ⟶
        Rep.res (character_stabilizer_subgroup (φ := φ) ψ).subtype τ :=
    Rep.ofHom <|
      LinearMap.intertwiningMap_of_isIntertwiningMap
        (theta_packet_source (φ := φ) ψ (Rep.of U.toRepresentation)).ρ
        (Rep.res (character_stabilizer_subgroup (φ := φ) ψ).subtype τ).ρ
        f₀.hom
        (by
          -- The subgroup-side intertwiner is unchanged; only the domain indexing is rewritten
          -- through `character_stabilizer_subgroup_equiv`.
          intro g x
          simpa [theta_packet_source, stabilizerInclusion_eq_subgroup_subtype_comp] using
            LinearMap.congr_fun
              (f₀.hom.2 ((character_stabilizer_subgroup_equiv (φ := φ) ψ).symm g)) x)
  refine ⟨f, ?_⟩
  intro hf
  apply hf₀
  ext x
  have hh : f.hom = 0 := by
    simpa using congrArg Rep.Hom.hom hf
  simpa [f₀, f] using congrArg (fun k ↦ k x) hh

/-- Proposition 8-8.2-1(c): every irreducible representation of `A ⋊[φ] H` is one of Serre's
little-groups packets. -/
theorem exists_iso_theta_of_isIrreducible [Finite A] [Finite H]
    {ι : Type*} (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
    (τ : Rep.{x} ℂ (A ⋊[φ] H)) [τ.ρ.IsIrreducible] :
    ∃ i, ∃ ρ : Rep.{x} ℂ H_[φ; χ i], ρ.ρ.IsIrreducible ∧ Nonempty (θ[φ; χ i, ρ] ≅ τ) := by
  -- Follow Serre's route literally: choose a nonzero `χ_i`-weight, take an irreducible
  -- stabilizer constituent there, and then invoke Frobenius reciprocity.
  rcases exists_orbit_representative_with_nonzero_character_weight
      (φ := φ) χ hχ τ with
    ⟨i, hweight⟩
  rcases exists_irreducible_subrepresentation_of_nonzero_character_weight
      (φ := φ) (τ := τ) (ψ := χ i) hweight with
    ⟨U, hU, hUirred⟩
  let ρ : Rep.{x} ℂ H_[φ; χ i] := Rep.of U.toRepresentation
  have hρirred : ρ.ρ.IsIrreducible := by
    simpa [ρ] using hUirred
  letI : ρ.ρ.IsIrreducible := hρirred
  rcases theta_packet_source_hom_of_character_weight_constituent_ne_zero
      (φ := φ) (τ := τ) (ψ := χ i) U hU with
    ⟨f, hf⟩
  let fInd :
      Rep.ind (character_stabilizer_subgroup (φ := φ) (χ i)).subtype
        (theta_packet_source (φ := φ) (χ i) (Rep.of U.toRepresentation)) ⟶ τ :=
    (Rep.indResHomEquiv
      (character_stabilizer_subgroup (φ := φ) (χ i)).subtype
      (theta_packet_source (φ := φ) (χ i) (Rep.of U.toRepresentation)) τ).symm f
  have hfInd : fInd ≠ 0 := by
    intro hzero
    let E :=
      Rep.indResHomEquiv
        (character_stabilizer_subgroup (φ := φ) (χ i)).subtype
        (theta_packet_source (φ := φ) (χ i) (Rep.of U.toRepresentation)) τ
    have hf_zero : f = 0 := by
      calc
        f = E (E.symm f) := by
              symm
              exact E.apply_symm_apply f
        _ = E fInd := by
              rfl
        _ = E 0 := by
              rw [hzero]
        _ = 0 := by
              simp
    exact hf hf_zero
  have eθ :
      (θ[φ; χ i, ρ]).ρ.Equiv
        (Rep.ind (character_stabilizer_subgroup (φ := φ) (χ i)).subtype
          (theta_packet_source (φ := φ) (χ i) (Rep.of U.toRepresentation))).ρ := by
    simpa [ρ] using theta_equiv_ind_character_stabilizer_subgroup (φ := φ) (χ i) ρ
  let isoθ :
      θ[φ; χ i, ρ] ≅
        Rep.ind (character_stabilizer_subgroup (φ := φ) (χ i)).subtype
          (theta_packet_source (φ := φ) (χ i) (Rep.of U.toRepresentation)) :=
    Rep.mkIso eθ
  let g : θ[φ; χ i, ρ] ⟶ τ := isoθ.hom ≫ fInd
  have hg : g ≠ 0 := by
    intro hzero
    apply hfInd
    have : isoθ.inv ≫ g = 0 := by
      simpa using congrArg (fun k ↦ isoθ.inv ≫ k) hzero
    simpa [g, Category.assoc] using this
  have hθirred : (θ[φ; χ i, ρ]).ρ.IsIrreducible :=
    theta_isIrreducible (φ := φ) (χ i) ρ
  letI : (θ[φ; χ i, ρ]).ρ.IsIrreducible := hθirred
  have hg_hom : g.hom ≠ 0 := by
    intro hg0
    exact hg (Rep.Hom.ext hg0)
  have hθτ :
      Nonempty ((θ[φ; χ i, ρ]).ρ.Equiv τ.ρ) := by
    -- A nonzero intertwiner between irreducibles is bijective by Schur's lemma.
    refine ⟨g.hom.ofBijective ?_⟩
    exact
      (Representation.IsIrreducible.bijective_or_eq_zero
        (ρ := (θ[φ; χ i, ρ]).ρ) (σ := τ.ρ) g.hom).resolve_right hg_hom
  exact ⟨i, ρ, hρirred, ⟨Rep.mkIso hθτ.some⟩⟩

end SemidirectAbelian

end

end Representation
