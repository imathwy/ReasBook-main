import Mathlib
import Serre.Chap14.Proposition_14_14_3_1
import Serre.Chap14.Exercise_14_14_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra
open Representation

universe u w x y

noncomputable section

section

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

local notation "ofModule" => @Representation.ofModule k G _ _

variable {k G}
variable {E : Type w} [AddCommGroup E] [Module k E] [Module k[G] E]
variable {P : Type x} [AddCommGroup P] [Module k[G] P]
variable {Q : Type y} [AddCommGroup Q] [Module k[G] Q]
/-- Helper for Exercise 14-14.5-5: reinterpret a `k[G]`-linear map as the `k`-linear map between
the owner modules underlying `Representation.ofModule`. -/
noncomputable def ofModule_linearMap_restrict
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    (f : M →ₗ[k[G]] N) :
    RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N :=
  { toFun := fun x =>
      (RestrictScalars.addEquiv k k[G] N).symm (f ((RestrictScalars.addEquiv k k[G] M) x))
    map_add' := by
      intro x y
      simp
    map_smul' := by
      intro a x
      -- Push the restricted scalar through the ambient `k[G]`-linearity of `f`.
      simp [RestrictScalars.smul_def, f.map_smul] }

/-- Helper for Exercise 14-14.5-5: a `k[G]`-linear equivalence yields an intertwining map between
the canonical owner representations attached to the two modules. -/
noncomputable def ofModule_intertwining_of_linearMap
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    (f : M →ₗ[k[G]] N) :
    (ofModule M).IntertwiningMap (ofModule N) := by
  refine ⟨ofModule_linearMap_restrict (k := k) (G := G) f, ?_⟩
  intro g
  ext x
  -- Evaluate the owner action through the `RestrictScalars` bridge and use `f`-equivariance.
  simp [ofModule_linearMap_restrict, Representation.ofModule,
    RestrictScalars.lsmul_apply_apply, f.map_smul]

/-- Helper for Exercise 14-14.5-5: dualizing the owner intertwining map attached to a
`k[G]`-linear map reverses its direction. -/
noncomputable def dual_intertwining_of_linearMap
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    (f : M →ₗ[k[G]] N) :
    (ofModule N).dual.IntertwiningMap (ofModule M).dual := by
  let u := ofModule_intertwining_of_linearMap (k := k) (G := G) f
  refine ⟨u.toLinearMap.dualMap, ?_⟩
  intro g
  ext φ x
  -- Apply the intertwining identity for `u` at `g⁻¹`, then evaluate the resulting equality.
  have hu :
      u (((ofModule M) g⁻¹) x) = ((ofModule N) g⁻¹) (u x) := by
    exact congrArg
      (fun T : RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N => T x)
      (u.isIntertwining' g⁻¹)
  change φ (((ofModule N) g⁻¹) (u x)) = φ (u (((ofModule M) g⁻¹) x))
  simpa using congrArg φ hu.symm

/-- Helper for Exercise 14-14.5-5: the owner-dual transpose of a `k[G]`-linear map, viewed as a
`k[G]`-linear map between the contragredient owner modules. -/
noncomputable def owner_dual_transpose
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    (f : M →ₗ[k[G]] N) :
    ((ofModule N).dual.asModule) →ₗ[k[G]] ((ofModule M).dual.asModule) :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    (ρ := (ofModule N).dual) (σ := (ofModule M).dual))
    (dual_intertwining_of_linearMap (k := k) (G := G) f)

/-- Helper for Exercise 14-14.5-5: a `k[G]`-linear equivalence yields an intertwining map between
the canonical owner representations attached to the two modules. -/
noncomputable def ofModule_intertwining_of_linearEquiv
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    (e : M ≃ₗ[k[G]] N) :
    (ofModule M).IntertwiningMap (ofModule N) := by
  exact ofModule_intertwining_of_linearMap (k := k) (G := G) e.toLinearMap

/-- Helper for Exercise 14-14.5-5: dualizing the owner intertwining map reverses its direction. -/
noncomputable def dual_intertwining_of_linearEquiv
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    (e : M ≃ₗ[k[G]] N) :
    (ofModule N).dual.IntertwiningMap (ofModule M).dual := by
  exact dual_intertwining_of_linearMap (k := k) (G := G) e.toLinearMap

/-- Helper for Exercise 14-14.5-5: a `k[G]`-linear equivalence transports to the contragredient
dual owner modules. -/
theorem dual_asModule_congr
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    (e : M ≃ₗ[k[G]] N) :
    Nonempty (((ofModule N).dual.asModule) ≃ₗ[k[G]] ((ofModule M).dual.asModule)) := by
  let φ :
      ((ofModule N).dual.asModule) →ₗ[k[G]] ((ofModule M).dual.asModule) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := (ofModule N).dual) (σ := (ofModule M).dual))
      (dual_intertwining_of_linearEquiv (k := k) (G := G) e)
  let ψ :
      ((ofModule M).dual.asModule) →ₗ[k[G]] ((ofModule N).dual.asModule) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := (ofModule M).dual) (σ := (ofModule N).dual))
      (dual_intertwining_of_linearEquiv (k := k) (G := G) e.symm)
  refine ⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩
  · ext f
    -- On the underlying duals, the two transposes are inverse because `e.symm` is inverse to `e`.
    apply (Representation.dual (ofModule M)).asModuleEquiv.injective
    ext x
    have hcore :
        ((ofModule_linearMap_restrict (k := k) (G := G) e.toLinearMap).dualMap
          ((ofModule_linearMap_restrict (k := k) (G := G) e.symm.toLinearMap).dualMap
            ((Representation.dual (ofModule M)).asModuleEquiv f))) x =
          ((Representation.dual (ofModule M)).asModuleEquiv f) x := by
      simp [ofModule_linearMap_restrict]
    simpa [φ, ψ, Representation.IntertwiningMap.equivLinearMapAsModule,
      Representation.asModuleEquiv] using hcore
  · ext f
    -- The same argument with `e` and `e.symm` swapped gives the reverse identity.
    apply (Representation.dual (ofModule N)).asModuleEquiv.injective
    ext x
    have hcore :
        ((ofModule_linearMap_restrict (k := k) (G := G) e.symm.toLinearMap).dualMap
          ((ofModule_linearMap_restrict (k := k) (G := G) e.toLinearMap).dualMap
            ((Representation.dual (ofModule N)).asModuleEquiv f))) x =
          ((Representation.dual (ofModule N)).asModuleEquiv f) x := by
      simp [ofModule_linearMap_restrict]
    simpa [φ, ψ, Representation.IntertwiningMap.equivLinearMapAsModule,
      Representation.asModuleEquiv] using hcore

/-- Helper for Exercise 14-14.5-5: forgetting the `k[G]`-owner on a dual vector space does not
change the underlying `k`-dual. -/
noncomputable def dual_restrictScalars_linearEquiv
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M] :
    Module.Dual k (RestrictScalars k k[G] M) ≃ₗ[k] Module.Dual k M := by
  refine
    { toFun := fun φ =>
        { toFun := fun x => φ ((RestrictScalars.addEquiv k k[G] M).symm x)
          map_add' := by
            intro x y
            simp
          map_smul' := by
            intro a x
            -- The restricted owner and the original module carry the same `k`-scalar action.
            have hs :
                ((RestrictScalars.addEquiv k k[G] M).symm (a • x) :
                    RestrictScalars k k[G] M) =
                  a • ((RestrictScalars.addEquiv k k[G] M).symm x) := by
              change a • x = (algebraMap k k[G] a) • x
              simpa using (algebraMap_smul k[G] a x).symm
            simp [hs] }
      invFun := fun φ =>
        { toFun := fun x => φ ((RestrictScalars.addEquiv k k[G] M) x)
          map_add' := by
            intro x y
            simp
          map_smul' := by
            intro a x
            -- The same identification also transports scalar multiplication back to the owner.
            have hs :
                (RestrictScalars.addEquiv k k[G] M) (a • x) =
                  a • (RestrictScalars.addEquiv k k[G] M) x := by
              change (algebraMap k k[G] a) • (RestrictScalars.addEquiv k k[G] M x) =
                  a • (RestrictScalars.addEquiv k k[G] M x)
              simpa using (algebraMap_smul k[G] a ((RestrictScalars.addEquiv k k[G] M) x))
            simp [hs] }
      left_inv := by
        intro φ
        ext x
        rfl
      right_inv := by
        intro φ
        ext x
        rfl
      map_add' := by
        intro φ ψ
        rfl
      map_smul' := by
        intro a φ
        rfl }

/-- Helper for Exercise 14-14.5-5: the source of a projective envelope of a simple module is
cyclic, hence finite over `k[G]`. -/
theorem projectiveEnvelope_simple_source_finite
    {S P : Type*} [AddCommGroup S] [AddCommGroup P] [Module k[G] S] [Module k[G] P]
    {f : P →ₗ[k[G]] S} (hS : IsSimpleModule k[G] S) (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : IsSimpleModule k[G] S := hS
  letI : Nontrivial S := IsSimpleModule.nontrivial (R := k[G]) (M := S)
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  obtain ⟨x, hx⟩ := hf.surjective s
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hs <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  -- Essentiality upgrades the cyclic submodule surjecting onto `S` to the whole source.
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1
        (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Exercise 14-14.5-5: finite generation over `k[G]` implies finite generation over
`k` after restricting scalars along `k → k[G]`. -/
theorem groupAlgebra_moduleFinite_restrictScalars
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (hM : Module.Finite k[G] M) :
    Module.Finite k M := by
  -- The group algebra is finite over `k`, so finite generation descends along the tower.
  letI : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  letI : Module.Finite k[G] M := hM
  exact Module.Finite.trans k[G] M

/-- Helper for Exercise 14-14.5-5: a proper subspace of the dual of a finite-dimensional vector
space annihilates a nonzero vector. -/
theorem exists_nonzero_vector_annihilated_by_proper_dual_submodule
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (N : Submodule k (Module.Dual k V)) (hN : N ≠ ⊤) :
    ∃ v : V, v ≠ 0 ∧ ∀ φ : Module.Dual k V, φ ∈ N → φ v = 0 := by
  have hcoann_ne_bot : N.dualCoannihilator ≠ ⊥ := by
    intro hcoann_bot
    haveI : FiniteDimensional k (Module.Dual k V) := by infer_instance
    haveI : FiniteDimensional k N := by infer_instance
    have htop : N = ⊤ := by
      calc
        N = N.dualCoannihilator.dualAnnihilator := by
          simpa using (Subspace.dualCoannihilator_dualAnnihilator_eq (W := N)).symm
        _ = (⊥ : Submodule k V).dualAnnihilator := by
          simp [hcoann_bot]
        _ = ⊤ := Submodule.dualAnnihilator_bot
    exact hN htop
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcoann_ne_bot
  refine ⟨v, hvne, ?_⟩
  -- Membership in the coannihilator says exactly that every functional in `N` vanishes on `v`.
  intro φ hφ
  rw [Submodule.mem_dualCoannihilator] at hvmem
  exact hvmem φ hφ

/-- Helper for Exercise 14-14.5-5: a proper `k[G]`-submodule of the owner dual of `P` remains
proper after transporting it to the plain `k`-dual, so it annihilates a nonzero vector of `P`. -/
theorem owner_dual_proper_submodule_annihilates_nonzero_vector
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P]
    [IsScalarTower k k[G] P] [FiniteDimensional k P]
    (N : Submodule k[G] ((ofModule P).dual.asModule)) (hN : N ≠ ⊤) :
    ∃ p : P, p ≠ 0 ∧
      ∀ ψ : ((ofModule P).dual.asModule), ψ ∈ N →
        (((Representation.dual (ofModule P)).asModuleEquiv.trans
          (dual_restrictScalars_linearEquiv (k := k) (G := G) (M := P))) ψ) p = 0 := by
  let e : ((ofModule P).dual.asModule) ≃ₗ[k] Module.Dual k P :=
    (Representation.dual (ofModule P)).asModuleEquiv.trans
      (dual_restrictScalars_linearEquiv (k := k) (G := G) (M := P))
  let N' : Submodule k (Module.Dual k P) :=
    (N.restrictScalars k).map (e : ((ofModule P).dual.asModule) →ₗ[k] Module.Dual k P)
  have hN' : N' ≠ ⊤ := by
    intro htop
    have htop' : N.restrictScalars k = ⊤ := by
      exact (Submodule.map_eq_top_iff (e := e)).1 htop
    have htop'' : N = ⊤ := by
      -- Equality of the restricted submodule already implies equality of the original owner.
      ext x
      change x ∈ N.restrictScalars k ↔ x ∈ (⊤ : Submodule k[G] ((ofModule P).dual.asModule))
      simp [htop']
    exact hN htop''
  obtain ⟨p, hp0, hp⟩ :=
    exists_nonzero_vector_annihilated_by_proper_dual_submodule (k := k) (V := P) N' hN'
  refine ⟨p, hp0, ?_⟩
  intro ψ hψ
  -- After transporting `ψ` into the plain dual, the annihilator statement is exactly `hp`.
  exact hp (e ψ) ⟨ψ, hψ, rfl⟩

/-- Helper for Exercise 14-14.5-5: the canonical owner-dual transport from the contragredient
module to the plain `k`-linear dual. -/
noncomputable def owner_dual_to_linearDual
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P] :
    ((ofModule P).dual.asModule) ≃ₗ[k] Module.Dual k P :=
  (Representation.dual (ofModule P)).asModuleEquiv.trans
    (dual_restrictScalars_linearEquiv (k := k) (G := G) (M := P))

/-- Helper for Exercise 14-14.5-5: the owner-dual transport rewrites the basis action on the dual
as evaluation after acting on the primal vector. -/
theorem owner_dual_to_linearDual_smul_apply
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P]
    (g : G) (ψ : ((ofModule P).dual.asModule)) (x : P) :
    (owner_dual_to_linearDual (k := k) (G := G) (P := P)
        ((MonoidAlgebra.of k G g⁻¹) • ψ)) x =
      (owner_dual_to_linearDual (k := k) (G := G) (P := P) ψ)
        ((MonoidAlgebra.of k G g) • x) := by
  -- Evaluate the owner action through `asModuleEquiv`, then identify the contragredient action
  -- with precomposition by the primal `g`-action.
  change
      (dual_restrictScalars_linearEquiv (k := k) (G := G) (M := P)
          ((Representation.dual (ofModule P)).asModuleEquiv
            ((MonoidAlgebra.of k G g⁻¹) • ψ))) x =
        (dual_restrictScalars_linearEquiv (k := k) (G := G) (M := P)
          ((Representation.dual (ofModule P)).asModuleEquiv ψ))
          ((MonoidAlgebra.of k G g) • x)
  change
      ((Representation.dual (ofModule P)).asModuleEquiv
          ((MonoidAlgebra.of k G g⁻¹) • ψ))
        ((RestrictScalars.addEquiv k k[G] P).symm x) =
      ((Representation.dual (ofModule P)).asModuleEquiv ψ)
        ((RestrictScalars.addEquiv k k[G] P).symm ((MonoidAlgebra.of k G g) • x))
  rw [Representation.asModuleEquiv_map_smul]
  rw [show MonoidAlgebra.of k G g⁻¹ = MonoidAlgebra.single g⁻¹ (1 : k) by rfl]
  rw [Representation.asAlgebraHom_single]
  simp only [one_smul]
  rw [Representation.dual_apply, Module.Dual.transpose_apply]
  simp [Representation.ofModule, RestrictScalars.lsmul_apply_apply]

/-- Helper for Exercise 14-14.5-5: if every functional in an owner-dual submodule vanishes at a
vector, then the same vanishing holds after any `k[G]`-action on that vector. -/
theorem owner_dual_vanishing_stable_under_groupAlgebra_action
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P]
    (N : Submodule k[G] ((ofModule P).dual.asModule)) {x : P}
    (hx : ∀ ψ : ((ofModule P).dual.asModule), ψ ∈ N →
      (owner_dual_to_linearDual (k := k) (G := G) (P := P) ψ) x = 0)
    (a : k[G]) :
    ∀ ψ : ((ofModule P).dual.asModule), ψ ∈ N →
      (owner_dual_to_linearDual (k := k) (G := G) (P := P) ψ) (a • x) = 0 := by
  -- Route correction: the old proof shape tried to jump straight to cyclic spans; first prove the
  -- pointwise invariance under the whole group algebra action.
  let hvanish : k[G] → Prop := fun a =>
    ∀ ψ : ((ofModule P).dual.asModule), ψ ∈ N →
      (owner_dual_to_linearDual (k := k) (G := G) (P := P) ψ) (a • x) = 0
  change hvanish a
  refine MonoidAlgebra.induction_on a ?_ ?_ ?_
  · intro g ψ hψ
    -- The basis case is exactly the owner-dual transport identity.
    rw [← owner_dual_to_linearDual_smul_apply (k := k) (G := G) (P := P) g ψ x]
    exact hx _ (N.smul_mem (MonoidAlgebra.of k G g⁻¹) hψ)
  · intro a b ha hb ψ hψ
    -- Additivity of the `k[G]`-action and of each transported functional preserves vanishing.
    rw [add_smul, LinearMap.map_add]
    simp [ha ψ hψ, hb ψ hψ]
  · intro r a ha ψ hψ
    -- Scalar multiples reduce to linearity of the transported functional.
    rw [smul_assoc, LinearMap.map_smul]
    simp [ha ψ hψ]

/-- Helper for Exercise 14-14.5-5: if an owner-dual submodule annihilates one vector, then it
annihilates the whole `k[G]`-cyclic span of that vector. -/
theorem owner_dual_vanishes_on_cyclic_span
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P]
    (N : Submodule k[G] ((ofModule P).dual.asModule)) {p x : P}
    (hp : ∀ ψ : ((ofModule P).dual.asModule), ψ ∈ N →
      (owner_dual_to_linearDual (k := k) (G := G) (P := P) ψ) p = 0)
    (hx : x ∈ Submodule.span k[G] ({p} : Set P)) :
    ∀ ψ : ((ofModule P).dual.asModule), ψ ∈ N →
      (owner_dual_to_linearDual (k := k) (G := G) (P := P) ψ) x = 0 := by
  -- Upgrade the pointwise vanishing at the generator to the whole cyclic span by span induction.
  refine
    Submodule.span_induction
      (s := ({p} : Set P))
      (p := fun x _ ↦
        ∀ ψ : ((ofModule P).dual.asModule), ψ ∈ N →
          (owner_dual_to_linearDual (k := k) (G := G) (P := P) ψ) x = 0)
      ?_ ?_ ?_ ?_ hx
  · intro y hy ψ hψ
    -- The generator case is the assumed annihilation at `p`.
    simp at hy
    simpa [hy] using hp ψ hψ
  · intro ψ hψ
    -- Every linear functional vanishes at the zero vector.
    simp
  · intro y z hy hz hy_zero hz_zero ψ hψ
    -- Additivity of the transported functional propagates the induction hypothesis.
    rw [LinearMap.map_add]
    simp [hy_zero ψ hψ, hz_zero ψ hψ]
  · intro a y hy hy_zero ψ hψ
    -- The span is stable under the group-algebra action, handled by the previous lemma.
    exact owner_dual_vanishing_stable_under_groupAlgebra_action
      (k := k) (G := G) (P := P) N
      (x := y) (hx := fun φ hφ ↦ hy_zero φ hφ) a ψ hψ

/-- Helper for Exercise 14-14.5-5: transporting the owner dual and then transposing is the same as
evaluating the transported functional after applying the original map. -/
theorem owner_dual_transpose_apply
    {S P : Type*} [AddCommGroup S] [AddCommGroup P]
    [Module k S] [Module k P] [Module k[G] S] [Module k[G] P]
    [IsScalarTower k k[G] S] [IsScalarTower k k[G] P]
    {i : S →ₗ[k[G]] P} (ψ : ((ofModule P).dual.asModule)) (s : S) :
    (owner_dual_to_linearDual (k := k) (G := G) (P := S) ((owner_dual_transpose (k := k) (G := G) i) ψ)) s =
      (owner_dual_to_linearDual (k := k) (G := G) (P := P) ψ) (i s) := by
  -- Unfold both owner-dual transports and evaluate the transpose pointwise.
  change
      (dual_restrictScalars_linearEquiv (k := k) (G := G) (M := S)
        ((Representation.dual (ofModule S)).asModuleEquiv
          ((owner_dual_transpose (k := k) (G := G) i) ψ))) s =
      (dual_restrictScalars_linearEquiv (k := k) (G := G) (M := P)
        ((Representation.dual (ofModule P)).asModuleEquiv ψ)) (i s)
  change
      ((Representation.dual (ofModule S)).asModuleEquiv
          ((owner_dual_transpose (k := k) (G := G) i) ψ))
          ((RestrictScalars.addEquiv k k[G] S).symm s) =
        ((Representation.dual (ofModule P)).asModuleEquiv ψ)
          ((RestrictScalars.addEquiv k k[G] P).symm (i s))
  rfl

/-- Helper for Exercise 14-14.5-5: in an injective envelope, the cyclic span of any nonzero vector
meets the image of the envelope nontrivially. -/
theorem span_singleton_inf_range_ne_bot_of_injectiveEnvelope
    {S P : Type*} [AddCommGroup S] [AddCommGroup P]
    [Module k S] [Module k P] [Module k[G] S] [Module k[G] P]
    [IsScalarTower k k[G] S] [IsScalarTower k k[G] P]
    {i : S →ₗ[k[G]] P} (hi : i.IsInjectiveEnvelope) {p : P} (hp : p ≠ 0) :
    (Submodule.span k[G] ({p} : Set P) ⊓ LinearMap.range i) ≠ ⊥ := by
  let C : Submodule k[G] P := Submodule.span k[G] ({p} : Set P)
  intro hbot
  have hCbot : C = ⊥ := hi.toIsEssentialExtension.eq_bot_of_inf_range_eq_bot C (by simpa [C] using hbot)
  have hp_mem : p ∈ C := by
    exact Submodule.mem_span_singleton_self p
  have hp_zero : p = 0 := by
    rw [hCbot] at hp_mem
    simpa using hp_mem
  exact hp hp_zero

/-- Helper for Exercise 14-14.5-5: a proper owner-dual submodule maps under the transpose into a
proper transported evaluation kernel on the simple source. -/
theorem transpose_simple_image_restrictScalars_le_owner_eval_ker_of_proper_submodule
    {S P : Type*} [AddCommGroup S] [AddCommGroup P]
    [Module k S] [Module k P] [Module k[G] S] [Module k[G] P]
    [IsScalarTower k k[G] S] [IsScalarTower k k[G] P]
    [FiniteDimensional k S] [FiniteDimensional k P] [IsSimpleModule k[G] S]
    {i : S →ₗ[k[G]] P} (hi : i.IsInjectiveEnvelope)
    (N : Submodule k[G] ((ofModule P).dual.asModule)) (hN : N ≠ ⊤) :
    ∃ s : S, s ≠ 0 ∧
      (N.map (owner_dual_transpose (k := k) (G := G) i)).restrictScalars k ≤
        Submodule.comap ((owner_dual_to_linearDual (k := k) (G := G) (P := S)).toLinearMap)
          (LinearMap.ker (Module.Dual.eval k S s)) := by
  obtain ⟨p, hp_ne, hp_annihilate⟩ :=
    owner_dual_proper_submodule_annihilates_nonzero_vector
      (k := k) (G := G) (P := P) N hN
  have hspan_ne_bot :
      (Submodule.span k[G] ({p} : Set P) ⊓ LinearMap.range i) ≠ ⊥ :=
    span_singleton_inf_range_ne_bot_of_injectiveEnvelope
      (k := k) (G := G) (i := i) hi hp_ne
  obtain ⟨y, hy_mem, hy_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hspan_ne_bot
  rcases hy_mem with ⟨hy_span, hy_range⟩
  rcases hy_range with ⟨s, hs_eq⟩
  have hs_ne : s ≠ 0 := by
    intro hs
    apply hy_ne
    simpa [hs] using hs_eq.symm
  refine ⟨s, hs_ne, ?_⟩
  intro ξ hξ
  have hξ' : ξ ∈ N.map (owner_dual_transpose (k := k) (G := G) i) := hξ
  change
      (owner_dual_to_linearDual (k := k) (G := G) (P := S) ξ) s = 0
  rcases hξ' with ⟨ψ, hψN, rfl⟩
  -- Rewrite transpose evaluation back on the owner dual of `P`, then use cyclic-span vanishing.
  rw [owner_dual_transpose_apply (k := k) (G := G) (i := i) ψ s, hs_eq]
  exact owner_dual_vanishes_on_cyclic_span
    (k := k) (G := G) (P := P) N hp_annihilate hy_span ψ hψN

/-- Helper for Exercise 14-14.5-5: a representation equivalence yields a `k[G]`-linear
equivalence between the corresponding owner modules. -/
noncomputable def asModuleLinearEquiv_of_equiv
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[k[G]] σ.asModule := by
  let f : ρ.asModule →ₗ[k[G]] σ.asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := ρ) (σ := σ)) e.toIntertwiningMap
  let g : σ.asModule →ₗ[k[G]] ρ.asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := σ) (σ := ρ)) e.symm.toIntertwiningMap
  refine LinearEquiv.ofLinear f g ?_ ?_
  · ext x
    -- Move the owner equality back to the underlying vector spaces, where `e` and `e.symm`
    -- cancel directly.
    apply σ.asModuleEquiv.injective
    change e (e.symm (σ.asModuleEquiv x)) = σ.asModuleEquiv x
    simp
  · ext x
    -- The reverse composite is the same cancellation argument on the source owner.
    apply ρ.asModuleEquiv.injective
    change e.symm (e (ρ.asModuleEquiv x)) = ρ.asModuleEquiv x
    simp

/-- Helper for Exercise 14-14.5-5: postcomposition by a target representation equivalence induces
an equivalence of internal-Hom representations. -/
noncomputable def linHom_postcompose_equiv
    {V W W' : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    {ρV : Representation k G V} {ρW : Representation k G W} {ρW' : Representation k G W'}
    (e : ρW.Equiv ρW') :
    (Representation.linHom ρV ρW).Equiv (Representation.linHom ρV ρW') := by
  refine Representation.Equiv.mk (LinearEquiv.congrRight e.toLinearEquiv) ?_
  intro g
  ext f x
  -- The internal-Hom action is conjugation, so postcomposition only needs the intertwining
  -- identity for the target equivalence `e`.
  change e ((ρW g) (f ((ρV g⁻¹) x))) = (ρW' g) (e (f ((ρV g⁻¹) x)))
  simpa using congrArg
    (fun T : W →ₗ[k] W' => T (f ((ρV g⁻¹) x)))
    (e.toIntertwiningMap.isIntertwining' g)

/-- Helper for Exercise 14-14.5-5: applying `ofModule` to the owner of the trivial representation
recovers that trivial representation up to the canonical equivalence from `Rep.unitIso`. -/
noncomputable def trivial_owner_rep_equiv :
    (Representation.ofModule ((Representation.trivial k G k).asModule)).Equiv
      (Representation.trivial k G k) := by
  let V : Rep k G := Rep.of (Representation.trivial k G k)
  exact Representation.equivOfIso (i := (Rep.unitIso V).symm)

/-- Helper for Exercise 14-14.5-5: after giving `k` the trivial `k[G]`-module structure, Exercise
`14-14.5-3` makes the frozen internal-Hom owner `Hom_k(P,k)` projective. -/
theorem linHom_to_frozen_trivial_owner_projective
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P]
    [Module k[G] k] [IsScalarTower k k[G] k]
    [FiniteDimensional k P] [Module.Projective k[G] P] :
    Module.Projective k[G]
      ((Representation.linHom (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) k)).asModule) := by
  -- This is exactly Exercise `14-14.5-3` with the trivial target owner frozen as the module `k`.
  simpa using
    (linHom_projective_of_projective_source
      (k := k) (G := G) (E := P) (F := k))

/-- Helper for Exercise 14-14.5-5: the same frozen projectivity statement can be rewritten using
the owner of the trivial representation as the target module. -/
theorem linHom_to_trivial_owner_frozen_alias_projective
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P]
    [FiniteDimensional k P] [Module.Projective k[G] P] :
    Module.Projective k[G]
      ((Representation.linHom (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) ((Representation.trivial k G k).asModule))).asModule) := by
  let _ : Module k[G] k := by
    change Module k[G] ((Representation.trivial k G k).asModule)
    infer_instance
  let _ : IsScalarTower k k[G] k := by
    change IsScalarTower k k[G] ((Representation.trivial k G k).asModule)
    infer_instance
  -- This is the frozen-source projectivity theorem rewritten along the definitional equality
  -- between `k` and the owner of the trivial representation.
  simpa using
    (linHom_to_frozen_trivial_owner_projective (k := k) (G := G) (P := P))

/-- Helper for Exercise 14-14.5-5: the owner dual is already the exact frozen internal-Hom owner
from Exercise `14-14.5-3`, so no further transport through the genuine trivial representation is
needed. -/
noncomputable def owner_dual_as_frozen_trivial_owner_linHom_linearEquiv
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P] :
    ((Representation.ofModule (k := k) (G := G) P).dual.asModule) ≃ₗ[k[G]]
      ((Representation.linHom (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) ((Representation.trivial k G k).asModule))).asModule) := by
  let T := (Representation.trivial k G k).asModule
  let eT : RestrictScalars k k[G] T ≃ₗ[k] T :=
    @restrictScalars_linearEquiv k inferInstance G inferInstance T
      inferInstance
      (representation_asModuleModule (ρ := Representation.trivial k G k))
      (Representation.trivial k G k).instModuleMonoidAlgebraAsModule
      (representation_asModule_isScalarTower (ρ := Representation.trivial k G k))
  let eCod : RestrictScalars k k[G] T ≃ₗ[k] k :=
    eT.trans (Representation.trivial k G k).asModuleEquiv
  let eHom :
      (RestrictScalars k k[G] P →ₗ[k] RestrictScalars k k[G] T) ≃ₗ[k]
        (P →ₗ[k] k) :=
    (restrictScalars_linearEquiv (k := k) (G := G) P).arrowCongr eCod
  let eLinear :
      Module.Dual k (RestrictScalars k k[G] P) ≃ₗ[k]
        (RestrictScalars k k[G] P →ₗ[k] RestrictScalars k k[G] T) :=
    ((restrictScalars_linearEquiv (k := k) (G := G) P).dualMap.symm).trans eHom.symm
  let eRep :
      (Representation.ofModule (k := k) (G := G) P).dual.Equiv
        (Representation.linHom
          (Representation.ofModule (k := k) (G := G) P)
          (Representation.ofModule (k := k) (G := G) T)) := by
    refine Representation.Equiv.mk eLinear ?_
    intro g
    ext φ x
    -- Route correction: compare both actions on the common owner `Hom_k(P,k)` and let the
    -- frozen trivial owner absorb the target action pointwise.
    simp [T, eT, eCod, eHom, eLinear, Representation.linHom_apply, Representation.dual_apply,
      Module.Dual.transpose_apply]
  let f :
      ((Representation.ofModule (k := k) (G := G) P).dual.asModule) →ₗ[k[G]]
        ((Representation.linHom
          (Representation.ofModule (k := k) (G := G) P)
          (Representation.ofModule (k := k) (G := G) T)).asModule) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := (Representation.ofModule (k := k) (G := G) P).dual)
      (σ := Representation.linHom
        (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) T)))
      eRep.toIntertwiningMap
  let g :
      ((Representation.linHom
          (Representation.ofModule (k := k) (G := G) P)
          (Representation.ofModule (k := k) (G := G) T)).asModule) →ₗ[k[G]]
        ((Representation.ofModule (k := k) (G := G) P).dual.asModule) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.linHom
        (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) T))
      (σ := (Representation.ofModule (k := k) (G := G) P).dual))
      eRep.symm.toIntertwiningMap
  refine LinearEquiv.ofLinear f g ?_ ?_
  · ext x
    -- The forward-then-backward composite is identity on the frozen internal-Hom owner.
    apply
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) T)).asModuleEquiv.injective
    change eRep (eRep.symm
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) T)).asModuleEquiv x)) =
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) T)).asModuleEquiv x
    simp
  · ext x
    -- The reverse composite is identity on the owner dual.
    apply ((Representation.ofModule (k := k) (G := G) P).dual).asModuleEquiv.injective
    change eRep.symm (eRep (((Representation.ofModule (k := k) (G := G) P).dual).asModuleEquiv x)) =
      ((Representation.ofModule (k := k) (G := G) P).dual).asModuleEquiv x
    simp

/-- Helper for Exercise 14-14.5-5: the owner dual of a finite projective `k[G]`-module is again
projective, via Exercise `14-14.5-3` applied to the trivial target owner. -/
theorem owner_dual_projective_of_projective
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P]
    [FiniteDimensional k P] [Module.Projective k[G] P] :
    Module.Projective k[G] ((ofModule P).dual.asModule) := by
  letI :
      Module.Projective k[G]
        ((Representation.linHom (Representation.ofModule (k := k) (G := G) P)
          (Representation.ofModule (k := k) (G := G) ((Representation.trivial k G k).asModule))).asModule) :=
    linHom_to_trivial_owner_frozen_alias_projective (k := k) (G := G) (P := P)
  -- Transport projectivity back across the direct frozen-owner duality equivalence.
  exact Module.Projective.of_equiv'
    (owner_dual_as_frozen_trivial_owner_linHom_linearEquiv
      (k := k) (G := G) (P := P)).symm

/-- Helper for Exercise 14-14.5-5: for a simple injective envelope, the transpose to the owner
dual is a projective envelope. -/
theorem transpose_simple_injectiveEnvelope_isProjectiveEnvelope
    {S P : Type*} [AddCommGroup S] [AddCommGroup P]
    [Module k S] [Module k P] [Module k[G] S] [Module k[G] P]
    [IsScalarTower k k[G] S] [IsScalarTower k k[G] P]
    [FiniteDimensional k S] [FiniteDimensional k P] [IsSimpleModule k[G] S]
    {i : S →ₗ[k[G]] P} (hi : i.IsInjectiveEnvelope) :
    (owner_dual_transpose (k := k) (G := G) i :
      ((ofModule P).dual.asModule) →ₗ[k[G]] ((ofModule S).dual.asModule)).IsProjectiveEnvelope := by
  let t :
      ((ofModule P).dual.asModule) →ₗ[k[G]] ((ofModule S).dual.asModule) :=
    owner_dual_transpose (k := k) (G := G) i
  letI : Module.Projective k[G] P :=
    (groupAlgebra_module_projective_iff_injective (k := k) (G := G) (M := P)).2 hi.toInjective
  letI : Module.Projective k[G] ((ofModule P).dual.asModule) :=
    owner_dual_projective_of_projective (k := k) (G := G) (P := P)
  have ht_surj : Function.Surjective t := by
    intro ξ
    let ik : S →ₗ[k] P := i.restrictScalars k
    obtain ⟨φ, hφ⟩ :=
      LinearMap.dualMap_surjective_of_injective (f := ik) hi.injective
        (owner_dual_to_linearDual (k := k) (G := G) (P := S) ξ)
    refine ⟨(owner_dual_to_linearDual (k := k) (G := G) (P := P)).symm φ, ?_⟩
    apply (owner_dual_to_linearDual (k := k) (G := G) (P := S)).injective
    ext s
    -- After transporting to the plain dual, surjectivity is exactly surjectivity of `ik.dualMap`.
    calc
      (owner_dual_to_linearDual (k := k) (G := G) (P := S)
          (t ((owner_dual_to_linearDual (k := k) (G := G) (P := P)).symm φ))) s
          = φ (ik s) := by
              simpa [t, ik] using
                owner_dual_transpose_apply (k := k) (G := G) (i := i)
                  ((owner_dual_to_linearDual (k := k) (G := G) (P := P)).symm φ) s
      _ = (owner_dual_to_linearDual (k := k) (G := G) (P := S) ξ) s := by
            simpa [ik] using congrArg (fun ψ : Module.Dual k S => ψ s) hφ
  have ht_essential : t.IsEssential := by
    refine ⟨fun N hNmap ↦ ?_⟩
    by_contra hN
    obtain ⟨s, hs_ne, hle⟩ :=
      transpose_simple_image_restrictScalars_le_owner_eval_ker_of_proper_submodule
        (k := k) (G := G) (hi := hi) N hN
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hs_ne
    have hker_ne_top : LinearMap.ker (Module.Dual.eval k S s) ≠ ⊤ := by
      intro htop
      have hmem : φ ∈ LinearMap.ker (Module.Dual.eval k S s) := by
        simpa [htop]
      have hzero : φ s = 0 := by
        simpa [LinearMap.mem_ker] using hmem
      have hone : (1 : k) = 0 := by
        simpa [hφ] using hzero
      exact one_ne_zero hone
    have hcomap_ne_top :
        Submodule.comap
            ((owner_dual_to_linearDual (k := k) (G := G) (P := S)).toLinearMap)
            (LinearMap.ker (Module.Dual.eval k S s)) ≠
          (⊤ : Submodule k ((ofModule S).dual.asModule)) := by
      intro htop
      apply hker_ne_top
      apply top_unique
      intro ψ hψ
      rcases (owner_dual_to_linearDual (k := k) (G := G) (P := S)).surjective ψ with ⟨ξ, rfl⟩
      have hξ :
          ξ ∈
            Submodule.comap
              ((owner_dual_to_linearDual (k := k) (G := G) (P := S)).toLinearMap)
              (LinearMap.ker (Module.Dual.eval k S s)) := by
        simpa [htop]
      simpa using hξ
    have htop_comap :
        Submodule.comap
            ((owner_dual_to_linearDual (k := k) (G := G) (P := S)).toLinearMap)
            (LinearMap.ker (Module.Dual.eval k S s)) =
          (⊤ : Submodule k ((ofModule S).dual.asModule)) := by
      have htop_le :
          (⊤ : Submodule k ((ofModule S).dual.asModule)) ≤
            Submodule.comap
              ((owner_dual_to_linearDual (k := k) (G := G) (P := S)).toLinearMap)
              (LinearMap.ker (Module.Dual.eval k S s)) := by
        have hmap_top :
            (N.map t).restrictScalars k =
              (⊤ : Submodule k ((ofModule S).dual.asModule)) := by
          simpa [hNmap]
        rw [← hmap_top]
        exact hle
      exact le_antisymm le_top htop_le
    exact hcomap_ne_top htop_comap
  letI : t.IsEssential := ht_essential
  -- The simple-case source-faithful route is now complete: projective source, dual surjectivity,
  -- and the previously closed evaluation-kernel containment imply that the transpose is a
  -- projective envelope.
  exact LinearMap.IsProjectiveEnvelope.mk ht_surj

end
