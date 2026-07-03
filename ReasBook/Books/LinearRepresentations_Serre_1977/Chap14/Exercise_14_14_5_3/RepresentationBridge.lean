import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_2
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_1
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.PerfectPairing.Basic

open scoped MonoidAlgebra

universe u v w x

noncomputable section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module k E] [Module k[G] E] [IsScalarTower k k[G] E]
variable {F : Type x} [AddCommGroup F] [Module k F] [Module k[G] F] [IsScalarTower k k[G] F]

/-- Helper for Exercise 14-14.5-3: the `RestrictScalars` wrapper retains the ambient `k`-module
structure. -/
instance restrictScalars_module (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M]
    [IsScalarTower k k[G] M] :
    Module k (RestrictScalars k k[G] M) := inferInstance

/-- Helper for Exercise 14-14.5-3: the `RestrictScalars` wrapper also retains the ambient
`k[G]`-module structure on the underlying type. -/
instance restrictScalars_groupAlgebraModule
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M] :
    Module k[G] (RestrictScalars k k[G] M) := by
  delta RestrictScalars
  infer_instance

/-- Helper for Exercise 14-14.5-3: the `RestrictScalars` wrapper preserves the additive-group
structure of the underlying `k[G]`-module. -/
instance restrictScalars_addCommGroup (M : Type*) [AddCommGroup M] [Module k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    AddCommGroup (RestrictScalars k k[G] M) := inferInstance

/-- Helper for Exercise 14-14.5-3: `k`-linear maps between wrapped `k[G]`-modules inherit the
pointwise additive-group structure. -/
instance restrictScalars_linearMap_addCommGroup
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    AddCommGroup (RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N) :=
  @LinearMap.addCommGroup k k
    (RestrictScalars k k[G] M) (RestrictScalars k k[G] N)
    (by infer_instance) (by infer_instance)
    (instAddCommMonoidRestrictScalars k k[G] M)
    (restrictScalars_addCommGroup (k := k) (G := G) N)
    (restrictScalars_module (k := k) (G := G) M)
    (restrictScalars_module (k := k) (G := G) N)
    (RingHom.id k)

/-- Helper for Exercise 14-14.5-3: scalar multiplication by `k` acts pointwise on linear maps
between wrapped `k[G]`-modules. -/
instance restrictScalars_linearMap_module
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    Module k (RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N) :=
  @LinearMap.module k k k
    (RestrictScalars k k[G] M) (RestrictScalars k k[G] N)
    (by infer_instance) (by infer_instance)
    (instAddCommMonoidRestrictScalars k k[G] M)
    (instAddCommMonoidRestrictScalars k k[G] N)
    (restrictScalars_module (k := k) (G := G) M)
    (restrictScalars_module (k := k) (G := G) N)
    (RingHom.id k)
    (by infer_instance)
    (restrictScalars_module (k := k) (G := G) N)
    (by infer_instance)

/-- Helper for Exercise 14-14.5-3: the owner type of a representation on an additive group is
itself an additive commutative group. -/
instance representation_asModuleAddCommGroup {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    AddCommGroup ρ.asModule := by
  delta Representation.asModule
  infer_instance

/-- Helper for Exercise 14-14.5-3: the owner type of a representation also retains its underlying
`k`-module structure. -/
instance representation_asModuleModule {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    Module k ρ.asModule := by
  delta Representation.asModule
  infer_instance

/-- Helper for Exercise 14-14.5-3: the canonical `k[G]`-module structure on the owner of a
representation is compatible with the ambient `k`-scalar action. -/
instance representation_asModule_isScalarTower {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    IsScalarTower k k[G] ρ.asModule :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    apply ρ.asModuleEquiv.injective
    simpa using
      (Representation.asModuleEquiv_map_smul (ρ := ρ) (r := algebraMap k k[G] r) (x := x))

/-- Helper for Exercise 14-14.5-3: wrapped `k`-linear Hom spaces between `RestrictScalars`
modules are again `k`-modules. -/
instance wrapped_restrictScalars_linHom_module
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    Module k (RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N) :=
  restrictScalars_linearMap_module (k := k) (G := G) (M := M) (N := N)

/-- Helper for Exercise 14-14.5-3: the owner of the internal-Hom representation on two
`ofModule` representations is an additive commutative group. -/
instance ofModule_linHom_asModule_addCommGroup
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    AddCommGroup
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) M)
        (Representation.ofModule (k := k) (G := G) N)).asModule) := by
  delta Representation.asModule
  infer_instance

/-- Helper for Exercise 14-14.5-3: the owner of the internal-Hom representation on two
`ofModule` representations is a `k`-module. -/
instance ofModule_linHom_asModule_module
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    Module k
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) M)
        (Representation.ofModule (k := k) (G := G) N)).asModule) := by
  delta Representation.asModule
  infer_instance

/-- Helper for Exercise 14-14.5-3: the owner of the internal-Hom representation on two
`ofModule` representations has compatible ambient `k`- and `k[G]`-scalar actions. -/
instance ofModule_linHom_asModule_isScalarTower
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    IsScalarTower k k[G]
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) M)
        (Representation.ofModule (k := k) (G := G) N)).asModule) := by
  -- Stay on the exact internal-Hom representation owner so the `k[G]`-action is the conjugation
  -- action coming from the representation, not a pointwise codomain action.
  letI :
      AddCommGroup (RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N) :=
    restrictScalars_linearMap_addCommGroup (k := k) (G := G) (M := M) (N := N)
  letI :
      Module k (RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N) :=
    restrictScalars_linearMap_module (k := k) (G := G) (M := M) (N := N)
  let ρ :
      Representation k G (RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N) :=
    Representation.linHom
      (Representation.ofModule (k := k) (G := G) M)
      (Representation.ofModule (k := k) (G := G) N)
  change IsScalarTower k k[G] ρ.asModule
  exact IsScalarTower.of_algebraMap_smul fun r x ↦ by
    apply ρ.asModuleEquiv.injective
    simpa using
      (Representation.asModuleEquiv_map_smul (ρ := ρ) (r := algebraMap k k[G] r) (x := x))

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's symmetry statement for the `k`-dimensions of the `k[G]`-linear Hom
--   spaces `E → F` and `F → E`.
-- * core/canonical: `Representation.ofModule`, `Representation.linHom`,
--   `Representation.invariantsEquivIntertwiningMap`, and
--   `Representation.IntertwiningMap.equivLinearMapAsModule`.
-- * bridge/view: inside the proof, identify the source-facing `k[G]`-module Hom space with the
--   intertwining space for the canonical representations attached to `E` and `F`; that bridge is
--   proof-internal rather than the public theorem surface.
--
-- Proof sketch: pass internally to the canonical representation-theoretic owner for the Hom
-- space, apply Exercise `14-14.5-2`, and transport the resulting invariant-space dimension
-- equality back to the source-facing `k[G]`-linear Hom spaces.
/-- Helper for Exercise 14-14.5-3: a finite-dimensional projective `k[G]`-module is a retract of
a finite free `k[G]`-module. -/
theorem finite_free_split_of_projective
    [Module.Projective k[G] E] [FiniteDimensional k E] :
    ∃ (n : ℕ) (f : (Fin n → k[G]) →ₗ[k[G]] E) (g : E →ₗ[k[G]] Fin n → k[G]),
      Function.Surjective f ∧ Function.Injective g ∧ f.comp g = LinearMap.id := by
  -- Finite dimensionality over `k` makes `E` finite over the finite-dimensional algebra `k[G]`.
  letI : Module.Finite k k[G] := Module.Finite.of_basis (MonoidAlgebra.basis G k)
  letI : Module.Finite k[G] E := Module.Finite.of_restrictScalars_finite k k[G] E
  -- Projectivity upgrades a finite presentation to a split finite free presentation.
  obtain ⟨n, f, g, hsurj, hinj, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (R := k[G]) (M := E)
  exact ⟨n, f, g, hsurj, hinj, hfg⟩

/-- Helper for Exercise 14-14.5-3: the owner module of `Representation.ofModule` is canonically
the original `k[G]`-module. -/
noncomputable def ofModule_asModuleLinearEquiv (M : Type*) [AddCommGroup M] [Module k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    (Representation.ofModule (k := k) (G := G) M).asModule ≃ₗ[k[G]] M := by
  let toFun :
      (Representation.ofModule (k := k) (G := G) M).asModule → M :=
    fun x ↦
      RestrictScalars.addEquiv k k[G] M
        ((Representation.ofModule (k := k) (G := G) M).asModuleEquiv x)
  let invFun :
      M → (Representation.ofModule (k := k) (G := G) M).asModule :=
    fun x ↦
      (Representation.ofModule (k := k) (G := G) M).asModuleEquiv.symm
        ((RestrictScalars.addEquiv k k[G] M).symm x)
  have hleft : Function.LeftInverse invFun toFun := by
    -- Both directions are the identity after unpacking the `RestrictScalars` wrapper.
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    -- The same computation gives the inverse identity on the original module.
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : k[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    -- Transport the `k[G]`-action through `asModuleEquiv`.
    change
      RestrictScalars.addEquiv k k[G] M
          ((Representation.ofModule (k := k) (G := G) M).asModuleEquiv (r • x)) =
        r • RestrictScalars.addEquiv k k[G] M
          ((Representation.ofModule (k := k) (G := G) M).asModuleEquiv x)
    simp [Representation.smul_ofModule_asModule]
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }

/-- Helper for Exercise 14-14.5-3: intertwining maps between the canonical `ofModule`
representations are exactly the `k[G]`-linear maps between the original modules. -/
noncomputable abbrev ofModule_intertwining_equiv_linearMap :
    Representation.IntertwiningMap
      (Representation.ofModule (k := k) (G := G) E)
      (Representation.ofModule (k := k) (G := G) F) ≃ₗ[k]
        (E →ₛₗ[RingHom.id (k[G])] F) :=
  by
    let eE := ofModule_asModuleLinearEquiv (k := k) (G := G) E
    let eF := ofModule_asModuleLinearEquiv (k := k) (G := G) F
    refine
      { toFun := fun u ↦
          eF.toLinearMap.comp
            (((Representation.IntertwiningMap.equivLinearMapAsModule
              (ρ := Representation.ofModule (k := k) (G := G) E)
              (σ := Representation.ofModule (k := k) (G := G) F)) u).comp
                eE.symm.toLinearMap)
        invFun := fun ℓ ↦
          (Representation.IntertwiningMap.equivLinearMapAsModule
            (ρ := Representation.ofModule (k := k) (G := G) E)
            (σ := Representation.ofModule (k := k) (G := G) F)).symm
              (eF.symm.toLinearMap.comp (ℓ.comp eE.toLinearMap))
        map_add' := by
          intro u v
          ext x
          simp [eE, eF, LinearMap.add_comp, LinearMap.comp_add]
        map_smul' := by
          intro a u
          ext x
          simp [LinearMap.comp_apply]
        left_inv := by
          intro u
          apply (Representation.IntertwiningMap.equivLinearMapAsModule
            (ρ := Representation.ofModule (k := k) (G := G) E)
            (σ := Representation.ofModule (k := k) (G := G) F)).injective
          ext x
          simp [eE, eF, LinearMap.comp_assoc]
        right_inv := by
          intro ℓ
          ext x
          simp [eE, eF, LinearMap.comp_assoc] }

/-- Helper for Exercise 14-14.5-3: a representation equivalence induces an equivalence on
invariants. -/
noncomputable def invariantsCongr {V : Type*} [AddCommGroup V] [Module k V]
    {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.invariants ≃ₗ[k] σ.invariants where
  toFun x :=
    ⟨e x, by
      intro g
      -- Intertwining carries fixed vectors to fixed vectors.
      calc
        σ g (e x) = e (ρ g x) := by
          simpa using (LinearMap.congr_fun (e.isIntertwining' g).symm x)
        _ = e x := by rw [x.property g]⟩
  invFun x :=
    ⟨e.symm x, by
      intro g
      -- The same argument works for the inverse equivalence.
      calc
        ρ g (e.symm x) = e.symm (σ g x) := by
          simpa using (LinearMap.congr_fun (e.symm.isIntertwining' g).symm x)
        _ = e.symm x := by rw [x.property g]⟩
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := by
    ext
    simp
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

/-- Helper for Exercise 14-14.5-3: precomposition by an intertwining map gives an intertwining map
between the two internal-Hom representations. -/
noncomputable def linHom_precompose {V : Type*} [AddCommGroup V] [Module k V]
    {W : Type*} [AddCommGroup W] [Module k W]
    {U : Type*} [AddCommGroup U] [Module k U]
    {ρV : Representation k G V} {ρW : Representation k G W} {ρU : Representation k G U}
    (u : ρV.IntertwiningMap ρW) :
    (Representation.linHom ρW ρU).IntertwiningMap (Representation.linHom ρV ρU) := by
  refine ⟨LinearMap.lcomp k U u.toLinearMap, ?_⟩
  intro g
  -- Conjugation on `linHom` commutes with precomposition by an intertwining map.
  ext h x
  simp [Representation.linHom_apply, u.isIntertwining]

/-- Helper for Exercise 14-14.5-3: a split finite-free presentation of the source module induces a
split retract on the owner modules of the internal-Hom representations. -/
theorem linHom_precompose_split_retract
    {P : Type*} [AddCommGroup P] [Module k P]
    {ρP : Representation k G P} {ρE : Representation k G E} {ρF : Representation k G F}
    (i : ρP.IntertwiningMap ρE) (s : ρE.IntertwiningMap ρP)
    (his : (i.toLinearMap : P →ₗ[k] E).comp s.toLinearMap = LinearMap.id) :
    let toAmbient :
        (Representation.linHom ρE ρF).asModule →ₗ[k[G]]
          (Representation.linHom ρP ρF).asModule :=
      (Representation.IntertwiningMap.equivLinearMapAsModule
        (ρ := Representation.linHom ρE ρF)
        (σ := Representation.linHom ρP ρF)) (linHom_precompose (ρU := ρF) i)
    let fromAmbient :
        (Representation.linHom ρP ρF).asModule →ₗ[k[G]]
          (Representation.linHom ρE ρF).asModule :=
      (Representation.IntertwiningMap.equivLinearMapAsModule
        (ρ := Representation.linHom ρP ρF)
        (σ := Representation.linHom ρE ρF)) (linHom_precompose (ρU := ρF) s)
    fromAmbient.comp toAmbient = LinearMap.id := by
  dsimp
  -- Once the split is moved to the owner modules, precomposition recovers the identity.
  ext h
  apply (Representation.linHom ρE ρF).asModuleEquiv.injective
  ext x
  change
    ((linHom_precompose (ρU := ρF) s).toLinearMap
      ((linHom_precompose (ρU := ρF) i).toLinearMap h)) x =
        ((Representation.linHom ρE ρF).asModuleEquiv h) x
  change ((Representation.linHom ρE ρF).asModuleEquiv
      ((linHom_precompose (ρU := ρF) s).toLinearMap
        ((linHom_precompose (ρU := ρF) i).toLinearMap h))) x =
      ((Representation.linHom ρE ρF).asModuleEquiv h) x
  change ((Representation.linHom ρE ρF).asModuleEquiv h)
      ((i.toLinearMap.comp s.toLinearMap) x) =
        ((Representation.linHom ρE ρF).asModuleEquiv h) x
  simpa using congrArg ((Representation.linHom ρE ρF).asModuleEquiv h)
    (LinearMap.congr_fun his x)

/-- Helper for Exercise 14-14.5-3: projectivity of the internal-Hom owner descends along the split
retract induced by precomposition. -/
theorem linHom_projective_of_split_source
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P]
    (f : P →ₗ[k[G]] E) (g : E →ₗ[k[G]] P) (hfg : f.comp g = LinearMap.id)
    (hP :
      Module.Projective k[G]
        ((Representation.linHom
          (Representation.ofModule (k := k) (G := G) P)
          (Representation.ofModule (k := k) (G := G) F)).asModule)) :
    Module.Projective k[G]
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)).asModule) := by
  let eP := ofModule_asModuleLinearEquiv (k := k) (G := G) P
  let eE := ofModule_asModuleLinearEquiv (k := k) (G := G) E
  let iLinear :
      (Representation.ofModule (k := k) (G := G) P).asModule →ₗ[k[G]]
        (Representation.ofModule (k := k) (G := G) E).asModule :=
    eE.symm.toLinearMap.comp (f.comp eP.toLinearMap)
  let sLinear :
      (Representation.ofModule (k := k) (G := G) E).asModule →ₗ[k[G]]
        (Representation.ofModule (k := k) (G := G) P).asModule :=
    eP.symm.toLinearMap.comp (g.comp eE.toLinearMap)
  -- Move the split presentation of `E` to the owner modules of the canonical representations.
  let i :
      (Representation.ofModule (k := k) (G := G) P).IntertwiningMap
        (Representation.ofModule (k := k) (G := G) E) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.ofModule (k := k) (G := G) P)
      (σ := Representation.ofModule (k := k) (G := G) E)).symm iLinear
  let s :
      (Representation.ofModule (k := k) (G := G) E).IntertwiningMap
        (Representation.ofModule (k := k) (G := G) P) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.ofModule (k := k) (G := G) E)
      (σ := Representation.ofModule (k := k) (G := G) P)).symm sLinear
  letI : Module k (RestrictScalars k k[G] P) := inferInstance
  letI : Module k (RestrictScalars k k[G] E) := inferInstance
  letI : Module k (RestrictScalars k k[G] F) := inferInstance
  let toAmbientIntertwining :
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)).IntertwiningMap
          (Representation.linHom
            (Representation.ofModule (k := k) (G := G) P)
            (Representation.ofModule (k := k) (G := G) F)) := by
    -- Precomposition by the transported split injection respects the internal-Hom action.
    refine ⟨LinearMap.lcomp k (RestrictScalars k k[G] F) i.toLinearMap, ?_⟩
    intro a
    ext h x
    simp [Representation.linHom_apply, i.isIntertwining]
  let fromAmbientIntertwining :
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) F)).IntertwiningMap
          (Representation.linHom
            (Representation.ofModule (k := k) (G := G) E)
            (Representation.ofModule (k := k) (G := G) F)) := by
    -- The same construction with the splitting retraction gives the reverse map.
    refine ⟨LinearMap.lcomp k (RestrictScalars k k[G] F) s.toLinearMap, ?_⟩
    intro a
    ext h x
    simp [Representation.linHom_apply, s.isIntertwining]
  let toAmbient :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F))
      (σ := Representation.linHom
        (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) F)))
      toAmbientIntertwining
  let fromAmbient :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.linHom
        (Representation.ofModule (k := k) (G := G) P)
        (Representation.ofModule (k := k) (G := G) F))
      (σ := Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)))
      fromAmbientIntertwining
  have hsplit : fromAmbient.comp toAmbient = LinearMap.id := by
    -- The owner-level split gives the desired retract on internal-Hom owners.
    have hisOwner : i.toLinearMap.comp s.toLinearMap = LinearMap.id := by
      ext x
      change (eE.symm (f (g (eE x)))) = x
      have hfgx := congrArg eE.symm (LinearMap.congr_fun hfg (eE x))
      simpa [i, s, iLinear, sLinear, eE.left_inv] using hfgx
    -- After translating back to the underlying intertwining maps, this is composition by
    -- `i.toLinearMap.comp s.toLinearMap`, hence by the identity.
    ext h
    apply (Representation.linHom
      (Representation.ofModule (k := k) (G := G) E)
      (Representation.ofModule (k := k) (G := G) F)).asModuleEquiv.injective
    ext x
    change
      (fromAmbientIntertwining.toLinearMap
        (toAmbientIntertwining.toLinearMap
          ((Representation.linHom
            (Representation.ofModule (k := k) (G := G) E)
            (Representation.ofModule (k := k) (G := G) F)).asModuleEquiv h))) x =
        ((Representation.linHom
          (Representation.ofModule (k := k) (G := G) E)
          (Representation.ofModule (k := k) (G := G) F)).asModuleEquiv h) x
    change
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)).asModuleEquiv h)
          ((i.toLinearMap.comp s.toLinearMap) x) =
        ((Representation.linHom
          (Representation.ofModule (k := k) (G := G) E)
          (Representation.ofModule (k := k) (G := G) F)).asModuleEquiv h) x
    simpa using congrArg
      (((Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)).asModuleEquiv h))
      (LinearMap.congr_fun hisOwner x)
  -- Projectivity descends along this split retract.
  letI :
      Module.Projective k[G]
        ((Representation.linHom
          (Representation.ofModule (k := k) (G := G) P)
          (Representation.ofModule (k := k) (G := G) F)).asModule) :=
    hP
  exact Module.Projective.of_split toAmbient fromAmbient hsplit

end
