import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_27_5
import StacksProject_2024.stacks_project.Chap12.Lemma_12_29_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_55_9

open CategoryTheory Limits
open scoped Topology

universe u v

noncomputable section

namespace CategoryTheory

section AlgebraicSpecialization

variable (R : Type u) (G : Type v) [Ring R] [Monoid G]

/-- The cofree algebraic `R`-linear `G`-action on a module `M`, given by right translation on
`G → M`. -/
private abbrev actionModuleCatCofreeObj (M : ModuleCat.{max u v} R) :
    Action (ModuleCat.{max u v} R) G where
  V := ModuleCat.of R (G → M)
  ρ :=
    { toFun := fun g ↦
        ModuleCat.ofHom
          { toFun := fun f h ↦ f (h * g)
            map_add' := fun _ _ ↦ by
              ext h
              rfl
            map_smul' := fun _ _ ↦ by
              ext h
              rfl }
      map_one' := by
        apply ModuleCat.hom_ext
        ext f h
        simp
      map_mul' := fun g h ↦ by
        apply ModuleCat.hom_ext
        ext f x
        simp [mul_assoc] }

/-- Postcomposition by a module morphism defines the map part of the cofree algebraic action
functor. -/
private abbrev actionModuleCatCofreeMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    actionModuleCatCofreeObj R G M ⟶ actionModuleCatCofreeObj R G N where
  hom := ModuleCat.ofHom
    { toFun := fun x g ↦ f.hom (x g)
      map_add' := fun _ _ ↦ by
        ext g
        simp
      map_smul' := fun _ _ ↦ by
        ext g
        simp }
  comm g := by
    ext x h
    rfl

/-- The cofree algebraic action functor right adjoint to forgetting the `G`-action. -/
private abbrev actionModuleCatCofree : ModuleCat.{max u v} R ⥤ Action (ModuleCat.{max u v} R) G
    where
  obj := actionModuleCatCofreeObj R G
  map := actionModuleCatCofreeMap R G
  map_id M := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x g
    simp
  map_comp f g := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x h
    simp

/-- The hom-set bijection for the forgetful/cofree adjunction on algebraic `R`-linear
`G`-actions. -/
private abbrev actionModuleCatForgetCofreeHomEquiv
    (X : Action (ModuleCat.{max u v} R) G) (M : ModuleCat.{max u v} R) :
    ((Action.forget (ModuleCat.{max u v} R) G).obj X ⟶ M) ≃
      (X ⟶ (actionModuleCatCofree R G).obj M) where
  toFun φ :=
    { hom := ModuleCat.ofHom
        { toFun := fun x g ↦ φ.hom ((X.ρ g).hom x)
          map_add' := fun _ _ ↦ by
            ext g
            simp
          map_smul' := fun _ _ ↦ by
            ext g
            simp }
      comm := fun g ↦ by
        ext x h
        simp [actionModuleCatCofreeObj] }
  invFun ψ := ModuleCat.ofHom
    { toFun := fun x ↦ ψ.hom.hom x 1
      map_add' := fun _ _ ↦ by simp
      map_smul' := fun _ _ ↦ by simp }
  left_inv φ := by
    ext x
    change φ.hom ((X.ρ 1).hom x) = φ.hom x
    simp [Action.ρ_one]
  right_inv ψ := by
    ext x g
    have hcomm := congrArg (fun k ↦ k x 1) (ModuleCat.hom_ext_iff.mp (ψ.comm g))
    simpa using hcomm

/-- The forgetful functor from algebraic `R`-linear `G`-actions to `R`-modules is left adjoint to
the cofree algebraic action functor. -/
private noncomputable def actionModuleCatForgetCofreeAdjunction :
    Action.forget (ModuleCat.{max u v} R) G ⊣ actionModuleCatCofree R G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := actionModuleCatForgetCofreeHomEquiv R G
      homEquiv_naturality_left_symm := by
        intro X Y M f φ
        ext x
        rfl
      homEquiv_naturality_right := by
        intro X M N f φ
        ext x
        rfl }

/-- The algebraic action category has functorial injective embeddings via the cofree right adjoint
to `Action.forget`. -/
private instance actionModuleCat_hasFunctorialInjectiveEmbeddings :
    HasFunctorialInjectiveEmbeddings (Action (ModuleCat.{max u v} R) G) := by
  letI : EnoughInjectives (ModuleCat.{max u v} R) := ModuleCat.enoughInjectives R
  letI : HasFunctorialInjectiveEmbeddings (ModuleCat.{max u v} R) := inferInstance
  let hzero : ∀ X : Action (ModuleCat.{max u v} R) G,
      IsZero ((Action.forget (ModuleCat.{max u v} R) G).obj X) → IsZero X := by
    intro X hX
    refine ⟨fun Y ↦ ?_, fun Y ↦ ?_⟩
    · refine ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩
      exact Action.hom_ext _ _ (hX.eq_of_src f.hom 0)
    · refine ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩
      exact Action.hom_ext _ _ (hX.eq_of_tgt f.hom 0)
  exact hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms
    (actionModuleCatCofree R G) (Action.forget (ModuleCat.{max u v} R) G)
    (actionModuleCatForgetCofreeAdjunction R G) hzero

end AlgebraicSpecialization

section SourceFacing

variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-
Domain-style sampling for Lemma 19.3.1:
- primary domain: discrete `R`-modules with continuous action of a topological group;
- sampled owner declarations:
  `Action`,
  `ObjectProperty.FullSubcategory`,
  `continuousSMul_iff_stabilizer_isOpen`,
  `ObjectProperty.ι`,
  `hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms`,
  `HasFunctorialInjectiveEmbeddings`;
- best owner abstraction:
  `source-facing`: the full subcategory of `Action (ModuleCat R) G` cut out by the canonical
    open-stabilizer criterion for continuity on discrete modules;
  `core/canonical`: `Action (ModuleCat R) G`;
  `bridge/view`: the right adjoint sending an algebraic action to the open-stabilizer submodule.
- primitive data: an algebraic `R`-linear action in `Action (ModuleCat R) G`;
- derived API: the source-facing owner property `isDiscreteContinuousAction R G`, the scoped
  notation `Mod_{R,G}`, the bridge to `ContinuousSMul` on a discrete carrier, and the induced
  functorial injective-embedding instance.

Source/core/bridge triage:
- `source-facing`: `Mod_{R,G}`, the category of discrete `R`-modules with continuous `G`-action,
  encoded intrinsically by the equivalent open-stabilizer condition;
- `core/canonical`: `Action (ModuleCat R) G`;
- `bridge/view`: the open-stabilizer coreflection from algebraic actions to the source-facing
  category. -/

private instance actionMulAction (X : Action (ModuleCat.{max u v} R) G) : MulAction G X.V where
  smul g x := (X.ρ g).hom x
  one_smul x := by
    change ((X.ρ 1).hom) x = x
    simpa [Action.ρ_one]
  mul_smul g h x := by
    change ((X.ρ (g * h)).hom) x = (((X.ρ h) ≫ (X.ρ g)).hom) x
    rw [X.ρ.map_mul]
    rfl

/-- The object property on algebraic `R`-linear `G`-actions corresponding to discrete modules
with continuous `G`-action. By `continuousSMul_iff_stabilizer_isOpen`, this is equivalently the
open-stabilizer condition on the carrier. -/
def isDiscreteContinuousAction : ObjectProperty (Action (ModuleCat.{max u v} R) G) :=
  fun X ↦ ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G)

scoped[DiscreteContinuousAction] notation3:max "Mod_{" R "," G "}" =>
  ObjectProperty.FullSubcategory (isDiscreteContinuousAction R G)

open scoped DiscreteContinuousAction

/-- The open-stabilizer condition is exactly continuity of the `G`-action when the carrier module
is given a discrete topology. -/
theorem isDiscreteContinuousAction_iff_continuousSMul
    (X : Action (ModuleCat.{max u v} R) G) [TopologicalSpace X.V] [DiscreteTopology X.V] :
    isDiscreteContinuousAction R G X ↔ ContinuousSMul G X.V := by
  letI : MulAction G X.V := actionMulAction R G X
  simpa [isDiscreteContinuousAction] using
    (continuousSMul_iff_stabilizer_isOpen :
      ContinuousSMul G X.V ↔ ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G)).symm

/-- Helper for Lemma 19.3.1: a subgroup containing an open subgroup is open. -/
private theorem open_subgroup_of_le {H K : Subgroup G} (hHK : H ≤ K)
    (hH : IsOpen (H : Set G)) : IsOpen (K : Set G) := by
  -- Any larger subgroup contains the open neighborhood of the identity coming from `H`.
  exact Subgroup.isOpen_mono hHK hH

/-- Helper for Lemma 19.3.1: equivariant isomorphisms preserve the open-stabilizer condition. -/
private theorem isDiscreteContinuousAction_of_iso {X Y : Action (ModuleCat.{max u v} R) G}
    (e : X ≅ Y) (hX : isDiscreteContinuousAction R G X) :
    isDiscreteContinuousAction R G Y := by
  intro y
  -- Pull `y` back along the inverse isomorphism so the open stabilizer on `X` is available.
  let x : X.V := e.inv.hom y
  have hle : MulAction.stabilizer G x ≤ MulAction.stabilizer G (e.hom.hom x) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    calc
      g • e.hom.hom x = e.hom.hom (g • x) := by
        symm
        simpa using congrArg (fun φ ↦ φ.hom x) (e.hom.comm g)
      _ = e.hom.hom x := by simpa [hg]
  -- The transported stabilizer contains the open stabilizer of `x`.
  have hopen :
      IsOpen (MulAction.stabilizer G (e.hom.hom x) : Set G) :=
    open_subgroup_of_le (G := G) hle (hX x)
  have hy : e.hom.hom x = y := by
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (Action.inv_hom_hom e)) y
  simpa [hy] using hopen

/-- Helper for Lemma 19.3.1: the stabilizer of a sum contains the intersection of the two
stabilizers. -/
private theorem open_stabilizer_add_mem {X : Action (ModuleCat.{max u v} R) G} {x y : X.V}
    (hx : IsOpen (MulAction.stabilizer G x : Set G))
    (hy : IsOpen (MulAction.stabilizer G y : Set G)) :
    IsOpen (MulAction.stabilizer G (x + y) : Set G) := by
  have hle :
      MulAction.stabilizer G x ⊓ MulAction.stabilizer G y ≤
        MulAction.stabilizer G (x + y) := by
    intro g hg
    have hgx : g • x = x := MulAction.mem_stabilizer_iff.mp hg.1
    have hgy : g • y = y := MulAction.mem_stabilizer_iff.mp hg.2
    rw [MulAction.mem_stabilizer_iff]
    -- A group element fixing each summand also fixes their sum.
    calc
      g • (x + y) = g • x + g • y := by
        change (X.ρ g).hom (x + y) = (X.ρ g).hom x + (X.ρ g).hom y
        exact (X.ρ g).hom.map_add x y
      _ = x + y := by simpa [hgx, hgy]
  have hxy :
      IsOpen ((MulAction.stabilizer G x ⊓ MulAction.stabilizer G y : Subgroup G) : Set G) := by
    simpa using hx.inter hy
  exact open_subgroup_of_le (G := G) hle hxy

/-- Helper for Lemma 19.3.1: scalar multiplication by `R` preserves openness of stabilizers. -/
private theorem open_stabilizer_rsmul_mem {X : Action (ModuleCat.{max u v} R) G} (r : R)
    {x : X.V} (hx : IsOpen (MulAction.stabilizer G x : Set G)) :
    IsOpen (MulAction.stabilizer G (r • x) : Set G) := by
  have hle :
      MulAction.stabilizer G x ≤ MulAction.stabilizer G (r • x) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    -- The action maps are `R`-linear, so fixing `x` implies fixing every scalar multiple.
    calc
      g • (r • x) = r • (g • x) := by
        change (X.ρ g).hom (r • x) = r • (X.ρ g).hom x
        exact (X.ρ g).hom.map_smul r x
      _ = r • x := by simpa [hg]
  exact open_subgroup_of_le (G := G) hle hx

/-- Helper for Lemma 19.3.1: the conjugation image of an open subgroup is open. -/
private theorem open_subgroup_map_conj (g : G) {H : Subgroup G}
    (hH : IsOpen (H : Set G)) :
    IsOpen ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  let e : G ≃ₜ G := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  -- Rewrite the conjugation image as the image of `H` under the conjugation homeomorphism.
  rw [Subgroup.coe_map]
  have hopen : IsOpen (e '' (H : Set G)) := e.isOpenMap _ hH
  simpa [e, MulAut.conj_apply, Set.image_image, Function.comp, mul_assoc] using hopen

/-- Helper for Lemma 19.3.1: the zero vector has open stabilizer in every algebraic action. -/
private theorem openStabilizerSubmodule_zero_mem (X : Action (ModuleCat.{max u v} R) G) :
    (0 : X.V) ∈ { x | IsOpen (MulAction.stabilizer G x : Set G) } := by
  have htop : MulAction.stabilizer G (0 : X.V) = ⊤ := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro _
      simp
    · intro _
      change (X.ρ g).hom 0 = 0
      simpa using (X.ρ g).hom.map_zero
  -- The stabilizer of zero is the whole group.
  simpa [htop] using (show IsOpen ((⊤ : Subgroup G) : Set G) from isOpen_univ)

instance isDiscreteContinuousAction_containsZero :
    (isDiscreteContinuousAction R G).ContainsZero := by
  let Z : Action (ModuleCat.{max u v} R) G := Action.trivial G (ModuleCat.of R PUnit)
  have hZ : IsZero Z := by
    refine ⟨?_, ?_⟩
    · intro Y
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro f
      apply Action.hom_ext
      apply ModuleCat.hom_ext
      ext x
      have hx : x = 0 := by
        cases x
        rfl
      simpa [hx] using f.hom.hom.map_zero
    · intro Y
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro f
      apply Action.hom_ext
      apply ModuleCat.hom_ext
      ext x
      cases f.hom.hom x
      rfl
  refine ⟨Z, hZ, ?_⟩
  intro x
  -- Every element of the zero action is fixed by all of `G`.
  have htop : MulAction.stabilizer G x = ⊤ := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro _
      simp
    · intro _
      cases x
      rfl
  simpa [htop] using (show IsOpen ((⊤ : Subgroup G) : Set G) from isOpen_univ)

instance isDiscreteContinuousAction_closedUnderKernels :
    (isDiscreteContinuousAction R G).IsClosedUnderKernels := by
  refine ⟨?_⟩
  intro Z hZ
  rcases hZ with ⟨f, k, hk, hXY⟩
  letI : Mono k.ι := Fork.IsLimit.mono hk
  letI : Mono k.ι.hom := (Action.forget (ModuleCat.{max u v} R) G).map_mono k.ι
  have hι_injective : Function.Injective k.ι.hom.hom :=
    (ModuleCat.mono_iff_injective k.ι.hom).1 inferInstance
  intro q
  let qX := k.ι.hom.hom q
  have hqX : IsOpen (MulAction.stabilizer G qX : Set G) := hXY.1 qX
  have hle : MulAction.stabilizer G qX ≤ MulAction.stabilizer G q := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    apply hι_injective
    calc
      k.ι.hom.hom (g • q) = g • k.ι.hom.hom q := by
        simpa using congrArg (fun φ ↦ φ.hom q) (k.ι.comm g)
      _ = k.ι.hom.hom q := by simpa [hg]
  exact open_subgroup_of_le (G := G) hle hqX

instance isDiscreteContinuousAction_closedUnderCokernels :
    (isDiscreteContinuousAction R G).IsClosedUnderCokernels := by
  refine ⟨?_⟩
  intro Z hZ
  rcases hZ with ⟨f, k, hk, hXY⟩
  intro q
  letI : Epi k.π := Cofork.IsColimit.epi hk
  letI : Epi k.π.hom := (Action.forget (ModuleCat.{max u v} R) G).map_epi k.π
  have hsurj : Function.Surjective k.π.hom := (ModuleCat.epi_iff_surjective k.π.hom).1 inferInstance
  rcases hsurj q with ⟨y, rfl⟩
  have hy : IsOpen (MulAction.stabilizer G y : Set G) := hXY.2 y
  have hle :
      MulAction.stabilizer G y ≤ MulAction.stabilizer G (k.π.hom y) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    calc
      g • k.π.hom y = k.π.hom (g • y) := by
        symm
        simpa using congrArg (fun φ ↦ φ.hom y) (k.π.comm g)
      _ = k.π.hom y := by simpa [hg]
  exact Subgroup.isOpen_mono hle hy

/-- Helper for Lemma 19.3.1: the coordinatewise algebraic action on the product module. -/
private abbrev productActionData (X Y : Action (ModuleCat.{max u v} R) G) :
    Action (ModuleCat.{max u v} R) G where
  V := ModuleCat.of R (X.V × Y.V)
  ρ :=
    { toFun := fun g ↦
        ModuleCat.ofHom
          { toFun := fun z ↦ (g • z.1, g • z.2)
            map_add' := fun a b ↦ by
              ext
              · change (X.ρ g).hom (a.1 + b.1) = (X.ρ g).hom a.1 + (X.ρ g).hom b.1
                exact (X.ρ g).hom.map_add _ _
              · change (Y.ρ g).hom (a.2 + b.2) = (Y.ρ g).hom a.2 + (Y.ρ g).hom b.2
                exact (Y.ρ g).hom.map_add _ _
            map_smul' := fun r z ↦ by
              ext
              · change (X.ρ g).hom (r • z.1) = r • (X.ρ g).hom z.1
                exact (X.ρ g).hom.map_smul r z.1
              · change (Y.ρ g).hom (r • z.2) = r • (Y.ρ g).hom z.2
                exact (Y.ρ g).hom.map_smul r z.2 }
      map_one' := by
        apply ModuleCat.hom_ext_iff.mpr
        apply LinearMap.ext
        intro z
        refine Prod.ext ?_ ?_
        · change (X.ρ 1).hom z.1 = z.1
          simpa [Action.ρ_one]
        · change (Y.ρ 1).hom z.2 = z.2
          simpa [Action.ρ_one]
      map_mul' := fun g h ↦ by
        apply ModuleCat.hom_ext_iff.mpr
        apply LinearMap.ext
        intro z
        refine Prod.ext ?_ ?_
        · change (X.ρ (g * h)).hom z.1 = (((X.ρ h) ≫ (X.ρ g)).hom) z.1
          simpa using congrArg (fun φ ↦ φ.hom z.1) (X.ρ.map_mul g h)
        · change (Y.ρ (g * h)).hom z.2 = (((Y.ρ h) ≫ (Y.ρ g)).hom) z.2
          simpa using congrArg (fun φ ↦ φ.hom z.2) (Y.ρ.map_mul g h) }

/-- Helper for Lemma 19.3.1: the first coordinate projection on the product action is
equivariant. -/
private abbrev productActionFst (X Y : Action (ModuleCat.{max u v} R) G) :
    productActionData R G X Y ⟶ X where
  hom := ModuleCat.ofHom (LinearMap.fst R X.V Y.V)
  comm g := by
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro z
    rfl

/-- Helper for Lemma 19.3.1: the second coordinate projection on the product action is
equivariant. -/
private abbrev productActionSnd (X Y : Action (ModuleCat.{max u v} R) G) :
    productActionData R G X Y ⟶ Y where
  hom := ModuleCat.ofHom (LinearMap.snd R X.V Y.V)
  comm g := by
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro z
    rfl

/-- Helper for Lemma 19.3.1: the coordinatewise product action satisfies the open-stabilizer
condition. -/
private theorem product_action_isDiscreteContinuous
    {X Y : Action (ModuleCat.{max u v} R) G}
    (hX : isDiscreteContinuousAction R G X) (hY : isDiscreteContinuousAction R G Y) :
    isDiscreteContinuousAction R G (productActionData R G X Y) := by
  intro z
  have hle :
      MulAction.stabilizer G z.1 ⊓ MulAction.stabilizer G z.2 ≤
        MulAction.stabilizer G z := by
    intro g hg
    have hg₁ : g • z.1 = z.1 := MulAction.mem_stabilizer_iff.mp hg.1
    have hg₂ : g • z.2 = z.2 := MulAction.mem_stabilizer_iff.mp hg.2
    rw [MulAction.mem_stabilizer_iff]
    -- A group element fixing both coordinates fixes the pair.
    exact Prod.ext hg₁ hg₂
  have hxy :
      IsOpen ((MulAction.stabilizer G z.1 ⊓ MulAction.stabilizer G z.2 : Subgroup G) :
        Set G) := by
    simpa using (hX z.1).inter (hY z.2)
  exact open_subgroup_of_le (G := G) hle hxy

/-- Helper for Lemma 19.3.1: the coordinatewise product action is a binary product in the ambient
action category. -/
private noncomputable abbrev productAction_isLimit (X Y : Action (ModuleCat.{max u v} R) G) :
    IsLimit (BinaryFan.mk (productActionFst (R := R) (G := G) X Y)
      (productActionSnd (R := R) (G := G) X Y)) := by
  refine BinaryFan.isLimitMk ?_ ?_ ?_ ?_
  · intro s
    refine
      { hom := ModuleCat.ofHom (LinearMap.prod s.fst.hom.hom s.snd.hom.hom)
        comm := fun g ↦ ?_ }
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro z
    refine Prod.ext ?_ ?_
    · simpa using congrArg (fun φ ↦ φ.hom z) (s.fst.comm g)
    · simpa using congrArg (fun φ ↦ φ.hom z) (s.snd.comm g)
  · intro s
    apply Action.hom_ext
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro z
    rfl
  · intro s
    apply Action.hom_ext
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro z
    rfl
  · intro s m hm₁ hm₂
    apply Action.hom_ext
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro z
    refine Prod.ext ?_ ?_
    · simpa using congrArg (fun k ↦ k.hom.hom z) hm₁
    · simpa using congrArg (fun k ↦ k.hom.hom z) hm₂

/-- Helper for Lemma 19.3.1: the open-stabilizer property is closed under binary products. -/
private instance isDiscreteContinuousAction_closedUnderBinaryProducts :
    (isDiscreteContinuousAction R G).IsClosedUnderBinaryProducts := by
  constructor
  rintro _ ⟨p⟩
  let F := p.diag
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let P : Action (ModuleCat.{max u v} R) G := productActionData R G X Y
  have hP : isDiscreteContinuousAction R G P := by
    -- The source proof only needs the coordinatewise open-stabilizer argument.
    exact product_action_isDiscreteContinuous (R := R) (G := G)
      (X := X) (Y := Y) (p.prop_diag_obj ⟨WalkingPair.left⟩) (p.prop_diag_obj ⟨WalkingPair.right⟩)
  let productFan : BinaryFan X Y :=
    BinaryFan.mk (productActionFst (R := R) (G := G) X Y)
      (productActionSnd (R := R) (G := G) X Y)
  have hProductFan : IsLimit productFan := productAction_isLimit (R := R) (G := G) X Y
  let hProductFan' :
      IsLimit ((Cone.postcompose (diagramIsoPair F).hom).obj p.cone) :=
    (IsLimit.postcomposeHomEquiv (diagramIsoPair F) _).2 p.isLimit
  exact isDiscreteContinuousAction_of_iso (R := R) (G := G)
    (IsLimit.conePointUniqueUpToIso hProductFan' hProductFan).symm hP

/-- Helper for Lemma 19.3.1: the open-stabilizer property is stable under equivariant
isomorphisms. -/
private instance isDiscreteContinuousAction_closedUnderIsomorphisms :
    (isDiscreteContinuousAction R G).IsClosedUnderIsomorphisms where
  of_iso := fun e hX ↦ isDiscreteContinuousAction_of_iso (R := R) (G := G) e hX

instance isDiscreteContinuousAction_closedUnderFiniteProducts :
    (isDiscreteContinuousAction R G).IsClosedUnderFiniteProducts := by
  -- Route correction: the source proof closes finite products through binary products and zero,
  -- so we hand that standard owner-level promotion to `ObjectProperty.IsClosedUnderFiniteProducts`.
  exact .mk'

instance (X : Mod_{R,G}) [TopologicalSpace X.obj.V] [DiscreteTopology X.obj.V] :
    ContinuousSMul G X.obj.V :=
  (isDiscreteContinuousAction_iff_continuousSMul R G X.obj).1 X.property

/-- The algebraic submodule of elements whose stabilizer is open. This is the maximal discrete
continuous subrepresentation of an algebraic action. -/
private def openStabilizerSubmodule (X : Action (ModuleCat.{max u v} R) G) :
    Submodule R X.V where
  carrier := { x | IsOpen (MulAction.stabilizer G x : Set G) }
  zero_mem' := openStabilizerSubmodule_zero_mem (R := R) (G := G) X
  add_mem' := by
    intro x y hx hy
    -- Intersect the two open stabilizers and note that it fixes the sum.
    exact open_stabilizer_add_mem (R := R) (G := G) hx hy
  smul_mem' := by
    intro r x hx
    -- A group element fixing `x` also fixes every scalar multiple of `x`.
    exact open_stabilizer_rsmul_mem (R := R) (G := G) r hx

/-- Helper for Lemma 19.3.1: conjugation carries the stabilizer of `x` to the stabilizer of
`g • x`, so openness is preserved. -/
private theorem openStabilizer_smul_mem (X : Action (ModuleCat.{max u v} R) G)
    (g : G) (x : openStabilizerSubmodule R G X) :
    IsOpen (MulAction.stabilizer G (g • x.1) : Set G) := by
  -- Conjugation identifies the two stabilizers, and conjugation is a homeomorphism of `G`.
  simpa [MulAction.stabilizer_smul_eq_stabilizer_map_conj] using
    open_subgroup_map_conj (G := G) g x.2

/-- Helper for Lemma 19.3.1: equivariant maps send elements with open stabilizer to elements with
open stabilizer. -/
private theorem openStabilizer_map_mem {X Y : Action (ModuleCat.{max u v} R) G}
    (f : X ⟶ Y) (x : openStabilizerSubmodule R G X) :
    (f.hom.hom x.1) ∈ openStabilizerSubmodule R G Y := by
  -- Any group element fixing `x` also fixes its image because `f` is equivariant.
  have hle :
      MulAction.stabilizer G x.1 ≤ MulAction.stabilizer G (f.hom.hom x.1) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    calc
      g • f.hom.hom x.1 = f.hom.hom (g • x.1) := by
        symm
        simpa using congrArg (fun φ ↦ φ.hom x.1) (f.comm g)
      _ = f.hom.hom x.1 := by simpa [hg]
  exact Subgroup.isOpen_mono hle x.2

/-- Helper for Lemma 19.3.1: each group element acts `R`-linearly on the open-stabilizer
submodule. -/
private abbrev openStabilizer_actionLinear (X : Action (ModuleCat.{max u v} R) G) (g : G) :
    openStabilizerSubmodule R G X →ₗ[R] openStabilizerSubmodule R G X where
  toFun := fun x ↦ ⟨g • x.1, openStabilizer_smul_mem R G X g x⟩
  map_add' := fun x y ↦ by
    -- Compare the restricted action on underlying elements and use linearity upstairs.
    apply Subtype.ext
    change g • ((x : X.V) + (y : X.V)) = g • (x : X.V) + g • (y : X.V)
    change (X.ρ g).hom ((x : X.V) + (y : X.V)) =
      (X.ρ g).hom (x : X.V) + (X.ρ g).hom (y : X.V)
    exact (X.ρ g).hom.map_add _ _
  map_smul' := fun r x ↦ by
    -- The restricted action remains `R`-linear because each `X.ρ g` is `R`-linear.
    apply Subtype.ext
    change g • (r • (x : X.V)) = r • (g • (x : X.V))
    change (X.ρ g).hom (r • (x : X.V)) = r • (X.ρ g).hom (x : X.V)
    exact (X.ρ g).hom.map_smul r (x : X.V)

/-- The algebraic action on the open-stabilizer submodule, obtained by restricting the ambient
action. -/
private abbrev openStabilizerActionData (X : Action (ModuleCat.{max u v} R) G) :
    Action (ModuleCat.{max u v} R) G where
  V := ModuleCat.of R (openStabilizerSubmodule R G X)
  ρ :=
    { toFun := fun g ↦
        ModuleCat.ofHom (openStabilizer_actionLinear (R := R) (G := G) X g)
      map_one' := by
        apply ModuleCat.hom_ext
        ext x
        change (1 : G) • (x : X.V) = x
        simpa [Action.ρ_one]
      map_mul' := fun g h ↦ by
        apply ModuleCat.hom_ext
        ext x
        change (g * h) • (x : X.V) = g • (h • (x : X.V))
        exact mul_smul g h (x : X.V)
    }

/-- Helper for Lemma 19.3.1: the restricted open-stabilizer action has the evident `MulAction`
instance on its carrier. -/
private instance openStabilizerActionData_mulAction
    (X : Action (ModuleCat.{max u v} R) G) :
    MulAction G (openStabilizerActionData R G X).V :=
  actionMulAction R G (openStabilizerActionData R G X)

/-- Helper for Lemma 19.3.1: restricting the action does not change element stabilizers. -/
private theorem openStabilizer_stabilizer_eq (X : Action (ModuleCat.{max u v} R) G)
    (x : (openStabilizerActionData R G X).V) :
    MulAction.stabilizer G x = MulAction.stabilizer G (x : X.V) := by
  let A : Action (ModuleCat.{max u v} R) G := openStabilizerActionData R G X
  letI : MulAction G A.V := actionMulAction R G A
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    exact congrArg Subtype.val hg
  · intro hg
    exact Subtype.ext hg

/-- The open-stabilizer coreflection object attached to an algebraic action. -/
private abbrev openStabilizerObj (X : Action (ModuleCat.{max u v} R) G) : Mod_{R,G} where
  obj := openStabilizerActionData R G X
  property := by
    let A : Action (ModuleCat.{max u v} R) G := openStabilizerActionData R G X
    letI : MulAction G A.V := actionMulAction R G A
    intro x
    -- The restricted action has the same stabilizers as the ambient one on each element.
    rw [openStabilizer_stabilizer_eq (R := R) (G := G) X x]
    exact x.2

/-- Helper for Lemma 19.3.1: equivariant maps restrict to linear maps on open-stabilizer
submodules. -/
private abbrev openStabilizer_mapLinear {X Y : Action (ModuleCat.{max u v} R) G} (f : X ⟶ Y) :
    openStabilizerSubmodule R G X →ₗ[R] openStabilizerSubmodule R G Y where
  toFun := fun x ↦ ⟨f.hom.hom x.1, openStabilizer_map_mem R G f x⟩
  map_add' := fun x y ↦ by
    -- The restricted map agrees with `f` on underlying values.
    apply Subtype.ext
    simpa using f.hom.hom.map_add (x : X.V) (y : X.V)
  map_smul' := fun r x ↦ by
    -- Scalar compatibility also comes directly from the ambient linear map.
    apply Subtype.ext
    simpa using f.hom.hom.map_smul r (x : X.V)

/-- The morphism induced on open-stabilizer coreflections by an equivariant map. -/
private abbrev openStabilizerHom {X Y : Action (ModuleCat.{max u v} R) G} (f : X ⟶ Y) :
    (openStabilizerObj R G X).obj ⟶ (openStabilizerObj R G Y).obj where
  hom := ModuleCat.ofHom (openStabilizer_mapLinear (R := R) (G := G) f)
  comm g := by
    apply ModuleCat.hom_ext
    ext x
    simpa using congrArg (fun φ ↦ φ.hom (x : X.V)) (f.comm g)

/-- The open-stabilizer coreflection on algebraic actions. -/
private abbrev openStabilizerFunctor :
    Action (ModuleCat.{max u v} R) G ⥤ Mod_{R,G} where
  obj := openStabilizerObj R G
  map := fun f ↦ ObjectProperty.homMk (openStabilizerHom R G f)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Helper for Lemma 19.3.1: the open-stabilizer coreflection includes back into the ambient
action by forgetting the subtype proof. -/
private abbrev openStabilizerIncl (Y : Action (ModuleCat.{max u v} R) G) :
    (openStabilizerObj R G Y).obj ⟶ Y where
  hom := ModuleCat.ofHom (openStabilizerSubmodule R G Y).subtype
  comm g := by
    apply ModuleCat.hom_ext
    ext y
    rfl

/-- Helper for Lemma 19.3.1: every equivariant map out of a discrete continuous action factors
through the open-stabilizer submodule of the target. -/
private abbrev openStabilizerFactor {X : Mod_{R,G}} {Y : Action (ModuleCat.{max u v} R) G}
    (f : ((ObjectProperty.ι (isDiscreteContinuousAction R G)).obj X ⟶ Y)) :
    X ⟶ openStabilizerObj R G Y :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun x ↦
            ⟨f.hom.hom x, openStabilizer_map_mem (R := R) (G := G) f ⟨x, X.property x⟩⟩
          map_add' := fun _ _ ↦ by
            apply Subtype.ext
            simpa using f.hom.hom.map_add _ _
          map_smul' := fun _ _ ↦ by
            apply Subtype.ext
            simpa using f.hom.hom.map_smul _ _ }
      comm := fun g ↦ by
        apply ModuleCat.hom_ext
        ext x
        simpa using congrArg (fun φ ↦ φ.hom x) (f.comm g) }

/-- Helper for Lemma 19.3.1: the open-stabilizer factorization gives the right-adjoint hom-set
equivalence. -/
private noncomputable def openStabilizer_homEquiv
    (X : Mod_{R,G}) (Y : Action (ModuleCat.{max u v} R) G) :
    (((ObjectProperty.ι (isDiscreteContinuousAction R G)).obj X) ⟶ Y) ≃
      (X ⟶ openStabilizerObj R G Y) where
  toFun := fun f ↦ openStabilizerFactor (R := R) (G := G) f
  invFun := fun f ↦ f.hom ≫ openStabilizerIncl (R := R) (G := G) Y
  left_inv := by
    intro f
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    rfl
  right_inv := by
    intro f
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    rfl

private noncomputable def discreteContActionAdjunction :
    ObjectProperty.ι (isDiscreteContinuousAction R G) ⊣ openStabilizerFunctor R G :=
  -- Route correction: the old unit/counit packaging was transport-heavy; the source proof uses
  -- the universal property of the open-stabilizer submodule, so we package that hom-equivalence
  -- directly.
  Adjunction.mkOfHomEquiv
    { homEquiv := openStabilizer_homEquiv (R := R) (G := G)
      homEquiv_naturality_left_symm := by
        intro X Y Z f φ
        apply Action.hom_ext
        apply ModuleCat.hom_ext
        ext x
        rfl
      homEquiv_naturality_right := by
        intro X Y Z f φ
        apply ObjectProperty.hom_ext
        apply Action.hom_ext
        apply ModuleCat.hom_ext
        ext x
        rfl }

/-- Lemma 19.3.1: for a topological group `G`, the category `Mod_{R,G}` of discrete `R`-modules
with continuous `G`-action has functorial injective embeddings. -/
instance : HasFunctorialInjectiveEmbeddings (Mod_{R,G}) := by
  let modι : Mod_{R,G} ⥤ Action (ModuleCat.{max u v} R) G :=
    ObjectProperty.ι (isDiscreteContinuousAction R G)
  letI : modι.PreservesMonomorphisms :=
    (isDiscreteContinuousAction R G).preservesMonomorphisms_ι_of_isNormalEpiCategory
  exact hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms
    (openStabilizerFunctor R G) modι (discreteContActionAdjunction R G)
    fun X hX ↦ IsZero.of_full_of_faithful_of_isZero modι X hX

end SourceFacing

end CategoryTheory
