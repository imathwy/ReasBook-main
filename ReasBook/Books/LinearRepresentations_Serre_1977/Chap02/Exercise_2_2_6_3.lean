import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

namespace Representation

noncomputable section

section

variable {k : Type*} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W]

-- Proof sketch: the range of an intertwining map `f : σ ⟶ ρ` is a `G`-stable subspace of `V`.
-- Because `σ` is irreducible, any nonzero range is isomorphic to `σ`, so
-- `Submodule.map_le_isotypicComponent` places it inside the `σ`-isotypic component; then evaluate
-- at `w`.
/-- The range of an intertwining map from the irreducible model `σ` into `ρ` lies in the
`σ`-isotypic component. -/
private theorem intertwiningMap_range_le_isotypicComponent
    (ρ : Representation k G V) (σ : Representation k G W) [σ.IsIrreducible]
    (f : σ.IntertwiningMap ρ) :
    f.range.toSubmodule ≤ (ρ.isotypicSubrepresentation σ).toSubmodule := by
  letI : Module (MonoidAlgebra k G) V := ρ.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra k G) W := σ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule (MonoidAlgebra k G) W := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  let fA := (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := σ) (σ := ρ)) f
  letI : IsSimpleModule (MonoidAlgebra k G) (⊤ : Submodule (MonoidAlgebra k G) W) :=
    IsSimpleModule.congr
      (Submodule.topEquiv : (⊤ : Submodule (MonoidAlgebra k G) W) ≃ₗ[MonoidAlgebra k G] W)
  -- Reinterpret the domain as the simple owner module `W` and apply the generic isotypic lemma.
  have hmap :
      LinearMap.range fA ≤
        isotypicComponent (MonoidAlgebra k G) V W := by
    simpa [fA] using
      (Submodule.map_le_isotypicComponent (R := MonoidAlgebra k G) (M := W) (N := V)
        (S := (⊤ : Submodule (MonoidAlgebra k G) W)) (f := fA)).trans_eq
        ((Submodule.topEquiv :
          (⊤ : Submodule (MonoidAlgebra k G) W) ≃ₗ[MonoidAlgebra k G] W).isotypicComponent_eq)
  simpa [Representation.isotypicSubrepresentation, Representation.IntertwiningMap.range, fA] using hmap

/-- Every intertwining map from the irreducible model `σ` into `ρ` lands in the
`σ`-isotypic component. -/
theorem intertwiningMap_apply_mem_isotypicComponent
    (ρ : Representation k G V) (σ : Representation k G W) [σ.IsIrreducible]
    (f : σ.IntertwiningMap ρ) (w : W) :
    f w ∈ (ρ.isotypicSubrepresentation σ).toSubmodule := by
  exact intertwiningMap_range_le_isotypicComponent ρ σ f <|
    (IntertwiningMap.mem_range _ _ f _).2 ⟨w, rfl⟩

-- Proof sketch: use tensor-product induction. On pure tensors `f ⊗ w`, the ambient evaluation map
-- is `f w`, which lies in the isotypic component by
-- `intertwiningMap_apply_mem_isotypicComponent`.
private theorem isotypicTensorEvaluation_mem
    (ρ : Representation k G V) (σ : Representation k G W) [σ.IsIrreducible]
    (x : σ.IntertwiningMap ρ ⊗[k] W) :
    TensorProduct.uncurry (.id k) _ _ _ (IntertwiningMap.toLinearMapl σ ρ) x ∈
      (ρ.isotypicSubrepresentation σ).toSubmodule := by
  -- Reduce to pure tensors, where the claim is exactly that each intertwiner lands in `V_i`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simpa using
      ((ρ.isotypicSubrepresentation σ).toSubmodule.zero_mem :
        (0 : V) ∈ (ρ.isotypicSubrepresentation σ).toSubmodule)
  · intro f w
    simpa using intertwiningMap_apply_mem_isotypicComponent ρ σ f w
  · intro x y hx hy
    simpa using (ρ.isotypicSubrepresentation σ).toSubmodule.add_mem hx hy

/-- Helper for Exercise 2-2.6-3: tensor evaluation commutes with the tensor-product action of the
trivial representation on `Hom_G(σ, ρ)` and the given action on `σ`. -/
private theorem isotypicTensorEvaluation_isIntertwining
    (ρ : Representation k G V) (σ : Representation k G W) [σ.IsIrreducible] :
    ∀ g x,
      TensorProduct.uncurry (.id k) _ _ _ (IntertwiningMap.toLinearMapl σ ρ)
        (((trivial k G (σ.IntertwiningMap ρ)).tprod σ) g x) =
      ρ g (TensorProduct.uncurry (.id k) _ _ _ (IntertwiningMap.toLinearMapl σ ρ) x) := by
  intro g x
  -- On pure tensors this is exactly the intertwining identity `f (σ g w) = ρ g (f w)`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro f w
    simpa [Representation.tprod_apply] using congr($(f.isIntertwining' g) w)
  · intro x y hx hy
    simpa using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Exercise 2-2.6-3: restricting the codomain of an intertwining map to a stable
subrepresentation preserves equivariance. -/
private theorem intertwiningMap_codRestrict_isIntertwining
    {X : Type*} [AddCommGroup X] [Module k X]
    (τ : Representation k G X) (ρ : Representation k G V) (U : Subrepresentation ρ)
    (f : τ.IntertwiningMap ρ) (hf : ∀ x, f x ∈ U.toSubmodule) :
    ∀ g x,
      (f.toLinearMap.codRestrict U.toSubmodule hf) (τ g x) =
        U.toRepresentation g ((f.toLinearMap.codRestrict U.toSubmodule hf) x) := by
  intro g x
  -- The codomain restriction changes only the target type, not the underlying evaluation.
  ext
  simpa using congr($(f.isIntertwining' g) x)

/-- The tensor-evaluation map, bundled as an intertwining map to the `σ`-isotypic
subrepresentation. -/
def isotypicTensorEvaluation
    (ρ : Representation k G V) (σ : Representation k G W) [σ.IsIrreducible] :
    ((trivial k G (σ.IntertwiningMap ρ)).tprod σ).IntertwiningMap
      (ρ.isotypicSubrepresentation σ).toRepresentation :=
  let τ := (trivial k G (σ.IntertwiningMap ρ)).tprod σ
  let Vσ := ρ.isotypicSubrepresentation σ
  let eval : σ.IntertwiningMap ρ ⊗[k] W →ₗ[k] V :=
    TensorProduct.uncurry (.id k) _ _ _ (IntertwiningMap.toLinearMapl σ ρ)
  let f : τ.IntertwiningMap ρ :=
    eval.intertwiningMap_of_isIntertwiningMap τ ρ (isotypicTensorEvaluation_isIntertwining ρ σ)
  let fVσ :=
    f.toLinearMap.codRestrict Vσ.toSubmodule (isotypicTensorEvaluation_mem ρ σ)
  fVσ.intertwiningMap_of_isIntertwiningMap τ Vσ.toRepresentation
    (intertwiningMap_codRestrict_isIntertwining τ ρ Vσ f (isotypicTensorEvaluation_mem ρ σ))

section

variable {ι : Type x}

local instance instDecidableEqIotaChap2263Basis : DecidableEq ι := Classical.decEq ι

-- Proof sketch: every summand map `h i : W → V` lands in the isotypic component by
-- `intertwiningMap_apply_mem_isotypicComponent`. The universal property of the direct sum
-- then shows that the whole evaluation map lands there as well.
private theorem familyDirectSumEvaluation_mem
    (ρ : Representation k G V) (σ : Representation k G W) [σ.IsIrreducible]
    (h : ι → σ.IntertwiningMap ρ)
    (x : DirectSum ι (fun _ : ι ↦ W)) :
    DirectSum.toModule k ι V (fun i ↦ (h i).toLinearMap) x ∈
      (ρ.isotypicSubrepresentation σ).toSubmodule := by
  -- Reduce to one summand at a time; each coordinate map already lands in the isotypic component.
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simpa using
      ((ρ.isotypicSubrepresentation σ).toSubmodule.zero_mem :
        (0 : V) ∈ (ρ.isotypicSubrepresentation σ).toSubmodule)
  · intro i w
    rw [← DirectSum.lof_eq_of (R := k) (ι := ι) (M := fun _ : ι ↦ W) i w]
    simpa [DirectSum.toModule_lof] using intertwiningMap_apply_mem_isotypicComponent ρ σ (h i) w
  · intro x y hx hy
    simpa using (ρ.isotypicSubrepresentation σ).toSubmodule.add_mem hx hy

/-- Helper for Exercise 2-2.6-3: the direct-sum evaluation map commutes with the external direct
sum action. -/
private theorem familyDirectSumEvaluation_isIntertwining
    (ρ : Representation k G V) (σ : Representation k G W) [σ.IsIrreducible]
    (h : ι → σ.IntertwiningMap ρ) :
    ∀ g x,
      DirectSum.toModule k ι V (fun i ↦ (h i).toLinearMap)
        ((directSum fun _ : ι ↦ σ) g x) =
      ρ g (DirectSum.toModule k ι V (fun i ↦ (h i).toLinearMap) x) := by
  intro g x
  -- On generators `lof i w`, this is the intertwining identity for the `i`-th coordinate map.
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro i w
    rw [← DirectSum.lof_eq_of (R := k) (ι := ι) (M := fun _ : ι ↦ W) i w]
    simpa [Representation.directSum, DirectSum.toModule_lof] using
      (Representation.IntertwiningMap.isIntertwining (ρ := σ) (σ := ρ) (f := h i) g w)
  · intro x y hx hy
    simpa using congrArg₂ HAdd.hAdd hx hy

/-- The direct-sum evaluation map, bundled as an intertwining map to the `σ`-isotypic
subrepresentation. -/
def familyDirectSumEvaluation
    (ρ : Representation k G V) (σ : Representation k G W) [σ.IsIrreducible]
    (h : ι → σ.IntertwiningMap ρ) :
    (directSum fun _ : ι ↦ σ).IntertwiningMap
      (ρ.isotypicSubrepresentation σ).toRepresentation :=
  let τ := directSum fun _ : ι ↦ σ
  let Vσ := ρ.isotypicSubrepresentation σ
  let eval : DirectSum ι (fun _ : ι ↦ W) →ₗ[k] V :=
    DirectSum.toModule k ι V fun i ↦ (h i).toLinearMap
  let f : τ.IntertwiningMap ρ :=
    eval.intertwiningMap_of_isIntertwiningMap τ ρ (familyDirectSumEvaluation_isIntertwining ρ σ h)
  let fVσ := f.toLinearMap.codRestrict Vσ.toSubmodule (familyDirectSumEvaluation_mem ρ σ h)
  fVσ.intertwiningMap_of_isIntertwiningMap τ Vσ.toRepresentation (fun g x ↦ by
    exact intertwiningMap_codRestrict_isIntertwining τ ρ Vσ f
      (familyDirectSumEvaluation_mem ρ σ h) g x)

end

end

section

variable {G : Type u} [Group G]
variable {K : Type*} [Field K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

section

variable [Finite G]

local instance instFintypeGChap2263Basis : Fintype G := Fintype.ofFinite G

section

variable {ι : Type x} [DecidableEq ι]

-- Proof sketch: package a `K[G]`-linear equivalence of owner modules as the underlying linear
-- equivalence of an intertwining equivalence between `Representation.ofModule' M` and the target
-- representation.
/-- Helper for Exercise 2-2.6-3: a `K[G]`-linear equivalence from an owner module `M` to the owner
module of a representation upgrades to an isomorphism of representations. -/
private theorem nonempty_equiv_of_module_linearEquiv
    {M : Type*} [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [IsScalarTower K (MonoidAlgebra K G) M]
    (τ : Representation K G W) (e : M ≃ₗ[MonoidAlgebra K G] τ.asModule) :
    Nonempty ((Representation.ofModule' (k := K) (G := G) M).Equiv τ) := by
  -- Forget the owner-module equivalence to a `K`-linear equivalence and check equivariance on the
  -- generating group-algebra elements `single g 1`.
  refine ⟨Representation.Equiv.mk (e.restrictScalars K) ?_⟩
  intro g
  ext m
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  show e (((Representation.ofModule' (k := K) (G := G) M) g) m) = (τ g) (e m)
  calc
    e (((Representation.ofModule' (k := K) (G := G) M) g) m)
        = e ((MonoidAlgebra.single g (1 : K)) • m) := by
            rfl
    _ = (MonoidAlgebra.single g (1 : K)) • e m := by
          exact e.map_smulₛₗ (MonoidAlgebra.single g (1 : K)) m
    _ = (τ g) (τ.asModuleEquiv (e m)) := by
          simpa using
            (Representation.single_smul (ρ := τ) (t := (1 : K)) (g := g) (v := e m))
    _ = (τ g) (e m) := by
          rfl

-- Proof sketch: `Subrepresentation.toRepresentation` is the same representation as
-- `Representation.ofModule'` on the underlying owner submodule.
/-- Helper for Exercise 2-2.6-3: the representation attached to a `G`-stable submodule agrees with
the `Representation.ofModule'` structure on the same owner module. -/
private theorem subrepresentation_equiv_ofModule'
    (ρ : Representation K G V) (U : Subrepresentation ρ) :
    Nonempty
      ((Representation.ofModule' (k := K) (G := G) U.asSubmodule).Equiv U.toRepresentation) := by
  -- The two carrier types are the same subtype, viewed once inside `ρ.asModule` and once inside
  -- `V`, so the underlying linear equivalence is the identity on elements.
  refine ⟨Representation.Equiv.mk ?_ ?_⟩
  · refine
      { toFun := fun x ↦ ⟨x.1, x.2⟩
        invFun := fun x ↦ ⟨x.1, x.2⟩
        left_inv := fun x ↦ by
          ext
          rfl
        right_inv := fun x ↦ by
          ext
          rfl
        map_add' := fun x y ↦ by
          ext
          rfl
        map_smul' := fun a x ↦ by
          ext
          rfl }
  · intro g
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, hx⟩
    -- Unfold the owner-module action on the subtype and compare it with the restricted action.
    have haction : MonoidAlgebra.single g (1 : K) • (⟨x, hx⟩ : U.asSubmodule) =
        ((ρ g).restrict (U.apply_mem_toSubmodule g)) ⟨x, hx⟩ := by
      ext
      simp only [SetLike.mk_smul_mk, single_smul, one_smul, LinearMap.restrict_coe_apply]
      rfl
    simpa [Representation.ofModule', Subrepresentation.toRepresentation] using haction

-- Proof sketch: the owner `K[G]`-module of the `σ`-isotypic component is semisimple and
-- isotypic of type `W`, so `IsIsotypicOfType.linearEquiv_finsupp` identifies it with a direct sum
-- of copies of `W`; the previous helper then upgrades that owner equivalence to a representation
-- equivalence.
/-- Helper for Exercise 2-2.6-3: the `σ`-isotypic component is equivariantly a direct sum of
copies of `σ`. -/
private theorem exists_equiv_directSum_isotypicComponent
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible] :
    ∃ ι : Type v,
      Nonempty ((directSum fun _ : ι ↦ σ).Equiv (ρ.isotypicSubrepresentation σ).toRepresentation) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module (MonoidAlgebra K G) V := ρ.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra K G) W := σ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower K (MonoidAlgebra K G) W := by
    simpa using σ.instIsScalarTowerMonoidAlgebraAsModule
  letI : IsSimpleModule (MonoidAlgebra K G) W := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  let U := (ρ.isotypicSubrepresentation σ).asSubmodule
  letI : IsScalarTower K (MonoidAlgebra K G) U := U.isScalarTower
  -- Route correction: first build the owner-module decomposition of the isotypic component, then
  -- upgrade it to a representation equivalence by comparing both sides with `Representation.ofModule'`.
  have hIso : IsIsotypicOfType (MonoidAlgebra K G) U W := by
    simpa [U, Representation.isotypicSubrepresentation] using
      (IsIsotypicOfType.isotypicComponent (R := MonoidAlgebra K G) (M := V) (S := W))
  obtain ⟨ι, ⟨eU⟩⟩ := hIso.linearEquiv_finsupp
  classical
  letI : DecidableEq ι := Classical.decEq ι
  letI : Module (MonoidAlgebra K G) (ι →₀ W) := Finsupp.module ι W
  letI : IsScalarTower K (MonoidAlgebra K G) (ι →₀ W) := Finsupp.isScalarTower ι W
  have hFinsupp :
      Nonempty ((Representation.ofModule' (k := K) (G := G) (ι →₀ W)).Equiv
        (directSum fun _ : ι ↦ σ)) := by
    -- The owner action on finitely supported functions is pointwise, matching the direct-sum action.
    refine ⟨Representation.Equiv.mk ((finsuppLEquivDirectSum K W ι).restrictScalars K) ?_⟩
    intro g
    apply LinearMap.ext
    intro m
    ext i
    change
      ((finsuppLEquivDirectSum K W ι)
          (((Representation.ofModule' (k := K) (G := G) (ι →₀ W)) g) m)) i =
        ((directSum fun _ : ι ↦ σ) g ((finsuppLEquivDirectSum K W ι) m)) i
    rw [finsuppLEquivDirectSum_apply]
    change (σ.asAlgebraHom (MonoidAlgebra.single g (1 : K))) (m i) = (σ g) (m i)
    simp [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  have hOwner :
      Nonempty ((Representation.ofModule' (k := K) (G := G) (ι →₀ W)).Equiv
        (Representation.ofModule' (k := K) (G := G) U)) := by
    -- The owner linear equivalence `eU` is already `K[G]`-linear, so it directly yields an
    -- equivalence between the associated `Representation.ofModule'` structures.
    refine ⟨Representation.Equiv.mk (eU.symm.restrictScalars K) ?_⟩
    intro g
    apply LinearMap.ext
    intro m
    show eU.symm (((Representation.ofModule' (k := K) (G := G) (ι →₀ W)) g) m) =
      ((Representation.ofModule' (k := K) (G := G) U) g) (eU.symm m)
    calc
      eU.symm (((Representation.ofModule' (k := K) (G := G) (ι →₀ W)) g) m)
          = eU.symm ((MonoidAlgebra.single g (1 : K)) • m) := by
              rfl
      _ = (MonoidAlgebra.single g (1 : K)) • eU.symm m := by
            exact eU.symm.map_smulₛₗ (MonoidAlgebra.single g (1 : K)) m
      _ = ((Representation.ofModule' (k := K) (G := G) U) g) (eU.symm m) := by
            rfl
  rcases hFinsupp with ⟨eF⟩
  rcases hOwner with ⟨eOwner⟩
  rcases subrepresentation_equiv_ofModule' (ρ := ρ) (U := ρ.isotypicSubrepresentation σ) with ⟨eSub⟩
  exact ⟨ι, ⟨eF.symm.trans (eOwner.trans eSub)⟩⟩

-- Proof sketch: the inclusion of a single summand into the external direct sum respects the
-- diagonal `G`-action because that action is coordinatewise.
/-- Helper for Exercise 2-2.6-3: the inclusion of one copy of `σ` into the external direct sum of
copies of `σ` is an intertwining map. -/
private theorem directSum_lof_isIntertwining
    (σ : Representation K G W) (i : ι) :
    ∀ g x,
      (DirectSum.lof K ι (fun _ : ι ↦ W) i) (σ g x) =
        (directSum fun _ : ι ↦ σ) g ((DirectSum.lof K ι (fun _ : ι ↦ W) i) x) := by
  intro g x
  -- Check equality coordinatewise after expanding the direct-sum action into `DirectSum.lmap`.
  rw [Representation.directSum]
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

-- Proof sketch: the projection to one summand of the external direct sum also respects the
-- diagonal action, again because the action is coordinatewise.
/-- Helper for Exercise 2-2.6-3: the coordinate projection from the external direct sum of copies
of `σ` to one copy of `σ` is an intertwining map. -/
private theorem directSum_component_isIntertwining
    (σ : Representation K G W) (i : ι) :
    ∀ g x,
      DirectSum.component K ι (fun _ : ι ↦ W) i ((directSum fun _ : ι ↦ σ) g x) =
        σ g (DirectSum.component K ι (fun _ : ι ↦ W) i x) := by
  intro g x
  -- The external direct-sum action is `DirectSum.lmap`, so the `i`-th coordinate is acted on by
  -- exactly `σ g`.
  rw [Representation.directSum]
  rfl

/-- Helper for Exercise 2-2.6-3: an irreducible representation has nontrivial carrier. -/
private theorem nontrivial_carrier_of_isIrreducible
    (σ : Representation K G W) [σ.IsIrreducible] : Nontrivial W := by
  -- If the carrier were trivial, the bottom and top subrepresentations would coincide, contrary
  -- to simplicity.
  by_contra hW
  letI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
  have hbot_top :
      (⊥ : Subrepresentation σ).toSubmodule = (⊤ : Subrepresentation σ).toSubmodule := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top <| Subrepresentation.toSubmodule_injective hbot_top

/-- Helper for Exercise 2-2.6-3: the `i`-th summand inclusion into the external direct sum is a
bundled intertwining map. -/
private noncomputable def directSum_lof_intertwining
    (σ : Representation K G W) (i : ι) :
    σ.IntertwiningMap (directSum fun _ : ι ↦ σ) :=
  (DirectSum.lof K ι (fun _ : ι ↦ W) i).intertwiningMap_of_isIntertwiningMap
    σ (directSum fun _ : ι ↦ σ) (directSum_lof_isIntertwining (σ := σ) i)

/-- Helper for Exercise 2-2.6-3: the `i`-th coordinate projection from the external direct sum is
a bundled intertwining map. -/
private noncomputable def directSum_component_intertwining
    (σ : Representation K G W) (i : ι) :
    (directSum fun _ : ι ↦ σ).IntertwiningMap σ :=
  (DirectSum.component K ι (fun _ : ι ↦ W) i).intertwiningMap_of_isIntertwiningMap
    (directSum fun _ : ι ↦ σ) σ (directSum_component_isIntertwining (σ := σ) i)

/-- Helper for Exercise 2-2.6-3: the inclusion of the `σ`-isotypic component into `ρ` is a
bundled intertwining map. -/
private noncomputable def isotypicSubrepresentation_subtype_intertwining
    (ρ : Representation K G V) (σ : Representation K G W) :
    (ρ.isotypicSubrepresentation σ).toRepresentation.IntertwiningMap ρ :=
  (ρ.isotypicSubrepresentation σ).toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
    (ρ.isotypicSubrepresentation σ).toRepresentation ρ fun g x ↦ by
      rfl

/-- Helper for Exercise 2-2.6-3: every intertwining map into `ρ` canonically corestricts to the
`σ`-isotypic component. -/
private noncomputable def intertwiningMap_codRestrict_isotypic
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible] :
    σ.IntertwiningMap ρ →ₗ[K] σ.IntertwiningMap (ρ.isotypicSubrepresentation σ).toRepresentation where
  toFun := fun f ↦
    let fVσ := f.toLinearMap.codRestrict (ρ.isotypicSubrepresentation σ).toSubmodule
      (intertwiningMap_apply_mem_isotypicComponent ρ σ f)
    fVσ.intertwiningMap_of_isIntertwiningMap σ (ρ.isotypicSubrepresentation σ).toRepresentation
      (intertwiningMap_codRestrict_isIntertwining σ ρ (ρ.isotypicSubrepresentation σ) f
        (intertwiningMap_apply_mem_isotypicComponent ρ σ f))
  map_add' := by
    intro f g
    -- Corestriction is pointwise addition because both maps already land in the same submodule.
    apply Representation.IntertwiningMap.ext
    ext w
    rfl
  map_smul' := by
    intro a f
    -- Scalar multiplication also commutes with the codomain restriction.
    apply Representation.IntertwiningMap.ext
    ext w
    rfl

/-- Helper for Exercise 2-2.6-3: the `i`-th Schur scalar of an intertwining map
`σ ⟶ ⨁ i, σ`. -/
private noncomputable def intertwiningMap_into_directSum_coeff
    (σ : Representation K G W) [σ.IsIrreducible]
    (g : σ.IntertwiningMap (directSum fun _ : ι ↦ σ)) (i : ι) : K :=
  letI : FiniteDimensional K W := IsIrreducible.finiteDimensional_of_finite σ
  Classical.choose <|
    intertwiningMap_eq_smul_id (ρ := σ)
      ((directSum_component_intertwining (σ := σ) i).comp g)

/-- Helper for Exercise 2-2.6-3: the `i`-th coordinate of an intertwining map
`σ ⟶ ⨁ i, σ` is the corresponding Schur scalar times the identity. -/
private theorem directSum_component_comp_eq_coeff_smul_id
    (σ : Representation K G W) [σ.IsIrreducible]
    (g : σ.IntertwiningMap (directSum fun _ : ι ↦ σ)) (i : ι) :
    (directSum_component_intertwining (σ := σ) i).comp g =
      intertwiningMap_into_directSum_coeff (σ := σ) g i • 1 := by
  -- This is exactly the scalar description supplied by Schur's lemma on each coordinate.
  letI : FiniteDimensional K W := IsIrreducible.finiteDimensional_of_finite σ
  simpa [intertwiningMap_into_directSum_coeff] using
    (Classical.choose_spec <|
      intertwiningMap_eq_smul_id (ρ := σ)
        ((directSum_component_intertwining (σ := σ) i).comp g))

/-- Helper for Exercise 2-2.6-3: a scalar multiple of the identity intertwiner is determined by
its scalar. -/
private theorem smul_id_eq_smul_id
    (σ : Representation K G W) [σ.IsIrreducible]
    {a b : K}
    (h : a • (1 : σ.IntertwiningMap σ) = b • 1) :
    a = b := by
  letI : Nontrivial W := nontrivial_carrier_of_isIrreducible (σ := σ)
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  -- Evaluate at one nonzero vector to reduce equality of homotheties to equality of scalars.
  have hw : a • w0 = b • w0 := by
    simpa [Representation.IntertwiningMap.smul_apply] using
      congrArg (fun f : σ.IntertwiningMap σ ↦ f w0) h
  have hsub : (a - b) • w0 = 0 := by
    calc
      (a - b) • w0 = a • w0 - b • w0 := by simp [sub_smul]
      _ = 0 := by rw [hw, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hw0)

/-- Helper for Exercise 2-2.6-3: the Schur coefficients of an intertwining map
`σ ⟶ ⨁ i, σ` have finite support. -/
private theorem intertwiningMap_into_directSum_coeff_support_finite
    (σ : Representation K G W) [σ.IsIrreducible]
    (g : σ.IntertwiningMap (directSum fun _ : ι ↦ σ)) :
    (Function.support (intertwiningMap_into_directSum_coeff (σ := σ) g)).Finite := by
  classical
  letI : Nontrivial W := nontrivial_carrier_of_isIrreducible (σ := σ)
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  -- Nonzero Schur coefficients force a nonzero coordinate of `g w0`, so the coefficient
  -- support is contained in the finite support of the direct-sum vector `g w0`.
  refine Set.Finite.subset (Finset.finite_toSet (g w0).support) ?_
  intro i hi
  have hcoord :
      DirectSum.component K ι (fun _ : ι ↦ W) i (g w0) =
        intertwiningMap_into_directSum_coeff (σ := σ) g i • w0 := by
    simpa [Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.smul_apply] using
      congrArg (fun f : σ.IntertwiningMap σ ↦ f w0)
        (directSum_component_comp_eq_coeff_smul_id (σ := σ) g i)
  have hcoeff : intertwiningMap_into_directSum_coeff (σ := σ) g i ≠ 0 :=
    Function.mem_support.mp hi
  have hcoord_ne : DirectSum.component K ι (fun _ : ι ↦ W) i (g w0) ≠ 0 := by
    rw [hcoord]
    exact smul_ne_zero hcoeff hw0
  simpa using hcoord_ne

/-- Helper for Exercise 2-2.6-3: package the Schur coefficients of an intertwining map
`σ ⟶ ⨁ i, σ` as a finitely supported function. -/
private noncomputable def intertwiningMap_into_directSum_coeffs
    (σ : Representation K G W) [σ.IsIrreducible]
    (g : σ.IntertwiningMap (directSum fun _ : ι ↦ σ)) :
    ι →₀ K :=
  Finsupp.ofSupportFinite
    (intertwiningMap_into_directSum_coeff (σ := σ) g)
    (intertwiningMap_into_directSum_coeff_support_finite (σ := σ) g)

/-- Helper for Exercise 2-2.6-3: reassemble a finitely supported scalar family into the
corresponding intertwining map `σ ⟶ ⨁ i, σ`. -/
private noncomputable def intertwiningMap_into_directSum_fromFinsupp
    (σ : Representation K G W) :
    (ι →₀ K) →ₗ[K] σ.IntertwiningMap (directSum fun _ : ι ↦ σ) :=
  Finsupp.linearCombination K (fun i ↦ directSum_lof_intertwining (σ := σ) i)

/-- Helper for Exercise 2-2.6-3: the coordinate of the reconstructed direct-sum intertwiner is the
expected scalar multiple of the identity. -/
private theorem directSum_component_comp_fromFinsupp
    (σ : Representation K G W) [σ.IsIrreducible]
    (c : ι →₀ K) (i : ι) :
    (directSum_component_intertwining (σ := σ) i).comp
        (intertwiningMap_into_directSum_fromFinsupp (σ := σ) c) =
      c i • 1 := by
  apply Representation.IntertwiningMap.ext
  ext w
  -- The coordinate formula is linear in `c`, so it suffices to check the zero and singleton cases.
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp [intertwiningMap_into_directSum_fromFinsupp, directSum_component_intertwining]
  · intro c d hc hd
    simpa [intertwiningMap_into_directSum_fromFinsupp, map_add, add_smul] using
      congrArg₂ HAdd.hAdd hc hd
  · intro j a
    rw [intertwiningMap_into_directSum_fromFinsupp, Finsupp.linearCombination_single]
    by_cases h : j = i
    · subst h
      simp [directSum_lof_intertwining,
        directSum_component_intertwining]
    · calc
        ((directSum_component_intertwining (σ := σ) i).comp
            (a • directSum_lof_intertwining (σ := σ) j)).toLinearMap w
            = DirectSum.component K ι (fun _ : ι ↦ W) i
                (a • ((DirectSum.lof K ι (fun _ : ι ↦ W) j) w)) := by
                  simp [directSum_lof_intertwining, directSum_component_intertwining]
        _ = a • DirectSum.component K ι (fun _ : ι ↦ W) i
              ((DirectSum.lof K ι (fun _ : ι ↦ W) j) w) := by
                simp
        _ = a • 0 := by
              rw [DirectSum.component.of]
              simp [h]
        _ = 0 := by simp
        _ = ((Finsupp.single j a) i • (1 : σ.IntertwiningMap σ)).toLinearMap w := by
              simp [h]

/-- Helper for Exercise 2-2.6-3: taking Schur coefficients of a finitely supported sum of summand
inclusions recovers the original coefficient at each index. -/
private theorem intertwiningMap_into_directSum_coeff_fromFinsupp
    (σ : Representation K G W) [σ.IsIrreducible]
    (c : ι →₀ K) (i : ι) :
    intertwiningMap_into_directSum_coeff (σ := σ)
      (intertwiningMap_into_directSum_fromFinsupp (σ := σ) c) i = c i := by
  -- Both coordinate computations describe the same endomorphism of `σ`, so Schur's scalar is
  -- unique.
  exact smul_id_eq_smul_id (σ := σ) <|
    (directSum_component_comp_eq_coeff_smul_id
      (σ := σ) (g := intertwiningMap_into_directSum_fromFinsupp (σ := σ) c) i).symm.trans
      (directSum_component_comp_fromFinsupp (σ := σ) c i)

/-- Helper for Exercise 2-2.6-3: the coefficient packaging map is a left inverse to the finite
linear combination of summand inclusions. -/
private theorem intertwiningMap_into_directSum_coeffs_fromFinsupp
    (σ : Representation K G W) [σ.IsIrreducible]
    (c : ι →₀ K) :
    intertwiningMap_into_directSum_coeffs (σ := σ)
      (intertwiningMap_into_directSum_fromFinsupp (σ := σ) c) = c := by
  ext i
  -- Evaluate both finitely supported functions at `i`.
  rw [intertwiningMap_into_directSum_coeffs, Finsupp.ofSupportFinite_coe]
  exact intertwiningMap_into_directSum_coeff_fromFinsupp (σ := σ) c i

/-- Helper for Exercise 2-2.6-3: every intertwining map `σ ⟶ ⨁ i, σ` is the finite linear
combination of the summand inclusions given by its Schur-coordinate coefficients. -/
private theorem intertwiningMap_into_directSum_eq_finsupp_sum_lof
    (σ : Representation K G W) [σ.IsIrreducible]
    (g : σ.IntertwiningMap (directSum fun _ : ι ↦ σ)) :
    intertwiningMap_into_directSum_fromFinsupp (σ := σ)
        (intertwiningMap_into_directSum_coeffs (σ := σ) g) = g := by
  apply Representation.IntertwiningMap.ext
  ext w i
  -- Compare both direct-sum maps after projecting to the `i`-th coordinate.
  have hleft :=
    congrArg (fun f : σ.IntertwiningMap σ ↦ f w)
      (directSum_component_comp_fromFinsupp (σ := σ)
        (intertwiningMap_into_directSum_coeffs (σ := σ) g) i)
  have hright :=
    congrArg (fun f : σ.IntertwiningMap σ ↦ f w)
      (directSum_component_comp_eq_coeff_smul_id (σ := σ) g i)
  simpa [intertwiningMap_into_directSum_coeffs, Finsupp.ofSupportFinite_coe,
    Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.smul_apply] using
    hleft.trans hright.symm

/-- Helper for Exercise 2-2.6-3: `Hom_G(σ, ⨁ i, σ)` is freely generated by the summand inclusion
maps, with basis indexed by the direct-sum summands. -/
private noncomputable def intertwiningMap_into_directSum_linearEquiv_finsupp
    (σ : Representation K G W) [σ.IsIrreducible] :
    (ι →₀ K) ≃ₗ[K] σ.IntertwiningMap (directSum fun _ : ι ↦ σ) :=
  LinearEquiv.ofBijective (intertwiningMap_into_directSum_fromFinsupp (σ := σ)) <| by
    constructor
    · intro c d hcd
      have hcoeffs :=
        congrArg (intertwiningMap_into_directSum_coeffs (σ := σ)) hcd
      simpa [intertwiningMap_into_directSum_coeffs_fromFinsupp] using hcoeffs
    · intro g
      refine ⟨intertwiningMap_into_directSum_coeffs (σ := σ) g, ?_⟩
      exact intertwiningMap_into_directSum_eq_finsupp_sum_lof (σ := σ) g

/-- Helper for Exercise 2-2.6-3: the `i`-th basis vector of `ι →₀ K` corresponds to the `i`-th
summand inclusion `σ ⟶ ⨁ i, σ`. -/
private theorem intertwiningMap_into_directSum_linearEquiv_finsupp_single
    (σ : Representation K G W) [σ.IsIrreducible]
    (i : ι) :
    intertwiningMap_into_directSum_linearEquiv_finsupp (σ := σ) (Finsupp.single i 1) =
      directSum_lof_intertwining (σ := σ) i := by
  -- The inverse basis vector is exactly the one-term linear combination supported at `i`.
  simp [intertwiningMap_into_directSum_linearEquiv_finsupp,
    intertwiningMap_into_directSum_fromFinsupp]

/-- Helper for Exercise 2-2.6-3: the summand inclusions `σ ⟶ ⨁ i, σ` are linearly independent. -/
private theorem directSum_lof_intertwining_linearIndependent
    (σ : Representation K G W) [σ.IsIrreducible] :
    LinearIndependent K (fun i : ι ↦ directSum_lof_intertwining (σ := σ) i) := by
  have hsingle :
      LinearIndependent K (fun i : ι ↦ (Finsupp.single i (1 : K) : ι →₀ K)) := by
    simpa [Finsupp.coe_basisSingleOne] using
      (Finsupp.basisSingleOne (R := K) (ι := ι)).linearIndependent
  have hker :
      (intertwiningMap_into_directSum_linearEquiv_finsupp (σ := σ)).toLinearMap.ker =
        (⊥ : Submodule K (ι →₀ K)) := by
    simpa using LinearEquiv.ker
      (intertwiningMap_into_directSum_linearEquiv_finsupp (σ := σ))
  -- The direct-sum summand inclusions are the images of the standard `Finsupp` basis vectors.
  convert
    hsingle.map'
      (intertwiningMap_into_directSum_linearEquiv_finsupp (σ := σ)).toLinearMap hker using 1
  funext i
  simpa [intertwiningMap_into_directSum_linearEquiv_finsupp_single]

/-- Helper for Exercise 2-2.6-3: postcomposition with an equivalence of representations induces a
linear equivalence on intertwining spaces out of a fixed source representation. -/
private noncomputable def intertwiningMap_postcompose_linearEquiv
    {X : Type*} [AddCommGroup X] [Module K X]
    {Y : Type*} [AddCommGroup Y] [Module K Y]
    {Z : Type*} [AddCommGroup Z] [Module K Z]
    (τ : Representation K G X) (υ : Representation K G Y) (ω : Representation K G Z)
    (e : υ.Equiv ω) :
    τ.IntertwiningMap υ ≃ₗ[K] τ.IntertwiningMap ω where
  toFun := fun f ↦ e.toIntertwiningMap.comp f
  invFun := fun f ↦ e.symm.toIntertwiningMap.comp f
  left_inv := by
    intro f
    -- Compose with `e` and then `e.symm`; the underlying linear maps reduce by reflexivity.
    apply Representation.IntertwiningMap.ext
    ext x
    simp [Representation.IntertwiningMap.comp_apply]
  right_inv := by
    intro f
    -- The same argument applies in the reverse direction.
    apply Representation.IntertwiningMap.ext
    ext x
    simp [Representation.IntertwiningMap.comp_apply]
  map_add' := by
    intro f g
    -- Postcomposition is pointwise linear.
    apply Representation.IntertwiningMap.ext
    ext x
    simp [Representation.IntertwiningMap.comp_apply]
  map_smul' := by
    intro a f
    -- Scalar multiplication commutes with postcomposition.
    apply Representation.IntertwiningMap.ext
    ext x
    simp [Representation.IntertwiningMap.comp_apply]

/-- Helper for Exercise 2-2.6-3: maps into the `σ`-isotypic component are equivalent to maps into
the ambient representation, because every map into `ρ` already lands in that component. -/
private noncomputable def intertwiningMap_isotypicSubrepresentation_linearEquiv
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible] :
    σ.IntertwiningMap (ρ.isotypicSubrepresentation σ).toRepresentation ≃ₗ[K]
      σ.IntertwiningMap ρ where
  toFun := fun f ↦ (isotypicSubrepresentation_subtype_intertwining (ρ := ρ) (σ := σ)).comp f
  invFun := intertwiningMap_codRestrict_isotypic (ρ := ρ) (σ := σ)
  left_inv := by
    intro f
    -- Corestricting the subtype inclusion map gives back the original map into the subrepresentation.
    apply Representation.IntertwiningMap.ext
    ext w
    rfl
  right_inv := by
    intro f
    -- Postcomposing the codomain restriction with the subtype inclusion recovers the original map.
    apply Representation.IntertwiningMap.ext
    ext w
    rfl
  map_add' := by
    intro f g
    -- The inclusion of the subrepresentation is linear.
    apply Representation.IntertwiningMap.ext
    ext w
    rfl
  map_smul' := by
    intro a f
    -- Scalar multiplication is preserved by the inclusion map.
    apply Representation.IntertwiningMap.ext
    ext w
    rfl

-- Proof sketch: from an isomorphism `e : ⨁ σ ≃ V_i`, take the restriction of `e` to each summand.
-- Injectivity of `e` makes those coordinate maps linearly independent, while surjectivity plus
-- Schur's lemma shows that every intertwiner `σ ⟶ ρ` is a finite linear combination of them.
/-- Helper for Exercise 2-2.6-3: transporting the standard direct-sum basis across an equivalence
onto the isotypic component yields a basis of the intertwining space, and the associated
evaluation map reconstructs that equivalence. -/
private theorem equiv_directSum_component_basis
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible]
    (e : (directSum fun _ : ι ↦ σ).Equiv (ρ.isotypicSubrepresentation σ).toRepresentation) :
    ∃ b : Module.Basis ι K (σ.IntertwiningMap ρ),
      e.toIntertwiningMap = ρ.familyDirectSumEvaluation σ b := by
  let e₁ :
      σ.IntertwiningMap (directSum fun _ : ι ↦ σ) ≃ₗ[K]
        σ.IntertwiningMap (ρ.isotypicSubrepresentation σ).toRepresentation :=
    intertwiningMap_postcompose_linearEquiv
      (τ := σ) (υ := directSum fun _ : ι ↦ σ)
      (ω := (ρ.isotypicSubrepresentation σ).toRepresentation) e
  let e₂ :
      σ.IntertwiningMap (ρ.isotypicSubrepresentation σ).toRepresentation ≃ₗ[K]
        σ.IntertwiningMap ρ :=
    intertwiningMap_isotypicSubrepresentation_linearEquiv (ρ := ρ) (σ := σ)
  let b : Module.Basis ι K (σ.IntertwiningMap ρ) :=
    (Finsupp.basisSingleOne (R := K) (ι := ι)).map
      ((intertwiningMap_into_directSum_linearEquiv_finsupp (σ := σ)).trans (e₁.trans e₂))
  refine ⟨b, ?_⟩
  have hb :
      ∀ i,
        b i =
          (isotypicSubrepresentation_subtype_intertwining (ρ := ρ) (σ := σ)).comp
            (e.toIntertwiningMap.comp (directSum_lof_intertwining (σ := σ) i)) := by
    intro i
    -- The transported basis vector is exactly the image of the `i`-th summand inclusion.
    simp [b, Finsupp.coe_basisSingleOne, e₁, e₂,
      intertwiningMap_into_directSum_linearEquiv_finsupp_single,
      intertwiningMap_postcompose_linearEquiv,
      intertwiningMap_isotypicSubrepresentation_linearEquiv]
  apply Representation.IntertwiningMap.ext
  apply DirectSum.linearMap_ext
  intro i
  ext w
  -- Route correction: reconstruct `e` by checking both maps on each direct-sum generator.
  simp [familyDirectSumEvaluation, hb]
  let φ : ι → W →ₗ[K] V := fun i ↦
    (isotypicSubrepresentation_subtype_intertwining (ρ := ρ) (σ := σ)).toLinearMap ∘ₗ
      e.toIntertwiningMap.toLinearMap ∘ₗ (directSum_lof_intertwining (σ := σ) i).toLinearMap
  have hto :
      DirectSum.toModule K ι V φ ((DirectSum.lof K ι (fun _ : ι ↦ W) i) w) = (φ i) w := by
    simpa [φ] using
      (DirectSum.toModule_lof (R := K) (ι := ι) (M := fun _ : ι ↦ W) (N := V) (φ := φ) i w)
  symm
  convert hto using 1
/-- Helper for Exercise 2-2.6-3: the component maps extracted from a direct-sum equivalence onto
the `σ`-isotypic component form a basis of the intertwining space, and their evaluation map
reconstructs the original equivalence. -/
private theorem equiv_directSum_component_family_spans_and_is_linearIndependent
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible]
    (e : (directSum fun _ : ι ↦ σ).Equiv (ρ.isotypicSubrepresentation σ).toRepresentation) :
    ∃ h : ι → σ.IntertwiningMap ρ,
      LinearIndependent K h ∧
        ⊤ ≤ Submodule.span K (Set.range h) ∧
        e.toIntertwiningMap = ρ.familyDirectSumEvaluation σ h := by
  obtain ⟨b, hb⟩ := equiv_directSum_component_basis (ρ := ρ) (σ := σ) (ι := ι) e
  refine ⟨b, b.linearIndependent, ?_, hb⟩
  -- A basis spans the whole intertwining space by definition.
  simpa [b.span_eq]

-- Proof sketch: a basis of the intertwining space identifies `Hom_G(σ, ρ) ⊗ W` with the direct
-- sum of copies of `W` indexed by the basis; on a pure tensor `f ⊗ w`, this sends the tensor to
-- the direct-sum vector whose `i`-th coordinate is `(b.repr f i) • w`.
/-- Helper for Exercise 2-2.6-3: a basis of the intertwining space induces the canonical linear
equivalence from `Hom_G(σ, ρ) ⊗ W` to the direct sum of copies of `W` indexed by that basis. -/
private noncomputable def basisTensorDirectSumLinearEquiv
    (ρ : Representation K G V) (σ : Representation K G W)
    (b : Module.Basis ι K (σ.IntertwiningMap ρ)) :
    (σ.IntertwiningMap ρ ⊗[K] W) ≃ₗ[K] DirectSum ι (fun _ : ι ↦ W) :=
  (TensorProduct.congr b.repr (LinearEquiv.refl K W)).trans
    ((TensorProduct.finsuppScalarLeft K W ι).trans (finsuppLEquivDirectSum K W ι))

-- Proof sketch: after transporting a pure tensor `f ⊗ w` to the direct sum by the previous
-- equivalence, the direct-sum evaluation map computes exactly
-- `∑ (b.repr f i) • b i w = f w`, which is the original tensor evaluation.
/-- Helper for Exercise 2-2.6-3: the basis-induced identification of `Hom_G(σ, ρ) ⊗ W` with a
direct sum of copies of `W` conjugates tensor evaluation to direct-sum evaluation. -/
private theorem basis_tensor_directSum_equiv_commutes_evaluation
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible]
    (b : Module.Basis ι K (σ.IntertwiningMap ρ)) :
    ∀ x,
      ρ.familyDirectSumEvaluation σ b (basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b x) =
        ρ.isotypicTensorEvaluation σ x := by
  intro x
  -- Route correction: instead of rebuilding the Schur argument here, transport evaluation through
  -- the basis/direct-sum linear equivalence and verify the identity on pure tensors.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · ext
    simp [basisTensorDirectSumLinearEquiv]
  · intro f w
    -- On a pure tensor, the direct-sum side evaluates the coordinate vector of `f`, which
    -- recombines to `f` by `b.linearCombination_repr`.
    have hcomb :
        (Finset.sum (b.repr f).support fun i ↦ (b.repr f i) • b i : σ.IntertwiningMap ρ) = f := by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr f
    have hsum :
        Finset.sum (b.repr f).support
          (fun i ↦ (b.repr f i) •
            (DirectSum.toModule K ι V (fun j ↦ (b j).toLinearMap)
              ((DirectSum.lof K ι (fun _ : ι ↦ W) i) w))) = f w := by
      have hsum' :
          ((Finset.sum (b.repr f).support fun i ↦ (b.repr f i) • b i : σ.IntertwiningMap ρ)) w =
            f w := by
        exact congrArg (fun h : σ.IntertwiningMap ρ ↦ h w) hcomb
      have hval : Finset.sum (b.repr f).support (fun i ↦ (b.repr f i) • (b i w)) = f w := by
        calc
          Finset.sum (b.repr f).support (fun i ↦ (b.repr f i) • (b i w))
              = ((Finset.sum (b.repr f).support fun i ↦ (b.repr f i) • b i :
                  σ.IntertwiningMap ρ)) w := by
                    simp [Representation.IntertwiningMap.sum_apply, Pi.smul_apply]
          _ = f w := hsum'
      calc
        Finset.sum (b.repr f).support
            (fun i ↦ (b.repr f i) •
              (DirectSum.toModule K ι V (fun j ↦ (b j).toLinearMap)
                ((DirectSum.lof K ι (fun _ : ι ↦ W) i) w)))
            = Finset.sum (b.repr f).support (fun i ↦ (b.repr f i) • (b i w)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [DirectSum.toModule_lof]
        _ = f w := hval
    ext
    unfold familyDirectSumEvaluation isotypicTensorEvaluation
    simp [basisTensorDirectSumLinearEquiv, TensorProduct.congr_tmul,
      TensorProduct.finsuppScalarLeft_apply_tmul, Finsupp.sum, DirectSum.toModule_lof]
    exact hsum
  · intro x y hx hy
    ext
    simpa [familyDirectSumEvaluation, isotypicTensorEvaluation] using
      congrArg₂ HAdd.hAdd (congrArg Subtype.val hx) (congrArg Subtype.val hy)

end

/-- Helper for Exercise 2-2.6-3: the tensor-evaluation map is bijective once one chooses a
direct-sum model of the `σ`-isotypic component and the induced basis of the intertwining space. -/
private theorem isotypicTensorEvaluation_bijective_aux
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible] :
    Function.Bijective (ρ.isotypicTensorEvaluation σ) := by
  -- Choose a direct-sum model of the isotypic component and extract the associated basis of
  -- `Hom_G(σ, ρ)`.
  obtain ⟨ι, ⟨e⟩⟩ := exists_equiv_directSum_isotypicComponent (ρ := ρ) (σ := σ)
  classical
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨h, hlin, hspan, he⟩ :=
    equiv_directSum_component_family_spans_and_is_linearIndependent
      (ρ := ρ) (σ := σ) (ι := ι) e
  let b : Module.Basis ι K (σ.IntertwiningMap ρ) := Module.Basis.mk hlin hspan.ge
  have hb :
      e.toIntertwiningMap = ρ.familyDirectSumEvaluation σ b := by
    simpa [b] using he
  have hfamily : Function.Bijective (ρ.familyDirectSumEvaluation σ b) := by
    simpa [hb] using e.toLinearEquiv.bijective
  -- Transport tensor evaluation across the basis/direct-sum identification.
  constructor
  · intro x y hxy
    apply (basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).injective
    apply hfamily.1
    simpa [basis_tensor_directSum_equiv_commutes_evaluation
      (ρ := ρ) (σ := σ) (ι := ι) b x,
      basis_tensor_directSum_equiv_commutes_evaluation
        (ρ := ρ) (σ := σ) (ι := ι) b y] using hxy
  · intro y
    rcases hfamily.2 y with ⟨z, hz⟩
    refine ⟨(basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).symm z, ?_⟩
    have hcomm :
        (ρ.familyDirectSumEvaluation σ b) z =
          (ρ.isotypicTensorEvaluation σ)
            ((basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).symm z) := by
      simpa using
        (basis_tensor_directSum_equiv_commutes_evaluation
          (ρ := ρ) (σ := σ) (ι := ι) b
          ((basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).symm z))
    exact hcomm.symm.trans hz

/-- Helper for Exercise 2-2.6-3: an irreducible representation has nontrivial carrier. -/
private theorem nontrivial_of_isIrreducible
    (ρ : Representation K G V) [ρ.IsIrreducible] : Nontrivial V := by
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top :
      (⊥ : Subrepresentation ρ).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top <| Subrepresentation.toSubmodule_injective hbot_top

-- Proof sketch: identify the intertwining space `H_i` with the multiplicity space of the
-- `σ`-isotypic component. Part (2) shows `H_i ⊗ W` is isomorphic to that isotypic summand, so
-- taking dimensions gives `dim H_i * dim W = dim V_i`, hence the displayed quotient formula.
/-- Exercise 2-2.6-3 (1): the dimension of the intertwining space `H_i = Hom_G(W_i, V)` equals
the multiplicity of `W_i` in `V`, namely `dim V_i / dim W_i` for the corresponding isotypic
component `V_i`. -/

theorem finrank_intertwiningMap_eq_isotypicMultiplicity
    (ρ : Representation K G V) [FiniteDimensional K V]
    (σ : Representation K G W) [σ.IsIrreducible] :
    Module.finrank K (σ.IntertwiningMap ρ) =
      Module.finrank K ((ρ.isotypicSubrepresentation σ).toSubmodule) / Module.finrank K W := by
  let e :=
    LinearEquiv.ofBijective (ρ.isotypicTensorEvaluation σ).toLinearMap
      (isotypicTensorEvaluation_bijective_aux (ρ := ρ) (σ := σ))
  -- The bijective evaluation map identifies `H_i ⊗ W_i` with the isotypic component `V_i`.
  have hfin :
      Module.finrank K (σ.IntertwiningMap ρ ⊗[K] W) =
        Module.finrank K ((ρ.isotypicSubrepresentation σ).toSubmodule) := by
    simpa [e] using e.finrank_eq
  have hmul :
      Module.finrank K (σ.IntertwiningMap ρ) * Module.finrank K W =
        Module.finrank K ((ρ.isotypicSubrepresentation σ).toSubmodule) := by
    calc
      Module.finrank K (σ.IntertwiningMap ρ) * Module.finrank K W
          = Module.finrank K (σ.IntertwiningMap ρ ⊗[K] W) := by
              symm
              simpa using
                (Module.finrank_tensorProduct
                  (R := K) (S := K) (M := σ.IntertwiningMap ρ) (M' := W))
      _ = Module.finrank K ((ρ.isotypicSubrepresentation σ).toSubmodule) := hfin
  letI : FiniteDimensional K W := IsIrreducible.finiteDimensional_of_finite σ
  letI : Nontrivial W := nontrivial_of_isIrreducible (ρ := σ)
  -- Divide by the nonzero dimension of the irreducible model `W_i`.
  exact Nat.eq_div_of_mul_eq_right
    (Nat.ne_of_gt (Module.finrank_pos : 0 < Module.finrank K W))
    (by simpa [mul_comm] using hmul)

-- Proof sketch: first show that `isotypicTensorEvaluation ρ σ` is exactly the textbook map
-- `F : H_i ⊗ W_i → V_i`. Then reduce to the case of a direct sum of copies of `σ` inside the
-- isotypic component and apply Schur's lemma to prove injectivity and surjectivity.
/-- Exercise 2-2.6-3 (2): the evaluation map `H_i ⊗ W_i → V_i`, where `G` acts trivially on
`H_i = Hom_G(W_i, V)`, is a bijective intertwining map. -/
theorem isotypicTensorEvaluation_bijective
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible] :
    Function.Bijective (ρ.isotypicTensorEvaluation σ) := by
  simpa using isotypicTensorEvaluation_bijective_aux (ρ := ρ) (σ := σ)

end

section

variable {ι : Type x}

local instance instDecidableEqIotaChap2263Equiv : DecidableEq ι := Classical.decEq ι

section

variable [Finite G] [Finite ι]

local instance instFintypeGChap2263Equiv : Fintype G := Fintype.ofFinite G
local instance instFintypeIotaChap2263Equiv : Fintype ι := Fintype.ofFinite ι

-- Proof sketch: choose the family `h` to be a basis of the intertwining space `H_i`. Part (2)
-- identifies `H_i ⊗ W_i` with the isotypic summand, while the chosen basis identifies
-- `H_i ⊗ W_i` with the direct sum of `|ι|` copies of `W_i`; transporting along these
-- identifications gives the stated bijectivity.
/-- Exercise 2-2.6-3 (3): if a finite family of intertwining maps `h : ι → Hom_G(W_i, V)` forms a
basis of the intertwining space, then the induced map from the direct sum of `|ι|` copies of
`W_i` onto `V_i` is a bijective intertwining map. -/
theorem familyDirectSumEvaluation_bijective
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible]
    (b : Module.Basis ι K (σ.IntertwiningMap ρ)) :
    Function.Bijective (ρ.familyDirectSumEvaluation σ b) := by
  -- Conjugate direct-sum evaluation to tensor evaluation through the basis/direct-sum
  -- identification of `Hom_G(σ, ρ) ⊗ W_i`.
  constructor
  · intro x y hxy
    apply (basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).symm.injective
    apply (isotypicTensorEvaluation_bijective (ρ := ρ) (σ := σ)).1
    have hcommx :
        (ρ.familyDirectSumEvaluation σ b) x =
          (ρ.isotypicTensorEvaluation σ)
            ((basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).symm x) := by
      simpa using
        (basis_tensor_directSum_equiv_commutes_evaluation
          (ρ := ρ) (σ := σ) (ι := ι) b
          ((basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).symm x))
    have hcommy :
        (ρ.familyDirectSumEvaluation σ b) y =
          (ρ.isotypicTensorEvaluation σ)
            ((basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).symm y) := by
      simpa using
        (basis_tensor_directSum_equiv_commutes_evaluation
          (ρ := ρ) (σ := σ) (ι := ι) b
          ((basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b).symm y))
    exact hcommx.symm.trans (hxy.trans hcommy)
  · intro y
    rcases (isotypicTensorEvaluation_bijective (ρ := ρ) (σ := σ)).2 y with ⟨x, hx⟩
    refine ⟨basisTensorDirectSumLinearEquiv (ρ := ρ) (σ := σ) b x, ?_⟩
    exact
      (basis_tensor_directSum_equiv_commutes_evaluation
        (ρ := ρ) (σ := σ) (ι := ι) b x).trans hx

/-- Companion formulation of Exercise 2-2.6-3 (3): a linearly independent spanning family of
intertwining maps yields the same bijective evaluation map via the canonical basis
`Basis.mk hlin hspan.ge`. -/
theorem familyDirectSumEvaluation_bijective_of_linearIndependent_of_span_eq_top
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible]
    (h : ι → σ.IntertwiningMap ρ)
    (hlin : LinearIndependent K h) (hspan : Submodule.span K (Set.range h) = ⊤) :
    Function.Bijective (ρ.familyDirectSumEvaluation σ h) := by
  simpa using
    (familyDirectSumEvaluation_bijective ρ σ (Module.Basis.mk hlin hspan.ge))

-- Proof sketch: an isomorphism from a direct sum of copies of `σ` to the `σ`-isotypic component
-- restricts on each summand to an intertwining map `σ ⟶ ρ`. These component maps assemble into a
-- basis of the intertwining space because the original isomorphism is bijective, and reconstruct
-- the given isomorphism by the universal property of the direct sum.
/-- Exercise 2-2.6-3 (4): every representation isomorphism from a finite direct sum of copies of
`W_i` onto `V_i` comes from a basis of `H_i = Hom_G(W_i, V)`. In particular, decomposing `V_i`
into irreducible summands isomorphic to `W_i` amounts to choosing a basis of that intertwining
space. -/
theorem exists_basis_family_of_equiv_directSum_isotypicComponent
    (ρ : Representation K G V) (σ : Representation K G W) [σ.IsIrreducible]
    (e : (directSum fun _ : ι ↦ σ).Equiv
      (ρ.isotypicSubrepresentation σ).toRepresentation) :
    ∃ b : Module.Basis ι K (σ.IntertwiningMap ρ),
      e.toIntertwiningMap = ρ.familyDirectSumEvaluation σ b := by
  -- Package the component family coming from the chosen direct-sum equivalence as a basis.
  obtain ⟨h, hlin, hspan, he⟩ :=
    equiv_directSum_component_family_spans_and_is_linearIndependent
      (ρ := ρ) (σ := σ) (ι := ι) e
  refine ⟨Module.Basis.mk hlin hspan.ge, ?_⟩
  simpa using he

end

end

end

end

end Representation
