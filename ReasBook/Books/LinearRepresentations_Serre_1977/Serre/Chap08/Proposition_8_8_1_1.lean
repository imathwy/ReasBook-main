import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_6_1
import LinearRepresentations_Serre_1977.Chap03.Definition_3_3_3_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra Pointwise Representation

universe u v

namespace Representation

noncomputable section

section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Helper for Proposition 8-8.1-1: the underlying `ℂ`-subspace obtained by transporting an
`A`-stable subspace through the operator `ρ g`. -/
private def transportedSubrepresentationCarrier
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (W : Subrepresentation (ρ.comp A.subtype)) (g : G) :
    Submodule ℂ V :=
  W.toSubmodule.map (ρ g)

/-- Helper for Proposition 8-8.1-1: normality of `A` makes the `ρ g`-image of an `A`-stable
subspace stable under the restricted `A`-action again. -/
private theorem transportedSubrepresentationCarrier_apply_mem
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : G) (a : A)
    {v : V} (hv : v ∈ transportedSubrepresentationCarrier ρ A W g) :
    ρ a v ∈ transportedSubrepresentationCarrier ρ A W g := by
  -- Write `v` as `ρ g w` with `w ∈ W`, then move the `A`-action across `ρ g` by conjugation.
  rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
  let a' : A := ⟨g⁻¹ * a * g, Subgroup.Normal.conj_mem' (H := A) inferInstance a a.property g⟩
  refine Submodule.mem_map.mpr ?_
  refine ⟨ρ a' w, W.apply_mem_toSubmodule a' hw, ?_⟩
  calc
    ρ g (ρ a' w) = ρ (g * (a' : A)) w := by
      exact (LinearMap.congr_fun (ρ.map_mul g (a' : A)) w).symm
    _ = ρ (g * (a' : A)) w := by
      rfl
    _ = ρ ((a : G) * g) w := by
      simp [a', mul_assoc]
    _ = ρ a (ρ g w) := by
      exact LinearMap.congr_fun (ρ.map_mul (a : G) g) w

/-- Helper for Proposition 8-8.1-1: transporting an `A`-stable subrepresentation through `ρ g`
produces another `A`-stable subrepresentation. -/
private def transportedSubrepresentation
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : G) :
    Subrepresentation (ρ.comp A.subtype) where
  toSubmodule := transportedSubrepresentationCarrier ρ A W g
  apply_mem_toSubmodule := transportedSubrepresentationCarrier_apply_mem ρ A W g

/-- Helper for Proposition 8-8.1-1: the transported subrepresentation has the expected carrier. -/
@[simp] private theorem transportedSubrepresentation_toSubmodule
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : G) :
    (transportedSubrepresentation ρ A W g).toSubmodule =
      transportedSubrepresentationCarrier ρ A W g :=
  rfl

/-- Helper for Proposition 8-8.1-1: every `ρ g` is injective, so transporting a nonzero
subrepresentation keeps it nonzero. -/
private theorem transportedSubrepresentation_ne_bot
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : G)
    (hW : W.toSubmodule ≠ ⊥) :
    (transportedSubrepresentation ρ A W g).toSubmodule ≠ ⊥ := by
  -- Apply `ρ g⁻¹` to an equality `map (ρ g) = ⊥` to recover `W = ⊥`.
  intro hbot
  apply hW
  refine le_antisymm ?_ bot_le
  intro w hw
  have hmem : ρ g w ∈ (transportedSubrepresentation ρ A W g).toSubmodule := by
    rw [transportedSubrepresentation_toSubmodule]
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have hzero_mem : ρ g w ∈ (⊥ : Submodule ℂ V) := by
    rw [hbot] at hmem
    simpa using hmem
  have hzero : ρ g w = 0 := by
    simpa using hzero_mem
  have happly := congrArg (ρ g⁻¹) hzero
  simpa using happly

/-- Helper for Proposition 8-8.1-1: if a restricted subrepresentation is nonzero as an
`ℂ[A]`-owner submodule, then its transported copy is still nonzero as an owner submodule. -/
private theorem transportedSubrepresentation_asSubmodule_ne_bot
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : G)
    (hW : W.asSubmodule ≠ ⊥) :
    (transportedSubrepresentation ρ A W g).asSubmodule ≠ ⊥ := by
  let ρA : Representation ℂ A V := ρ.comp A.subtype
  have hW_toSubmodule : W.toSubmodule ≠ ⊥ := by
    intro hbot
    apply hW
    ext v
    change ((v : V) ∈ W.toSubmodule) ↔ v ∈ (⊥ : Submodule (MonoidAlgebra ℂ A) ρA.asModule)
    rw [hbot]
    constructor <;> intro hv <;> simpa using hv
  have htransport_toSubmodule :
      (transportedSubrepresentation ρ A W g).toSubmodule ≠ ⊥ :=
    transportedSubrepresentation_ne_bot ρ A W g hW_toSubmodule
  intro hbot
  have hbot_toSubmodule : (transportedSubrepresentation ρ A W g).toSubmodule = ⊥ := by
    ext v
    change v ∈ (transportedSubrepresentation ρ A W g).asSubmodule ↔
        v ∈ (⊥ : Submodule (MonoidAlgebra ℂ A) ρA.asModule)
    rw [hbot]
  exact htransport_toSubmodule hbot_toSubmodule

/-- Helper for Proposition 8-8.1-1: transporting a fully invariant `A`-stable summand through
`ρ g` preserves full invariance for the restricted `A`-module. -/
private theorem transportedSubrepresentation_asSubmodule_isFullyInvariant
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : G)
    (hW : W.asSubmodule.IsFullyInvariant) :
    ((transportedSubrepresentation ρ A W g).asSubmodule).IsFullyInvariant := by
  let ρA : Representation ℂ A V := ρ.comp A.subtype
  letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
  intro f v hv
  change v ∈ (transportedSubrepresentation ρ A W g).toSubmodule at hv
  change f v ∈ (transportedSubrepresentation ρ A W g).toSubmodule
  rw [transportedSubrepresentation_toSubmodule] at hv ⊢
  rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
  let fInter : ρA.IntertwiningMap ρA :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρA) (σ := ρA)).symm f
  let fConjLin : V →ₗ[ℂ] V := (ρ g⁻¹).comp (fInter.toLinearMap.comp (ρ g))
  have hfConj : ρA.IsIntertwiningMap ρA fConjLin := by
    rw [Representation.isIntertwiningMap_iff]
    intro a x
    let a' : A := ⟨g * a * g⁻¹, Subgroup.Normal.conj_mem inferInstance (a : G) a.property g⟩
    -- Move the `A`-action across `ρ g⁻¹`, use equivariance of `f`, then move it back across
    -- `ρ g`.
    calc
      fConjLin (ρA a x)
          = ρ g⁻¹ (fInter (ρ g (ρA a x))) := by
              rfl
      _ = ρ g⁻¹ (fInter (ρA a' (ρ g x))) := by
            congr 1
            simp [ρA, a', mul_assoc]
      _ = ρ g⁻¹ (ρA a' (fInter (ρ g x))) := by
            congr 1
            show fInter (ρA a' (ρ g x)) = ρA a' (fInter (ρ g x))
            exact LinearMap.congr_fun (fInter.isIntertwining' a') (ρ g x)
      _ = ρA a (ρ g⁻¹ (fInter (ρ g x))) := by
            simp [ρA, a', mul_assoc]
      _ = ρA a (fConjLin x) := by
            rfl
  let fConj : Module.End (MonoidAlgebra ℂ A) V :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρA) (σ := ρA))
      (fConjLin.intertwiningMap_of_isIntertwiningMap ρA ρA hfConj.isIntertwining)
  have hwConj : fConj w ∈ W.asSubmodule := by
    exact hW fConj hw
  -- Apply full invariance to the conjugated endomorphism on the original component and then
  -- transport the resulting vector forward by `ρ g`.
  refine Submodule.mem_map.mpr ⟨fConj w, hwConj, ?_⟩
  change ρ g (ρ g⁻¹ (f (ρ g w))) = f (ρ g w)
  calc
    ρ g (ρ g⁻¹ (f (ρ g w))) = ρ (g * g⁻¹) (f (ρ g w)) := by
      exact (LinearMap.congr_fun (ρ.map_mul g g⁻¹) (f (ρ g w))).symm
    _ = f (ρ g w) := by
      simp

/-- Helper for Proposition 8-8.1-1: transporting an `A`-stable subrepresentation through `ρ g`
identifies it with the conjugate representation `W.toRepresentation ^ g`. -/
private noncomputable def transportedSubrepresentation_rep_equiv
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : G) :
    Representation.Equiv
      ((W.toRepresentation).comp (MulAut.conjNormal g⁻¹).toMonoidHom)
      (transportedSubrepresentation ρ A W g).toRepresentation := by
  -- The transported carrier is literally `W.toSubmodule.map (ρ g)`, so `ρ g` gives the
  -- underlying linear equivalence and the conjugation formula supplies equivariance.
  let e : W.toSubmodule ≃ₗ[ℂ] (transportedSubrepresentation ρ A W g).toSubmodule :=
    Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).injective W.toSubmodule
  refine Representation.Equiv.mk e ?_
  intro a
  ext w
  change ρ g (ρ ((MulAut.conjNormal g).symm a) (w : V)) = ρ a (ρ g w)
  calc
    ρ g (ρ ((MulAut.conjNormal g).symm a) (w : V))
        = ρ (g * (((MulAut.conjNormal g).symm a : A))) (w : V) := by
            exact
              (LinearMap.congr_fun (ρ.map_mul g (((MulAut.conjNormal g).symm a : A))) (w : V)).symm
    _ = ρ ((a : G) * g) (w : V) := by
          simp [MulAut.conjNormal_symm_apply, mul_assoc]
    _ = ρ a (ρ g w) := by
          exact LinearMap.congr_fun (ρ.map_mul (a : G) g) (w : V)

/-- Helper for Proposition 8-8.1-1: conjugating the `A`-action by `g` does not change the
subrepresentation lattice. -/
private noncomputable def conjugatedSubrepresentationOrderIso
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (A : Subgroup G) [A.Normal]
    (σ : Representation ℂ A W') (g : G) :
    Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro a x hx
        rcases (MulAut.conjNormal g⁻¹).surjective a with ⟨b, rfl⟩
        exact U.apply_mem_toSubmodule b hx }
  invFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro a x hx
        exact U.apply_mem_toSubmodule ((MulAut.conjNormal g⁻¹) a) hx }
  left_inv U := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv U := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro U V
    rfl

/-- Helper for Proposition 8-8.1-1: a representation equivalence induces an order isomorphism on
subrepresentations. -/
private noncomputable def subrepresentationOrderIso
    {A : Type*} [Group A]
    {V' W' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ A V'} {σ : Representation ℂ A W'} (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro a x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- Mapping a stable subspace through an intertwining equivalence preserves stability.
        refine ⟨ρ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro a x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- The inverse intertwining equivalence transports stable subspaces back.
        refine ⟨σ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv U := by
    -- Mapping to `σ` and back to `ρ` recovers the original subrepresentation.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv U := by
    -- The same argument shows that mapping from `σ` back to `ρ` and forward again is inverse.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, by simp⟩, by simp⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro h x hx
      have hxmap : e x ∈ U.toSubmodule.map e.toLinearMap :=
        Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      have hVmap : e x ∈ V.toSubmodule.map e.toLinearMap := h hxmap
      rcases Submodule.mem_map.mp hVmap with ⟨y, hy, hyx⟩
      have : y = x := by
        apply e.injective
        simpa using hyx
      simpa [this] using hy
    · intro h x hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for Proposition 8-8.1-1: the order isomorphism for conjugating the `A`-action leaves
the underlying `ℂ`-submodule unchanged. -/
@[simp] private theorem conjugatedSubrepresentationOrderIso_toSubmodule
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (A : Subgroup G) [A.Normal]
    (σ : Representation ℂ A W') (g : G)
    (U : Subrepresentation ((σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom))) :
    (conjugatedSubrepresentationOrderIso A σ g U).toSubmodule = U.toSubmodule :=
  rfl

/-- Helper for Proposition 8-8.1-1: irreducibility transfers across a representation
equivalence. -/
private theorem isIrreducible_of_equiv
    {A : Type*} [Group A]
    {V' W' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ A V'} {σ : Representation ℂ A W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  -- Equivalent representations have isomorphic lattices of invariant subspaces.
  exact (subrepresentationOrderIso e).isSimpleOrder_iff.mp inferInstance

/-- Helper for Proposition 8-8.1-1: transporting an irreducible restricted subrepresentation
through `ρ g` preserves irreducibility. -/
private theorem transportedSubrepresentation_isIrreducible
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) [W.toRepresentation.IsIrreducible] (g : G) :
    (transportedSubrepresentation ρ A W g).toRepresentation.IsIrreducible := by
  -- The previous equivalence identifies transport with conjugation, so irreducibility is
  -- unchanged.
  letI :
      Representation.IsIrreducible
        ((W.toRepresentation).comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
    exact (conjugatedSubrepresentationOrderIso A W.toRepresentation g).isSimpleOrder_iff.mpr
      inferInstance
  have e :
      Representation.Equiv
        ((W.toRepresentation).comp (MulAut.conjNormal g⁻¹).toMonoidHom)
        (transportedSubrepresentation ρ A W g).toRepresentation :=
    transportedSubrepresentation_rep_equiv ρ A W g
  exact isIrreducible_of_equiv e

/-- Helper for Proposition 8-8.1-1: conjugating both source and target actions by the same normal
automorphism does not change the intertwining condition for a linear map. -/
private theorem isIntertwiningMap_comp_conjNormal_iff
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    (A : Subgroup G) [A.Normal]
    (σ : Representation ℂ A W₁) (τ : Representation ℂ A W₂)
    (g : G) (f : W₁ →ₗ[ℂ] W₂) :
    Representation.IsIntertwiningMap
        (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)
        (τ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) f ↔
      Representation.IsIntertwiningMap σ τ f := by
  rw [Representation.isIntertwiningMap_iff, Representation.isIntertwiningMap_iff]
  constructor
  · intro hf a x
    obtain ⟨b, rfl⟩ := (MulAut.conjNormal g⁻¹).surjective a
    simpa using hf b x
  · intro hf a x
    simpa using hf ((MulAut.conjNormal g⁻¹) a) x

/-- Helper for Proposition 8-8.1-1: each element of `A` stabilizes any chosen `A`-isotypic
component. -/
private theorem stabilizer_contains_A_of_isotypic_component
    (ρ : Representation ℂ G V) (A : Subgroup G) :
    let ρA : Representation ℂ A V := ρ.comp A.subtype
    letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra ℂ A) V,
      A ≤ ρ.submoduleStabilizer ((Subrepresentation.ofSubmodule' c.1).toSubmodule) :=
  by
    intro ρA
    letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
    intro c a ha
    let aA : A := ⟨a, ha⟩
    let W : Subrepresentation ρA := Subrepresentation.ofSubmodule' c.1
    rw [mem_submoduleStabilizer_iff_map_eq]
    -- The chosen owner summand is already an `A`-stable subrepresentation, so every `a ∈ A`
    -- preserves its underlying `ℂ`-subspace, and `a⁻¹` gives the reverse inclusion.
    apply le_antisymm
    · intro x hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [W] using W.apply_mem_toSubmodule aA hy
    · intro x hx
      refine Submodule.mem_map.mpr ⟨ρ aA⁻¹ x, ?_, ?_⟩
      · simpa [W] using W.apply_mem_toSubmodule aA⁻¹ hx
      · calc
          ρ a (ρ aA⁻¹ x) = ρ ((a : G) * (aA⁻¹ : A)) x := by
            exact (LinearMap.congr_fun (ρ.map_mul (a : G) (aA⁻¹ : A)) x).symm
          _ = x := by
            simp [aA]

/-- Helper for Proposition 8-8.1-1: the owner `ℂ[A]`-action on the intrinsic module of
`Subrepresentation.ofSubmodule' N` is the original owner action on `N`. -/
private theorem subrepresentation_ofSubmodule'_asAlgebraHom_apply
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (N : Submodule (MonoidAlgebra ℂ A') ρ.asModule)
    (r : MonoidAlgebra ℂ A') (x : N) :
    (((Subrepresentation.ofSubmodule' N).toRepresentation).asAlgebraHom r) x = r • x := by
  -- Compare the two owner actions after forgetting to the ambient subtype carrier.
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

/-- Helper for Proposition 8-8.1-1: the intrinsic owner module of `Subrepresentation.ofSubmodule'
N` is canonically the original `ℂ[A]`-submodule `N`. -/
private noncomputable def subrepresentation_ofSubmodule'_asModule_linearEquiv
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (N : Submodule (MonoidAlgebra ℂ A') ρ.asModule) :
    ((Subrepresentation.ofSubmodule' N).toRepresentation).asModule ≃ₗ[MonoidAlgebra ℂ A'] N := by
  let ρN : Representation ℂ A' N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  refine
    { toFun := fun x => ρN.asModuleEquiv x
      invFun := fun x => ρN.asModuleEquiv.symm x
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

/-- Helper for Proposition 8-8.1-1: the intrinsic owner module of a bundled subrepresentation is
canonically the owner submodule it defines inside the ambient representation. -/
private noncomputable def subrepresentation_owner_intrinsic_linearEquiv
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W : Subrepresentation ρ) :
    W.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ A'] W.asSubmodule := by
  -- Rewrite `W` as `Subrepresentation.ofSubmodule' W.asSubmodule` and reuse the canonical bridge.
  simpa using subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) W.asSubmodule

/-- Helper for Proposition 8-8.1-1: the owner and intrinsic views of the submodule lattice of a
subrepresentation are canonically order-isomorphic. -/
private noncomputable def subrepresentation_owner_intrinsic_submodule_orderIso
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W : Subrepresentation ρ) :
    Submodule (MonoidAlgebra ℂ A') W.toRepresentation.asModule ≃o
      Submodule (MonoidAlgebra ℂ A') W.asSubmodule := by
  let ρW : Representation ℂ A' W.toSubmodule := W.toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρW.asModule := ρW.instModuleMonoidAlgebraAsModule
  -- The canonical linear equivalence on ambient carriers transports submodules in both
  -- directions.
  exact Submodule.orderIsoMapComap (subrepresentation_owner_intrinsic_linearEquiv (ρ := ρ) W)

/-- Helper for Proposition 8-8.1-1: the intrinsic counterpart of an owner submodule is linearly
equivalent to the original owner submodule. -/
private noncomputable def subrepresentation_owner_intrinsic_submodule_linearEquiv
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W : Subrepresentation ρ)
    (m : Submodule (MonoidAlgebra ℂ A') W.asSubmodule) :
    ((subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρ) W).symm m) ≃ₗ[MonoidAlgebra ℂ A'] m := by
  let ρW : Representation ℂ A' W.toSubmodule := W.toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρW.asModule := ρW.instModuleMonoidAlgebraAsModule
  let e : ρW.asModule ≃ₗ[MonoidAlgebra ℂ A'] W.asSubmodule :=
    subrepresentation_owner_intrinsic_linearEquiv (ρ := ρ) W
  let mInt : Submodule (MonoidAlgebra ℂ A') ρW.asModule :=
    (subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρ) W).symm m
  -- The intrinsic submodule is the `comap` of `m` along `e`, so `e` restricts directly to an
  -- equivalence onto `m`.
  refine
    { toFun := fun x => ⟨e x, x.property⟩
      invFun := fun y => ⟨e.symm y, by simpa [mInt, subrepresentation_owner_intrinsic_submodule_orderIso, e] using y.property⟩
      left_inv := by
        intro x
        ext
        simp
      right_inv := by
        intro y
        ext
        simp
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro r x
        ext
        simp }

/-- Helper for Proposition 8-8.1-1: simplicity is preserved when moving a submodule between the
owner and intrinsic views of the same subrepresentation. -/
private theorem isSimpleModule_owner_intrinsic_iff
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W : Subrepresentation ρ)
    (m : Submodule (MonoidAlgebra ℂ A') W.asSubmodule) :
    IsSimpleModule (MonoidAlgebra ℂ A')
        ((subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρ) W).symm m) ↔
      IsSimpleModule (MonoidAlgebra ℂ A') m := by
  -- Transport simplicity along the canonical owner/intrinsic linear equivalence for the chosen
  -- submodule.
  simpa using
    (subrepresentation_owner_intrinsic_submodule_linearEquiv (ρ := ρ) W m).isSimpleModule_iff

/-- Helper for Proposition 8-8.1-1: simple intrinsic constituents of an isotypic block become
equivalent after comparison in the owner view of that block. -/
private theorem pulled_back_constituents_equiv_in_isotypic_block
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (W₀ : Subrepresentation ρ)
    (hW₀ : IsIsotypic (MonoidAlgebra ℂ A') W₀.asSubmodule)
    (m m' : Submodule (MonoidAlgebra ℂ A') W₀.toRepresentation.asModule)
    [IsSimpleModule (MonoidAlgebra ℂ A') m]
    [IsSimpleModule (MonoidAlgebra ℂ A') m'] :
    Nonempty (m ≃ₗ[MonoidAlgebra ℂ A'] m') := by
  let eW₀ := subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρ) W₀
  let mOwner : Submodule (MonoidAlgebra ℂ A') W₀.asSubmodule := eW₀ m
  let mOwner' : Submodule (MonoidAlgebra ℂ A') W₀.asSubmodule := eW₀ m'
  have hm_eq : eW₀.symm mOwner = m := by
    simpa [mOwner] using eW₀.symm_apply_apply m
  have hm'_eq : eW₀.symm mOwner' = m' := by
    simpa [mOwner'] using eW₀.symm_apply_apply m'
  have hmOwner_simple : IsSimpleModule (MonoidAlgebra ℂ A') mOwner := by
    -- Move the first intrinsic simple constituent into the owner lattice of `W₀`.
    letI : IsSimpleModule (MonoidAlgebra ℂ A') (eW₀.symm mOwner) := hm_eq ▸ inferInstance
    have hm_simple : IsSimpleModule (MonoidAlgebra ℂ A') (eW₀.symm mOwner) := inferInstance
    exact (isSimpleModule_owner_intrinsic_iff (ρ := ρ) W₀ mOwner).mp hm_simple
  have hmOwner'_simple : IsSimpleModule (MonoidAlgebra ℂ A') mOwner' := by
    -- The same owner/intrinsic bridge applies to the second constituent.
    letI : IsSimpleModule (MonoidAlgebra ℂ A') (eW₀.symm mOwner') := hm'_eq ▸ inferInstance
    have hm'_simple : IsSimpleModule (MonoidAlgebra ℂ A') (eW₀.symm mOwner') := inferInstance
    exact (isSimpleModule_owner_intrinsic_iff (ρ := ρ) W₀ mOwner').mp hm'_simple
  unfold IsIsotypic IsIsotypicOfType at hW₀
  letI : IsSimpleModule (MonoidAlgebra ℂ A') mOwner := hmOwner_simple
  letI : IsSimpleModule (MonoidAlgebra ℂ A') mOwner' := hmOwner'_simple
  have hInt :
      Nonempty ((eW₀.symm mOwner) ≃ₗ[MonoidAlgebra ℂ A'] (eW₀.symm mOwner')) := by
    rcases hW₀ mOwner mOwner' with ⟨eOwner⟩
    exact
      ⟨((subrepresentation_owner_intrinsic_submodule_linearEquiv
          (ρ := ρ) W₀ mOwner).trans eOwner.symm).trans
          (subrepresentation_owner_intrinsic_submodule_linearEquiv
            (ρ := ρ) W₀ mOwner').symm⟩
  rcases hInt with ⟨eInt⟩
  exact ⟨hm_eq ▸ hm'_eq ▸ eInt⟩

/-- Helper for Proposition 8-8.1-1: a representation equivalence induces a `ℂ[A]`-linear
equivalence on the associated owner modules. -/
private noncomputable def representationEquiv_asModuleLinearEquiv
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ A' V'} {σ : Representation ℂ A' W'}
    (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[MonoidAlgebra ℂ A'] σ.asModule := by
  refine
    { toFun := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ) e.toIntertwiningMap
      invFun := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ) e.symm.toIntertwiningMap
      left_inv := by
        intro x
        change e.symm (e x) = x
        simp
      right_inv := by
        intro x
        change e (e.symm x) = x
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        simp }

/-- Helper for Proposition 8-8.1-1: untwisting a conjugated irreducible representation recovers
irreducibility of the original action. -/
private theorem unconj_isIrreducible
    (A : Subgroup G) [A.Normal]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ A W') (g : G)
    (hσg :
      let σg : Representation ℂ A W' := σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
      σg.IsIrreducible) :
    σ.IsIrreducible := by
  -- The conjugation order isomorphism preserves simplicity of the subrepresentation lattice.
  let σg : Representation ℂ A W' := σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
  letI : σg.IsIrreducible := hσg
  exact (conjugatedSubrepresentationOrderIso A σ g).isSimpleOrder_iff.mp inferInstance

/-- Helper for Proposition 8-8.1-1: a conjugated subrepresentation is definitionally the same
carrier equipped with the untwisted action. -/
private noncomputable def conjugatedSubrepresentation_rep_equiv
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (A : Subgroup G) [A.Normal]
    (σ : Representation ℂ A W') (g : G)
    (U : Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)) :
    Representation.Equiv U.toRepresentation
      (((conjugatedSubrepresentationOrderIso A σ g U).toRepresentation).comp
        (MulAut.conjNormal g⁻¹).toMonoidHom) := by
  -- Conjugation changes only the action formula; the underlying subtype is unchanged.
  refine Representation.Equiv.mk (LinearEquiv.refl _ _) ?_
  intro a
  ext u
  rfl

/-- Helper for Proposition 8-8.1-1: an intertwining equivalence remains intertwining after
precomposing both actions by the same conjugation automorphism. -/
private noncomputable def representationEquiv_comp_conjNormal
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    (A : Subgroup G) [A.Normal]
    {σ : Representation ℂ A W₁} {τ : Representation ℂ A W₂}
    (e : σ.Equiv τ) (g : G) :
    Representation.Equiv
      (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)
      (τ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
  -- Precomposing both actions by the same automorphism leaves the intertwining relation
  -- unchanged.
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro a
  ext x
  exact LinearMap.congr_fun (e.isIntertwining' ((MulAut.conjNormal g⁻¹) a)) x

/-- Helper for Proposition 8-8.1-1: an owner-module linear equivalence between two
subrepresentations upgrades to a representation equivalence. -/
private noncomputable def subrepresentation_equiv_of_asSubmoduleLinearEquiv
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ A' V'}
    (U W : Subrepresentation ρ)
    (e : U.asSubmodule ≃ₗ[MonoidAlgebra ℂ A'] W.asSubmodule) :
    Representation.Equiv U.toRepresentation W.toRepresentation := by
  let eU := subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) U.asSubmodule
  let eW := subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) W.asSubmodule
  let eRep : U.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ A'] W.toRepresentation.asModule :=
    (eU.trans e).trans eW.symm
  -- Convert the owner-linear map into an intertwiner, then use bijectivity to package it as an
  -- equivalence of representations.
  let f : U.toRepresentation.IntertwiningMap W.toRepresentation :=
    (Representation.IntertwiningMap.equivLinearMapAsModule U.toRepresentation
      W.toRepresentation).symm eRep.toLinearMap
  exact f.ofBijective eRep.bijective

/-- Helper for Proposition 8-8.1-1: restricting a representation equivalence to a
subrepresentation identifies it with the image subrepresentation under
`subrepresentationOrderIso`. -/
private noncomputable def subrepresentation_equiv_of_equiv_image
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ A' V'} {σ : Representation ℂ A' W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    Representation.Equiv U.toRepresentation ((subrepresentationOrderIso e U).toRepresentation) := by
  let eSub : U.toSubmodule ≃ₗ[ℂ] (subrepresentationOrderIso e U).toSubmodule :=
    Submodule.equivMapOfInjective e.toLinearMap e.injective U.toSubmodule
  -- Restrict the ambient intertwiner to the chosen invariant subspace and its image.
  refine Representation.Equiv.mk eSub ?_
  intro a
  ext u
  exact LinearMap.congr_fun (e.isIntertwining' a) u

/-- Helper for Proposition 8-8.1-1: a simple owner submodule yields an irreducible bundled
subrepresentation. -/
private theorem isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (N : Submodule (MonoidAlgebra ℂ A') ρ.asModule)
    (hN : IsSimpleModule (MonoidAlgebra ℂ A') N) :
    (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
  let ρN : Representation ℂ A' N := (Subrepresentation.ofSubmodule' N).toRepresentation
  letI : Module (MonoidAlgebra ℂ A') ρN.asModule := ρN.instModuleMonoidAlgebraAsModule
  -- Transport simplicity across the canonical owner-module equivalence for `ofSubmodule'`.
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρN).mpr
      (@IsSimpleModule.congr (MonoidAlgebra ℂ A') inferInstance ρN.asModule
        ρN.instAddCommGroupAsModule ρN.instModuleMonoidAlgebraAsModule
        N N.addCommGroup N.module
        (subrepresentation_ofSubmodule'_asModule_linearEquiv (ρ := ρ) N) hN)

/-- Helper for Proposition 8-8.1-1: transporting an `A`-isotypic component through `ρ g`
preserves isotypicity. -/
private theorem transportedSubrepresentation_asSubmodule_isIsotypic
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal] [Finite A]
    [NeZero (Nat.card A : ℂ)] :
    let ρA : Representation ℂ A V := ρ.comp A.subtype
    letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra ℂ A) V, ∀ g : G,
      IsIsotypic (MonoidAlgebra ℂ A)
        ((transportedSubrepresentation ρ A (Subrepresentation.ofSubmodule' c.1) g).asSubmodule) :=
  by
    intro ρA
    letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
    letI : Module (MonoidAlgebra ℂ A) ρA.asModule := ρA.instModuleMonoidAlgebraAsModule
    intro c g
    let W₀ : Subrepresentation ρA := Subrepresentation.ofSubmodule' c.1
    let T : Subrepresentation ρA := transportedSubrepresentation ρ A W₀ g
    let ρW₀ : Representation ℂ A W₀.toSubmodule := W₀.toRepresentation
    letI : Module (MonoidAlgebra ℂ A) ρW₀.asModule := ρW₀.instModuleMonoidAlgebraAsModule
    letI : Module (MonoidAlgebra ℂ A) W₀.toRepresentation.asModule :=
      W₀.toRepresentation.instModuleMonoidAlgebraAsModule
    let ρT : Representation ℂ A T.toSubmodule := T.toRepresentation
    letI : Module (MonoidAlgebra ℂ A) ρT.asModule := ρT.instModuleMonoidAlgebraAsModule
    letI : Module (MonoidAlgebra ℂ A) T.toRepresentation.asModule :=
      T.toRepresentation.instModuleMonoidAlgebraAsModule
    have hW₀_owner : IsIsotypic (MonoidAlgebra ℂ A) W₀.asSubmodule := by
      -- The selected summand is one of the canonical isotypic components.
      simpa [W₀] using (IsIsotypic.isotypicComponents c.2)
    unfold IsIsotypic IsIsotypicOfType
    intro m hm m' hm'
    letI : IsSimpleModule (MonoidAlgebra ℂ A) m := hm
    letI : IsSimpleModule (MonoidAlgebra ℂ A) m' := hm'
    let mInt : Submodule (MonoidAlgebra ℂ A) ρT.asModule :=
      (subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρA) T).symm m
    let mInt' : Submodule (MonoidAlgebra ℂ A) ρT.asModule :=
      (subrepresentation_owner_intrinsic_submodule_orderIso (ρ := ρA) T).symm m'
    have hmInt_simple : IsSimpleModule (MonoidAlgebra ℂ A) mInt := by
      -- Move the first simple owner constituent into the intrinsic module of `T`.
      exact (isSimpleModule_owner_intrinsic_iff (ρ := ρA) T m).2 inferInstance
    have hmInt'_simple : IsSimpleModule (MonoidAlgebra ℂ A) mInt' := by
      -- The same bridge transports the second simple owner constituent.
      exact (isSimpleModule_owner_intrinsic_iff (ρ := ρA) T m').2 inferInstance
    let U : Subrepresentation ρT := Subrepresentation.ofSubmodule' mInt
    let U' : Subrepresentation ρT := Subrepresentation.ofSubmodule' mInt'
    have hU_irred : U.toRepresentation.IsIrreducible := by
      -- Simple intrinsic submodules of `T` are irreducible bundled subrepresentations.
      exact isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule ρT mInt hmInt_simple
    have hU'_irred : U'.toRepresentation.IsIrreducible := by
      exact isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule ρT mInt' hmInt'_simple
    let eT :
        Representation.Equiv
          (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom)
          ρT :=
      transportedSubrepresentation_rep_equiv ρ A W₀ g
    let Ug : Subrepresentation (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom) :=
      subrepresentationOrderIso eT.symm U
    let Ug' : Subrepresentation (ρW₀.comp (MulAut.conjNormal g⁻¹).toMonoidHom) :=
      subrepresentationOrderIso eT.symm U'
    have eUg : U.toRepresentation.Equiv Ug.toRepresentation := by
      -- Pull the first intrinsic constituent back through the transport equivalence.
      simpa [Ug] using subrepresentation_equiv_of_equiv_image eT.symm U
    have eUg' : U'.toRepresentation.Equiv Ug'.toRepresentation := by
      simpa [Ug'] using subrepresentation_equiv_of_equiv_image eT.symm U'
    have hUg_irred : Ug.toRepresentation.IsIrreducible := by
      letI : U.toRepresentation.IsIrreducible := hU_irred
      exact isIrreducible_of_equiv eUg
    have hUg'_irred : Ug'.toRepresentation.IsIrreducible := by
      letI : U'.toRepresentation.IsIrreducible := hU'_irred
      exact isIrreducible_of_equiv eUg'
    let U₀ : Subrepresentation ρW₀ := conjugatedSubrepresentationOrderIso A ρW₀ g Ug
    let U₀' : Subrepresentation ρW₀ := conjugatedSubrepresentationOrderIso A ρW₀ g Ug'
    have eU₀ :
        Ug.toRepresentation.Equiv
          (U₀.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
      -- Untwisting the first pulled-back constituent only changes the action formula.
      simpa [U₀] using conjugatedSubrepresentation_rep_equiv A ρW₀ g Ug
    have eU₀' :
        Ug'.toRepresentation.Equiv
          (U₀'.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := by
      simpa [U₀'] using conjugatedSubrepresentation_rep_equiv A ρW₀ g Ug'
    have hU₀_irred : U₀.toRepresentation.IsIrreducible := by
      letI : Ug.toRepresentation.IsIrreducible := hUg_irred
      let ρU₀conj : Representation ℂ A U₀.toSubmodule :=
        U₀.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom
      have hU₀_conj_irred :
          ρU₀conj.IsIrreducible :=
        isIrreducible_of_equiv eU₀
      -- Removing the conjugated action recovers an irreducible constituent of the original block.
      exact unconj_isIrreducible A U₀.toRepresentation g hU₀_conj_irred
    have hU₀'_irred : U₀'.toRepresentation.IsIrreducible := by
      letI : Ug'.toRepresentation.IsIrreducible := hUg'_irred
      let ρU₀'conj : Representation ℂ A U₀'.toSubmodule :=
        U₀'.toRepresentation.comp (MulAut.conjNormal g⁻¹).toMonoidHom
      have hU₀'_conj_irred :
          ρU₀'conj.IsIrreducible :=
        isIrreducible_of_equiv eU₀'
      exact unconj_isIrreducible A U₀'.toRepresentation g hU₀'_conj_irred
    let ρU₀ : Representation ℂ A U₀.toSubmodule := U₀.toRepresentation
    letI : Module (MonoidAlgebra ℂ A) ρU₀.asModule := ρU₀.instModuleMonoidAlgebraAsModule
    letI : Module (MonoidAlgebra ℂ A) U₀.toRepresentation.asModule :=
      U₀.toRepresentation.instModuleMonoidAlgebraAsModule
    let ρU₀' : Representation ℂ A U₀'.toSubmodule := U₀'.toRepresentation
    letI : Module (MonoidAlgebra ℂ A) ρU₀'.asModule := ρU₀'.instModuleMonoidAlgebraAsModule
    letI : Module (MonoidAlgebra ℂ A) U₀'.toRepresentation.asModule :=
      U₀'.toRepresentation.instModuleMonoidAlgebraAsModule
    have hU₀_simple : IsSimpleModule (MonoidAlgebra ℂ A) U₀.asSubmodule := by
      -- Convert irreducibility of the pulled-back constituent into owner-module simplicity.
      exact
        @IsSimpleModule.congr (MonoidAlgebra ℂ A) inferInstance U₀.asSubmodule
          U₀.asSubmodule.addCommGroup U₀.asSubmodule.module
          ρU₀.asModule ρU₀.instAddCommGroupAsModule ρU₀.instModuleMonoidAlgebraAsModule
          (subrepresentation_owner_intrinsic_linearEquiv (ρ := ρW₀) U₀).symm
          ((Representation.irreducible_iff_isSimpleModule_asModule ρU₀).mp hU₀_irred)
    have hU₀'_simple : IsSimpleModule (MonoidAlgebra ℂ A) U₀'.asSubmodule := by
      exact
        @IsSimpleModule.congr (MonoidAlgebra ℂ A) inferInstance U₀'.asSubmodule
          U₀'.asSubmodule.addCommGroup U₀'.asSubmodule.module
          ρU₀'.asModule ρU₀'.instAddCommGroupAsModule ρU₀'.instModuleMonoidAlgebraAsModule
          (subrepresentation_owner_intrinsic_linearEquiv (ρ := ρW₀) U₀').symm
          ((Representation.irreducible_iff_isSimpleModule_asModule ρU₀').mp hU₀'_irred)
    letI : IsSimpleModule (MonoidAlgebra ℂ A) U₀.asSubmodule := hU₀_simple
    letI : IsSimpleModule (MonoidAlgebra ℂ A) U₀'.asSubmodule := hU₀'_simple
    have hU₀_equiv :
        Nonempty (U₀'.asSubmodule ≃ₗ[MonoidAlgebra ℂ A] U₀.asSubmodule) :=
      by
        -- Compare the pulled-back simple constituents inside the original isotypic block `W₀`.
        exact
          pulled_back_constituents_equiv_in_isotypic_block
            (ρ := ρA) W₀ hW₀_owner U₀'.asSubmodule U₀.asSubmodule
    let e₀ :
        Representation.Equiv U₀'.toRepresentation U₀.toRepresentation :=
      subrepresentation_equiv_of_asSubmoduleLinearEquiv U₀' U₀ hU₀_equiv.some
    let eTransport :
        U'.toRepresentation.Equiv U.toRepresentation :=
      (((eUg'.trans eU₀').trans (representationEquiv_comp_conjNormal A e₀ g)).trans
        eU₀.symm).trans eUg.symm
    let eInt : mInt' ≃ₗ[MonoidAlgebra ℂ A] mInt :=
      ((subrepresentation_owner_intrinsic_linearEquiv (ρ := ρT) U').symm.trans
        (representationEquiv_asModuleLinearEquiv eTransport)).trans
        (subrepresentation_owner_intrinsic_linearEquiv (ρ := ρT) U)
    let eOwner : m' ≃ₗ[MonoidAlgebra ℂ A] m :=
      ((subrepresentation_owner_intrinsic_submodule_linearEquiv (ρ := ρA) T m').symm.trans
        eInt).trans
        (subrepresentation_owner_intrinsic_submodule_linearEquiv (ρ := ρA) T m)
    -- Transport both simple constituents to the original block, compare them there, then return.
    simpa using ⟨eOwner⟩

/-- Helper for Proposition 8-8.1-1: a transported `A`-isotypic component is again an
`A`-isotypic component. -/
private theorem transported_isotypic_component_mem
    (ρ : Representation ℂ G V) (A : Subgroup G) [A.Normal] [Finite A]
    [NeZero (Nat.card A : ℂ)] :
    let ρA : Representation ℂ A V := ρ.comp A.subtype
    letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
    ∀ c : isotypicComponents (MonoidAlgebra ℂ A) V, ∀ g : G,
      (transportedSubrepresentation ρ A (Subrepresentation.ofSubmodule' c.1) g).asSubmodule ∈
        isotypicComponents (MonoidAlgebra ℂ A) V :=
  by
    intro ρA
    letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
    intro c g
    let T : Submodule (MonoidAlgebra ℂ A) V :=
      (transportedSubrepresentation ρ A (Subrepresentation.ofSubmodule' c.1) g).asSubmodule
    have hc_full :
        (Subrepresentation.ofSubmodule' c.1).asSubmodule.IsFullyInvariant := by
      simpa using (Submodule.IsFullyInvariant.of_mem_isotypicComponents c.2)
    change T ∈ isotypicComponents (MonoidAlgebra ℂ A) V
    rw [mem_isotypicComponents_iff]
    exact
      ⟨transportedSubrepresentation_asSubmodule_isIsotypic ρ A c g,
        transportedSubrepresentation_asSubmodule_isFullyInvariant ρ A
          (Subrepresentation.ofSubmodule' c.1) g
          hc_full,
        transportedSubrepresentation_asSubmodule_ne_bot ρ A
          (Subrepresentation.ofSubmodule' c.1) g
          (bot_lt_isotypicComponents c.2).ne'⟩

/-- Helper for Proposition 8-8.1-1: every nonzero `H`-stable subrepresentation contains an
irreducible `H`-subrepresentation. -/
private theorem exists_irreducible_subrepresentation_le
    {H : Subgroup G} [Finite H]
    (ρH : Representation ℂ H V) (U : Subrepresentation ρH)
    (hU : U.asSubmodule ≠ ⊥) :
    ∃ W : Subrepresentation ρH,
      W.toSubmodule ≤ U.toSubmodule ∧
        W.toSubmodule ≠ ⊥ ∧
          W.toRepresentation.IsIrreducible := by
  letI : NeZero (Nat.card H : ℂ) := by
    exact ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  letI : Module (MonoidAlgebra ℂ H) V := ρH.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule (MonoidAlgebra ℂ H) V := by infer_instance
  obtain ⟨N, hNle, hNsimple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (R := MonoidAlgebra ℂ H) (M := V) U.asSubmodule).resolve_left hU
  let W : Subrepresentation ρH := Subrepresentation.ofSubmodule' N
  refine ⟨W, ?_, ?_, ?_⟩
  · -- The chosen simple owner submodule sits inside the original `H`-stable space.
    simpa [W] using hNle
  · -- A nonzero owner submodule remains nonzero after forgetting to the underlying `ℂ`-subspace.
    intro hW
    have hN_ne_bot : N ≠ ⊥ := by
      letI : IsSimpleModule (MonoidAlgebra ℂ H) N := hNsimple
      exact Submodule.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) N)
    apply hN_ne_bot
    ext v
    have hW' : (Subrepresentation.ofSubmodule' N).toSubmodule = (⊥ : Submodule ℂ V) := by
      simpa [W] using hW
    simpa using congrArg (fun S : Submodule ℂ V ↦ v ∈ S) hW'
  · -- Simplicity of the owner submodule upgrades to irreducibility of the bundled witness.
    exact isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule ρH N hNsimple

/-- Helper for Proposition 8-8.1-1: the supremum of the quotient-indexed translates of a
subrepresentation is stable under the ambient `G`-action. -/
private theorem leftQuotientSubmodule_iSup_stable
    (ρ : Representation ℂ G V)
    {H : Subgroup G}
    (U : Subrepresentation (ρ.comp H.subtype))
    (s : G) :
    (⨆ q : G ⧸ H, ρ.leftQuotientSubmodule H U q).map (ρ s) ≤
      ⨆ q : G ⧸ H, ρ.leftQuotientSubmodule H U q := by
  -- Route correction: instead of proving stability of the span abstractly, send each quotient
  -- summand into the corresponding `(s • q)`-summand and then take the supremum.
  calc
    (⨆ q : G ⧸ H, ρ.leftQuotientSubmodule H U q).map (ρ s) =
        ⨆ q : G ⧸ H, (ρ.leftQuotientSubmodule H U q).map (ρ s) := by
          rw [Submodule.map_iSup]
    _ ≤ ⨆ q : G ⧸ H, ρ.leftQuotientSubmodule H U q := by
          refine iSup_le fun q ↦ ?_
          have hq :
              (ρ.leftQuotientSubmodule H U q).map (ρ s) ≤
                ρ.leftQuotientSubmodule H U (s • q) := by
            refine Quotient.inductionOn' q ?_
            intro g
            change Submodule.map (ρ s) (Submodule.map (ρ g) U.toSubmodule) ≤
              ρ.leftQuotientSubmodule H U (((s * g : G) : G ⧸ H))
            rw [ρ.leftQuotientSubmodule_mk H U (s * g)]
            intro x hx
            rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
            rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
            exact Submodule.mem_map.mpr ⟨u, hu, by
              simpa [Module.End.mul_apply] using
                (LinearMap.congr_fun (ρ.map_mul s g) u).symm⟩
          exact hq.trans (le_iSup (fun q : G ⧸ H ↦ ρ.leftQuotientSubmodule H U q) (s • q))

/-- Helper for Proposition 8-8.1-1: once `ρ` is induced from an `H`-stable summand, ambient
irreducibility lets one shrink the inducing summand to any nonzero `H`-subrepresentation. -/
private theorem isInducedFromSubrepresentation_of_nonzero_le
    (ρ : Representation ℂ G V) [Finite G] [ρ.IsIrreducible]
    {H : Subgroup G} [Finite H]
    {U W : Subrepresentation (ρ.comp H.subtype)}
    (hUW : U.toSubmodule ≤ W.toSubmodule)
    (hUne : U.asSubmodule ≠ ⊥)
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    ρ.IsInducedFromSubrepresentation H U :=
  by
    classical
    let _ : DecidableEq (G ⧸ H) := Classical.decEq _
    let ℳW : G ⧸ H → Submodule ℂ V := ρ.leftQuotientSubmodule H W
    let ℳU : G ⧸ H → Submodule ℂ V := ρ.leftQuotientSubmodule H U
    have hInternalW : DirectSum.IsInternal ℳW := by
      -- Unpack the Chapter 3 owner for `W` into independence and spanning data.
      simpa [ℳW, Representation.IsInducedFromSubrepresentation] using hInd
    have hfamily_le : ℳU ≤ ℳW := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro g
      simpa [ℳU, ℳW, ρ.leftQuotientSubmodule_mk H U g, ρ.leftQuotientSubmodule_mk H W g] using
        (Submodule.map_mono hUW)
    have hIndepU : iSupIndep ℳU := by
      -- Independence descends pointwise because each `U`-translate lies in the corresponding
      -- `W`-translate.
      exact hInternalW.submodule_iSupIndep.mono hfamily_le
    let S : Submodule ℂ V := ⨆ q : G ⧸ H, ℳU q
    let Sρ : Subrepresentation ρ :=
      { toSubmodule := S
        apply_mem_toSubmodule := by
          intro s x hx
          -- Stability of the span is exactly the transport-to-the-shifted-coset statement above.
          have hxmap : ρ s x ∈ S.map (ρ s) := by
            exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
          exact leftQuotientSubmodule_iSup_stable ρ U s hxmap }
    have hU_to_ne : U.toSubmodule ≠ ⊥ := by
      let ρH : Representation ℂ H V := ρ.comp H.subtype
      intro hbot
      have hbot_as : U.asSubmodule = ⊥ := by
        ext v
        change ((v : V) ∈ U.toSubmodule) ↔ v ∈ (⊥ : Submodule (MonoidAlgebra ℂ H) ρH.asModule)
        rw [hbot]
        change v = 0 ↔ v = 0
        rfl
      exact hUne hbot_as
    have hS_ne_bot : S ≠ ⊥ := by
      intro hSbot
      apply hU_to_ne
      have hU_le_S : U.toSubmodule ≤ S := by
        intro x hx
        have hxq : x ∈ ρ.leftQuotientSubmodule H U ((1 : G) : G ⧸ H) := by
          rw [ρ.leftQuotientSubmodule_mk H U (1 : G)]
          exact Submodule.mem_map.mpr ⟨x, hx, by simpa using (LinearMap.congr_fun ρ.map_one x).symm⟩
        exact (show ρ.leftQuotientSubmodule H U ((1 : G) : G ⧸ H) ≤ S by
          simpa [S, ℳU] using
            (le_iSup (fun q : G ⧸ H ↦ ρ.leftQuotientSubmodule H U q) ((1 : G) : G ⧸ H))) hxq
      exact le_bot_iff.mp (hSbot ▸ hU_le_S)
    have hSρ_ne_bot : Sρ ≠ ⊥ := by
      intro hbot
      apply hS_ne_bot
      simpa [Sρ] using congrArg Subrepresentation.toSubmodule hbot
    have hSρ_top : Sρ = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top Sρ).resolve_left hSρ_ne_bot
    have hspanU : iSup ℳU = ⊤ := by
      -- Irreducibility forces the nonzero stable span of the `U`-translates to be all of `V`.
      simpa [S, Sρ] using congrArg Subrepresentation.toSubmodule hSρ_top
    -- Repackage the descended independence and top-span statements into inducedness.
    unfold Representation.IsInducedFromSubrepresentation
    exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndepU hspanU

/-- Helper for Proposition 8-8.1-1: if the restricted semisimple module has only one isotypic
component, then the whole restricted module is isotypic. -/
private theorem isIsotypic_of_subsingleton_isotypicComponents
    (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M]
    (hsub : Subsingleton (isotypicComponents R M)) :
    IsIsotypic R M := by
  classical
  by_cases hne : Nonempty (isotypicComponents R M)
  · rcases hne with ⟨⟨c, hc⟩⟩
    -- A singleton family of isotypic components has supremum equal to its unique member.
    have hsSup_le : sSup (isotypicComponents R M) ≤ c := by
      exact sSup_le fun m hm ↦ by
        have hm_eq : m = c := by
          exact congrArg Subtype.val (hsub.elim ⟨m, hm⟩ ⟨c, hc⟩)
        exact hm_eq ▸ le_rfl
    have htop_le : (⊤ : Submodule R M) ≤ c := by
      simpa [sSup_isotypicComponents R M] using hsSup_le
    have hc_top : c = ⊤ := top_unique htop_le
    -- Once the unique isotypic component is all of `M`, its isotypy is exactly the target claim.
    subst hc_top
    have htop_isotypic : IsIsotypic R ↥(⊤ : Submodule R M) := by
      simpa using (IsIsotypic.isotypicComponents hc)
    exact (LinearEquiv.isIsotypic_iff (e := (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M))).mp
      htop_isotypic
  · have hEmpty : isotypicComponents R M = ∅ := by
      ext m
      constructor
      · intro hm
        exact hne ⟨⟨m, hm⟩⟩
      · intro hm
        simp at hm
    have htop_eq_bot : (⊤ : Submodule R M) = ⊥ := by
      calc
        (⊤ : Submodule R M) = sSup (isotypicComponents R M) := (sSup_isotypicComponents R M).symm
        _ = sSup (∅ : Set (Submodule R M)) := by simp [hEmpty]
        _ = ⊥ := by simp
    letI : Subsingleton M := by
      refine ⟨fun x y ↦ ?_⟩
      have hx_top : x ∈ (⊤ : Submodule R M) := by simp
      have hy_top : y ∈ (⊤ : Submodule R M) := by simp
      have hx_bot : x ∈ (⊥ : Submodule R M) := by simpa [htop_eq_bot] using hx_top
      have hy_bot : y ∈ (⊥ : Submodule R M) := by simpa [htop_eq_bot] using hy_top
      have hx_zero : x = 0 := by simpa [Submodule.mem_bot] using hx_bot
      have hy_zero : y = 0 := by simpa [Submodule.mem_bot] using hy_bot
      simp [hx_zero, hy_zero]
    -- The zero module is automatically isotypic.
    exact IsIsotypic.of_subsingleton R M

/-- Helper for Proposition 8-8.1-1: converting a set-indexed family of owner submodules into the
corresponding subtype-indexed family of bundled subrepresentations preserves independence and
spanning after forgetting from `ℂ[A]` to `ℂ`. -/
private theorem iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family
    {A' : Type*} [Group A']
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ A' V') (s : Set (Submodule (MonoidAlgebra ℂ A') ρ.asModule))
    (hs_indep : sSupIndep s) (hs_top : sSup s = ⊤) :
    iSupIndep (fun i : s ↦ (Subrepresentation.ofSubmodule' i.1).toSubmodule) ∧
      (⨆ i : s, (Subrepresentation.ofSubmodule' i.1).toSubmodule) = ⊤ := by
  -- Convert the set-indexed independence to the subtype-indexed owner family first.
  have hs_indep' : iSupIndep (fun i : s ↦ (i : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) :=
    (sSupIndep_iff s).mp hs_indep
  -- Restrict scalars from `ℂ[A]` to `ℂ`; this keeps both independence and the top supremum.
  have hσ_indep :
      iSupIndep (fun i : s ↦ Submodule.restrictScalars ℂ (i : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) := by
    rw [iSupIndep] at hs_indep'
    rw [iSupIndep]
    intro i
    rw [disjoint_iff_inf_le]
    have hi :
        ((i : Submodule (MonoidAlgebra ℂ A') ρ.asModule) ⊓
            ⨆ (j : s) (_ : j ≠ i), (j : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) ≤ ⊥ := by
      simpa [disjoint_iff_inf_le] using hs_indep' i
    simpa [Submodule.restrictScalars_inf, Submodule.restrictScalars_iSup] using
      (Submodule.restrictScalars_mono (S := ℂ) (hst := hi))
  have hs_top' : (⨆ i : s, (i : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) = ⊤ := by
    simpa [sSup_eq_iSup'] using hs_top
  have hσ_top :
      (⨆ i : s, Submodule.restrictScalars ℂ (i : Submodule (MonoidAlgebra ℂ A') ρ.asModule)) = ⊤ := by
    simpa [Submodule.restrictScalars_iSup] using
      congrArg (Submodule.restrictScalars ℂ) hs_top'
  -- `Subrepresentation.ofSubmodule'` is definitionally the restricted-scalar carrier.
  simpa using ⟨hσ_indep, hσ_top⟩
-- Proof sketch: decompose the restricted representation `ρ.comp A.subtype` into its isotypic
-- summands. Conjugation by elements of `G` permutes these summands because `A` is normal. Since
-- `ρ` is irreducible, this permutation action is transitive. If there is only one summand, the
-- restriction is isotypic. Otherwise, choose one summand, let `H` be its stabilizer in `G`, and
-- identify `ρ` with the representation induced from the corresponding irreducible `H`
-- subrepresentation.
/-
Source/core/bridge triage:
* `source-facing`: Serre's alternative between induction from a proper overgroup containing `A`
  and isotypy of the restriction to `A`.
* `core/canonical`: the owner predicates are `Representation.IsInducedFromSubrepresentation` and
  `IsIsotypic` on the carrier `V` equipped with the restricted `MonoidAlgebra ℂ A`-module
  structure coming from `ρ.comp A.subtype`.
* `bridge/view`: the proper-overgroup branch is just an existential packaging of subgroup
  containment, properness, irreducibility of the chosen `H`-subrepresentation, and the canonical
  induction owner, so it should stay a direct existential; if one wants to name the irreducible
  type in the isotypic branch explicitly, that belongs to the companion predicate
  `IsIsotypicOfType`, not to the main proposition surface.
-/
/-- Proposition 8-8.1-1: if `A` is a normal subgroup of the finite group `G` and `ρ` is an
irreducible complex representation of `G`, then either `ρ` is induced from an irreducible
`H`-subrepresentation for some proper subgroup `H` containing `A`, or the restriction of `ρ` to
`A` is isotypic as a `MonoidAlgebra ℂ A`-module. For finite groups, the semisimplicity and
finite-dimensional input needed for the isotypic language are derived internally from
`ρ.IsIrreducible`. -/
theorem exists_proper_overgroup_irreducible_induced_or_restriction_isotypic
    (ρ : Representation ℂ G V) [Finite G] [ρ.IsIrreducible] (A : Subgroup G) [A.Normal] :
    (∃ H : Subgroup G,
      A ≤ H ∧ H < ⊤ ∧
        ∃ W : Subrepresentation (ρ.comp H.subtype),
          W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) ∨
      (let ρA : Representation ℂ A V := ρ.comp A.subtype
       letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
       IsIsotypic (MonoidAlgebra ℂ A) V) := by
  classical
  let ρA : Representation ℂ A V := ρ.comp A.subtype
  letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
  letI : Finite A := by infer_instance
  letI : NeZero (Nat.card A : ℂ) := by
    exact ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  letI : IsSemisimpleModule (MonoidAlgebra ℂ A) V := by infer_instance
  -- Split first by Serre's dichotomy on the number of isotypic summands for the restricted
  -- `A`-module.
  by_cases hsub : Subsingleton (isotypicComponents (MonoidAlgebra ℂ A) V)
  · -- A unique isotypic component must be the whole restricted module, giving branch (b).
    right
    simpa [ρA] using
      isIsotypic_of_subsingleton_isotypicComponents
        (R := MonoidAlgebra ℂ A) (M := V) hsub
  · -- Route correction: the owner-module bridges are now proved, so the remaining blocker is no
    -- longer the intrinsic-vs-owner conversion. With the stabilizer wrapper and transported
    -- membership packaged, the Chapter 7 argument now runs on the actual component set; the only
    -- remaining structural gaps are the transport-isotypy lemma and the descent-from-a-nonzero
    -- subrepresentation lemma recorded above.
    let I := isotypicComponents (MonoidAlgebra ℂ A) V
    let W : I → Submodule ℂ V := fun c ↦ (Subrepresentation.ofSubmodule' c.1).toSubmodule
    letI : MulAction G I := {
      smul := fun g c ↦
        ⟨(transportedSubrepresentation ρ A (Subrepresentation.ofSubmodule' c.1) g).asSubmodule,
          transported_isotypic_component_mem ρ A c g⟩
      one_smul := by
        intro c
        apply Subtype.ext
        ext v
        constructor
        · intro hv
          rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
          simpa using hw
        · intro hv
          refine Submodule.mem_map.mpr ⟨v, hv, ?_⟩
          simpa using (LinearMap.congr_fun ρ.map_one v).symm
      mul_smul := by
        intro g h c
        apply Subtype.ext
        ext v
        constructor
        · intro hv
          rcases Submodule.mem_map.mp hv with ⟨w, hw, hwv⟩
          refine Submodule.mem_map.mpr ⟨ρ h w, ?_, ?_⟩
          · exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
          · simpa [LinearMap.comp_apply] using hwv
        · intro hv
          rcases Submodule.mem_map.mp hv with ⟨w, hw, hwv⟩
          rcases Submodule.mem_map.mp hw with ⟨u, hu, rfl⟩
          refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
          simpa [LinearMap.comp_apply] using hwv }
    -- Transport by `ρ g` is definitionally the permutation relation needed by Remark 7-7.1-4.
    have hperm : ρ.PermutesSubmoduleFamily W := by
      intro g c
      rfl
    have hcomponents :
        iSupIndep W ∧ (⨆ c : I, W c) = ⊤ :=
      iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family (ρ := ρA)
        (s := isotypicComponents (MonoidAlgebra ℂ A) V)
        (hs_indep := sSupIndep_isotypicComponents (MonoidAlgebra ℂ A) V)
        (hs_top := sSup_isotypicComponents (MonoidAlgebra ℂ A) V)
    have hindep : iSupIndep W := hcomponents.1
    have hspan : (⨆ c : I, W c) = ⊤ := hcomponents.2
    have hne : ∀ c : I, W c ≠ ⊥ := fun c ↦ by
      intro hbot
      apply (bot_lt_isotypicComponents c.2).ne'
      ext x
      change x ∈ c.1 ↔ x ∈ (⊥ : Submodule (MonoidAlgebra ℂ A) V)
      simpa [W] using congrArg (fun S : Submodule ℂ V ↦ x ∈ S) hbot
    letI : MulAction.IsPretransitive G I :=
      Representation.IsIrreducible.isPretransitive_of_permuted_internalSummands
        ρ W hindep hperm hne
    letI : Nontrivial I := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨c₀, c₁, hc_ne⟩ := exists_pair_ne I
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G c₀ c₁
    let H : Subgroup G := ρ.submoduleStabilizer (W c₀)
    have hA_le_H : A ≤ H := by
      -- Each `A`-element stabilizes every isotypic summand.
      simpa [H, W] using stabilizer_contains_A_of_isotypic_component ρ A c₀
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hg_mem : g ∈ H := by simpa [H, htop]
      have hW_eq : W c₁ = W c₀ := by
        calc
          W c₁ = W (g • c₀) := by simpa [hg]
          _ = (W c₀).map (ρ g) := (hperm g c₀).symm
          _ = W c₀ := (mem_submoduleStabilizer_iff_map_eq ρ (W c₀)).mp hg_mem
      have hc_eq : c₀.1 = c₁.1 := by
        ext x
        change x ∈ c₀.1 ↔ x ∈ c₁.1
        simpa [W] using congrArg (fun S : Submodule ℂ V ↦ x ∈ S) hW_eq.symm
      exact hc_ne (Subtype.ext hc_eq)
    have hH_lt : H < ⊤ := lt_top_iff_ne_top.mpr hH_ne_top
    have hIndW :
        ρ.IsInducedFromSubrepresentation H (ρ.stabilizedSubrepresentation (W c₀)) := by
      -- Remark 7-7.1-4 converts the permuted internal decomposition into an induced witness.
      simpa [H, W] using
        Representation.IsIrreducible.isInducedFromStabilizer_of_permuted_internalSummands
          ρ W c₀ hindep hspan hperm hne
    let ρH : Representation ℂ H V := ρ.comp H.subtype
    have hW₀_ne :
        (ρ.stabilizedSubrepresentation (W c₀)).asSubmodule ≠ ⊥ := by
      intro hbot
      have hbot_to :
          (ρ.stabilizedSubrepresentation (W c₀)).toSubmodule = ⊥ := by
        ext v
        change v ∈ (ρ.stabilizedSubrepresentation (W c₀)).asSubmodule ↔
            v ∈ (⊥ : Submodule (MonoidAlgebra ℂ H) ρH.asModule)
        rw [hbot]
      exact hne c₀ <| by simpa [H, W] using hbot_to
    obtain ⟨U, hU_le, hU_ne, hU_irred⟩ :=
      exists_irreducible_subrepresentation_le
        ρH (ρ.stabilizedSubrepresentation (W c₀)) hW₀_ne
    have hU_as_ne : U.asSubmodule ≠ ⊥ := by
      intro hbot
      have hbot_to : U.toSubmodule = ⊥ := by
        ext v
        change v ∈ U.asSubmodule ↔ v ∈ (⊥ : Submodule (MonoidAlgebra ℂ H) ρH.asModule)
        rw [hbot]
      exact hU_ne hbot_to
    have hIndU : ρ.IsInducedFromSubrepresentation H U :=
      isInducedFromSubrepresentation_of_nonzero_le ρ hU_le hU_as_ne hIndW
    -- Pick an irreducible constituent inside the stabilized isotypic summand and descend the
    -- induced witness to it.
    left
    exact ⟨H, hA_le_H, hH_lt, U, hU_irred, hIndU⟩

end

end

end Representation
