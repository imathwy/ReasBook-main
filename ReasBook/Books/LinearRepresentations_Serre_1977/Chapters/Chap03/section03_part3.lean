import Mathlib
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_3_3_1 (from Chap03) -/
universe u v w

namespace Representation

noncomputable section

section InducedFromSubrepresentation

variable {k : Type u} {G : Type v} [Semiring k] [Group G]
variable {V : Type w} [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V) (H : Subgroup G)
variable (W : Subrepresentation (ρ.comp H.subtype))

/-- If two elements of `G` lie in the same left coset of `H`, then they send an `H`-stable
submodule `W` to the same submodule of `V`. -/
-- Proof sketch: from the left-coset relation write one representative as the other multiplied by
-- an element of `H`; because `W` is stable under the restricted action of `H`, applying that
-- element preserves `W`, so mapping `W` by the two operators gives the same image.
private theorem leftQuotientSubmodule_eq_of_leftRel {s t : G}
    (hst : QuotientGroup.leftRel H s t) :
    W.toSubmodule.map (ρ s) = W.toSubmodule.map (ρ t) := by
  rw [le_antisymm_iff]
  constructor
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
    rw [QuotientGroup.leftRel_apply] at hst
    let h : H := ⟨s⁻¹ * t, hst⟩
    -- Replace the representative `s` by `t = s * h`; this is the coset-change step.
    refine Submodule.mem_map.mpr ?_
    refine ⟨ρ h⁻¹ w, W.apply_mem_toSubmodule h⁻¹ hw, ?_⟩
    -- The inverse subgroup element sends the witness back into `W`, so the image is unchanged.
    change ρ t (ρ h⁻¹ w) = ρ s w
    calc
      ρ t (ρ h⁻¹ w) = ρ (s * h) (ρ h⁻¹ w) := by
        congr 1
        simp [h]
      _ = ρ s (ρ h (ρ h⁻¹ w)) := by
        simp [Module.End.mul_apply, map_mul]
      _ = ρ s w := by
        simp
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
    rw [QuotientGroup.leftRel_apply] at hst
    let h : H := ⟨s⁻¹ * t, hst⟩
    -- The reverse inclusion uses the same subgroup element to move the witness back.
    refine Submodule.mem_map.mpr ?_
    refine ⟨ρ h w, W.apply_mem_toSubmodule h hw, ?_⟩
    change ρ s (ρ h w) = ρ t w
    calc
      ρ s (ρ h w) = ρ (s * h) w := by
        simp [Module.End.mul_apply, map_mul]
      _ = ρ t w := by
        congr 1
        simp [h]

/-- The family of translates of `W` indexed by the left cosets `G ⧸ H`. -/
def leftQuotientSubmodule : G ⧸ H → Submodule k V :=
  Quotient.lift
    (fun g : G ↦ W.toSubmodule.map (ρ g))
    (fun _ _ h ↦ leftQuotientSubmodule_eq_of_leftRel ρ H W h)

@[simp] theorem leftQuotientSubmodule_mk (g : G) :
    ρ.leftQuotientSubmodule H W (g : G ⧸ H) = W.toSubmodule.map (ρ g) :=
  rfl

/-- Definition 3-3.3-1: the representation `ρ` is induced by the restricted representation on an
`H`-stable subspace `W` when the transported subspaces indexed by the left cosets `G ⧸ H` are
the summands of an internal direct sum decomposition of `V`. -/
def IsInducedFromSubrepresentation : Prop :=
  let _ : DecidableEq (G ⧸ H) := Classical.decEq _
  DirectSum.IsInternal (ρ.leftQuotientSubmodule H W)

end InducedFromSubrepresentation

section IsMonomial

variable {k : Type u} {G : Type v} [DivisionRing k] [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- A representation is monomial if it is induced from a one-dimensional subrepresentation of a
subgroup. -/
def IsMonomial (ρ : Representation k G V) : Prop :=
  ∃ H : Subgroup G, ∃ W : Subrepresentation (ρ.comp H.subtype),
    Module.finrank k W.toSubmodule = 1 ∧
      ρ.IsInducedFromSubrepresentation H W

end IsMonomial

end

end Representation

/-! ### Exercise_3_3_3_5 (from Chap03) -/
universe u v w

namespace Representation

section

open CategoryTheory
open scoped MonoidAlgebra

variable {G : Type u} [Group G] [Finite G]
variable {k : Type v} [Field k]
variable {H : Subgroup G}

-- Source/core/bridge triage:
-- * source-facing: existence of an irreducible `H`-representation whose induced
--   `G`-representation contains `X` as a subrepresentation.
-- * core/canonical owners: subgroup induction is `Rep.ind H.subtype`, and literal
--   subrepresentations are owned by `Subrepresentation`.
-- * bridge/view: `Rep.of U.toRepresentation` is the canonical rebundling of the chosen
--   subrepresentation `U` as an object of `Rep k G`.
--
-- Primitive data are the subgroup `H`, the irreducible inducing representation `W`, and the
-- subrepresentation `U` of `Rep.ind H.subtype W`. The final equivalence with `X` is derived data,
-- so the theorem exposes those witnesses directly rather than through a separate wrapper; the only
-- remaining `Nonempty` is the proposition-level packaging of the resulting isomorphism witness.
-- Proof sketch: view the given irreducible representation as an irreducible constituent of the
-- regular representation of `G`. Restrict the regular representation to `H`, choose an
-- irreducible `H`-subrepresentation occurring there, and use Frobenius reciprocity together with
-- the universal property of induction to obtain a nonzero intertwining map from `X` to the
-- induced representation from that `H`-representation. Irreducibility of `X` makes this map an
-- embedding, so `X` is isomorphic to a subrepresentation of the induced representation. For a
-- finite group, irreducible representations over a field are automatically finite-dimensional by
-- `IsIrreducible.finiteDimensional_of_finite`, so the statement is expressed without extra
-- finite-dimensionality data.
omit [Finite G] in
/-- Helper for Exercise 3-3.3-5: a nontrivial finite-dimensional `k[H]`-module admits a nonzero
map onto an irreducible `H`-representation coming from a simple quotient. -/
private theorem exists_irreducible_quotient_of_finiteDimensional_nontrivial
    (H : Subgroup G) (M : ModuleCat k[H]) [Module.Finite k[H] M] [Nontrivial M] :
    ∃ (W : Rep k H) (_ : W.ρ.IsIrreducible)
      (q : ((Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H).obj M ⟶ W)),
        q ≠ 0 := by
  -- Finite generation over `k[H]` makes the owner module coatomic.
  let ofH : ModuleCat k[H] ⥤ Rep k H := Rep.ofModuleMonoidAlgebra
  obtain ⟨N, hN, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule k[H] M)).resolve_left bot_ne_top
  let W : Rep k H := ofH.obj (ModuleCat.of k[H] (M ⧸ N))
  have hWirr : W.ρ.IsIrreducible := by
    -- A coatom quotient is simple, hence irreducible in the canonical `Rep` owner.
    have hSimple : IsSimpleModule k[H] (M ⧸ N) := (isSimpleModule_iff_isCoatom).2 hN
    simpa [W, Rep.ofModuleMonoidAlgebra_obj_ρ] using
      (Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp hSimple
  let q : ofH.obj M ⟶ W := ofH.map (ModuleCat.ofHom (Submodule.mkQ N))
  have hmkQ_nonzero : Submodule.mkQ N ≠ 0 := by
    -- The quotient map is nonzero because a proper coatom omits some vector.
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN.1)
    intro hzero
    have hx0 : (Submodule.mkQ N) x = 0 := by
      simp [hzero]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx0
    exact hx hx0
  have hq_nonzero : q ≠ 0 := by
    -- Faithfulness of `ofModuleMonoidAlgebra` reflects the nonvanishing of `mkQ`.
    intro hq
    apply hmkQ_nonzero
    have hmodule : ModuleCat.ofHom (Submodule.mkQ N) = 0 := ofH.map_injective hq
    ext x
    have hpoint :=
      congrArg (fun f : M ⟶ ModuleCat.of k[H] (M ⧸ N) ↦ f.hom x) hmodule
    simpa using hpoint
  exact ⟨W, hWirr, q, hq_nonzero⟩

omit [Finite G] in
/-- Helper for Exercise 3-3.3-5: an injective morphism identifies its source with its image
subrepresentation. -/
private theorem equiv_to_range_of_injective_hom
    {X Y : Rep k G} (f : X ⟶ Y) (hf : Function.Injective f.hom) :
    let U := f.hom.range
    Nonempty (X.ρ.Equiv U.toRepresentation) := by
  let U := f.hom.range
  let fLin := f.hom.toLinearMap
  let fRangeLin := fLin.rangeRestrict
  let fRange : X.ρ.IntertwiningMap U.toRepresentation :=
    fRangeLin.intertwiningMap_of_isIntertwiningMap X.ρ U.toRepresentation
      (by
        -- The range is stable because `f` intertwines the two actions.
        intro g x
        apply Subtype.ext
        change f.hom (X.ρ g x) = Y.ρ g (f.hom x)
        simpa using congrArg (fun l : X →ₗ[k] Y ↦ l x) (f.hom.2 g))
  have hfRange_bijective : Function.Bijective fRange := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hf
      exact congrArg Subtype.val hxy
    · simpa [fRange, fLin, fRangeLin] using fLin.surjective_rangeRestrict
  exact ⟨fRange.ofBijective hfRange_bijective⟩

/-- Exercise 3-3.3-5: every irreducible `k`-representation of a finite group `G` is
equivariantly isomorphic to a subrepresentation of a representation induced from some irreducible
`k`-representation of the subgroup `H`. -/
theorem exists_subrepresentation_equiv_induced_from_irreducible
    (H : Subgroup G) (X : Rep.{max (max u v) w} k G) [X.ρ.IsIrreducible] :
    ∃ (W : Rep.{max (max u v) w} k H) (_ : W.ρ.IsIrreducible)
      (U : Subrepresentation (Rep.ind H.subtype W).ρ),
        Nonempty (X.ρ.Equiv U.toRepresentation) := by
  let XH := Rep.res H.subtype X
  letI : Module k[G] X := X.ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule k[G] X := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule X.ρ).mp inferInstance
  letI : Nontrivial X := IsSimpleModule.nontrivial k[G] X
  letI : FiniteDimensional k X := IsIrreducible.finiteDimensional_of_finite X.ρ
  letI : FiniteDimensional k XH := by infer_instance
  letI : Nontrivial XH := by infer_instance
  letI : Module k[H] XH.ρ.asModule := inferInstance
  let e := XH.ρ.asModuleEquiv
  letI : Module.Finite k[H] XH.ρ.asModule := by
    letI : Module.Finite k XH.ρ.asModule :=
      Module.Finite.of_surjective e.symm.toLinearMap fun y ↦
        ⟨e y, by simp⟩
    exact Module.Finite.of_restrictScalars_finite k k[H] XH.ρ.asModule
  letI : Nontrivial XH.ρ.asModule := e.toEquiv.nontrivial
  let ofH : ModuleCat k[H] ⥤ Rep k H := Rep.ofModuleMonoidAlgebra
  let MXH : ModuleCat k[H] := Rep.toModuleMonoidAlgebra.obj XH
  letI : Module.Finite k[H] MXH := by
    simpa [MXH] using (inferInstance : Module.Finite k[H] XH.ρ.asModule)
  letI : Nontrivial MXH := by
    simpa [MXH] using (inferInstance : Nontrivial XH.ρ.asModule)
  -- First choose an irreducible quotient of the restricted representation on the owner-module side.
  have hquotient :
      ∃ (W : Rep.{max (max u v) w} k H) (_ : W.ρ.IsIrreducible) (q : ofH.obj MXH ⟶ W), q ≠ 0 := by
    simpa [MXH] using
      exists_irreducible_quotient_of_finiteDimensional_nontrivial H MXH
  obtain ⟨W, hWirr, qModule, hqModule⟩ := hquotient
  let q : XH ⟶ W := XH.unitIso.hom ≫ qModule
  have hq : q ≠ 0 := by
    -- Precomposing with the inverse unit isomorphism reduces back to the module quotient.
    intro hq
    apply hqModule
    have hcomp := congrArg (fun m ↦ XH.unitIso.inv ≫ m) hq
    simpa [q] using hcomp
  -- Then use the finite-index `Res ⊣ Ind` adjunction to get a nonzero map into the induced
  -- representation.
  classical
  letI : DecidableRel ⇑(QuotientGroup.rightRel H) := Classical.decRel _
  let f := (Rep.resIndAdjunction k H).homEquiv X W q
  have hf : f ≠ 0 := by
    -- The adjunction hom-equivalence reflects nonvanishing.
    intro hf
    apply hq
    have hsymm_zero :
        ((Rep.resIndAdjunction k H).homEquiv X W).symm
            (0 : X ⟶ Rep.ind H.subtype W) = 0 := by
      simpa using
        (Rep.resIndAdjunction_homEquiv_symm_apply W (0 : X ⟶ Rep.ind H.subtype W))
    calc
      q = ((Rep.resIndAdjunction k H).homEquiv X W).symm f := by
        symm
        exact ((Rep.resIndAdjunction k H).homEquiv X W).left_inv q
      _ = ((Rep.resIndAdjunction k H).homEquiv X W).symm 0 := by rw [hf]
      _ = 0 := hsymm_zero
  have hf_injective : Function.Injective f.hom := by
    -- Irreducibility of `X` upgrades any nonzero intertwiner out of `X` to an embedding.
    refine
      (Representation.IsIrreducible.injective_or_eq_zero f.hom).resolve_right ?_
    intro hf_zero
    apply hf
    ext x
    exact congrArg (fun ℓ ↦ ℓ x) hf_zero
  -- Finally identify `X` with the image subrepresentation of that injective map.
  refine ⟨W, hWirr, f.hom.range, ?_⟩
  simpa using equiv_to_range_of_injective_hom f hf_injective

end

end Representation

/-! ### Exercise_3_3_3_6 (from Chap03) -/
universe u v w

namespace Representation

noncomputable section

section InducedFromCoinducedModel

variable {k : Type u} {G : Type v} [Semiring k] [Group G]
variable (H : Subgroup G)
variable {W : Type w} [AddCommMonoid W] [Module k W]
variable (θ : Representation k H W)

local instance : CoeFun (θ.coindV H.subtype) (fun _ ↦ G → W) where
  coe f := f.1

/-- The right-translation action of `H` preserves the property of being supported on `H`. -/
-- Proof sketch: if `u ∉ H` and `t ∈ H`, then also `u * t ∉ H`, so the translated function still
-- vanishes at `u`.
private theorem supportedOnSubgroup_apply_mem (t : H)
    {f : θ.coindV H.subtype}
    (hf : Function.support f ⊆ (H : Set G)) :
    Function.support (((θ.coind H.subtype).comp H.subtype) t f) ⊆ (H : Set G) :=
  by
  -- Rephrase support containment as pointwise vanishing away from `H`.
  rw [Function.support_subset_iff'] at hf ⊢
  intro u hu
  have hut : u * t ∉ H := by
    intro hut
    have hu' : u ∈ H := by
      have : (u * t) * t⁻¹ ∈ H := H.mul_mem hut (H.inv_mem t.2)
      simpa [mul_assoc] using this
    exact hu hu'
  simpa using hf (u * t) hut

/-- The `H`-subrepresentation `W₀ ⊆ V` of functions supported on `H`. -/
def supportedOnSubgroupSubrepresentation :
    Subrepresentation ((θ.coind H.subtype).comp H.subtype) where
  toSubmodule := {
    carrier := {f | Function.support f ⊆ (H : Set G)}
    zero_mem' := by
      simp
    add_mem' := fun hf hg ↦
      (Function.support_add _ _).trans <| Set.union_subset hf hg
    smul_mem' := fun a f hf ↦ by
      simpa using
        (Function.support_smul_subset_right (fun _ : G ↦ a) (f : G → W)).trans hf
  }
  apply_mem_toSubmodule := supportedOnSubgroup_apply_mem H θ

local notation "W₀" => supportedOnSubgroupSubrepresentation H θ

/-- Membership in the subgroup-supported subrepresentation is support containment in `H`. -/
theorem mem_supportedOnSubgroupSubrepresentation_iff
    (f : θ.coindV H.subtype) :
    f ∈ W₀ ↔ Function.support (f : G → W) ⊆ (H : Set G) :=
  Iff.rfl

/-- Membership in the subgroup-supported subrepresentation is vanishing away from `H`. -/
theorem mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem
    (f : θ.coindV H.subtype) :
    f ∈ W₀ ↔ ∀ u : G, u ∉ H → f u = 0 := by
  rw [mem_supportedOnSubgroupSubrepresentation_iff]
  simpa using (Function.support_subset_iff' :
    Function.support (f : G → W) ⊆ (H : Set G) ↔ ∀ u, u ∉ (H : Set G) → f u = 0)

/-- The underlying function of `f_w`, equal to `θ_u w` on `H` and `0` outside `H`. -/
private def subgroupSupportedFunctionFun (w : W) : G → W :=
  let _ : DecidablePred (fun u : G ↦ u ∈ H) := Classical.decPred _
  fun u ↦ if hu : u ∈ H then θ ⟨u, hu⟩ w else 0

/-- The function `f_w` lies in the canonical coinduced-function model `θ.coindV H.subtype`. -/
-- Proof sketch: split into whether the argument lies in `H`; on `H`, the covariance identity is
-- exactly the representation law for `θ`, and off `H` both sides are zero.
private theorem subgroupSupportedFunction_mem_coindV (w : W) :
    subgroupSupportedFunctionFun H θ w ∈ θ.coindV H.subtype :=
  by
  -- Check the coinduced covariance relation pointwise.
  rw [Representation.mem_coindV]
  intro t u
  by_cases hu : u ∈ H
  · -- On `H`, the defining formula reduces to the representation law for `θ`.
    have hmul : (t : G) * u ∈ H := H.mul_mem t.2 hu
    simpa only [subgroupSupportedFunctionFun, hu, hmul, Subgroup.subtype_apply] using
      LinearMap.congr_fun (θ.map_mul t ⟨u, hu⟩) w
  · -- Outside `H`, both sides vanish because left multiplication by `t ∈ H` preserves
    -- non-membership in the subgroup.
    have hmul : (t : G) * u ∉ H := by
      intro hmul
      apply hu
      have : ((t : G)⁻¹) * ((t : G) * u) ∈ H := H.mul_mem (H.inv_mem t.2) hmul
      simpa [mul_assoc] using this
    simpa only [subgroupSupportedFunctionFun, hu, hmul, Subgroup.subtype_apply] using
      (map_zero (θ t)).symm

/-- The element `f_w` of the canonical coinduced-function representation `θ.coind H.subtype`. -/
def subgroupSupportedFunction (w : W) : θ.coindV H.subtype :=
  ⟨subgroupSupportedFunctionFun H θ w,
    subgroupSupportedFunction_mem_coindV H θ w⟩

/-- On elements of `H`, the function `f_w` is given by the `H`-action on `w`. -/
-- Proof sketch: unfold `subgroupSupportedFunction` and evaluate the defining `if`.
theorem subgroupSupportedFunction_of_mem (w : W) {u : G} (hu : u ∈ H) :
    subgroupSupportedFunction H θ w u = θ ⟨u, hu⟩ w := by
  -- On `H` the defining `if` takes the representation branch.
  simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/-- Outside `H`, the function `f_w` vanishes. -/
-- Proof sketch: unfold `subgroupSupportedFunction` and evaluate the defining `if`.
theorem subgroupSupportedFunction_of_not_mem (w : W) {u : G} (hu : u ∉ H) :
    subgroupSupportedFunction H θ w u = 0 := by
  -- Away from `H` the defining `if` forces the function to vanish.
  simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/-- The function `f_w` belongs to the subgroup-supported subrepresentation `W₀`. -/
-- Proof sketch: this follows immediately from the defining formula for `f_w`.
theorem subgroupSupportedFunction_mem_supportedOnSubgroupSubrepresentation (w : W) :
    subgroupSupportedFunction H θ w ∈ W₀ := by
  -- The explicit formula for `f_w` vanishes on every point outside `H`.
  rw [mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem]
  intro u hu
  simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/-- The map `w ↦ f_w` is additive. -/
-- Proof sketch: both sides are functions with the same pointwise values on and off `H`.
private theorem subgroupSupportedFunction_add (w₁ w₂ : W) :
    subgroupSupportedFunction H θ (w₁ + w₂) =
      subgroupSupportedFunction H θ w₁ + subgroupSupportedFunction H θ w₂ := by
  -- Compare the two coinduced functions pointwise on and off `H`.
  ext u
  by_cases hu : u ∈ H
  · simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu, map_add]
  · simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/- The map `w ↦ f_w` is `k`-linear. -/
-- Proof sketch: compare pointwise values and use linearity of the representation maps `θ_u`.
private theorem subgroupSupportedFunction_smul (a : k) (w : W) :
    subgroupSupportedFunction H θ (a • w) =
      a • subgroupSupportedFunction H θ w := by
  -- Compare the two coinduced functions pointwise on and off `H`.
  ext u
  by_cases hu : u ∈ H
  · simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu, map_smul]
  · simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/-- The linear map `w ↦ f_w` into the canonical coinduced-function model `θ.coindV H.subtype`. -/
private def subgroupSupportedFunctionLinearMap :
    W →ₗ[k] θ.coindV H.subtype where
  toFun := subgroupSupportedFunction H θ
  map_add' := subgroupSupportedFunction_add H θ
  map_smul' := subgroupSupportedFunction_smul H θ

/-- The map `w ↦ f_w` intertwines `θ` with the restricted coinduced action. -/
-- Proof sketch: compare the two subgroup-supported functions pointwise; on each `u ∈ G`, both
-- sides are the value of `f_w` translated by `t`, which is exactly the `H`-equivariance built into
-- the coinduced model.
private theorem subgroupSupportedFunction_isIntertwining
    (t : H) (w : W) :
    subgroupSupportedFunction H θ (θ t w) =
      ((θ.coind H.subtype).comp H.subtype) t (subgroupSupportedFunction H θ w) := by
  -- Compare the two functions pointwise.
  ext u
  by_cases hu : u ∈ H
  · -- On `H`, right translation stays inside `H`, so the two formulas differ only by the
    -- representation law for `θ`.
    have hmul : u * t ∈ H := H.mul_mem hu t.2
    simpa only [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu, hmul,
      MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, coind_apply,
      LinearMap.restrict_coe_apply, LinearMap.funLeft_apply] using
      (LinearMap.congr_fun (θ.map_mul ⟨u, hu⟩ t) w).symm
  · -- Off `H`, both sides vanish because right translation by `t ∈ H` cannot move the argument
    -- into `H`.
    have hmul : u * t ∉ H := by
      intro hmul
      apply hu
      have : (u * (t : G)) * (t : G)⁻¹ ∈ H := H.mul_mem hmul (H.inv_mem t.2)
      simpa [mul_assoc] using this
    simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu, hmul,
      MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, coind_apply,
      LinearMap.restrict_coe_apply, LinearMap.funLeft_apply]

/-- The canonical `H`-equivariant map `w ↦ f_w` from `θ` into the subgroup-supported
subrepresentation `W₀`. -/
def supportedOnSubgroupHom :
    θ.IntertwiningMap (W₀).toRepresentation :=
  let f : W →ₗ[k] (W₀).toSubmodule :=
    (subgroupSupportedFunctionLinearMap H θ).codRestrict
      (W₀).toSubmodule
      (subgroupSupportedFunction_mem_supportedOnSubgroupSubrepresentation H θ)
  f.intertwiningMap_of_isIntertwiningMap θ (W₀).toRepresentation fun t w ↦
    Subtype.ext <| subgroupSupportedFunction_isIntertwining H θ t w

/-- The canonical intertwining map `w ↦ f_w` into `W₀` is the subgroup-supported function `f_w`.
-/
theorem supportedOnSubgroupHom_apply (w : W) :
    (supportedOnSubgroupHom H θ w : θ.coindV H.subtype) =
      subgroupSupportedFunction H θ w := by
  simp [supportedOnSubgroupHom, subgroupSupportedFunctionLinearMap]

/-- The map `w ↦ f_w` is a bijection from `W` onto `W₀`. -/
-- Proof sketch: injectivity is read off by evaluating at `1 ∈ H`; surjectivity reconstructs an
-- arbitrary function in `W₀` from its value at `1`, using covariance on `H` and vanishing away
-- from `H`.
private theorem supportedOnSubgroupHom_bijective :
    Function.Bijective (supportedOnSubgroupHom H θ) := by
  constructor
  · intro w₁ w₂ h
    -- Evaluate at `1` to recover the original vector in `W`.
    have hEval :
        subgroupSupportedFunction H θ w₁ 1 = subgroupSupportedFunction H θ w₂ 1 := by
      simpa [supportedOnSubgroupHom_apply] using
        congrArg (fun f : W₀ ↦ ((f : θ.coindV H.subtype) 1)) h
    have hEval' : θ ⟨1, H.one_mem⟩ w₁ = θ ⟨1, H.one_mem⟩ w₂ := by
      simpa [subgroupSupportedFunction, subgroupSupportedFunctionFun, H.one_mem] using hEval
    calc
      w₁ = θ ⟨1, H.one_mem⟩ w₁ := by
        symm
        exact LinearMap.congr_fun (θ.map_one) w₁
      _ = θ ⟨1, H.one_mem⟩ w₂ := hEval'
      _ = w₂ := by
        exact LinearMap.congr_fun (θ.map_one) w₂
  · intro f
    -- Reconstruct `f` from its value at `1`, using covariance on `H` and vanishing off `H`.
    refine ⟨(f : θ.coindV H.subtype) 1, ?_⟩
    apply Subtype.ext
    ext u
    by_cases hu : u ∈ H
    · have hcoind :
          (f : θ.coindV H.subtype) u =
            θ ⟨u, hu⟩ ((f : θ.coindV H.subtype) 1) := by
        simpa using (f : θ.coindV H.subtype).2 ⟨u, hu⟩ (1 : G)
      simpa [supportedOnSubgroupHom_apply, subgroupSupportedFunction_of_mem, hu] using
        hcoind.symm
    · have hf_zero :
          (f : θ.coindV H.subtype) u = 0 :=
        (mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem H θ
          (f : θ.coindV H.subtype)).mp f.2 u hu
      simpa [supportedOnSubgroupHom_apply, subgroupSupportedFunction_of_not_mem, hu] using
        hf_zero.symm

/-- Helper for Exercise 3-3.3-6: the quotient coordinate `QuotientGroup.mk u⁻¹` records exactly
when the right translate of `u` by `q.out` lands in `H`. -/
private theorem quotient_inv_eq_iff_mul_mem (q : G ⧸ H) (u : G) :
    ((QuotientGroup.mk u⁻¹ : G ⧸ H) = q) ↔ u * q.out ∈ H := by
  -- Rewrite equality in the quotient against the chosen representative `q.out`.
  rw [← Quotient.out_eq q, QuotientGroup.eq]
  simp

local instance quotientDecidableEq : DecidableEq (G ⧸ H) := Classical.decEq _

-- Route correction: use the inverse-quotient coordinate directly, since it is stable under the
-- left `H`-action appearing in `Representation.mem_coindV`.
/-- Helper for Exercise 3-3.3-6: the raw `q`-coset cutoff of a coinduced function still satisfies
the coinduced covariance relation. -/
private theorem cosetComponentFun_mem_coindV
    (q : G ⧸ H) (f : θ.coindV H.subtype) :
    (fun u : G ↦ if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q then f u else 0) ∈
      θ.coindV H.subtype := by
  -- The quotient coordinate `QuotientGroup.mk u⁻¹` is unchanged by left multiplication by `H`.
  rw [Representation.mem_coindV]
  intro t u
  have hleft :
      (QuotientGroup.mk (((t : G) * u)⁻¹) : G ⧸ H) = QuotientGroup.mk u⁻¹ := by
    rw [QuotientGroup.eq]
    simp
  by_cases huq : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q
  · have hmulq : (QuotientGroup.mk (((t : G) * u)⁻¹) : G ⧸ H) = q := hleft.trans huq
    simpa only [huq, hmulq, Subgroup.subtype_apply] using f.2 t u
  · have hmulq :
        (QuotientGroup.mk (((t : G) * u)⁻¹) : G ⧸ H) ≠ q := by
      intro hmulq
      exact huq (hleft.symm.trans hmulq)
    simpa only [huq, hmulq, Subgroup.subtype_apply] using (map_zero (θ t)).symm

/-- Helper for Exercise 3-3.3-6: the `q`-indexed coset component of a coinduced function, obtained
by keeping only the values whose inverse lies in the quotient class `q`. -/
private def cosetComponent (q : G ⧸ H) (f : θ.coindV H.subtype) : θ.coindV H.subtype :=
  ⟨fun u ↦ if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q then f u else 0,
    cosetComponentFun_mem_coindV H θ q f⟩

/-- Helper for Exercise 3-3.3-6: each quotient-indexed component already lies in the corresponding
translate of the subgroup-supported subrepresentation. -/
private theorem cosetComponent_mem_leftQuotientSubmodule
    (q : G ⧸ H) (f : θ.coindV H.subtype) :
    cosetComponent H θ q f ∈ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q := by
  -- Translate the `q`-component back to the trivial coset, where it becomes subgroup-supported.
  rw [← Quotient.out_eq q, Representation.leftQuotientSubmodule_mk, Submodule.mem_map]
  let g : θ.coindV H.subtype := ((θ.coind H.subtype) q.out⁻¹) (cosetComponent H θ q f)
  have hg : g ∈ W₀ := by
    -- After translating by `q.out⁻¹`, a value can survive only on `H`.
    rw [mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem]
    intro u hu
    have huq :
        (QuotientGroup.mk ((u * q.out⁻¹)⁻¹) : G ⧸ H) ≠ q := by
      intro huq
      have : (u * q.out⁻¹) * q.out ∈ H :=
        (quotient_inv_eq_iff_mul_mem H q (u * q.out⁻¹)).mp huq
      exact hu (by simpa [mul_assoc] using this)
    dsimp [g]
    have hcut : (QuotientGroup.mk (q.out * u⁻¹) : G ⧸ H) ≠ q := by
      simpa using huq
    simp [coind_apply, cosetComponent, hcut]
  refine ⟨g, hg, ?_⟩
  -- Translating forward by `q.out` recovers the original `q`-component.
  subst g
  simpa using
    (LinearMap.congr_fun ((θ.coind H.subtype).map_mul q.out q.out⁻¹)
      (cosetComponent H θ q f)).symm

/-- Helper for Exercise 3-3.3-6: an element of the `q`-translate of `W₀` vanishes away from the
coset indexed by `q`. -/
private theorem leftQuotientSubmodule_apply_eq_zero_of_ne
    {q : G ⧸ H} {f : θ.coindV H.subtype}
    (hf : f ∈ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q)
    {u : G} (hu : (QuotientGroup.mk u⁻¹ : G ⧸ H) ≠ q) : f u = 0 := by
  -- Unpack membership in the `q`-summand as a translate of a subgroup-supported function.
  rw [← Quotient.out_eq q, Representation.leftQuotientSubmodule_mk, Submodule.mem_map] at hf
  rcases hf with ⟨g, hg, rfl⟩
  have hug : u * q.out ∉ H := by
    intro hug
    exact hu ((quotient_inv_eq_iff_mul_mem H q u).2 hug)
  have hg_zero :
      g (u * q.out) = 0 :=
    (mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem H θ g).mp hg
      (u * q.out) hug
  simpa [coind_apply] using hg_zero

/-- Helper for Exercise 3-3.3-6: if a function is already supported on the `q`-coset, then its
`q`-component is the whole function. -/
private theorem cosetComponent_eq_of_mem
    {q : G ⧸ H} {f : θ.coindV H.subtype}
    (hf : f ∈ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q) :
    cosetComponent H θ q f = f := by
  -- Evaluate pointwise: on the `q`-coset nothing changes, and away from it the function already
  -- vanishes.
  ext u
  by_cases huq : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q
  · show (if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q then f u else 0) = f u
    simp [huq]
  · have hf_zero : f u = 0 := leftQuotientSubmodule_apply_eq_zero_of_ne H θ hf huq
    show (if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q then f u else 0) = f u
    simp [huq, hf_zero]

/-- Helper for Exercise 3-3.3-6: if a function is supported on the `q`-coset, then every other
quotient component vanishes. -/
private theorem cosetComponent_eq_zero_of_mem_ne
    {q q' : G ⧸ H} (hqq' : q' ≠ q) {f : θ.coindV H.subtype}
    (hf : f ∈ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q) :
    cosetComponent H θ q' f = 0 := by
  -- The `q'`-cutoff sees only points where the `q`-summand must already vanish.
  ext u
  by_cases huq' : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q'
  · have huq : (QuotientGroup.mk u⁻¹ : G ⧸ H) ≠ q := by
      intro huq
      exact hqq' (huq'.symm.trans huq)
    have hf_zero : f u = 0 := leftQuotientSubmodule_apply_eq_zero_of_ne H θ hf huq
    show (if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q' then f u else 0) = 0
    simp [huq', hf_zero]
  · show (if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q' then f u else 0) = 0
    simp [huq']

/-- The canonical equivalence of `H`-representations identifying `θ` with the subgroup-supported
subrepresentation `W₀` via `w ↦ f_w`. -/
def supportedOnSubgroupEquiv :
    θ.Equiv (W₀).toRepresentation :=
  let f : θ.IntertwiningMap (W₀).toRepresentation :=
    supportedOnSubgroupHom H θ
  Representation.Equiv.mk
    (LinearEquiv.ofBijective f.toLinearMap (supportedOnSubgroupHom_bijective H θ))
    f.isIntertwining'

/-- The equivalence `θ ≃ W₀` sends `w` to the supported function `f_w`. -/
-- Proof sketch: unfold `supportedOnSubgroupEquiv`; it is the codomain-restricted map
-- `w ↦ f_w` viewed as an `H`-equivariant equivalence.
theorem supportedOnSubgroupEquiv_apply (w : W) :
    (supportedOnSubgroupEquiv H θ w : θ.coindV H.subtype) =
      subgroupSupportedFunction H θ w := by
  simpa [supportedOnSubgroupEquiv] using
    (supportedOnSubgroupHom_apply H θ w)

/-- Helper for Exercise 3-3.3-6: with finitely many cosets, a coinduced function is the sum of
its quotient-indexed cutoff pieces. -/
private theorem sum_cosetComponent_eq [Fintype (G ⧸ H)]
    (f : θ.coindV H.subtype) :
    (∑ q : G ⧸ H, cosetComponent H θ q f) = f := by
  -- At each point `u`, only the cutoff indexed by `QuotientGroup.mk u⁻¹` survives.
  ext u
  simp [cosetComponent]

/-- Helper for Exercise 3-3.3-6: the quotient-indexed translates of `W₀` span the coinduced
representation once the quotient `G ⧸ H` is finite. -/
private theorem leftQuotientSubmodule_iSup_eq_top_supportedOnSubgroup
    [Finite (G ⧸ H)] :
    iSup (fun q : G ⧸ H =>
      (θ.coind H.subtype).leftQuotientSubmodule H W₀ q) = ⊤ := by
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  -- Reconstruct an arbitrary coinduced function as the sum of its coset components.
  apply top_unique
  intro f _
  rw [← sum_cosetComponent_eq H θ f]
  exact Submodule.sum_mem _ fun q _ ↦
    Submodule.mem_iSup_of_mem q (cosetComponent_mem_leftQuotientSubmodule H θ q f)

/-- Helper for Exercise 3-3.3-6: any element of the supremum of the wrong quotient summands
vanishes on the chosen quotient block. -/
private theorem leftQuotientSubmodule_apply_eq_zero_of_mem_iSup_ne
    (q : G ⧸ H) {f : θ.coindV H.subtype}
    (hf : f ∈ ⨆ q' : G ⧸ H,
      ⨆ (_ : q' ≠ q), (θ.coind H.subtype).leftQuotientSubmodule H W₀ q')
    {u : G} (hu : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q) :
    f u = 0 := by
  -- Induct through the outer and inner suprema using the pointwise vanishing predicate.
  refine Submodule.iSup_induction
      (p := fun q' : G ⧸ H ↦
        ⨆ (_ : q' ≠ q), (θ.coind H.subtype).leftQuotientSubmodule H W₀ q')
      (motive := fun g : θ.coindV H.subtype ↦ g u = 0) hf ?_ ?_ ?_
  · intro q' g hg
    refine Submodule.iSup_induction
        (p := fun _ : q' ≠ q ↦ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q')
        (motive := fun g : θ.coindV H.subtype ↦ g u = 0) hg ?_ ?_ ?_
    · intro hq' g hg'
      -- Each wrong summand already vanishes on the `q`-coset by the single-summand lemma.
      have huq' : (QuotientGroup.mk u⁻¹ : G ⧸ H) ≠ q' := by
        intro huq'
        exact hq' (huq'.symm.trans hu)
      exact leftQuotientSubmodule_apply_eq_zero_of_ne H θ hg' huq'
    · simp
    · intro g₁ g₂ hg₁ hg₂
      simp [hg₁, hg₂]
  · simp
  · intro g₁ g₂ hg₁ hg₂
    simp [hg₁, hg₂]

/-- Helper for Exercise 3-3.3-6: the `q`-component of an element supported on all other summands
is zero. -/
private theorem cosetComponent_eq_zero_of_mem_iSup_ne
    (q : G ⧸ H) {f : θ.coindV H.subtype}
    (hf : f ∈ ⨆ q' : G ⧸ H,
      ⨆ (_ : q' ≠ q), (θ.coind H.subtype).leftQuotientSubmodule H W₀ q') :
    cosetComponent H θ q f = 0 := by
  -- Evaluate pointwise: on the chosen coset use the vanishing lemma above, elsewhere the cutoff
  -- defining `cosetComponent` is already zero.
  ext u
  by_cases hu : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q
  · have hfu : f u = 0 :=
      leftQuotientSubmodule_apply_eq_zero_of_mem_iSup_ne H θ q hf hu
    simp [cosetComponent, hu, hfu]
  · simp [cosetComponent, hu]

/-- Helper for Exercise 3-3.3-6: the quotient-indexed translates of `W₀` are independent. -/
private theorem leftQuotientSubmodule_iSupIndep_supportedOnSubgroup :
    iSupIndep (fun q : G ⧸ H =>
      (θ.coind H.subtype).leftQuotientSubmodule H W₀ q) := by
  -- The cutoff `cosetComponent q` acts as the identity on the `q`-summand and kills the
  -- supremum of all other summands, so the intersection is trivial.
  rw [iSupIndep_def]
  intro q
  rw [Submodule.disjoint_def]
  intro x hxq hxrest
  have hself : cosetComponent H θ q x = x :=
    cosetComponent_eq_of_mem H θ hxq
  have hzero : cosetComponent H θ q x = 0 :=
    cosetComponent_eq_zero_of_mem_iSup_ne H θ q hxrest
  simpa [hself] using hzero

/-- Helper for Exercise 3-3.3-6: the quotient-indexed family of left translates of the
subgroup-supported subrepresentation. -/
private abbrev leftQuotientSubmoduleFamily :
    G ⧸ H → Submodule k (θ.coindV H.subtype) :=
  fun q => (θ.coind H.subtype).leftQuotientSubmodule H W₀ q

/-- Helper for Exercise 3-3.3-6: the direct-sum decomposition sends a coinduced function to its
family of quotient-indexed coset components. -/
private def leftQuotientSubmoduleDecompositionFun [Fintype (G ⧸ H)]
    (f : θ.coindV H.subtype) :
    DirectSum (G ⧸ H) fun q ↦ ↥(leftQuotientSubmoduleFamily H θ q) :=
  DirectSum.mk
    (fun q : G ⧸ H ↦ ↥(leftQuotientSubmoduleFamily H θ q))
    Finset.univ
    (fun q ↦ ⟨cosetComponent H θ q.1 f,
      cosetComponent_mem_leftQuotientSubmodule H θ q.1 f⟩)

/-- Helper for Exercise 3-3.3-6: each coordinate of the decomposition map is the corresponding
coset component. -/
private theorem leftQuotientSubmoduleDecompositionFun_apply [Fintype (G ⧸ H)]
    (f : θ.coindV H.subtype) (q : G ⧸ H) :
    leftQuotientSubmoduleDecompositionFun H θ f q =
      ⟨cosetComponent H θ q f,
        cosetComponent_mem_leftQuotientSubmodule H θ q f⟩ := by
  -- The direct-sum element is built from all coordinates on `Finset.univ`, so evaluation at `q`
  -- returns exactly the `q`-component.
  exact DirectSum.mk_apply_of_mem (β := fun q : G ⧸ H ↦ ↥(leftQuotientSubmoduleFamily H θ q))
    (s := Finset.univ)
    (f := fun q ↦ ⟨cosetComponent H θ q.1 f,
      cosetComponent_mem_leftQuotientSubmodule H θ q.1 f⟩)
    (hn := Finset.mem_univ q)

/-- Helper for Exercise 3-3.3-6: the decomposition map preserves zero. -/
private theorem leftQuotientSubmoduleDecompositionFun_zero [Fintype (G ⧸ H)] :
    leftQuotientSubmoduleDecompositionFun H θ (0 : θ.coindV H.subtype) = 0 := by
  -- Each quotient coordinate is the zero coset component.
  ext q u
  simp [leftQuotientSubmoduleDecompositionFun_apply, cosetComponent]

/-- Helper for Exercise 3-3.3-6: the decomposition map preserves addition. -/
private theorem leftQuotientSubmoduleDecompositionFun_add [Fintype (G ⧸ H)]
    (f g : θ.coindV H.subtype) :
    leftQuotientSubmoduleDecompositionFun H θ (f + g) =
      leftQuotientSubmoduleDecompositionFun H θ f +
        leftQuotientSubmoduleDecompositionFun H θ g := by
  -- Each quotient coordinate is cut out pointwise, so addition is coordinatewise.
  ext q u
  by_cases huq : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q
  · simp [leftQuotientSubmoduleDecompositionFun_apply, cosetComponent, huq]
  · simp [leftQuotientSubmoduleDecompositionFun_apply, cosetComponent, huq]

/-- Helper for Exercise 3-3.3-6: the additive decomposition map into the quotient-indexed direct
sum of left translates of `W₀`. -/
private def leftQuotientSubmoduleDecomposition [Fintype (G ⧸ H)] :
    θ.coindV H.subtype →+
      DirectSum (G ⧸ H) fun q ↦ ↥(leftQuotientSubmoduleFamily H θ q) where
  toFun := leftQuotientSubmoduleDecompositionFun H θ
  map_zero' := leftQuotientSubmoduleDecompositionFun_zero H θ
  map_add' := leftQuotientSubmoduleDecompositionFun_add H θ

/-- Helper for Exercise 3-3.3-6: recomposing the quotient-indexed coset components recovers the
original coinduced function. -/
private theorem coeAddMonoidHom_comp_leftQuotientSubmoduleDecomposition
    [Fintype (G ⧸ H)] :
    (DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ)).comp
      (leftQuotientSubmoduleDecomposition H θ) =
      AddMonoidHom.id (θ.coindV H.subtype) := by
  classical
  -- Recomposition is the finite sum of the quotient-indexed cutoff pieces.
  apply DFunLike.ext
  intro f
  ext u
  change ((DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ))
      (leftQuotientSubmoduleDecomposition H θ f)) u = f u
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  simpa [leftQuotientSubmoduleDecomposition, leftQuotientSubmoduleDecompositionFun,
    DirectSum.mk, cosetComponent] using
    congrArg (fun g : θ.coindV H.subtype => g u) (sum_cosetComponent_eq H θ f)

/-- Helper for Exercise 3-3.3-6: decomposing a pure direct-sum summand and then recomposing keeps
that summand unchanged, hence the decomposition map is also a left inverse. -/
private theorem leftQuotientSubmoduleDecomposition_comp_coeAddMonoidHom
    [Fintype (G ⧸ H)] :
    (leftQuotientSubmoduleDecomposition H θ).comp
      (DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ)) =
      AddMonoidHom.id
        (DirectSum (G ⧸ H) fun q ↦ ↥(leftQuotientSubmoduleFamily H θ q)) := by
  -- It suffices to check the identity on `0`, on pure generators, and then extend by additivity.
  apply DFunLike.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero =>
      simpa [AddMonoidHom.comp_apply, leftQuotientSubmoduleDecomposition]
        using leftQuotientSubmoduleDecompositionFun_zero H θ
  | of q x =>
      ext r u
      by_cases hr : r = q
      · subst hr
        have hself :
            cosetComponent H θ r (x : θ.coindV H.subtype) = (x : θ.coindV H.subtype) :=
          cosetComponent_eq_of_mem H θ x.property
        simp [AddMonoidHom.comp_apply, leftQuotientSubmoduleDecomposition,
          DirectSum.coeAddMonoidHom_of, leftQuotientSubmoduleDecompositionFun_apply, hself]
      · have hzero :
            cosetComponent H θ r (x : θ.coindV H.subtype) = 0 :=
          cosetComponent_eq_zero_of_mem_ne H θ hr x.property
        simp [AddMonoidHom.comp_apply, leftQuotientSubmoduleDecomposition,
          DirectSum.coeAddMonoidHom_of, DirectSum.of_eq_of_ne,
          leftQuotientSubmoduleDecompositionFun_apply, hr, hzero]
  | add x y hx hy =>
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, map_add, map_add]
      simpa using congrArg₂ HAdd.hAdd hx hy

/-- Exercise 3-3.3-6: the comparison between the given `H`-representation `θ` and the
subgroup-supported subrepresentation `W₀` is the canonical `H`-equivariant equivalence
`supportedOnSubgroupEquiv H θ : θ.Equiv W₀.toRepresentation`, whose underlying linear
equivalence is `(supportedOnSubgroupEquiv H θ).toLinearEquiv`. If `H` has finite index, then the
canonical coinduced-function representation `θ.coind H.subtype` is induced from the
subgroup-supported subrepresentation `W₀`. -/
-- Proof sketch: use the canonical finite-index comparison `Rep.indCoindIso` between
-- `Ind_H^G(W)` and `Coind_H^G(W)`, together with the trivial-coset generator
-- `IndV.mk H.subtype θ 1 : W →ₗ[k] Ind_H^G(W)`, then identify its image in the coinduced model
-- with `W₀`; the left-coset translates of `W₀` give the internal direct-sum decomposition of
-- `θ.coind H.subtype`.
theorem isInducedFrom_supportedOnSubgroupSubrepresentation [H.FiniteIndex] :
    (θ.coind H.subtype).IsInducedFromSubrepresentation H
      W₀ := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hleft :
      (DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ)).comp
        (leftQuotientSubmoduleDecomposition H θ) =
        AddMonoidHom.id (θ.coindV H.subtype) := by
    exact coeAddMonoidHom_comp_leftQuotientSubmoduleDecomposition H θ
  have hright :
      (leftQuotientSubmoduleDecomposition H θ).comp
        (DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ)) =
        AddMonoidHom.id (DirectSum (G ⧸ H) fun q ↦ ↥(leftQuotientSubmoduleFamily H θ q)) := by
    exact leftQuotientSubmoduleDecomposition_comp_coeAddMonoidHom H θ
  let decomp : DirectSum.Decomposition (leftQuotientSubmoduleFamily H θ) :=
    DirectSum.Decomposition.ofAddHom (ℳ := leftQuotientSubmoduleFamily H θ)
      (leftQuotientSubmoduleDecomposition H θ)
      hleft
      hright
  letI : DirectSum.Decomposition (leftQuotientSubmoduleFamily H θ) := decomp
  -- Route correction: in the semiring setting, prove internality by exhibiting the explicit
  -- quotient-indexed decomposition map and its two-sided inverse property.
  change DirectSum.IsInternal (leftQuotientSubmoduleFamily H θ)
  exact DirectSum.Decomposition.isInternal (ℳ := leftQuotientSubmoduleFamily H θ)

end InducedFromCoinducedModel

end

end Representation

/-! ### Exercise_3_3_3_7 (from Chap03) -/
open scoped TensorProduct
open scoped Representation.ExternalTensor
open MonoidHom

universe u v w w'

namespace Subgroup

section

variable {G : Type v} [Group G]

/- The direct-product bridge attached to complementary commuting subgroups. This is a
`bridge/view` declaration: the primitive data are the complement proof and the commuting
hypothesis, and the resulting `MulEquiv` is the canonical owner for the multiplication
identification `H × K ≃* G`. -/
/-- If complementary subgroups `H` and `K` commute elementwise, multiplication identifies the
direct product `H × K` with `G`. -/
noncomputable def IsComplement'.prodMulEquiv
    {H K : Subgroup G} (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    H × K ≃* G :=
  MulEquiv.ofBijective
    (H.subtype.noncommCoprod K.subtype hcomm)
    (by simpa [noncommCoprod_apply] using hHK)

end

end Subgroup

namespace Representation

section

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable (H K : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type w'} [AddCommGroup W] [Module k W]

/-- Helper for Exercise 3-3.3-7: under the direct-product identification `H × K ≃* G`, left
multiplication by an element of `H` only changes the `H`-coordinate. -/
private lemma prodMulEquiv_symm_subtype
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (h : H) :
    (hHK.prodMulEquiv hcomm).symm (h : G) = (h, 1) := by
  let eHK := hHK.prodMulEquiv hcomm
  -- Compare both sides after transporting them back to `G` through the direct-product
  -- identification.
  apply eHK.injective
  rw [eHK.apply_symm_apply]
  change ↑h = (H.subtype.noncommCoprod K.subtype hcomm) (h, 1)
  simp [noncommCoprod_apply]

/-- Helper for Exercise 3-3.3-7: under the direct-product identification `H × K ≃* G`, left
multiplication by an element of `H` only changes the `H`-coordinate. -/
private lemma prodMulEquiv_symm_subtype_mul
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (h : H) (g : G) :
    (hHK.prodMulEquiv hcomm).symm ((h : G) * g) =
      (h * ((hHK.prodMulEquiv hcomm).symm g).1, ((hHK.prodMulEquiv hcomm).symm g).2) := by
  let eHK := hHK.prodMulEquiv hcomm
  -- The direct-product coordinates turn left multiplication by `h` into multiplication on the
  -- `H`-coordinate only.
  rw [eHK.symm.map_mul, prodMulEquiv_symm_subtype H K hHK hcomm h]
  rcases eHK.symm g with ⟨hg, kg⟩
  simp

/-- Helper for Exercise 3-3.3-7: right translation by `u⁻¹` in `G` becomes componentwise
multiplication by the inverse coordinates of `u` in `H × K`. -/
private lemma prodMulEquiv_symm_mul_inv
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g u : G) :
    (hHK.prodMulEquiv hcomm).symm (g * u⁻¹) =
      (((hHK.prodMulEquiv hcomm).symm g).1 * ((hHK.prodMulEquiv hcomm).symm u).1⁻¹,
        ((hHK.prodMulEquiv hcomm).symm g).2 * ((hHK.prodMulEquiv hcomm).symm u).2⁻¹) := by
  let eHK := hHK.prodMulEquiv hcomm
  -- The direct-product coordinates respect multiplication and inversion.
  change eHK.symm (g * u⁻¹) = eHK.symm g * (eHK.symm u)⁻¹
  simpa using eHK.symm.map_mul g u⁻¹

/-- Helper for Exercise 3-3.3-7: the raw map on `k[G] ⊗ W` that sends the basis vector `g` to the
`K`-basis vector indexed by the `K`-coordinate of `g`, while twisting `W` by the inverse
`H`-coordinate. -/
private noncomputable def induced_to_externalTensor_raw
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    (G →₀ k) ⊗[k] W →ₗ[k] W ⊗[k] (K →₀ k) :=
  let eHK := hHK.prodMulEquiv hcomm
  TensorProduct.lift <|
    Finsupp.lift (W →ₗ[k] W ⊗[k] (K →₀ k)) k G fun g ↦
      ((TensorProduct.mk k W (K →₀ k)).flip (Finsupp.single ((eHK.symm g).2)⁻¹ 1)) ∘ₗ
        θ ((eHK.symm g).1)⁻¹

/-- Helper for Exercise 3-3.3-7: the raw tensor formula is well defined on the induced
coinvariants. -/
private lemma induced_to_externalTensor_descends
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (h : H) :
    induced_to_externalTensor_raw H K θ hHK hcomm ∘ₗ
        Representation.tprod ((leftRegular k G).comp H.subtype) θ h =
      induced_to_externalTensor_raw H K θ hHK hcomm := by
  -- It suffices to compare both sides on the pure tensors `single g 1 ⊗ w`.
  refine TensorProduct.ext ?_
  refine Finsupp.lhom_ext' fun g ↦ ?_
  ext w
  simp [induced_to_externalTensor_raw, Representation.tprod_apply, Finsupp.lift_apply,
    prodMulEquiv_symm_subtype_mul]

/-- Helper for Exercise 3-3.3-7: the descended map from the induced model to the external tensor
model. -/
private noncomputable def induced_to_externalTensor
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    IndV H.subtype θ →ₗ[k] W ⊗[k] (K →₀ k) :=
  Coinvariants.lift _ (induced_to_externalTensor_raw H K θ hHK hcomm)
    (induced_to_externalTensor_descends H K θ hHK hcomm)

/-- Helper for Exercise 3-3.3-7: on the standard generator `IndV.mk g w`, the descended map reads
off the direct-product coordinates of `g`. -/
private lemma induced_to_externalTensor_apply_mk
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g : G) (w : W) :
    induced_to_externalTensor H K θ hHK hcomm (Representation.IndV.mk H.subtype θ g w) =
      θ (((hHK.prodMulEquiv hcomm).symm g).1)⁻¹ w ⊗ₜ[k]
        Finsupp.single (((hHK.prodMulEquiv hcomm).symm g).2)⁻¹ 1 := by
  -- Unfolding the quotient lift reduces immediately to the defining tensor formula.
  simp [induced_to_externalTensor, induced_to_externalTensor_raw, Finsupp.lift_apply]

/-- Helper for Exercise 3-3.3-7: the inverse candidate from `W ⊗ k[K]` back to the induced
representation sends `w ⊗ δ_k` to the induced generator supported at the element `(1, k⁻¹)`. -/
private noncomputable def externalTensor_to_induced_linear
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    W ⊗[k] (K →₀ k) →ₗ[k] IndV H.subtype θ :=
  TensorProduct.lift <|
    LinearMap.flip <|
      Finsupp.lift (W →ₗ[k] IndV H.subtype θ) k K fun k' ↦
        Representation.IndV.mk H.subtype θ ((hHK.prodMulEquiv hcomm) (1, k'⁻¹))

/-- Helper for Exercise 3-3.3-7: the inverse candidate is explicit on pure tensors with a single
`K`-basis vector. -/
private lemma externalTensor_to_induced_linear_apply_single
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (w : W) (k' : K) (r : k) :
    externalTensor_to_induced_linear H K θ hHK hcomm (w ⊗ₜ[k] Finsupp.single k' r) =
      r • Representation.IndV.mk H.subtype θ ((hHK.prodMulEquiv hcomm) (1, k'⁻¹)) w := by
  -- The `Finsupp.lift` linear-combination formula collapses on a single basis vector.
  simp [externalTensor_to_induced_linear, Finsupp.lift_apply]

/-- Helper for Exercise 3-3.3-7: the coordinate formula for `induced_to_externalTensor` respects
the `G`-action on the standard induced generators. -/
private lemma induced_to_externalTensor_intertwines_mk
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g u : G) (w : W) :
    induced_to_externalTensor H K θ hHK hcomm
        ((ind H.subtype θ) g (Representation.IndV.mk H.subtype θ u w)) =
      (((θ ⊠ leftRegular k K).comp (hHK.prodMulEquiv hcomm).symm.toMonoidHom) g)
        (induced_to_externalTensor H K θ hHK hcomm (Representation.IndV.mk H.subtype θ u w)) := by
  let eHK := hHK.prodMulEquiv hcomm
  rcases hg : eHK.symm g with ⟨gH, gK⟩
  rcases hu : eHK.symm u with ⟨uH, uK⟩
  -- Expand the induced action on the standard generator and read off its direct-product
  -- coordinates.
  rw [Representation.ind_mk, induced_to_externalTensor_apply_mk]
  have hu_mul :
      eHK.symm (u * g⁻¹) = (uH * gH⁻¹, uK * gK⁻¹) := by
    simpa [hg, hu] using prodMulEquiv_symm_mul_inv H K hHK hcomm u g
  rw [hu_mul]
  -- Evaluate the target tensor-product action on the same generator.
  rw [induced_to_externalTensor_apply_mk]
  have hg' : (hHK.prodMulEquiv hcomm).symm g = (gH, gK) := by
    simpa [eHK] using hg
  have hu' : (hHK.prodMulEquiv hcomm).symm u = (uH, uK) := by
    simpa [eHK] using hu
  have hleftRegular :
      leftRegular k K gK (Finsupp.single uK⁻¹ (1 : k)) =
        Finsupp.single (gK * uK⁻¹) 1 := by
    simpa using
      (Representation.ofMulAction_single (k := k) (G := K) (H := K) gK uK⁻¹ (1 : k))
  -- The `H`-coordinate multiplies on the left, while the `K`-basis vector translates by
  -- left-regular multiplication.
  simpa [MonoidHom.coe_comp, Function.comp_apply, Representation.tprod_apply,
    TensorProduct.map_tmul, hg', hu', hleftRegular, Module.End.mul_apply, map_mul]

/-- Helper for Exercise 3-3.3-7: the explicit inverse sends the image of each induced generator
back to that same generator. -/
private lemma externalTensor_to_induced_left_inverse_mk
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g : G) (w : W) :
    externalTensor_to_induced_linear H K θ hHK hcomm
        (induced_to_externalTensor H K θ hHK hcomm (Representation.IndV.mk H.subtype θ g w)) =
      Representation.IndV.mk H.subtype θ g w := by
  let eHK := hHK.prodMulEquiv hcomm
  rcases hcoords : eHK.symm g with ⟨gH, gK⟩
  -- Expand the forward map on the generator `IndV.mk g w`.
  rw [induced_to_externalTensor_apply_mk]
  rw [show (hHK.prodMulEquiv hcomm).symm g = (gH, gK) by simpa [eHK, hcoords]]
  -- Apply the inverse candidate to the resulting basis tensor.
  rw [externalTensor_to_induced_linear_apply_single]
  simp only [one_smul, inv_inv]
  have hk_eval : eHK (1, gK) = (gK : G) := by
    simp [eHK, Subgroup.IsComplement'.prodMulEquiv, noncommCoprod_apply]
  have hg_eval : eHK (gH, gK) = (gH : G) * (gK : G) := by
    simp [eHK, Subgroup.IsComplement'.prodMulEquiv, noncommCoprod_apply]
  have hg_decomp : g = (gH : G) * (gK : G) := by
    calc
      g = eHK (gH, gK) := by simpa [eHK, hcoords] using (eHK.apply_symm_apply g).symm
      _ = (gH : G) * (gK : G) := hg_eval
  rw [hk_eval, hg_decomp]
  -- Move the `H`-factor from the `G`-coordinate of the induced generator into the coefficient
  -- vector using the coinvariant relation.
  have hmk :
      Representation.IndV.mk H.subtype θ ((gH : G) * (gK : G)) w =
        Representation.IndV.mk H.subtype θ (gK : G) (θ gH⁻¹ w) := by
    simpa [Representation.IndV.mk, Representation.ofMulAction_single] using
      (Representation.Coinvariants.mk_inv_tmul
        (ρ := (leftRegular k G).comp H.subtype)
        (τ := θ)
        (x := Finsupp.single (gK : G) (1 : k))
        (y := w)
        (g := gH⁻¹))
  exact hmk.symm

/-- Helper for Exercise 3-3.3-7: the coordinate map recovers a pure tensor supported on a single
`K`-basis vector after applying the explicit inverse candidate. -/
private lemma induced_to_externalTensor_right_inverse_single
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (w : W) (k' : K) (r : k) :
    induced_to_externalTensor H K θ hHK hcomm
        (externalTensor_to_induced_linear H K θ hHK hcomm
          (w ⊗ₜ[k] Finsupp.single k' r)) =
      w ⊗ₜ[k] Finsupp.single k' r := by
  let eHK := hHK.prodMulEquiv hcomm
  -- Expand the inverse candidate on the chosen `K`-basis tensor.
  rw [externalTensor_to_induced_linear_apply_single, map_smul]
  -- The forward map then reads off the trivial `H`-coordinate and the chosen `K`-coordinate.
  rw [induced_to_externalTensor_apply_mk]
  have hcoords : eHK.symm (eHK (1, k'⁻¹)) = (1, k'⁻¹) := by
    simp [eHK]
  rw [hcoords]
  -- After simplifying the coordinates, only the original pure tensor remains.
  simpa [inv_one, ← TensorProduct.tmul_smul]

/-- Helper for Exercise 3-3.3-7: the explicit coordinate map intertwines the induced `G`-action
with the pulled-back tensor-product action. -/
private lemma induced_to_externalTensor_isIntertwining
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g : G) :
    induced_to_externalTensor H K θ hHK hcomm ∘ₗ (ind H.subtype θ) g =
      (((θ ⊠ leftRegular k K).comp (hHK.prodMulEquiv hcomm).symm.toMonoidHom) g) ∘ₗ
        induced_to_externalTensor H K θ hHK hcomm := by
  -- Check equivariance on the canonical induced generators `IndV.mk g w`.
  apply Representation.IndV.hom_ext (φ := H.subtype) (ρ := θ)
  intro u
  ext w
  simpa [LinearMap.comp_apply] using
    induced_to_externalTensor_intertwines_mk H K θ hHK hcomm g u w

/-- Helper for Exercise 3-3.3-7: the inverse candidate is a left inverse to the coordinate map on
the whole induced module. -/
private lemma externalTensor_to_induced_left_inverse
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    externalTensor_to_induced_linear H K θ hHK hcomm ∘ₗ
        induced_to_externalTensor H K θ hHK hcomm =
      (LinearMap.id : IndV H.subtype θ →ₗ[k] IndV H.subtype θ) := by
  -- The induced model is generated by the images of `IndV.mk`, so the generator identity
  -- upgrades to a map identity by `IndV.hom_ext`.
  apply Representation.IndV.hom_ext (φ := H.subtype) (ρ := θ)
  intro g
  ext w
  simpa [LinearMap.comp_apply] using
    externalTensor_to_induced_left_inverse_mk H K θ hHK hcomm g w

/-- Helper for Exercise 3-3.3-7: the coordinate map is a right inverse to the explicit inverse on
the tensor-product model. -/
private lemma induced_to_externalTensor_right_inverse
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    induced_to_externalTensor H K θ hHK hcomm ∘ₗ
        externalTensor_to_induced_linear H K θ hHK hcomm =
      (LinearMap.id : W ⊗[k] (K →₀ k) →ₗ[k] W ⊗[k] (K →₀ k)) := by
  -- Check the identity on pure tensors `w ⊗ single k' 1`; tensor and `Finsupp` extensionality
  -- then promote it to all tensors.
  refine TensorProduct.ext ?_
  ext w k'
  simpa [LinearMap.comp_apply] using
    induced_to_externalTensor_right_inverse_single H K θ hHK hcomm w k' (1 : k)

/-- Helper for Exercise 3-3.3-7: the standard induced model is equivariantly isomorphic to the
external tensor product `θ ⊠ r_K` transported along the direct-product identification `H × K ≃ G`.
-/
private noncomputable abbrev ind_equiv_externalTensor_leftRegular_of_direct_product
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    (ind H.subtype θ).Equiv ((θ ⊠ leftRegular k K).comp (hHK.prodMulEquiv hcomm).symm.toMonoidHom) :=
  -- Route correction: the explicit coordinate map already gives the right model; the remaining
  -- task is to package its generator-level equivariance and inverse formulas into a linear
  -- equivalence of representations.
  Representation.Equiv.mk
    (LinearEquiv.ofLinear
      (induced_to_externalTensor H K θ hHK hcomm)
      (externalTensor_to_induced_linear H K θ hHK hcomm)
      (induced_to_externalTensor_right_inverse H K θ hHK hcomm)
      (externalTensor_to_induced_left_inverse H K θ hHK hcomm))
    (induced_to_externalTensor_isIntertwining H K θ hHK hcomm)

/- Source/core/bridge triage:
* source-facing: the exercise identifies an induced `G`-representation with the pullback of
  `θ ⊗ r_K` along the product decomposition `H × K ≃ G`.
* core/canonical: `Representation.ind`, the external tensor-product owner
  `(θ.comp (fst H K)).tprod ((leftRegular k K).comp (snd H K))`, and
  `Representation.leftRegular`.
* bridge/view: `Subgroup.IsComplement'.prodMulEquiv` packages the subgroup product identification
  obtained from `H.IsComplement' K` and the commutation hypothesis.

Primitive data are the induced equivalence `hρ` and the direct-product hypotheses `hHK`, `hcomm`.
The product-group equivalence is a bridge derived from the direct-product hypotheses, while the
tensor-product model is the canonical source-facing notation `θ ⊠ leftRegular k K` for that owner,
rather than a separate local wrapper definition.
-/
/-- Exercise 3-3.3-7: if `G` is the direct product of its subgroups `H` and `K`, and `ρ` is a
representation of `G` induced by a representation `θ` of `H`, then `ρ` is isomorphic to the
pullback along the multiplication identification `H × K ≃ G` of the external tensor product
`θ ⊠ r_K`, where `r_K` is the regular representation of `K`. -/
-- Proof sketch: the direct-product hypothesis is encoded by the canonical complement owner
-- `H.IsComplement' K` together with pairwise commutation of elements of `H` and `K`. These data
-- recover the multiplication isomorphism `H × K ≃* G`, after which one compares the standard
-- induced model with the external tensor-product model `θ ⊠ r_K` on `W ⊗[k] (K →₀ k)` and
-- composes with
-- the given equivalence `ρ ≃ ind H.subtype θ`.
noncomputable def isomorphic_to_externalTensor_left_regular_of_induced_of_direct_product
    (ρ : Representation k G V) (θ : Representation k H W)
    (hρ : ρ.Equiv (ind H.subtype θ))
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    ρ.Equiv ((θ ⊠ leftRegular k K).comp (hHK.prodMulEquiv hcomm).symm.toMonoidHom) :=
  -- The target comparison is the given induced equivalence followed by the explicit direct-product
  -- model for the induced representation.
  hρ.trans (ind_equiv_externalTensor_leftRegular_of_direct_product H K θ hHK hcomm)

end

end Representation
