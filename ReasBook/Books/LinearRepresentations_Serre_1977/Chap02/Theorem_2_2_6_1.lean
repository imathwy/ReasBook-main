import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_1
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_5_1
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra

universe u v w w'

namespace Representation

noncomputable section

section

variable {k : Type*} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W]

/-- The canonical `σ`-isotypic summand of `ρ`, bundled as a `G`-stable subrepresentation.
It is a thin bridge/view of the owner `k[G]`-submodule `isotypicComponent k[G] V W`. -/
abbrev isotypicSubrepresentation (ρ : Representation k G V) (σ : Representation k G W) :
    Subrepresentation ρ :=
  letI : Module k[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : Module k[G] W := σ.instModuleMonoidAlgebraAsModule
  Subrepresentation.ofSubmodule' (isotypicComponent k[G] V W)

end

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W]

local instance theorem_2_2_6_1_fintype_of_finite : Fintype G := Fintype.ofFinite G
local instance theorem_2_2_6_1_neZero_complex_natCard : NeZero (Nat.card G : ℂ) := by
  exact ⟨by exact_mod_cast Nat.card_pos.ne'⟩
local instance instInvertibleNatCardComplexChap2261 : Invertible (Nat.card G : ℂ) := by
  refine invertibleOfNonzero ?_
  exact_mod_cast Nat.card_pos.ne'

variable (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [σ.IsIrreducible]

local instance instModuleMonoidAlgebraV : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
local instance instModuleMonoidAlgebraW : Module ℂ[G] W := σ.instModuleMonoidAlgebraAsModule

/-- The normalized endomorphism of `ρ` obtained by weighting the action maps with the conjugate
character of the irreducible representation `σ`. Theorem 2-2.6-1 later identifies this operator
as the identity on the `σ`-isotypic component and as zero on the isotypic components of the other
irreducibles. -/
def characterWeightedEndomorphism :
    Module.End ℂ V :=
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  ((Module.finrank ℂ W : ℂ) / Nat.card G) •
    ρ.asAlgebraHom (∑ t : G, star (σ.character t) • MonoidAlgebra.of ℂ G t)

/-- Helper for Theorem 2-2.6-1: the conjugate of the irreducible character is again a class
function. -/
private theorem star_character_mem_classFunctionSubmodule :
    (fun t : G ↦ star (σ.character t)) ∈ classFunctionSubmodule ℂ G := by
  rw [mem_classFunctionSubmodule_iff]
  refine ⟨?_⟩
  intro u v huv
  rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp huv) with ⟨a, rfl⟩
  simpa using congrArg star (σ.char_conj u a).symm

/-- Helper for Theorem 2-2.6-1: the weighted operator preserves every `G`-stable subspace because
it is a linear combination of the action maps `ρ t`. -/
private theorem characterWeightedEndomorphism_map_mem_subrepresentation
    (U : Subrepresentation ρ) {v : V} (hv : v ∈ U.toSubmodule) :
    characterWeightedEndomorphism ρ σ v ∈ U.toSubmodule := by
  -- View the weighted operator as scalar multiplication by one group-algebra element on the
  -- underlying `ℂ[G]`-submodule, so stability is immediate from the submodule structure.
  let a : ℂ[G] := ∑ t : G, star (σ.character t) • MonoidAlgebra.of ℂ G t
  have ha :
      ρ.asAlgebraHom a v ∈ U.toSubmodule := by
    -- Expand the group-algebra action and check each summand separately.
    have hsum :
        (∑ t : G, star (σ.character t) • ρ t v) ∈ U.toSubmodule := by
      exact U.toSubmodule.sum_mem fun t _ ↦
        U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule t hv)
    simpa [a, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply] using hsum
  -- The outer complex scalar also preserves the underlying `ℂ`-submodule.
  simpa [characterWeightedEndomorphism, a] using
    U.toSubmodule.smul_mem (((Module.finrank ℂ W : ℂ) / Nat.card G)) ha

/-- Helper for Theorem 2-2.6-1: the weighted operator preserves the canonical `σ`-isotypic
subrepresentation. -/
private theorem characterWeightedEndomorphism_map_mem_isotypicSubrepresentation
    {v : V} (hv : v ∈ (ρ.isotypicSubrepresentation σ).toSubmodule) :
    characterWeightedEndomorphism ρ σ v ∈ (ρ.isotypicSubrepresentation σ).toSubmodule := by
  -- This is the special case of `characterWeightedEndomorphism_map_mem_subrepresentation` needed
  -- for the final projector statement.
  exact characterWeightedEndomorphism_map_mem_subrepresentation (ρ := ρ) (σ := σ)
    (ρ.isotypicSubrepresentation σ) hv

/-- Helper for Theorem 2-2.6-1: the weighted operator preserves every irreducible isotypic
subrepresentation, since it preserves every `G`-stable subspace. -/
private theorem characterWeightedEndomorphism_map_mem_target_isotypicSubrepresentation
    {W' : Type w'} [AddCommGroup W'] [Module ℂ W']
    (τ : Representation ℂ G W') [τ.IsIrreducible] {v : V}
    (hv : v ∈ (ρ.isotypicSubrepresentation τ).toSubmodule) :
    characterWeightedEndomorphism ρ σ v ∈ (ρ.isotypicSubrepresentation τ).toSubmodule := by
  -- This is the same stability statement, now packaged for the auxiliary `τ`-isotypic summands
  -- that appear in the vanishing clause of the theorem.
  exact characterWeightedEndomorphism_map_mem_subrepresentation (ρ := ρ) (σ := σ)
    (ρ.isotypicSubrepresentation τ) hv

/-- Helper for Theorem 2-2.6-1: a `ℂ[G]`-linear equivalence of owner modules upgrades to an
equivalence of the corresponding representations. -/
private theorem nonempty_equiv_of_module_linearEquiv
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (τ : Representation ℂ G W') [τ.IsIrreducible]
    {M : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]
    (e : M ≃ₗ[ℂ[G]] τ.asModule) :
    Nonempty ((Representation.ofModule' (k := ℂ) (G := G) M).Equiv τ) := by
  -- Package the owner-module equivalence into an intertwining equivalence by rewriting each
  -- representation action as multiplication by `single g 1` in the group algebra.
  refine ⟨Representation.Equiv.mk (e.restrictScalars ℂ) ?_⟩
  intro g
  ext m
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  show e (((Representation.ofModule' (k := ℂ) (G := G) M) g) m) = (τ g) (e m)
  calc
    e (((Representation.ofModule' (k := ℂ) (G := G) M) g) m)
        = e ((MonoidAlgebra.single g (1 : ℂ)) • m) := by
            rfl
    _ = (MonoidAlgebra.single g (1 : ℂ)) • e m := by
          exact e.map_smulₛₗ (MonoidAlgebra.single g (1 : ℂ)) m
    _ = (τ g) (τ.asModuleEquiv (e m)) := by
          simpa using
            (Representation.single_smul (ρ := τ) (t := (1 : ℂ)) (g := g) (v := e m))
    _ = (τ g) (e m) := by
          rfl

/-- Helper for Theorem 2-2.6-1: membership in the owner `ℂ[G]`-submodule view of the canonical
`σ`-isotypic summand is the same as membership in the bundled `ℂ`-submodule view. -/
private theorem mem_isotypicSubrepresentation_asSubmodule_iff {v : V} :
    v ∈ (ρ.isotypicSubrepresentation σ).asSubmodule ↔
      v ∈ (ρ.isotypicSubrepresentation σ).toSubmodule := by
  -- This is the basic bridge between the owner `ℂ[G]`-submodule API and the bundled
  -- subrepresentation API used in the final projector statement.
  rfl

/-- Helper for Theorem 2-2.6-1: every simple owner submodule inside a `τ`-isotypic component
has associated representation equivalent to `τ`. -/
private theorem nonempty_equiv_of_simple_submodule_le_isotypicSubrepresentation
    {W' : Type w'} [AddCommGroup W'] [Module ℂ W']
    (τ : Representation ℂ G W') [τ.IsIrreducible]
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    (hS : S ≤ (ρ.isotypicSubrepresentation τ).asSubmodule) :
    Nonempty ((Representation.ofModule' (k := ℂ) (G := G) S).Equiv τ) := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : Module ℂ[G] W' := τ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] W' := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule τ).mp inferInstance
  let S' : Submodule ℂ[G] V := S
  have hS' : S' ≤ (ρ.isotypicSubrepresentation τ).asSubmodule := by
    simpa [S'] using hS
  -- The owner `τ`-isotypic component is exactly `isotypicComponent ℂ[G] V W'`, so its inclusion
  -- map transfers the canonical `τ`-isotypic structure to the simple summand `S`.
  have hTargetIsotypic : IsIsotypicOfType ℂ[G] ((ρ.isotypicSubrepresentation τ).asSubmodule) W' := by
    simpa [Representation.isotypicSubrepresentation] using
      (IsIsotypicOfType.isotypicComponent (R := ℂ[G]) (M := V) (S := W'))
  have hIsotypic : IsIsotypicOfType ℂ[G] S' W' := by
    exact hTargetIsotypic.of_injective (Submodule.inclusion hS') (Submodule.inclusion_injective hS')
  -- Evaluating the isotypic-of-type criterion on the simple summand `S` produces the desired
  -- owner-level module equivalence.
  letI : IsSimpleModule ℂ[G] S' := by
    simpa [S'] using (inferInstance : IsSimpleModule ℂ[G] S)
  letI : IsSimpleModule ℂ[G] (⊤ : Submodule ℂ[G] S') :=
    IsSimpleModule.congr (Submodule.topEquiv : (⊤ : Submodule ℂ[G] S') ≃ₗ[ℂ[G]] S')
  have hEquivTop : Nonempty ((⊤ : Submodule ℂ[G] S') ≃ₗ[ℂ[G]] W') := hIsotypic ⊤
  have hEquiv : Nonempty (S ≃ₗ[ℂ[G]] W') := by
    rcases hEquivTop with ⟨eTop⟩
    exact ⟨(Submodule.topEquiv : (⊤ : Submodule ℂ[G] S') ≃ₗ[ℂ[G]] S').symm.trans eTop⟩
  rcases hEquiv with ⟨e⟩
  -- Finally package the `ℂ[G]`-linear equivalence as an equivalence of representations.
  letI : IsScalarTower ℂ ℂ[G] S := S.isScalarTower
  letI : IsScalarTower ℂ ℂ[G] W' := by
    simpa using (inferInstance : IsScalarTower ℂ ℂ[G] τ.asModule)
  refine ⟨Representation.Equiv.mk (e.restrictScalars ℂ) ?_⟩
  intro g
  ext s
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  show e (((Representation.ofModule' (k := ℂ) (G := G) S) g) s) = (τ g) (e s)
  calc
    e (((Representation.ofModule' (k := ℂ) (G := G) S) g) s)
        = e ((MonoidAlgebra.single g (1 : ℂ)) • s) := by
            rfl
    _ = (MonoidAlgebra.single g (1 : ℂ)) • e s := by
          exact e.map_smulₛₗ (MonoidAlgebra.single g (1 : ℂ)) s
    _ = (τ g) (τ.asModuleEquiv (e s)) := by
          convert (Representation.single_smul (ρ := τ) (t := (1 : ℂ)) (g := g) (v := e s)) using 1
          simp
    _ = (τ g) (e s) := by
          rfl

/-- Helper for Theorem 2-2.6-1: for a module viewed through `Representation.ofModule'`, the
associated group-algebra operator acts by the original `ℂ[G]`-scalar multiplication. -/
private theorem ofModule'_asAlgebraHom_apply
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]
    (r : ℂ[G]) (m : M) :
    ((Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and check the claim on monomials `of g`.
  refine MonoidAlgebra.induction_on (p := fun r : ℂ[G] =>
    ((Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom r) m = r • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Theorem 2-2.6-1: the owner module of `Representation.ofModule' M` is canonically
the original `ℂ[G]`-module `M`. -/
private noncomputable def ofModule'_asModuleLinearEquiv
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[ℂ[G]] M := by
  refine
    { toFun := fun x => (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv x
      invFun := fun x => (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv.symm x
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
        -- Rewrite the transported action through `asModuleEquiv`, then identify it with the
        -- original `ℂ[G]`-action using `ofModule'_asAlgebraHom_apply`.
        calc
          (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv (r • x)
              = ((Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom r)
                  ((Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv x) := by
                    simpa using
                      (Representation.asModuleEquiv_map_smul
                        (ρ := Representation.ofModule' (k := ℂ) (G := G) M) r x)
          _ = r • (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv x := by
                simp [ofModule'_asAlgebraHom_apply] }

/-- Helper for Theorem 2-2.6-1: the group-algebra action on `Representation.ofModule' S`,
when viewed back in the ambient space `V`, is exactly the original action of `ρ`. -/
private theorem subtype_val_ofModule'_asAlgebraHom
    (S : Submodule ℂ[G] ρ.asModule) (r : ℂ[G]) {x : V} (hx : x ∈ S) :
    Subtype.val (((Representation.ofModule' (k := ℂ) (G := G) S).asAlgebraHom r) ⟨x, hx⟩) =
      (ρ.asAlgebraHom r) x := by
  -- Forgetting the subtype turns the owner action on `S` back into the ambient owner action.
  simpa using congrArg Subtype.val
    (ofModule'_asAlgebraHom_apply (G := G) (M := S) r ⟨x, hx⟩)

/-- Helper for Theorem 2-2.6-1: the weighted operator computed on `Representation.ofModule' S`
agrees with the ambient weighted operator after coercing from `S` to `V`. -/
private theorem subtype_val_characterWeightedEndomorphism_ofModule'
    (S : Submodule ℂ[G] ρ.asModule) {x : V} (hx : x ∈ S) :
    Subtype.val ((characterWeightedEndomorphism
        (ρ := Representation.ofModule' (k := ℂ) (G := G) S) (σ := σ)) ⟨x, hx⟩) =
      characterWeightedEndomorphism ρ σ x := by
  let a : ℂ[G] := ∑ t : G, star (σ.character t) • MonoidAlgebra.of ℂ G t
  -- Expand both weighted operators through the shared group-algebra element `a`.
  calc
    Subtype.val ((characterWeightedEndomorphism
        (ρ := Representation.ofModule' (k := ℂ) (G := G) S) (σ := σ)) ⟨x, hx⟩)
      = (((Module.finrank ℂ W : ℂ) / Nat.card G) : ℂ) •
          Subtype.val (((Representation.ofModule' (k := ℂ) (G := G) S).asAlgebraHom a) ⟨x, hx⟩) := by
            simp [characterWeightedEndomorphism, a]
    _ = (((Module.finrank ℂ W : ℂ) / Nat.card G) : ℂ) • (ρ.asAlgebraHom a x) := by
          rw [subtype_val_ofModule'_asAlgebraHom (ρ := ρ) (S := S) (r := a) hx]
          rfl
    _ = characterWeightedEndomorphism ρ σ x := by
          simp [characterWeightedEndomorphism, a]

/-- Helper for Theorem 2-2.6-1: the previous transport identity can be read in the ambient-to-owner
direction when later proofs want to rewrite the ambient operator into the restricted one. -/
private theorem characterWeightedEndomorphism_eq_subtype_val_ofModule'
    (S : Submodule ℂ[G] ρ.asModule) {x : V} (hx : x ∈ S) :
    characterWeightedEndomorphism ρ σ x =
      Subtype.val ((characterWeightedEndomorphism
        (ρ := Representation.ofModule' (k := ℂ) (G := G) S) (σ := σ)) ⟨x, hx⟩) := by
  -- This is just the symmetric form of the owner-to-ambient transport lemma used in the scalar
  -- calculation.
  symm
  exact subtype_val_characterWeightedEndomorphism_ofModule' (ρ := ρ) (σ := σ) S hx

/-- Helper for Theorem 2-2.6-1: a representation equivalence
`Representation.ofModule' S ≃ σ` yields the underlying owner-level `ℂ[G]`-linear equivalence
`S ≃ₗ[ℂ[G]] σ.asModule`. -/
private theorem nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    (hSσ : Nonempty ((Representation.ofModule' (k := ℂ) (G := G) S).Equiv σ)) :
    Nonempty (S ≃ₗ[ℂ[G]] σ.asModule) := by
  rcases hSσ with ⟨e⟩
  let f : (Representation.ofModule' (k := ℂ) (G := G) S).asModule →ₗ[ℂ[G]] σ.asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.ofModule' (k := ℂ) (G := G) S) (σ := σ)) e.toIntertwiningMap
  have hf_bij : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact e.injective hxy
    · intro w
      refine ⟨(ofModule'_asModuleLinearEquiv (G := G) S).symm (e.symm (σ.asModuleEquiv w)), ?_⟩
      -- Move the target equality back to the ambient `ℂ`-vector-space picture of `σ`.
      change (e ((Representation.ofModule' (k := ℂ) (G := G) S).asModuleEquiv
        ((Representation.ofModule' (k := ℂ) (G := G) S).asModuleEquiv.symm
          (e.symm (σ.asModuleEquiv w)))) : W) =
        (σ.asModuleEquiv w : W)
      simp
  exact ⟨(ofModule'_asModuleLinearEquiv (G := G) S).symm.trans (LinearEquiv.ofBijective f hf_bij)⟩

/-- Helper for Theorem 2-2.6-1: a simple owner summand equivalent to `σ` lies in the canonical
`σ`-isotypic component. -/
private theorem simple_submodule_le_isotypicSubrepresentation_of_equiv
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    (hSσ : Nonempty ((Representation.ofModule' (k := ℂ) (G := G) S).Equiv σ)) :
    S ≤ (ρ.isotypicSubrepresentation σ).asSubmodule := by
  -- Convert the representation equivalence to the owner-module equivalence that the isotypic API
  -- expects, then rewrite the defining `isotypicComponent`.
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : Module ℂ[G] W := σ.instModuleMonoidAlgebraAsModule
  let S' : Submodule ℂ[G] V := S
  let eσ : σ.asModule ≃ₗ[ℂ[G]] W := by
    -- This is the owner-level identity equivalence for the module underlying `σ`.
    refine
      { toFun := fun x => σ.asModuleEquiv x
        invFun := fun x => σ.asModuleEquiv.symm x
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
            σ.asModuleEquiv (r • x) = σ.asAlgebraHom r (σ.asModuleEquiv x) := by
              simpa using (Representation.asModuleEquiv_map_smul (ρ := σ) r x)
            _ = r • σ.asModuleEquiv x := by
              rfl }
  have hEq : isotypicComponent ℂ[G] V S' = isotypicComponent ℂ[G] V W := by
    rcases nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule' (ρ := ρ) (σ := σ) S hSσ with
      ⟨eS⟩
    simpa [S'] using (eS.trans eσ).isotypicComponent_eq
  intro x hx
  have hxS' : x ∈ S' := by
    simpa [S'] using hx
  have hx' : x ∈ isotypicComponent ℂ[G] V S' := S'.le_isotypicComponent hxS'
  simpa [Representation.isotypicSubrepresentation, S', hEq] using hx'

/-- Helper for Theorem 2-2.6-1: an equivalence between `Representation.ofModule' S` and `σ`
forces the underlying complex dimensions of `S` and `W` to agree. -/
private theorem finrank_eq_of_nonempty_equiv_ofModule'
    (S : Submodule ℂ[G] ρ.asModule)
    (hSσ : Nonempty ((Representation.ofModule' (k := ℂ) (G := G) S).Equiv σ)) :
    Module.finrank ℂ S = Module.finrank ℂ W := by
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  rcases hSσ with ⟨e⟩
  letI : FiniteDimensional ℂ S := e.toLinearEquiv.symm.finiteDimensional
  exact LinearEquiv.finrank_eq e.toLinearEquiv

private theorem ofModule'_isIrreducible_of_isSimpleModule
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S] :
    (Representation.ofModule' (k := ℂ) (G := G) S).IsIrreducible := by
  -- Transfer simplicity across the canonical owner-module equivalence and then invoke the
  -- irreducibility/simple-module bridge for `Representation.ofModule'`.
  let ρS : Representation ℂ G S := Representation.ofModule' (k := ℂ) (G := G) S
  letI : Module ℂ[G] ρS.asModule := ρS.instModuleMonoidAlgebraAsModule
  have hS : IsSimpleModule ℂ[G] S := inferInstance
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρS).mpr
      (@IsSimpleModule.congr (ℂ[G]) inferInstance ρS.asModule
        ρS.instAddCommGroupAsModule ρS.instModuleMonoidAlgebraAsModule
        S S.addCommGroup S.module
        (ofModule'_asModuleLinearEquiv (G := G) S) hS)

/-- Helper for Theorem 2-2.6-1: on a simple owner summand, the weighted character operator is the
homothety predicted by LinearRepresentations_Serre_1977's character pairing formula. -/
private theorem characterWeightedEndomorphism_eq_pairing_smul_of_mem_simple_submodule
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    {x : V} (hx : x ∈ S) :
    characterWeightedEndomorphism ρ σ x =
      ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
          ⟪(Representation.ofModule' (k := ℂ) (G := G) S).character, σ.character⟫) : ℂ) • x := by
  let ρS : Representation ℂ G S := Representation.ofModule' (k := ℂ) (G := G) S
  letI : ρS.IsIrreducible := ofModule'_isIrreducible_of_isSimpleModule (ρ := ρ) S
  letI : FiniteDimensional ℂ S := IsIrreducible.finiteDimensional_of_finite ρS
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  letI : Nontrivial S := IsSimpleModule.nontrivial ℂ[G] S
  have hS_ne_zero : (Module.finrank ℂ S : ℂ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  letI : Invertible (Module.finrank ℂ S : ℂ) := invertibleOfNonzero hS_ne_zero
  let f : classFunctionSubmodule ℂ G :=
    ⟨fun t : G ↦ star (σ.character t), star_character_mem_classFunctionSubmodule (σ := σ)⟩
  have hscalar :
      ρS.asAlgebraHom (∑ t : G, star (σ.character t) • MonoidAlgebra.of ℂ G t) =
        (((Module.finrank ℂ S : ℂ)⁻¹ *
            ∑ t : G, star (σ.character t) * ρS.character t) : ℂ) • LinearMap.id := by
    -- Proposition 2-2.5-1 computes the source-facing class-function operator on `S`.
    exact asAlgebraHom_classFunction_sum_eq_character_sum_smul_id ρS f hS_ne_zero
  have happly :
      ρS.asAlgebraHom (∑ t : G, star (σ.character t) • MonoidAlgebra.of ℂ G t) ⟨x, hx⟩ =
        ((((Module.finrank ℂ S : ℂ)⁻¹ *
            ∑ t : G, star (σ.character t) * ρS.character t) : ℂ)) • ⟨x, hx⟩ := by
    -- Apply the scalar-operator identity to the chosen vector of the simple summand.
    simpa using congrArg (fun T : Module.End ℂ S => T ⟨x, hx⟩) hscalar
  have hpair :
      (((Nat.card G : ℂ)⁻¹ *
          ∑ t : G, star (σ.character t) * ρS.character t) : ℂ) =
        ⟪ρS.character, σ.character⟫ := by
    -- Rewrite LinearRepresentations_Serre_1977's averaged sum as the canonical character pairing.
    calc
      ((Nat.card G : ℂ)⁻¹ * ∑ t : G, star (σ.character t) * ρS.character t)
        = ((Nat.card G : ℂ)⁻¹ * ∑ t : G, ρS.character t * σ.character t⁻¹) := by
            congr 1
            apply Finset.sum_congr rfl
            intro t _
            rw [← σ.char_inv_eq_star_of_isOfFinOrder t (isOfFinOrder_of_finite t), mul_comm]
      _ = ⟪ρS.character, σ.character⟫ := by
            symm
            exact Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply
              ρS.character σ.character
  have hscalar_rewrite :
      ((((Module.finrank ℂ W : ℂ) / Nat.card G) *
          ((Module.finrank ℂ S : ℂ)⁻¹ *
            ∑ t : G, star (σ.character t) * ρS.character t)) : ℂ) =
        ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
            ⟪ρS.character, σ.character⟫) : ℂ) := by
    calc
      (((Module.finrank ℂ W : ℂ) / Nat.card G) *
          ((Module.finrank ℂ S : ℂ)⁻¹ *
            ∑ t : G, star (σ.character t) * ρS.character t))
        = (((Module.finrank ℂ W : ℂ) * (Module.finrank ℂ S : ℂ)⁻¹) *
            ((Nat.card G : ℂ)⁻¹ *
              ∑ t : G, star (σ.character t) * ρS.character t)) := by
                rw [div_eq_mul_inv]
                ring
      _ = (((Module.finrank ℂ W : ℂ) * (Module.finrank ℂ S : ℂ)⁻¹) *
            ⟪ρS.character, σ.character⟫) := by
              rw [hpair]
      _ = (((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
            ⟪ρS.character, σ.character⟫) := by
              rw [div_eq_mul_inv]
  have happly_val :
      Subtype.val
          (ρS.asAlgebraHom (∑ t : G, star (σ.character t) • MonoidAlgebra.of ℂ G t) ⟨x, hx⟩) =
        ((((Module.finrank ℂ S : ℂ)⁻¹ *
            ∑ t : G, star (σ.character t) * ρS.character t) : ℂ)) • x := by
    -- Forget the subtype after applying the scalar-operator identity on `S`.
    exact congrArg Subtype.val happly
  have hscaled_apply_val :
      (((Module.finrank ℂ W : ℂ) / Nat.card G) : ℂ) •
          Subtype.val
            (ρS.asAlgebraHom (∑ t : G, star (σ.character t) • MonoidAlgebra.of ℂ G t) ⟨x, hx⟩) =
        (((Module.finrank ℂ W : ℂ) / Nat.card G) : ℂ) •
          ((((Module.finrank ℂ S : ℂ)⁻¹ *
              ∑ t : G, star (σ.character t) * ρS.character t) : ℂ)) • x := by
    -- Scale the transported scalar-action identity by the outer normalizing factor.
    exact congrArg (fun z : V ↦ (((Module.finrank ℂ W : ℂ) / Nat.card G) : ℂ) • z) happly_val
  have htransport :
      Subtype.val ((characterWeightedEndomorphism (ρ := ρS) (σ := σ)) ⟨x, hx⟩) =
        ((((Module.finrank ℂ W : ℂ) / Nat.card G) *
          ((Module.finrank ℂ S : ℂ)⁻¹ *
            ∑ t : G, star (σ.character t) * ρS.character t)) : ℂ) • x := by
    -- Expand the restricted weighted operator and substitute the scalar action from `happly`.
    calc
      Subtype.val ((characterWeightedEndomorphism (ρ := ρS) (σ := σ)) ⟨x, hx⟩)
        = (((Module.finrank ℂ W : ℂ) / Nat.card G) : ℂ) •
            Subtype.val
              (ρS.asAlgebraHom
                (∑ t : G, star (σ.character t) • MonoidAlgebra.of ℂ G t) ⟨x, hx⟩) := by
                  simp [characterWeightedEndomorphism]
      _ = (((Module.finrank ℂ W : ℂ) / Nat.card G) : ℂ) •
            ((((Module.finrank ℂ S : ℂ)⁻¹ *
                ∑ t : G, star (σ.character t) * ρS.character t) : ℂ)) • x := hscaled_apply_val
      _ = ((((Module.finrank ℂ W : ℂ) / Nat.card G) *
            ((Module.finrank ℂ S : ℂ)⁻¹ *
              ∑ t : G, star (σ.character t) * ρS.character t)) : ℂ) • x := by
                simpa [mul_assoc] using
                  (smul_smul (((Module.finrank ℂ W : ℂ) / Nat.card G) : ℂ)
                    (((Module.finrank ℂ S : ℂ)⁻¹ *
                      ∑ t : G, star (σ.character t) * ρS.character t)) x)
  -- Transport the scalar formula from the restricted representation back to the ambient space.
  exact
    (characterWeightedEndomorphism_eq_subtype_val_ofModule' (ρ := ρ) (σ := σ) S hx).trans <|
      htransport.trans <| by
        rw [hscalar_rewrite]

/-- Helper for Theorem 2-2.6-1: on a simple owner summand equivalent to `σ`, the weighted
character operator acts as the identity. -/
private theorem characterWeightedEndomorphism_eq_self_of_mem_simple_submodule_of_equiv
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    {x : V} (hx : x ∈ S)
    (hSσ : Nonempty ((Representation.ofModule' (k := ℂ) (G := G) S).Equiv σ)) :
    characterWeightedEndomorphism ρ σ x = x := by
  let ρS : Representation ℂ G S := Representation.ofModule' (k := ℂ) (G := G) S
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  letI : Module ℂ[G] W := σ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] W := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  letI : Nontrivial W := IsSimpleModule.nontrivial ℂ[G] W
  have hW_ne_zero : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  rcases hSσ with ⟨eSσ⟩
  have hpair_one : ⟪σ.character, σ.character⟫ = (1 : ℂ) := by
    -- The canonical orthonormality formula gives the self-pairing of an irreducible character.
    calc
      ⟪σ.character, σ.character⟫
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, σ.character g * σ.character g⁻¹ := by
            exact Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply
              σ.character σ.character
      _ = 1 := by
            classical
            let hσσ : Nonempty (σ.Equiv σ) := ⟨Representation.Equiv.refl σ⟩
            simpa [hσσ] using (Representation.char_orthonormal (ρ := σ) (σ := σ))
  -- Rewrite the scalar-on-simple formula through the chosen equivalence with `σ`.
  calc
    characterWeightedEndomorphism ρ σ x
      = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
          ⟪ρS.character, σ.character⟫) : ℂ) • x := by
            exact characterWeightedEndomorphism_eq_pairing_smul_of_mem_simple_submodule
              (ρ := ρ) (σ := σ) S hx
    _ = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
          ⟪σ.character, σ.character⟫) : ℂ) • x := by
            rw [Representation.char_iso eSσ]
    _ = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) * 1) : ℂ) • x := by
            rw [hpair_one]
    _ = x := by
          rw [mul_one, finrank_eq_of_nonempty_equiv_ofModule' (ρ := ρ) (σ := σ) S ⟨eSσ⟩,
            div_self hW_ne_zero, one_smul]

/-- Helper for Theorem 2-2.6-1: on a simple owner summand not equivalent to `σ`, the weighted
character operator vanishes. -/
private theorem characterWeightedEndomorphism_eq_zero_of_mem_simple_submodule_of_not_equiv
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    {x : V} (hx : x ∈ S)
    (hSσ : ¬ Nonempty ((Representation.ofModule' (k := ℂ) (G := G) S).Equiv σ)) :
    characterWeightedEndomorphism ρ σ x = 0 := by
  let ρS : Representation ℂ G S := Representation.ofModule' (k := ℂ) (G := G) S
  letI : ρS.IsIrreducible := ofModule'_isIrreducible_of_isSimpleModule (ρ := ρ) S
  letI : FiniteDimensional ℂ S := IsIrreducible.finiteDimensional_of_finite ρS
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  have hσS : ¬ Nonempty (σ.Equiv ρS) := by
    intro hσS
    exact hSσ ⟨hσS.some.symm⟩
  have hpair_zero : ⟪ρS.character, σ.character⟫ = (0 : ℂ) := by
    -- The same orthonormality formula gives zero for nonisomorphic irreducibles.
    calc
      ⟪ρS.character, σ.character⟫
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρS.character g * σ.character g⁻¹ := by
            exact Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply
              ρS.character σ.character
      _ = 0 := by
            classical
            simpa [hσS] using (Representation.char_orthonormal (ρ := ρS) (σ := σ))
  -- The scalar in the simple-summand formula is zero by irreducible character orthogonality.
  calc
    characterWeightedEndomorphism ρ σ x
      = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
          ⟪ρS.character, σ.character⟫) : ℂ) • x := by
            exact characterWeightedEndomorphism_eq_pairing_smul_of_mem_simple_submodule
              (ρ := ρ) (σ := σ) S hx
    _ = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) * 0) : ℂ) • x := by
          rw [hpair_zero]
    _ = 0 := by
          simp

/-- Helper for Theorem 2-2.6-1: on a simple owner summand, the weighted operator lands in the
canonical `σ`-isotypic component. -/
private theorem characterWeightedEndomorphism_mem_isotypicSubrepresentation_of_mem_simple_submodule
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    {x : V} (hx : x ∈ S) :
    characterWeightedEndomorphism ρ σ x ∈ (ρ.isotypicSubrepresentation σ).toSubmodule := by
  by_cases hSσ : Nonempty ((Representation.ofModule' (k := ℂ) (G := G) S).Equiv σ)
  · -- On a `σ`-type simple summand, the weighted operator is the identity.
    rw [characterWeightedEndomorphism_eq_self_of_mem_simple_submodule_of_equiv
      (ρ := ρ) (σ := σ) S hx hSσ]
    simpa using
      simple_submodule_le_isotypicSubrepresentation_of_equiv (ρ := ρ) (σ := σ) S hSσ hx
  · -- On every other simple summand, the weighted operator is zero.
    rw [characterWeightedEndomorphism_eq_zero_of_mem_simple_submodule_of_not_equiv
      (ρ := ρ) (σ := σ) S hx hSσ]
    simpa using ((ρ.isotypicSubrepresentation σ).toSubmodule.zero_mem : (0 : V) ∈
      (ρ.isotypicSubrepresentation σ).toSubmodule)

/-- Helper for Theorem 2-2.6-1: the weighted operator is the identity on the whole canonical
`σ`-isotypic component. -/
private theorem characterWeightedEndomorphism_eq_self_of_mem_isotypicSubrepresentation
    {v : V} (hv : v ∈ (ρ.isotypicSubrepresentation σ).toSubmodule) :
    characterWeightedEndomorphism ρ σ v = v := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ ℂ[G] V := by
    simpa using (inferInstance : IsScalarTower ℂ ℂ[G] ρ.asModule)
  letI : IsSemisimpleModule ℂ[G] V := inferInstance
  let N : Submodule ℂ[G] V := (ρ.isotypicSubrepresentation σ).asSubmodule
  have hsup :
      (⨆ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N), S) = N := by
    simpa [sSup_eq_iSup] using
      (IsSemisimpleModule.sSup_simples_le (R := ℂ[G]) (M := V) N)
  have hspan :
      Submodule.span ℂ
        (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N),
          (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) =
      N.restrictScalars ℂ := by
    rw [← Submodule.iSup_eq_span'
      (p := fun S : Submodule ℂ[G] V ↦ S.restrictScalars ℂ)
      (h := fun S ↦ IsSimpleModule ℂ[G] S ∧ S ≤ N)]
    simpa using congrArg (Submodule.restrictScalars ℂ) hsup
  have hv_span :
      v ∈ Submodule.span ℂ
        (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N),
          (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) := by
    rw [hspan]
    simpa [N] using hv
  -- Semisimplicity lets us reduce from the whole isotypic component to its simple constituents.
  refine Submodule.span_induction (p := fun x _ ↦ characterWeightedEndomorphism ρ σ x = x)
    ?_ ?_ ?_ ?_ hv_span
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨S, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hSN, hx⟩
    let Sρ : Submodule ℂ[G] ρ.asModule := S
    letI : IsSimpleModule ℂ[G] Sρ := hSN.1
    have hSσ :
        Nonempty ((Representation.ofModule' (k := ℂ) (G := G) Sρ).Equiv σ) :=
      nonempty_equiv_of_simple_submodule_le_isotypicSubrepresentation
        (ρ := ρ) (τ := σ) Sρ hSN.2
    exact characterWeightedEndomorphism_eq_self_of_mem_simple_submodule_of_equiv
      (ρ := ρ) (σ := σ) Sρ (by simpa [Sρ] using hx) hSσ
  · simp [characterWeightedEndomorphism]
  · intro x y hx hy hfx hfy
    calc
      characterWeightedEndomorphism ρ σ (x + y)
          = characterWeightedEndomorphism ρ σ x + characterWeightedEndomorphism ρ σ y := by
              exact LinearMap.map_add (characterWeightedEndomorphism ρ σ) x y
      _ = x + y := by rw [hfx, hfy]
  · intro a x hx hfx
    calc
      characterWeightedEndomorphism ρ σ (a • x) = a • characterWeightedEndomorphism ρ σ x := by
        exact LinearMap.map_smul (characterWeightedEndomorphism ρ σ) a x
      _ = a • x := by rw [hfx]

-- Proof sketch: Maschke makes the `ℂ[G]`-module underlying `ρ` semisimple, identify the
-- canonical isotypic component attached to `σ`, and use the orthogonality calculation from
-- Proposition 2-2.3-6 to show that the character sum acts by the identity on this summand.
/-- Theorem 2-2.6-1: for an irreducible representation `σ`, the normalized character-weighted
endomorphism attached to `σ` is the projector of `ρ` onto the canonical `σ`-isotypic
component. -/
theorem characterWeightedEndomorphism_isProj_isotypicSubrepresentation :
    LinearMap.IsProj (ρ.isotypicSubrepresentation σ).toSubmodule
      (characterWeightedEndomorphism ρ σ) := by
  -- Route correction: the simple-summand scalar calculation and the vanishing-on-other-isotypics
  -- are already available, so we globalize LinearRepresentations_Serre_1977's argument by spanning the ambient owner module
  -- with simple submodules and checking the operator on each simple constituent.
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ ℂ[G] V := by
    simpa using (inferInstance : IsScalarTower ℂ ℂ[G] ρ.asModule)
  letI : IsSemisimpleModule ℂ[G] V := inferInstance
  have hsup :
      (⨆ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S), S) =
        (⊤ : Submodule ℂ[G] V) := by
    simpa [sSup_eq_iSup] using
      (IsSemisimpleModule.sSup_simples_eq_top (R := ℂ[G]) (M := V))
  have hspan :
      Submodule.span ℂ
        (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S),
          (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) =
      (⊤ : Submodule ℂ V) := by
    rw [← Submodule.iSup_eq_span'
      (p := fun S : Submodule ℂ[G] V ↦ S.restrictScalars ℂ)
      (h := fun S ↦ IsSimpleModule ℂ[G] S)]
    simpa using congrArg (Submodule.restrictScalars ℂ) hsup
  have hmap_mem :
      ∀ x : V, characterWeightedEndomorphism ρ σ x ∈ (ρ.isotypicSubrepresentation σ).toSubmodule :=
    by
      intro x
      have hx_span :
          x ∈ Submodule.span ℂ
            (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S),
              (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) := by
        rw [hspan]
        simp
      -- Each simple summand is either of type `σ`, where the operator is the identity, or of a
      -- different type, where the operator vanishes.
      refine Submodule.span_induction
        (p := fun y _ ↦ characterWeightedEndomorphism ρ σ y ∈
          (ρ.isotypicSubrepresentation σ).toSubmodule) ?_ ?_ ?_ ?_ hx_span
      · intro y hy
        rcases Set.mem_iUnion.1 hy with ⟨S, hy⟩
        rcases Set.mem_iUnion.1 hy with ⟨hS, hy⟩
        let Sρ : Submodule ℂ[G] ρ.asModule := S
        letI : IsSimpleModule ℂ[G] Sρ := hS
        exact characterWeightedEndomorphism_mem_isotypicSubrepresentation_of_mem_simple_submodule
          (ρ := ρ) (σ := σ) Sρ (by simpa [Sρ] using hy)
      · simpa using ((ρ.isotypicSubrepresentation σ).toSubmodule.zero_mem :
          (0 : V) ∈ (ρ.isotypicSubrepresentation σ).toSubmodule)
      · intro x y hx hy hxmem hymem
        simpa using (ρ.isotypicSubrepresentation σ).toSubmodule.add_mem hxmem hymem
      · intro a y hy hymem
        simpa using (ρ.isotypicSubrepresentation σ).toSubmodule.smul_mem a hymem
  have hid :
      ∀ x ∈ (ρ.isotypicSubrepresentation σ).toSubmodule, characterWeightedEndomorphism ρ σ x = x :=
    by
      intro x hx
      exact characterWeightedEndomorphism_eq_self_of_mem_isotypicSubrepresentation
        (ρ := ρ) (σ := σ) hx
  exact LinearMap.IsProj.mk hmap_mem hid

/-- The complementary vanishing part of Theorem 2-2.6-1: the normalized character-weighted
endomorphism attached to `σ` vanishes on the isotypic components of the irreducibles not
equivalent to `σ`. -/
theorem characterWeightedEndomorphism_eq_zero_of_mem_other_isotypicSubrepresentation
    {W' : Type w'} [AddCommGroup W'] [Module ℂ W']
    (τ : Representation ℂ G W') [τ.IsIrreducible] {v : V}
    (hστ : ¬ Nonempty (σ.Equiv τ))
    (hv : v ∈ (ρ.isotypicSubrepresentation τ).toSubmodule) :
    characterWeightedEndomorphism ρ σ v = 0 := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ ℂ[G] V := by
    simpa using (inferInstance : IsScalarTower ℂ ℂ[G] ρ.asModule)
  letI : IsSemisimpleModule ℂ[G] V := inferInstance
  let N : Submodule ℂ[G] V := (ρ.isotypicSubrepresentation τ).asSubmodule
  have hsup :
      (⨆ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N), S) = N := by
    simpa [sSup_eq_iSup] using
      (IsSemisimpleModule.sSup_simples_le (R := ℂ[G]) (M := V) N)
  have hspan :
      Submodule.span ℂ
        (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N),
          (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) =
      N.restrictScalars ℂ := by
    rw [← Submodule.iSup_eq_span'
      (p := fun S : Submodule ℂ[G] V ↦ S.restrictScalars ℂ)
      (h := fun S ↦ IsSimpleModule ℂ[G] S ∧ S ≤ N)]
    simpa using congrArg (Submodule.restrictScalars ℂ) hsup
  have hv_span :
      v ∈ Submodule.span ℂ
        (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N),
          (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) := by
    rw [hspan]
    simpa [N] using hv
  -- Semisimplicity again reduces the vanishing claim to the simple constituents of the
  -- `τ`-isotypic component.
  refine Submodule.span_induction (p := fun x _ ↦ characterWeightedEndomorphism ρ σ x = 0)
    ?_ ?_ ?_ ?_ hv_span
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨S, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hSN, hx⟩
    let Sρ : Submodule ℂ[G] ρ.asModule := S
    letI : IsSimpleModule ℂ[G] Sρ := hSN.1
    have hSτ :
        Nonempty ((Representation.ofModule' (k := ℂ) (G := G) Sρ).Equiv τ) :=
      nonempty_equiv_of_simple_submodule_le_isotypicSubrepresentation
        (ρ := ρ) (τ := τ) Sρ hSN.2
    have hSσ :
        ¬ Nonempty ((Representation.ofModule' (k := ℂ) (G := G) Sρ).Equiv σ) := by
      intro hSσ
      exact hστ ⟨hSσ.some.symm.trans hSτ.some⟩
    exact characterWeightedEndomorphism_eq_zero_of_mem_simple_submodule_of_not_equiv
      (ρ := ρ) (σ := σ) Sρ (by simpa [Sρ] using hx) hSσ
  · simp [characterWeightedEndomorphism]
  · intro x y hx hy hfx hfy
    calc
      characterWeightedEndomorphism ρ σ (x + y)
          = characterWeightedEndomorphism ρ σ x + characterWeightedEndomorphism ρ σ y := by
              exact LinearMap.map_add (characterWeightedEndomorphism ρ σ) x y
      _ = 0 := by rw [hfx, hfy, add_zero]
  · intro a x hx hfx
    calc
      characterWeightedEndomorphism ρ σ (a • x) = a • characterWeightedEndomorphism ρ σ x := by
        exact LinearMap.map_smul (characterWeightedEndomorphism ρ σ) a x
      _ = 0 := by rw [hfx, smul_zero]

end

end

end Representation
