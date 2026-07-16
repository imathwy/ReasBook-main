import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Corollary_2_2_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {k : Type u} {ι : Type v} {G : Type u} [CommSemiring k] [Monoid G]

/- The source-facing Wedderburn map `\tilde{\rho}` attached to a family of `k`-representations.
It is the thin bridge from the family of representation algebra maps to the canonical mathlib
owner `Pi.algHom`; chosen bases only identify the target endomorphism algebras with matrix
algebras afterward. -/
@[simps!]
abbrev familyEndAlgHom (π : ι → Rep k G) : k[G] →ₐ[k] Π i, Module.End k (π i) :=
  Pi.algHom k (fun i ↦ Module.End k (π i)) fun i ↦ (π i).ρ.asAlgebraHom

scoped[Representation] notation "ρ̃[" π "]" => familyEndAlgHom π

end

section

variable {K : Type u} {ι : Type v} {G : Type u} [Field K] [Group G] [Finite G]
variable [Invertible (Nat.card G : K)] [IsAlgClosed K]
variable (π : ι → Rep K G)
variable [∀ i, FiniteDimensional K (π i)]

section CompleteFamily

/-- Helper for Proposition 6-6.2-1: the target product of endomorphism algebras has dimension
`|G|` once the family is complete and pairwise nonisomorphic. -/
lemma familyEndAlgHom_target_finrank_eq_card
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Module.finrank K (Π i, Module.End K (π i)) = Nat.card G := by
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  have hπ_pairwise_fdrep :
      PairwiseNonisomorphic (fun i ↦ FDRep.of (π i).ρ) :=
    pairwiseNonisomorphic_fdrep_of_rep (π := π) hπ_pairwise
  -- Rewrite the product finrank as the sum of the squared irreducible degrees.
  rw [Module.finrank_pi_fintype]
  simp_rw [Module.finrank_linearMap]
  simpa [pow_two] using
    sum_sq_degree_eq_card_of_complete_irreducible_family
      (fun i ↦ FDRep.of (π i).ρ) hπ_complete hπ_pairwise_fdrep

/-- Helper for Proposition 6-6.2-1: for a module viewed through `Representation.ofModule'`,
the induced group-algebra action is the original `K[G]`-scalar multiplication. -/
lemma ofModule'_asAlgebraHom_apply
    (M : Type*) [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M]
    (r : K[G]) (m : M) :
    ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and check the claim on monomials.
  refine MonoidAlgebra.induction_on (p := fun r : K[G] =>
    ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r) m = r • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Proposition 6-6.2-1: the owner module of `Representation.ofModule' M` is
canonically the original `K[G]`-module `M`. -/
lemma nonempty_ofModule'_asModuleLinearEquiv
    (M : Type*) [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M] :
    Nonempty ((Representation.ofModule' (k := K) (G := G) M).asModule ≃ₗ[K[G]] M) := by
  -- Use the standard `asModuleEquiv` and verify that it respects the owner `K[G]`-action.
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
    -- Rewrite the transported action through `asModuleEquiv`, then identify it with the
    -- original `K[G]`-action on `M`.
    calc
      (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := K) (G := G) M).asModuleEquiv x) := by
                simpa using
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := K) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv x := by
            simp [ofModule'_asAlgebraHom_apply]
  refine ⟨?_⟩
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }

/-- Helper for Proposition 6-6.2-1: a simple left ideal, viewed as `Representation.ofModule'`,
is an irreducible representation. -/
lemma ofModule'_isIrreducible_of_isSimpleModule
    (S : Submodule K[G] K[G]) (hS : IsSimpleModule K[G] S) :
    (Representation.ofModule' (k := K) (G := G) S).IsIrreducible := by
  -- Transfer simplicity across the canonical owner-module equivalence and then use the
  -- irreducibility/simple-module bridge.
  rcases nonempty_ofModule'_asModuleLinearEquiv (K := K) (G := G) S with ⟨eS⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := K) (G := G) S)).2
      (@IsSimpleModule.congr (K[G]) inferInstance
        ((Representation.ofModule' (k := K) (G := G) S).asModule)
        (Representation.ofModule' (k := K) (G := G) S).instAddCommGroupAsModule
        (Representation.ofModule' (k := K) (G := G) S).instModuleMonoidAlgebraAsModule
        S S.addCommGroup S.module eS hS)

/-- Helper for Proposition 6-6.2-1: a `Rep` isomorphism yields an equivalence of the underlying
representations. -/
lemma nonempty_equiv_of_nonempty_iso_of_rep
    {V : Type u} [AddCommGroup V] [Module K V]
    {W : Type u} [AddCommGroup W] [Module K W]
    (τ : Representation K G V) (σ : Representation K G W)
    (h : Nonempty (Rep.of τ ≅ Rep.of σ)) :
    Nonempty (τ.Equiv σ) := by
  rcases h with ⟨e⟩
  -- Package the forward and inverse `Rep` morphisms into a representation equivalence.
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

/-- Helper for Proposition 6-6.2-1: an equivalence `Representation.ofModule' S ≃ τ` yields the
underlying owner-level `K[G]`-linear equivalence `S ≃ₗ[K[G]] τ.asModule`. -/
lemma nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'
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
            simpa [ofModule'_asAlgebraHom_apply]
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
      -- Move the target equality back to the ambient `K`-vector-space picture of `τ`.
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

/-- Helper for Proposition 6-6.2-1: the preceding owner-level equivalence upgrades to the exact
`ModuleCat` isomorphism consumed by the kernel argument below. -/
lemma nonempty_moduleIso_of_nonempty_equiv_ofModule'
    {W : Type u} [AddCommGroup W] [Module K W]
    (τ : Representation K G W) (S : Submodule K[G] K[G])
    (h : Nonempty ((Representation.ofModule' (k := K) (G := G) S).Equiv τ)) :
    Nonempty (ModuleCat.of K[G] S ≅ Rep.toModuleMonoidAlgebra.obj (Rep.of τ)) := by
  rcases nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'
      (K := K) (G := G) τ S h with ⟨e⟩
  -- `Rep.toModuleMonoidAlgebra.obj (Rep.of τ)` is definitionally `ModuleCat.of K[G] τ.asModule`.
  refine ⟨?_⟩
  simpa using e.toModuleIso

/-- Helper for Proposition 6-6.2-1: a simple left ideal of `K[G]` is isomorphic, as a
`K[G]`-module object, to one member of the complete irreducible family. -/
lemma exists_moduleIso_of_simple_submodule_of_complete_family
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (S : Submodule K[G] K[G]) (hS : IsSimpleModule K[G] S) :
    ∃ i, Nonempty (ModuleCat.of K[G] S ≅ Rep.toModuleMonoidAlgebra.obj (Rep.of (π i).ρ)) := by
  -- Route correction: we avoid the unstable `Rep.counitIso` round-trip and instead keep the
  -- carrier literally equal to `S` by passing to `Representation.ofModule' S`.
  let τS : Representation K G S := Representation.ofModule' (k := K) (G := G) S
  have hτS : τS.IsIrreducible := by
    -- A simple left ideal is already a simple `K[G]`-module, so `Representation.ofModule' S`
    -- is irreducible.
    simpa [τS] using
      ofModule'_isIrreducible_of_isSimpleModule (K := K) (G := G) S hS
  letI : τS.IsIrreducible := hτS
  rcases IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := fun i ↦ FDRep.of (π i).ρ) hπ_complete τS inferInstance with ⟨i, hi⟩
  have hi_rep : Nonempty (Rep.of τS ≅ Rep.of (π i).ρ) := by
    -- Forget the finite-dimensional owner structure; the underlying `Rep` isomorphism is what
    -- the module-level bridge consumes.
    rcases hi with ⟨eFD⟩
    exact ⟨(forget₂ (FDRep K G) (Rep K G)).mapIso eFD⟩
  have hi_equiv : Nonempty (τS.Equiv (π i).ρ) :=
    nonempty_equiv_of_nonempty_iso_of_rep (K := K) (G := G) τS (π i).ρ hi_rep
  exact ⟨i, nonempty_moduleIso_of_nonempty_equiv_ofModule'
    (K := K) (G := G) (π i).ρ S hi_equiv⟩

/-- Helper for Proposition 6-6.2-1: if `x` maps to zero under `ρ̃[π]`, then it annihilates every
module element in every family member after passing to the canonical `K[G]`-module owner. -/
lemma family_member_smul_eq_zero_of_familyEndAlgHom_eq_zero
    {x : K[G]} (hx : (ρ̃[π]) x = 0) (i : ι)
    (z : Rep.toModuleMonoidAlgebra.obj (Rep.of (π i).ρ)) :
    x • z = 0 := by
  -- Read the `i`th factor of `ρ̃[π] x = 0` and evaluate that zero endomorphism on `z`.
  have hxi : ((ρ̃[π]) x) i = 0 := by
    simpa using congrFun hx i
  simpa using LinearMap.congr_fun hxi z

/-- Helper for Proposition 6-6.2-1: if `x` maps to zero under `ρ̃[π]`, then left multiplication
by `x` vanishes on every simple left ideal of `K[G]`. -/
lemma simple_submodule_smul_eq_zero_of_familyEndAlgHom_eq_zero
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    {x : K[G]} (hx : (ρ̃[π]) x = 0)
    (S : Submodule K[G] K[G]) (hS : IsSimpleModule K[G] S)
    {y : K[G]} (hy : y ∈ S) :
    x * y = 0 := by
  -- Transport the vanishing statement from the family member back across the module isomorphism.
  rcases exists_moduleIso_of_simple_submodule_of_complete_family
      (π := π) hπ_complete S hS with ⟨i, ⟨e⟩⟩
  have hz : x • ModuleCat.Hom.hom e.hom ⟨y, hy⟩ = 0 :=
    family_member_smul_eq_zero_of_familyEndAlgHom_eq_zero
      (π := π) hx i (ModuleCat.Hom.hom e.hom ⟨y, hy⟩)
  have hz' := congrArg (ModuleCat.Hom.hom e.inv) hz
  rw [LinearMap.map_smul] at hz'
  simp only [LinearMap.map_zero] at hz'
  have hid : (ModuleCat.Hom.hom e.inv) ((ModuleCat.Hom.hom e.hom) ⟨y, hy⟩) = ⟨y, hy⟩ := by
    -- The inverse module morphism sends the transported vector back to the original vector in `S`.
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun f => f ⟨y, hy⟩) (congrArg ModuleCat.Hom.hom e.hom_inv_id)
  rw [hid] at hz'
  exact Subtype.ext_iff.mp hz'

/-- Helper for Proposition 6-6.2-1: if an element of `K[G]` kills every simple left ideal, then
its left-multiplication operator on `K[G]` is zero. -/
lemma left_mul_eq_zero_of_zero_on_all_simple_submodules
    {x : K[G]}
    (hx : ∀ (S : Submodule K[G] K[G]), IsSimpleModule K[G] S →
      ∀ ⦃y : K[G]⦄, y ∈ S → x * y = 0) :
    Algebra.lmul K (K[G]) x = 0 := by
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
  -- Route correction: the kernel of left multiplication by `x` need not be a `K[G]`-submodule,
  -- so we globalize vanishing by spanning `K[G]` with simple left ideals over the base field.
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

/-- Helper for Proposition 6-6.2-1: the canonical Wedderburn map is injective for a complete
pairwise nonisomorphic family. -/
lemma familyEndAlgHom_injective_of_complete_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Function.Injective (ρ̃[π]) := by
  intro x y hxy
  -- Reduce injectivity to the zero-kernel case and apply the semisimple regular-module argument.
  have hxy_zero : (ρ̃[π]) (x - y) = 0 := by
    simpa [map_sub, hxy]
  have hleft_zero : Algebra.lmul K (K[G]) (x - y) = 0 :=
    left_mul_eq_zero_of_zero_on_all_simple_submodules (K := K) (G := G)
      (fun S hS {y} hy ↦
        simple_submodule_smul_eq_zero_of_familyEndAlgHom_eq_zero
          (π := π) hπ_complete hxy_zero S hS hy)
  exact sub_eq_zero.mp <|
    (Algebra.lmul_injective (R := K) (A := K[G])) (by simpa using hleft_zero)

-- Proof sketch: apply the orthogonality relations for matrix coefficients to show that the image
-- of `ρ̃[π]` contains the matrix units in each simple factor. This gives
-- surjectivity onto the product of endomorphism algebras; Chapter 2 identifies the completeness
-- hypothesis with the dimension formula `|G| = ∑ i, (dim π_i)^2`, which then upgrades
-- surjectivity to bijectivity.
/-- Proposition 6-6.2-1: for a complete pairwise nonisomorphic family of irreducible
finite-dimensional representations over an algebraically closed field in which `|G|` is
invertible, the canonical homomorphism `ρ̃[π] = \tilde{\rho}` from `K[G]` to the product
`Π i, Module.End K (π i)` is bijective. -/
theorem irreducibleFamilyEndAlgHom_bijective
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Function.Bijective (ρ̃[π]) := by
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  have hinj : Function.Injective (ρ̃[π]) :=
    familyEndAlgHom_injective_of_complete_family (π := π) hπ_pairwise hπ_complete
  have hdim_target :
      Module.finrank K (Π i, Module.End K (π i)) = Nat.card G :=
    familyEndAlgHom_target_finrank_eq_card (π := π) hπ_pairwise hπ_complete
  letI : Fintype G := Fintype.ofFinite G
  have hdim_source : Module.finrank K (K[G]) = Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact Module.finrank_finsupp_self K
  have hdim :
      Module.finrank K (K[G]) = Module.finrank K (Π i, Module.End K (π i)) := by
    rw [hdim_source, hdim_target]
  have hlin_inj : Function.Injective ((ρ̃[π]).toLinearMap) := hinj
  have hlin_surj : Function.Surjective ((ρ̃[π]).toLinearMap) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hlin_inj
  -- Injectivity plus equality of dimensions upgrades the algebra hom to a bijection.
  exact ⟨hinj, hlin_surj⟩

/-- The canonical Wedderburn isomorphism attached to a complete pairwise nonisomorphic irreducible
family. It is the `AlgEquiv` refinement of Proposition `6-6.2-1`. -/
def irreducibleFamilyEndAlgEquiv
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    K[G] ≃ₐ[K] Π i, Module.End K (π i) :=
  AlgEquiv.ofBijective (ρ̃[π])
    (irreducibleFamilyEndAlgHom_bijective π hπ_pairwise hπ_complete)

-- Proof sketch: the basis-dependent matrix-valued map is obtained by composing the intrinsic
-- Wedderburn map `ρ̃[π]` with the product of the algebra equivalences
-- `LinearMap.toMatrixAlgEquiv (b i)`. Bijectivity is therefore transported across that product
-- algebra equivalence.
/-- In chosen bases, Proposition 6-6.2-1 identifies `\tilde{\rho}` with the usual homomorphism
from `K[G]` to the product of matrix algebras. -/
theorem irreducibleFamilyMatrixAlgHom_bijective
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (b : ∀ i, Module.Basis (Fin (Module.finrank K (π i))) K (π i))
    : Function.Bijective
      (Pi.algHom K
        (fun i ↦ Matrix (Fin (Module.finrank K (π i))) (Fin (Module.finrank K (π i))) K)
        fun i ↦ (LinearMap.toMatrixAlgEquiv (b i)).toAlgHom.comp (π i).ρ.asAlgebraHom) := by
  let e :
      (Π i, Module.End K (π i)) ≃ₐ[K]
        Π i, Matrix (Fin (Module.finrank K (π i))) (Fin (Module.finrank K (π i))) K :=
    AlgEquiv.piCongrRight fun i ↦ LinearMap.toMatrixAlgEquiv (b i)
  have hcomp :
      e.toAlgHom.comp (ρ̃[π]) =
        Pi.algHom K
          (fun i ↦ Matrix (Fin (Module.finrank K (π i))) (Fin (Module.finrank K (π i))) K)
          fun i ↦ (LinearMap.toMatrixAlgEquiv (b i)).toAlgHom.comp (π i).ρ.asAlgebraHom := by
    ext u i
    rfl
  rw [← hcomp]
  exact (AlgEquiv.bijective e).comp
    (irreducibleFamilyEndAlgHom_bijective π hπ_pairwise hπ_complete)

end CompleteFamily

end

end Representation
