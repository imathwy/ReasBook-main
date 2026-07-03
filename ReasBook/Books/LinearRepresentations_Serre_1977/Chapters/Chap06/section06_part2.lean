import Mathlib
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_6_6_2_1 (from Chap06) -/
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

/-! ### Proposition_6_6_2_2 (from Chap06) -/
open scoped BigOperators MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {K : Type u} {ι : Type v} {G : Type u} [Field K] [Group G] [Finite G]
variable [Invertible (Nat.card G : K)] [IsAlgClosed K]
variable (π : ι → Rep K G)
variable [∀ i, FiniteDimensional K (π i)]

section CompleteFamily

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: on a finite index type, `finsum` agrees with the ordinary
`Finset.univ` sum. -/
lemma finsum_eq_sum_univ {α : Type*} [Fintype α] [DecidableEq α] (f : α → K) :
    (∑ᶠ a : α, f a) = Finset.univ.sum f := by
  classical
  let hf : Function.HasFiniteSupport f := Set.toFinite _
  rw [finsum_eq_sum f hf]
  -- Replace the support sum by a filtered univ sum, then drop the zero terms.
  change ∑ x ∈ (Function.support f).toFinite.toFinset, f x = Finset.univ.sum f
  have hs : (Function.support f).toFinite.toFinset = Finset.univ.filter (fun x : α => f x ≠ 0) := by
    ext x
    simp [Function.support]
  rw [hs, Finset.sum_filter_ne_zero]

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: the trace of a block-diagonal map on a finite product is the
sum of the traces of its diagonal blocks. -/
lemma trace_piMap_eq_sum_trace {α : Type*} [Fintype α] [DecidableEq α]
    {M : α → Type*} [∀ a, AddCommGroup (M a)] [∀ a, Module K (M a)]
    [∀ a, Module.Free K (M a)] [∀ a, Module.Finite K (M a)]
    (f : ∀ a, M a →ₗ[K] M a) :
    LinearMap.trace K (∀ a, M a) (LinearMap.piMap f) = ∑ a, LinearMap.trace K (M a) (f a) := by
  let b : ∀ a, Module.Basis _ K (M a) := fun a ↦ Module.Free.chooseBasis K (M a)
  -- Compute the product trace in the sigma-indexed basis induced from the factor bases.
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basis b)]
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_sigma, LinearMap.piMap, LinearMap.toMatrix_apply]
  congr with a
  simpa [Matrix.trace, LinearMap.toMatrix_apply] using
    (LinearMap.trace_eq_matrix_trace K (b a) (f a)).symm

omit [Invertible (Nat.card G : K)] [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: left multiplication on the group algebra has trace `|G|`
times the coefficient at `1`. -/
lemma trace_lmul_groupAlgebra_eq_card_mul_coeff_one (v : K[G]) :
    LinearMap.trace K (K[G]) (Algebra.lmul K (K[G]) v) = (Nat.card G : K) * v 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hcard : (Nat.card G : K) = (Fintype.card G : K) := by
    simp [Nat.card_eq_fintype_card]
  -- Evaluate the regular trace in the delta-function basis of `K[G]`.
  rw [show LinearMap.trace K (K[G]) (Algebra.lmul K (K[G]) v) =
      (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne (Algebra.lmul K (K[G]) v)).trace by
    exact LinearMap.trace_eq_matrix_trace K Finsupp.basisSingleOne (Algebra.lmul K (K[G]) v)]
  rw [Matrix.trace, hcard]
  simp [LinearMap.toMatrix_apply]
  calc
    Finset.univ.sum (fun x : G => (((LinearMap.mul K K[G]) v) fun₀ | x => 1) x)
        = Finset.univ.sum (fun _ : G => v 1) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            simpa using (MonoidAlgebra.mul_single_apply v (1 : K) x x)
    _ = (Fintype.card G : K) * v 1 := by
          simp

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: on a matrix algebra, the trace of left multiplication by `A`
is the matrix size times `trace A`. -/
lemma trace_lmul_matrix_eq_card_mul_trace {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) :
    LinearMap.trace K (Matrix n n K) (Algebra.lmul K (Matrix n n K) A) =
      (Fintype.card n : K) * A.trace := by
  let swapArgs : (n → n → K) ≃ₗ[K] n → n → K :=
    { toFun := fun f j i => f i j
      invFun := fun f j i => f i j
      left_inv := by intro f; funext i j; rfl
      right_inv := by intro f; funext i j; rfl
      map_add' := by intro f g; funext i j; rfl
      map_smul' := by intro c f; funext i j; rfl }
  let e : Matrix n n K ≃ₗ[K] n → n → K := (Matrix.ofLinearEquiv K).symm.trans swapArgs
  have hconj :
      e.conj (Algebra.lmul K (Matrix n n K) A) = LinearMap.piMap (fun _ : n => Matrix.toLin' A) := by
    -- View a matrix as its family of columns so left multiplication becomes block diagonal.
    ext M i j
    simp [e, swapArgs, Matrix.toLin'_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  calc
    LinearMap.trace K (Matrix n n K) (Algebra.lmul K (Matrix n n K) A)
        = LinearMap.trace K (n → n → K) (e.conj (Algebra.lmul K (Matrix n n K) A)) := by
            symm
            exact LinearMap.trace_conj' (Algebra.lmul K (Matrix n n K) A) e
    _ = LinearMap.trace K (n → n → K) (LinearMap.piMap (fun _ : n => Matrix.toLin' A)) := by
          rw [hconj]
    _ = ∑ _ : n, LinearMap.trace K (n → K) (Matrix.toLin' A) := by
          exact trace_piMap_eq_sum_trace (K := K) (f := fun _ : n => Matrix.toLin' A)
    _ = (Fintype.card n : K) * A.trace := by
          simp [Matrix.trace_toLin'_eq]

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: after choosing a basis of `V`, the matrix of an endomorphism
has the same trace as the original linear map. -/
lemma trace_matrix_of_end {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Module.End K V) :
    let b := Module.Free.chooseBasis K V
    let e := LinearMap.toMatrixAlgEquiv b
    (e A).trace = LinearMap.trace K V A := by
  let b := Module.Free.chooseBasis K V
  let e := LinearMap.toMatrixAlgEquiv b
  -- Convert the matrix trace back to the original endomorphism through `toLin`.
  calc
    (e A).trace = LinearMap.trace K V ((Matrix.toLin b b) (e A)) := by
      exact (Matrix.trace_toLin_eq (A := e A) (b := b)).symm
    _ = LinearMap.trace K V A := by
      change LinearMap.trace K V (Matrix.toLinAlgEquiv b (e A)) = LinearMap.trace K V A
      rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: for an endomorphism algebra, the trace of left multiplication
by `A` is `dim(V)` times `trace A`. -/
lemma trace_lmul_end_eq_finrank_mul_trace {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Module.End K V) :
    LinearMap.trace K (Module.End K V) (Algebra.lmul K (Module.End K V) A) =
      (Module.finrank K V : K) * LinearMap.trace K V A := by
  let b := Module.Free.chooseBasis K V
  let e := LinearMap.toMatrixAlgEquiv b
  have hconj :
      e.toLinearEquiv.conj (Algebra.lmul K (Module.End K V) A) =
        Algebra.lmul K (Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K) (e A) := by
    -- Transport left multiplication from endomorphisms to matrices through the basis algebra equivalence.
    ext f i j
    simpa using congrArg (fun g => g i j) (e.map_mul A (e.symm f))
  calc
    LinearMap.trace K (Module.End K V) (Algebra.lmul K (Module.End K V) A)
        = LinearMap.trace K (Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K)
            (e.toLinearEquiv.conj (Algebra.lmul K (Module.End K V) A)) := by
              symm
              exact LinearMap.trace_conj' (Algebra.lmul K (Module.End K V) A) e.toLinearEquiv
    _ = LinearMap.trace K (Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K)
          (Algebra.lmul K (Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K) (e A)) := by
          rw [hconj]
    _ = (Module.finrank K V : K) * (e A).trace := by
          simpa [Module.finrank_eq_card_chooseBasisIndex] using
            trace_lmul_matrix_eq_card_mul_trace (K := K) (A := e A)
    _ = (Module.finrank K V : K) * LinearMap.trace K V A := by
          simpa using congrArg (fun t => (Module.finrank K V : K) * t) (trace_matrix_of_end (K := K) A)

/-- Helper for Proposition 6-6.2-2: the product-side trace is the degree-weighted sum of the
factor traces. -/
lemma trace_lmul_familyEnd_eq_sum_finrank_mul_trace [Fintype ι] [DecidableEq ι]
    (f : Π i, Module.End K (π i)) :
    LinearMap.trace K (Π i, Module.End K (π i))
        (Algebra.lmul K (Π i, Module.End K (π i)) f) =
      ∑ i, (Module.finrank K (π i) : K) * LinearMap.trace K (π i) (f i) := by
  have hlmul :
      Algebra.lmul K (Π i, Module.End K (π i)) f =
        LinearMap.piMap (fun i => Algebra.lmul K (Module.End K (π i)) (f i)) := by
    -- Left multiplication in the product algebra is coordinatewise.
    ext g i x
    rfl
  rw [hlmul, trace_piMap_eq_sum_trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact trace_lmul_end_eq_finrank_mul_trace (K := K) (A := f i)

/-- Helper for Proposition 6-6.2-2: the canonical Wedderburn equivalence conjugates left
multiplication by `v` on `K[G]` to left multiplication by `ρ̃[π] v` on the product endomorphism
algebra. -/
lemma familyEndAlgEquiv_conj_lmul
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (v : K[G]) :
    (irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).toLinearEquiv.conj
        (Algebra.lmul K (K[G]) v) =
      Algebra.lmul K (Π i, Module.End K (π i)) ((ρ̃[π]) v) := by
  let e := irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete
  -- Transport multiplication through the algebra equivalence pointwise on the product.
  ext f i x
  change e (v * e.symm f) i x = (((ρ̃[π]) v * f) i) x
  rw [map_mul, AlgEquiv.apply_symm_apply]
  rfl

-- Proof sketch: apply the regular trace on `K[G]` to the shifted element `s⁻¹ * u`,
-- transport that trace across the Wedderburn equivalence from Proposition `6-6.2-1`,
-- and evaluate the target trace factorwise.
/-- Proposition 6-6.2-2: for a complete pairwise nonisomorphic family of irreducible
finite-dimensional representations over an algebraically closed field in which `|G|` is
invertible, the coefficient of `s` in the group-algebra element `u` is the normalized sum of the
traces of `ρ_i(s⁻¹)` composed with the `i`-th factor of the canonical Wedderburn image
`ρ̃[π] u`, weighted by the degrees `dim(π i)`. -/
theorem groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (u : K[G]) (s : G) :
    u s =
      (Nat.card G : K)⁻¹ *
        ∑ᶠ i : ι, (Module.finrank K (π i) : K) *
          LinearMap.trace K (π i) ((π i).ρ s⁻¹ * (ρ̃[π]) u i) := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  letI : Fintype G := Fintype.ofFinite G
  let v : K[G] := MonoidAlgebra.of K G s⁻¹ * u
  let term : ι → K := fun i ↦
    (Module.finrank K (π i) : K) * LinearMap.trace K (π i) ((π i).ρ s⁻¹ * (ρ̃[π]) u i)
  have hcard : (Nat.card G : K) ≠ 0 := by
    exact (isUnit_iff_ne_zero).mp (isUnit_of_invertible (Nat.card G : K))
  have hv_coeff : v 1 = u s := by
    -- Shifting by `s⁻¹` moves the `s`-coefficient of `u` to the `1`-coefficient of `v`.
    simp [v, MonoidAlgebra.of_apply]
  have hv_image (i : ι) : ((ρ̃[π]) v) i = (π i).ρ s⁻¹ * (ρ̃[π]) u i := by
    -- Push the shifted group-algebra element through the product algebra hom.
    simp [v, familyEndAlgHom, MonoidAlgebra.of_apply]
  have htrace_term (i : ι) :
      (Module.finrank K (π i) : K) * LinearMap.trace K (π i) (((ρ̃[π]) v) i) = term i := by
    -- After rewriting the image of `v`, the trace term matches the statement exactly.
    simp [term, hv_image i]
  have htrace : (Nat.card G : K) * u s = Finset.univ.sum term := by
    -- Compare the regular trace on `K[G]` with the factorwise trace on the product side.
    calc
      (Nat.card G : K) * u s = (Nat.card G : K) * v 1 := by rw [hv_coeff]
      _ = LinearMap.trace K (K[G]) (Algebra.lmul K (K[G]) v) := by
            symm
            exact trace_lmul_groupAlgebra_eq_card_mul_coeff_one (K := K) (G := G) v
      _ = LinearMap.trace K (Π i, Module.End K (π i))
            ((irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).toLinearEquiv.conj
              (Algebra.lmul K (K[G]) v)) := by
              symm
              exact LinearMap.trace_conj' (Algebra.lmul K (K[G]) v)
                (irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).toLinearEquiv
      _ = LinearMap.trace K (Π i, Module.End K (π i))
            (Algebra.lmul K (Π i, Module.End K (π i)) ((ρ̃[π]) v)) := by
              rw [familyEndAlgEquiv_conj_lmul (π := π) hπ_pairwise hπ_complete v]
      _ = ∑ i, (Module.finrank K (π i) : K) * LinearMap.trace K (π i) (((ρ̃[π]) v) i) := by
              exact trace_lmul_familyEnd_eq_sum_finrank_mul_trace (π := π) ((ρ̃[π]) v)
      _ = Finset.univ.sum term := by
              refine Finset.sum_congr rfl fun i _ => htrace_term i
  have hfinsum : (∑ᶠ i : ι, term i) = Finset.univ.sum term :=
    finsum_eq_sum_univ (K := K) term
  -- Multiply the trace identity by `|G|⁻¹` to isolate the coefficient `u s`.
  calc
    u s = (1 : K) * u s := by
      simp
    _ = (Nat.card G : K)⁻¹ * ((Nat.card G : K) * u s) := by
      rw [show (1 : K) = (Nat.card G : K)⁻¹ * (Nat.card G : K) by
        rw [inv_mul_cancel₀ hcard]]
      rw [mul_assoc]
    _ = (Nat.card G : K)⁻¹ * Finset.univ.sum term := by
      rw [htrace]
    _ = (Nat.card G : K)⁻¹ * ∑ᶠ i : ι, term i := by
      rw [hfinsum]
    _ = (Nat.card G : K)⁻¹ *
          ∑ᶠ i : ι, (Module.finrank K (π i) : K) *
            LinearMap.trace K (π i) ((π i).ρ s⁻¹ * (ρ̃[π]) u i) := by
      rfl

-- Proof sketch: apply Proposition `groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace` to the
-- element of `K[G]` obtained from `f` via the canonical inverse Wedderburn isomorphism, then use
-- `apply_symm_apply` to identify its canonical Wedderburn image with `f`.
/-- The inverse of the canonical Wedderburn isomorphism recovers the coefficient of `s` by the
normalized degree-weighted trace sum over the irreducible factors. -/
theorem irreducibleFamilyEndAlgEquiv_symm_apply
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (f : Π i, Module.End K (π i)) (s : G) :
    (irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm f s =
      (Nat.card G : K)⁻¹ *
        ∑ᶠ i : ι, (Module.finrank K (π i) : K) *
          LinearMap.trace K (π i) ((π i).ρ s⁻¹ * f i) := by
  let e := irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete
  have hi : ∀ i, (ρ̃[π]) (e.symm f) i = f i := fun i ↦
    congrFun (e.apply_symm_apply f) i
  simpa [hi] using
    groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace π hπ_pairwise hπ_complete (e.symm f) s

end CompleteFamily

end

end Representation

/-! ### Exercise_6_6_3_3 (from Chap06) -/
open scoped BigOperators MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {k G : Type u} [fieldK : Field k]
variable [groupG : Group G] [finiteG : Finite G]

local instance instFintypeGExercise_6_6_3_3 : Fintype G := Fintype.ofFinite G

section CharacterCentralElementDef

variable (V : Rep k G)

-- Proof sketch: the coefficient function `s ↦ V.ρ.character s⁻¹` is constant on conjugacy
-- classes because characters are class functions, so the corresponding group-algebra element
-- commutes with each basis element `MonoidAlgebra.of k G t`.
/-- The central group-algebra element attached to the character of `V` by LinearRepresentations_Serre_1977's formula. -/
theorem characterCentralElement_mem_center :
    ((Module.finrank k V : k) / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of k G s ∈
      Subalgebra.center k (k[G]) := by
  let f : G → k := fun s ↦ ((Module.finrank k V : k) / Nat.card G) * V.ρ.character s⁻¹
  have hf : IsClassFunction f := by
    -- The inverse character remains constant on conjugacy classes.
    refine ⟨?_⟩
    intro a b hab
    rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, hg⟩
    calc
      ((Module.finrank k V : k) / Nat.card G) * V.ρ.character a⁻¹
          =
        ((Module.finrank k V : k) / Nat.card G) * V.ρ.character (g * a⁻¹ * g⁻¹) := by
            rw [(V.ρ.char_conj a⁻¹ g).symm]
      _ = ((Module.finrank k V : k) / Nat.card G) * V.ρ.character b⁻¹ := by
            have hinv : g * a⁻¹ * g⁻¹ = b⁻¹ := by
              rw [← hg]
              simp [mul_assoc]
            simp [hinv]
  set z : k[G] := Finsupp.equivFunOnFinite.symm f
  have hcoeff :
      z = ((Module.finrank k V : k) / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of k G s := by
    calc
      z
          = ∑ s : G,
              ((((Module.finrank k V : k) / Nat.card G) * V.ρ.character s⁻¹) •
                MonoidAlgebra.of k G s) := by
              simpa [z, MonoidAlgebra.of, f] using
                (Finsupp.equivFunOnFinite_symm_eq_sum f)
      _ = ((Module.finrank k V : k) / Nat.card G) •
            ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of k G s := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            simp [mul_smul]
  have hz : z ∈ Subalgebra.center k (k[G]) := by
    -- A class function gives coefficients that commute with every group-algebra element.
    have hzsub : z ∈ Subsemiring.center k[G] := by
      rw [Subsemiring.mem_center_iff]
      intro y
      ext h
      rw [MonoidAlgebra.mul_apply_left, MonoidAlgebra.mul_apply_right]
      rw [Finsupp.sum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hcomm : f (a⁻¹ * h) = f (h * a⁻¹) := by
        have hmk : ConjClasses.mk (a⁻¹ * h) = ConjClasses.mk (h * a⁻¹) := by
          exact ConjClasses.mk_eq_mk_iff_isConj.mpr <| isConj_iff.mpr ⟨h, by simp [mul_assoc]⟩
        exact hf.factorsThrough hmk
      simpa [mul_comm] using congrArg (fun t : k ↦ y a * t) hcomm
    simpa using hzsub
  simpa [hcoeff] using hz

variable [finV : FiniteDimensional k V]

/-- The character-theoretic central element of `k[G]` attached to `V`. Without irreducibility, it
need not be primitive or idempotent. -/
def characterCentralElement : Subalgebra.center k (k[G]) :=
  ⟨((Module.finrank k V : k) / Nat.card G) •
      ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of k G s,
    characterCentralElement_mem_center V⟩

end CharacterCentralElementDef

section CompleteFamilyExistence

variable [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- Helper for Exercise 6-6.3-3: under the Maschke hypotheses, one can choose a complete
pairwise nonisomorphic family of finite-dimensional representations in `Rep`. -/
theorem exists_complete_pairwise_nonisomorphic_rep_family :
    ∃ (ι : Type u) (_ : Fintype ι) (π : ι → Rep.{u, u, u} k G)
      (_ : ∀ i, FiniteDimensional k (π i)),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ) := by
  classical
  letI : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero (Nat.card G : k)⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular k G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type u := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let πfd : ι → FDRep k G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπfd_pairwise : PairwiseNonisomorphic πfd := by
    -- Distinct quotient classes cannot label isomorphic chosen representatives.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hrel :
        Nonempty
          (Representation.Equiv
            ((σ (Quotient.out q)).toRepresentation)
            ((σ (Quotient.out q')).toRepresentation)) := by
      simpa [πfd] using
        (show Nonempty (Representation.Equiv ((πfd q).ρ) ((πfd q').ρ)) from
          ⟨Representation.equivOfIso ((forget₂ (FDRep k G) (Rep k G)).mapIso e)⟩)
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := Quotient.sound hrel
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπfd_simple (q : ι) : Simple (πfd q) := by
    -- Each chosen representative is one of the irreducible summands of the regular
    -- representation.
    letI : Representation.IsIrreducible (πfd q).ρ := by
      simpa [πfd] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (πfd q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank k (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπfd_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank k (πfd q) := by
    have hmult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ) } =
          Module.finrank k (πfd q) := by
      letI : Representation.IsIrreducible (πfd q).ρ := by
        exact FDRep.isIrreducible_of_simple (πfd q)
      simpa using
        leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (πfd q).ρ
          inferInstance
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ) } = (S q).card := by
      rw [show S q = Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (q : ι) : Finset.sum (S q) dimσ = Module.finrank k (πfd q) ^ 2 := by
    calc
      Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank k (πfd q)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S q).card * Module.finrank k (πfd q) := by
            simp
      _ = Module.finrank k (πfd q) ^ 2 := by
            rw [hS_card, pow_two]
  have hcover :
      Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hj_mem : j ∈ S (⟦j⟧ : ι) := by
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · rcases Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)) with ⟨e⟩
          exact ⟨e.symm⟩
      exact Finset.mem_biUnion.mpr ⟨(⟦j⟧ : ι), Finset.mem_univ _, hj_mem⟩
  have htotal_eq_card : Finset.sum (Finset.univ : Finset κ) dimσ = Nat.card G := by
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free k (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing k (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank k (G →₀ k) := by
        symm
        calc
          Module.finrank k (G →₀ k) =
            Module.finrank k (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
              exact e.finrank_eq.symm
          _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
              dsimp [dimσ]
              exact Module.finrank_directSum (R := k) (M := fun j ↦ (σ j).toSubmodule)
      _ = Nat.card G := by
          rw [Nat.card_eq_fintype_card]
          exact Module.finrank_finsupp_self k
  have hπ_sum : ∑ q : ι, Module.finrank k (πfd q) ^ 2 = Nat.card G := by
    calc
      ∑ q : ι, Module.finrank k (πfd q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
          symm
          exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
          rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπfd_complete : IsCompleteIrreducibleFamily πfd := by
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
      πfd hπfd_simple hπfd_pairwise hπ_sum
  let π : ι → Rep.{u, u, u} k G := fun q ↦ (forget₂ (FDRep k G) (Rep k G)).obj (πfd q)
  have hπ_fd : ∀ q, FiniteDimensional k (π q) := by
    intro q
    simpa [π] using (inferInstance : FiniteDimensional k (πfd q))
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    apply hπfd_pairwise hqq'
    rcases hIso with ⟨e⟩
    refine ⟨?_⟩
    simpa [π] using (Representation.equivOfIso e).toFDRepIso
  have hπ_complete : IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (π q).ρ) := by
    simpa [π] using hπfd_complete
  exact ⟨ι, inferInstance, π, hπ_fd, hπ_pairwise, hπ_complete⟩

end CompleteFamilyExistence

section CharacterCentralElement

variable [charZeroK : CharZero k] [algClosedK : IsAlgClosed k]
variable [invCardG : Invertible (Nat.card G : k)]

attribute [local instance] Classical.propDecidable

section IsoFacts

variable {X Y : Rep.{u, u, u} k G}
variable [finX : FiniteDimensional k X] [finY : FiniteDimensional k Y]

omit finiteG charZeroK invCardG
/-- Helper for Exercise 6-6.3-3: isomorphic irreducible representations have the same central
character on the center of `k[G]`. -/
theorem centralCharacter_eq_of_nonempty_iso
    (hXY : Nonempty (X ≅ Y)) (hX : X.ρ.IsIrreducible) (hY : Y.ρ.IsIrreducible) :
    ω[X.ρ] = ω[Y.ρ] := by
  classical
  rcases hXY with ⟨e⟩
  let eρ : X.ρ.Equiv Y.ρ := Representation.equivOfIso e
  have hcomm : ∀ a : k[G], ∀ x : X, eρ (X.ρ.asAlgebraHom a x) = Y.ρ.asAlgebraHom a (eρ x) := by
    intro a
    refine MonoidAlgebra.induction_on
      (p := fun a : k[G] ↦ ∀ x : X, eρ (X.ρ.asAlgebraHom a x) = Y.ρ.asAlgebraHom a (eρ x))
      a ?_ ?_ ?_
    · intro g x
      simpa [Representation.asAlgebraHom_of] using
        congrArg (fun f : X →ₗ[k] Y ↦ f x) (eρ.isIntertwining' g)
    · intro a b ha hb x
      simp [ha x, hb x]
    · intro r a ha x
      simp [ha x]
  ext u
  letI : X.ρ.IsIrreducible := hX
  letI : Y.ρ.IsIrreducible := hY
  letI : Nontrivial X := not_subsingleton_iff_nontrivial.mp fun hXsub ↦
    (show (⊥ : Subrepresentation X.ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <|
      top_unique <| by
        intro x hx
        change x = 0
        exact hXsub.elim x 0
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hx' : eρ x ≠ 0 := by
    intro hzero
    apply hx
    have hzero' : eρ.toLinearEquiv x = eρ.toLinearEquiv 0 := by
      simpa using hzero
    simpa using eρ.toLinearEquiv.injective hzero'
  have hXu :
      X.ρ.asAlgebraHom u x = ω[X.ρ] u • x := by
    simpa using
      congrArg (fun f : Module.End k X ↦ f x)
        (asAlgebraHom_center_eq_centralCharacter_smul_id X.ρ u)
  have hYu :
      Y.ρ.asAlgebraHom u (eρ x) = ω[Y.ρ] u • eρ x := by
    simpa using
      congrArg (fun f : Module.End k Y ↦ f (eρ x))
        (asAlgebraHom_center_eq_centralCharacter_smul_id Y.ρ u)
  have hscalar : ω[X.ρ] u • eρ x = ω[Y.ρ] u • eρ x := by
    -- Conjugate the central action across the representation isomorphism and compare the scalar
    -- actions furnished by Schur's lemma.
    calc
      ω[X.ρ] u • eρ x = eρ (ω[X.ρ] u • x) := by simp
      _ = eρ (X.ρ.asAlgebraHom u x) := by rw [hXu]
      _ = Y.ρ.asAlgebraHom u (eρ x) := hcomm (u : k[G]) x
      _ = ω[Y.ρ] u • eρ x := hYu
  have hsub : (ω[X.ρ] u - ω[Y.ρ] u) • eρ x = 0 := by
    rw [sub_smul, hscalar, sub_self]
  exact sub_eq_zero.mp <| by
    rcases smul_eq_zero.mp hsub with hzero | hzero
    · exact hzero
    · exact (hx' hzero).elim

include finiteG charZeroK invCardG

omit charZeroK algClosedK invCardG finX finY
/-- Helper for Exercise 6-6.3-3: isomorphic representations give the same character-theoretic
central element. -/
theorem characterCentralElement_eq_of_nonempty_iso
    (hXY : Nonempty (X ≅ Y)) :
    characterCentralElement X = characterCentralElement Y := by
  rcases hXY with ⟨e⟩
  have hfinrank : Module.finrank k X = Module.finrank k Y :=
    (Representation.equivOfIso e).toLinearEquiv.finrank_eq
  have hchar : X.ρ.character = Y.ρ.character :=
    Representation.char_iso (Representation.equivOfIso e)
  apply Subtype.ext
  -- Compare coefficients after transporting both the degree and the character across the
  -- isomorphism.
  ext s
  simp [characterCentralElement, MonoidAlgebra.of, hfinrank, hchar]

include charZeroK algClosedK invCardG finX finY

end IsoFacts

omit groupG finiteG charZeroK algClosedK
/-- Helper for Exercise 6-6.3-3: any natural-number divisor of `|G|` remains nonzero in `k`
when `|G|` is invertible in `k`. -/
lemma nat_cast_ne_zero_of_dvd_group_order
    {n : ℕ} (hn : n ∣ Nat.card G) :
    (n : k) ≠ 0 := by
  rcases hn with ⟨m, hm⟩
  intro hzero
  have hcard_zero : (Nat.card G : k) = 0 := by
    -- Cast the divisibility witness into `k`, then the vanishing of `n` forces `|G|` to vanish.
    calc
      (Nat.card G : k) = ((n * m : ℕ) : k) := by
        rw [hm]
      _ = (n : k) * (m : k) := by
        rw [Nat.cast_mul]
      _ = 0 := by simp [hzero]
  exact Invertible.ne_zero (Nat.card G : k) hcard_zero

include groupG finiteG charZeroK algClosedK

section IrreducibleFacts

variable {X Y : Rep.{u, u, u} k G}
variable [finX : FiniteDimensional k X] [finY : FiniteDimensional k Y]

omit finX
/-- Helper for Exercise 6-6.3-3: an irreducible representation has nonzero degree in the
coefficient field. -/
lemma finrank_cast_ne_zero_of_is_irreducible
    (hX : X.ρ.IsIrreducible) :
    (Module.finrank k X : k) ≠ 0 := by
  -- LinearRepresentations_Serre_1977's later divisibility theorem gives `dim X ∣ |G|`; since `|G|` is invertible in
  -- `k`, this degree is nonzero in `k`.
  letI : X.ρ.IsIrreducible := hX
  have hdiv : Module.finrank k X ∣ Nat.card G := finrank_dvd_card X.ρ
  exact nat_cast_ne_zero_of_dvd_group_order (k := k) (G := G) hdiv

include finX

omit finiteG charZeroK algClosedK invCardG
/-- Helper for Exercise 6-6.3-3: an isomorphism in `Rep` is equivalent to an equivalence of the
underlying representations. -/
lemma nonempty_iso_iff_nonempty_rho_equiv :
    Nonempty (X ≅ Y) ↔ Nonempty (X.ρ.Equiv Y.ρ) := by
  constructor
  · intro hXY
    rcases hXY with ⟨e⟩
    -- Forget the categorical isomorphism to its intertwining equivalence.
    exact ⟨Representation.equivOfIso e⟩
  · intro hXY
    rcases hXY with ⟨e⟩
    -- Repackage the representation equivalence through the finite-dimensional owner `FDRep`.
    simpa using ⟨(forget₂ (FDRep k G) (Rep k G)).mapIso e.toFDRepIso⟩

include finiteG charZeroK algClosedK invCardG

/-- Helper for Exercise 6-6.3-3: LinearRepresentations_Serre_1977's explicit central element acts on an irreducible
representation by the normalized intertwining multiplicity. -/
lemma centralCharacter_characterCentralElement_eq_dim_ratio_mul_finrank_intertwining
    (hX : X.ρ.IsIrreducible) (_hY : Y.ρ.IsIrreducible) :
    ω[X.ρ] (characterCentralElement Y) =
      ((Module.finrank k Y : k) / (Module.finrank k X : k)) *
        Module.finrank k (Y.ρ.IntertwiningMap X.ρ) := by
  have hfinrankX := finrank_cast_ne_zero_of_is_irreducible (X := X) hX
  have hcoeff :
      ∀ s : G,
        ((characterCentralElement Y : k[G]) s) =
          ((Module.finrank k Y : k) / Nat.card G) * Y.ρ.character s⁻¹ := by
    intro s
    let a : k := ((Module.finrank k Y : k) / Nat.card G)
    have hsingle :
        (∑ t : G, (Y.ρ.character t⁻¹ • MonoidAlgebra.of k G t : k[G])) s =
          Y.ρ.character s⁻¹ := by
      have hsum_single :
          (∑ t : G, (Y.ρ.character t⁻¹ • MonoidAlgebra.of k G t : k[G])) =
            Finsupp.equivFunOnFinite.symm (fun t : G ↦ Y.ρ.character t⁻¹) := by
        -- Repackage the source-facing sum as the canonical finitely supported function.
        simpa [MonoidAlgebra.of] using
          (Finsupp.equivFunOnFinite_symm_eq_sum (fun t : G ↦ Y.ρ.character t⁻¹)).symm
      -- Read off the coefficient at `s` from the packaged finitely supported function.
      simpa using congrArg (fun z : k[G] ↦ z s) hsum_single
    -- Evaluate the explicit coefficient of LinearRepresentations_Serre_1977's central element at `s`.
    change (a * (∑ t : G, (Y.ρ.character t⁻¹ • MonoidAlgebra.of k G t : k[G])) s =
      a * Y.ρ.character s⁻¹)
    rw [hsingle]
  have hsum :
      ∑ s : G,
          (((Module.finrank k Y : k) / Nat.card G) * Y.ρ.character s⁻¹) *
            X.ρ.character s =
        ((Module.finrank k Y : k) / Nat.card G) *
          ∑ s : G, X.ρ.character s * Y.ρ.character s⁻¹ := by
    calc
      ∑ s : G,
          (((Module.finrank k Y : k) / Nat.card G) * Y.ρ.character s⁻¹) *
            X.ρ.character s
        =
          ∑ s : G,
            ((Module.finrank k Y : k) / Nat.card G) *
              (X.ρ.character s * Y.ρ.character s⁻¹) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            ring
      _ =
          ((Module.finrank k Y : k) / Nat.card G) *
            ∑ s : G, X.ρ.character s * Y.ρ.character s⁻¹ := by
            symm
            rw [Finset.mul_sum]
  -- Route correction: rewrite LinearRepresentations_Serre_1977's element into the canonical character pairing first, and
  -- only then invoke the owner theorem identifying that pairing with an intertwining dimension.
  rw [centralCharacter_apply_eq_sum_character (ρ := X.ρ)
    (u := characterCentralElement Y) hfinrankX]
  calc
    (Module.finrank k X : k)⁻¹ *
        ∑ s : G, ((characterCentralElement Y : k[G]) s) * X.ρ.character s
      =
        (Module.finrank k X : k)⁻¹ *
          ∑ s : G,
            (((Module.finrank k Y : k) / Nat.card G) * Y.ρ.character s⁻¹) *
              X.ρ.character s := by
          -- Expand the coefficients of `characterCentralElement Y`.
          refine congrArg (fun z : k ↦ (Module.finrank k X : k)⁻¹ * z) ?_
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [hcoeff s]
    _ =
        (Module.finrank k X : k)⁻¹ *
          (((Module.finrank k Y : k) / Nat.card G) *
            ∑ s : G, X.ρ.character s * Y.ρ.character s⁻¹) := by
          -- Pull the scalar factor out of the finite sum and commute the character factors into
          -- the owner-theorem order.
          rw [hsum]
    _ =
        ((Module.finrank k Y : k) / (Module.finrank k X : k)) *
          ((Nat.card G : k)⁻¹ * ∑ s : G, X.ρ.character s * Y.ρ.character s⁻¹) := by
          -- Isolate the normalized pairing of `Y` with `X`.
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ =
        ((Module.finrank k Y : k) / (Module.finrank k X : k)) *
          Module.finrank k (Y.ρ.IntertwiningMap X.ρ) := by
          rw [Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := Y.ρ) (σ := X.ρ)]

omit finX finY
/-- Helper for Exercise 6-6.3-3: isomorphic irreducible representations have the same degree, so
the degree ratio in LinearRepresentations_Serre_1977's formula is `1`. -/
lemma finrank_ratio_eq_one_of_nonempty_iso
    (hX : X.ρ.IsIrreducible) (hXY : Nonempty (X ≅ Y)) :
    ((Module.finrank k Y : k) / (Module.finrank k X : k)) = 1 := by
  rcases hXY with ⟨e⟩
  have hfinrank : Module.finrank k Y = Module.finrank k X :=
    (Representation.equivOfIso e).toLinearEquiv.finrank_eq.symm
  have hfinrankX := finrank_cast_ne_zero_of_is_irreducible (X := X) hX
  -- Transport dimension across the isomorphism and cancel the nonzero denominator.
  rw [hfinrank, div_self hfinrankX]

include finX finY

/-- Helper for Exercise 6-6.3-3: the central character of an irreducible representation evaluates
LinearRepresentations_Serre_1977's central element by the Kronecker delta on isomorphism classes. -/
theorem centralCharacter_characterCentralElement_eq_ite_of_irreducible
    (hX : X.ρ.IsIrreducible) (hY : Y.ρ.IsIrreducible) :
    ω[X.ρ] (characterCentralElement Y) = if Nonempty (X ≅ Y) then 1 else 0 := by
  have hpair :=
    centralCharacter_characterCentralElement_eq_dim_ratio_mul_finrank_intertwining
      (X := X) (Y := Y) hX hY
  have hintertwining :
      Module.finrank k (Y.ρ.IntertwiningMap X.ρ) =
        if Nonempty (Y.ρ.Equiv X.ρ) then 1 else 0 := by
    -- Schur's lemma turns the intertwining multiplicity into the Kronecker delta.
    simpa using
      Representation.finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
        Y.ρ hY X.ρ hX
  -- Execute the source proof's governing structure: explicit central element -> normalized
  -- pairing -> intertwining multiplicity -> Schur delta.
  rw [hpair, hintertwining]
  by_cases hXY : Nonempty (X ≅ Y)
  · have hYX : Nonempty (Y ≅ X) := by
      rcases hXY with ⟨e⟩
      exact ⟨e.symm⟩
    have hρ : Nonempty (Y.ρ.Equiv X.ρ) :=
      (nonempty_iso_iff_nonempty_rho_equiv (X := Y) (Y := X)).mp hYX
    have hratio :
        ((Module.finrank k Y : k) / (Module.finrank k X : k)) = 1 :=
      finrank_ratio_eq_one_of_nonempty_iso (X := X) (Y := Y) hX hXY
    -- On the isomorphic branch, Schur gives multiplicity `1` and the degree ratio cancels.
    simp [hXY, hρ, hratio]
  · have hρ : ¬ Nonempty (Y.ρ.Equiv X.ρ) := by
      intro hρ
      apply hXY
      have hYX : Nonempty (Y ≅ X) :=
        (nonempty_iso_iff_nonempty_rho_equiv (X := Y) (Y := X)).mpr hρ
      rcases hYX with ⟨e⟩
      exact ⟨e.symm⟩
    -- In the nonisomorphic branch, Schur's lemma already forces the scalar to vanish.
    simp [hXY, hρ]

end IrreducibleFacts

end CharacterCentralElement

section

variable {ι : Type v}
variable (π : ι → Rep k G)
variable [∀ i, FiniteDimensional k (π i)]

section CompleteFamily

variable [CharZero k] [IsAlgClosed k] [Invertible (Nat.card G : k)]

variable (hπ_pairwise : PairwiseNonisomorphic π)
variable (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))

attribute [local instance] Classical.propDecidable

-- Proof sketch: transport the standard basis of `ι → k` back along the central-character algebra
-- equivalence from Proposition `6-6.3-2`, then identify the inverse image of `Pi.basisFun k ι i`
-- with LinearRepresentations_Serre_1977's explicit central element using the character formula of Proposition `6-6.3-1`.
/-- Exercise 6-6.3-3: under the canonical central-character algebra equivalence, the inverse image
of the `i`-th standard basis vector is the central primitive idempotent attached to `π i`. -/
theorem centralCharacterFamilyAlgEquiv_symm_basisFun
    (i : ι) :
    let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
    (centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete).symm (Pi.basisFun k ι i) =
      characterCentralElement (π i) := by
  classical
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  apply e.injective
  -- Push both sides through the central-character equivalence and read the coordinates.
  ext j
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  letI : (π j).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete j
  by_cases hji : j = i
  · subst hji
    simp [e, centralCharacter_characterCentralElement_eq_ite_of_irreducible]
  · have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
    simp [e, hji, hnot, centralCharacter_characterCentralElement_eq_ite_of_irreducible]

attribute [simp] centralCharacterFamilyAlgEquiv_symm_basisFun

-- Proof sketch: LinearRepresentations_Serre_1977's elements `p_i` are exactly the inverse images of the standard basis
-- vectors under Proposition `6-6.3-2`, so transporting `Pi.basisFun k ι` gives a basis of the
-- center.
/-- A basis statement for Exercise 6-6.3-3: for a complete pairwise nonisomorphic irreducible
family, the corresponding central primitive idempotents form a basis of the center of `k[G]`. -/
theorem centralPrimitiveIdempotents_form_basis :
    (hπ_pairwise : PairwiseNonisomorphic π) →
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) →
    ∃ b : Module.Basis ι k (Subalgebra.center k (k[G])),
      ∀ i, b i = characterCentralElement (π i) := by
  intro hπ_pairwise hπ_complete
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  refine ⟨(Pi.basisFun k ι).map
      (centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete).symm.toLinearEquiv, ?_⟩
  -- Read each transported basis vector through the source-faithful identification above.
  intro i
  simpa using
    (centralCharacterFamilyAlgEquiv_symm_basisFun
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) i)

-- Proof sketch: transport the finite sum through the center-character algebra equivalence. The sum
-- of the standard basis vectors in `ι → k` is the constant function `1`, which corresponds to the
-- unit of the center.
/-- The sum of the central primitive idempotents is the unit of the center of `k[G]`. -/
theorem sum_centralPrimitiveIdempotent :
    (hπ_pairwise : PairwiseNonisomorphic π) →
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) →
    ∑ᶠ i, characterCentralElement (π i) = 1 := by
  intro hπ_pairwise hπ_complete
  classical
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  have hsupp : Function.HasFiniteSupport (fun i : ι ↦ characterCentralElement (π i)) :=
    Set.toFinite _
  apply e.injective
  -- Transport the finite sum to the product algebra, where the summands are basis vectors.
  rw [finsum_eq_sum _ hsupp, map_sum]
  simp_rw [← centralCharacterFamilyAlgEquiv_symm_basisFun
    (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)]
  ext j
  simp [e]

end CompleteFamily

section Irreducible

variable [CharZero k] [IsAlgClosed k] [Invertible (Nat.card G : k)]
variable (V W : Rep.{u, u, u} k G)
variable [FiniteDimensional k V] [FiniteDimensional k W]

attribute [local instance] Classical.propDecidable

-- Proof sketch: combine `asAlgebraHom_center_eq_centralCharacter_smul_id` with the evaluation of
-- `ω[V.ρ] (characterCentralElement V)` coming from the canonical normalized character-pairing
-- theorem over `[Invertible (Nat.card G : k)]`; the self-pairing of an irreducible character is
-- `1`.
/-- For an irreducible representation over an algebraically closed field in which `|G|` is
invertible, the associated central element acts by the identity on that representation. -/
theorem asAlgebraHom_centralPrimitiveIdempotent_eq_id
    (hV : V.ρ.IsIrreducible) :
    V.ρ.asAlgebraHom (characterCentralElement V : k[G]) = LinearMap.id := by
  letI : V.ρ.IsIrreducible := hV
  -- Route correction: compute the central-character scalar first, then translate it to the action.
  rw [asAlgebraHom_center_eq_centralCharacter_smul_id V.ρ (characterCentralElement V)]
  have hω :=
    centralCharacter_characterCentralElement_eq_ite_of_irreducible
      (X := V) (Y := V) hV hV
  simp at hω
  simp [hω]

-- Proof sketch: the central element attached to `V` acts by the identity on the irreducible
-- representation `V`; since `characterCentralElement V` lies in the center, idempotence follows by
-- comparing the two central actions on the regular representation.
/-- Over an algebraically closed field in which `|G|` is invertible, each irreducible central
primitive idempotent satisfies `p^2 = p`. -/
theorem centralPrimitiveIdempotent_mul_self
    (hV : V.ρ.IsIrreducible) :
    characterCentralElement V * characterCentralElement V = characterCentralElement V := by
  classical
  obtain ⟨ι, _, π, hπ_fd, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_rep_family (k := k) (G := G)
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  obtain ⟨i, hi_fd⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (fun i ↦ FDRep.of (π i).ρ) hπ_complete V.ρ inferInstance
  have hi : Nonempty (V ≅ π i) := by
    rcases hi_fd with ⟨eFD⟩
    exact ⟨(forget₂ (FDRep k G) (Rep k G)).mapIso eFD⟩
  have hV_eq : characterCentralElement V = characterCentralElement (π i) :=
    characterCentralElement_eq_of_nonempty_iso (X := V) (Y := π i) hi
  -- Transport LinearRepresentations_Serre_1977's element to the canonical basis vector and use coordinatewise idempotence.
  rw [hV_eq]
  apply e.injective
  rw [map_mul]
  simp_rw [show characterCentralElement (π i) = e.symm (Pi.basisFun k ι i) by
    symm
    exact centralCharacterFamilyAlgEquiv_symm_basisFun
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) i]
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [Pi.basisFun_apply, hji]

-- Proof sketch: apply the nonisomorphic irreducible character orthogonality relation to the
-- central element attached to `W`; it acts by zero on `V`, so the product vanishes.
/-- Over an algebraically closed field in which `|G|` is invertible, central primitive
idempotents attached to nonisomorphic irreducibles are orthogonal. -/
theorem centralPrimitiveIdempotent_mul_eq_zero_of_not_isomorphic
    (hV : V.ρ.IsIrreducible) (hW : W.ρ.IsIrreducible) (hVW : ¬ Nonempty (V ≅ W)) :
    characterCentralElement V * characterCentralElement W = 0 := by
  classical
  obtain ⟨ι, _, π, hπ_fd, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_rep_family (k := k) (G := G)
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  obtain ⟨i, hi_fd⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (fun i ↦ FDRep.of (π i).ρ) hπ_complete V.ρ inferInstance
  obtain ⟨j, hj_fd⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (fun i ↦ FDRep.of (π i).ρ) hπ_complete W.ρ inferInstance
  have hi : Nonempty (V ≅ π i) := by
    rcases hi_fd with ⟨eFD⟩
    exact ⟨(forget₂ (FDRep k G) (Rep k G)).mapIso eFD⟩
  have hj : Nonempty (W ≅ π j) := by
    rcases hj_fd with ⟨eFD⟩
    exact ⟨(forget₂ (FDRep k G) (Rep k G)).mapIso eFD⟩
  have hij : i ≠ j := by
    intro hij_eq
    subst hij_eq
    rcases hi with ⟨eV⟩
    rcases hj with ⟨eW⟩
    exact hVW ⟨eV.trans eW.symm⟩
  have hV_eq : characterCentralElement V = characterCentralElement (π i) :=
    characterCentralElement_eq_of_nonempty_iso (X := V) (Y := π i) hi
  have hW_eq : characterCentralElement W = characterCentralElement (π j) :=
    characterCentralElement_eq_of_nonempty_iso (X := W) (Y := π j) hj
  -- Transport both factors to distinct coordinate basis vectors and multiply pointwise.
  rw [hV_eq, hW_eq]
  apply e.injective
  rw [map_mul, map_zero]
  simp_rw [show characterCentralElement (π i) = e.symm (Pi.basisFun k ι i) by
    symm
    exact centralCharacterFamilyAlgEquiv_symm_basisFun
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) i]
  simp_rw [show characterCentralElement (π j) = e.symm (Pi.basisFun k ι j) by
    symm
    exact centralCharacterFamilyAlgEquiv_symm_basisFun
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) j]
  ext x
  by_cases hxi : x = i
  · subst hxi
    simp [Pi.basisFun_apply, hij]
  · by_cases hxj : x = j
    · subst hxj
      simp [Pi.basisFun_apply, hij]
    · simp [Pi.basisFun_apply, hxi, hxj]

-- Proof sketch: expand `characterCentralElement W` and identify the resulting scalar with the
-- normalized pairing of the irreducible characters of `V` and `W`; the canonical owner theorems
-- for that pairing give `1` on an isomorphism class and `0` otherwise.
/-- The central character of an irreducible representation takes the central element of `W` to `1`
on its own isomorphism class and to `0` on all other irreducible classes. -/
theorem centralCharacter_centralPrimitiveIdempotent
    (hV : V.ρ.IsIrreducible) (hW : W.ρ.IsIrreducible) :
    ω[V.ρ] (characterCentralElement W) =
      if Nonempty (V ≅ W) then 1 else 0 := by
  -- This is exactly the character-orthogonality computation proved above.
  simpa using
    centralCharacter_characterCentralElement_eq_ite_of_irreducible
      (X := V) (Y := W) hV hW

end Irreducible

end

end

end Representation
