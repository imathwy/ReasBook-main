import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Isotypic
import Serre.Chap01.Theorem_1_1_4_2
import Serre.Chap02.CompleteIrreducibleFamily
import Serre.Chap02.Theorem_2_2_3_5
import Serre.Chap02.Corollary_2_2_4_2
import Serre.Chap02.Proposition_2_2_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped MonoidAlgebra
open scoped Representation
open CategoryTheory
open DirectSum

universe u v w x

namespace Representation

noncomputable section

section

variable {K : Type u} [Field K]
variable {G : Type u} [Monoid G]

/-- Helper for Corollary 2-2.4-3: the character of a finite internal decomposition is the sum of
the characters of the summands. -/
private theorem character_eq_sum_of_internal_family
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (ρ : Representation K G V) (σ : κ → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i : κ, ((σ i).toRepresentation).character := by
  ext g
  simpa [Representation.character] using
    LinearMap.trace_eq_sum_trace_restrict hinternal
      (fun i ↦ (σ i).apply_mem_toSubmodule g)

end

section

variable {K : Type u} [Field K]
variable {G : Type u} [Monoid G]
variable {ι : Type v}

/-- Canonical `Rep`-to-`FDRep` bridge: pairwise nonisomorphism of a `Rep`-valued family remains
pairwise nonisomorphism after passing to the finite-dimensional owner `FDRep`. -/
theorem pairwiseNonisomorphic_fdrep_of_rep
    (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π) :
    PairwiseNonisomorphic (fun i ↦ FDRep.of (π i).ρ) := by
  intro i j hij hij_iso
  apply hπ_pairwise hij
  rcases hij_iso with ⟨e⟩
  exact ⟨(forget₂ (FDRep K G) (Rep K G)).mapIso e⟩

end

section

variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v}
variable {K : Type u} [Field K]

omit [Group G] [Finite G] in
private abbrev IsIrreducibleLeftRegularSummand
    [IsAlgClosed K] [NeZero (Nat.card G : K)]
    (σ : Subrepresentation (leftRegular K G)) : Prop :=
  let _ : AddCommGroup σ.toSubmodule := inferInstance
  Representation.IsIrreducible σ.toRepresentation

/-- Helper for Corollary 2-2.4-3: the group ring `K[G]` attached to the ambient finite group. -/
private abbrev GroupRing : Type u := MonoidAlgebra K G

/-- Helper for Corollary 2-2.4-3: the semisimple Jacobson quotient of the group ring. -/
private abbrev GroupRingSemisimpleQuotient : Type u :=
  GroupRing (K := K) (G := G) ⧸ Ring.jacobson (GroupRing (K := K) (G := G))


omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: completeness makes every family member irreducible as a
representation. -/
private theorem isIrreducible_of_complete_family_member
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    Representation.IsIrreducible (π i).ρ := by
  -- Move from the owner-level `Simple` structure in `FDRep` back to irreducibility of the
  -- underlying representation.
  letI : Simple (π i) := hπ_complete.isSimple i
  exact FDRep.isIrreducible_of_simple (π i)

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: completeness already supplies the owner-level simplicity
witness for each family member. -/
private theorem simple_of_complete_family_member
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    Simple (π i) := by
  exact hπ_complete.isSimple i

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: pairwise nonisomorphism of the `FDRep` family already forbids
equivalences of the underlying representations at distinct indices. -/
private theorem not_nonempty_equiv_of_pairwiseNonisomorphic
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    {i j : ι} (hij : i ≠ j) :
    ¬ Nonempty (Representation.Equiv (π i).ρ (π j).ρ) := by
  -- Any representation equivalence upgrades to an owner-level `FDRep` isomorphism.
  intro hij_equiv
  exact hπ_pairwise hij ⟨hij_equiv.some.toFDRepIso⟩

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: a `K[G]`-linear equivalence of owner modules upgrades to an
equivalence of the underlying representations. -/
private theorem nonempty_equiv_of_nonempty_moduleLinearEquiv
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type x} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (h : Nonempty
      (Representation.asModule ρ ≃ₗ[MonoidAlgebra K G] Representation.asModule σ)) :
    Nonempty (Representation.Equiv ρ σ) := by
  rcases h with ⟨e⟩
  -- Rewrite `K[G]`-linearity on the generators `of g` as the intertwining relation for `ρ` and
  -- `σ`.
  refine ⟨Representation.Equiv.mk (e.restrictScalars K) ?_⟩
  intro g
  ext v
  simpa [MonoidAlgebra.of, Representation.single_smul] using
    e.map_smulₛₗ (MonoidAlgebra.of K G g) v

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: a `K[G]`-linear equivalence between the owner-module views of two
representations upgrades to a representation equivalence. -/
private theorem nonempty_equiv_of_nonempty_asModuleLinearEquiv
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type x} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (h : Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra K G] σ.asModule)) :
    Nonempty (Representation.Equiv ρ σ) := by
  rcases h with ⟨e⟩
  refine ⟨Representation.Equiv.mk
    (ρ.asModuleEquiv.symm.trans ((e.restrictScalars K).trans σ.asModuleEquiv)) ?_⟩
  intro g
  ext v
  calc
    σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v)))
        = σ.asModuleEquiv (e (MonoidAlgebra.of K G g • ρ.asModuleEquiv.symm v)) := by
            rw [ρ.asModuleEquiv_symm_map_rho]
    _ = σ.asModuleEquiv (MonoidAlgebra.of K G g • e (ρ.asModuleEquiv.symm v)) := by
          rw [e.map_smul]
    _ = σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v))) := by
          simpa using
            σ.asModuleEquiv_map_smul (MonoidAlgebra.of K G g) (e (ρ.asModuleEquiv.symm v))

/-- Helper for Corollary 2-2.4-3: for a finite group, the group ring `K[G]` is Artinian. -/
private theorem groupRing_isArtinian :
    IsArtinianRing (GroupRing (K := K) (G := G)) := by
  letI : Module.Finite K (GroupRing (K := K) (G := G)) := inferInstance
  exact IsArtinianRing.of_finite K (GroupRing (K := K) (G := G))

/-- Helper for Corollary 2-2.4-3: the Jacobson quotient of `K[G]` is semisimple because the group
ring is Artinian. -/
private theorem groupRingSemisimpleQuotient_isSemisimple :
    IsSemisimpleRing (GroupRingSemisimpleQuotient (K := K) (G := G)) := by
  -- The Jacobson quotient is still finite-dimensional over `K`, hence Artinian.
  let _ : Module.Finite K (GroupRingSemisimpleQuotient (K := K) (G := G)) := inferInstance
  let _ : IsArtinianRing (GroupRingSemisimpleQuotient (K := K) (G := G)) :=
    IsArtinianRing.of_finite K (GroupRingSemisimpleQuotient (K := K) (G := G))
  -- An Artinian ring is semisimple exactly when its Jacobson radical vanishes.
  exact
    (IsArtinianRing.isSemisimpleRing_iff_jacobson
      (R := GroupRingSemisimpleQuotient (K := K) (G := G))).2 <| by
      simpa [GroupRingSemisimpleQuotient, GroupRing] using
        (Ring.jacobson_quotient_jacobson (R := GroupRing (K := K) (G := G)))

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: a linear equivalence over the Jacobson quotient can be read as a
`K[G]`-linear equivalence once the Jacobson radical acts trivially on both modules. -/
private theorem nonempty_moduleLinearEquiv_of_nonempty_semisimpleQuotientLinearEquiv
    {V : Type w} [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    {W : Type x} [AddCommGroup W] [Module (MonoidAlgebra K G) W]
    (hV : Ring.jacobson (MonoidAlgebra K G) ≤
      Module.annihilator (MonoidAlgebra K G) V)
    (hW : Ring.jacobson (MonoidAlgebra K G) ≤
      Module.annihilator (MonoidAlgebra K G) W)
    :
    let _ : Module ((MonoidAlgebra K G) ⧸
      Module.annihilator (MonoidAlgebra K G) V) V :=
        Module.quotientAnnihilator (R := MonoidAlgebra K G) (M := V)
    let _ : Module ((MonoidAlgebra K G) ⧸
      Module.annihilator (MonoidAlgebra K G) W) W :=
        Module.quotientAnnihilator (R := MonoidAlgebra K G) (M := W)
    let _ : Module ((MonoidAlgebra K G) ⧸ Ring.jacobson (MonoidAlgebra K G)) V :=
        Module.compHom V (Ideal.Quotient.factor hV)
    let _ : Module ((MonoidAlgebra K G) ⧸ Ring.jacobson (MonoidAlgebra K G)) W :=
        Module.compHom W (Ideal.Quotient.factor hW)
    Nonempty (V ≃ₗ[(MonoidAlgebra K G) ⧸ Ring.jacobson (MonoidAlgebra K G)] W) →
      Nonempty (V ≃ₗ[MonoidAlgebra K G] W) := by
  intro _ _ _ _ h
  rcases h with ⟨e⟩
  -- Rewrite `K[G]`-scalar multiplication through the quotient action and keep the same
  -- underlying bijection.
  refine ⟨{
    toLinearMap := {
      toFun := fun x ↦ e x
      map_add' := e.map_add
      map_smul' := ?_
    }
    invFun := fun y ↦ e.symm y
    left_inv := e.left_inv
    right_inv := e.right_inv
  }⟩
  intro r x
  change e ((Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra K G)) r) • x) =
    (Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra K G)) r) • e x
  exact e.map_smul (Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra K G)) r) x

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: simplicity transports across a surjective ring homomorphism
when we compare the two scalar actions by the identity semilinear map. -/
private theorem isSimpleModule_of_ringHom_surjective
    {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [Module A M]
    (q : R →+* A) (hq : Function.Surjective q)
    (hM : let _ : Module R M := Module.compHom M q
      IsSimpleModule R M) :
    IsSimpleModule A M := by
  let _ : Module R M := Module.compHom M q
  letI : RingHomSurjective q := ⟨hq⟩
  let l : M →ₛₗ[q] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hbij : Function.Bijective l := by
    constructor
    · intro x y hxy
      exact hxy
    · intro x
      exact ⟨x, rfl⟩
  -- The identity semilinear map identifies the restricted and descended module structures.
  exact (l.isSimpleModule_iff_of_bijective hbij).mp hM

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: every member of a complete irreducible family is nontrivial. -/
private theorem complete_family_member_nontrivial
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    Nontrivial (π i) := by
  -- A simple object cannot be the zero object, so its underlying carrier is nontrivial.
  let _ : Simple (π i) := hπ_complete.isSimple i
  by_contra htrivial
  let _ : Subsingleton (π i) := not_nontrivial_iff_subsingleton.mp htrivial
  have hzero : (𝟙 (π i) : π i ⟶ π i) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  exact CategoryTheory.id_nonzero (π i) hzero

omit [Finite G] in
/-- Helper for Corollary 2-2.4-3: every member of a complete irreducible family has positive
degree. -/
private theorem complete_family_member_finrank_pos
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    0 < Module.finrank K (π i) := by
  -- Once nontriviality is known, positivity of the finite-dimensional degree is immediate.
  let _ : Nontrivial (π i) := complete_family_member_nontrivial π hπ_complete i
  exact Module.finrank_pos

/-- For a finite group, a complete pairwise nonisomorphic irreducible family has only finitely
many indices. -/
theorem IsCompleteIrreducibleFamily.finite_index
    [IsAlgClosed K] [NeZero (Nat.card G : K)]
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π) : Finite ι := by
  classical
  -- Route correction: work directly with a finite irreducible decomposition of `leftRegular`,
  -- then inject the complete family into its finite set of summand classes.
  obtain ⟨(κ : Type v), hκ, σ, hσ_indep, hσ_top, hσ_irr_raw⟩ :=
    exists_isInternal_irreducible_subrepresentations (leftRegular K G)
  letI : Fintype κ := hκ
  letI : DecidableEq κ := Classical.decEq κ
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  have hσ_irr : ∀ j, IsIrreducibleLeftRegularSummand (σ j) := by
    -- Repackage the irreducibility hypothesis in the form expected by the multiplicity theorem.
    intro j
    let _ : AddCommGroup (σ j).toSubmodule := inferInstance
    simpa [IsIrreducibleLeftRegularSummand] using hσ_irr_raw j
  have hexists (i : ι) :
      ∃ j : κ, Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) := by
    -- The multiplicity of `π i` inside `leftRegular` is its degree, so positivity yields a
    -- concrete summand with the required isomorphism type.
    have hπi_irreducible : Representation.IsIrreducible ((π i).ρ) :=
      isIrreducible_of_complete_family_member π hπ_complete i
    have hmult :
        Nat.card { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } =
          Module.finrank K (π i) := by
      exact
        (leftRegular_irreducible_multiplicity_eq_finrank
          σ hinternal
          (fun j ↦ by
            let _ : AddCommGroup (σ j).toSubmodule := inferInstance
            simpa [IsIrreducibleLeftRegularSummand] using hσ_irr j)
          (π i).ρ hπi_irreducible :
            Nat.card { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } =
              Module.finrank K (π i))
    have hcard_pos :
        0 < Nat.card
          { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } := by
      rw [hmult]
      exact complete_family_member_finrank_pos π hπ_complete i
    rcases Nat.card_pos_iff.mp hcard_pos with ⟨⟨j, hj⟩⟩
    exact ⟨j, hj⟩
  let pick : ι → κ := fun i ↦
    Classical.choose (hexists i)
  have hpick (i : ι) :
      Nonempty (Representation.Equiv ((σ (pick i)).toRepresentation) ((π i).ρ)) := by
    exact Classical.choose_spec (hexists i)
  have hpick_injective : Function.Injective pick := by
    -- Equal chosen summands would identify two family members, contradicting pairwise
    -- nonisomorphism.
    intro i i' hp
    by_contra hii
    have hi :
        Nonempty (Representation.Equiv ((σ (pick i)).toRepresentation) ((π i).ρ)) :=
      hpick i
    have hi_to_i' :
        Nonempty (Representation.Equiv ((σ (pick i')).toRepresentation) ((π i).ρ)) := by
      have hprop :
          Nonempty (Representation.Equiv ((σ (pick i)).toRepresentation) ((π i).ρ)) =
            Nonempty (Representation.Equiv ((σ (pick i')).toRepresentation) ((π i).ρ)) := by
        simpa using
          congrArg
            (fun k : κ ↦
              Nonempty (Representation.Equiv ((σ k).toRepresentation) ((π i).ρ)))
            hp
      exact hprop.mp hi
    rcases hi_to_i' with ⟨ei⟩
    rcases hpick i' with ⟨ei'⟩
    exact
      (not_nonempty_equiv_of_pairwiseNonisomorphic π hπ_pairwise hii)
        ⟨ei.symm.trans ei'⟩
  exact Finite.of_injective pick hpick_injective

section Rep

/-- A complete irreducible family of finite-dimensional representations indexed in `Rep K G`
inherits finiteness of the index set by viewing it through the canonical bridge `FDRep.of`. -/
theorem IsCompleteIrreducibleFamily.finite_index_of_rep (π : ι → Rep K G)
    [IsAlgClosed K] [NeZero (Nat.card G : K)]
    [∀ i, FiniteDimensional K (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_pairwise : PairwiseNonisomorphic π) : Finite ι := by
  exact IsCompleteIrreducibleFamily.finite_index
    (fun i ↦ FDRep.of (π i).ρ)
    hπ_complete
    (pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise)

end Rep

section

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v}

/- Corollary 2-2.4-3 (1) is the canonical owner theorem
`Representation.sum_sq_degree_eq_card_of_complete_irreducible_family`; the finite index set
needed for the summation surface is supplied downstream by
`IsCompleteIrreducibleFamily.finite_index`. -/
#check Representation.sum_sq_degree_eq_card_of_complete_irreducible_family

end

section

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v}

section CompleteFamily

variable (π : ι → FDRep K G)

/-- Helper for Corollary 2-2.4-3: the regular character is the degree-weighted sum of the
characters in a complete pairwise nonisomorphic irreducible family. -/
  private theorem leftRegular_character_eq_sum_degree_mul_character_of_complete_irreducible_family
    [NeZero (Nat.card G : K)] [Finite ι] [Fintype ι]
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (s : G) :
    (leftRegular K G).character s =
      ∑ i : ι, (Module.finrank K (π i) : K) * (π i).character s := by
  classical
  let _ : FiniteDimensional K (G →₀ K) := by infer_instance
  obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type v) (_ : Fintype κ) (σ : κ → Subrepresentation (leftRegular K G)),
        iSupIndep (fun j ↦ (σ j).toSubmodule) ∧
          (⨆ j, (σ j).toSubmodule) = ⊤ ∧
          ∀ j, IsIrreducibleLeftRegularSummand (σ j) := by
    obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr_raw⟩ :=
      exists_isInternal_irreducible_subrepresentations (leftRegular K G)
    refine ⟨κ, hκ, σ, hσ_indep, ?_⟩
    refine ⟨hσ_top, ?_⟩
    intro j
    simpa using hσ_irr_raw j
  letI : Fintype κ := hκ
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦
      Nonempty (Representation.Equiv (σ j).toRepresentation (π i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let χπ : ι → G → K := fun i ↦ Representation.character ((π i).ρ)
  let χσ : κ → K := fun j ↦
    LinearMap.trace K (σ j).toSubmodule ((σ j).toRepresentation s)
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    exact hπ_pairwise hii ⟨(e.symm.trans e').toFDRepIso⟩
  have hS_card (i : ι) : (S i).card = Module.finrank K (π i) := by
    have hπi_irreducible : Representation.IsIrreducible ((π i).ρ) := by
      letI : Simple (π i) := hπ_complete.isSimple i
      exact FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible ((π i).ρ) := hπi_irreducible
    have hcard :
        Fintype.card
            { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } =
          (S i).card := by
      rw [show S i =
          Finset.univ.filter
            (fun j ↦ Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter
          (fun j ↦ Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using
        leftRegular_irreducible_multiplicity_eq_finrank
          σ hinternal
            (fun j ↦ by
              let _ : AddCommGroup (σ j).toSubmodule := inferInstance
              simpa [IsIrreducibleLeftRegularSummand] using hσ_irr j)
            (π i).ρ inferInstance
  have hS_sum (i : ι) :
      Finset.sum (S i) χσ = (Module.finrank K (π i) : K) * χπ i s := by
    calc
      Finset.sum (S i) χσ = Finset.sum (S i) (fun _j ↦ χπ i s) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        let _ : AddCommGroup (σ j).toSubmodule := inferInstance
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        simpa [χπ, χσ] using congrArg (fun χ : G → K ↦ χ s) (Representation.char_iso e)
      _ = (S i).card * χπ i s := by simp
      _ = (Module.finrank K (π i) : K) * χπ i s := by simp [hS_card]
  have hcovered_raw :
      Finset.sum covered χσ = ∑ i : ι, Finset.sum (S i) χσ := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  have hcovered_univ : covered = Finset.univ := by
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      let _ : AddCommGroup (σ j).toSubmodule := inferInstance
      obtain ⟨i, hi⟩ :=
        IsCompleteIrreducibleFamily.exists_iso_of_representation
          π hπ_complete (σ j).toRepresentation <| by
            change IsIrreducibleLeftRegularSummand (σ j)
            exact hσ_irr j
      refine Finset.mem_biUnion.mpr ⟨i, by simp, ?_⟩
      rcases hi with ⟨e⟩
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso e)⟩
  have hsum_sigma : (leftRegular K G).character s = ∑ j : κ, χσ j := by
    have hchar := character_eq_sum_of_internal_family (leftRegular K G) σ hinternal
    simpa [χσ, Representation.character] using congrFun hchar s
  calc
    (leftRegular K G).character s = ∑ j : κ, χσ j := hsum_sigma
    _ = Finset.sum covered χσ := by simp [covered, hcovered_univ]
    _ = ∑ i : ι, Finset.sum (S i) χσ := hcovered_raw
    _ = ∑ i : ι, (Module.finrank K (π i) : K) * χπ i s := by
          refine Finset.sum_congr rfl fun i _ ↦ hS_sum i

-- Proof sketch: identify the regular character with the degree-weighted sum of the irreducible
-- characters using the same multiplicity computation as in part (1), then evaluate at `s ≠ 1`
-- and simplify Proposition `leftRegular_character_eq_ite`.
/-- Corollary 2-2.4-3 (2): if `s ≠ 1`, then the degree-weighted sum of the irreducible characters
of a complete set of pairwise nonisomorphic irreducible representations over an algebraically
closed field of characteristic not dividing `|G|` vanishes at `s`. -/
theorem sum_degree_mul_character_eq_zero_of_ne_one_of_complete_irreducible_family
    [NeZero (Nat.card G : K)]
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (s : G) (hs : s ≠ 1) :
    let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    let _ : Fintype ι := Fintype.ofFinite ι
    ∑ i : ι, (Module.finrank K (π i) : K) * (π i).character s = 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  calc
    ∑ i : ι, (Module.finrank K (π i) : K) * (π i).character s =
        (leftRegular K G).character s := by
          symm
          exact
            leftRegular_character_eq_sum_degree_mul_character_of_complete_irreducible_family
              π hπ_complete hπ_pairwise s
    _ = 0 := leftRegular_character_eq_zero_of_ne_one hs

end CompleteFamily

end

end

end

end Representation
