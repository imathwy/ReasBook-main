import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_3_3.HomFiberBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.CommonOwner
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.EntryBridge
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_5_2
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_5_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap06.Exercise_6_6_1_3

/-!
# Brauer reciprocity adjunction kernel for Proposition 16-16.3-3

This module assembles the three field-theoretic ingredients of Serre's "`e` and `d` are adjoint"
step (Prop. 45 / 16-16.3-3), faithfully over a base of characteristic zero (so that the relevant
group algebra is semisimple and the Schur-weighted pairing computes a `Hom` dimension):

* `finrank_intertwining_eq_simpleBasisCoord_mul_schur` (**L1**): over a field `L` with `L[G]`
  semisimple, the `Hom`-dimension into a simple equals the simple-basis coordinate times the Schur
  endomorphism weight;
* `brauer_homFiber_baseChange_finrank_eq` (**L2**): the field-independent `Hom`-fiber comparison
  over the discrete-valuation ring `A'`, comparing the generic `K'`-fiber of the scalar extension
  of a projective lift with the residue `k'`-fiber against a stable-lattice reduction;
* `finrank_intertwining_restrictScalars_eq_finrank_smul` (**L3**): the residue base change of a
  `Hom` dimension along the finite residue extension `k ⊆ k'`, picking up the degree factor
  `[k':k]`.

These three identities, combined in `Proposition_16_16_3_3.lean` with the already-established
multiplicity readbacks, supply the Brauer adjunction `⟨e(P), z⟩_K = ⟨P, d(z)⟩` underlying the
condition-`(R)` positivity descent.
-/

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

namespace Representation

section L1

/-- Helper for L1: additivity of `Hom(-, S)` over a short exact sequence of finite-dimensional
modules over a semisimple ring `R`, measured by the base-field dimension. Since `R` is semisimple,
`S` is injective, so `Hom(-, S)` is exact; with `L` controlling dimensions this gives additivity. -/
private theorem homToFixed_finrank_add_of_exact_local
    {L : Type u} [Field L]
    {R : Type u} [Ring R] [Algebra L R]
    {S : Type u} [AddCommGroup S] [Module R S]
    [Module L S] [IsScalarTower L R S] [FiniteDimensional L S]
    {N M Q : Type u} [AddCommGroup N] [AddCommGroup M] [AddCommGroup Q]
    [Module R N] [Module R M] [Module R Q]
    [Module L N] [Module L M] [Module L Q]
    [IsScalarTower L R N] [IsScalarTower L R M] [IsScalarTower L R Q]
    [FiniteDimensional L N] [FiniteDimensional L M] [FiniteDimensional L Q]
    (hssM : IsSemisimpleModule R M)
    {f : N →ₗ[R] M} {g : M →ₗ[R] Q}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.finrank L (M →ₗ[R] S) =
      Module.finrank L (N →ₗ[R] S) + Module.finrank L (Q →ₗ[R] S) := by
  classical
  letI := hssM
  let F : (Q →ₗ[R] S) →ₗ[L] (M →ₗ[R] S) := LinearMap.lcomp L S g
  let G' : (M →ₗ[R] S) →ₗ[L] (N →ₗ[R] S) := LinearMap.lcomp L S f
  haveI : FiniteDimensional L (N →ₗ[R] S) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ L R N S L)
      (LinearMap.restrictScalars_injective _)
  haveI : FiniteDimensional L (M →ₗ[R] S) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ L R M S L)
      (LinearMap.restrictScalars_injective _)
  haveI : FiniteDimensional L (Q →ₗ[R] S) :=
    FiniteDimensional.of_injective (LinearMap.restrictScalarsₗ L R Q S L)
      (LinearMap.restrictScalars_injective _)
  have hF_inj : Function.Injective F :=
    LinearMap.lcomp_injective_of_surjective g hg
  have hG'_surj : Function.Surjective G' := by
    intro h
    obtain ⟨φ, hφ⟩ := IsSemisimpleModule.extension_property f hf h
    exact ⟨φ, by simpa [G', LinearMap.lcomp_apply'] using hφ⟩
  have hExact : Function.Exact F G' := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro h hh
      simp only [LinearMap.mem_ker] at hh
      have hhf : h ∘ₗ f = 0 := hh
      have hker_le : LinearMap.ker g ≤ LinearMap.ker h := by
        rw [LinearMap.exact_iff.mp hfg]
        rintro x ⟨n, rfl⟩
        have := LinearMap.congr_fun hhf n
        simpa using this
      let hbar : (M ⧸ LinearMap.ker g) →ₗ[R] S := (LinearMap.ker g).liftQ h hker_le
      let h' : Q →ₗ[R] S := hbar ∘ₗ (g.quotKerEquivOfSurjective hg).symm.toLinearMap
      have hh' : h' ∘ₗ g = h := by
        ext x
        have hmk : (g.quotKerEquivOfSurjective hg).symm (g x) =
            (Submodule.Quotient.mk x : M ⧸ LinearMap.ker g) := by
          apply (g.quotKerEquivOfSurjective hg).injective
          rw [LinearEquiv.apply_symm_apply]
          rfl
        change hbar ((g.quotKerEquivOfSurjective hg).symm (g x)) = h x
        rw [hmk]
        change (LinearMap.ker g).liftQ h hker_le (Submodule.Quotient.mk x) = h x
        rw [Submodule.liftQ_apply]
      exact ⟨h', by simpa [F, LinearMap.lcomp_apply'] using hh'⟩
    · rintro _ ⟨a, rfl⟩
      simp only [LinearMap.mem_ker]
      change G' (F a) = 0
      have hgf0 : g.comp f = 0 := hfg.linearMap_comp_eq_zero
      ext x
      simp only [G', F, LinearMap.lcomp_apply, LinearMap.zero_apply]
      have : (g.comp f) x = 0 := by rw [hgf0]; rfl
      simp only [LinearMap.comp_apply] at this
      rw [this]
      simp
  have hrn := LinearMap.finrank_range_add_finrank_ker G'
  have hrangeG' : Module.finrank L (LinearMap.range G') = Module.finrank L (N →ₗ[R] S) := by
    rw [LinearMap.range_eq_top.mpr hG'_surj]
    exact finrank_top _ _
  have hkerG' : Module.finrank L (LinearMap.ker G') = Module.finrank L (Q →ₗ[R] S) := by
    have hke : LinearMap.ker G' = LinearMap.range F := LinearMap.exact_iff.mp hExact
    rw [hke, ← (LinearEquiv.ofInjective F hF_inj).finrank_eq]
  rw [hrangeG', hkerG'] at hrn
  omega

variable {L : Type u} [Field L] {G : Type u} [Group G] [Finite G] [CharZero L]

/-- Helper for L1: `L[G]` is semisimple when `L` has characteristic zero. -/
private theorem groupAlgebra_isSemisimpleRing_charZero : IsSemisimpleRing L[G] := by
  haveI : CharP L 0 := CharP.ofCharZero L
  have hcard : 1 ≤ Nat.card G := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hndvd : ¬ (0 : ℕ) ∣ Nat.card G := by
    simp only [Nat.zero_dvd]
    omega
  exact group_algebra_isSemisimpleRing_of_char_not_dvd_group_order
    (k := L) (G := G) (p := 0) hndvd

set_option backward.isDefEq.respectTransparency false in
/-- Helper for L1: the `L`-dimension of `Hom(-, S)` into a fixed finite-dimensional representation
is additive along a short exact sequence of finite-dimensional representations, because `L[G]` is
semisimple. -/
private theorem homToFixed_intertwining_finrank_add_of_shortExact_local
    (S : FDRep L G) (T : ShortComplex (FDRep L G)) (hT : T.ShortExact) :
    Module.finrank L (Representation.IntertwiningMap T.X₂.ρ S.ρ) =
      Module.finrank L (Representation.IntertwiningMap T.X₁.ρ S.ρ) +
        Module.finrank L (Representation.IntertwiningMap T.X₃.ρ S.ρ) := by
  letI iSmodG : Module L[G] (Representation.asModule S.ρ) := inferInstance
  letI iSmod : Module L (Representation.asModule S.ρ) := representation_asModuleModule S.ρ
  letI iSst : IsScalarTower L L[G] (Representation.asModule S.ρ) :=
    representation_asModule_isScalarTower S.ρ
  haveI iSfin : @FiniteDimensional L (Representation.asModule S.ρ) _ _ iSmod :=
    inferInstanceAs (FiniteDimensional L S.V)
  haveI iSsmc : SMulCommClass L[G] L (Representation.asModule S.ρ) :=
    IsScalarTower.to_smulCommClass' (R := L) (A := L[G]) (M := Representation.asModule S.ρ)
  letI : Module L[G] (Representation.asModule T.X₁.ρ) := inferInstance
  letI : Module L[G] (Representation.asModule T.X₂.ρ) := inferInstance
  letI : Module L[G] (Representation.asModule T.X₃.ρ) := inferInstance
  letI : Module L (Representation.asModule T.X₁.ρ) := representation_asModuleModule T.X₁.ρ
  letI : Module L (Representation.asModule T.X₂.ρ) := representation_asModuleModule T.X₂.ρ
  letI : Module L (Representation.asModule T.X₃.ρ) := representation_asModuleModule T.X₃.ρ
  have hbridge₁ :
      Module.finrank L (Representation.IntertwiningMap T.X₁.ρ S.ρ) =
        Module.finrank L (Representation.asModule T.X₁.ρ →ₗ[L[G]] Representation.asModule S.ρ) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := T.X₁.ρ) (σ := S.ρ)).finrank_eq
  have hbridge₂ :
      Module.finrank L (Representation.IntertwiningMap T.X₂.ρ S.ρ) =
        Module.finrank L (Representation.asModule T.X₂.ρ →ₗ[L[G]] Representation.asModule S.ρ) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := T.X₂.ρ) (σ := S.ρ)).finrank_eq
  have hbridge₃ :
      Module.finrank L (Representation.IntertwiningMap T.X₃.ρ S.ρ) =
        Module.finrank L (Representation.asModule T.X₃.ρ →ₗ[L[G]] Representation.asModule S.ρ) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := T.X₃.ρ) (σ := S.ρ)).finrank_eq
  have hssM₂ : IsSemisimpleModule L[G] (Representation.asModule T.X₂.ρ) := by
    haveI : IsSemisimpleRing L[G] := groupAlgebra_isSemisimpleRing_charZero (L := L) (G := G)
    infer_instance
  rw [hbridge₂, hbridge₁, hbridge₃]
  let ρ₁ : Representation L G T.X₁ := T.X₁.ρ
  let ρ₂ : Representation L G T.X₂ := T.X₂.ρ
  let ρ₃ : Representation L G T.X₃ := T.X₃.ρ
  letI : Module L[G] T.X₁ := by simpa using (inferInstance : Module L[G] ρ₁.asModule)
  letI : Module L[G] T.X₂ := by simpa using (inferInstance : Module L[G] ρ₂.asModule)
  letI : Module L[G] T.X₃ := by simpa using (inferInstance : Module L[G] ρ₃.asModule)
  letI : IsScalarTower L L[G] T.X₁ := by
    simpa using (inferInstance : IsScalarTower L L[G] ρ₁.asModule)
  letI : IsScalarTower L L[G] T.X₂ := by
    simpa using (inferInstance : IsScalarTower L L[G] ρ₂.asModule)
  letI : IsScalarTower L L[G] T.X₃ := by
    simpa using (inferInstance : IsScalarTower L L[G] ρ₃.asModule)
  let F : FDRep L G ⥤ ModuleCat L[G] :=
    forget₂ (FDRep L G) (Rep L G) ⋙ Rep.toModuleMonoidAlgebra
  let U : ShortComplex (ModuleCat L[G]) := T.map F
  have hU : U.ShortExact := hT.map_of_exact F
  let f : T.X₁ →ₗ[L[G]] T.X₂ := by simpa [U, F] using U.f.hom
  let g : T.X₂ →ₗ[L[G]] T.X₃ := by simpa [U, F] using U.g.hom
  have hf : Function.Injective f := by simpa [f] using hU.moduleCat_injective_f
  have hg : Function.Surjective g := by simpa [g] using hU.moduleCat_surjective_g
  have hfg : Function.Exact f g := by
    simpa [f, g] using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact
  haveI : FiniteDimensional L T.X₁ := inferInstanceAs (FiniteDimensional L T.X₁.V)
  haveI : FiniteDimensional L T.X₂ := inferInstanceAs (FiniteDimensional L T.X₂.V)
  haveI : FiniteDimensional L T.X₃ := inferInstanceAs (FiniteDimensional L T.X₃.V)
  exact homToFixed_finrank_add_of_exact_local
      (R := L[G]) (S := Representation.asModule S.ρ)
      (N := Representation.asModule T.X₁.ρ) (M := Representation.asModule T.X₂.ρ)
      (Q := Representation.asModule T.X₃.ρ) hssM₂ hf hg hfg

omit [Finite G] [CharZero L] in
/-- Helper for L1: nonisomorphic simple representations have no nonzero intertwiners (Schur over any
field), so their intertwining space has dimension zero. -/
private theorem simpleIntertwining_finrank_eq_zero_of_ne_local
    {ι : Type*}
    (π : ι → FDRep L G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {i j : ι} (hij : i ≠ j) :
    Module.finrank L (Representation.IntertwiningMap (π i).ρ (π j).ρ) = 0 := by
  letI : Simple (π i) := hπ_complete.isSimple i
  letI : Simple (π j) := hπ_complete.isSimple j
  letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
  letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
  have hzero : ∀ f : Representation.IntertwiningMap (π i).ρ (π j).ρ, f = 0 := by
    intro f
    by_contra hf
    have hbij : Function.Bijective f :=
      (Representation.IsIrreducible.bijective_or_eq_zero
        (ρ := (π i).ρ) (σ := (π j).ρ) f).resolve_right hf
    have hIso : Nonempty (π i ≅ π j) := ⟨(f.ofBijective hbij).toFDRepIso⟩
    exact (hπ_pairwise hij) hIso
  have hSub : Subsingleton (Representation.IntertwiningMap (π i).ρ (π j).ρ) :=
    ⟨fun f g ↦ by rw [hzero f, hzero g]⟩
  exact Module.finrank_eq_zero_of_subsingleton
    (R := L) (M := Representation.IntertwiningMap (π i).ρ (π j).ρ)

/-- Helper for L1: the additive functional on the free abelian group of finite-dimensional
representations sending `[σ]` to `dim_L Hom(σ, S)`. -/
private noncomputable abbrev homToFixedFinrankLift_local (S : FDRep L G) :
    FreeAbelianGroup (FDRep L G) →+ ℤ :=
  FreeAbelianGroup.lift fun σ ↦
    (Module.finrank L (Representation.IntertwiningMap σ.ρ S.ρ) : ℤ)

/-- Helper for L1: the `dim_L Hom(-, S)` lift vanishes on the defining Grothendieck relations,
because `Hom(-, S)` is exact (`L[G]` semisimple), so its dimension is additive along short exact
sequences. -/
private theorem finiteRepGrothendieckRelations_le_homToFixedFinrankLift_ker_local (S : FDRep L G) :
    finiteRepGrothendieckRelations L G ≤ (homToFixedFinrankLift_local (L := L) (G := G) S).ker := by
  refine (AddSubgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with ⟨⟨T, hT⟩, rfl⟩
  have hadd :
      Module.finrank L (Representation.IntertwiningMap T.X₂.ρ S.ρ) =
        Module.finrank L (Representation.IntertwiningMap T.X₁.ρ S.ρ) +
          Module.finrank L (Representation.IntertwiningMap T.X₃.ρ S.ρ) :=
    homToFixed_intertwining_finrank_add_of_shortExact_local (L := L) (G := G) S T hT
  change homToFixedFinrankLift_local (L := L) (G := G) S
    (FreeAbelianGroup.of T.X₂ - FreeAbelianGroup.of T.X₁ - FreeAbelianGroup.of T.X₃) = 0
  simp only [homToFixedFinrankLift_local, map_sub, FreeAbelianGroup.lift_apply_of]
  rw [hadd]
  push_cast
  ring

/-- Helper for L1: the descended additive functional `R₀[L](G) →+ ℤ`, `[σ] ↦ dim_L Hom(σ, S)`. -/
private noncomputable def homToFixedFinrankHom_local (S : FDRep L G) :
    R₀[L](G) →+ ℤ :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations L G)
    (homToFixedFinrankLift_local (L := L) (G := G) S)
    (finiteRepGrothendieckRelations_le_homToFixedFinrankLift_ker_local (L := L) (G := G) S)

/-- Helper for L1: the descended `Hom(-, S)` functional evaluates on an honest class `[M]₀` as
`dim_L Hom(M, S)`. -/
private theorem homToFixedFinrankHom_apply_class_local (S M : FDRep L G) :
    homToFixedFinrankHom_local (L := L) (G := G) S [M]₀ =
      (Module.finrank L (Representation.IntertwiningMap M.ρ S.ρ) : ℤ) := by
  simp [homToFixedFinrankHom_local, finiteRepGrothendieckClass, homToFixedFinrankLift_local]

/-- **L1** (Helper for Proposition 16-16.3-3): Schur readback over a semisimple group algebra.  For
a complete pairwise-nonisomorphic family of simple finite-dimensional `L`-representations of `G`
(with `L` of characteristic zero, so `L[G]` is semisimple), the dimension of the intertwining space
`Hom(V, πK_j)` equals the `j`-th simple-basis coordinate of `[V]₀` times the Schur endomorphism
weight `dim_L End(πK_j)`. -/
theorem finrank_intertwining_eq_simpleBasisCoord_mul_schur
    {ι : Type*}
    (πK : ι → FDRep L G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (j : ι) (V : FDRep L G) :
    (Module.finrank L (Representation.IntertwiningMap V.ρ (πK j).ρ) : ℤ) =
      (simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete).repr
          (finiteRepGrothendieckClass L G V) j
        * (Module.finrank L (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ) := by
  classical
  let bK := simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  let weight : ℤ := (Module.finrank L (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ)
  let Φ : R₀[L](G) →ₗ[ℤ] ℤ := (homToFixedFinrankHom_local (L := L) (G := G) (πK j)).toIntLinearMap
  let Ψ : R₀[L](G) →ₗ[ℤ] ℤ :=
    weight • { toFun := fun x ↦ bK.repr x j
               map_add' := by intro x y; simp
               map_smul' := by intro a x; simp : R₀[L](G) →ₗ[ℤ] ℤ }
  have hmaps : Φ = Ψ := by
    apply bK.ext
    intro i
    have hΦclass :
        Φ (bK i) = (Module.finrank L (Representation.IntertwiningMap (πK i).ρ (πK j).ρ) : ℤ) := by
      rw [show bK i = [πK i]₀ from
        simple_finiteRep_classes_basis_of_complete_family_apply πK hπK_pairwise hπK_complete i]
      exact homToFixedFinrankHom_apply_class_local (L := L) (G := G) (πK j) (πK i)
    have hcoord : bK.repr (bK i) j = (if i = j then 1 else 0 : ℤ) := by
      rw [bK.repr_self i]
      simp [Finsupp.single_apply]
    by_cases hij : i = j
    · subst i
      calc
        Φ (bK j)
            = (Module.finrank L (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) : ℤ) := hΦclass
        _ = Ψ (bK j) := by
              simp only [Ψ, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
              rw [hcoord]
              simp [weight]
    · have hsimpleZero :
          Module.finrank L (Representation.IntertwiningMap (πK i).ρ (πK j).ρ) = 0 :=
        simpleIntertwining_finrank_eq_zero_of_ne_local (L := L) (G := G)
          πK hπK_pairwise hπK_complete hij
      calc
        Φ (bK i) = 0 := by rw [hΦclass, hsimpleZero]; rfl
        _ = Ψ (bK i) := by
              simp only [Ψ, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
              rw [hcoord]
              simp [hij]
  have hV : Φ [V]₀ = Ψ [V]₀ := congrArg (fun f : R₀[L](G) →ₗ[ℤ] ℤ ↦ f [V]₀) hmaps
  have hΦV : Φ [V]₀ = (Module.finrank L (Representation.IntertwiningMap V.ρ (πK j).ρ) : ℤ) := by
    change (homToFixedFinrankHom_local (L := L) (G := G) (πK j)) [V]₀ = _
    exact homToFixedFinrankHom_apply_class_local (L := L) (G := G) (πK j) V
  rw [hΦV] at hV
  simp only [Ψ, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at hV
  rw [hV]
  ring

end L1

section L3

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable {G : Type u} [Group G]
variable {P : Type u} [AddCommGroup P] [Module k P]
variable {N : Type u} [AddCommGroup N] [Module k' N] [Module k N] [IsScalarTower k k' N]

/-- Helper: the scalar-extended representation evaluated at `g` is the base change of `ρ g`. -/
private theorem scalarExtension_apply_eq_baseChange
    (ρ : Representation k G P) (g : G) :
    (Representation.scalarExtension (k := k') ρ) g = LinearMap.baseChange k' (ρ g) := by
  simp [Representation.scalarExtension, Module.End.baseChangeHom, LinearMap.baseChangeHom_apply]

/-- Forward direction: base change of an intertwiner `ρ → restrictScalars σ` is an intertwiner
`scalarExtension ρ → σ`. -/
private def baseChangeFwd (ρ : Representation k G P) (σ : Representation k' G N)
    (f : IntertwiningMap ρ (Representation.restrictScalars k σ)) :
    IntertwiningMap (Representation.scalarExtension (k := k') ρ) σ where
  toLinearMap := LinearMap.liftBaseChange k' f.toLinearMap
  isIntertwining' g := by
    refine TensorProduct.AlgebraTensorModule.ext fun c x => ?_
    -- LHS / RHS computed on a pure tensor `c ⊗ x`.
    rw [LinearMap.comp_apply, scalarExtension_apply_eq_baseChange, LinearMap.baseChange_tmul,
      LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, LinearMap.liftBaseChange_tmul]
    -- `f (ρ g x) = (restrictScalars σ) g (f x) = σ g (f x)`, and `σ g` is `k'`-linear.
    have hf := congrFun (congrArg DFunLike.coe (f.isIntertwining' g)) x
    simp only [LinearMap.comp_apply, Representation.restrictScalars_apply] at hf
    rw [hf, map_smul]

/-- Inverse direction: restriction of an intertwiner `scalarExtension ρ → σ` along `1 ⊗ ·` is an
intertwiner `ρ → restrictScalars σ`. -/
private def baseChangeInv (ρ : Representation k G P) (σ : Representation k' G N)
    (g : IntertwiningMap (Representation.scalarExtension (k := k') ρ) σ) :
    IntertwiningMap ρ (Representation.restrictScalars k σ) where
  toLinearMap := (LinearMap.liftBaseChangeEquiv k').symm g.toLinearMap
  isIntertwining' γ := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.liftBaseChangeEquiv_symm_apply,
      Representation.restrictScalars_apply]
    -- `g (1 ⊗ ρ γ x) = g ((scalarExtension ρ) γ (1 ⊗ x)) = σ γ (g (1 ⊗ x))`.
    have hb : ((1 : k') ⊗ₜ[k] (ρ γ x) : k' ⊗[k] P)
        = (Representation.scalarExtension (k := k') ρ) γ ((1 : k') ⊗ₜ[k] x) := by
      rw [scalarExtension_apply_eq_baseChange, LinearMap.baseChange_tmul]
    rw [hb]
    exact congrFun (congrArg DFunLike.coe (g.isIntertwining' γ)) ((1 : k') ⊗ₜ[k] x)

/-- The `k`-module structure on the target intertwiner space obtained by restriction of scalars
along `k → k'`. -/
private instance targetModuleK (ρ : Representation k G P) (σ : Representation k' G N) :
    Module k (IntertwiningMap (Representation.scalarExtension (k := k') ρ) σ) :=
  Module.compHom _ (algebraMap k k')

private instance targetTower (ρ : Representation k G P) (σ : Representation k' G N) :
    IsScalarTower k k' (IntertwiningMap (Representation.scalarExtension (k := k') ρ) σ) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The `k`-linear equivalence between the two intertwiner spaces (extension–restriction
adjunction for the algebra map `k → k'`).  The source carries its `k`-module structure; the target
carries the restriction-of-scalars `k`-module structure from its native `k'`-structure. -/
private def intertwiningBaseChangeEquiv (ρ : Representation k G P) (σ : Representation k' G N) :
    IntertwiningMap ρ (Representation.restrictScalars k σ) ≃ₗ[k]
      IntertwiningMap (Representation.scalarExtension (k := k') ρ) σ where
  toFun := baseChangeFwd ρ σ
  invFun := baseChangeInv ρ σ
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    show (LinearMap.liftBaseChangeEquiv k').symm
        (LinearMap.liftBaseChange k' f.toLinearMap) = f.toLinearMap
    exact (LinearMap.liftBaseChangeEquiv k').symm_apply_apply f.toLinearMap
  right_inv g := by
    apply Representation.IntertwiningMap.ext
    show LinearMap.liftBaseChange k'
        ((LinearMap.liftBaseChangeEquiv k').symm g.toLinearMap) = g.toLinearMap
    exact (LinearMap.liftBaseChangeEquiv k').apply_symm_apply g.toLinearMap
  map_add' f f' := by
    apply Representation.IntertwiningMap.ext
    show LinearMap.liftBaseChange k' (f.toLinearMap + f'.toLinearMap)
        = LinearMap.liftBaseChange k' f.toLinearMap + LinearMap.liftBaseChange k' f'.toLinearMap
    exact map_add (LinearMap.liftBaseChangeEquiv k') f.toLinearMap f'.toLinearMap
  map_smul' a f := by
    apply Representation.IntertwiningMap.ext
    -- LHS `.toLinearMap`: `liftBaseChange (a • f.toLinearMap)`.
    -- RHS `.toLinearMap`: the target `k`-smul is `(algebraMap k k' a) • ·` (native `k'`-smul).
    have hL : (baseChangeFwd ρ σ (a • f)).toLinearMap
        = LinearMap.liftBaseChange k' ((a • f).toLinearMap) := rfl
    have hf : (a • f).toLinearMap = a • f.toLinearMap := rfl
    have hR : (((RingHom.id k) a) • baseChangeFwd ρ σ f).toLinearMap
        = (algebraMap k k' a) • LinearMap.liftBaseChange k' (f.toLinearMap) := by
      change ((algebraMap k k' a) • baseChangeFwd ρ σ f).toLinearMap = _
      rfl
    rw [hL, hf, hR, show (a • f.toLinearMap) = (algebraMap k k' a) • f.toLinearMap by
          rw [algebraMap_smul]]
    exact map_smul (LinearMap.liftBaseChangeEquiv k') (algebraMap k k' a) f.toLinearMap

section Finrank

variable [FiniteDimensional k k']
variable [Finite G]
variable [FiniteDimensional k P]
variable [FiniteDimensional k' N]

set_option linter.unusedSectionVars false in
/-- **L3** (Helper for Proposition 16-16.3-3): residue / finite base change of the intertwiner
dimension: the `k`-dimension of `Hom_{k[G]}(ρ, restrictScalars σ)` equals `[k' : k]` times the
`k'`-dimension of `Hom_{k'[G]}(scalarExtension ρ, σ)`. -/
theorem finrank_intertwining_restrictScalars_eq_finrank_smul
    (ρ : Representation k G P) (σ : Representation k' G N) :
    Module.finrank k
        (IntertwiningMap ρ (Representation.restrictScalars k σ))
      = Module.finrank k k' *
        Module.finrank k'
          (IntertwiningMap (Representation.scalarExtension (k := k') ρ) σ) := by
  -- The intertwiner space over `k'` is finite-dimensional over `k'`.
  haveI : FiniteDimensional k' (k' ⊗[k] P) := Module.Finite.base_change k k' P
  haveI : FiniteDimensional k'
      (IntertwiningMap (Representation.scalarExtension (k := k') ρ) σ) := inferInstance
  -- Step 1: the `k`-linear equivalence identifies the source with the target as `k`-modules.
  rw [LinearEquiv.finrank_eq (intertwiningBaseChangeEquiv ρ σ)]
  -- Step 2: the tower law over `k ⊆ k'` on the target intertwiner space.
  rw [Module.finrank_mul_finrank k k'
    (IntertwiningMap (Representation.scalarExtension (k := k') ρ) σ)]

end Finrank

end L3

/-! ## L2: base-change Brauer reciprocity `Hom`-fiber equality

For a tower of commutative rings `A → B → S` and an `A[G]`-module `M`, the `B[G]`-module
`B ⊗[A] M` (carrying the scalar-extended action) has the property that its further scalar extension
to `S` is equivalent, as an `S`-representation, to the direct scalar extension of `M` to `S`. -/

section GeneralCancel

variable {A : Type u} [CommRing A]
variable {B : Type u} [CommRing B] [Algebra A B]
variable {S : Type u} [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
variable {G : Type u} [Group G]
variable {M : Type u} [AddCommGroup M] [Module A M] [Module A[G] M] [IsScalarTower A A[G] M]

/-- The `B[G]`-module structure on `B ⊗[A] M` via the scalar-extended representation. -/
local instance genBaseChangeModule : Module B[G] (B ⊗[A] M) :=
  let ρ : Representation B G (B ⊗[A] M) :=
    Representation.scalarExtension (show Representation A G M from Representation.ofModule' M)
  Module.compHom _ ρ.asAlgebraHom.toRingHom

/-- The base-change `B[G]`-action on `B ⊗[A] M` is compatible with the `B`-scalar action. -/
local instance genBaseChangeTower : IsScalarTower B B[G] (B ⊗[A] M) := by
  refine IsScalarTower.of_algebraMap_smul fun b x => ?_
  change ((Representation.scalarExtension
      (show Representation A G M from Representation.ofModule' M)).asAlgebraHom
      (algebraMap B B[G] b)) x = b • x
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp

/-- The base-change `B[G]`-action on `B ⊗[A] M` agrees with `monoidAlgebra_of_smul_tmul`. -/
theorem genBaseChange_of_smul_tmul (g : G) (b : B) (x : M) :
    MonoidAlgebra.of B G g • (b ⊗ₜ[A] x : B ⊗[A] M) =
      b ⊗ₜ[A] (MonoidAlgebra.of A G g • x) := by
  let ρ : Representation A G M := Representation.ofModule' M
  let ρB : Representation B G (B ⊗[A] M) := Representation.scalarExtension ρ
  have hsingle :=
    Representation.single_smul (ρ := ρB) (t := (1 : B)) (g := g)
      (v := TensorProduct.mk A B M b x)
  simpa [ρ, ρB, Representation.scalarExtension, Representation.ofModule',
    MonoidAlgebra.of_apply] using hsingle

/-- The underlying `S`-linear cancellation `S ⊗[B] (B ⊗[A] M) ≃ₗ[S] S ⊗[A] M`. -/
def genCancelCarrier : (S ⊗[B] (B ⊗[A] M)) ≃ₗ[S] (S ⊗[A] M) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange A B S S M

@[simp] theorem genCancelCarrier_tmul (s : S) (b : B) (x : M) :
    genCancelCarrier (B := B) (s ⊗ₜ[B] (b ⊗ₜ[A] x)) = (b • s) ⊗ₜ[A] x := by
  simp [genCancelCarrier, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

/-- **General source-side base-change cancellation** as a representation equivalence:
`scalarExtension_{B→S}(ofModule' (B ⊗[A] M)) ≃ scalarExtension_{A→S}(ofModule' M)`. -/
def genCancelEquiv :
    (show Representation S G (S ⊗[B] (B ⊗[A] M)) from
      Representation.scalarExtension (Representation.ofModule' (B ⊗[A] M))).Equiv
        (show Representation S G (S ⊗[A] M) from
          Representation.scalarExtension (Representation.ofModule' M)) := by
  refine Representation.Equiv.mk (genCancelCarrier (B := B)) ?_
  intro g
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
          have hsrc : (Representation.scalarExtension
              (Representation.ofModule' (B ⊗[A] M)) : Representation S G _) g
                (s ⊗ₜ[B] (b ⊗ₜ[A] x))
              = s ⊗ₜ[B] ((MonoidAlgebra.of B G g) • (b ⊗ₜ[A] x)) := by
            change (LinearMap.baseChange S
              ((Representation.ofModule' (B ⊗[A] M) : Representation B G _) g))
                (s ⊗ₜ[B] (b ⊗ₜ[A] x)) = _
            rw [LinearMap.baseChange_tmul]
            rfl
          have htgt : (Representation.scalarExtension
              (Representation.ofModule' M) : Representation S G _) g
                ((b • s) ⊗ₜ[A] x)
              = (b • s) ⊗ₜ[A] ((MonoidAlgebra.of A G g) • x) := by
            change (LinearMap.baseChange S
              ((Representation.ofModule' M : Representation A G _) g))
                ((b • s) ⊗ₜ[A] x) = _
            rw [LinearMap.baseChange_tmul]
            rfl
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [show (genCancelCarrier (B := B)) (s ⊗ₜ[B] (b ⊗ₜ[A] x))
                = genCancelCarrier (B := B) (s ⊗ₜ[B] (b ⊗ₜ[A] x)) from rfl,
            genCancelCarrier_tmul, hsrc, htgt,
            genBaseChange_of_smul_tmul (M := M) g b x, genCancelCarrier_tmul]
      | add z w hz hw =>
          simp only [TensorProduct.tmul_add, map_add, LinearMap.comp_apply,
            LinearEquiv.coe_coe] at *
          rw [hz, hw]
  | add y w hy hw =>
      simp only [LinearMap.comp_apply, map_add, LinearEquiv.coe_coe] at *
      rw [hy, hw]

end GeneralCancel

section BaseChangeHomFiber

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
  [Algebra A A'] [Module.Finite A A'] [IsLocalHom (algebraMap A A')]
variable {G : Type u} [Group G] [Finite G]
variable (Q : FiniteProjectiveGroupAlgebraModule A G)

attribute [local instance] Fintype.ofFinite

/-- The base-changed module `A' ⊗[A] Q.V` carries an `A'[G]`-module structure via the
scalar-extended representation. -/
local instance baseChangeModuleAG' :
    Module A'[G] (A' ⊗[A] Q.V) :=
  let ρ : Representation A' G (A' ⊗[A] Q.V) :=
    Representation.scalarExtension (show Representation A G Q.V from Representation.ofModule' Q.V)
  Module.compHom _ ρ.asAlgebraHom.toRingHom

/-- The base-change `A'[G]`-action is compatible with the `A'`-scalar action. -/
local instance baseChangeTowerAG' :
    IsScalarTower A' A'[G] (A' ⊗[A] Q.V) := by
  refine IsScalarTower.of_algebraMap_smul fun a x => ?_
  change ((Representation.scalarExtension
      (show Representation A G Q.V from Representation.ofModule' Q.V)).asAlgebraHom
      (algebraMap A' A'[G] a)) x = a • x
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp

omit [IsLocalRing A] [HenselianLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsLocalRing A'] [IsDomain A']
  [IsDiscreteValuationRing A'] [Module.Finite A A'] [IsLocalHom (algebraMap A A')] in
/-- Base change carries the averaged conjugation operator on `Q.V` to the tensor of the averaged
conjugation action on vectors (generic version over any `A`-algebra `A'`). -/
theorem baseChange_sumOfConjugates_apply_tmul'
    (u : Module.End A Q.V) (a : A') (x : Q.V) :
    (Module.End.baseChangeHom A A' Q.V u).sumOfConjugates G
      (a ⊗ₜ[A] x) = a ⊗ₜ[A] (u.sumOfConjugates G x) := by
  rw [LinearMap.sumOfConjugates_apply, LinearMap.sumOfConjugates_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [LinearMap.conjugate_apply, LinearMap.conjugate_apply]
  rw [show MonoidAlgebra.single g (1 : A') • (a ⊗ₜ[A] x) =
      a ⊗ₜ[A] (MonoidAlgebra.single g (1 : A) • x) by
      have := monoidAlgebra_of_smul_tmul (Λ := A) (P := Q.V) (κ := A') g a x
      simpa [MonoidAlgebra.of_apply] using this]
  rw [show ((Module.End.baseChangeHom A A' Q.V) u)
      (a ⊗ₜ[A] (MonoidAlgebra.single g (1 : A) • x)) =
      a ⊗ₜ[A] u (MonoidAlgebra.single g (1 : A) • x) by
      simpa [Module.End.baseChangeHom] using
        (LinearMap.baseChange_tmul (f := u) (A := A') a
          (MonoidAlgebra.single g (1 : A) • x))]
  rw [show MonoidAlgebra.single g⁻¹ (1 : A') •
      (a ⊗ₜ[A] u (MonoidAlgebra.single g (1 : A) • x)) =
      MonoidAlgebra.of A' G g⁻¹ •
        (a ⊗ₜ[A] u (MonoidAlgebra.single g (1 : A) • x)) by rfl]
  simpa using
    monoidAlgebra_of_smul_tmul
      (Λ := A) (P := Q.V) (κ := A') g⁻¹ a
      (u (MonoidAlgebra.single g (1 : A) • x))

omit [IsLocalRing A] [HenselianLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsLocalRing A'] [IsDomain A']
  [IsDiscreteValuationRing A'] [Module.Finite A A'] [IsLocalHom (algebraMap A A')] in
/-- Base change carries a global averaging identity to `A' ⊗[A] Q.V`. -/
theorem baseChange_sumOfConjugates_eq_id'
    (u : Module.End A Q.V) (hu : u.sumOfConjugates G = LinearMap.id) :
    (Module.End.baseChangeHom A A' Q.V u).sumOfConjugates G = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      calc
        (Module.End.baseChangeHom A A' Q.V u).sumOfConjugates G (a ⊗ₜ[A] x)
            = a ⊗ₜ[A] (u.sumOfConjugates G x) := by
              simpa using baseChange_sumOfConjugates_apply_tmul' Q u a x
        _ = a ⊗ₜ[A] x := by simp [hu]
  | add z w hz hw => simp [hz, hw]

/-- The base-changed module `A' ⊗[A] Q.V` is projective over `A'[G]`. -/
local instance baseChangeProjectiveAG' :
    Module.Projective A'[G] (A' ⊗[A] Q.V) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module.Finite A Q.V := Q.finite
  -- The underlying `A'`-module is projective (base change of `A`-projective).
  letI : Module.Free A Q.V := Q.free
  haveI hPA' : Module.Projective A' (A' ⊗[A] Q.V) := inferInstance
  -- Extract Serre's averaging endomorphism over `A` and base change it.
  rcases
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := A) (G := G) (P := Q.V)).mp Q.projective with ⟨_, u, hu⟩
  refine
    (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      (Λ := A') (G := G) (P := A' ⊗[A] Q.V)).mpr ?_
  exact ⟨hPA', Module.End.baseChangeHom A A' Q.V u,
    baseChange_sumOfConjugates_eq_id' Q u hu⟩

/-! ### Residue field tower and the source-side residue transport -/

local notation "κ" => IsLocalRing.ResidueField A
local notation "κ'" => IsLocalRing.ResidueField A'

variable [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
  [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
  [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
variable (P : FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)

/-- The `κ[G]`-module structure on `κ ⊗[A] Q.V` (from the scalar-extended representation). -/
local instance residueModuleAG : Module κ[G] (κ ⊗[A] Q.V) :=
  let ρ : Representation κ G (κ ⊗[A] Q.V) :=
    Representation.scalarExtension (show Representation A G Q.V from Representation.ofModule' Q.V)
  Module.compHom _ ρ.asAlgebraHom.toRingHom

local instance residueTowerAG : IsScalarTower κ κ[G] (κ ⊗[A] Q.V) := by
  refine IsScalarTower.of_algebraMap_smul fun a x => ?_
  change ((Representation.scalarExtension
      (show Representation A G Q.V from Representation.ofModule' Q.V)).asAlgebraHom
      (algebraMap κ κ[G] a)) x = a • x
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp

/-- The scalar extension `scalarExtension_{A→κ}(ofModule' Q.V)` is the canonical representation on
the `κ[G]`-module `κ ⊗[A] Q.V`. -/
def residueOfModuleEquiv :
    (show Representation κ G (κ ⊗[A] Q.V) from
      Representation.ofModule' (κ ⊗[A] Q.V)).Equiv
      (show Representation κ G (κ ⊗[A] Q.V) from
        Representation.scalarExtension (Representation.ofModule' Q.V)) := by
  refine Representation.ofModulePrimeEquivOfActionEq
    (show Representation κ G (κ ⊗[A] Q.V) from
      Representation.scalarExtension (Representation.ofModule' Q.V)) ?_
  intro g x
  -- The `of g`-action is, by construction, the scalar-extended representation evaluated at `g`.
  rw [← Representation.asAlgebraHom_single_one
    (ρ := (Representation.scalarExtension
      (show Representation A G Q.V from Representation.ofModule' Q.V))) g]
  rfl

/-- The canonical representation on `P.V` is (definitionally) the underlying representation of
`P.toRep`. -/
def targetResidueOfModuleEquiv :
    (show Representation κ G P.V from Representation.ofModule' P.V).Equiv P.toRep.ρ :=
  Representation.Equiv.refl _

/-- A chosen projective lift identifies the residue scalar extension of `Q`'s owner with the target
residue projective representation `P.toRep.ρ` (the `A`-level reduction step; the residue-field
reduction `κ ⊗[A] Q.V ≅ P.V` is where completeness/Henselianness of `A` is used).  This re-proves
`projectiveLift_residue_scalarExtension_equiv` without its spurious DVR hypotheses on `A`. -/
noncomputable def projectiveLiftResidueEquiv
    (hQP : Nonempty (Q.residueFieldReduction ≅ P)) :
    (show Representation κ G (κ ⊗[A] Q.V) from
      Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv P.toRep.ρ :=
  let ρred : Rep κ G :=
    Rep.of (show Representation κ G (κ ⊗[A] Q.V) from
      Representation.scalarExtension (Representation.ofModule' Q.V))
  let eSrcIso : ρred ≅ Q.residueFieldReduction.toRep := by
    simpa [ρred, FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.toRep] using (Rep.unitIso ρred)
  let elin : Q.residueFieldReduction.V ≃ₗ[κ[G]] P.V :=
    ((finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := κ) (G := G) Q.residueFieldReduction P).1 hQP).some
  let eRedP : Q.residueFieldReduction.toRep ≅ P.toRep :=
    Rep.ofModuleMonoidAlgebra.mapIso elin.toModuleIso
  (Representation.equivOfIso eSrcIso).trans (Representation.equivOfIso eRedP)

/-- **Source-side residue transport.** Identifies `scalarExtension_{A→κ'}(ofModule' Q.V)` with the
carrier representation of the target residue projective `P.scalarExtension κ'`, using the chosen
projective lift `hQP` and base-change cancellation through the residue tower `A → κ → κ'`. -/
def residueChainEquiv
    (hQP : Nonempty (Q.residueFieldReduction ≅ P)) :
    (show Representation κ' G (κ' ⊗[A] Q.V) from
      Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv
      (P.scalarExtension κ').ρ := by
  -- e1 : scalarExtension_{A→κ'}(ofModule' Q.V) ≃ scalarExtension_{κ→κ'}(ofModule'(κ ⊗[A] Q.V)).
  let e1 :
      (show Representation κ' G (κ' ⊗[A] Q.V) from
        Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv
        (show Representation κ' G (κ' ⊗[κ] (κ ⊗[A] Q.V)) from
          Representation.scalarExtension (Representation.ofModule' (κ ⊗[A] Q.V))) :=
    (genCancelEquiv (A := A) (B := κ) (S := κ') (M := Q.V)).symm
  -- eA : scalarExtension_{A→κ}(ofModule' Q.V) ≃ P.toRep.ρ.
  let eA := projectiveLiftResidueEquiv (A := A) (G := G) Q P hQP
  -- ebridge : ofModule'(κ ⊗[A] Q.V) ≃ P.toRep.ρ over κ.
  let ebridge :
      (show Representation κ G (κ ⊗[A] Q.V) from
        Representation.ofModule' (κ ⊗[A] Q.V)).Equiv P.toRep.ρ :=
    (residueOfModuleEquiv (A := A) (G := G) Q).trans eA
  -- e2 : scalarExtension_{κ→κ'}(ofModule'(κ ⊗[A] Q.V)) ≃ scalarExtension_{κ→κ'}(P.toRep.ρ).
  let e2 :
      (show Representation κ' G (κ' ⊗[κ] (κ ⊗[A] Q.V)) from
        Representation.scalarExtension (Representation.ofModule' (κ ⊗[A] Q.V))).Equiv
        (Representation.scalarExtension (k := κ') P.toRep.ρ) :=
    Representation.scalarExtensionEquiv (A := κ) (F := κ') ebridge
  -- e3 : scalarExtension_{κ→κ'}(P.toRep.ρ) ≃ scalarExtension_{κ→κ'}(ofModule' P.V) = (P.scalarExt κ').ρ.
  let e3 :
      (Representation.scalarExtension (k := κ') P.toRep.ρ).Equiv
        (P.scalarExtension κ').ρ :=
    (Representation.scalarExtensionEquiv (A := κ) (F := κ')
      (targetResidueOfModuleEquiv (A := A) (G := G) P)).symm
  exact (e1.trans e2).trans e3

/-- **Full source-side residue transport.** Identifies
`scalarExtension_{A'→κ'}(ofModule' (A' ⊗[A] Q.V))` (the source representation of the residue fiber)
with the carrier representation of the target residue projective `P.scalarExtension κ'`, by first
cancelling the intermediate base change `A → A'` and then applying the residue chain `A → κ → κ'`. -/
def residueFullEquiv
    (hQP : Nonempty (Q.residueFieldReduction ≅ P)) :
    (show Representation κ' G (κ' ⊗[A'] (A' ⊗[A] Q.V)) from
      Representation.scalarExtension (Representation.ofModule' (A' ⊗[A] Q.V))).Equiv
      (P.scalarExtension κ').ρ :=
  (genCancelEquiv (A := A) (B := A') (S := κ') (M := Q.V)).trans
    (residueChainEquiv (A := A) (G := G) Q P hQP)

/-- **Source-side generic transport.** Identifies `scalarExtension_{A'→K'}(ofModule' (A' ⊗[A] Q.V))`
with the carrier representation of the generic projective `Q.scalarExtension K'`, by base-change
cancellation through the tower `A → A' → K'`. -/
def fractionChainEquiv
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsScalarTower A A' K'] :
    (show Representation K' G (K' ⊗[A'] (A' ⊗[A] Q.V)) from
      Representation.scalarExtension (Representation.ofModule' (A' ⊗[A] Q.V))).Equiv
      (Q.scalarExtension K').ρ :=
  (genCancelEquiv (A := A) (B := A') (S := K') (M := Q.V)).trans
    (Representation.finiteProjective_scalarExtension_rep_equiv (A := A) (K := K') Q).some

/-- **L2** — base-change Brauer reciprocity `Hom`-fiber equality.  With a complete local Henselian
base `A`, a module-finite local DVR `A'/A`, a fraction field `K'` of `A'` and the residue extension
`κ → κ'`, a projective `A[G]`-module `Q` with a residue lift `P` over `κ`, and a stable `A'`-lattice
`L` in a `K'`-representation `X`, the `K'`-dimension of the generic intertwiner space agrees with
the `κ'`-dimension of the residue intertwiner space.  Both compute the `A'`-rank of the common Hom
owner `(A' ⊗[A] Q.V) →ₗ[A'[G]] L.toSubmodule`. -/
theorem brauer_homFiber_baseChange_finrank_eq
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [Algebra A K']
    [IsScalarTower A A' K']
    (hQP : Nonempty (Q.residueFieldReduction ≅ P))
    {X : FDRep K' G} (L : StableLattice A' X.ρ) :
    Module.finrank K'
        (Representation.IntertwiningMap (Q.scalarExtension K').ρ X.ρ)
      = Module.finrank κ'
          (Representation.IntertwiningMap
            (P.scalarExtension κ').ρ
            (FDRep.of L.reductionRepresentation).ρ) := by
  -- Instances for the source module `Q' = A' ⊗[A] Q.V` over the PID `A'`.
  letI : Fintype G := Fintype.ofFinite G
  letI : Module.Finite A Q.V := Q.finite
  letI : Module.Free A Q.V := Q.free
  letI : Module.Finite A' (A' ⊗[A] Q.V) := inferInstance
  letI : Module.Free A' (A' ⊗[A] Q.V) := inferInstance
  letI : Module.Projective A'[G] (A' ⊗[A] Q.V) := baseChangeProjectiveAG' Q
  -- Instances for the target module `L.toSubmodule` over the PID `A'`.
  letI : Module A'[G] L.toSubmodule := by
    change Module A'[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A' A'[G] L.toSubmodule := by
    change IsScalarTower A' A'[G] L.toRepresentation.asModule
    infer_instance
  letI : Module.Free A' L.toSubmodule := inferInstance
  letI : Module.Finite A' L.toSubmodule := inferInstance
  -- The common-owner Hom-fiber theorem over the PID `A'` computes both field fibers equally.
  have hbase :
      Module.finrank K' (scalarExtIntertwiner A' G (A' ⊗[A] Q.V) L.toSubmodule K') =
        Module.finrank κ' (scalarExtIntertwiner A' G (A' ⊗[A] Q.V) L.toSubmodule κ') :=
    scalarExtIntertwiner_finrank_eq
      (A := A') (G := G) (Q := A' ⊗[A] Q.V) (T := L.toSubmodule) (S₁ := K') (S₂ := κ')
  -- Transport the generic fiber.
  have hK :
      Module.finrank K' (scalarExtIntertwiner A' G (A' ⊗[A] Q.V) L.toSubmodule K') =
        Module.finrank K' (Representation.IntertwiningMap (Q.scalarExtension K').ρ X.ρ) :=
    Representation.IntertwiningMap.finrank_eq_of_equiv
      (fractionChainEquiv (A := A) (G := G) Q (K' := K'))
      (Representation.stableLattice_scalarExtension_ofModule_equiv (A := A') (K := K') L).some
  -- Transport the residue fiber.
  have hk :
      Module.finrank κ' (scalarExtIntertwiner A' G (A' ⊗[A] Q.V) L.toSubmodule κ') =
        Module.finrank κ'
          (Representation.IntertwiningMap (P.scalarExtension κ').ρ
            (FDRep.of L.reductionRepresentation).ρ) :=
    Representation.IntertwiningMap.finrank_eq_of_equiv
      (residueFullEquiv (A := A) (G := G) Q P hQP)
      (Representation.stableLattice_reduction_scalarExtension_equiv (A := A') (K := K') L).some
  -- Compare the raw Hom fibers, then transport each side to the public owners.
  exact hK.symm.trans (hbase.trans hk)

end BaseChangeHomFiber

end Representation
