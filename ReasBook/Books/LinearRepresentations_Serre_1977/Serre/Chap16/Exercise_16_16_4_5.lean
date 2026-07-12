import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_4
import LinearRepresentations_Serre_1977.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_2
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ProjectiveLiteralLifts
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_12
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_3_3.HomFiberBridge
import LinearRepresentations_Serre_1977.Chap16.Remark_16_16_3_5.ReductionBaseChange
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.SimpleFamilyFinite
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.BrauerMultiplicity
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.SemisimpleSchur
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.FieldIndependence.CharPReduction

noncomputable section

open CategoryTheory
open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u x

section ReductionTransport

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [CommRing K] [Algebra A K]
variable {G : Type u} [Monoid G]
variable {E : Type u} [AddCommGroup E] [Module K E]

/-- Helper for Exercise 16-16.4-5: two `A`-module structures on the same ambient `K`-representation
that are *equal* carry isomorphic stable-lattice reductions.  This is the cast-plumbing lemma that
identifies the literal scalar-extension lattice with its `FDRep`-instance transport
(`fdRep_stableLattice_of_literal`): the two only differ by the `Module A`-instance diamond on
`K ⊗[A] Q.V`, whose two instances agree on values, hence are equal. -/
private theorem reductionRep_fdRepOf_eq
    {ρ : Representation K G E}
    {i1 i2 : Module A E} (hi : i1 = i2)
    {t1 : @IsScalarTower A K E _ _
      (@SMulZeroClass.toSMul A E _ (@DistribSMul.toSMulZeroClass A E _
        (@DistribMulAction.toDistribSMul A E _ _ (@Module.toDistribMulAction A E _ _ i1))))}
    {t2 : @IsScalarTower A K E _ _
      (@SMulZeroClass.toSMul A E _ (@DistribSMul.toSMulZeroClass A E _
        (@DistribMulAction.toDistribSMul A E _ _ (@Module.toDistribMulAction A E _ _ i2))))}
    {L1 : @StableLattice K _ G _ E _ _ A _ _ i1 t1 ρ}
    {L2 : @StableLattice K _ G _ E _ _ A _ _ i2 t2 ρ}
    [Module.Finite (IsLocalRing.ResidueField A)
      (@StableLattice.reduction A _ _ K _ _ G _ E _ i1 _ t1 ρ L1)]
    [Module.Finite (IsLocalRing.ResidueField A)
      (@StableLattice.reduction A _ _ K _ _ G _ E _ i2 _ t2 ρ L2)]
    (hL : HEq L1 L2) :
    (FDRep.of (@StableLattice.reductionRepresentation A _ _ K _ _ G _ E _ i1 _ t1 ρ L1))
      = (FDRep.of (@StableLattice.reductionRepresentation A _ _ K _ _ G _ E _ i2 _ t2 ρ L2)) := by
  subst hi
  have ht : t1 = t2 := Subsingleton.elim _ _
  subst ht
  cases hL
  rfl

end ReductionTransport

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
variable [CharZero K]
variable [IsAlgClosed (IsLocalRing.ResidueField A)]

local notation "k" => IsLocalRing.ResidueField A

variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type u} [Group G] [Finite G]

-- Mathlib recall: `List.TFAE` and `List.TFAE.out` are the canonical TFAE owners.

/-- Helper for Exercise 16-16.4-5: the source of a projective envelope of a simple module is
finitely generated over `k[G]`. -/
private lemma moduleFinite_of_projectiveEnvelope_simple
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Exercise 16-16.4-5: every simple finite-dimensional `k[G]`-representation admits
an actual finite projective envelope. -/
private lemma finite_projective_envelope_of_simple
    (S : FDRep k G) [Simple S] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule S.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G S := S.ρ
  letI : Module k[G] S := by
    simpa [ρ] using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple S)
  letI : IsSimpleModule k[G] S := by
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] S
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple
      (G := G) (P := P') (M := S) (f := f'.hom) (hf := hf')
  let Pfg : FGModuleCat k[G] := by
    refine ⟨P', ?_⟩
    exact hfinite
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, by
    change Module.Projective k[G] P'
    infer_instance⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  · simpa [P, ρ] using hf'

/-- Helper for Exercise 16-16.4-5: choose representatives for all simple finite-dimensional
`k[G]`-representations. -/
private lemma exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨iso⟩
            exact ⟨iso.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨iso⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨iso⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro T hT
      let q : ι := ⟦⟨T, hT⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty ((Quotient.out q).1 ≅ T) := Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨iso⟩
      exact ⟨iso.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 16-16.4-5: if a simple copy inside a projective envelope survived the
envelope map, the envelope would split and the simple target would already be projective. -/
private lemma embedding_range_le_ker_of_nonprojective
    {Smod Pmod : Type u}
    [AddCommGroup Smod] [Module k[G] Smod]
    [AddCommGroup Pmod] [Module k[G] Pmod]
    {f : Pmod →ₗ[k[G]] Smod} {i : Smod →ₗ[k[G]] Pmod}
    (hS : IsSimpleModule k[G] Smod) (hi : Function.Injective i) (hf : f.IsProjectiveEnvelope)
    (hS_not_projective : ¬ Module.Projective k[G] Smod) :
    LinearMap.range i ≤ LinearMap.ker f := by
  -- Route correction: force the source-faithful split argument instead of a Jordan-Hölder count.
  intro x hx
  rcases hx with ⟨y, rfl⟩
  by_contra hnot
  have hcomp_ne_zero : f.comp i ≠ 0 := by
    intro hcomp_zero
    have hzero : (f.comp i) y = 0 := by
      simp [hcomp_zero]
    exact hnot <| by
      simpa [LinearMap.comp_apply, LinearMap.mem_ker] using hzero
  letI : IsSimpleModule k[G] Smod := hS
  have hbij : Function.Bijective (f.comp i) := LinearMap.bijective_of_ne_zero hcomp_ne_zero
  let e : Smod ≃ₗ[k[G]] Smod := LinearEquiv.ofBijective (f.comp i) hbij
  let s : Smod →ₗ[k[G]] Pmod := i.comp e.symm.toLinearMap
  have hs_split : f.comp s = LinearMap.id := by
    ext z
    change (f.comp i) (e.symm z) = z
    exact e.apply_symm_apply z
  have hproj : Module.Projective k[G] Smod := Module.Projective.of_split s f hs_split
  exact hS_not_projective hproj

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Exercise 16-16.4-5: a projective simple `k[G]`-module is (isomorphic to) the
underlying representation of a finite projective owner `P0`. Its own projective envelope is an
isomorphism since the target is projective. -/
private lemma exists_finiteProjective_owner_iso_of_projective_simple
    (S : FDRep k G) [Simple S] (hproj : Module.Projective k[G] (asModule S.ρ)) :
    ∃ P0 : FiniteProjectiveGroupAlgebraModule k G, Nonempty (P0.toFiniteRep ≅ S) := by
  letI : Module.Projective k[G] (asModule S.ρ) := hproj
  obtain ⟨P0, f0, hf0⟩ := finite_projective_envelope_of_simple (A := A) S
  obtain ⟨eV⟩ := LinearMap.IsProjectiveEnvelope.nonempty_linearEquiv_target hf0
  refine ⟨P0, ?_⟩
  obtain ⟨e0⟩ := Representation.nonempty_ofModuleMonoidAlgebra_asModuleLinearEquiv_local_support
    (A := A) (G := G) ↥P0.V
  exact Representation.fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local_support
    (A := A) (σ := P0.toFiniteRep) (τ := S) ⟨e0.trans eV⟩

/-- Helper for Exercise 16-16.4-5: an `FDRep` isomorphism yields a representation equivalence of
the underlying representations. -/
private lemma nonempty_repEquiv_of_fdRepIso {σ τ : FDRep k G} (h : Nonempty (σ ≅ τ)) :
    Nonempty (Representation.Equiv σ.ρ τ.ρ) := by
  obtain ⟨e⟩ := h
  exact ⟨Representation.equivOfIso ((forget₂ (FDRep k G) (Rep k G)).mapIso e)⟩

/-- Helper for Exercise 16-16.4-5: an isomorphism of finite projective owners upgrades to an
isomorphism of their underlying finite-dimensional representations. -/
private lemma toFiniteRep_nonempty_iso_of_owner_iso
    {P Q : FiniteProjectiveGroupAlgebraModule k G} (h : Nonempty (P ≅ Q)) :
    Nonempty (P.toFiniteRep ≅ Q.toFiniteRep) := by
  rcases (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := k) (G := G) P Q).1 h with ⟨e⟩
  let eRep :
      ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep) ≅
        ((forget₂ (FDRep k G) (Rep k G)).obj Q.toFiniteRep) :=
    Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv _ _) eRep.hom,
    (FDRep.forget₂HomLinearEquiv _ _) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Exercise 16-16.4-5: the literal scalar-extension stable lattice, transported onto an
opaque `FDRep` representative `X = Q.scalarExtension K` so its `A`-module instances are the canonical
`FDRep.instModuleRestrictScalars` ones (the literal lemma exposes the raw `TensorProduct` instances;
the `A`-actions agree because `A` acts through `algebraMap A K`, proven by tensor induction). -/
@[irreducible] private def fdRep_stableLattice_of_literal (Q : FiniteProjectiveGroupAlgebraModule A G)
    {X : FDRep K G} (hX : X = Q.scalarExtension K) : StableLattice A X.ρ := by
  rw [hX]
  convert Representation.projective_scalarExtension_literal_range_stableLattice_local_support
    (A := A) (K := K) (G := G) Q using 2
  apply Module.ext
  funext r m
  refine TensorProduct.induction_on m ?_ ?_ ?_
  · change (algebraMap A K r) • (0 : ((Q.scalarExtension K).V : Type u))
      = r • (0 : ((Q.scalarExtension K).V : Type u))
    rw [smul_zero, smul_zero]
  · intro a q
    change (algebraMap A K r) • (a ⊗ₜ[A] q) = r • (a ⊗ₜ[A] q)
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def]
    simp
  · intro x y hx hy
    change (algebraMap A K r) • (x + y) = r • (x + y)
    rw [smul_add, smul_add]
    exact congrArg₂ (· + ·) hx hy

/-- Helper for Exercise 16-16.4-5: the generic self-Hom fiber of the lifted projective owner is
one-dimensional, transported across `P0 ≅ S` and `reduction ≅ S` from `End_k(S) = k` (Schur over
the algebraically closed residue field). -/
private lemma generic_self_hom_finrank_eq_one
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (S : FDRep k G) [Simple S]
    (P0 : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ P0))
    (hP0S : Nonempty (P0.toFiniteRep ≅ S))
    {X : FDRep K G} (L : StableLattice A X.ρ)
    (hred : Nonempty (FDRep.of L.reductionRepresentation ≅ S)) :
    Module.finrank K
      (Representation.IntertwiningMap (Q.scalarExtension K).ρ X.ρ) = 1 := by
  obtain ⟨eP⟩ := nonempty_repEquiv_of_fdRepIso (A := A) hP0S
  obtain ⟨eL⟩ := nonempty_repEquiv_of_fdRepIso (A := A) hred
  have hRHS :
      Module.finrank k (Representation.IntertwiningMap P0.toRep.ρ
          (FDRep.of L.reductionRepresentation).ρ) =
        Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) :=
    Representation.IntertwiningMap.finrank_eq_of_equiv eP eL
  haveI : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  have hbridge := projectiveLiftBaseChange_stableLattice_hom_finrank_eq
    (A := A) (K := K) (G := G) P0 Q hQ L
  rw [hbridge, hRHS]
  exact Representation.IsIrreducible.finrank_intertwiningMap_self S.ρ

unseal fdRep_stableLattice_of_literal in
/-- Helper for Exercise 16-16.4-5: the reduction of `fdRep_stableLattice_of_literal` is isomorphic
to `S`, via the literal lattice's reduction iso and `Q.residueFieldReduction ≅ P0`, `P0.toFiniteRep ≅ S`. -/
private lemma fdRep_stableLattice_of_literal_reduction_iso
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    {X : FDRep K G} (hX : X = Q.scalarExtension K)
    (P0 : FiniteProjectiveGroupAlgebraModule k G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ P0))
    {S : FDRep k G} (hP0S : Nonempty (P0.toFiniteRep ≅ S)) :
    Nonempty (FDRep.of (fdRep_stableLattice_of_literal (A := A) (K := K) Q hX).reductionRepresentation ≅ S) := by
  obtain ⟨e1⟩ :=
    Representation.projective_scalarExtension_literal_range_reduction_iso_local_support
      (A := A) (K := K) (G := G) Q
  obtain ⟨e2⟩ := toFiniteRep_nonempty_iso_of_owner_iso (A := A) (h := hQ)
  obtain ⟨e3⟩ := hP0S
  refine ⟨?_⟩
  convert e1.trans (e2.trans e3) using 2
  -- The literal lattice and its `FDRep`-instance transport `fdRep_stableLattice_of_literal` differ
  -- only by the `Module A`-instance diamond on `K ⊗[A] Q.V`; the two instances agree on values, so
  -- the reduction representations (hence the reduction `FDRep`s) coincide.
  subst hX
  refine reductionRep_fdRepOf_eq ?_ ?_
  · -- the two `Module A`-instances agree on values (both act through `algebraMap A K`)
    apply Module.ext
    funext r m
    refine TensorProduct.induction_on m ?_ ?_ ?_
    · change (algebraMap A K r) • (0 : ((Q.scalarExtension K).V : Type u))
        = r • (0 : ((Q.scalarExtension K).V : Type u))
      rw [smul_zero, smul_zero]
    · intro a q
      change (algebraMap A K r) • (a ⊗ₜ[A] q) = r • (a ⊗ₜ[A] q)
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def]
      simp
    · intro x y hx hy
      change (algebraMap A K r) • (x + y) = r • (x + y)
      rw [smul_add, smul_add]
      exact congrArg₂ (· + ·) hx hy
  · -- the transport is definitionally the literal lattice up to the instance cast, hence `HEq`
    simp only [eq_mpr_eq_cast, cast_cast]
    first
      | exact cast_heq _ _
      | exact eqRec_heq _ _
      | exact (cast_heq _ _).symm
      | exact HEq.symm (heq_of_eqRec_eq (id (Eq.symm rfl)) rfl)

/-- Helper for Exercise 16-16.4-5: a projective simple residue representation lifts to a
defect-zero generic simple representation whose reduction is the original simple module. -/
private lemma projective_simple_has_defect_zero_lift
    (S : FDRep k G) [Simple S]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hproj : Module.Projective k[G] (asModule S.ρ)) :
    ∃ (X : FDRep K G) (L : StableLattice A X.ρ),
      Representation.IsIrreducible
        (Representation.scalarExtension X.ρ :
          Representation (AlgebraicClosure K) G ((AlgebraicClosure K) ⊗[K] X.V)) ∧
      HasDefectZero X.ρ p ∧
      Nonempty (FDRep.of L.reductionRepresentation ≅ S) := by
  classical
  -- STEP 1: a finite projective owner `P0` with `P0.toFiniteRep ≅ S` (extracted, since `asModule`
  -- group-algebra instance synthesis there needs relaxed transparency).
  obtain ⟨P0, hP0S⟩ := exists_finiteProjective_owner_iso_of_projective_simple (A := A) S hproj
  -- STEP 2: Henselian projective lift over `A`.
  obtain ⟨Q, hQ⟩ :=
    Representation.exists_projective_lift_of_residueField_projective (A := A) (G := G) P0
  -- STEP 3: generic representation, kept OPAQUE (so the carrier is not repeatedly unfolded); `hX`
  -- bridges to `Q.scalarExtension K` where needed.
  obtain ⟨X, hX⟩ : ∃ Y : FDRep K G, Y = Q.scalarExtension K := ⟨_, rfl⟩
  -- STEP 4: literal scalar-extension lattice on the canonical `FDRep` module instances.
  let L : StableLattice A X.ρ := fdRep_stableLattice_of_literal (A := A) (K := K) Q hX
  -- STEP 8: the reduction of the literal lattice is isomorphic to `S`.
  have hred : Nonempty (FDRep.of L.reductionRepresentation ≅ S) :=
    fdRep_stableLattice_of_literal_reduction_iso (A := A) (K := K) Q hX P0 hQ hP0S
  -- STEP 5: the generic self-Hom fiber is one-dimensional, by transport through `S` (extracted
  -- into its own elaboration budget); `rw [← hX]` turns `Hom(Q.scalarExtension K, X)` into `End X`.
  have hfinrank1 : Module.finrank K (Representation.IntertwiningMap X.ρ X.ρ) = 1 := by
    have h := generic_self_hom_finrank_eq_one (A := A) (K := K) S P0 Q hQ hP0S (X := X) L hred
    rw [← hX] at h
    exact h
  -- STEP 6/7: absolute irreducibility over `AlgebraicClosure K` via char-0 semisimplicity.
  letI : NeZero (Nat.card G : AlgebraicClosure K) :=
    ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  haveI hss : IsSemisimpleRepresentation
      (Representation.scalarExtension X.ρ :
        Representation (AlgebraicClosure K) G ((AlgebraicClosure K) ⊗[K] X.V)) := inferInstance
  have habs : Representation.IsIrreducible
      (Representation.scalarExtension X.ρ :
        Representation (AlgebraicClosure K) G ((AlgebraicClosure K) ⊗[K] X.V)) :=
    isIrreducible_scalarExtension_of_isSemisimple_of_finrank_intertwiningMap_eq_one
      X.ρ hss hfinrank1
  -- Defect-zero: irreducibility of `X.ρ` itself plus the `p`-part divisibility.
  letI : NeZero (Nat.card G : K) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  haveI hssX : IsSemisimpleRepresentation X.ρ := inferInstance
  have hirr : Representation.IsIrreducible X.ρ :=
    isIrreducible_of_isSemisimpleRepresentation_of_finrank_intertwiningMap_eq_one
      X.ρ hfinrank1
  have hdvd : p ^ (Nat.card G).factorization p ∣ Module.finrank K (Representation.asModule X.ρ) := by
    have hP0dvd : p ^ (Nat.card G).factorization p ∣ Module.finrank k P0.toRep :=
      finiteProjectiveRep_finrank_dvd_pPart (p := p) P0
    obtain ⟨eP⟩ := nonempty_repEquiv_of_fdRepIso (A := A) hP0S
    have hP0eq : Module.finrank k P0.toRep = Module.finrank k S.V :=
      eP.toLinearEquiv.finrank_eq
    obtain ⟨eLred⟩ := nonempty_repEquiv_of_fdRepIso (A := A) hred
    have hredeq : Module.finrank k L.reduction = Module.finrank k S.V :=
      eLred.toLinearEquiv.finrank_eq
    have hXeq : Module.finrank K (Representation.asModule X.ρ) = Module.finrank K X.V :=
      (Representation.asModuleEquiv X.ρ).finrank_eq
    have hredX : Module.finrank k L.reduction = Module.finrank K X.V :=
      StableLattice.reduction_finrank_eq (A := A) (K := K) L
    rw [hXeq, ← hredX, hredeq, ← hP0eq]
    exact hP0dvd
  exact ⟨X, L, habs, ⟨hirr, hdvd⟩, hred⟩

/-- Helper for Exercise 16-16.4-5: the Cartan diagonal entry attached to the projective envelope
of `π iS` is the fixed-simple multiplicity of the finite-representation class of that envelope. -/
private lemma cartan_entry_eq_fixed_simple_multiplicity_of_envelope
    (S : FDRep k G) [Simple S]
    {ι : Type x} [Fintype ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι) (hS_iso : Nonempty (π iS ≅ S))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    cartanMatrix k G
      (projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope)
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete)
      iS iS =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S
        [(P iS).toFiniteRep]₀ := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let b :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  -- Read the Cartan entry as the `iS`-coordinate on the simple basis.
  calc
    cartanMatrix k G bP b iS iS = b.repr (cartanHom k G (bP iS)) iS := by
      simp [cartanMatrix, LinearMap.toMatrix_apply]
    _ = simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S
          (cartanHom k G (bP iS)) := by
          -- The fixed-simple multiplicity functional is exactly this simple-basis coordinate.
          simpa [b] using
            (simple_basis_coord_eq_fixed_simple_multiplicity_local
              (A := A) (G := G) (S := S) π hπ_pairwise hπ_complete iS hS_iso
              (cartanHom k G (bP iS)))
    _ = simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S
          [(P iS).toFiniteRep]₀ := by
          -- The chosen projective-envelope basis vector is literally `[P iS]ₚ₀`, and Cartan
          -- sends projective classes to their underlying finite-representation classes.
          rw [projectiveEnvelope_classes_basis_of_complete_family_apply, cartanHom_projectiveClass_eq]

/-- Helper for Exercise 16-16.4-5: a `k[G]`-linear equivalence between a finite projective owner
and the underlying module of a finite-dimensional representation identifies their finite-
representation Grothendieck classes. -/
private lemma toFiniteRep_grothendieckClass_eq_of_linearEquiv
    (P : FiniteProjectiveGroupAlgebraModule k G) (σ : FDRep k G)
    (e : P.V ≃ₗ[k[G]] asModule σ.ρ) :
    [P.toFiniteRep]₀ = [σ]₀ := by
  -- Read the module equivalence as a `Rep`-level isomorphism `P.toRep ≅ Rep.of σ.ρ`.
  let eRep : P.toRep ≅ Rep.of σ.ρ :=
    Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫ (Rep.unitIso (Rep.of σ.ρ)).symm
  let eEquiv : P.toRep.ρ.Equiv σ.ρ := Representation.equivOfIso eRep
  -- Upgrade to an `FDRep` isomorphism `P.toFiniteRep ≅ σ` and compare Grothendieck classes.
  have hiso : Nonempty (P.toFiniteRep ≅ σ) := by
    refine ⟨(Representation.Equiv.toFDRepIso eEquiv) ≪≫ ?_⟩
    exact Action.mkIso (Iso.refl _) (fun g => by ext x; rfl)
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso hiso

/-- Helper for Exercise 16-16.4-5: if the simple residue module is projective, its Cartan
diagonal entry is `1` for any complete simple family and projective-envelope family. -/
private lemma cartan_diagonal_eq_one_of_projective_simple
    (S : FDRep k G) [Simple S]
    (hproj : Module.Projective k[G] (asModule S.ρ))
    {ι : Type x} [Fintype ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι) (hS_iso : Nonempty (π iS ≅ S))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    cartanMatrix k G
      (projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope)
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete)
      iS iS = 1 := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  rw [cartan_entry_eq_fixed_simple_multiplicity_of_envelope
        (A := A) S π hπ_pairwise hπ_complete iS hS_iso P hP_envelope]
  -- Goal: `simple_factor_multiplicity_hom_fixed_local S [(P iS).toFiniteRep]₀ = 1`.
  -- The chosen envelope of `π iS`.
  obtain ⟨f, hf⟩ := hP_envelope iS
  -- `π iS ≅ S` transports projectivity of `asModule S.ρ` to `asModule (π iS).ρ`.
  obtain ⟨eIso⟩ := hS_iso
  let em : asModule (π iS).ρ ≃ₗ[k[G]] asModule S.ρ :=
    (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso eIso).toLinearEquiv
  letI : Module.Projective k[G] (asModule S.ρ) := hproj
  letI : Module.Projective k[G] (asModule (π iS).ρ) := Module.Projective.of_equiv' em.symm
  -- A surjection onto a projective module splits, giving a section `s`.
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf.surjective
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f hrange
  -- `f ∘ s = id`, so `f` is a left inverse of `s`.
  have hleft : Function.LeftInverse f s := fun a => by
    have := LinearMap.ext_iff.1 hs a; simpa using this
  -- The section is surjective by essentiality of the envelope.
  have hs_surj : Function.Surjective s := by
    rw [← LinearMap.range_eq_top]
    refine hf.toIsEssential.eq_top_of_map_eq_top (LinearMap.range s) ?_
    rw [← LinearMap.range_comp, hs, LinearMap.range_id]
  -- The section is injective because `f ∘ s = id`.
  have hs_inj : Function.Injective s := hleft.injective
  let es : asModule (π iS).ρ ≃ₗ[k[G]] (P iS).V := LinearEquiv.ofBijective s ⟨hs_inj, hs_surj⟩
  -- Bridge the envelope source to the class of `π iS`.
  rw [toFiniteRep_grothendieckClass_eq_of_linearEquiv (A := A) (P := P iS) (σ := π iS) es.symm]
  -- Finish: the multiplicity of `S` in `[π iS]` is `1`.
  rw [← simple_basis_coord_eq_fixed_simple_multiplicity_local
        (A := A) (G := G) (S := S) π hπ_pairwise hπ_complete iS ⟨eIso⟩ [π iS]₀,
      ← simple_finiteRep_classes_basis_of_complete_family_apply
        (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) (i := iS)]
  rw [Module.Basis.repr_self, Finsupp.single_eq_same]

/-- Helper for Exercise 16-16.4-5: for a module viewed through `Representation.ofModule'`, the
associated group-algebra operator is the original group-algebra scalar action. -/
private lemma ofModule'_asAlgebraHom_smul
    {X : Type u} [AddCommGroup X] [Module k X] [Module k[G] X] [IsScalarTower k k[G] X]
    (r : k[G]) (m : X) :
    ((Representation.ofModule' X : Representation k G X).asAlgebraHom r) m = r • m := by
  refine MonoidAlgebra.induction_on (p := fun a : k[G] =>
    ((Representation.ofModule' X : Representation k G X).asAlgebraHom a) m = a • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Exercise 16-16.4-5: the owner module of `Representation.ofModule' X` is canonically
the original `k[G]`-module `X`. -/
private lemma ofModule'_asModuleLinearEquiv_self
    (X : Type u) [AddCommGroup X] [Module k X] [Module k[G] X] [IsScalarTower k k[G] X] :
    Nonempty ((Representation.ofModule' X : Representation k G X).asModule ≃ₗ[k[G]] X) := by
  let ρ : Representation k G X := Representation.ofModule' X
  let toFun : ρ.asModule → X := fun x => ρ.asModuleEquiv x
  let invFun : X → ρ.asModule := fun x => ρ.asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by intro x; simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by intro x; simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by intro x y; rfl
  have hsmul : ∀ (r : k[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    calc
      ρ.asModuleEquiv (r • x)
          = (ρ.asAlgebraHom r) (ρ.asModuleEquiv x) :=
            (Representation.asModuleEquiv_map_smul (ρ := ρ) r x)
      _ = r • ρ.asModuleEquiv x := ofModule'_asAlgebraHom_smul (A := A) r (ρ.asModuleEquiv x)
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

/-- Helper for Exercise 16-16.4-5: an equivalence of owner `k[G]`-modules of two finite-dimensional
representations upgrades to an isomorphism of the canonical `FDRep` owners. -/
private lemma nonempty_fdRepOfRho_iso_of_asModuleLinearEquiv
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.asModule ≃ₗ[k[G]] σ.asModule) :
    Nonempty (FDRep.of ρ ≅ FDRep.of σ) := by
  let fI : ρ.IntertwiningMap σ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := σ)).symm e.toLinearMap
  exact ⟨Representation.Equiv.toFDRepIso
    (Representation.Equiv.mk (e.restrictScalars k) fI.isIntertwining')⟩

/-- Helper for Exercise 16-16.4-5: a `k[G]`-linear equivalence between a finite-dimensional
`k[G]`-module and the owner module of a finite-dimensional representation identifies their
finite-representation Grothendieck classes. -/
private lemma fdRepOfModule_grothendieckClass_eq_of_linearEquiv
    (X : Type u) [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [Module k[G] X] [IsScalarTower k k[G] X]
    (σ : FDRep k G) (e : X ≃ₗ[k[G]] asModule σ.ρ) :
    [fdRepOfModule X]₀ = [σ]₀ := by
  let ρX : Representation k G X := Representation.ofModule' X
  obtain ⟨e0⟩ := ofModule'_asModuleLinearEquiv_self (A := A) (G := G) (X := X)
  have hiso0 : Nonempty (FDRep.of ρX ≅ FDRep.of σ.ρ) :=
    nonempty_fdRepOfRho_iso_of_asModuleLinearEquiv (A := A)
      (ρ := ρX) (σ := σ.ρ) (e0.trans e)
  have hiso1 : Nonempty (FDRep.of σ.ρ ≅ σ) :=
    ⟨Action.mkIso (Iso.refl _) (fun g => by ext x; rfl)⟩
  refine (finiteRepGrothendieckClass_eq_of_nonempty_iso
    (V := fdRepOfModule X) (W := FDRep.of σ.ρ) hiso0).trans ?_
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso hiso1

/-- Helper for Exercise 16-16.4-5: a `k[G]`-linear equivalence of finite-dimensional `k[G]`-modules
identifies their `fdRepOfModule` finite-representation Grothendieck classes. -/
private lemma fdRepOfModule_class_congr
    {X Y : Type u} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [Module k[G] X] [IsScalarTower k k[G] X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    [Module k[G] Y] [IsScalarTower k k[G] Y]
    (e : X ≃ₗ[k[G]] Y) :
    (([fdRepOfModule X]₀ : R₀[k](G)) = [fdRepOfModule Y]₀) := by
  apply finiteRepGrothendieckClass_eq_of_nonempty_iso
  obtain ⟨e0X⟩ : Nonempty ((Representation.ofModule' X).asModule ≃ₗ[k[G]] X) :=
    ofModule'_asModuleLinearEquiv_self (A := A) (G := G) (X := X)
  obtain ⟨e0Y⟩ : Nonempty ((Representation.ofModule' Y).asModule ≃ₗ[k[G]] Y) :=
    ofModule'_asModuleLinearEquiv_self (A := A) (G := G) (X := Y)
  exact nonempty_fdRepOfRho_iso_of_asModuleLinearEquiv (A := A)
    (ρ := Representation.ofModule' X) (σ := Representation.ofModule' Y)
    (e0X.trans (e.trans e0Y.symm))

/-- Helper for Exercise 16-16.4-5: a nonprojective simple `M` appears at least twice as a
composition factor of any projective envelope source: once on the head (`Pσ.V / ker f ≅ M`) and a
second time inside the kernel (the embedded simple copy `range i ≤ ker f`). Hence the fixed-simple
multiplicity of the envelope class is at least `2`. Keeping the simple module `M` abstract makes the
heavy Grothendieck-class bookkeeping cheap (its module instances are parameters, not synthesised). -/
private lemma envelope_kernel_multiplicity_ge_two
    (S : FDRep k G) [Simple S]
    (M : Type u) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M]
    (Pσ : FiniteProjectiveGroupAlgebraModule k G)
    {f : Pσ.V →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope)
    {i : M →ₗ[k[G]] Pσ.V} (hi : Function.Injective i)
    (hsub : LinearMap.range i ≤ LinearMap.ker f)
    (hmultM :
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S [fdRepOfModule M]₀ = 1) :
    2 ≤ simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S [Pσ.toFiniteRep]₀ := by
  classical
  -- Finiteness instances for the modules appearing in the additivity lemma.
  haveI hkerfd : FiniteDimensional k ↥(LinearMap.ker f) :=
    FiniteDimensional.of_injective ((LinearMap.ker f).subtype.restrictScalars k)
      Subtype.coe_injective
  -- Quotient finiteness via the `k`-restricted submodule (same carrier, but the `k`-quotient
  -- finite-dimensionality instance is cheap, avoiding the pathological `mkQ.restrictScalars` search).
  haveI hquotfd : FiniteDimensional k (Pσ.V ⧸ LinearMap.ker f) :=
    (inferInstance : FiniteDimensional k (Pσ.V ⧸ (LinearMap.ker f).restrictScalars k))
  -- The injective embedding `i` corestricted to its image inside `ker f`.
  let i' : M →ₗ[k[G]] ↥(LinearMap.ker f) :=
    LinearMap.codRestrict (LinearMap.ker f) i (fun x => hsub (LinearMap.mem_range_self i x))
  have hi' : Function.Injective i' := fun a b hab => hi (congrArg Subtype.val hab)
  haveI hrangefd : FiniteDimensional k ↥(LinearMap.range i') :=
    FiniteDimensional.of_injective ((LinearMap.range i').subtype.restrictScalars k)
      Subtype.coe_injective
  haveI hkerquotfd : FiniteDimensional k (↥(LinearMap.ker f) ⧸ LinearMap.range i') :=
    (inferInstance :
      FiniteDimensional k (↥(LinearMap.ker f) ⧸ (LinearMap.range i').restrictScalars k))
  -- Short exact sequence 1: `0 → ker f → Pσ.V → Pσ.V ⧸ ker f → 0`.
  have h1 : [fdRepOfModule ↥Pσ.V]₀
      = [fdRepOfModule ↥(LinearMap.ker f)]₀
        + [fdRepOfModule (Pσ.V ⧸ LinearMap.ker f)]₀ :=
    finiteRepGrothendieckClass_ofModule_eq_submodule_add_quotient ↥Pσ.V (LinearMap.ker f)
  -- Short exact sequence 2: `0 → range i' → ker f → ker f ⧸ range i' → 0`.
  have h2 : [fdRepOfModule ↥(LinearMap.ker f)]₀
      = [fdRepOfModule ↥(LinearMap.range i')]₀
        + [fdRepOfModule (↥(LinearMap.ker f) ⧸ LinearMap.range i')]₀ :=
    finiteRepGrothendieckClass_ofModule_eq_submodule_add_quotient
      ↥(LinearMap.ker f) (LinearMap.range i')
  -- Identify the head quotient and the embedded copy with `M` at the class level.
  have hPV : [fdRepOfModule ↥Pσ.V]₀ = [Pσ.toFiniteRep]₀ := by
    obtain ⟨e0⟩ := nonempty_ofModuleMonoidAlgebra_asModuleLinearEquiv_local_support
      (A := A) (G := G) ↥Pσ.V
    exact fdRepOfModule_grothendieckClass_eq_of_linearEquiv (A := A) (X := ↥Pσ.V)
      Pσ.toFiniteRep e0.symm
  have hQ : [fdRepOfModule (Pσ.V ⧸ LinearMap.ker f)]₀ = [fdRepOfModule M]₀ :=
    fdRepOfModule_class_congr (A := A) (f.quotKerEquivOfSurjective hf.surjective)
  have hR : [fdRepOfModule ↥(LinearMap.range i')]₀ = [fdRepOfModule M]₀ :=
    fdRepOfModule_class_congr (A := A) (LinearEquiv.ofInjective i' hi').symm
  -- The remaining quotient contributes a nonnegative multiplicity.
  have hnn : 0 ≤ simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S
      [fdRepOfModule (↥(LinearMap.ker f) ⧸ LinearMap.range i')]₀ :=
    simple_factor_multiplicity_hom_fixed_local_class_nonneg (A := A) S
      (fdRepOfModule (↥(LinearMap.ker f) ⧸ LinearMap.range i'))
  -- Apply the additive multiplicity functional to both short exact sequences.
  have key1 := congrArg
    (fun c => simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S c) h1
  have key2 := congrArg
    (fun c => simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S c) h2
  simp only [map_add, hPV, hQ, hR, hmultM] at key1 key2
  -- `key1 : mult [Pσ.toFiniteRep] = mult [ker f] + 1`,
  -- `key2 : mult [ker f] = 1 + mult [ker f ⧸ range i']`, so the total is `≥ 2`.
  rw [key1, key2]
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Exercise 16-16.4-5: Cartan diagonal entry `1` forces the underlying simple module
to be projective, because a nonprojective projective envelope would contribute a second copy of
the simple module in the Grothendieck group. -/
private lemma projective_of_cartan_diagonal_one
    (S : FDRep k G) [Simple S]
    {ι : Type x} [Fintype ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι) (hS_iso : Nonempty (π iS ≅ S))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hdiag :
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete)
        iS iS = 1) :
    Module.Projective k[G] (asModule S.ρ) := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  -- Express the diagonal entry as the fixed-simple multiplicity of the envelope class.
  rw [cartan_entry_eq_fixed_simple_multiplicity_of_envelope
        (A := A) S π hπ_pairwise hπ_complete iS hS_iso P hP_envelope] at hdiag
  -- The chosen projective envelope of `π iS` and the iso `π iS ≅ S`.
  obtain ⟨f, hf⟩ := hP_envelope iS
  obtain ⟨eIso⟩ := hS_iso
  letI : Simple (π iS) := hπ_complete.isSimple iS
  have hSmod_simple :=
    (Representation.irreducible_iff_isSimpleModule_asModule (π iS).ρ).mp
      (FDRep.isIrreducible_of_simple (π iS))
  -- The owner-module equivalence `asModule (π iS).ρ ≃ asModule S.ρ`.
  let em : asModule (π iS).ρ ≃ₗ[k[G]] asModule S.ρ :=
    (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso eIso).toLinearEquiv
  -- Argue by contradiction: assume the simple residue module is not projective.
  by_contra hnp
  have hSmod_np : ¬ Module.Projective k[G] (asModule (π iS).ρ) := by
    intro hP
    letI := hP
    exact hnp (Module.Projective.of_equiv' em)
  -- Embed a copy of `π iS` into the envelope source, landing inside `ker f`.
  obtain ⟨i, hi⟩ : ∃ i : asModule (π iS).ρ →ₗ[k[G]] ↥(P iS).V, Function.Injective i :=
    exists_injective_hom_to_projectiveEnvelope_of_simple (f := f) (hS := hSmod_simple) (hf := hf)
  -- Inline the split argument (avoids re-synthesising the `asModule` group-algebra instance):
  -- if the simple copy escaped `ker f` the envelope would split off `π iS`, making it projective.
  have hsub : LinearMap.range i ≤ LinearMap.ker f := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    by_contra hnot
    have hcomp_ne_zero : f.comp i ≠ 0 := by
      intro hcomp_zero
      have hzero : (f.comp i) y = 0 := by simp [hcomp_zero]
      exact hnot <| by simpa [LinearMap.comp_apply, LinearMap.mem_ker] using hzero
    haveI : IsSimpleModule k[G] (asModule (π iS).ρ) := hSmod_simple
    have hbij : Function.Bijective (f.comp i) := LinearMap.bijective_of_ne_zero hcomp_ne_zero
    let e : asModule (π iS).ρ ≃ₗ[k[G]] asModule (π iS).ρ :=
      LinearEquiv.ofBijective (f.comp i) hbij
    let s : asModule (π iS).ρ →ₗ[k[G]] ↥(P iS).V := i.comp e.symm.toLinearMap
    have hs_split : f.comp s = LinearMap.id := by
      ext z
      change (f.comp i) (e.symm z) = z
      exact e.apply_symm_apply z
    exact hSmod_np (Module.Projective.of_split s f hs_split)
  -- The multiplicity of `S` in `[fdRepOfModule (asModule (π iS).ρ)] = [π iS]` is exactly `1`.
  have hmultM : simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S
      [fdRepOfModule (asModule (π iS).ρ)]₀ = 1 := by
    rw [fdRepOfModule_grothendieckClass_eq_of_linearEquiv (A := A) (X := asModule (π iS).ρ)
          (π iS) (LinearEquiv.refl k[G] (asModule (π iS).ρ)),
        ← simple_basis_coord_eq_fixed_simple_multiplicity_local
          (A := A) (G := G) (S := S) π hπ_pairwise hπ_complete iS ⟨eIso⟩ [π iS]₀,
        ← simple_finiteRep_classes_basis_of_complete_family_apply
          (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) (i := iS)]
    rw [Module.Basis.repr_self, Finsupp.single_eq_same]
  -- The kernel of the envelope contains a second copy of `π iS`, so the multiplicity of `S` in the
  -- envelope class is at least `2` — contradicting the diagonal value `1`.
  have hge2 := envelope_kernel_multiplicity_ge_two (A := A) S (asModule (π iS).ρ)
    (P iS) hf hi hsub hmultM
  omega

/-- Exercise 16-16.4-5: for a fixed local modular system `(A, K, p)` and an irreducible
`k[G]`-module `S`, the following are equivalent: `S` is projective over `k[G]`, `S` is the
reduction modulo `𝔪_A` of a defect-zero stable lattice in a simple `K[G]`-module as in
Proposition `16-16.4-1`, and the diagonal Cartan coefficient `C_SS` attached to the
distinguished projective-envelope basis is equal to `1`. -/
theorem simple_finiteRep_projective_defect_zero_and_cartan_tfae
    (S : FDRep k G) [Simple S]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    List.TFAE
      [ Module.Projective k[G] (asModule S.ρ),
        ∃ (X : FDRep K G) (L : StableLattice A X.ρ),
          ∃ _ :
              Representation.IsIrreducible
                (Representation.scalarExtension X.ρ :
                  Representation (AlgebraicClosure K) G ((AlgebraicClosure K) ⊗[K] X.V)),
            ∃ _ : HasDefectZero X.ρ p,
              Nonempty (FDRep.of L.reductionRepresentation ≅ S),
        ∀ {ι : Type x} [Fintype ι]
          (π : ι → FDRep k G)
          (hπ_pairwise : PairwiseNonisomorphic π)
          (hπ_complete : IsCompleteIrreducibleFamily π)
          (iS : ι)
          (_ : Nonempty (π iS ≅ S))
          (P : ι → FiniteProjectiveGroupAlgebraModule k G)
          (hP_envelope :
            ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope),
          cartanMatrix k G
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope)
            (simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete)
            iS iS = 1 ] := by
  classical
  tfae_have 1 → 2 := by
    intro hproj
    -- Use the literal projective scalar-extension lattice attached to a lifted projective owner.
    rcases projective_simple_has_defect_zero_lift (A := A) (K := K) (p := p) (G := G) S hproj with
      ⟨X, L, hXabs, hdefect, hred⟩
    exact ⟨X, L, hXabs, hdefect, hred⟩
  tfae_have 2 → 1 := by
    rintro ⟨X, L, hXabs, hdefect, hred⟩
    -- Proposition `16-16.4-1` makes the reduction of a defect-zero lattice projective.
    have hprojL :
        Module.Projective k[G] L.reductionRepresentation.asModule :=
      StableLattice.reduction_projective_of_defect_zero
        (A := A) (K := K) (G := G) (p := p) (L := L) hdefect
    rcases hred with ⟨e⟩
    let eMod : asModule (FDRep.of L.reductionRepresentation).ρ ≃ₗ[k[G]] asModule S.ρ :=
      (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso e).toLinearEquiv
    letI : Module.Projective k[G] (asModule (FDRep.of L.reductionRepresentation).ρ) := by
      simpa using hprojL
    exact Module.Projective.of_equiv' eMod
  tfae_have 1 → 3 := by
    intro hproj
    intro ι _ π hπ_pairwise hπ_complete iS hS_iso P hP_envelope
    -- Projectivity splits the chosen envelope, so the Cartan diagonal collapses to the basis vector.
    exact
      cartan_diagonal_eq_one_of_projective_simple
        (S := S) (hproj := hproj) (π := π)
        (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
        (iS := iS) (hS_iso := hS_iso) (P := P) (hP_envelope := hP_envelope)
  tfae_have 3 → 1 := by
    intro hcartan
    classical
    -- Choose a complete pairwise-nonisomorphic simple family (lives in `Type (u+1)`), note it is
    -- finite, and reindex it down to the ambient universe `x` via `Shrink`.
    obtain ⟨ι₀, π₀, hπ₀_pair, hπ₀_comp⟩ :=
      exists_complete_pairwise_nonisomorphic_simple_family_local (A := A) (G := G)
    haveI : Finite ι₀ :=
      finiteOfCompletePairwiseNonisomorphicSimpleFamily π₀ hπ₀_pair hπ₀_comp
    haveI : Small.{x} ι₀ := inferInstance
    let e : ι₀ ≃ Shrink.{x} ι₀ := equivShrink ι₀
    let π : Shrink.{x} ι₀ → FDRep k G := fun j => π₀ (e.symm j)
    haveI : Fintype (Shrink.{x} ι₀) := Fintype.ofFinite _
    have hπ_pair : PairwiseNonisomorphic π := by
      intro a b hab hiso
      exact hπ₀_pair (fun h => hab (e.symm.injective h)) hiso
    haveI hπ_comp : IsCompleteIrreducibleFamily π :=
      { isSimple := fun j => hπ₀_comp.isSimple (e.symm j)
        exists_iso := by
          intro τ hτ
          obtain ⟨i₀, hi₀⟩ := hπ₀_comp.exists_iso τ hτ
          refine ⟨e i₀, ?_⟩
          simpa [π, Equiv.symm_apply_apply] using hi₀ }
    -- Locate `S` inside the family and build the distinguished projective-envelope family.
    obtain ⟨iS₀, hiS₀⟩ := hπ₀_comp.exists_iso S inferInstance
    let iS : Shrink.{x} ι₀ := e iS₀
    have hS_iso : Nonempty (π iS ≅ S) := by
      rcases hiS₀ with ⟨iso⟩
      exact ⟨by simpa [π, iS, Equiv.symm_apply_apply] using iso.symm⟩
    have hPex : ∀ j : Shrink.{x} ι₀,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π j).ρ, f.IsProjectiveEnvelope :=
      fun j => finite_projective_envelope_of_simple (A := A) (π j)
    choose P hP_envelope using hPex
    -- Reading off the diagonal value `1` and inverting it gives projectivity.
    have hdiag := hcartan π hπ_pair hπ_comp iS hS_iso P hP_envelope
    exact projective_of_cartan_diagonal_one (A := A) S π hπ_pair hπ_comp iS hS_iso P
      hP_envelope hdiag
  tfae_finish

end
