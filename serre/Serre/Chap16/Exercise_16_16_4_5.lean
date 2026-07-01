import Mathlib
import Serre.Chap14.Corollary_14_14_3_3
import Serre.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import Serre.Chap14.Exercise_14_14_4_5
import Serre.Chap14.Exercise_14_14_5_4
import Serre.Chap14.Infra_14_4_ProjectiveLift
import Serre.Chap14.Lemma_14_14_4_2
import Serre.Chap15.Definition_15_15_1_1
import Serre.Chap15.Definition_15_15_3_1
import Serre.Chap15.Theorem_15_15_2_2
import Serre.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import Serre.Chap16.Exercise_16_16_1_12
import Serre.Chap16.Proposition_16_16_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u x

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
variable [IsAlgClosed K]

local notation "k" => IsLocalRing.ResidueField A

variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type u} [Group G] [Finite G]

/- Domain-style sampling for this item:
* primary domain: modular representation theory for finite groups, relating defect-zero lifts,
  projectivity over `k[G]`, and diagonal Cartan coefficients;
* relevant owner declarations inspected before refining:
  `Representation.HasDefectZero`,
  `StableLattice.reduction_projective_of_defect_zero`,
  `projectiveEnvelope_classes_basis_of_complete_family`,
  `cartanMatrix`;
* best owner abstraction: the Chapter `15` Cartan owner `cartanMatrix k G` together with the
  distinguished Chapter `14` simple/projective-envelope bases attached to a complete simple family.

Source/core/bridge triage:
* source-facing: this exercise asserts the equivalence between projectivity of a fixed simple
  `k[G]`-module, existence of a defect-zero lift over `A`, and the Cartan-diagonal condition
  `C_SS = 1`;
* core/canonical: `HasDefectZero`, `StableLattice`, `cartanMatrix`, and the canonical simple and
  projective-envelope basis owners from Chapters `14` and `15`;
* bridge/view: the condition `C_SS = 1` is only a theorem-level proposition obtained by reading a
  diagonal entry of the canonical Cartan matrix, so it should not be introduced as a separate
  public owner.

Primitive data vs derived API:
* primitive data: the simple object `S`, a defect-zero lift `(X, L)`, and the finite simple family
  with projective envelopes needed to evaluate the canonical Cartan matrix;
* derived API: the diagonal condition itself, which is read directly from the canonical Cartan
  owner instead of being stored as a parallel local definition.
-/

/-- Helper for Exercise 16-16.4-5: the canonical `k[G]`-module owner attached to an
`FDRep k G`. -/
private noncomputable abbrev fdRepAsModule_local (τ : FDRep k G) : ModuleCat k[G] :=
  Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj τ)

-- Proof sketch: once the target simple module is already projective, any projective envelope onto
-- it is an isomorphism, so the envelope source contributes the same Grothendieck class as the
-- simple target.
/-- Helper for Exercise 16-16.4-5: a finite projective envelope onto a projective simple target is
isomorphic to that target in `FDRep k G`. -/
theorem finite_projective_envelope_toFiniteRep_iso_target_of_projective
    {k0 : Type u} [Field k0]
    {π : FDRep k0 G}
    {P : FiniteProjectiveGroupAlgebraModule k0 G}
    (hπproj : Module.Projective k0[G] (asModule π.ρ))
    {f : P.V →ₗ[k0[G]] asModule π.ρ}
    (hf : f.IsProjectiveEnvelope) :
    Nonempty (P.toFiniteRep ≅ π) := by
  let M : ModuleCat k0[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k0 G) (Rep k0 G)).obj π)
  let _ : Module.Projective k0[G] M := by
    -- Repackage projectivity on the canonical `ModuleCat` owner of `π`.
    simpa using hπproj
  let f' : P.V →ₗ[k0[G]] M := by
    -- The envelope map is unchanged by this target rebundling.
    simpa using f
  have hf' : f'.IsProjectiveEnvelope := by
    -- The projective-envelope structure survives the same rebundling.
    simpa [f'] using hf
  obtain ⟨eLin⟩ := hf'.nonempty_linearEquiv_target
  let eRep' : P.toRep ≅ ((forget₂ (FDRep k0 G) (Rep k0 G)).obj π) :=
    Rep.ofModuleMonoidAlgebra.mapIso eLin.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k0 G) (Rep k0 G)).obj π)).symm
  let eRep : ((forget₂ (FDRep k0 G) (Rep k0 G)).obj P.toFiniteRep) ≅
      ((forget₂ (FDRep k0 G) (Rep k0 G)).obj π) := by
    -- Forgetting `P.toFiniteRep` yields the same `Rep` owner as `P.toRep`.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep] using eRep'
  -- Transport the recovered `Rep` isomorphism back to `FDRep`.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv P.toFiniteRep π) eRep.hom,
    (FDRep.forget₂HomLinearEquiv π P.toFiniteRep) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k0 G) (Rep k0 G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k0 G) (Rep k0 G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Exercise 16-16.4-5: a `k[G]`-linear equivalence between the owner modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep k G`. -/
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv
    {σ τ : FDRep k G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[k[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  -- Repackage the recovered `k[G]`-linear equivalence as an isomorphism in `Rep k G`.
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj τ)).symm
  -- Faithfulness of `FDRep ⥤ Rep` transports that isomorphism back to `FDRep`.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

-- Proof sketch: if `S` is projective, then the projective envelope indexed by `iS` is already
-- isomorphic to `π iS`, so the `iS`-th diagonal Cartan coefficient is the coordinate of a basis
-- vector against itself.
/-- Helper for Exercise 16-16.4-5: projectivity of a simple module forces the matching diagonal
Cartan coefficient to be `1`. -/
theorem cartan_diagonal_eq_one_of_projective_simple
    {k0 : Type u} [Field k0]
    (S : FDRep k0 G) [Simple S]
    {ι : Type x} [Fintype ι]
    (π : ι → FDRep k0 G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι)
    (hS_iso : Nonempty (π iS ≅ S))
    (P : ι → FiniteProjectiveGroupAlgebraModule k0 G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k0[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hproj : Module.Projective k0[G] (asModule S.ρ)) :
    cartanMatrix k0 G
      (projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope)
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete)
      iS iS = 1 := by
  rcases hP_envelope iS with ⟨f, hf⟩
  rcases hS_iso with ⟨eS⟩
  have hπproj : Module.Projective k0[G] (asModule (π iS).ρ) := by
    let eMod : asModule (π iS).ρ ≃ₗ[k0[G]] asModule S.ρ :=
      (((forget₂ (FDRep k0 G) (Rep k0 G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso eS).toLinearEquiv
    let _ : Module.Projective k0[G] (asModule S.ρ) := hproj
    -- Transport projectivity across the chosen isomorphism `π iS ≅ S`.
    exact Module.Projective.of_equiv' eMod.symm
  have hIso : Nonempty ((P iS).toFiniteRep ≅ π iS) :=
    finite_projective_envelope_toFiniteRep_iso_target_of_projective
      hπproj hf
  let b :=
    simple_finiteRep_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete
  -- Evaluate the Cartan matrix entry on the canonical projective-envelope and simple bases.
  simp only [cartanMatrix, LinearMap.toMatrix_apply]
  rw [projectiveEnvelope_classes_basis_of_complete_family_apply]
  change b.repr (cartanHom k0 G [P iS]ₚ₀) iS = 1
  rw [cartanHom_projectiveClass_eq]
  rw [finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k0) (G := G) hIso]
  have hb : b.repr [π iS]₀ = Finsupp.single iS (1 : ℤ) := by
    simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using b.repr_self iS
  have hbi := congrArg (fun c : ι →₀ ℤ => c iS) hb
  simpa using hbi

omit [CharP k p] [Fact p.Prime] [IsDomain A] [IsDiscreteValuationRing A] [Finite G] in
/-- Helper for Exercise 16-16.4-5: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
theorem exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot admit an isomorphism.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 16-16.4-5: reindex the complete simple family by a finite type living in
the ambient universe `x`, so it can be fed to the canonical Cartan/simple-basis owners. -/
theorem exists_fintype_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type x) (_ : Fintype ι) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  obtain ⟨ι₀, π₀, hπ₀_pairwise, hπ₀_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (A := A) (G := G)
  letI : Finite ι₀ := IsCompleteIrreducibleFamily.finite_index π₀ hπ₀_complete hπ₀_pairwise
  letI : Fintype ι₀ := Fintype.ofFinite ι₀
  let n : ℕ := Fintype.card ι₀
  let e : Fin n ≃ ι₀ := (Fintype.equivFin ι₀).symm
  let ι : Type x := ULift.{x, 0} (Fin n)
  let π : ι → FDRep k G := fun i ↦ π₀ (e i.down)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro i j hij hIso
    have hij' : e i.down ≠ e j.down := by
      intro hEq
      apply hij
      cases i
      cases j
      simp at hEq ⊢
      cases hEq
      rfl
    exact hπ₀_pairwise hij' hIso
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro i
      exact hπ₀_complete.isSimple (e i.down)
    · intro τ hτ
      have hτ_irred : Representation.IsIrreducible τ.ρ := by
        simpa using (FDRep.isIrreducible_of_simple τ)
      obtain ⟨i₀, hi₀⟩ :=
        IsCompleteIrreducibleFamily.exists_iso_of_representation
          (K := k) (G := G) π₀ hπ₀_complete τ.ρ hτ_irred
      have hτ_iso : Nonempty (FDRep.of τ.ρ ≅ τ) := by
        simpa using (show Nonempty (FDRep.of τ.ρ ≅ FDRep.of τ.ρ) from ⟨Iso.refl _⟩)
      refine ⟨⟨e.symm i₀⟩, ?_⟩
      rcases hi₀ with ⟨eτ⟩
      rcases hτ_iso with ⟨eτ'⟩
      simpa [π, e] using (show Nonempty (τ ≅ π₀ i₀) from ⟨eτ'.symm.trans eτ⟩)
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

omit [CharP k p] [Fact p.Prime] [IsDomain A] [IsDiscreteValuationRing A] [Finite G] in
/-- Helper for Exercise 16-16.4-5: the source of a projective envelope of a simple module is
cyclic, hence finitely generated over the group algebra. -/
theorem moduleFinite_of_projectiveEnvelope_simple_local
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    -- The chosen cyclic generator maps to a nonzero vector, so the image cannot vanish.
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
    -- Once the cyclic span is all of `P`, the canonical map from `k[G]` is onto.
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

omit [CharP k p] [Fact p.Prime] [IsDomain A] [IsDiscreteValuationRing A] in
/-- Helper for Exercise 16-16.4-5: every simple finite-dimensional `k[G]`-representation admits a
finite projective envelope in the canonical owner category of projective modules. -/
theorem exists_finite_projective_envelope_of_simple_local
    (τ : FDRep k G) [Simple τ] :
    ∃ Q : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : Q.V →ₗ[k[G]] asModule τ.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    -- Expose the ambient `k[G]`-module structure carried by `τ`.
    simpa [ρ] using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Categorical simplicity gives irreducibility of the underlying representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule k[G] τ := by
    -- Move the simple-object statement to the `k[G]`-module owner needed by the envelope theorem.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] τ
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  obtain ⟨Q', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] Q' := by
    letI : Nontrivial τ := IsSimpleModule.nontrivial (R := k[G]) (M := τ)
    obtain ⟨m, hm⟩ := exists_ne (0 : τ)
    obtain ⟨x, hx⟩ := hf'.surjective m
    let N : Submodule k[G] Q' := Submodule.span k[G] {x}
    have hmap_ne_bot : N.map f'.hom ≠ ⊥ := by
      -- The chosen cyclic generator maps to a nonzero vector, so the image cannot vanish.
      intro hbot
      have hxmem : f'.hom x ∈ N.map f'.hom := by
        exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
      have hfx : f'.hom x = 0 := by
        rw [hbot] at hxmem
        simpa using hxmem
      exact hm <| by simpa [hx] using hfx
    have hmap_top : N.map f'.hom = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top (N.map f'.hom)).resolve_left hmap_ne_bot
    have hN_top : N = ⊤ := hf'.toIsEssential.eq_top_of_map_eq_top N hmap_top
    have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] Q' x) := by
      -- Once the cyclic span is all of `Q'`, the canonical map from `k[G]` is onto.
      simpa [LinearMap.toSpanSingleton_apply] using
        (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
    exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] Q' x) hsurj
  let Qfg : FGModuleCat k[G] := by
    refine ⟨Q', ?_⟩
    change Module.Finite k[G] Q'
    exact hfinite
  have hproj : Module.Projective k[G] Qfg := by
    change Module.Projective k[G] Q'
    infer_instance
  let Q : FiniteProjectiveGroupAlgebraModule k G := ⟨Qfg, hproj⟩
  refine ⟨Q, ?_⟩
  refine ⟨(by simpa [ρ] using f'.hom), ?_⟩
  -- The bundled `ModuleCat` envelope is definitionally the same linear-map envelope on `Q.V`.
  simpa [Q, ρ] using hf'

/-- Helper for Exercise 16-16.4-5: a projective simple `k[G]`-module admits an actual finite
projective `A[G]`-lift whose residue reduction is that simple module. -/
theorem projective_simple_residueField_lift
    (S : FDRep k G) [Simple S]
    (hproj : Module.Projective k[G] (asModule S.ρ)) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction.toFiniteRep ≅ S) := by
  -- First package `S` as the target of a finite projective envelope over `k[G]`.
  obtain ⟨P, f, hf⟩ :=
    exists_finite_projective_envelope_of_simple_local (A := A) (G := G) S
  have hPS : Nonempty (P.toFiniteRep ≅ S) :=
    finite_projective_envelope_toFiniteRep_iso_target_of_projective
      (G := G) hproj hf
  -- Then lift that actual projective `k[G]`-owner through Chapter `14`.
  obtain ⟨Q, hQP⟩ :=
    Representation.exists_projective_lift_of_residueField_projective
      (A := A) (G := G) P
  refine ⟨Q, ?_⟩
  have hQredP :
      Nonempty (Q.residueFieldReduction.toFiniteRep ≅ P.toFiniteRep) := by
    rcases
        (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
          (A := k) (G := G) Q.residueFieldReduction P).1 hQP with
      ⟨e⟩
    let eRep :
        ((forget₂ (FDRep k G) (Rep k G)).obj Q.residueFieldReduction.toFiniteRep) ≅
          ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep) :=
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso
    -- Transport the recovered `Rep` isomorphism back to `FDRep`.
    refine ⟨⟨(FDRep.forget₂HomLinearEquiv _ _) eRep.hom,
      (FDRep.forget₂HomLinearEquiv _ _) eRep.inv, ?_, ?_⟩⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  rcases hQredP with ⟨eQredP⟩
  rcases hPS with ⟨ePS⟩
  -- Compose the reduction identification with the envelope source identification.
  exact ⟨eQredP.trans ePS⟩

/-- Helper for Exercise 16-16.4-5: a finite-dimensional `k[G]`-module is finite length because
finite-dimensionality over the field `k` implies both noetherian and artinian conditions. -/
theorem isFiniteLength_of_groupAlgebra_module_local
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    IsFiniteLength k[G] M := by
  -- The vector-space finiteness over `k` controls the `k[G]`-module lattice as well.
  exact (isFiniteLength_iff_isNoetherian_isArtinian).2
    ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

/-- Helper for Exercise 16-16.4-5: choose a Jordan-Hölder series for a finite-dimensional
`k[G]`-module. -/
noncomputable def finiteLengthCompositionSeries_local
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    CompositionSeries (Submodule k[G] M) :=
  Classical.choose
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module_local (A := A) (G := G) M))

/-- Helper for Exercise 16-16.4-5: the chosen finite-length composition series starts at `⊥`. -/
theorem finiteLengthCompositionSeries_head_local
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    (finiteLengthCompositionSeries_local (A := A) (G := G) M).head = ⊥ :=
  (Classical.choose_spec
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module_local (A := A) (G := G) M))).1

/-- Helper for Exercise 16-16.4-5: the chosen finite-length composition series ends at `⊤`. -/
theorem finiteLengthCompositionSeries_last_local
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    (finiteLengthCompositionSeries_local (A := A) (G := G) M).last = ⊤ :=
  (Classical.choose_spec
    (isFiniteLength_iff_exists_compositionSeries.mp
      (isFiniteLength_of_groupAlgebra_module_local (A := A) (G := G) M))).2

/-- Helper for Exercise 16-16.4-5: the quotient factor attached to one step of a composition
series. -/
private abbrev compositionSeriesFactor_local
    {M : Type*} [AddCommGroup M] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) :=
  ((s (Fin.succ i)) ⧸ (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype)

/-- Helper for Exercise 16-16.4-5: a `k[G]`-submodule inherits its `k`-module structure by
restriction of scalars. -/
private instance submodule_module_over_base_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Submodule k[G] M) : Module k N :=
  Module.compHom N (algebraMap k k[G])

/-- Helper for Exercise 16-16.4-5: the scalar tower `k → k[G]` restricts to every
`k[G]`-submodule. -/
private instance submodule_isScalarTower_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Submodule k[G] M) : IsScalarTower k k[G] N :=
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    ext
    exact IsScalarTower.algebraMap_smul (k[G]) a (x : M)

/-- Helper for Exercise 16-16.4-5: quotients of `k[G]`-modules inherit the underlying
`k`-module structure by restriction of scalars. -/
private instance quotient_module_over_base_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Submodule k[G] M) : Module k (M ⧸ N) :=
  Module.compHom (M ⧸ N) (algebraMap k k[G])

/-- Helper for Exercise 16-16.4-5: the scalar tower `k → k[G]` descends to every quotient of a
`k[G]`-module. -/
private instance quotient_isScalarTower_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Submodule k[G] M) : IsScalarTower k k[G] (M ⧸ N) :=
  IsScalarTower.of_algebraMap_smul fun a x ↦
    IsScalarTower.algebraMap_smul (k[G]) a x

/-- Helper for Exercise 16-16.4-5: a factor of a composition series matches a fixed simple
`k[G]`-module. -/
private def compositionSeriesFactorMatches_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) : Prop :=
  Nonempty (compositionSeriesFactor_local (s := s) (i := i) ≃ₗ[k[G]] T)

/-- Helper for Exercise 16-16.4-5: the number of factors in a chosen composition series that are
isomorphic to a fixed simple module. -/
private noncomputable def simple_factor_count_of_module_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) : ℕ :=
  Nat.card { i : Fin s.length // compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) }

/-- Helper for Exercise 16-16.4-5: the Chapter `14` "occurs twice" theorem converts directly
into a lower bound on the number of matching Jordan-Hölder factors in the chosen series. -/
theorem simple_factor_count_ge_two_of_nonprojective_projectiveEnvelope_local
    {S0 : Type*} [AddCommGroup S0] [Module k[G] S0]
    {P0 : Type*} [AddCommGroup P0] [Module k[G] P0]
    {f : P0 →ₗ[k[G]] S0}
    (hS : IsSimpleModule k[G] S0) (hf : f.IsProjectiveEnvelope)
    {s : CompositionSeries (Submodule k[G] P0)}
    (hs_head : s.head = ⊥) (hs_last : s.last = ⊤)
    (hS_not_projective : ¬ Module.Projective k[G] S0) :
    2 ≤ simple_factor_count_of_module_local (T := S0) (s := s) := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ :=
    simple_occurs_twice_in_compositionSeries_of_nonprojective_projectiveEnvelope
      hS hf hs_head hs_last hS_not_projective
  let A :=
    { l : Fin s.length // compositionSeriesFactorMatches_local (T := S0) (s := s) (i := l) }
  have hcard : 2 ≤ Fintype.card A := by
    -- The two distinct matching indices from Chapter `14` already give two distinct elements of
    -- the counting subtype.
    exact Nat.succ_le_of_lt <|
      (Fintype.one_lt_card_iff).2
        ⟨⟨i, hi⟩, ⟨j, hj⟩, by
          intro hEq
          apply hij
          exact Subtype.ext_iff.mp hEq⟩
  -- Unfold the counting owner only at the end, after the cardinal lower bound is established.
  simpa [simple_factor_count_of_module_local, A, Nat.card_eq_fintype_card] using hcard

/-- Helper for Exercise 16-16.4-5: transporting a factor quotient across a linear equivalence
preserves the property of matching the fixed target module. -/
private theorem compositionSeriesFactorMatches_iff_of_linearEquiv_local
    {T A0 B0 : Type*} [AddCommGroup T] [AddCommGroup A0] [AddCommGroup B0]
    [Module k[G] T] [Module k[G] A0] [Module k[G] B0]
    (e : A0 ≃ₗ[k[G]] B0) :
    Nonempty (A0 ≃ₗ[k[G]] T) ↔ Nonempty (B0 ≃ₗ[k[G]] T) := by
  constructor
  · intro hA
    rcases hA with ⟨eA⟩
    exact ⟨e.symm.trans eA⟩
  · intro hB
    rcases hB with ⟨eB⟩
    exact ⟨e.trans eB⟩

/-- Helper for Exercise 16-16.4-5: equivalent composition series have the same count of matching
factors. -/
private theorem simple_factor_count_series_equiv_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T] [Module k[G] M]
    {s₁ s₂ : CompositionSeries (Submodule k[G] M)}
    (h : s₁.Equivalent s₂) :
    simple_factor_count_of_module_local (T := T) (s := s₁) =
      simple_factor_count_of_module_local (T := T) (s := s₂) := by
  classical
  let e :
      { i : Fin s₁.length // compositionSeriesFactorMatches_local (T := T) (s := s₁) (i := i) } ≃
        { j : Fin s₂.length // compositionSeriesFactorMatches_local (T := T) (s := s₂) (i := j) } :=
    { toFun := fun i => ⟨h.choose i.1, by
        rcases h.choose_spec i.1 with ⟨ei⟩
        exact (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T) (e := ei)).1 i.2⟩
      invFun := fun j => ⟨h.choose.symm j.1, by
        rcases h.choose_spec (h.choose.symm j.1) with ⟨ej⟩
        have hj : h.choose (h.choose.symm j.1) = j.1 := by
          simp
        have ej' :
            compositionSeriesFactor_local (s := s₁) (i := h.choose.symm j.1) ≃ₗ[k[G]]
              compositionSeriesFactor_local (s := s₂) (i := h.choose (h.choose.symm j.1)) := by
          simpa [compositionSeriesFactor_local] using ej
        have hmatch :
            compositionSeriesFactorMatches_local (T := T) (s := s₂)
              (i := h.choose (h.choose.symm j.1)) := by
          simpa [hj] using j.2
        exact (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T) (e := ej')).2 hmatch⟩
      left_inv := by
        intro i
        ext
        simp
      right_inv := by
        intro j
        ext
        simp }
  simpa [simple_factor_count_of_module_local] using Nat.card_congr e

/-- Helper for Exercise 16-16.4-5: mapping a factor quotient along an injective linear map
identifies it with the corresponding factor in the mapped composition series. -/
private noncomputable def compositionSeriesFactor_map_equiv_local
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    {f : N →ₗ[k[G]] M} (hf : Function.Injective f)
    (s : CompositionSeries (Submodule k[G] N)) (i : Fin s.length) :
    compositionSeriesFactor_local (s := s) (i := i) ≃ₗ[k[G]]
      compositionSeriesFactor_local
        (s := s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩)
        (i := i) := by
  let e : s i.succ ≃ₗ[k[G]] Submodule.map f (s i.succ) :=
    Submodule.equivMapOfInjective (f := f) hf (s i.succ)
  have hmap :
      Submodule.map (e : s i.succ →ₗ[k[G]] Submodule.map f (s i.succ))
          ((s (Fin.castSucc i)).comap (s i.succ).subtype) =
        (Submodule.map f (s (Fin.castSucc i))).comap (Submodule.map f (s i.succ)).subtype := by
    -- Compare the predecessor submodules after transporting along the injective map equivalence.
    rw [Submodule.map_equiv_eq_comap_symm]
    ext z
    constructor
    · intro hz
      change ((e.symm z : s i.succ) : N) ∈ s (Fin.castSucc i) at hz
      change z.1 ∈ Submodule.map f (s (Fin.castSucc i))
      exact ⟨(e.symm z : s i.succ), hz, by simp [e]⟩
    · intro hz
      change ((e.symm z : s i.succ) : N) ∈ s (Fin.castSucc i)
      change z.1 ∈ Submodule.map f (s (Fin.castSucc i)) at hz
      rcases hz with ⟨y, hy, hyz⟩
      rcases z.2 with ⟨w, hw, hwz⟩
      have hwy : w = y := hf (hwz.trans hyz.symm)
      have hyq : y ∈ s i.succ := hwy ▸ hw
      have heyz : e ⟨y, hyq⟩ = z := by
        apply Subtype.ext
        simpa [e] using hyz
      have hEq : (⟨y, hyq⟩ : s i.succ) = e.symm z :=
        e.injective (heyz.trans (e.apply_symm_apply z).symm)
      simpa [hEq.symm] using hy
  simpa [compositionSeriesFactor_local] using
    (Submodule.Quotient.equiv
      ((s (Fin.castSucc i)).comap (s i.succ).subtype)
      ((Submodule.map f (s (Fin.castSucc i))).comap (Submodule.map f (s i.succ)).subtype)
      e hmap)

/-- Helper for Exercise 16-16.4-5: mapping a composition series along an injective linear map
preserves the count of matching factors. -/
private theorem simple_factor_count_series_map_local
    {T M N : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup N]
    [Module k[G] T] [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    {f : N →ₗ[k[G]] M} (hf : Function.Injective f)
    (s : CompositionSeries (Submodule k[G] N)) :
    simple_factor_count_of_module_local (T := T)
        (s := s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩) =
      simple_factor_count_of_module_local (T := T) (s := s) := by
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩
  let e :
      { i : Fin s.length // compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) } ≃
        { i : Fin s'.length // compositionSeriesFactorMatches_local (T := T) (s := s') (i := i) } :=
    { toFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_map_equiv_local (hf := hf) (s := s) (i := i.1))).1 i.2⟩
      invFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_map_equiv_local (hf := hf) (s := s) (i := i.1))).2 i.2⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        ext
        rfl }
  simpa [simple_factor_count_of_module_local, s'] using (Nat.card_congr e).symm

/-- Helper for Exercise 16-16.4-5: comapping along a surjective linear map identifies factor
quotients with the original factors. -/
private noncomputable def compositionSeriesFactor_comap_equiv_local
    {M Q : Type*} [AddCommGroup M] [AddCommGroup Q]
    [Module k M] [Module k Q] [Module k[G] M] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] Q]
    {g : M →ₗ[k[G]] Q} (hg : Function.Surjective g)
    (s : CompositionSeries (Submodule k[G] Q)) (i : Fin s.length) :
    compositionSeriesFactor_local
        (s := s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩)
        (i := i) ≃ₗ[k[G]]
      compositionSeriesFactor_local (s := s) (i := i) := by
  let φ₀ : Submodule.comap g (s i.succ) →ₗ[k[G]] s i.succ :=
    { toFun := fun x => ⟨g x, x.2⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  have hφ₀_surj : Function.Surjective φ₀ := by
    -- Surjectivity comes from surjectivity of `g` on the ambient module.
    intro y
    rcases hg y with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · simpa [hx] using y.2
    · ext
      simp [φ₀, hx]
  let φ :
      Submodule.comap g (s i.succ) →ₗ[k[G]]
        (s i.succ ⧸ (s (Fin.castSucc i)).comap (s i.succ).subtype) :=
    (Submodule.mkQ ((s (Fin.castSucc i)).comap (s i.succ).subtype)).comp φ₀
  have hφ_surj : Function.Surjective φ := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro y
    rcases hφ₀_surj y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hker :
      φ.ker =
        (Submodule.comap g (s (Fin.castSucc i))).comap (Submodule.comap g (s i.succ)).subtype := by
    -- Landing in the previous step is exactly the kernel condition after quotienting.
    ext x
    change
      ((Submodule.mkQ ((s (Fin.castSucc i)).comap (s i.succ).subtype)) (φ₀ x) = 0) ↔
        x.1 ∈ Submodule.comap g (s (Fin.castSucc i))
    simp [φ₀]
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective φ hφ_surj)

/-- Helper for Exercise 16-16.4-5: comapping a composition series along a surjective linear map
preserves the count of matching factors. -/
private theorem simple_factor_count_series_comap_local
    {T M Q : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup Q]
    [Module k[G] T] [Module k M] [Module k Q] [Module k[G] M] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] Q]
    {g : M →ₗ[k[G]] Q} (hg : Function.Surjective g)
    (s : CompositionSeries (Submodule k[G] Q)) :
    simple_factor_count_of_module_local (T := T)
        (s := s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩) =
      simple_factor_count_of_module_local (T := T) (s := s) := by
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩
  let e :
      { i : Fin s'.length // compositionSeriesFactorMatches_local (T := T) (s := s') (i := i) } ≃
        { i : Fin s.length // compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) } :=
    { toFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_comap_equiv_local (hg := hg) (s := s) (i := i.1))).1 i.2⟩
      invFun := fun i => ⟨i.1, by
        simpa [s'] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_comap_equiv_local (hg := hg) (s := s) (i := i.1))).2 i.2⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        ext
        rfl }
  simpa [simple_factor_count_of_module_local, s'] using Nat.card_congr e

/-- Helper for Exercise 16-16.4-5: the multiplicity of a fixed target module in a finite
`k[G]`-module, computed from the chosen Jordan-Hölder series. -/
private noncomputable def simple_factor_multiplicity_local
    (T : Type*) [AddCommGroup T] [Module k[G] T]
    (M : Type*) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module k[G] M] [IsScalarTower k k[G] M] : ℕ :=
  simple_factor_count_of_module_local (T := T)
    (s := finiteLengthCompositionSeries_local (A := A) (G := G) M)

/-- Helper for Exercise 16-16.4-5: the chosen-series multiplicity agrees with the count computed
from any other composition series with endpoints `⊥` and `⊤`. -/
private theorem simple_factor_multiplicity_eq_count_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T]
    [Module k M] [FiniteDimensional k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (s : CompositionSeries (Submodule k[G] M))
    (hs_head : s.head = ⊥) (hs_last : s.last = ⊤) :
    simple_factor_multiplicity_local (A := A) (G := G) T M =
      simple_factor_count_of_module_local (T := T) (s := s) := by
  -- Jordan-Hölder identifies the chosen composition series with any other one having the same
  -- endpoints, so the factor count is independent of the chosen series.
  exact simple_factor_count_series_equiv_local (T := T) (h :=
    CompositionSeries.jordan_holder
      (finiteLengthCompositionSeries_local (A := A) (G := G) M) s
      ((finiteLengthCompositionSeries_head_local (A := A) (G := G) M).trans hs_head.symm)
      ((finiteLengthCompositionSeries_last_local (A := A) (G := G) M).trans hs_last.symm))

/-- Helper for Exercise 16-16.4-5: in an exact sequence, the mapped left series and comapped
right series meet at the exact seam. -/
private theorem compositionSeries_map_last_eq_comap_head_of_exact_local
    {M N Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module k M] [Module k N] [Module k Q]
    [Module k[G] M] [Module k[G] N] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N] [IsScalarTower k k[G] Q]
    {f : N →ₗ[k[G]] M} {g : M →ₗ[k[G]] Q}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (t : CompositionSeries (Submodule k[G] N)) (ht : t.last = ⊤)
    (s : CompositionSeries (Submodule k[G] Q)) (hs : s.head = ⊥) :
    let t' : CompositionSeries (Submodule k[G] M) :=
      t.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩
    let s' : CompositionSeries (Submodule k[G] M) :=
      s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩
    t'.last = s'.head := by
  dsimp
  let t' : CompositionSeries (Submodule k[G] M) :=
    t.map ⟨Submodule.map f, fun {p q} h => Submodule.map_covBy_of_injective hf h⟩
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.comap g, fun {p q} h => Submodule.comap_covBy_of_surjective hg h⟩
  -- Exactness identifies `range f` with `ker g`, so the two transported series glue there.
  calc
    t'.last = Submodule.map f (⊤ : Submodule k[G] N) := by
      simpa [t'] using congrArg (Submodule.map f) ht
    _ = Submodule.comap g (⊥ : Submodule k[G] Q) := by
      rw [Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp hfg]
    _ = s'.head := by
      symm
      simpa [s'] using congrArg (Submodule.comap g) hs

/-- Helper for Exercise 16-16.4-5: smashing composition series preserves the factors coming from
the left block. -/
private noncomputable def compositionSeriesFactor_smash_left_equiv_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) (i : Fin t.length) :
    compositionSeriesFactor_local (s := t.smash s h) (i := i.castAdd s.length) ≃ₗ[k[G]]
      compositionSeriesFactor_local (s := t) (i := i) := by
  -- Compare the interval endpoints inside the smashed series and in the original left block.
  have hsucc :
      (t.smash s h) (i.castAdd s.length).succ = t i.succ := by
    simpa using (RelSeries.smash_succ_castAdd (p := t) (q := s) h i)
  let e : (t.smash s h) (i.castAdd s.length).succ ≃ₗ[k[G]] t i.succ :=
    LinearEquiv.ofEq _ _ hsucc
  have hmap :
      Submodule.map (e : (t.smash s h) (i.castAdd s.length).succ →ₗ[k[G]] t i.succ)
          (((t.smash s h) (i.castAdd s.length).castSucc).comap
            ((t.smash s h) (i.castAdd s.length).succ).subtype) =
        (t i.castSucc).comap (t i.succ).subtype := by
    ext x
    simp [e, RelSeries.smash_castAdd]
  simpa [compositionSeriesFactor_local] using
    (Submodule.Quotient.equiv
      (((t.smash s h) (i.castAdd s.length).castSucc).comap
        ((t.smash s h) (i.castAdd s.length).succ).subtype)
      ((t i.castSucc).comap (t i.succ).subtype) e hmap)

/-- Helper for Exercise 16-16.4-5: smashing composition series preserves the factors coming from
the right block. -/
private noncomputable def compositionSeriesFactor_smash_right_equiv_local
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) (i : Fin s.length) :
    compositionSeriesFactor_local (s := t.smash s h) (i := i.natAdd t.length) ≃ₗ[k[G]]
      compositionSeriesFactor_local (s := s) (i := i) := by
  -- The right block also survives unchanged after translating the endpoints through the smash.
  have hsucc :
      (t.smash s h) (i.natAdd t.length).succ = s i.succ := by
    simpa using (RelSeries.smash_succ_natAdd (p := t) (q := s) h i)
  let e : (t.smash s h) (i.natAdd t.length).succ ≃ₗ[k[G]] s i.succ :=
    LinearEquiv.ofEq _ _ hsucc
  have hmap :
      Submodule.map (e : (t.smash s h) (i.natAdd t.length).succ →ₗ[k[G]] s i.succ)
          (((t.smash s h) (i.natAdd t.length).castSucc).comap
            ((t.smash s h) (i.natAdd t.length).succ).subtype) =
        (s i.castSucc).comap (s i.succ).subtype := by
    ext x
    simp [e, -Fin.castSucc_natAdd, RelSeries.smash_natAdd]
  simpa [compositionSeriesFactor_local] using
    (Submodule.Quotient.equiv
      (((t.smash s h) (i.natAdd t.length).castSucc).comap
        ((t.smash s h) (i.natAdd t.length).succ).subtype)
      ((s i.castSucc).comap (s i.succ).subtype) e hmap)

/-- Helper for Exercise 16-16.4-5: the count of matching factors in a smashed composition series
is the sum of the counts in the two blocks. -/
private theorem simple_factor_count_series_smash_local
    {T M : Type*} [AddCommGroup T] [AddCommGroup M] [Module k[G] T]
    [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (t s : CompositionSeries (Submodule k[G] M)) (h : t.last = s.head) :
    simple_factor_count_of_module_local (T := T) (s := t.smash s h) =
      simple_factor_count_of_module_local (T := T) (s := t) +
        simple_factor_count_of_module_local (T := T) (s := s) := by
  classical
  have hpred :
      ∀ l : Fin (t.length + s.length),
        compositionSeriesFactorMatches_local (T := T) (s := t.smash s h) (i := l) ↔
          match finSumFinEquiv.symm l with
          | Sum.inl i => compositionSeriesFactorMatches_local (T := T) (s := t) (i := i)
          | Sum.inr i => compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) := by
    intro l
    cases hl : finSumFinEquiv.symm l with
    | inl i =>
        have hl' : l = i.castAdd s.length := by
          have hl'' := congrArg (fun x : Fin t.length ⊕ Fin s.length =>
            (finSumFinEquiv x : Fin (t.length + s.length))) hl
          simpa using hl''
        subst l
        simpa [finSumFinEquiv_symm_apply_castAdd] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_smash_left_equiv_local (t := t) (s := s) (h := h)
              (i := i)))
    | inr i =>
        have hl' : l = i.natAdd t.length := by
          have hl'' := congrArg (fun x : Fin t.length ⊕ Fin s.length =>
            (finSumFinEquiv x : Fin (t.length + s.length))) hl
          simpa using hl''
        subst l
        simpa [finSumFinEquiv_symm_apply_natAdd] using
          (compositionSeriesFactorMatches_iff_of_linearEquiv_local (T := T)
            (e := compositionSeriesFactor_smash_right_equiv_local (t := t) (s := s) (h := h)
              (i := i)))
  let e :
      { l : Fin (t.length + s.length) //
          compositionSeriesFactorMatches_local (T := T) (s := t.smash s h) (i := l) } ≃
        ({ i : Fin t.length //
            compositionSeriesFactorMatches_local (T := T) (s := t) (i := i) } ⊕
          { i : Fin s.length //
            compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) }) :=
    ((finSumFinEquiv.symm).subtypeEquiv hpred).trans
      (Equiv.subtypeSum
        (p := fun u : Fin t.length ⊕ Fin s.length =>
          match u with
          | Sum.inl i => compositionSeriesFactorMatches_local (T := T) (s := t) (i := i)
          | Sum.inr i => compositionSeriesFactorMatches_local (T := T) (s := s) (i := i)))
  -- The matching factors split into the disjoint left and right blocks.
  calc
    simple_factor_count_of_module_local (T := T) (s := t.smash s h) =
        Nat.card
          ({ i : Fin t.length //
              compositionSeriesFactorMatches_local (T := T) (s := t) (i := i) } ⊕
            { i : Fin s.length //
              compositionSeriesFactorMatches_local (T := T) (s := s) (i := i) }) := by
          simpa [simple_factor_count_of_module_local] using Nat.card_congr e
    _ = simple_factor_count_of_module_local (T := T) (s := t) +
        simple_factor_count_of_module_local (T := T) (s := s) := by
          rw [simple_factor_count_of_module_local, simple_factor_count_of_module_local, Nat.card_sum]

/-- Helper for Exercise 16-16.4-5: fixed-target multiplicity is additive in short exact sequences
of finite `k[G]`-modules. -/
private theorem simple_factor_multiplicity_eq_add_of_exact_local
    {T M N Q : Type*} [AddCommGroup T] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module k[G] T] [Module k M] [Module k N] [Module k Q]
    [FiniteDimensional k M] [FiniteDimensional k N] [FiniteDimensional k Q]
    [Module k[G] M] [Module k[G] N] [Module k[G] Q]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N] [IsScalarTower k k[G] Q]
    {f : N →ₗ[k[G]] M} {g : M →ₗ[k[G]] Q}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    simple_factor_multiplicity_local (A := A) (G := G) T M =
      simple_factor_multiplicity_local (A := A) (G := G) T N +
        simple_factor_multiplicity_local (A := A) (G := G) T Q := by
  let t : CompositionSeries (Submodule k[G] N) :=
    finiteLengthCompositionSeries_local (A := A) (G := G) N
  let s : CompositionSeries (Submodule k[G] Q) :=
    finiteLengthCompositionSeries_local (A := A) (G := G) Q
  let t' : CompositionSeries (Submodule k[G] M) :=
    t.map ⟨Submodule.map f, fun {_ _} h => Submodule.map_covBy_of_injective hf h⟩
  let s' : CompositionSeries (Submodule k[G] M) :=
    s.map ⟨Submodule.comap g, fun {_ _} h => Submodule.comap_covBy_of_surjective hg h⟩
  let hseam : t'.last = s'.head :=
    compositionSeries_map_last_eq_comap_head_of_exact_local
      (hf := hf) (hg := hg) (hfg := hfg)
      (t := t) (ht := finiteLengthCompositionSeries_last_local (A := A) (G := G) N)
      (s := s) (hs := finiteLengthCompositionSeries_head_local (A := A) (G := G) Q)
  let r : CompositionSeries (Submodule k[G] M) := t'.smash s' hseam
  have ht_head : t.head = ⊥ :=
    finiteLengthCompositionSeries_head_local (A := A) (G := G) N
  have hs_last : s.last = ⊤ :=
    finiteLengthCompositionSeries_last_local (A := A) (G := G) Q
  -- Route correction: prove additivity at the series level on `r := t'.smash s' hseam`, then
  -- transport back to the chosen multiplicities on the three module owners.
  calc
    simple_factor_multiplicity_local (A := A) (G := G) T M =
        simple_factor_count_of_module_local (T := T) (s := r) := by
          apply simple_factor_multiplicity_eq_count_local (A := A) (G := G) (T := T) r
          · simpa [r, t', t, ht_head, -Submodule.map_bot] using Submodule.map_bot f
          · simpa [r, s', s, hs_last, -Submodule.comap_top] using Submodule.comap_top g
    _ = simple_factor_count_of_module_local (T := T) (s := t') +
        simple_factor_count_of_module_local (T := T) (s := s') := by
          simp [r, simple_factor_count_series_smash_local]
    _ = simple_factor_count_of_module_local (T := T) (s := t) +
        simple_factor_count_of_module_local (T := T) (s := s) := by
          rw [simple_factor_count_series_map_local (T := T) (hf := hf) (s := t),
            simple_factor_count_series_comap_local (T := T) (hg := hg) (s := s)]
    _ = simple_factor_multiplicity_local (A := A) (G := G) T N +
        simple_factor_multiplicity_local (A := A) (G := G) T Q := by
          rw [← simple_factor_multiplicity_eq_count_local (A := A) (G := G) (T := T) t
              ht_head
              (finiteLengthCompositionSeries_last_local (A := A) (G := G) N),
            ← simple_factor_multiplicity_eq_count_local (A := A) (G := G) (T := T) s
              (finiteLengthCompositionSeries_head_local (A := A) (G := G) Q)
              hs_last]

/-- Helper for Exercise 16-16.4-5: fixed-simple multiplicity packaged as an additive map on the
free abelian group generated by finite-dimensional `k[G]`-representations. -/
private noncomputable abbrev simple_factor_multiplicity_lift_local
    (S : FDRep k G) :
    FreeAbelianGroup (FDRep k G) →+ ℤ :=
  FreeAbelianGroup.lift fun σ ↦
    let ρS : Representation k G S := S.ρ
    letI : Module k[G] S := by
      simpa using (inferInstance : Module k[G] ρS.asModule)
    let ρσ : Representation k G σ := σ.ρ
    letI : Module k[G] σ := by
      simpa using (inferInstance : Module k[G] ρσ.asModule)
    letI : IsScalarTower k k[G] σ := by
      simpa using (inferInstance : IsScalarTower k k[G] ρσ.asModule)
    Int.ofNat (simple_factor_multiplicity_local (A := A) (G := G) S σ)

/-- Helper for Exercise 16-16.4-5: the fixed-simple multiplicity lift vanishes on the defining
Grothendieck relations. -/
private theorem finiteRepGrothendieckRelations_le_simple_factor_multiplicity_lift_ker_local
    (S : FDRep k G) :
    finiteRepGrothendieckRelations k G ≤
      (simple_factor_multiplicity_lift_local (A := A) (G := G) S).ker := by
  let ρS : Representation k G S := S.ρ
  letI : Module k[G] S := by
    simpa using (inferInstance : Module k[G] ρS.asModule)
  refine (AddSubgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with ⟨⟨T, hT⟩, rfl⟩
  let ρ₁ : Representation k G T.X₁ := T.X₁.ρ
  let ρ₂ : Representation k G T.X₂ := T.X₂.ρ
  let ρ₃ : Representation k G T.X₃ := T.X₃.ρ
  letI : Module k[G] T.X₁ := by
    simpa using (inferInstance : Module k[G] ρ₁.asModule)
  letI : Module k[G] T.X₂ := by
    simpa using (inferInstance : Module k[G] ρ₂.asModule)
  letI : Module k[G] T.X₃ := by
    simpa using (inferInstance : Module k[G] ρ₃.asModule)
  letI : IsScalarTower k k[G] T.X₁ := by
    simpa using (inferInstance : IsScalarTower k k[G] ρ₁.asModule)
  letI : IsScalarTower k k[G] T.X₂ := by
    simpa using (inferInstance : IsScalarTower k k[G] ρ₂.asModule)
  letI : IsScalarTower k k[G] T.X₃ := by
    simpa using (inferInstance : IsScalarTower k k[G] ρ₃.asModule)
  let F : FDRep k G ⥤ ModuleCat k[G] :=
    forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra
  let U : ShortComplex (ModuleCat k[G]) := T.map F
  have hU : U.ShortExact := hT.map_of_exact F
  let f : T.X₁ →ₗ[k[G]] T.X₂ := by
    simpa [U, F] using U.f.hom
  let g : T.X₂ →ₗ[k[G]] T.X₃ := by
    simpa [U, F] using U.g.hom
  have hf : Function.Injective f := by
    simpa [f] using hU.moduleCat_injective_f
  have hg : Function.Surjective g := by
    simpa [g] using hU.moduleCat_surjective_g
  have hfg : Function.Exact f g := by
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact
  have hadd :
      simple_factor_multiplicity_local (A := A) (G := G) S T.X₂ =
        simple_factor_multiplicity_local (A := A) (G := G) S T.X₁ +
          simple_factor_multiplicity_local (A := A) (G := G) S T.X₃ := by
    -- Transport the defining short exact sequence to the owner `k[G]`-module carriers and apply
    -- additivity of fixed-simple multiplicity.
    simpa using
      (simple_factor_multiplicity_eq_add_of_exact_local
        (A := A) (G := G) (T := S) hf hg hfg)
  change
    simple_factor_multiplicity_lift_local (A := A) (G := G) S
        (FreeAbelianGroup.of T.X₂ - FreeAbelianGroup.of T.X₁ - FreeAbelianGroup.of T.X₃) = 0
  -- After evaluating the free-abelian-group lift on each generator, the exact-sequence
  -- additivity identity cancels the defining relation.
  simp [simple_factor_multiplicity_lift_local, hadd, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 16-16.4-5: the fixed-simple multiplicity descends to Serre's
Grothendieck group. -/
private noncomputable def simple_factor_multiplicity_hom_fixed_local
    (S : FDRep k G) :
    R₀[k](G) →+ ℤ :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (simple_factor_multiplicity_lift_local (A := A) (G := G) S)
    (finiteRepGrothendieckRelations_le_simple_factor_multiplicity_lift_ker_local
      (A := A) (G := G) S)

/-- Helper for Exercise 16-16.4-5: a subtype of `Fin 1` is either empty or has one element,
according to whether the unique index satisfies the defining predicate. -/
private theorem nat_card_subtype_fin_one_eq_ite_local
    (P : Fin 1 → Prop) [DecidablePred P] :
    Nat.card { i : Fin 1 // P i } = if P 0 then 1 else 0 := by
  classical
  by_cases h : P 0
  · have hAll : ∀ i : Fin 1, P i := by
      intro i
      simpa [Fin.eq_zero i] using h
    letI : Unique { i : Fin 1 // P i } :=
      ⟨⟨0, h⟩, fun x => by
        rcases x with ⟨i, hi⟩
        simp [Fin.eq_zero i]⟩
    simp [h]
  · have hNone : ∀ i : Fin 1, ¬ P i := by
      intro i
      simpa [Fin.eq_zero i] using h
    haveI : IsEmpty { i : Fin 1 // P i } := ⟨fun x => hNone x.1 x.2⟩
    simp [h]

/-- Helper for Exercise 16-16.4-5: the fixed-simple multiplicity hom evaluates on a simple class
as the expected Kronecker delta. -/
private theorem simple_factor_multiplicity_hom_apply_simple_local
    (τ σ : FDRep k G) [Simple σ] [Decidable (Nonempty (σ ≅ τ))] :
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) τ [σ]₀ =
      if Nonempty (σ ≅ τ) then 1 else 0 := by
  let ρτ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    simpa using (inferInstance : Module k[G] ρτ.asModule)
  let ρσ : Representation k G σ := σ.ρ
  letI : Module k[G] σ := by
    simpa using (inferInstance : Module k[G] ρσ.asModule)
  letI : IsScalarTower k k[G] σ := by
    simpa using (inferInstance : IsScalarTower k k[G] ρσ.asModule)
  have hsimple : IsSimpleModule k[G] σ := by
    letI : Representation.IsIrreducible ρσ := by
      simpa [ρσ] using (FDRep.isIrreducible_of_simple σ)
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule ρσ).mp inferInstance
  have hcov : (⊥ : Submodule k[G] σ) ⋖ ⊤ := by
    -- Route correction: compute the simple-case multiplicity on the explicit `⊥ < ⊤` series.
    rw [covBy_iff_quot_is_simple bot_le]
    let eTop :
        ((⊤ : Submodule k[G] σ) ⧸
          Submodule.comap (Submodule.subtype (⊤ : Submodule k[G] σ))
            (⊥ : Submodule k[G] σ)) ≃ₗ[k[G]] σ :=
      (Submodule.quotEquivOfEqBot _ (by simp)).trans Submodule.topEquiv
    exact (LinearEquiv.isSimpleModule_iff eTop).2 hsimple
  let s : CompositionSeries (Submodule k[G] σ) :=
    (RelSeries.singleton _ (⊥ : Submodule k[G] σ)).snoc ⊤ hcov
  have hs_head : s.head = ⊥ := by
    simpa [s] using
      (RelSeries.head_snoc (RelSeries.singleton _ (⊥ : Submodule k[G] σ)) ⊤ hcov)
  have hs_last : s.last = ⊤ := by
    simpa [s] using
      (RelSeries.last_snoc (RelSeries.singleton _ (⊥ : Submodule k[G] σ)) ⊤ hcov)
  have hslen : s.length = 1 := by
    simp [s]
  let i0 : Fin s.length := hslen.symm ▸ (0 : Fin 1)
  have hmult :
      simple_factor_multiplicity_local (A := A) (G := G) τ σ =
        simple_factor_count_of_module_local (T := τ) (s := s) := by
    exact
      simple_factor_multiplicity_eq_count_local
        (A := A) (G := G) (T := τ) s hs_head hs_last
  have hfactor_equiv :
      compositionSeriesFactor_local (s := s) (i := i0) ≃ₗ[k[G]] σ := by
    simpa [s, i0, hslen, compositionSeriesFactor_local] using
      ((Submodule.quotEquivOfEqBot
          (Submodule.comap (Submodule.subtype (⊤ : Submodule k[G] σ))
            (⊥ : Submodule k[G] σ)) (by simp)).trans
        (Submodule.topEquiv.trans (LinearEquiv.refl k[G] σ)))
  have hmatch :
      compositionSeriesFactorMatches_local (T := τ) (s := s) (i := i0) ↔
        Nonempty (σ ≅ τ) := by
    constructor
    · intro h
      rcases h with ⟨e⟩
      simpa using
        (fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv
          (A := A) (G := G) (σ := σ) (τ := τ) ⟨hfactor_equiv.symm.trans e⟩)
    · intro h
      rcases h with ⟨e⟩
      exact ⟨hfactor_equiv.trans
        (by
          simpa using
            ((((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso e).toLinearEquiv))⟩
  have hcount :
      simple_factor_count_of_module_local (T := τ) (s := s) =
        if Nonempty (σ ≅ τ) then 1 else 0 := by
    classical
    let P : Fin 1 → Prop := fun i ↦
      compositionSeriesFactorMatches_local (T := τ) (s := s) (i := hslen.symm ▸ i)
    let eCount :
        { i : Fin s.length //
            compositionSeriesFactorMatches_local (T := τ) (s := s) (i := i) } ≃
          { i : Fin 1 // P i } :=
      { toFun := fun i => ⟨Equiv.cast (congrArg Fin hslen) i.1, by simpa [P] using i.2⟩
        invFun := fun i => ⟨Equiv.cast (congrArg Fin hslen.symm) i.1, by simpa [P] using i.2⟩
        left_inv := fun i => by
          rcases i with ⟨i, hi⟩
          simp
        right_inv := fun i => by
          rcases i with ⟨i, hi⟩
          simp }
    have hP : ∀ i : Fin 1, P i ↔ Nonempty (σ ≅ τ) := by
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa [P, i0] using hmatch
    calc
      simple_factor_count_of_module_local (T := τ) (s := s) = Nat.card { i : Fin 1 // P i } := by
        rw [simple_factor_count_of_module_local]
        exact Nat.card_congr eCount
      _ = if P 0 then 1 else 0 := nat_card_subtype_fin_one_eq_ite_local P
      _ = if Nonempty (σ ≅ τ) then 1 else 0 := by
            simp [hP 0]
  -- Evaluate the descended map on `[σ]₀`, rewrite the multiplicity through the explicit simple
  -- two-step series, and then count the unique Jordan-Hölder factor.
  calc
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) τ [σ]₀ =
        simple_factor_multiplicity_lift_local (A := A) (G := G) τ (FreeAbelianGroup.of σ) := by
          simp [simple_factor_multiplicity_hom_fixed_local, finiteRepGrothendieckClass]
    _ = Int.ofNat (simple_factor_multiplicity_local (A := A) (G := G) τ σ) := by
          simp [simple_factor_multiplicity_lift_local]
    _ = Int.ofNat (simple_factor_count_of_module_local (T := τ) (s := s)) := by
          rw [hmult]
    _ = if Nonempty (σ ≅ τ) then 1 else 0 := by
          simp [hcount]

/-- Helper for Exercise 16-16.4-5: on the chosen complete simple family, the fixed-simple
multiplicity hom is the Kronecker-delta functional at the distinguished index `iS`. -/
private theorem simple_factor_multiplicity_hom_apply_simple_family_local
    (S : FDRep k G) [Simple S]
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι)
    (hS_iso : Nonempty (π iS ≅ S))
    (j : ι) :
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S [π j]₀ =
      if j = iS then 1 else 0 := by
  classical
  letI : Simple (π j) := hπ_complete.isSimple j
  have hdelta :
      (if Nonempty (π j ≅ S) then 1 else 0 : ℤ) = if j = iS then 1 else 0 := by
    by_cases hj : j = iS
    · subst hj
      simp [hS_iso]
    · have hnot : ¬ Nonempty (π j ≅ S) := by
        intro h
        rcases h with ⟨e⟩
        rcases hS_iso with ⟨eS⟩
        exact hπ_pairwise hj (⟨e.trans eS.symm⟩)
      simp [hj, hnot]
  simpa [hdelta] using
    (simple_factor_multiplicity_hom_apply_simple_local
      (A := A) (G := G) (τ := S) (σ := π j))

/-- Helper for Exercise 16-16.4-5: the fixed-simple multiplicity hom agrees with the coordinate
functional in the canonical simple-class basis. -/
private theorem simple_factor_multiplicity_hom_eq_simple_basis_coord_local
    (S : FDRep k G) [Simple S]
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι)
    (hS_iso : Nonempty (π iS ≅ S))
    (x : R₀[k](G)) :
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S x =
      (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr x iS := by
  classical
  let b :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let coord : R₀[k](G) →+ ℤ :=
    { toFun := fun y ↦ b.repr y iS
      map_zero' := by simp
      map_add' := by
        intro y z
        simp }
  have hbasis :
      ∀ j, simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S (b j) =
        coord (b j) := by
    intro j
    have hleft :
        simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S (b j) =
          if j = iS then 1 else 0 := by
      simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
        (simple_factor_multiplicity_hom_apply_simple_family_local
          (A := A) (G := G) S π hπ_pairwise hπ_complete iS hS_iso j)
    have hright :
        coord (b j) = if j = iS then 1 else 0 := by
      have hb : b.repr (b j) = Finsupp.single j (1 : ℤ) := by
        simpa using b.repr_self j
      have hbi := congrArg (fun c : ι →₀ ℤ => c iS) hb
      simpa [coord, Finsupp.single_apply] using hbi
    exact hleft.trans hright.symm
  have hhom :
      (simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) S).toIntLinearMap =
        coord.toIntLinearMap := by
    apply b.ext
    intro j
    exact hbasis j
  simpa using congrArg (fun f : R₀[k](G) →ₗ[ℤ] ℤ ↦ f x) hhom

/-- Helper for Exercise 16-16.4-5: under nonprojectivity of the fixed simple `S`, the remaining
source-faithful bridge is to identify the diagonal Cartan entry with the composition-factor count
in the chosen projective envelope and deduce the lower bound `2 ≤ C_SS`. -/
theorem cartan_diagonal_ge_two_of_nonprojective_simple_count_bridge
    (S : FDRep k G) [Simple S]
    {ι : Type x} [Fintype ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι)
    (hS_iso : Nonempty (π iS ≅ S))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hS_not_projective : ¬ Module.Projective k[G] (asModule S.ρ)) :
    (2 : ℤ) ≤
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete)
        iS iS := by
  classical
  rcases hP_envelope iS with ⟨f, hf⟩
  rcases hS_iso with ⟨eS⟩
  let τ := π iS
  let ρτ : Representation k G τ := τ.ρ
  letI : Simple τ := hπ_complete.isSimple iS
  letI : Module k[G] τ := by
    simpa [τ, ρτ] using (inferInstance : Module k[G] ρτ.asModule)
  letI : IsScalarTower k k[G] τ := by
    simpa [τ, ρτ] using (inferInstance : IsScalarTower k k[G] ρτ.asModule)
  have hτsimple : IsSimpleModule k[G] τ := by
    letI : Representation.IsIrreducible τ.ρ := by
      simpa [τ] using FDRep.isIrreducible_of_simple τ
    simpa [τ, ρτ] using
      (Representation.irreducible_iff_isSimpleModule_asModule τ.ρ).mp inferInstance
  let Mτ : ModuleCat k[G] := fdRepAsModule_local (τ := τ)
  let fτ₀ : (P iS).V →ₗ[k[G]] Mτ := by
    simpa [fdRepAsModule_local, τ, ρτ] using f
  have hfτ₀ : fτ₀.IsProjectiveEnvelope := by
    simpa [fτ₀, fdRepAsModule_local, τ, ρτ] using hf
  let eτ : Mτ ≃ₗ[k[G]] τ := by
    simpa [fdRepAsModule_local, τ, ρτ] using (LinearEquiv.refl k[G] τ)
  let fτ : (P iS).V →ₗ[k[G]] τ := eτ.toLinearMap.comp fτ₀
  have hfτ : fτ.IsProjectiveEnvelope := by
    let _ : Module.Projective k[G] (P iS).V := hfτ₀.toProjective
    let _ : fτ.IsEssential := by
      exact
        (LinearMap.isEssential_iff_conj (R := k[G])
          (LinearEquiv.refl k[G] (P iS).V) eτ).2 hfτ₀.toIsEssential
    refine LinearMap.IsProjectiveEnvelope.mk ?_
    intro y
    rcases hfτ₀.surjective (eτ.symm y) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change eτ (fτ₀ x) = y
    simpa [hx]
  let eMod : τ ≃ₗ[k[G]] asModule S.ρ := by
    simpa [τ, ρτ] using
      (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso eS).toLinearEquiv
  have hτ_not_projective : ¬ Module.Projective k[G] τ := by
    intro hτproj
    have hSproj : Module.Projective k[G] (asModule S.ρ) := by
      let _ : Module.Projective k[G] τ := hτproj
      exact Module.Projective.of_equiv' eMod
    exact hS_not_projective hSproj
  let _ : Module.Finite k[G] (P iS).V :=
    moduleFinite_of_projectiveEnvelope_simple_local (A := A) (G := G) hfτ
  let σ : FDRep k G := (P iS).toFiniteRep
  let ρσ : Representation k G σ := σ.ρ
  letI : Module k[G] σ := by
    simpa [σ, ρσ, FiniteProjectiveGroupAlgebraModule.toRep] using
      (inferInstance : Module k[G] (P iS).V)
  letI : IsScalarTower k k[G] σ := by
    simpa [σ, ρσ, FiniteProjectiveGroupAlgebraModule.toRep] using
      (inferInstance : IsScalarTower k k[G] (P iS).V)
  let fσ : σ →ₗ[k[G]] τ := by
    simpa [σ, ρσ, FiniteProjectiveGroupAlgebraModule.toRep] using fτ
  have hfσ : fσ.IsProjectiveEnvelope := by
    simpa [fσ, σ, ρσ, FiniteProjectiveGroupAlgebraModule.toRep] using hfτ
  let s : CompositionSeries (Submodule k[G] σ) :=
    finiteLengthCompositionSeries_local (A := A) (G := G) σ
  have hcount : 2 ≤ simple_factor_count_of_module_local (T := τ) (s := s) := by
    have hs_head : s.head = ⊥ := by
      simpa [s] using finiteLengthCompositionSeries_head_local (A := A) (G := G) σ
    have hs_last : s.last = ⊤ := by
      simpa [s] using finiteLengthCompositionSeries_last_local (A := A) (G := G) σ
    exact
      simple_factor_count_ge_two_of_nonprojective_projectiveEnvelope_local
        (A := A) (G := G) (f := fσ) (s := s) hτsimple hfσ hs_head hs_last hτ_not_projective
  have hmult :
      (2 : ℤ) ≤
        simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) τ
          [((P iS).toFiniteRep)]₀ := by
    have hmult_nat :
        2 ≤ simple_factor_multiplicity_local (A := A) (G := G) τ σ := by
      have hs_head : s.head = ⊥ := by
        simpa [s] using finiteLengthCompositionSeries_head_local (A := A) (G := G) σ
      have hs_last : s.last = ⊤ := by
        simpa [s] using finiteLengthCompositionSeries_last_local (A := A) (G := G) σ
      rw [simple_factor_multiplicity_eq_count_local (A := A) (G := G) (T := τ)
        (M := σ) s hs_head hs_last]
      exact hcount
    have hmult_int :
        (2 : ℤ) ≤ Int.ofNat (simple_factor_multiplicity_local (A := A) (G := G) τ σ) := by
      have hmult_int' :
          (2 : ℤ) ≤ (simple_factor_multiplicity_local (A := A) (G := G) τ σ : ℤ) := by
        exact_mod_cast hmult_nat
      simpa using hmult_int'
    simp [simple_factor_multiplicity_hom_fixed_local, finiteRepGrothendieckClass,
      simple_factor_multiplicity_lift_local, σ, FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep]
    have hmult_nat' :
        2 ≤ simple_factor_multiplicity_local (A := A) (G := G) τ (P iS).toRep := by
      simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
        FiniteProjectiveGroupAlgebraModule.toRep] using hmult_nat
    have hmτ : this✝² = (inferInstance : Module k[G] ↑τ.V) := Subsingleton.elim _ _
    have hmP : this✝ = (inferInstance : Module k[G] (P iS).toRep) := Subsingleton.elim _ _
    have hmTower : this = (inferInstance : IsScalarTower k k[G] (P iS).toRep) :=
      Subsingleton.elim _ _
    simpa [hmτ, hmP, hmTower] using hmult_nat'
  let b :=
    simple_finiteRep_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete
  have hcoord :
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) τ
          (cartanHom k G [P iS]ₚ₀) =
        cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          b iS iS := by
    calc
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) τ
          (cartanHom k G [P iS]ₚ₀) =
        b.repr (cartanHom k G [P iS]ₚ₀) iS := by
          simpa [τ, b] using
            (simple_factor_multiplicity_hom_eq_simple_basis_coord_local
              (A := A) (G := G) τ π hπ_pairwise hπ_complete iS ⟨Iso.refl _⟩
              (cartanHom k G [P iS]ₚ₀))
      _ =
        cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          b iS iS := by
            simp only [cartanMatrix, LinearMap.toMatrix_apply]
            rw [projectiveEnvelope_classes_basis_of_complete_family_apply]
            rfl
  calc
    (2 : ℤ) ≤ simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) τ
        (cartanHom k G [P iS]ₚ₀) := by
          simpa [τ, cartanHom_projectiveClass_eq] using hmult
    _ =
        cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete)
          iS iS := hcoord

/-- Helper for Exercise 16-16.4-5: if the fixed simple `S` is not projective, then the matching
diagonal Cartan entry cannot be `1`. -/
theorem cartan_diagonal_ne_one_of_nonprojective_simple_local
    (S : FDRep k G) [Simple S]
    {ι : Type x} [Fintype ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (iS : ι)
    (hS_iso : Nonempty (π iS ≅ S))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hS_not_projective : ¬ Module.Projective k[G] (asModule S.ρ)) :
    cartanMatrix k G
      (projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope)
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete)
      iS iS ≠ 1 := by
  have hdiag_ge_two :
      (2 : ℤ) ≤
        cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete)
          iS iS :=
    cartan_diagonal_ge_two_of_nonprojective_simple_count_bridge
      (A := A) (G := G) S π hπ_pairwise hπ_complete iS hS_iso P hP_envelope
      hS_not_projective
  intro hdiag
  -- The lower bound `2 ≤ C_SS` contradicts the assumption `C_SS = 1`.
  have : ¬ (2 : ℤ) ≤ 1 := by norm_num
  exact this (hdiag ▸ hdiag_ge_two)

section StableLatticeModuleBridgeLocal

variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

/-- Helper for Exercise 16-16.4-5: the underlying `A`-submodule of a stable lattice carries the
induced `A[G]`-module structure. -/
private instance stableLattice_toSubmodule_module_local
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    Module A[G] L.toSubmodule := by
  change Module A[G] L.toRepresentation.asModule
  infer_instance

/-- Helper for Exercise 16-16.4-5: the induced `A[G]`-module structure on a stable lattice is
compatible with restriction of scalars from `A`. -/
private instance stableLattice_toSubmodule_isScalarTower_local
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    IsScalarTower A A[G] L.toSubmodule := by
  change IsScalarTower A A[G] L.toRepresentation.asModule
  infer_instance

end StableLatticeModuleBridgeLocal

/-- Helper for Exercise 16-16.4-5: the literal scalar-extension map sends `x` to the pure tensor
`1 ⊗ x` inside `Q.scalarExtension K`. -/
private abbrev projective_scalarExtension_literal_map_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A] K ⊗[A] Q.V :=
  TensorProduct.mk A K Q.V 1

/-- Helper for Exercise 16-16.4-5: over the fraction field, the literal map `x ↦ 1 ⊗ x` is
injective. -/
private theorem projective_scalarExtension_literal_map_injective_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Injective
      (projective_scalarExtension_literal_map_local (A := A) (K := K) (G := G) Q) := by
  intro x y hxy
  letI : Module.Free A Q.V := Q.free
  let b : Module.Basis (Module.Free.ChooseBasisIndex A Q.V) A Q.V :=
    Module.Free.chooseBasis A Q.V
  apply b.repr.injective
  ext i
  have hcoord :=
    congrArg (fun z ↦ ((Algebra.TensorProduct.basis K b).repr z) i) hxy
  apply (IsFractionRing.injective A K)
  simpa using hcoord

/-- Helper for Exercise 16-16.4-5: the image of `x ↦ 1 ⊗ x` is stable under the scalar-extended
`G`-action. -/
private theorem projective_scalarExtension_literal_map_apply_mem_range_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (g : G) {x : K ⊗[A] Q.V}
    (hx :
      x ∈
        (projective_scalarExtension_literal_map_local
          (A := A) (K := K) (G := G) Q).range) :
    (Q.scalarExtension K).ρ g x ∈
      (projective_scalarExtension_literal_map_local
        (A := A) (K := K) (G := G) Q).range := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨Q.toRep.ρ g y, ?_⟩
  change
    ((Module.End.baseChangeHom A K Q.V) (Q.toRep.ρ g)) (1 ⊗ₜ[A] y) =
      1 ⊗ₜ[A] Q.toRep.ρ g y
  exact LinearMap.baseChange_tmul (f := Q.toRep.ρ g) (A := K) 1 y

/-- Helper for Exercise 16-16.4-5: the literal image of `Q.V` inside `Q.scalarExtension K`
spans the scalar extension over `K` and is finite over `A`, hence is a stable lattice. -/
private theorem projective_scalarExtension_literal_map_range_isLattice_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Submodule.IsLattice K
      ((projective_scalarExtension_literal_map_local
        (A := A) (K := K) (G := G) Q).range) := by
  refine
    { fg := ?_
      span_eq_top := ?_ }
  · have hfg_top : (⊤ : Submodule A Q.V).FG := by
      exact (Module.Finite.iff_fg (N := (⊤ : Submodule A Q.V))).1 inferInstance
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map
      (projective_scalarExtension_literal_map_local
        (A := A) (K := K) (G := G) Q) hfg_top
  · letI : Module.Free A Q.V := Q.free
    let b : Module.Basis (Module.Free.ChooseBasisIndex A Q.V) A Q.V :=
      Module.Free.chooseBasis A Q.V
    apply eq_top_iff.2
    intro x hx
    have hxrepr : x = ∑ i, ((Algebra.TensorProduct.basis K b).repr x) i •
        (Algebra.TensorProduct.basis K b) i := by
      simpa using ((Algebra.TensorProduct.basis K b).sum_repr x).symm
    rw [hxrepr]
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hi' :
        (Algebra.TensorProduct.basis K b) i ∈
          Submodule.span K
            (((projective_scalarExtension_literal_map_local
                (A := A) (K := K) (G := G) Q).range :
                Submodule A (K ⊗[A] Q.V)) :
              Set (K ⊗[A] Q.V)) := by
      apply Submodule.subset_span
      refine ⟨b i, ?_⟩
      simpa [projective_scalarExtension_literal_map_local] using
        (Algebra.TensorProduct.basis_apply (A := K) (b := b) i)
    exact Submodule.smul_mem _ _ hi'

/-- Helper for Exercise 16-16.4-5: the literal image of `Q.V` inside `Q.scalarExtension K`
defines the stable lattice used in Serre's honest-projective calculation. -/
private noncomputable def projective_scalarExtension_literal_stableLattice_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (Q.scalarExtension K).ρ :=
  { toSubmodule :=
      (projective_scalarExtension_literal_map_local
        (A := A) (K := K) (G := G) Q).range
    apply_mem_toSubmodule :=
      projective_scalarExtension_literal_map_apply_mem_range_local
        (A := A) (K := K) (G := G) Q
    isLattice :=
      projective_scalarExtension_literal_map_range_isLattice_local
        (A := A) (K := K) (G := G) Q }

/-- Helper for Exercise 16-16.4-5: restricting the literal map to the stable-lattice range keeps
the exact owner used later in the projective comparison. -/
private noncomputable def projective_scalarExtension_literal_rangeRestrictLinearMap_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A]
      (projective_scalarExtension_literal_stableLattice_local
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  (projective_scalarExtension_literal_map_local
    (A := A) (K := K) (G := G) Q).rangeRestrict

/-- Helper for Exercise 16-16.4-5: restricting the literal map to its image is bijective. -/
private theorem projective_scalarExtension_literal_map_rangeRestrict_bijective_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Bijective
      (projective_scalarExtension_literal_map_local
        (A := A) (K := K) (G := G) Q).rangeRestrict := by
  constructor
  · exact
      (LinearMap.injective_rangeRestrict_iff
        (f := projective_scalarExtension_literal_map_local
          (A := A) (K := K) (G := G) Q)).2
        (projective_scalarExtension_literal_map_injective_local
          (A := A) (K := K) (G := G) Q)
  · exact LinearMap.surjective_rangeRestrict
      (projective_scalarExtension_literal_map_local
        (A := A) (K := K) (G := G) Q)

/-- Helper for Exercise 16-16.4-5: the literal source module `Q.V` identifies `A`-linearly with
its image inside `Q.scalarExtension K`. -/
private noncomputable def projective_scalarExtension_literal_rangeEquiv_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V ≃ₗ[A]
      (projective_scalarExtension_literal_stableLattice_local
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  LinearEquiv.ofBijective
    (projective_scalarExtension_literal_map_local
      (A := A) (K := K) (G := G) Q).rangeRestrict
    (projective_scalarExtension_literal_map_rangeRestrict_bijective_local
      (A := A) (K := K) (G := G) Q)

/-- Helper for Exercise 16-16.4-5: the `A`-linear identification with the literal range is in
fact `A[G]`-linear on the subgroup generators. -/
private theorem projective_scalarExtension_literal_rangeRestrict_map_of_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (g : G) (x : Q.V) :
    projective_scalarExtension_literal_rangeRestrictLinearMap_local
        (A := A) (K := K) (G := G) Q ((MonoidAlgebra.of A G g) • x) =
      (MonoidAlgebra.of A G g) •
        projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q x := by
  apply Subtype.ext
  rw [StableLattice.toRepresentation_monoidAlgebra_of_smul
    (L := projective_scalarExtension_literal_stableLattice_local
      (A := A) (K := K) (G := G) Q) g
    (projective_scalarExtension_literal_rangeRestrictLinearMap_local
      (A := A) (K := K) (G := G) Q x)]
  have hrestrict :
      ↑(projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q x) =
        TensorProduct.mk A K Q.V 1 x := by
    rfl
  calc
    ↑(projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q ((MonoidAlgebra.of A G g) • x)) =
        TensorProduct.mk A K Q.V 1 ((MonoidAlgebra.of A G g) • x) := by
          rfl
    _ =
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (MonoidAlgebra.of A G g)) •
          TensorProduct.mk A K Q.V 1 x := by
            simpa [MonoidAlgebra.of_apply] using
              (monoidAlgebra_of_smul_tmul
                (Λ := A) (P := Q.V) (κ := K) g (1 : K) x).symm
    _ =
        ((Q.scalarExtension K).ρ g)
          (TensorProduct.mk A K Q.V 1 x) := by
            simpa [MonoidAlgebra.of_apply] using
              (Representation.single_smul
                (ρ := (Q.scalarExtension K).ρ)
                (t := (1 : K)) (g := g) (v := TensorProduct.mk A K Q.V 1 x))
    _ =
        ((Q.scalarExtension K).ρ g)
          ↑(projective_scalarExtension_literal_rangeRestrictLinearMap_local
            (A := A) (K := K) (G := G) Q x) := by
              rw [hrestrict]
    _ =
        ↑((projective_scalarExtension_literal_stableLattice_local
            (A := A) (K := K) (G := G) Q).toRepresentation g
          (projective_scalarExtension_literal_rangeRestrictLinearMap_local
            (A := A) (K := K) (G := G) Q x)) := by
              rfl

/-- Helper for Exercise 16-16.4-5: the range-restricted literal map intertwines the
`A[G]`-action on `Q.V` with the induced action on the literal-range subtype. -/
private theorem projective_scalarExtension_literal_rangeRestrict_map_groupAlgebra_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (r : A[G]) (x : Q.V) :
    projective_scalarExtension_literal_rangeRestrictLinearMap_local
        (A := A) (K := K) (G := G) Q (r • x) =
      r • projective_scalarExtension_literal_rangeRestrictLinearMap_local
        (A := A) (K := K) (G := G) Q x := by
  refine MonoidAlgebra.induction_on
    (p := fun a : A[G] =>
      projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q (a • x) =
        a • projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q x) r ?_ ?_ ?_
  · intro g
    simpa using
      projective_scalarExtension_literal_rangeRestrict_map_of_local
        (A := A) (K := K) (G := G) Q g x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    calc
      projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q ((c • a) • x) =
        projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q (c • (a • x)) := by
            simpa [smul_smul]
      _ =
        c • projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q (a • x) := by
            simp
      _ =
        c • (a • projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q x) := by
            rw [ha]
      _ =
        (c • a) • projective_scalarExtension_literal_rangeRestrictLinearMap_local
          (A := A) (K := K) (G := G) Q x := by
            simpa using
              (smul_assoc c a
                (projective_scalarExtension_literal_rangeRestrictLinearMap_local
                  (A := A) (K := K) (G := G) Q x)).symm

/-- Helper for Exercise 16-16.4-5: the `A`-linear identification with the literal range is in
fact `A[G]`-linear. -/
private theorem projective_scalarExtension_literal_rangeEquiv_map_groupAlgebra_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (r : A[G]) (x : Q.V) :
    projective_scalarExtension_literal_rangeEquiv_local
      (A := A) (K := K) (G := G) Q (r • x) =
      r • projective_scalarExtension_literal_rangeEquiv_local
        (A := A) (K := K) (G := G) Q x := by
  have hrestrict :=
    projective_scalarExtension_literal_rangeRestrict_map_groupAlgebra_local
      (A := A) (K := K) (G := G) (Q := Q) (r := r) (x := x)
  simpa [projective_scalarExtension_literal_rangeEquiv_local,
    projective_scalarExtension_literal_rangeRestrictLinearMap_local] using hrestrict

/-- Helper for Exercise 16-16.4-5: the literal source module `Q.V` identifies with the lattice
range as an `A[G]`-module. -/
private noncomputable def projective_scalarExtension_literal_rangeLinearEquiv_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V ≃ₗ[A[G]]
      (projective_scalarExtension_literal_stableLattice_local
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  { toFun :=
      projective_scalarExtension_literal_rangeEquiv_local
        (A := A) (K := K) (G := G) Q
    map_add' := by
      intro x y
      exact
        (projective_scalarExtension_literal_rangeEquiv_local
          (A := A) (K := K) (G := G) Q).map_add x y
    map_smul' :=
      projective_scalarExtension_literal_rangeEquiv_map_groupAlgebra_local
        (A := A) (K := K) (G := G) Q
    invFun :=
      (projective_scalarExtension_literal_rangeEquiv_local
        (A := A) (K := K) (G := G) Q).symm
    left_inv :=
      (projective_scalarExtension_literal_rangeEquiv_local
        (A := A) (K := K) (G := G) Q).left_inv
    right_inv :=
      (projective_scalarExtension_literal_rangeEquiv_local
        (A := A) (K := K) (G := G) Q).right_inv }

/-- Helper for Exercise 16-16.4-5: the literal lattice range is projective over `A[G]` because it
is `A[G]`-linearly equivalent to `Q.V`. -/
private theorem projective_scalarExtension_literal_range_projective_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module.Projective A[G]
      (projective_scalarExtension_literal_stableLattice_local
        (A := A) (K := K) (G := G) Q).toSubmodule := by
  let e :=
    projective_scalarExtension_literal_rangeLinearEquiv_local
      (A := A) (K := K) (G := G) Q
  exact Module.Projective.of_equiv' e

/-- Helper for Exercise 16-16.4-5: the reduction of the literal stable lattice is isomorphic, as a
`k[G]`-representation, to the intrinsic residue-field reduction of `Q`. -/
private theorem projective_scalarExtension_literal_stableLattice_reduction_iso_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      Nonempty (FDRep.of L.reductionRepresentation ≅ Q.residueFieldReduction.toFiniteRep) := by
  set_option maxHeartbeats 400000 in
  let L :=
    projective_scalarExtension_literal_stableLattice_local
      (A := A) (K := K) (G := G) Q
  let eAQ :=
    projective_scalarExtension_literal_rangeLinearEquiv_local
      (A := A) (K := K) (G := G) Q
  have hprojQ : Module.Projective A[G] Q.V := by infer_instance
  have hprojL : Module.Projective A[G] L.toSubmodule :=
    projective_scalarExtension_literal_range_projective_local
      (A := A) (K := K) (G := G) Q
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  have hAQ :
      Nonempty (Q.V ≃ₗ[A[G]] L.toSubmodule) := ⟨eAQ⟩
  have hred : Nonempty (L.reduction ≃ₗ[k[G]] (k ⊗[A] Q.V)) := by
    rcases
        (projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
          (Λ := A) (G := G)
          (P := Q.V)
          (Pbar := k ⊗[A] Q.V)
          (f := TensorProduct.mk A k Q.V 1)
          (hf := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
            (Λ := A) (G := G) (P := Q.V))
          (P' := L.toSubmodule)
          (Pbar' := L.reduction)
          (f' := (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction))
          (hf' := L.reduction_mkQ_isResidueFieldReduction)
          hprojQ hprojL).mp hAQ with
      ⟨e⟩
    exact ⟨e.symm⟩
  have hred' : Nonempty (L.reduction ≃ₗ[k[G]] Q.residueFieldReduction.V) := by
    simpa using hred
  rcases hred' with ⟨ered⟩
  let σ : FDRep k G := FDRep.of L.reductionRepresentation
  let τ : FDRep k G := Q.residueFieldReduction.toFiniteRep
  let eRep' : Rep.ofModuleMonoidAlgebra.obj (ModuleCat.of k[G] L.reduction) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj τ) := by
    simpa [τ, FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.toFiniteRep, FiniteProjectiveGroupAlgebraModule.toRep]
      using Rep.ofModuleMonoidAlgebra.mapIso ered.toModuleIso
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≪≫ eRep'
  have hFD :
      Nonempty (FDRep.of L.reductionRepresentation ≅ Q.residueFieldReduction.toFiniteRep) := by
    refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
      (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  exact ⟨L, hFD⟩

/-- Helper for Exercise 16-16.4-5: a stable lattice in `Q.scalarExtension K` can be chosen so that
its reduction class matches the intrinsic residue-field reduction of `Q`. -/
theorem projective_scalarExtension_literal_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  obtain ⟨L, hLQ⟩ :=
    projective_scalarExtension_literal_stableLattice_reduction_iso_local
      (A := A) (K := K) (G := G) Q
  refine ⟨L, ?_⟩
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hLQ

/-- Helper for Exercise 16-16.4-5: a finite-dimensional representation with the same
Grothendieck class as a fixed semisimple simple one is itself isomorphic to that simple
representation. -/
theorem projective_scalarExtension_literal_reduction_iso_local
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (S : FDRep k G) [Simple S]
    (hQredS : Nonempty (Q.residueFieldReduction.toFiniteRep ≅ S)) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      Nonempty (FDRep.of L.reductionRepresentation ≅ S) := by
  rcases
      projective_scalarExtension_literal_stableLattice_reduction_iso_local
        (A := A) (K := K) (G := G) Q with
    ⟨L, eLQ⟩
  rcases hQredS with ⟨eQS⟩
  exact ⟨L, ⟨eLQ.some.trans eQS⟩⟩

/-- Helper for Exercise 16-16.4-5: for a finite projective `A[G]`-module, scalar extension to `K`
and residue-field reduction to `k` preserve the same rank. -/
theorem scalarExtension_finrank_eq_residueFieldReduction_finrank_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module.finrank K (asModule (Q.scalarExtension K).ρ) =
      Module.finrank k (asModule Q.residueFieldReduction.toFiniteRep.ρ) := by
  letI : Module.Free A Q.V := Q.free
  let b : Module.Basis (Module.Free.ChooseBasisIndex A Q.V) A Q.V :=
    Module.Free.chooseBasis A Q.V
  letI : Finite (Module.Free.ChooseBasisIndex A Q.V) := Module.Finite.finite_basis b
  let Wk : ModuleCat k[G] := ModuleCat.of k[G] (k ⊗[A] Q.V)
  let bTensor : Module.Basis (Module.Free.ChooseBasisIndex A Q.V) k (k ⊗[A] Q.V) :=
    Algebra.TensorProduct.basis k b
  have hfinrank_tensor :
      Module.finrank k (k ⊗[A] Q.V) =
        Fintype.card (Module.Free.ChooseBasisIndex A Q.V) := by
    exact
      @Module.finrank_eq_card_basis k (k ⊗[A] Q.V) _ _ _ _ _
        (Module.Free.ChooseBasisIndex A Q.V) _ bTensor
  have hfinrank_red :
      Module.finrank k Q.residueFieldReduction.V =
        Fintype.card (Module.Free.ChooseBasisIndex A Q.V) := by
    simpa [Wk, FiniteProjectiveGroupAlgebraModule.residueFieldReduction] using
      hfinrank_tensor
  calc
    Module.finrank K (asModule (Q.scalarExtension K).ρ) =
        Fintype.card (Module.Free.ChooseBasisIndex A Q.V) := by
          change Module.finrank K (K ⊗[A] Q.V) =
            Fintype.card (Module.Free.ChooseBasisIndex A Q.V)
          simpa using
            (Module.finrank_eq_card_basis (Algebra.TensorProduct.basis K b))
    _ = Module.finrank k (asModule Q.residueFieldReduction.toFiniteRep.ρ) := by
          symm
          calc
            Module.finrank k (asModule Q.residueFieldReduction.toFiniteRep.ρ) =
                Module.finrank k Q.residueFieldReduction.V := by
                  exact
                    (Representation.asModuleEquiv
                      (ρ := Q.residueFieldReduction.toFiniteRep.ρ)).finrank_eq
            _ = Fintype.card (Module.Free.ChooseBasisIndex A Q.V) := by
                  exact hfinrank_red

/-- Helper for Exercise 16-16.4-5: the Chapter `16.1.12` Cartan-dimension theorem forces the
dimension of a projective simple module to be divisible by the `p`-part of `|G|`. -/
theorem projective_simple_dimension_dvd_p_part_local
    (S : FDRep k G) [Simple S]
    (hproj : Module.Projective k[G] (asModule S.ρ)) :
    p ^ Nat.factorization (Nat.card G) p ∣ Module.finrank k S := by
  classical
  obtain ⟨Q, f, hf⟩ :=
    exists_finite_projective_envelope_of_simple_local (A := A) (G := G) S
  have hQS : Nonempty (Q.toFiniteRep ≅ S) :=
    finite_projective_envelope_toFiniteRep_iso_target_of_projective
      (G := G) hproj hf
  let P : Sylow p G := Classical.choice (Sylow.nonempty (p := p) (G := G))
  let n := Nat.factorization (Nat.card G) p
  have hcardP : Nat.card (P : Subgroup G) = p ^ n := by
    simpa [n] using P.card_eq_multiplicity
  have hrange :
      (cartanHom k G).range ≤
        (finiteRepGrothendieckDimensionMod k G p n).ker :=
    by
      exact cartanHom_range_le_dimensionMod_ker_of_sylow P n hcardP
  have hzero :
      finiteRepGrothendieckDimensionMod k G p n (cartanHom k G [Q]ₚ₀) = 0 := by
    -- The Cartan class of a projective envelope lies in the kernel of the descended dimension map.
    exact hrange ⟨[Q]ₚ₀, rfl⟩
  rw [cartanHom_projectiveClass_eq] at hzero
  rw [finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hQS] at hzero
  change ((Int.ofNat (Module.finrank k S)) : ZMod (p ^ n)) = 0 at hzero
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
  exact Int.ofNat_dvd_natCast.mp hzero

/-- Helper for Exercise 16-16.4-5: an honest projective `A[G]`-lift of a projective simple
residue module has defect zero on the generic fiber. -/
theorem hasDefectZero_of_projective_simple_residue_lift_local
    (S : FDRep k G) [Simple S]
    (hproj : Module.Projective k[G] (asModule S.ρ))
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQredS : Nonempty (Q.residueFieldReduction.toFiniteRep ≅ S)) :
    HasDefectZero (Q.scalarExtension K).ρ p := by
  obtain ⟨L, hLredS⟩ :=
    projective_scalarExtension_literal_reduction_iso_local
      (A := A) (K := K) (G := G) Q S hQredS
  rcases hLredS with ⟨eLS⟩
  let _ : Simple (FDRep.of L.reductionRepresentation) := CategoryTheory.Simple.of_iso eLS
  have hLirr : L.reductionRepresentation.IsIrreducible := by
    -- The chosen reduction is simple because it is identified with the fixed simple residue
    -- module `S`.
    simpa using FDRep.isIrreducible_of_simple (FDRep.of L.reductionRepresentation)
  have hXirr : Representation.IsIrreducible (Q.scalarExtension K).ρ := by
    -- Serre's source route deduces generic-fiber irreducibility from simplicity of the same
    -- literal lattice reduction.
    simpa using simple_reduction_implies_isIrreducible
      (A := A) (K := K) (G := G) ((Q.scalarExtension K).ρ) L hLirr
  have hSdim :
      p ^ Nat.factorization (Nat.card G) p ∣ Module.finrank k S :=
    projective_simple_dimension_dvd_p_part_local
      (A := A) (p := p) (G := G) S hproj
  have hQreddim :
      Module.finrank k (asModule Q.residueFieldReduction.toFiniteRep.ρ) =
        Module.finrank k (asModule S.ρ) := by
    -- The residue-field lift data identifies the reduction of `Q` with `S`, so the dimensions
    -- coincide.
    rcases hQredS with ⟨eQS⟩
    simpa using (FDRep.isoToLinearEquiv eQS).finrank_eq
  have hXdim :
      Module.finrank K (asModule (Q.scalarExtension K).ρ) =
        Module.finrank k (asModule Q.residueFieldReduction.toFiniteRep.ρ) :=
    scalarExtension_finrank_eq_residueFieldReduction_finrank_local
      (A := A) (K := K) (G := G) Q
  refine ⟨hXirr, ?_⟩
  -- Transport the `p`-part divisibility from the projective simple residue module to the generic
  -- fiber through the literal lattice comparison.
  have hdim : Module.finrank K (asModule (Q.scalarExtension K).ρ) = Module.finrank k (asModule S.ρ) :=
    hXdim.trans hQreddim
  exact hdim ▸ hSdim

/-- Helper for Exercise 16-16.4-5: rebuild the literal range lattice on the default
restrict-scalars `A`-module owner carried by `Q.scalarExtension K`. -/
private noncomputable def projective_scalarExtension_literal_stableLattice_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (Q.scalarExtension K).ρ := by
  let X : FDRep K G := Q.scalarExtension K
  let L :=
    projective_scalarExtension_literal_stableLattice_local
      (A := A) (K := K) (G := G) Q
  refine
    { toSubmodule :=
        { carrier := (L.toSubmodule : Set X.V)
          zero_mem' := L.toSubmodule.zero_mem
          add_mem' := fun hx hy ↦ L.toSubmodule.add_mem hx hy
          smul_mem' := fun a x hx ↦ by
            simpa [Algebra.smul_def] using L.toSubmodule.smul_mem a hx }
      apply_mem_toSubmodule := by
        intro g x hx
        exact L.apply_mem_toSubmodule g hx
      isLattice := by
        simpa using L.isLattice }

/-- Helper for Exercise 16-16.4-5: once the projective simple residue module is lifted to an
actual projective `A[G]`-owner, the remaining source-faithful step is to upgrade the literal
reduction class to an actual reduction isomorphism and then package the generic fiber as
defect-zero. -/
theorem projective_simple_has_defect_zero_lift
    (S : FDRep k G) [Simple S]
    (hproj : Module.Projective k[G] (asModule S.ρ)) :
    ∃ (Q : FiniteProjectiveGroupAlgebraModule A G)
      (L : StableLattice A (Q.scalarExtension K).ρ),
        HasDefectZero (Q.scalarExtension K).ρ p ∧
          Nonempty (FDRep.of L.reductionRepresentation ≅ S) := by
  obtain ⟨Q, hQredS⟩ :=
    projective_simple_residueField_lift (A := A) (G := G) S hproj
  obtain ⟨L, hLredS⟩ :=
    projective_scalarExtension_literal_reduction_iso_local
      (A := A) (K := K) (G := G) Q S hQredS
  refine ⟨Q, L, ?_, hLredS⟩
  exact
    hasDefectZero_of_projective_simple_residue_lift_local
      (A := A) (K := K) (p := p) (G := G) S hproj Q hQredS

-- Proof sketch: `(ii) ⇒ (i)` is Proposition `16-16.4-1 (5)`. For `(i) ⇒ (ii)`, lift the
-- projective simple `k[G]`-module to a projective `A[G]`-module inside the fixed fraction-field
-- setting `K/A` and identify the corresponding defect-zero stable lattice. The equivalence with
-- `(iii)` is the Cartan-diagonal criterion from Exercise `15.7`, read directly from the canonical
-- Chapter `14`/`15` simple-basis and Cartan owners.
/-- Exercise 16-16.4-5: for a fixed local modular system `(A, K, p)` and an irreducible
`k[G]`-module `S`, the following are equivalent: `S` is projective over `k[G]`, `S` is the
reduction modulo `𝔪_A` of a defect-zero stable lattice in a simple `K[G]`-module as in
Proposition `16-16.4-1`, and the diagonal Cartan coefficient `C_SS` attached to the
distinguished projective-envelope basis is equal to `1`. -/
set_option maxHeartbeats 5000000 in theorem simple_finiteRep_projective_defect_zero_and_cartan_tfae
    (S : FDRep k G) [Simple S] :
    List.TFAE
      [ Module.Projective k[G] (asModule S.ρ),
        ∃ (X : FDRep K G) (L : StableLattice A X.ρ),
            HasDefectZero X.ρ p ∧
              Nonempty (FDRep.of L.reductionRepresentation ≅ S),
        ∀ {ι : Type x} [_inst : Fintype ι]
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
  tfae_have 2 → 1 := by
    intro h₂
    rcases h₂ with ⟨X, L, hdefect, hred_iso⟩
    have hred_proj :
        Module.Projective k[G] (asModule (FDRep.of L.reductionRepresentation).ρ) := by
      -- Proposition `16-16.4-1 (5)` makes the reduction of a defect-zero lattice projective.
      simpa using L.reduction_projective_of_defect_zero (p := p) hdefect
    rcases hred_iso with ⟨e⟩
    let eMod :
        asModule (FDRep.of L.reductionRepresentation).ρ ≃ₗ[k[G]] asModule S.ρ :=
      (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso e).toLinearEquiv
    -- Transport projectivity across the chosen reduction isomorphism to the target simple module.
    letI : Module.Projective k[G] (asModule (FDRep.of L.reductionRepresentation).ρ) := hred_proj
    exact Module.Projective.of_equiv' eMod
  tfae_have 1 → 3 := by
    intro hproj
    intro ι _ π hπ_pairwise hπ_complete iS hS_iso P hP_envelope
    -- Read the diagonal Cartan coefficient through the canonical projective-envelope basis at
    -- the index corresponding to `S`.
    exact cartan_diagonal_eq_one_of_projective_simple
      S π hπ_pairwise hπ_complete
      iS hS_iso P hP_envelope hproj
  tfae_have 3 → 1 := by
    intro h₃
    classical
    by_contra hS_not_projective
    obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
      exists_fintype_complete_pairwise_nonisomorphic_simple_family_local (A := A) (G := G)
    have hS_irred : Representation.IsIrreducible S.ρ := by
      simpa using (FDRep.isIrreducible_of_simple S)
    obtain ⟨iS, hS_iso'⟩ :=
      IsCompleteIrreducibleFamily.exists_iso_of_representation
        (K := k) (G := G) π hπ_complete S.ρ hS_irred
    have hS_iso : Nonempty (π iS ≅ S) := by
      rcases hS_iso' with ⟨e⟩
      exact ⟨e.symm⟩
    choose P hP_envelope using fun i : ι ↦ by
      letI : Simple (π i) := hπ_complete.isSimple i
      exact exists_finite_projective_envelope_of_simple_local (A := A) (G := G) (τ := π i)
    have hdiag :
        cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete)
          iS iS = 1 :=
      h₃ (ι := ι) π hπ_pairwise hπ_complete iS hS_iso P hP_envelope
    exact
      (cartan_diagonal_ne_one_of_nonprojective_simple_local
        (A := A) (G := G) S π hπ_pairwise hπ_complete
        iS hS_iso P hP_envelope hS_not_projective) hdiag
  tfae_have 1 → 2 := by
    intro hproj
    set_option maxHeartbeats 800000 in
    obtain ⟨Q, L, hdefect, hred⟩ :=
      projective_simple_has_defect_zero_lift
        (A := A) (K := K) (p := p) (G := G) S hproj
    refine ⟨Q.scalarExtension K, ?_, hdefect, hred⟩
    convert L using 1
  tfae_finish

end
