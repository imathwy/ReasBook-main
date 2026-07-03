import Mathlib
import Mathlib.Analysis.Matrix.PosDef

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_16_1_4 (from Chap16) -/
noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

/- Domain-style sampling for Corollary 16-16.1-4:
* primary domain: scalar extension of finite projective `A[G]`-modules and the induced
  Grothendieck-group maps `P₀[k](G) → R₀[K](G)`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `projectiveGrothendieckReductionEquiv`,
  `finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso`;
* best owner abstraction: the canonical owner category
  `FiniteProjectiveGroupAlgebraModule A G`, together with the canonical Grothendieck-group maps
  built from it;
* source/core/bridge triage:
  source-facing: equality of scalar-extension classes forces isomorphism of the original finite
    projective `A[G]`-modules;
  core/canonical: LinearRepresentations_Serre_1977's map `projectiveGrothendieckScalarExtensionHom A K` and the reduction
    equivalence `projectiveGrothendieckReductionEquiv A G`;
  bridge/view: Chapter `14`'s classification theorem from equality in `P₀[A](G)` to an isomorphism
    in the owner category.
* primitive data: equality of the scalar-extension classes in `R₀[K](G)`;
* derived API: injectivity of `projectiveGrothendieckScalarExtensionHom A K`, transported
  equality in `P₀[A](G)`, and the resulting owner isomorphism.
The theorem should therefore conclude with the canonical owner-level isomorphism `P ≅ P'`, rather
than keeping a parallel module-level bridge as its main public surface.
-/

-- Proof sketch: the source proof uses injectivity of LinearRepresentations_Serre_1977's map `e` directly, so the right Lean
-- skeleton is to reflect equality of scalar-extension classes back along the base-change
-- homomorphism `P₀[A](G) → R₀[K](G)` and then finish with the Chapter `14` class-equality
-- criterion. The only remaining blocker is the earlier public injectivity bridge for that
-- base-change homomorphism on the present `[IsLocalRing A] [IsFractionRing A K]` surface.
/-- Helper for Corollary 16-16.1-4: the base-change homomorphism on projective Grothendieck
classes is injective on the present Henselian-local surface. -/
private theorem projective_baseChange_injective :
    Function.Injective (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K) := by
  -- Reflect equality of base-change classes through the split injectivity of LinearRepresentations_Serre_1977's map and
  -- then transport back across the reduction equivalence.
  obtain ⟨s, hs⟩ :=
    projectiveGrothendieckScalarExtensionHom_split_injective
      (A := A) (K := K) (G := G)
  intro x y hxy
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) x =
        projectiveGrothendieckReductionEquiv (A := A) (G := G) y := by
    apply hs.injective
    -- Rewrite LinearRepresentations_Serre_1977's scalar-extension map on both sides to the source-facing base-change map.
    simpa [projectiveGrothendieckScalarExtensionHom_apply] using hxy
  exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).injective hred

/-- Helper for Corollary 16-16.1-4: equality of scalar-extension classes reflects to equality of
projective Grothendieck classes over `A[G]`. -/
private theorem projective_class_eq_of_scalarExtensionClass_eq
    (P P' : FiniteProjectiveGroupAlgebraModule A G)
    (hclass : [P.scalarExtension K]₀ = [P'.scalarExtension K]₀) :
    [P]ₚ₀ = [P']ₚ₀ := by
  -- Reflect the equality of generic-fiber classes through the injective base-change map.
  apply projective_baseChange_injective (A := A) (K := K) (G := G)
  -- On projective generators, the source-facing base-change map is scalar extension.
  simpa [projectiveGrothendieckBaseChangeHom_projectiveClass_eq] using hclass

/-- Corollary 16-16.1-4: if two finite projective `A[G]`-modules have the same scalar-extension
class in `R₀[K](G)`, then they are already isomorphic in the canonical owner category of finite
projective `A[G]`-modules. -/
theorem finiteProjectiveGroupAlgebraModule_iso_of_scalarExtensionClass_eq
    (P P' : FiniteProjectiveGroupAlgebraModule A G)
    (hclass : [P.scalarExtension K]₀ = [P'.scalarExtension K]₀) :
    Nonempty (P ≅ P') := by
  -- First reflect the equality of generic-fiber classes back to `P₀[A](G)`.
  have hprojective : [P]ₚ₀ = [P']ₚ₀ :=
    projective_class_eq_of_scalarExtensionClass_eq (A := A) (K := K) (G := G) P P' hclass
  -- Then apply the Chapter 14 criterion identifying class equality with isomorphism.
  exact (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso P P').mp hprojective

end

end Representation

/-! ### Corollary_16_16_1_6 (from Chap16) -/
noncomputable section

open Module
open scoped Representation
open scoped MonoidAlgebra
open CategoryTheory

universe u w x

namespace Representation


section

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

/-- Helper for Corollary 16-16.1-6: the canonical `p`-part/prime-to-`p` factorization of
`Nat.card G` coming from `ordProj` and `ordCompl`. -/
private theorem card_eq_ordProj_mul_ordCompl_and_coprime :
    let n := Nat.factorization (Nat.card G) p
    let m := ordCompl[p] (Nat.card G)
    Nat.card G = p ^ n * m ∧ Nat.Coprime p m := by
  dsimp
  constructor
  · simpa using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  · simpa using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'

/-- Helper for Corollary 16-16.1-6: the only local adapter from the `ordProj` bookkeeping to the
canonical Theorem `16-16.1-5` annihilation statement. -/
private theorem cartanHom_cokernel_annihilated_by_p_part_local
    (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m) :
    ∀ x : cartanCokernel k G, (p ^ n) • x = 0 := by
  -- Route correction: the source proof cites Theorem `16-16.1-5` directly, so this corollary now
  -- delegates the annihilation step to the canonical Chapter `16` theorem instead of rebuilding
  -- a local Sylow/Cartan owner stack.
  simpa using
    Representation.cartanHom_cokernel_annihilated_by_p_part
      (p := p) (k := k) (G := G) n m hcard hm

end

/-
Domain-style sampling for Corollary 16-16.1-6:
* primary domain: the Cartan homomorphism between the projective and ordinary Grothendieck groups
  of `k[G]`, together with its quotient cokernel.
* inspected owner declarations in this domain:
  `cartanHom`,
  `cartanCokernel`,
  `cartanHom_projectiveClass_eq`,
  `IsPGroup`.
* best owner abstraction: the canonical owner map `cartanHom k G` together with its derived
  quotient owner `cartanCokernel k G`.
* source/core/bridge triage:
  source-facing: injectivity of the Cartan map and the finiteness and `p`-group structure of its
    cokernel;
  core/canonical: `cartanHom k G`, `cartanCokernel k G`, `IsPGroup`;
  bridge/view: none needed in this file.

Primitive data vs derived API:
* primitive data belongs upstream to the owner map `cartanHom k G : P₀[k](G) →+ R₀[k](G)` and its
  derived quotient owner `cartanCokernel k G`.
* this file should therefore expose only theorem-level consequences of those owners, rather than
  introducing any parallel wrapper or re-encoding of the Cartan data.
-/

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Corollary 16-16.1-6: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // CategoryTheory.Simple τ }
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
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    -- Isomorphic representatives define the same quotient class, so distinct classes stay
    -- pairwise nonisomorphic.
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
      have hq :
          Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Corollary 16-16.1-6: `R₀[k](G)` has a finite `ℤ`-basis coming from a complete
simple family. -/
private theorem finiteRepGrothendieck_basis :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι),
      Nonempty
        (@Module.Basis ι ℤ (R₀[k](G)) Int.instSemiring
          (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
          (AddCommGroup.toIntModule (R₀[k](G)))) := by
  sorry

/-- Helper for Corollary 16-16.1-6: the source of a projective envelope of a simple module is
cyclic, hence finitely generated. -/
private theorem moduleFinite_of_projectiveEnvelope_simple
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
    have : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using this
  have hmap_top : N.map f = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  -- Once the cyclic span is all of `P`, the singleton generator gives a surjection from `k[G]`.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Corollary 16-16.1-6: every simple finite-dimensional representation admits a finite
projective envelope in the category of `k[G]`-modules. -/
private theorem exists_finite_projectiveEnvelope_of_simple
    (τ : FDRep k G) [CategoryTheory.Simple τ] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule τ.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    simpa using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule k[G] τ := by
    -- Translate simplicity of the representation owner to simplicity of the underlying module.
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] τ
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  -- Use the Artinian projective-envelope existence theorem, then repackage the source as a
  -- finite projective `k[G]`-module.
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple
      (P := P') (M := τ) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    change Module.Projective k[G] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  -- The `ModuleCat` envelope is definitionally the same linear map envelope on the bundled owner.
  simpa [P, ρ] using hf'

/-- Helper for Corollary 16-16.1-6: both Cartan source and target admit `ℤ`-bases indexed by the
same complete simple family. -/
private theorem cartan_source_target_bases :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι),
      Nonempty (Module.Basis ι ℤ (P₀[k](G))) ∧
        Nonempty
          (@Module.Basis ι ℤ (R₀[k](G)) Int.instSemiring
            (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
            (AddCommGroup.toIntModule (R₀[k](G)))) := by
  sorry

/-- Helper for Corollary 16-16.1-6: both Cartan source and target are free finite-rank
`ℤ`-modules of the same rank. -/
private theorem cartan_source_target_free_and_finite :
    Module.Free ℤ (P₀[k](G)) ∧ Module.Finite ℤ (P₀[k](G)) ∧
      @Module.Free ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) ∧
      @Module.Finite ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) := by
  classical
  obtain ⟨ι, _, ⟨bP⟩, ⟨bR⟩⟩ := cartan_source_target_bases (k := k) (G := G)
  have hFreeR :
      @Module.Free ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) :=
    @Module.Free.of_basis ℤ (R₀[k](G)) Int.instSemiring
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      (AddCommGroup.toIntModule (R₀[k](G))) ι bR
  have hFiniteR :
      @Module.Finite ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) :=
    @Module.Finite.of_basis ℤ (R₀[k](G)) ι Int.instSemiring
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      (AddCommGroup.toIntModule (R₀[k](G))) _ bR
  -- The common-index basis package gives the needed free and finite structures immediately.
  exact ⟨Module.Free.of_basis bP, Module.Finite.of_basis bP,
    hFreeR, hFiniteR⟩

/-- Helper for Corollary 16-16.1-6: the Cartan source and target have the same `ℤ`-rank, namely
the number of simple `k[G]`-classes. -/
private theorem cartan_source_target_finrank_eq :
    Module.finrank ℤ (P₀[k](G)) =
      @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) := by
  classical
  obtain ⟨ι, hι, ⟨bP⟩, ⟨bR⟩⟩ := cartan_source_target_bases (k := k) (G := G)
  letI : Fintype ι := hι
  have hcardR :
      @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) = Fintype.card ι :=
    @Module.finrank_eq_card_basis ℤ (R₀[k](G)) Int.instSemiring
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      (AddCommGroup.toIntModule (R₀[k](G))) _ ι _ bR
  -- LinearRepresentations_Serre_1977's source and target have the same rank because the basis index type is shared.
  exact (Module.finrank_eq_card_basis bP).trans hcardR.symm

/-- Helper for Corollary 16-16.1-6: in characteristic zero, every finite-dimensional class is the
Cartan image of an actual finite projective `k[G]`-module class. -/
private theorem exists_projective_preimage_of_fdrep [CharZero k] (V : FDRep k G) :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G, cartanHom k G [P]ₚ₀ = [V]₀ := by
  let ρ : Rep k G := (forget₂ (FDRep k G) (Rep k G)).obj V
  let W0 : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
  let _ : Module k W0 := Module.compHom W0 (algebraMap k k[G])
  let _ : IsScalarTower k k[G] W0 := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hρfinite : Module.Finite k ρ := by
    simpa [ρ] using (show Module.Finite k V from inferInstance)
  let f : ρ →ₗ[k] W0 :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) = ((algebraMap k k[G]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  let _ : Module.Finite k W0 :=
    Module.Finite.of_surjective f fun y : W0 ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩
  let _ : Module.Finite k[G] W0 := Module.Finite.of_restrictScalars_finite k k[G] W0
  let W : FGModuleCat k[G] := by
    refine ⟨W0, ?_⟩
    change Module.Finite k[G] W0
    infer_instance
  letI : NeZero (Nat.card G : k) := by
    refine ⟨Nat.cast_ne_zero.mpr ?_⟩
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  have hproj : Module.Projective k[G] W := by
    -- Maschke semisimplicity turns the finite `k[G]`-module underlying `V` into a projective one.
    change Module.Projective k[G] W0
    exact Module.projective_of_isSemisimpleRing _ _
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨W, hproj⟩
  refine ⟨P, ?_⟩
  rw [cartanHom_projectiveClass_eq]
  let σ := P.toFiniteRep
  let eRep :
      ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
        ((forget₂ (FDRep k G) (Rep k G)).obj V) := by
    simpa [σ, P, W, W0, ρ, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (Rep.unitIso ρ).symm
  let e : σ ≅ V := by
    refine ⟨(FDRep.forget₂HomLinearEquiv σ V) eRep.hom,
      (FDRep.forget₂HomLinearEquiv V σ) eRep.inv, ?_, ?_⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  -- The projective model is isomorphic to `V`, so it defines the same Grothendieck class.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨e⟩

/-- Helper for Corollary 16-16.1-6: in characteristic zero every simple class already comes from a
projective module, so the Cartan range is all of `R₀[k](G)`. -/
private theorem cartan_range_eq_top_of_charZero [CharZero k] :
    (cartanHom k G).range = ⊤ := by
  rw [AddMonoidHom.range_eq_top]
  intro x
  -- Reduce the quotient presentation of `R₀[k](G)` to generators coming from actual
  -- finite-dimensional representations.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro V
    rcases exists_projective_preimage_of_fdrep (k := k) (G := G) V with ⟨P, hP⟩
    exact ⟨[P]ₚ₀, hP⟩
  · intro a ha
    rcases ha with ⟨y, hy⟩
    exact ⟨-y, by simpa [hy]⟩
  · intro a b ha hb
    rcases ha with ⟨ya, hya⟩
    rcases hb with ⟨yb, hyb⟩
    exact ⟨ya + yb, by simpa [map_add, hya, hyb]⟩

/-- Helper for Corollary 16-16.1-6: if the Cartan cokernel is annihilated by `N`, then every
`N`-multiple in `R₀[k](G)` already lies in the Cartan range. -/
private theorem cartan_nsmul_mem_range_of_cokernel_annihilation
    (N : ℕ)
    (hkill : ∀ x : cartanCokernel k G, N • x = 0)
    (x : R₀[k](G)) :
    (N : ℕ) • x ∈ (cartanHom k G).range := by
  have hmk :
      QuotientAddGroup.mk' (cartanHom k G).range ((N : ℕ) • x) =
        (N : ℕ) • (QuotientAddGroup.mk' (cartanHom k G).range x) := by
    -- Rewrite the quotient class of an `N`-multiple using the quotient map's compatibility with
    -- `nsmul`.
    simpa using (QuotientAddGroup.mk' (cartanHom k G).range).map_nsmul x N
  have hzero : (QuotientAddGroup.mk' (cartanHom k G).range ((N : ℕ) • x) :
      cartanCokernel k G) = 0 := by
    -- The annihilation hypothesis kills the quotient class of `x`, hence also the quotient class
    -- of its `N`-multiple.
    rw [hmk]
    exact hkill (QuotientAddGroup.mk' (cartanHom k G).range x)
  exact (QuotientAddGroup.eq_zero_iff ((N : ℕ) • x)).1 hzero

/-- Helper for Corollary 16-16.1-6: on the canonical owner `R₀[k](G)`, applying
`nsmulAddMonoidHom` is exactly the same as taking an `N`-fold sum. -/
private theorem cartan_nsmul_owner_normalization_local
    (N : ℕ) (x : R₀[k](G)) :
    (@nsmulAddMonoidHom (R₀[k](G))
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      N) x =
      (N : ℕ) • x := by
  sorry

/-- Helper for Corollary 16-16.1-6: if `N` kills every cokernel class, then the Cartan range has
nonzero additive index. -/
private theorem cartan_range_index_ne_zero_of_annihilation
    (N : ℕ) (hN0 : N ≠ 0)
    (hkill : ∀ x : cartanCokernel k G, N • x = 0) :
    (cartanHom k G).range.index ≠ 0 := by
  let hfree_finite :=
    cartan_source_target_free_and_finite (k := k) (G := G)
  letI := hfree_finite.2.2.1
  letI := hfree_finite.2.2.2
  let L : AddSubgroup (R₀[k](G)) :=
    (@nsmulAddMonoidHom (R₀[k](G))
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      N).range
  have hL_le : L ≤ (cartanHom k G).range := by
    -- Every witness in the `N`-multiple subgroup rewrites to the annihilation API's `N • x` form.
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact cartan_nsmul_owner_normalization_local (k := k) (G := G) N y ▸
      cartan_nsmul_mem_range_of_cokernel_annihilation (k := k) (G := G) N hkill y
  have hL_index :
      L.index =
        N ^ @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
          (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
          (AddCommGroup.toIntModule (R₀[k](G))) := by
    -- The source-faithful finite-index step uses the standard index of the `N`-multiple subgroup.
    simpa [L] using AddSubgroup.index_range_nsmul (M := R₀[k](G)) N
  have hL_finite : L.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff, hL_index]
    exact pow_ne_zero _ hN0
  letI : L.FiniteIndex := hL_finite
  letI : (cartanHom k G).range.FiniteIndex := AddSubgroup.finiteIndex_of_le hL_le
  exact AddSubgroup.finiteIndex_iff.mp inferInstance

/-- Helper for Corollary 16-16.1-6: once the additive Cartan range has finite index, LinearRepresentations_Serre_1977's
rank comparison already gives it the full ambient `ℤ`-rank on the canonical owner `R₀[k](G)`. -/
private theorem cartan_additive_range_finrank_eq_of_finiteIndex_local
    [((cartanHom k G).range).FiniteIndex] :
    Module.finrank ℤ ↥((cartanHom k G).range) =
      @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) := by
  let hfree_finite :=
    Representation.cartan_source_target_free_and_finite_support (k := k) (G := G)
  letI := hfree_finite.2.2.1
  letI := hfree_finite.2.2.2
  -- Finite index lets the additive range keep the full ambient rank without introducing any new
  -- owner transport beyond the canonical `R₀[k](G)` support file API.
  simpa using AddSubgroup.finrank_eq_of_finiteIndex (M := R₀[k](G)) ((cartanHom k G).range)

-- Proof sketch: both Grothendieck groups should be free `ℤ`-modules of the same rank, and the
-- characteristic-`p` section proves the cokernel is finite; that rank comparison should force the
-- kernel to vanish.
/-- Corollary 16-16.1-6 (1): the Cartan homomorphism `c : P_k(G) → R_k(G)` is injective. -/
theorem cartanHom_injective :
    Function.Injective (cartanHom k G) := by
  let hfree_finite :=
    Representation.cartan_source_target_free_and_finite_support (k := k) (G := G)
  letI := hfree_finite.1
  letI := hfree_finite.2.1
  have hRangeFiniteIndex : (cartanHom k G).range.FiniteIndex := by
    by_cases hchar0 : ringChar k = 0
    · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hchar0
      -- In characteristic zero LinearRepresentations_Serre_1977's proof makes the Cartan range all of `R₀[k](G)`.
      have hrange : (cartanHom k G).range = ⊤ :=
        cartan_range_eq_top_of_charZero (k := k) (G := G)
      have htop : (⊤ : AddSubgroup (R₀[k](G))).FiniteIndex := by
        rw [AddSubgroup.finiteIndex_iff]
        simp
      simpa [hrange] using htop
    · let p := ringChar k
      letI : CharP k p := ringChar.charP (R := k)
      have hp_ne_zero : p ≠ 0 := hchar0
      have hp_ne_one : p ≠ 1 := CharP.char_ne_one k p
      have hp_two_le : 2 ≤ p := by
        omega
      letI : Fact p.Prime := ⟨CharP.char_is_prime_of_two_le k p hp_two_le⟩
      let n := Nat.factorization (Nat.card G) p
      let m := ordCompl[p] (Nat.card G)
      have hcard_hm := card_eq_ordProj_mul_ordCompl_and_coprime (p := p) (G := G)
      have hindex :
          (cartanHom k G).range.index ≠ 0 := by
        -- In positive characteristic Theorem `16-16.1-5` gives an annihilator, hence finite index.
        exact cartan_range_index_ne_zero_of_annihilation
          (k := k) (G := G) (N := p ^ n)
          (pow_ne_zero _ (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
          (cartanHom_cokernel_annihilated_by_p_part_local (p := p) (k := k) (G := G) n m
            hcard_hm.1 hcard_hm.2)
      exact AddSubgroup.finiteIndex_iff.mpr hindex
  have hRangeRank :
      Module.finrank ℤ ↥((cartanHom k G).range) =
        @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
          (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
          (AddCommGroup.toIntModule (R₀[k](G))) := by
    -- Finite index of the additive range gives the full ambient rank on the canonical owner.
    exact cartan_additive_range_finrank_eq_of_finiteIndex_local (k := k) (G := G)
  have hQuotRank :
      Module.finrank ℤ (P₀[k](G) ⧸ (cartanHom k G).ker) =
        Module.finrank ℤ ↥((cartanHom k G).range) := by
    -- The additive first isomorphism theorem identifies the quotient by the kernel with the range.
    simpa using
      (AddEquiv.toIntLinearEquiv
        (QuotientAddGroup.quotientKerEquivRange (cartanHom k G))).finrank_eq
  have hSourceTargetRank :
      Module.finrank ℤ (P₀[k](G)) =
        @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
          (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
          (AddCommGroup.toIntModule (R₀[k](G))) := by
    exact cartan_source_target_finrank_eq (k := k) (G := G)
  have hKerZero : Module.finrank ℤ ↥((cartanHom k G).ker) = 0 := by
    -- Rank-nullity over `ℤ` leaves no room for a nontrivial kernel once source and target ranks agree.
    have hnull :
        Module.finrank ℤ (P₀[k](G) ⧸ (cartanHom k G).ker) +
          Module.finrank ℤ ↥((cartanHom k G).ker) =
            Module.finrank ℤ (P₀[k](G)) := by
      simpa using
        (Submodule.finrank_quotient_add_finrank (R := ℤ) (M := P₀[k](G))
          (((cartanHom k G).ker).toIntSubmodule))
    rw [hQuotRank, hRangeRank, hSourceTargetRank] at hnull
    omega
  have hKerZeroSubmodule : Module.finrank ℤ (((cartanHom k G).ker).toIntSubmodule) = 0 := by
    exact hKerZero
  have hKerBot : (cartanHom k G).ker = ⊥ := by
    -- A finite `ℤ`-submodule of finrank zero is trivial.
    exact AddSubgroup.toIntSubmodule.injective (Submodule.finrank_eq_zero.mp hKerZeroSubmodule)
  -- Injectivity is exactly the vanishing of the additive kernel.
  exact (AddMonoidHom.ker_eq_bot_iff (cartanHom k G)).mp hKerBot

end

section

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

/-- Helper for Corollary 16-16.1-6: the `p`-part `p ^ Nat.factorization (Nat.card G) p` kills the
Cartan cokernel. -/
private theorem cartanCokernel_annihilated_by_ordProj :
    ∀ x : cartanCokernel k G, (p ^ Nat.factorization (Nat.card G) p) • x = 0 := by
  let n := Nat.factorization (Nat.card G) p
  let m := ordCompl[p] (Nat.card G)
  -- Route correction: package the `ordProj`/`ordCompl` factorization once, then reuse the single
  -- local placeholder for the Chapter `16` annihilation step.
  have hcard_hm := card_eq_ordProj_mul_ordCompl_and_coprime (p := p) (G := G)
  have hcard : Nat.card G = p ^ n * m := hcard_hm.1
  have hm : Nat.Coprime p m := hcard_hm.2
  simpa [n] using
    cartanHom_cokernel_annihilated_by_p_part_local (k := k) (G := G) n m hcard hm

/-- Helper for Corollary 16-16.1-6: a quotient of a free finite `ℤ`-module annihilated by a
nonzero integer is finite. -/
private theorem cartanCokernel_finite_of_annihilation
    (N : ℕ) (hN0 : N ≠ 0)
    (hkill : ∀ x : cartanCokernel k G, N • x = 0) :
    Finite (cartanCokernel k G) := by
  have hindex :
      (cartanHom k G).range.index ≠ 0 :=
    cartan_range_index_ne_zero_of_annihilation (k := k) (G := G) N hN0 hkill
  let _ : (cartanHom k G).range.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr hindex
  -- Finite index of the Cartan range is equivalent to finiteness of the quotient.
  infer_instance

omit [CharP k p] in
/-- Helper for Corollary 16-16.1-6: if every element of the Cartan cokernel is annihilated by a
power of `p`, then the cokernel is a `p`-group. -/
private theorem cartanCokernel_isPGroup_of_annihilation
    (n : ℕ)
    (hkill : ∀ x : cartanCokernel k G, (p ^ n) • x = 0) :
    IsPGroup p (Multiplicative (cartanCokernel k G)) := by
  rw [IsPGroup.iff_orderOf]
  intro x
  -- The additive annihilation statement turns into a multiplicative `p`-power relation.
  have hpow : x ^ (p ^ n) = 1 := by
    simpa using congrArg Multiplicative.ofAdd (hkill (Multiplicative.toAdd x))
  obtain ⟨m, _, hm⟩ :=
    (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp (orderOf_dvd_of_pow_eq_one hpow)
  exact ⟨m, hm⟩

/-- Helper for Corollary 16-16.1-6: the characteristic-`p` cokernel finiteness statement with an
explicit prime parameter. -/
private theorem cartanCokernel_finite_explicit
    {p : ℕ} [CharP k p] [Fact p.Prime] :
    Finite (cartanCokernel k G) := by
  -- Apply the `ModN` finiteness bridge to the canonical `p`-part annihilator.
  exact cartanCokernel_finite_of_annihilation
    (k := k) (G := G) (N := p ^ Nat.factorization (Nat.card G) p)
    (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))
    (cartanCokernel_annihilated_by_ordProj (k := k) (G := G))

/-- Helper for Corollary 16-16.1-6: the characteristic-`p` `p`-group statement with an explicit
prime parameter. -/
private theorem cartanCokernel_isPGroup_explicit
    {p : ℕ} [CharP k p] [Fact p.Prime] :
    IsPGroup p (Multiplicative (cartanCokernel k G)) := by
  -- The same annihilation statement forces every element order to divide a `p`-power.
  exact cartanCokernel_isPGroup_of_annihilation
    (k := k) (G := G) (n := Nat.factorization (Nat.card G) p)
    (cartanCokernel_annihilated_by_ordProj (k := k) (G := G))

-- Proof sketch: Theorem `16-16.1-5` shows that the cokernel is annihilated by the `p`-part of
-- `Nat.card G`, so every element has `p`-power order; finiteness follows because the Cartan map is
-- a map between free finite-rank `ℤ`-modules of the same rank.
/-- Corollary 16-16.1-6 (2): the Cartan cokernel is finite. -/
theorem cartanCokernel_finite
    {p : ℕ} [CharP k p] [Fact p.Prime] :
    Finite (cartanCokernel k G) := by
  exact cartanCokernel_finite_explicit (k := k) (G := G) (p := p)

/-- Corollary 16-16.1-6 (2): the Cartan cokernel is a `p`-group. -/
theorem cartanCokernel_isPGroup :
    IsPGroup p (Multiplicative (cartanCokernel k G)) := by
  exact cartanCokernel_isPGroup_explicit (k := k) (G := G) (p := p)

end

end Representation

/-! ### Corollary_16_16_1_7 (from Chap16) -/
noncomputable section

universe u

open CategoryTheory
open scoped Representation

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-
Domain-style sampling for Corollary 16-16.1-7:
* primary domain: the Cartan homomorphism `cartanHom k G : P₀[k](G) →+ R₀[k](G)` for finite
  projective `k[G]`-modules and the Chapter `14` classification of projective modules by their
  classes in `P₀[k](G)`;
* relevant owner declarations inspected in this domain:
  `cartanHom`,
  `cartanHom_projectiveClass_eq`,
  `cartanHom_injective`,
  `finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso`;
* best owner abstraction: the canonical owner category `FiniteProjectiveGroupAlgebraModule k G`;
* source/core/bridge triage:
  source-facing: equality of the classes of `P.toFiniteRep` and `Q.toFiniteRep` in `R₀[k](G)`
    forces `P` and `Q` to be isomorphic;
  core/canonical: the owner map `cartanHom k G`;
  bridge/view: Chapter `14`'s owner-level classification theorem from equality in `P₀[k](G)` to
    an isomorphism in `FiniteProjectiveGroupAlgebraModule k G`.
* primitive data: the equality `hclass : [P.toFiniteRep]₀ = [Q.toFiniteRep]₀` in `R₀[k](G)`;
* derived API: equality of the projective classes via injectivity of `cartanHom k G`, then the
  resulting owner-level isomorphism.
The public surface should therefore use the canonical owner isomorphism `P ≅ Q`, not the
derived linear-equivalence bridge on underlying `k[G]`-modules.
-/

-- Proof sketch: equality of the classes of `P` and `Q` in `R_k(G)` means that their projective
-- classes in `P_k(G)` have the same image under the Cartan homomorphism. Corollary `16-16.1-6`
-- makes the Cartan homomorphism injective, so the projective classes coincide, and the Chapter 14
-- classification of projective modules by their Grothendieck classes then gives an isomorphism in
-- the canonical owner category `FiniteProjectiveGroupAlgebraModule k G`.
/-- Corollary 16-16.1-7: if two projective `k[G]`-modules have the same composition factors with
multiplicity, encoded here by equality of their classes in `R_k(G)`, then they are isomorphic as
objects of `FiniteProjectiveGroupAlgebraModule k G`. -/
theorem finiteProjectiveGroupAlgebraModule_iso_of_finiteRepGrothendieckClass_eq
    (P Q : FiniteProjectiveGroupAlgebraModule k G)
    (hclass : [P.toFiniteRep]₀ = [Q.toFiniteRep]₀) :
    Nonempty (P ≅ Q) := by
  exact
    (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso P Q).mp <|
      cartanHom_injective <| by
        simpa [cartanHom_projectiveClass_eq] using hclass

end

end Representation

/-! ### Corollary_16_16_1_8 (from Chap16) -/
noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u x

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

variable [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [NeZero (Nat.card G : IsLocalRing.ResidueField A)]

variable
  (π : ι → FDRep (IsLocalRing.ResidueField A) G)
  (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
  (hπ_pairwise : PairwiseNonisomorphic π)
  (hπ_complete : IsCompleteIrreducibleFamily π)
  (hP_envelope :
    ∀ i, ∃ f :
      (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
        f.IsProjectiveEnvelope)

/- Domain-style sampling for Corollary 16-16.1-8:
* primary domain: the Cartan homomorphism `cartanHom k G : P₀[k](G) → R₀[k](G)` and its canonical
  matrix view with respect to the Chapter `14` distinguished bases;
* relevant owner declarations inspected in this domain:
  `cartanHom`,
  `cartanMatrix`,
  `simple_finiteRep_classes_basis_of_complete_family`,
  `projectiveEnvelope_classes_basis_of_complete_family`;
* best owner abstraction: the canonical owner matrix `cartanMatrix k G`, with the simple-class and
  projective-envelope bases treated as derived input data from the Chapter `14` owner theorems;
* source/core/bridge triage:
  source-facing: symmetry, positive definiteness, and determinant shape of LinearRepresentations_Serre_1977's distinguished
    Cartan matrix under the large-field hypothesis;
  core/canonical: `cartanMatrix k G` as the matrix of `cartanHom k G`;
  bridge/view: the Chapter `14` basis constructions that realize the source's distinguished bases.

Primitive data vs derived API:
* primitive data for this file: the complete simple family `π`, the projective envelopes `P i`,
  and the corresponding envelope witnesses;
* derived API: the distinguished Chapter `14` bases and the resulting canonical Cartan matrix
  `cartanMatrix k G`. The finiteness bookkeeping needed to form that matrix is recovered locally
  from `hπ_complete` and `hπ_pairwise` via `finite_index`, rather than exported on the theorem
  surface.
-/

local notation "bP" =>
  projectiveEnvelope_classes_basis_of_complete_family
    π hπ_pairwise hπ_complete P hP_envelope

local notation "bR" =>
  simple_finiteRep_classes_basis_of_complete_family
    π hπ_pairwise hπ_complete

/-- Helper for Corollary 16-16.1-8: the large-field proof should show that the distinguished
Cartan matrix is positive definite. -/
private theorem cartanMatrix_source_faithful_gram_data
    [Finite ι] [Fintype ι] [DecidableEq ι]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G bP bR = E.transpose * E ∧ Function.Injective E.mulVec := by
  exact
    cartanMatrix_source_faithful_gram_data_support
      (A := A) (K := K) (G := G) π P hπ_pairwise hπ_complete hP_envelope

/-- Helper for Corollary 16-16.1-8: the large-field proof should show that the distinguished
Cartan matrix is positive definite. -/
private theorem cartanMatrix_posDef_of_sufficiently_large_aux
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      exact (cartanMatrix k G bP bR).PosDef
  := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨κ, _, _, E, hGram, hEinj⟩ :=
    cartanMatrix_source_faithful_gram_data
      (A := A) (K := K) (G := G) (π := π) (P := P)
      (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (hP_envelope := hP_envelope)
  -- Once the Chapter `15` pairing step is read as `C = Eᵀ * E`, positivity is a pure matrix
  -- consequence of the injectivity of scalar extension from Theorem `16-16.1-2`.
  simpa [hGram] using Matrix.PosDef.conjTranspose_mul_self E hEinj

-- Proof sketch: when `K` is sufficiently large, Theorem `16-16.1-2` makes the scalar-extension
-- matrix `E` split injective and the `cde` triangle identifies the Cartan matrix with `Eᵀ * E`;
-- this expression is visibly symmetric.
/-- Corollary 16-16.1-8 (1): if `K` is sufficiently large, then the Cartan matrix of `G` over the
residue field `k = A/𝔪_A`, written in the distinguished bases coming from a complete simple family
and their projective envelopes, is symmetric. -/
theorem cartanMatrix_isSymm_of_sufficiently_large
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      exact (cartanMatrix k G bP bR).IsSymm
  := by
    -- Symmetry is the Hermitian shadow of the positive-definite Cartan form.
    simpa [Matrix.IsSymm, Matrix.IsHermitian] using
      (cartanMatrix_posDef_of_sufficiently_large_aux
        (A := A) (K := K) (G := G) (π := π) (P := P)
        (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
        (hP_envelope := hP_envelope)).isHermitian

-- Proof sketch: write the Cartan form as the pullback of the standard character pairing over `K`
-- along the injective scalar-extension matrix from Theorem `16-16.1-2`; the transported matrix is
-- therefore positive definite.
/-- Corollary 16-16.1-8 (2): if `K` is sufficiently large, then the Cartan matrix of `G` over the
residue field `k = A/𝔪_A`, written in the distinguished bases coming from a complete simple family
and their projective envelopes, is positive definite. -/
theorem cartanMatrix_posDef_of_sufficiently_large
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      exact (cartanMatrix k G bP bR).PosDef
  := by
    -- Reuse the dedicated owner proof so the public corollary stays source-facing.
    exact cartanMatrix_posDef_of_sufficiently_large_aux
      (A := A) (K := K) (G := G) (π := π) (P := P)
      (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (hP_envelope := hP_envelope)

/-- Helper for Corollary 16-16.1-8: the absolute value of the distinguished Cartan determinant is
the cardinality of the Cartan cokernel. -/
private theorem cartanMatrix_det_natAbs_eq_card_cokernel :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      exact
        Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
          Nat.card (cartanCokernel k G)
  := by
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    have hcartan : Function.Injective (cartanHom k G) := Representation.cartanHom_injective
    let eRange :
        finiteProjectiveGroupAlgebraGrothendieckGroup k G ≃+ (cartanHom k G).range :=
      AddMonoidHom.ofInjective hcartan
    let bRange : Module.Basis ι ℤ (cartanHom k G).range :=
      Module.Basis.map bP eRange.toIntLinearEquiv
    have hindex :
        (cartanHom k G).range.index =
          Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) := by
      -- Compute the range index from the determinant of the transported projective basis.
      rw [AddSubgroup.index_eq_natAbs_det bR (cartanHom k G).range bRange]
      congr 1
      have hbRange :
          (fun i ↦ ((bRange i : (cartanHom k G).range) : R₀[k](G))) =
            (cartanHom k G) ∘ bP := by
        ext i
        change ↑(eRange (bP i)) = cartanHom k G (bP i)
        simpa [cartanHom_projectiveClass_eq] using
          (AddMonoidHom.ofInjective_apply (f := cartanHom k G) hcartan (x := bP i))
      rw [hbRange, Module.Basis.det_apply]
      congr
      ext i j
      simp [cartanMatrix, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    -- The Cartan cokernel is the quotient by the Cartan range, so its cardinality is the range
    -- index.
    calc
      Int.natAbs (Matrix.det (cartanMatrix k G bP bR))
          = (cartanHom k G).range.index := hindex.symm
      _ = Nat.card (cartanCokernel k G) := by
        simpa [cartanCokernel] using
          (AddSubgroup.index_eq_card (H := (cartanHom k G).range) (G := R₀[k](G)))

/-- Helper for Corollary 16-16.1-8: the absolute value of the distinguished Cartan determinant is
a power of `p` because the Cartan cokernel is a finite `p`-group. -/
private theorem cartanMatrix_det_natAbs_eq_prime_pow_of_sufficiently_large
    {p : ℕ} [CharP k p] [Fact p.Prime] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      exact ∃ n : ℕ, Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) = p ^ n
  := by
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    have hfiniteCokernel : Finite (cartanCokernel k G) := by
      exact cartanCokernel_finite
    letI : Finite (cartanCokernel k G) := hfiniteCokernel
    have hCokernelPGroup :
        IsPGroup p (Multiplicative (cartanCokernel k G)) :=
      cartanCokernel_isPGroup
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hCokernelPGroup
    refine ⟨n, ?_⟩
    -- Replace the determinant absolute value by the Cartan-cokernel cardinality, then use the
    -- `p`-group cardinality formula.
    rw [cartanMatrix_det_natAbs_eq_card_cokernel]
    simpa using hn

/-- Helper for Corollary 16-16.1-8: once the Cartan determinant is known to be nonnegative, its
`Int.natAbs` formula upgrades to an equality in `ℤ`. -/
private theorem int_eq_natAbs_of_nonneg {z : ℤ} {n : ℕ}
    (hnatAbs : Int.natAbs z = n) (hz : 0 ≤ z) :
    z = n := by
  -- Replace `Int.natAbs z` by `z` using nonnegativity and then rewrite with the known formula.
  calc
    z = (Int.natAbs z : ℤ) := (Int.natAbs_of_nonneg hz).symm
    _ = n := by rw [hnatAbs]

/-- Helper for Corollary 16-16.1-8: any integral Gram matrix `Eᵀ * E` has nonnegative
determinant. This isolates the determinant sign step from the representation-theoretic proof of
the Cartan Gram identity. -/
private theorem Matrix.int_gram_det_nonneg_local
    {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]
    (E : Matrix κ η ℤ) :
    0 ≤ Matrix.det (E.transpose * E) := by
  let Eℝ : Matrix κ η ℝ := E.map (Int.castRingHom ℝ)
  have hpsd : Matrix.PosSemidef (Eℝ.transpose * Eℝ) := by
    -- After casting to `ℝ`, the Gram matrix is visibly positive semidefinite.
    simpa [Eℝ] using (Matrix.posSemidef_conjTranspose_mul_self Eℝ)
  have hmap :
      (E.transpose * E).map (Int.castRingHom ℝ) = Eℝ.transpose * Eℝ := by
    -- Entrywise, casting commutes with transpose and matrix multiplication.
    ext i j
    simp [Eℝ, Matrix.mul_apply]
  have hdet_nonneg : 0 ≤ Matrix.det (Eℝ.transpose * Eℝ) :=
    Matrix.PosSemidef.det_nonneg hpsd
  have hcast :
      ((Matrix.det (E.transpose * E) : ℤ) : ℝ) = Matrix.det (Eℝ.transpose * Eℝ) := by
    -- Rewrite the determinant after casting the integral matrix entries to `ℝ`.
    rw [Int.cast_det]
    simpa [hmap] using congrArg Matrix.det hmap
  have hreal : 0 ≤ (((Matrix.det (E.transpose * E) : ℤ) : ℝ)) := by
    rw [hcast]
    exact hdet_nonneg
  exact_mod_cast hreal

/-- Helper for Corollary 16-16.1-8: once the source-faithful proof provides a Gram factorization
`C = Eᵀ * E`, the determinant sign follows from the previous pure matrix lemma. -/
private theorem Matrix.int_det_nonneg_of_eq_transpose_mul_self_local
    {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]
    (C : Matrix η η ℤ) (E : Matrix κ η ℤ)
    (hC : C = E.transpose * E) :
    0 ≤ Matrix.det C := by
  -- Replace `C` by the Gram matrix exhibited by the source-faithful positive-definite route.
  simpa [hC] using Matrix.int_gram_det_nonneg_local E

/-- Helper for Corollary 16-16.1-8: after LinearRepresentations_Serre_1977's quadratic-form route has produced positive
definiteness of the distinguished Cartan matrix, only the sign bridge from `PosDef` to
`0 ≤ det C` remains before the `natAbs` formula can be turned into an equality in `ℤ`. -/
private theorem cartanMatrix_det_nonneg_of_sufficiently_large_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      exact 0 ≤ Matrix.det (cartanMatrix k G bP bR)
  := by
    classical
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    obtain ⟨κ, _, _, E, hGram, _⟩ :=
      cartanMatrix_source_faithful_gram_data
        (A := A) (K := K) (G := G) (π := π) (P := P)
        (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
        (hP_envelope := hP_envelope)
    exact
      Matrix.int_det_nonneg_of_eq_transpose_mul_self_local
        (C := cartanMatrix k G bP bR) E hGram

-- Proof sketch: part `(2)` gives positivity of the determinant. Corollary `16-16.1-6`
-- identifies the cokernel of the Cartan homomorphism as a finite `p`-group, so the determinant of
-- the Cartan matrix, which computes the index of the image in the distinguished bases, must be a
-- power of `p`.
/-- Corollary 16-16.1-8 (3): if `K` is sufficiently large, then the determinant of the Cartan
matrix of `G` over the residue field `k = A/𝔪_A`, written in the distinguished bases coming from a
complete simple family and their projective envelopes, is a power of `p`. -/
theorem cartanMatrix_det_eq_prime_pow_of_sufficiently_large
    {p : ℕ} [CharP k p] [Fact p.Prime]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    by
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      exact ∃ n : ℕ, Matrix.det (cartanMatrix k G bP bR) = (p : ℤ) ^ n
  := by
  -- Route correction: this sign upgrade is now completely formal once
  -- `cartanMatrix_posDef_of_sufficiently_large_aux` is finished. The remaining implementation work
  -- is to stabilize the elaboration of `Matrix.PosDef.det_pos` on the local abbreviation
  -- `C := cartanMatrix k G bP bR`, then combine it with
  -- `cartanMatrix_det_natAbs_eq_prime_pow_of_sufficiently_large` via
  -- `int_eq_natAbs_of_nonneg`.
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨n, hn⟩ :=
    cartanMatrix_det_natAbs_eq_prime_pow_of_sufficiently_large
      (A := A) (G := G) (π := π) (P := P)
      (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (hP_envelope := hP_envelope) (p := p)
  refine ⟨n, ?_⟩
  have hz :
      0 ≤ Matrix.det (cartanMatrix k G bP bR) :=
    cartanMatrix_det_nonneg_of_sufficiently_large_local
      (A := A) (K := K) (G := G) (π := π) (P := P)
      (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (hP_envelope := hP_envelope)
  simpa using
    (int_eq_natAbs_of_nonneg
      (z := Matrix.det (cartanMatrix k G bP bR)) (n := p ^ n) hn hz)

end

end Representation

/-! ### Corollary_16_16_1_8_CartanGramSupport (from Chap16) -/
noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u x

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Corollary 16-16.1-8: support theorem packaging the source-faithful Gram
factorization of the distinguished Cartan matrix. -/
theorem cartanMatrix_source_faithful_gram_data_support
    (π : ι → FDRep (IsLocalRing.ResidueField A) G)
    (P : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hP_envelope :
      ∀ i, ∃ f :
        (P i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π i).ρ,
          f.IsProjectiveEnvelope)
    [Finite ι] [Fintype ι] [DecidableEq ι]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E ∧ Function.Injective E.mulVec := by
  sorry

end

end Representation

/-! ### Corollary_16_16_1_8_ProjectiveTriangleSupport (from Chap16) -/
noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Corollary 16-16.1-8: support theorem packaging the projective-generator case of
LinearRepresentations_Serre_1977's `c = d ∘ e` triangle. -/
theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  sorry

/-- Helper for Corollary 16-16.1-8: support theorem packaging the additive compatibility
`d ∘ e = c` on projective Grothendieck classes over the residue field. -/
theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local_support
    [HenselianLocalRing A]
    (x : finiteProjectiveGroupAlgebraGrothendieckGroup k G) :
    decompositionHom A K G
        ((projectiveGrothendieckScalarExtensionHom A K) x) =
      cartanHom k G x := by
  sorry

end

end Representation

/-! ### Exercise_16_16_1_10 (from Chap16) -/
/- Domain-style sampling for this item:
* primary domain: LinearRepresentations_Serre_1977's decomposition homomorphism on Grothendieck groups of finite-dimensional
  representations over a fraction field and its residue field.
* relevant owner declarations inspected in the same domain:
  `stableLatticeReduction_grothendieckClass_eq`,
  `decompositionHom`,
  `decompositionHom_finiteRepClass_eq`,
  `decompositionHom_surjective`.

Primitive data vs derived API:
* the owner data are already carried by `Representation.decompositionHom`;
* the large-field surjectivity assertion is already carried by the canonical theorem
  `Representation.decompositionHom_surjective`;
* this exercise adds no new source-facing object, only the proof-note observation that the
  surjectivity statement does not require any completeness hypothesis on the fraction field.

Source/core/bridge triage:
* source-facing: Exercise `16-16.1-10` is a proof note about the existing Chapter `16`
  surjectivity statement;
* core/canonical: the owner theorem is `Representation.decompositionHom_surjective`;
* bridge/view: there is no additional bridge construction here, so the refined surface should stay
  a direct recall of the canonical theorem rather than a duplicate wrapper. -/
recall Representation.decompositionHom_surjective
