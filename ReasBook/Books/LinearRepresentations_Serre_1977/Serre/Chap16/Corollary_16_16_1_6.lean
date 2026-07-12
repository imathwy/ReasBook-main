import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6.Bases
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5

-- Declarations for this item will be appended below by the statement pipeline.

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
  · simpa using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) (Nat.card_pos (α := G)).ne'

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
* primitive data belongs upstream to the owner map
  `cartanHom k G : P₀[k](G) →+ R₀[k](G)` and its derived quotient owner
  `cartanCokernel k G`.
* this file should therefore expose only theorem-level consequences of those owners, rather than
  introducing any parallel wrapper or re-encoding of the Cartan data.
-/

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]

omit [IsAlgClosed k] [Finite G] in
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
          (QuotientAddGroup.Quotient.addCommGroup
            (finiteRepGrothendieckRelations k G)).toAddCommMonoid
          (AddCommGroup.toIntModule (R₀[k](G)))) := by
  -- The support file owns the simple-family basis construction; this local theorem only adapts
  -- that canonical owner statement to the explicit quotient-additive owner used below.
  simpa using finiteRepGrothendieck_basis_support (k := k) (G := G)

omit [IsAlgClosed k] [Finite G] in
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
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  -- Once the cyclic span is all of `P`, the singleton generator gives a surjection from `k[G]`.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

omit [IsAlgClosed k] in
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
            (QuotientAddGroup.Quotient.addCommGroup
              (finiteRepGrothendieckRelations k G)).toAddCommMonoid
            (AddCommGroup.toIntModule (R₀[k](G)))) := by
  -- Reuse the shared common-index basis package and only normalize the target owner spelling.
  simpa using cartan_source_target_bases_support (k := k) (G := G)

/-- Helper for Corollary 16-16.1-6: both Cartan source and target are free finite-rank
`ℤ`-modules of the same rank. -/
private theorem cartan_source_target_free_and_finite :
    Module.Free ℤ (P₀[k](G)) ∧ Module.Finite ℤ (P₀[k](G)) ∧
      @Module.Free ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) ∧
      @Module.Finite ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) := by
  classical
  obtain ⟨ι, _, ⟨bP⟩, ⟨bR⟩⟩ := cartan_source_target_bases (k := k) (G := G)
  have hFreeR :
      @Module.Free ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) :=
    @Module.Free.of_basis ℤ (R₀[k](G)) Int.instSemiring
      (QuotientAddGroup.Quotient.addCommGroup
        (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      (AddCommGroup.toIntModule (R₀[k](G))) ι bR
  have hFiniteR :
      @Module.Finite ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) :=
    @Module.Finite.of_basis ℤ (R₀[k](G)) ι Int.instSemiring
      (QuotientAddGroup.Quotient.addCommGroup
        (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      (AddCommGroup.toIntModule (R₀[k](G))) _ bR
  -- The common-index basis package gives the needed free and finite structures immediately.
  exact ⟨Module.Free.of_basis bP, Module.Finite.of_basis bP,
    hFreeR, hFiniteR⟩

/-- Helper for Corollary 16-16.1-6: the Cartan source and target have the same `ℤ`-rank, namely
the number of simple `k[G]`-classes. -/
private theorem cartan_source_target_finrank_eq :
    Module.finrank ℤ (P₀[k](G)) =
      @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) := by
  classical
  obtain ⟨ι, hι, ⟨bP⟩, ⟨bR⟩⟩ := cartan_source_target_bases (k := k) (G := G)
  letI : Fintype ι := hι
  have hcardR :
      @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule (R₀[k](G))) = Fintype.card ι :=
    @Module.finrank_eq_card_basis ℤ (R₀[k](G)) Int.instSemiring
      (QuotientAddGroup.Quotient.addCommGroup
        (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      (AddCommGroup.toIntModule (R₀[k](G))) _ ι _ bR
  -- Serre's source and target have the same rank because the basis index type is shared.
  exact (Module.finrank_eq_card_basis bP).trans hcardR.symm

omit [IsAlgClosed k] in
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
        change ρ.ρ.asModuleEquiv.symm (r • x) =
          ((algebraMap k k[G]) r) • ρ.ρ.asModuleEquiv.symm x
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

omit [IsAlgClosed k] in
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
    exact ⟨-y, by simp [hy]⟩
  · intro a b ha hb
    rcases ha with ⟨ya, hya⟩
    rcases hb with ⟨yb, hyb⟩
    exact ⟨ya + yb, by simp [map_add, hya, hyb]⟩

omit [IsAlgClosed k] in
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
    simp
  have hzero : (QuotientAddGroup.mk' (cartanHom k G).range ((N : ℕ) • x) :
      cartanCokernel k G) = 0 := by
    -- The annihilation hypothesis kills the quotient class of `x`, hence also the quotient class
    -- of its `N`-multiple.
    rw [hmk]
    exact hkill (QuotientAddGroup.mk' (cartanHom k G).range x)
  exact (QuotientAddGroup.eq_zero_iff ((N : ℕ) • x)).1 hzero

omit [IsAlgClosed k] [Finite G] in
/-- Helper for Corollary 16-16.1-6: on the canonical owner `R₀[k](G)`, applying
`nsmulAddMonoidHom` is exactly the same as taking an `N`-fold sum. -/
private theorem cartan_nsmul_owner_normalization_local
    (N : ℕ) (x : R₀[k](G)) :
    (@nsmulAddMonoidHom (R₀[k](G))
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      N) x =
      (N : ℕ) • x := by
  have hmul :
      (@nsmulAddMonoidHom (R₀[k](G))
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        N) x =
        (N : R₀[k](G)) * x := by
    -- First compare both natural-number actions with multiplication by the natural scalar inside
    -- the Grothendieck ring.
    induction N with
    | zero =>
        simp [nsmulAddMonoidHom]
    | succ N ih =>
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← ih]
        exact
          @succ_nsmul (R₀[k](G))
            (QuotientAddGroup.Quotient.addCommGroup
              (finiteRepGrothendieckRelations k G)).toAddCommMonoid.toAddMonoid
            x N
  -- The ring-owner spelling of multiplication by `N` is the standard `N`-fold additive sum.
  exact hmul.trans (nsmul_eq_mul N x).symm

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
      (QuotientAddGroup.Quotient.addCommGroup
        (finiteRepGrothendieckRelations k G)).toAddCommMonoid
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
          (QuotientAddGroup.Quotient.addCommGroup
            (finiteRepGrothendieckRelations k G)).toAddCommMonoid
          (AddCommGroup.toIntModule (R₀[k](G))) := by
    -- The source-faithful finite-index step uses the standard index of the `N`-multiple subgroup.
    simpa [L] using AddSubgroup.index_range_nsmul (M := R₀[k](G)) N
  have hL_finite : L.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff, hL_index]
    exact pow_ne_zero _ hN0
  letI : L.FiniteIndex := hL_finite
  letI : (cartanHom k G).range.FiniteIndex := AddSubgroup.finiteIndex_of_le hL_le
  exact AddSubgroup.finiteIndex_iff.mp inferInstance

/-- Helper for Corollary 16-16.1-6: once the additive Cartan range has finite index, Serre's
rank comparison already gives it the full ambient `ℤ`-rank on the canonical owner `R₀[k](G)`. -/
private theorem cartan_additive_range_finrank_eq_of_finiteIndex_local
    [((cartanHom k G).range).FiniteIndex] :
    Module.finrank ℤ ↥((cartanHom k G).range) =
      @Module.finrank ℤ (R₀[k](G)) Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
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
/-- First conclusion of Corollary 16-16.1-6: the Cartan homomorphism
`c : P_k(G) → R_k(G)` is injective. -/
theorem cartanHom_injective :
    Function.Injective (cartanHom k G) := by
  let hfree_finite :=
    Representation.cartan_source_target_free_and_finite_support (k := k) (G := G)
  letI := hfree_finite.1
  letI := hfree_finite.2.1
  have hRangeFiniteIndex : (cartanHom k G).range.FiniteIndex := by
    by_cases hchar0 : ringChar k = 0
    · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hchar0
      -- In characteristic zero Serre's proof makes the Cartan range all of `R₀[k](G)`.
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
          (QuotientAddGroup.Quotient.addCommGroup
            (finiteRepGrothendieckRelations k G)).toAddCommMonoid
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
          (QuotientAddGroup.Quotient.addCommGroup
            (finiteRepGrothendieckRelations k G)).toAddCommMonoid
          (AddCommGroup.toIntModule (R₀[k](G))) := by
    exact cartan_source_target_finrank_eq (k := k) (G := G)
  have hKerZero : Module.finrank ℤ ↥((cartanHom k G).ker) = 0 := by
    -- Rank-nullity over `ℤ` leaves no room for a nontrivial kernel once source and target
    -- ranks agree.
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

omit [CharP k p] [IsAlgClosed k] in
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
/-- Finiteness conclusion of Corollary 16-16.1-6: the Cartan cokernel is finite. -/
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
