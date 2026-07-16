import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap03.Exercise_3_3_3_7
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.CartanBasisExtension
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.PGroupBridges
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.ElementaryDecompositionBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.ExternalTensorCollapse

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open IsCyclotomicExtension.Rat
open scoped Pointwise
open scoped Representation
open scoped MonoidAlgebra
open scoped MonoidalCategory
open scoped TensorProduct
open scoped ZeroObject
open scoped Representation.ExternalTensor

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p] [instAlgClosedK : IsAlgClosed k]
variable {G : Type u} [Group G]
variable {A : Type*} [AddCommGroup A]
variable [Fact p.Prime]

local instance finiteRepGrothendieckAddCommMonoid
    {H : Type u} [Group H] : AddCommMonoid (R₀[k](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)).toAddCommMonoid

local instance finiteRepGrothendieckAddCommGroup
    {H : Type u} [Group H] : AddCommGroup (R₀[k](H)) :=
  QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)

local instance finiteRepGrothendieckIntModule
    {H : Type u} [Group H] : Module ℤ (R₀[k](H)) :=
  AddCommGroup.toIntModule (R₀[k](H))

/-- Helper for Theorem 16-16.1-5: inducing a finite projective `k[H]`-module along `H ≤ G`
stays finite-dimensional over `k`. -/
private theorem FiniteProjectiveGroupAlgebraModule.subgroupInduction_finite_local
    [Finite G] {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    Module.Finite k (Rep.ind H.subtype P.toRep) := by
  let ρ := Representation.tprod ((leftRegular k G).comp H.subtype) P.toRep.ρ
  let M :=
    (TensorProduct k (G →₀ k) P.toRep) ⧸
      Representation.Coinvariants.ker (k := k) (G := H)
        (V := TensorProduct k (G →₀ k) P.toRep) ρ
  let _ : Module.Finite k M := by
    infer_instance
  change Module.Finite k M
  infer_instance

/-- Helper for Theorem 16-16.1-5: induction along `H ≤ G` preserves projectivity for finite
projective `k[H]`-modules. -/
private theorem FiniteProjectiveGroupAlgebraModule.subgroupInduction_projective_local
    [Finite G] {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    Module.Projective k[G] (Rep.ind H.subtype P.toRep).ρ.asModule := by
  have hP : Projective P.toRep := by
    rw [← Rep.equivalenceModuleMonoidAlgebra.map_projective_iff]
    let M : ModuleCat k[H] := ModuleCat.of k[H] P.V
    have hM : Projective M := by
      rw [← IsProjective.iff_projective (R := k[H]) (P := P.V)]
      exact P.projective
    have hIso : Rep.toModuleMonoidAlgebra.obj P.toRep ≅ M := by
      simpa [M, FiniteProjectiveGroupAlgebraModule.toRep] using
        Rep.counitIso (k := k) (G := H) M
    exact Projective.of_iso hIso.symm hM
  have hInd : Projective (Rep.ind H.subtype P.toRep) := by
    simpa using Adjunction.map_projective (Rep.indResAdjunction k H.subtype) P.toRep hP
  change Module.Projective k[G] (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep))
  have hModObj : Projective (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep)) :=
    (Rep.equivalenceModuleMonoidAlgebra.map_projective_iff (Rep.ind H.subtype P.toRep)).2 hInd
  letI : Projective (Rep.toModuleMonoidAlgebra.obj (Rep.ind H.subtype P.toRep)) := hModObj
  infer_instance

/-- Helper for Theorem 16-16.1-5: the theorem-local induced finite projective owner on `G`. -/
private abbrev FiniteProjectiveGroupAlgebraModule.subgroupInduction_local
    [Finite G] {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    FiniteProjectiveGroupAlgebraModule k G :=
  let ρ := Rep.ind H.subtype P.toRep
  let Wk : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
  let _ : Module.Finite k ρ :=
    FiniteProjectiveGroupAlgebraModule.subgroupInduction_finite_local (k := k) (G := G) P
  let _ : Module k Wk := Module.compHom Wk (algebraMap k k[G])
  let _ : IsScalarTower k k[G] Wk := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f : ρ →ₗ[k] Wk :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) = ((algebraMap k k[G]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  let _ : Module.Finite k Wk :=
    Module.Finite.of_surjective f fun y : Wk ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩
  let _ : Module.Finite k[G] Wk := Module.Finite.of_restrictScalars_finite k k[G] Wk
  let W : FGModuleCat k[G] := by
    refine ⟨Wk, ?_⟩
    change Module.Finite k[G] Wk
    infer_instance
  let hW : Module.Projective k[G] W := by
    simpa [Wk, W, ρ, Rep.toModuleMonoidAlgebra] using
      FiniteProjectiveGroupAlgebraModule.subgroupInduction_projective_local (k := k) (G := G) P
  ⟨W, hW⟩

/-- Helper for Theorem 16-16.1-5: forgetting the induced projective owner gives the same
finite-dimensional class as inducing the underlying finite-dimensional representation. -/
private theorem induced_projective_toFiniteRep_class_eq
    [Finite G] {H : Subgroup G} (P : FiniteProjectiveGroupAlgebraModule k H) :
    [((FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) P).toFiniteRep)]₀ =
      [FDRep.subgroupInduction (k := k) (G := G) P.toFiniteRep]₀ := by
  let σ₁ := (FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) P).toFiniteRep
  let σ₂ := FDRep.subgroupInduction (k := k) (G := G) P.toFiniteRep
  let eRep :
      ((forget₂ (FDRep k G) (Rep k G)).obj σ₁) ≅
        ((forget₂ (FDRep k G) (Rep k G)).obj σ₂) := by
    simpa [σ₁, σ₂, FDRep.subgroupInduction, FiniteProjectiveGroupAlgebraModule.subgroupInduction_local,
      FiniteProjectiveGroupAlgebraModule.toFiniteRep, FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso (Rep.ind H.subtype P.toRep)).symm
  let e : σ₁ ≅ σ₂ := by
    refine ⟨(FDRep.forget₂HomLinearEquiv σ₁ σ₂) eRep.hom,
      (FDRep.forget₂HomLinearEquiv σ₂ σ₁) eRep.inv, ?_, ?_⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨e⟩

/-- Helper for Theorem 16-16.1-5: every projective Grothendieck class on `H` has an induced
Cartan preimage on `G`, constructed generatorwise from the induced finite projective owner. -/
private theorem exists_subgroupInduction_cartan_preimage
    [Finite G] (H : Subgroup G) (x : P₀[k](H)) :
    ∃ x' : P₀[k](G),
      cartanHom k G x' =
        finiteRep_subgroupInduction (k := k) (G := G) H (cartanHom k H x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · refine ⟨0, by simp⟩
  · intro P
    refine ⟨[(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local (k := k) (G := G) P)]ₚ₀, ?_⟩
    change
      cartanHom k G
          ([(FiniteProjectiveGroupAlgebraModule.subgroupInduction_local
            (k := k) (G := G) P)]ₚ₀ : P₀[k](G)) =
        finiteRep_subgroupInduction (k := k) (G := G) H
          (cartanHom k H ([P]ₚ₀ : P₀[k](H)))
    rw [cartanHom_projectiveClass_eq, cartanHom_projectiveClass_eq,
      finiteRep_subgroupInduction_apply_class]
    exact induced_projective_toFiniteRep_class_eq (k := k) (G := G) P
  · intro a ha
    rcases ha with ⟨x', hx'⟩
    refine ⟨-x', ?_⟩
    simpa [map_neg] using congrArg Neg.neg hx'
  · intro a b ha hb
    rcases ha with ⟨x₁, hx₁⟩
    rcases hb with ⟨x₂, hx₂⟩
    refine ⟨x₁ + x₂, ?_⟩
    simpa [map_add] using congrArg₂ HAdd.hAdd hx₁ hx₂

/- Domain-style sampling for Theorem 16-16.1-5:
* source-facing layer: Serre's theorem that the `p`-part of `|G|` kills the cokernel of the
  Cartan homomorphism.
* core/canonical owner already fixed upstream in Chapter `15`: `cartanHom k G : P₀[k](G) →+
  R₀[k](G)`.
* related project declarations inspected in the same domain:
  `cartanHom`,
  `cartanCokernel`,
  `cartanHom_projectiveClass_eq`.

Primitive data belongs to the owner `cartanHom k G`; this file contributes only the theorem-level
image statement and its immediate cokernel reformulation.
-/

/-- Helper for Theorem 16-16.1-5: every Grothendieck class is a finite sum of inductions from
ordinary elementary subgroups (over an algebraically closed `k`). -/
private theorem grothendieckClass_exists_sum_of_elementary_subgroup_inductions_local
    [Finite G] (x : R₀[k](G)) :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, finiteRep_subgroupInduction (k := k) (G := G) (H i) (y i) := by
  -- The theorem-local bridge file already isolates the Brauer-induction specialization needed
  -- here, so only the induction-owner spelling needs to be rewritten.
  simpa [finiteRep_subgroupInduction] using
    (grothendieckClass_exists_sum_of_elementary_subgroup_inductions_bridge
      (k := k) (G := G) x)

omit [Group G] in
/-- If `Nat.card G = p ^ n * m` with `p` prime and coprime to `m`, then `G` is finite. This
packages the finiteness recovery used to form the Cartan homomorphism in the `p`-modular
arguments of Chapter `16`. -/
theorem finite_of_card_eq_mul_of_coprime
    {n m : ℕ} (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m) : Finite G := by
  have hm0 : m ≠ 0 := by
    intro hm_eq_zero
    have : Nat.Coprime p 0 := by
      simpa [hm_eq_zero] using hm
    exact Nat.Prime.ne_one Fact.out <| by
      simpa [Nat.coprime_zero_right] using this
  -- The displayed factorization makes `Nat.card G` nonzero, hence `G` finite.
  exact Nat.finite_of_card_ne_zero <| by
    rw [hcard]
    exact Nat.mul_ne_zero (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)) hm0

omit [CharP k p] [Fact p.Prime] [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: once a `p ^ n`-multiple already lies in the Cartan range, its
class vanishes in the Cartan cokernel. -/
private theorem cartan_cokernel_p_part_eq_zero
    [Finite G]
    (n : ℕ) (y : R₀[k](G))
    (hy : (p ^ n) • y ∈ (cartanHom k G).range) :
    QuotientAddGroup.mk' (cartanHom k G).range ((p ^ n) • y) = (0 : cartanCokernel k G) := by
  -- The quotient map kills exactly the Cartan image.
  exact (QuotientAddGroup.eq_zero_iff ((p ^ n) • y)).2 hy

omit [CharP k p] [Fact p.Prime] [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: natural-number scalar multiplication on `R₀[k](H)` distributes
over a finite sum indexed by a `Fintype`. -/
private theorem grothendieck_nsmul_sum
    {H : Type u} [Group H] {ι : Type*} [Fintype ι]
    (N : ℕ) (f : ι → R₀[k](H)) :
    (N : ℕ) • ∑ i, f i = ∑ i, (N : ℕ) • f i := by
  classical
  -- Rewrite the scalar as multiplication in the Grothendieck ring and use distributivity once.
  simpa [nsmul_eq_mul] using
    (Finset.mul_sum Finset.univ (fun i ↦ f i) (((N : ℕ) : R₀[k](H))))

omit [CharP k p] [Fact p.Prime] [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: if a fixed natural-number multiple of each simple basis vector
of `R₀[k](G)` lies in the range of an additive map `f`, then the same multiple of every class lies
in the range of `f`. -/
private theorem addMonoidHom_nsmul_mem_range_of_simple_basis_preimages_local
    [Finite G] {ι : Type (u + 1)} [Fintype ι]
    (f : A →+ R₀[k](G))
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (N : ℕ)
    (hπ_range : ∀ i, (N : ℕ) • [π i]₀ ∈ f.range)
    (y : R₀[k](G)) :
    (N : ℕ) • y ∈ f.range := by
  -- The public basis-extension theorem already packages exactly this step.
  exact addMonoidHom_nsmul_mem_range_of_simple_basis_preimages
    (f := f) (π := π) hπ_pairwise hπ_complete N hπ_range y

omit [CharP k p] [Fact p.Prime] [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: choose one representative from each isomorphism class of simple
finite-dimensional `k[G]`-representations. This keeps the simple-basis step local to the theorem
instead of importing the Chapter `16` basis corollary. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_basis_local
    [Finite G] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
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
  have hπ_pairwise : PairwiseNonisomorphic π := by
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
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 16-16.1-5: the free lift sending a finite-dimensional class on `A` to its
pullback along `φ : B →* A`. -/
private abbrev finiteRepGrothendieckPrecomposeLift
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A) :
    FreeAbelianGroup (FDRep k A) →+ R₀[k](B) :=
  FreeAbelianGroup.lift fun V ↦ [FDRep.of (V.ρ.comp φ)]₀

/-- Helper for Theorem 16-16.1-5: transport an `FDRep` morphism along `φ : B →* A` by keeping
its underlying `k`-linear map and rechecking equivariance only on the pulled-back `B`-action. -/
private abbrev finiteRep_precompose_map_local
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A)
    {V W : FDRep k A} (f : V ⟶ W) :
    FDRep.of (V.ρ.comp φ) ⟶ FDRep.of (W.ρ.comp φ) :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (Rep.ofHom ⟨((forget₂ (FDRep k A) (Rep k A)).map f).hom.toLinearMap, fun b => by
      -- The original intertwining identity applies after evaluating at `φ b`.
      simpa using (((forget₂ (FDRep k A) (Rep k A)).map f).hom.isIntertwining' (φ b))⟩)

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: forgetting the pulled-back `FDRep` morphism recovers the
explicit `Rep` morphism built from the same linear map. -/
private theorem finiteRep_precompose_map_forget_local
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A)
    {V W : FDRep k A} (f : V ⟶ W) :
    (forget₂ (FDRep k B) (Rep k B)).map
        (finiteRep_precompose_map_local (k := k) (A := A) (B := B) φ f) =
      Rep.ofHom
        ⟨(((forget₂ (FDRep k A) (Rep k A)).map f).hom.toLinearMap), fun b => by
          -- Again evaluate the original intertwining identity at `φ b`.
          simpa using (((forget₂ (FDRep k A) (Rep k A)).map f).hom.isIntertwining' (φ b))⟩ := by
  -- `finiteRep_precompose_map_local` was defined by transporting this `Rep` map back through
  -- `FDRep.forget₂HomLinearEquiv`.
  let fφ :
      ((forget₂ (FDRep k B) (Rep k B)).obj (FDRep.of (V.ρ.comp φ)) ⟶
        (forget₂ (FDRep k B) (Rep k B)).obj (FDRep.of (W.ρ.comp φ))) :=
    Rep.ofHom
      ⟨(((forget₂ (FDRep k A) (Rep k A)).map f).hom.toLinearMap), fun b => by
        simpa using (((forget₂ (FDRep k A) (Rep k A)).map f).hom.isIntertwining' (φ b))⟩
  have hforget :
      (forget₂ (FDRep k B) (Rep k B)).map
          (finiteRep_precompose_map_local (k := k) (A := A) (B := B) φ f) = fφ := by
    change (FDRep.forget₂HomLinearEquiv (FDRep.of (V.ρ.comp φ)) (FDRep.of (W.ρ.comp φ))).symm
        ((FDRep.forget₂HomLinearEquiv (FDRep.of (V.ρ.comp φ)) (FDRep.of (W.ρ.comp φ))) fφ) = fφ
    exact (FDRep.forget₂HomLinearEquiv _ _).left_inv fφ
  simpa [fφ] using hforget

/-- Helper for Theorem 16-16.1-5: the explicit short complex obtained by precomposing the three
terms of `S` with `φ`, while keeping the underlying `k`-linear maps unchanged. -/
private abbrev finiteRepGrothendieckPrecompose_shortComplex_local
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A)
    (S : ShortComplex (FDRep k A)) : ShortComplex (FDRep k B) :=
  ShortComplex.mk
    (finiteRep_precompose_map_local (k := k) (A := A) (B := B) φ S.f)
    (finiteRep_precompose_map_local (k := k) (A := A) (B := B) φ S.g)
    (by
      -- After forgetting to `Rep k B`, composition is still zero because the linear maps did not
      -- change from the original short complex over `A`.
      apply (forget₂ (FDRep k B) (Rep k B)).map_injective
      rw [Functor.map_comp]
      rw [finiteRep_precompose_map_forget_local (k := k) (A := A) (B := B) φ S.f]
      rw [finiteRep_precompose_map_forget_local (k := k) (A := A) (B := B) φ S.g]
      ext x
      have hzero :=
        LinearMap.congr_fun
          (congrArg
            (fun m =>
              m.hom.toLinearMap)
            ((S.map (forget₂ (FDRep k A) (Rep k A))).zero)) x
      simpa using hzero)

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: precomposing a short exact sequence of finite-dimensional
representations with `φ : B →* A` keeps it short exact because only the group action changes. -/
private theorem finiteRepGrothendieckPrecompose_shortExact_local
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A)
    (S : ShortComplex (FDRep k A)) (hS : S.ShortExact) :
    (finiteRepGrothendieckPrecompose_shortComplex_local
      (k := k) (A := A) (B := B) φ S).ShortExact := by
  let F : FDRep k A ⥤ ModuleCat k :=
    (forget₂ (FDRep k A) (Rep k A)) ⋙ (forget₂ (Rep k A) (ModuleCat k))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat k` exposes the unchanged linear maps of the original short exact
    -- sequence.
    simpa [F] using hS.map_of_exact F
  let fA : S.X₁ →ₗ[k] S.X₂ := (((forget₂ (FDRep k A) (Rep k A)).map S.f).hom.toLinearMap)
  let gA : S.X₂ →ₗ[k] S.X₃ := (((forget₂ (FDRep k A) (Rep k A)).map S.g).hom.toLinearMap)
  have hExact : Function.Exact fA gA := by
    -- On underlying `k`-modules, `S` is exact.
    simpa [F, fA, gA] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hInj : Function.Injective fA := by
    -- The left map stays injective after forgetting to modules.
    simpa [F, fA] using hSF.moduleCat_injective_f
  have hSurj : Function.Surjective gA := by
    -- The right map stays surjective after the same forgetful step.
    simpa [F, gA] using hSF.moduleCat_surjective_g
  let TRep : ShortComplex (Rep k B) :=
    (finiteRepGrothendieckPrecompose_shortComplex_local (k := k) (A := A) (B := B) φ S).map
      (forget₂ (FDRep k B) (Rep k B))
  have hRepMap : (TRep.map (forget₂ (Rep k B) (ModuleCat k))).ShortExact := by
    -- After precomposition, the underlying module short complex uses the same linear maps, so the
    -- exactness/injectivity/surjectivity data transfers unchanged.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (TRep.map (forget₂ (Rep k B) (ModuleCat k)))).2 <| by
            simpa [TRep, finiteRepGrothendieckPrecompose_shortComplex_local,
              finiteRep_precompose_map_local, fA, gA] using hExact
    · rw [ModuleCat.mono_iff_injective]
      simpa [TRep, finiteRepGrothendieckPrecompose_shortComplex_local,
        finiteRep_precompose_map_local, fA] using hInj
    · rw [ModuleCat.epi_iff_surjective]
      simpa [TRep, finiteRepGrothendieckPrecompose_shortComplex_local,
        finiteRep_precompose_map_local, gA] using hSurj
  have hRepShort : TRep.ShortExact := by
    -- Reflect short exactness from `ModuleCat k` back to `Rep k B`.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := TRep) (F := forget₂ (Rep k B) (ModuleCat k))).1 hRepMap
  have hTRep :
      ((finiteRepGrothendieckPrecompose_shortComplex_local
          (k := k) (A := A) (B := B) φ S).map
        (forget₂ (FDRep k B) (Rep k B))).ShortExact := by
    -- The explicit `Rep` short complex is definitionally the image of the `FDRep` one.
    simpa [TRep] using hRepShort
  -- Reflect once more from `Rep k B` back to `FDRep k B`.
  exact
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := finiteRepGrothendieckPrecompose_shortComplex_local
        (k := k) (A := A) (B := B) φ S)
      (F := forget₂ (FDRep k B) (Rep k B))).1 hTRep

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: pulling back along a monoid hom preserves the defining
Grothendieck relations because it preserves short exact sequences on the unchanged underlying
vector-space carriers. -/
private theorem finiteRepGrothendieckRelations_le_precomposeLift_ker
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A) :
    finiteRepGrothendieckRelations k A ≤
      (finiteRepGrothendieckPrecomposeLift (k := k) φ).ker := by
  -- Evaluate the precomposition lift on each defining short-exact-sequence generator.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  have hPre :
      (finiteRepGrothendieckPrecompose_shortComplex_local
        (k := k) (A := A) (B := B) φ S).ShortExact :=
    finiteRepGrothendieckPrecompose_shortExact_local
      (k := k) (A := A) (B := B) φ S hS
  have hRelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := B)
      (finiteRepGrothendieckPrecompose_shortComplex_local
        (k := k) (A := A) (B := B) φ S) hPre
  -- The free lift rewrites the defining relation to the corresponding relation in the pulled-back
  -- short exact sequence over `B`.
  change
    finiteRepGrothendieckPrecomposeLift (k := k) φ
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  change
    [FDRep.of (S.X₂.ρ.comp φ)]₀ -
        [FDRep.of (S.X₁.ρ.comp φ)]₀ -
        [FDRep.of (S.X₃.ρ.comp φ)]₀ = 0
  calc
    [FDRep.of (S.X₂.ρ.comp φ)]₀ -
        [FDRep.of (S.X₁.ρ.comp φ)]₀ -
        [FDRep.of (S.X₃.ρ.comp φ)]₀ =
      ([FDRep.of (S.X₁.ρ.comp φ)]₀ + [FDRep.of (S.X₃.ρ.comp φ)]₀) -
        [FDRep.of (S.X₁.ρ.comp φ)]₀ -
        [FDRep.of (S.X₃.ρ.comp φ)]₀ := by
          rw [hRelation]
    _ = 0 := by
          abel

/-- Helper for Theorem 16-16.1-5: pull back Serre's Grothendieck classes along a group
homomorphism. -/
private def finiteRepGrothendieckPrecompose
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A) :
    R₀[k](A) →+ R₀[k](B) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k A)
    (finiteRepGrothendieckPrecomposeLift (k := k) φ)
    (finiteRepGrothendieckRelations_le_precomposeLift_ker (k := k) φ)

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: the pullback map on `R₀` sends a generator class to the class of
the pulled-back representation. -/
@[simp] private theorem finiteRepGrothendieckPrecompose_apply_class
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A) (V : FDRep k A) :
    finiteRepGrothendieckPrecompose (k := k) φ [V]₀ =
      [FDRep.of (V.ρ.comp φ)]₀ := by
  rfl

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: pulling back the trivial class stays trivial. -/
@[simp] private theorem finiteRepGrothendieckPrecompose_trivial_class
    {A : Type u} [Group A] {B : Type u} [Group B] (φ : B →* A) :
    finiteRepGrothendieckPrecompose (k := k) φ
        (([𝟙_ (FDRep k A)]₀ : R₀[k](A))) =
      ([𝟙_ (FDRep k B)]₀ : R₀[k](B)) := by
  rw [finiteRepGrothendieckPrecompose_apply_class]
  rfl

omit [CharP k p] [Fact p.Prime] [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: precomposing a representation with a group equivalence preserves
irreducibility over the coefficient field. -/
theorem isIrreducible_comp_mulEquiv_forSurjectivity
    {A : Type u} [Group A] {B : Type u} [Group B]
    {V : Type u} [AddCommGroup V] [Module k V]
    (e : A ≃* B) (σ : Representation k B V)
    [Representation.IsIrreducible σ] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  -- Transport subrepresentations across the group equivalence and reuse irreducibility of `σ`.
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro b x hx
        simpa using W.apply_mem_toSubmodule (e.symm b) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: on the prime-to-`p` factor, a simple class comes from a
concrete finite projective owner, not only abstractly from the Cartan range. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_local
    {S : Type u} [Group S] {P M : Type u} [AddCommGroup P] [Module k[S] P]
    [AddCommGroup M] [Module k[S] M] [IsSimpleModule k[S] M]
    {f : P →ₗ[k[S]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[S] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[S]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[S] P := Submodule.span k[S] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    -- The chosen cyclic generator maps to a nonzero element of the simple target.
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
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[S] P x) := by
    -- Once the cyclic span is all of `P`, the canonical map from `k[S]` is onto.
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[S]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[S] P x) hsurj

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: a normal `p`-subgroup acts trivially on an irreducible
characteristic-`p` representation. -/
private theorem isTrivial_restrict_normal_pSubgroup_of_isIrreducible_local
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (N : Subgroup G) [Finite N] [N.Normal] (hN : IsPGroup p N) :
    Representation.IsTrivial (ρ.comp N.subtype) := by
  classical
  let ρN : Representation k N V := ρ.comp N.subtype
  letI : Nontrivial V := by
    by_contra hV
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact (show (⊥ : Subrepresentation ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <| by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (show x = 0 from Subsingleton.elim x 0)
  let U : Subrepresentation ρ :=
    { toSubmodule := ρN.invariants
      apply_mem_toSubmodule := by
        intro g x hx
        rw [ρN.mem_invariants] at hx ⊢
        intro n
        have hconj : g⁻¹ * (n : G) * g ∈ N :=
          Subgroup.Normal.conj_mem' inferInstance (n : G) n.2 g
        have hxconj : ρ (g⁻¹ * (n : G) * g) x = x := hx ⟨g⁻¹ * (n : G) * g, hconj⟩
        calc
          ρ (n : G) (ρ g x) = ρ ((n : G) * g) x := by
            simp [map_mul]
          _ = ρ (g * (g⁻¹ * (n : G) * g)) x := by
                simp [mul_assoc]
          _ = ρ g (ρ (g⁻¹ * (n : G) * g) x) := by
                simp [map_mul]
          _ = ρ g x := by rw [hxconj] }
  have hU_ne_bot : U ≠ ⊥ := by
    -- The restricted `p`-group action fixes a nonzero vector in characteristic `p`.
    intro hU
    exact
      ((invariants_ne_bot_of_isPGroup_charP (ρ := ρN) hN) <|
        by simpa [U] using congrArg Subrepresentation.toSubmodule hU)
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  -- Irreducibility upgrades the invariant subspace to the whole carrier.
  refine ⟨fun n ↦ ?_⟩
  ext x
  have hxU : x ∈ U.toSubmodule := by
    rw [hU_top]
    exact Submodule.mem_top
  have hx : x ∈ ρN.invariants := by
    simpa [U] using hxU
  exact (ρN.mem_invariants x).1 hx n

omit [IsAlgClosed k] in
/-- A normal `p`-subgroup acts trivially on an irreducible representation in characteristic
`p`. This public bridge exposes the normal-subgroup fixed-vector argument used in Theorem
`16-16.1-5` for later Cartan and Brauer-character arguments. -/
theorem restrict_normal_pSubgroup_isTrivial_of_isIrreducible
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (N : Subgroup G) [Finite N] [N.Normal] (hN : IsPGroup p N) :
    Representation.IsTrivial (ρ.comp N.subtype) := by
  -- Reuse the theorem-local proof that combines the `p`-group fixed-vector lemma with
  -- irreducibility of the ambient representation.
  exact isTrivial_restrict_normal_pSubgroup_of_isIrreducible_local
    (p := p) (ρ := ρ) N hN

/-- Helper for Theorem 16-16.1-5: a cyclic subgroup splits into its prime-to-`p` and `p` parts. -/
private theorem cyclic_subgroup_exists_primeToP_pGroup_split_local
    {H : Type u} [Group H] [Finite H]
    (C : Subgroup H) (hC : IsCyclic C) :
    ∃ (S P : Subgroup H),
      S ≤ C ∧
        P ≤ C ∧
          Nat.Coprime p (Nat.card S) ∧
            IsPGroup p P ∧
              S ≤ Subgroup.centralizer (P : Set H) ∧
                Disjoint S P ∧
                  C = S ⊔ P := by
  letI : IsCyclic C := hC
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := C)
  let cH : H := c
  let S : Subgroup H := Subgroup.zpowers (pRegularComponent p cH)
  let P : Subgroup H := Subgroup.zpowers (pUnipotentComponent p cH)
  have hC_eq : C = Subgroup.zpowers cH := by
    -- The chosen generator of `C` still generates the same subgroup inside `H`.
    ext x
    constructor
    · intro hx
      have hxgen : (⟨x, hx⟩ : C) ∈ Subgroup.zpowers c := hcgen ⟨x, hx⟩
      rcases (Subgroup.mem_zpowers_iff.mp hxgen) with ⟨n, hn⟩
      exact (Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩)
    · intro hx
      exact ((Subgroup.zpowers_le).2 c.2) hx
  let hdecomp :=
    p_component_decomposition_exists (p := p) cH (isOfFinOrder_of_finite cH)
  have hS_le : S ≤ C := by
    -- The `p`-regular component is a power of the generator `c`.
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hdecomp.right_mem_zpowers
  have hP_le : P ≤ C := by
    -- The `p`-unipotent component is also a power of the generator `c`.
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hdecomp.left_mem_zpowers
  have hS_coprime : Nat.Coprime p (Nat.card S) := by
    -- The cyclic subgroup generated by the `p`-regular component has prime-to-`p` order.
    -- (`-Nat.card_eq_fintype_card`: a concurrent global `Fintype`-from-`Finite` instance otherwise
    -- rewrites `Nat.card` to `Fintype.card` and blocks `Nat.card_zpowers`.)
    simpa [S, Nat.card_zpowers, -Nat.card_eq_fintype_card] using hdecomp.isPRegular
  have hP_isPGroup : IsPGroup p P := by
    -- The cyclic subgroup generated by the `p`-unipotent component is a `p`-group.
    rw [isPGroup_iff_forall_isPElement]
    intro y
    have hy_div :
        orderOf ((y : P) : H) ∣ orderOf (pUnipotentComponent p cH) :=
      orderOf_dvd_of_mem_zpowers y.2
    rcases hdecomp.isPElement with ⟨n, hn⟩
    have hy_pow : orderOf ((y : P) : H) ∣ p ^ n := by
      simpa [hn] using hy_div
    rcases (Nat.dvd_prime_pow Fact.out).1 hy_pow with ⟨m, -, hm⟩
    exact ⟨m, by simpa [Subgroup.orderOf_mk] using hm⟩
  have hS_cent : S ≤ Subgroup.centralizer (P : Set H) := by
    -- Both factors are generated by powers of the same element, so they commute.
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases (Subgroup.mem_zpowers_iff.mp hs) with ⟨m, rfl⟩
    rcases (Subgroup.mem_zpowers_iff.mp hu) with ⟨n, rfl⟩
    simpa using ((hdecomp.commute.zpow_left n).zpow_right m).eq
  have hSP_disjoint : Disjoint S P := by
    -- An element in both factors has order both prime to `p` and a `p`-power.
    rw [disjoint_iff]
    ext z
    constructor
    · intro hz
      rw [Subgroup.mem_bot]
      rw [Subgroup.mem_inf] at hz
      have hzS : z ∈ S := hz.1
      have hzP : z ∈ P := hz.2
      have hzDivS : orderOf z ∣ orderOf (pRegularComponent p cH) :=
        orderOf_dvd_of_mem_zpowers hzS
      have hzDivP : orderOf z ∣ orderOf (pUnipotentComponent p cH) :=
        orderOf_dvd_of_mem_zpowers hzP
      rcases hdecomp.isPElement with ⟨n, hn⟩
      have hzPow : orderOf z ∣ p ^ n := by
        simpa [hn] using hzDivP
      rcases (Nat.dvd_prime_pow Fact.out).1 hzPow with ⟨m, -, hm⟩
      have hzOne : orderOf z = 1 := by
        exact hm.trans (Nat.Coprime.eq_one_of_dvd (hdecomp.isPRegular.pow_left m) (hm ▸ hzDivS))
      exact orderOf_eq_one_iff.mp hzOne
    · intro hz
      rw [Subgroup.mem_inf]
      have hz1 : z = 1 := Subgroup.mem_bot.mp hz
      constructor <;> simp [hz1]
  have hC_le_sup : C ≤ S ⊔ P := by
    -- The original generator is the product of its chosen `p`-regular and `p`-unipotent parts.
    have hc_sup : cH ∈ S ⊔ P := by
      rw [show cH = pRegularComponent p cH * pUnipotentComponent p cH by
        calc
          cH = pUnipotentComponent p cH * pRegularComponent p cH := hdecomp.eq_mul
          _ = pRegularComponent p cH * pUnipotentComponent p cH := by
                simpa using hdecomp.commute.eq]
      exact Subgroup.mul_mem (S ⊔ P)
        ((show S ≤ S ⊔ P from le_sup_left) (Subgroup.mem_zpowers (pRegularComponent p cH)))
        ((show P ≤ S ⊔ P from le_sup_right) (Subgroup.mem_zpowers (pUnipotentComponent p cH)))
    rw [hC_eq]
    exact (Subgroup.zpowers_le).2 hc_sup
  have hsup_le_C : S ⊔ P ≤ C := sup_le hS_le hP_le
  refine ⟨S, P, hS_le, hP_le, hS_coprime, hP_isPGroup, hS_cent, hSP_disjoint, ?_⟩
  exact le_antisymm hC_le_sup hsup_le_C

/-- Helper for Theorem 16-16.1-5: if `Q` centralizes a cyclic factor `C`, then it centralizes the
`p`-primary factor cut out inside `C`. -/
private theorem qgroup_centralizes_pgroup_factor_of_cyclic_split_local
    {H : Type u} [Group H] {q : ℕ} [Fact q.Prime]
    {C Q P₀ : Subgroup H}
    (hCQcent : C ≤ Subgroup.centralizer (Q : Set H))
    (hP₀C : P₀ ≤ C) :
    Q ≤ Subgroup.centralizer (P₀ : Set H) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (hCQcent (hP₀C hu) q hq).symm

/-- Helper for Theorem 16-16.1-5: after splitting the cyclic factor of an elementary subgroup,
one obtains a complement by a prime-to-`p` subgroup and a `p`-group. -/
private theorem primeToP_pGroup_complement_of_cyclic_split_and_qgroup_complement_local
    {H : Type u} [Group H] {q : ℕ} [Fact q.Prime]
    {C Q S₀ P₀ : Subgroup H}
    [Finite Q]
    (hCQ : C.IsComplement' Q)
    (hCQcent : C ≤ Subgroup.centralizer (Q : Set H))
    (hQ : IsPGroup q Q) (hqp : q ≠ p)
    (hS₀C : S₀ ≤ C) (hP₀C : P₀ ≤ C)
    (hS₀ : Nat.Coprime p (Nat.card S₀)) (hP₀ : IsPGroup p P₀)
    (hS₀cent : S₀ ≤ Subgroup.centralizer (P₀ : Set H))
    (hS₀P₀disj : Disjoint S₀ P₀)
    (hCeq : C = S₀ ⊔ P₀) :
    Nat.Coprime p (Nat.card ↥(S₀ ⊔ Q)) ∧
      (S₀ ⊔ Q) ≤ Subgroup.centralizer (P₀ : Set H) ∧
      (S₀ ⊔ Q).IsComplement' P₀ := by
  have hcent_norm {B : Subgroup H} :
      Subgroup.centralizer (B : Set H) ≤ Subgroup.normalizer B := by
    -- Centralizing a subgroup is stronger than normalizing it.
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      have hzEq : z * u * z⁻¹ = u := by
        calc
          z * u * z⁻¹ = u * z * z⁻¹ := by rw [← hz u hu]
          _ = u := by simp [mul_assoc]
      rw [hzEq]
      exact hu
    · intro hu
      let q : H := z * u * z⁻¹
      have hq : q ∈ B := hu
      have hqEq : z * q * z⁻¹ = q := by
        calc
          z * q * z⁻¹ = q * z * z⁻¹ := by rw [← hz q hq]
          _ = q := by simp [mul_assoc, q]
      have huEq : u = z * u * z⁻¹ := by
        calc
          u = z⁻¹ * q * z := by simp [q, mul_assoc]
          _ = z⁻¹ * (z * q * z⁻¹) * z := by rw [hqEq]
          _ = q := by simp [mul_assoc]
          _ = z * u * z⁻¹ := rfl
      rw [huEq]
      exact hu
  have hQcent : Q ≤ Subgroup.centralizer (P₀ : Set H) :=
    qgroup_centralizes_pgroup_factor_of_cyclic_split_local
      (q := q) (C := C) (Q := Q) (P₀ := P₀)
      (hCQcent := hCQcent) (hP₀C := hP₀C)
  have hS₀Qcent : (S₀ ⊔ Q) ≤ Subgroup.centralizer (P₀ : Set H) := by
    -- Both the `S₀` and `Q` factors centralize `P₀`.
    rw [sup_le_iff]
    exact ⟨hS₀cent, hQcent⟩
  have hS₀Qdisj : Disjoint S₀ Q := hCQ.disjoint.mono_left hS₀C
  have hS₀Qnorm : S₀ ≤ Subgroup.normalizer Q := by
    -- Centralizing `Q` is enough to normalize it.
    intro s hs
    exact (hcent_norm (B := Q)) (hCQcent (hS₀C hs))
  have hS₀Qset : (↑(S₀ ⊔ Q) : Set H) = (↑S₀ : Set H) * (↑Q : Set H) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S₀ Q hS₀Qnorm
  have hSQP₀disj : Disjoint (S₀ ⊔ Q) P₀ := by
    -- A mixed factorization inside `P₀` collapses to the identity by the two disjointness
    -- relations.
    rw [Subgroup.disjoint_def]
    intro x hx hxP
    have hx' : (x : H) ∈ (↑(S₀ ⊔ Q) : Set H) := hx
    rw [hS₀Qset] at hx'
    rcases hx' with ⟨s, hs, u, hu, hxu⟩
    have hsuP : s * u ∈ P₀ := by
      simpa [hxu] using hxP
    have hsInC : s ∈ C := hS₀C hs
    have huC : u ∈ C := by
      have hsInvC : s⁻¹ ∈ C := C.inv_mem hsInC
      have hmulC : s⁻¹ * (s * u) ∈ C := C.mul_mem hsInvC (hP₀C hsuP)
      simpa [mul_assoc] using hmulC
    have hCQdisj := hCQ.disjoint
    rw [Subgroup.disjoint_def] at hCQdisj
    have hu1 : u = 1 := hCQdisj huC hu
    have hsP : s ∈ P₀ := by
      simpa [hu1] using hsuP
    have hS₀P₀disj' := hS₀P₀disj
    rw [Subgroup.disjoint_def] at hS₀P₀disj'
    have hs1 : s = 1 := hS₀P₀disj' hs hsP
    calc
      x = s * u := hxu.symm
      _ = 1 := by simp [hs1, hu1]
  have hS₀Qcard : Nat.card ↥(S₀ ⊔ Q) = Nat.card S₀ * Nat.card Q := by
    -- The join is literally the product set because `S₀` normalizes `Q`.
    let f : S₀ × Q → ↥(S₀ ⊔ Q) := fun x ↦
      ⟨(x.1 : H) * x.2, by exact Subgroup.mul_mem_sup x.1.2 x.2.2⟩
    have hf_bij : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro a b hab
        have hmul : (a.1 : H) * a.2 = (b.1 : H) * b.2 := congrArg Subtype.val hab
        exact (Subgroup.mul_injective_of_disjoint hS₀Qdisj) hmul
      · intro x
        have hx : (x : H) ∈ (↑S₀ : Set H) * (↑Q : Set H) := by
          rw [← hS₀Qset]
          exact x.2
        rcases hx with ⟨s, hs, u, hu, hsu⟩
        refine ⟨(⟨s, hs⟩, ⟨u, hu⟩), ?_⟩
        exact Subtype.ext hsu
    simpa [Nat.card_prod] using (Nat.card_eq_of_bijective f hf_bij).symm
  have hQcop : Nat.Coprime p (Nat.card Q) :=
    coprime_card_of_isPGroup_of_ne (p := p) (q := q) hqp.symm hQ
  have hSQcop : Nat.Coprime p (Nat.card ↥(S₀ ⊔ Q)) := by
    -- Both factors in the new left side have order prime to `p`.
    rw [hS₀Qcard]
    exact hS₀.mul_right hQcop
  have hsup_top : (S₀ ⊔ Q) ⊔ P₀ = ⊤ := by
    calc
      (S₀ ⊔ Q) ⊔ P₀ = (S₀ ⊔ P₀) ⊔ Q := by ac_rfl
      _ = C ⊔ Q := by rw [← hCeq]
      _ = ⊤ := hCQ.sup_eq_top
  have hSQP₀norm : (S₀ ⊔ Q) ≤ Subgroup.normalizer P₀ := by
    -- The whole new left factor centralizes `P₀`.
    intro x hx
    exact (hcent_norm (B := P₀)) (hS₀Qcent hx)
  have hmul_univ : ((↑(S₀ ⊔ Q) : Set H) * (↑P₀ : Set H)) = (Set.univ : Set H) := by
    calc
      ((↑(S₀ ⊔ Q) : Set H) * (↑P₀ : Set H)) = ↑((S₀ ⊔ Q) ⊔ P₀) := by
        symm
        exact Subgroup.coe_mul_of_left_le_normalizer_right (S₀ ⊔ Q) P₀ hSQP₀norm
      _ = Set.univ := by simp [hsup_top]
  exact ⟨hSQcop, hS₀Qcent,
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hSQP₀disj hmul_univ⟩

/-- Helper for Theorem 16-16.1-5: every ordinary elementary subgroup admits the source-faithful
split into a prime-to-`p` factor and a `p`-group factor. -/
theorem elementary_primeToP_pGroup_complement_forSurjectivity
    [Finite G] (H : Subgroup G) (hH : IsElementary H) :
    ∃ (S P : Subgroup H),
      Nat.Coprime p (Nat.card S) ∧
        IsPGroup p P ∧
          S ≤ Subgroup.centralizer (P : Set H) ∧
            S.IsComplement' P := by
  letI : Finite H := Finite.of_injective H.subtype H.subtype_injective
  rcases hH with ⟨q, C, Q, hCQ⟩
  letI : Fact q.Prime := ⟨hCQ.prime⟩
  letI : Finite Q := hCQ.finite_pGroup_factor
  by_cases hqp : q = p
  · subst hqp
    -- When the elementary prime matches `p`, the original decomposition already has the required
    -- form.
    exact ⟨C, Q, hCQ.coprime_card, hCQ.isPGroup, hCQ.centralizes, hCQ.isComplement⟩
  · obtain ⟨S₀, P₀, hS₀C, hP₀C, hS₀, hP₀, hS₀cent, hS₀P₀disj, hCeq⟩ :=
      cyclic_subgroup_exists_primeToP_pGroup_split_local (p := p) C hCQ.cyclic
    obtain ⟨hSQ, hPcent, hSPcomp⟩ :=
      primeToP_pGroup_complement_of_cyclic_split_and_qgroup_complement_local
        (p := p) (hCQ := hCQ.isComplement) (hCQcent := hCQ.centralizes)
        (hQ := hCQ.isPGroup) (hqp := hqp) (hS₀C := hS₀C) (hP₀C := hP₀C)
        (hS₀ := hS₀) (hP₀ := hP₀) (hS₀cent := hS₀cent) (hS₀P₀disj := hS₀P₀disj)
        (hCeq := hCeq)
    exact ⟨S₀ ⊔ Q, P₀, hSQ, hP₀, hPcent, hSPcomp⟩

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: every simple finite-dimensional `k[S]`-representation admits a
finite projective envelope inside the canonical projective-owner category. -/
private theorem exists_finite_projective_envelope_of_simple_local
    {S : Type u} [Group S] [Finite S]
    (U : FDRep k S) [Simple U] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k S,
      ∃ f : P.V →ₗ[k[S]] asModule U.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k S U := U.ρ
  letI : Module k[S] U := by
    -- Expose the ambient `k[S]`-module structure carried by the owner `U`.
    simpa [ρ] using (inferInstance : Module k[S] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Categorical simplicity of `U` implies irreducibility of its bundled representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple U)
  letI : IsSimpleModule k[S] U := by
    -- The projective-envelope owner theorem is stated for `k[S]`-modules.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[S] := ModuleCat.of k[S] U
  let _ : Module.Finite k k[S] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[S] := IsArtinianRing.of_finite k k[S]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[S] P' :=
    moduleFinite_of_projectiveEnvelope_simple_local (k := k) (S := S) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[S] := by
    -- Repackage the envelope source as a finite projective owner.
    refine ⟨P', ?_⟩
    change Module.Finite k[S] P'
    exact hfinite
  have hproj : Module.Projective k[S] Pfg := by
    -- Projectivity is already part of the envelope source structure.
    change Module.Projective k[S] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k S := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  · simpa [P, ρ] using hf'

omit [IsAlgClosed k] [Fact p.Prime] in
/-- Helper for Theorem 16-16.1-5: once `p ∤ |S|`, the source of a projective envelope already has
the same Grothendieck class as its target, because Maschke makes the target projective. -/
private theorem projectiveEnvelope_finiteRepClass_eq_target_of_order_prime_to_p_local
    {S : Type u} [Group S] [Finite S]
    (hS : ¬ p ∣ Nat.card S)
    {π : FDRep k S}
    {P : FiniteProjectiveGroupAlgebraModule k S}
    {f : P.V →ₗ[k[S]] asModule π.ρ}
    (hf : f.IsProjectiveEnvelope) :
    [P.toFiniteRep]₀ = [π]₀ := by
  -- Route correction: replay the Chapter `15` Maschke argument locally instead of importing the
  -- aggregate proposition file. The source route is unchanged: the target module is projective
  -- because `p ∤ |S|`, so a projective envelope is already isomorphic to the target.
  let M : ModuleCat k[S] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k S) (Rep k S)).obj π)
  have hM_projective : Module.Projective k[S] M := by
    -- Maschke's theorem makes the group algebra semisimple in the prime-to-`p` case.
    let _ : Fintype S := Fintype.ofFinite S
    let _ : NeZero (Nat.card S : k) := NeZero.of_not_dvd k hS
    let _ : IsSemisimpleRing k[S] := by
      infer_instance
    exact Module.projective_of_isSemisimpleRing k[S] M
  let _ : Module.Projective k[S] M := hM_projective
  let f' : P.V →ₗ[k[S]] M := by
    -- The target module is just `π` viewed through its canonical `ModuleCat` owner.
    simpa using f
  have hf' : f'.IsProjectiveEnvelope := by
    -- The projective-envelope structure is definitionally unchanged by the rebundling.
    simpa [f'] using hf
  obtain ⟨eLin⟩ := hf'.nonempty_linearEquiv_target
  let eRep' : P.toRep ≅ ((forget₂ (FDRep k S) (Rep k S)).obj π) :=
    Rep.ofModuleMonoidAlgebra.mapIso eLin.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k S) (Rep k S)).obj π)).symm
  let eRep : ((forget₂ (FDRep k S) (Rep k S)).obj P.toFiniteRep) ≅
      ((forget₂ (FDRep k S) (Rep k S)).obj π) := by
    -- Forgetting `P.toFiniteRep` returns the same `Rep` object as `P.toRep`.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep] using eRep'
  let e : P.toFiniteRep ≅ π :=
    ⟨(FDRep.forget₂HomLinearEquiv P.toFiniteRep π) eRep.hom,
      (FDRep.forget₂HomLinearEquiv π P.toFiniteRep) eRep.inv,
      by
        apply (forget₂ (FDRep k S) (Rep k S)).map_injective
        change eRep.hom ≫ eRep.inv = 𝟙 _
        exact eRep.hom_inv_id,
      by
        apply (forget₂ (FDRep k S) (Rep k S)).map_injective
        change eRep.inv ≫ eRep.hom = 𝟙 _
        exact eRep.inv_hom_id⟩
  -- Isomorphic finite-dimensional owners define the same class in `R₀[k](S)`.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := S) ⟨e⟩

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: on the prime-to-`p` factor, a simple class comes from a
concrete finite projective owner, not only abstractly from the Cartan range. -/
private theorem exists_projective_owner_of_simple_of_order_prime_to_p
    {S : Type u} [Group S] [Finite S]
    (hS : Nat.Coprime p (Nat.card S)) (U : FDRep k S) [Simple U] :
    ∃ Q : FiniteProjectiveGroupAlgebraModule k S, cartanHom k S [Q]ₚ₀ = [U]₀ := by
  have hS_not_dvd : ¬ p ∣ Nat.card S :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp hS
  obtain ⟨Q, f, hf⟩ := exists_finite_projective_envelope_of_simple_local (k := k) (U := U)
  refine ⟨Q, ?_⟩
  -- Maschke makes the target itself projective, so the projective envelope already has the same
  -- Grothendieck class as the simple target.
  calc
    cartanHom k S [Q]ₚ₀ = [Q.toFiniteRep]₀ := by
      exact cartanHom_projectiveClass_eq k S Q
    _ = [U]₀ := by
      simpa using
        (projectiveEnvelope_finiteRepClass_eq_target_of_order_prime_to_p_local
          (p := p) (k := k) (S := S) hS_not_dvd (π := U) (P := Q) (f := f) hf)

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: on a simple representation of `S × P`, the right `p`-group
factor acts trivially. -/
theorem simple_right_factor_isTrivial_of_isPGroup
    {S : Type u} [Group S] [Finite S] {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P) (τ : FDRep k (S × P)) [Simple τ] :
    Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P)) := by
  letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
  let N : Subgroup (S × P) := (⊥ : Subgroup S).prod (⊤ : Subgroup P)
  let eN : P ≃* N :=
    { toFun := fun p' ↦ ⟨(1, p'), by
        change ((1 : S), p') ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
        exact ⟨by simp, by simp⟩⟩
      invFun := fun n ↦ n.1.2
      left_inv := by
        intro p'
        rfl
      right_inv := by
        intro n
        apply Subtype.ext
        rcases n with ⟨⟨s, p'⟩, hn⟩
        change (1, p') = (s, p')
        have hs : s = 1 := by
          simpa [N] using hn.1
        simp [hs]
      map_mul' := by
        intro p₁ p₂
        apply Subtype.ext
        simp }
  have hN_p : IsPGroup p N := hP.of_equiv eN
  letI : Representation.IsTrivial (τ.ρ.comp N.subtype) :=
    isTrivial_restrict_normal_pSubgroup_of_isIrreducible_local
      (p := p) (k := k) (ρ := τ.ρ) N hN_p
  -- Evaluate the normal-subgroup triviality on the explicit right-axis elements.
  refine ⟨fun p' ↦ ?_⟩
  ext x
  let n : N := ⟨(1, p'), by
    change ((1 : S), p') ∈ (⊥ : Subgroup S).prod (⊤ : Subgroup P)
    exact ⟨by simp, by simp⟩⟩
  change ((τ.ρ.comp N.subtype) n) x = x
  exact isTrivial_apply (τ.ρ.comp N.subtype) n x

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: if the right factor acts trivially, the whole `S × P`-action
inflates from the left factor along `fst`. -/
private theorem representation_eq_comp_inl_comp_fst_of_trivial_right
    {S : Type u} [Group S] {P : Type u} [Group P]
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k (S × P) V)
    (hTriv : Representation.IsTrivial (ρ.comp (MonoidHom.inr S P))) :
    ρ = (ρ.comp (MonoidHom.inl S P)).comp (MonoidHom.fst S P) := by
  letI : Representation.IsTrivial (ρ.comp (MonoidHom.inr S P)) := hTriv
  ext g x
  rcases g with ⟨s, p'⟩
  calc
    ρ (s, p') x = ρ ((s, 1) * (1, p')) x := by simp
    _ = ρ (s, 1) (ρ (1, p') x) := by
          rw [map_mul]
          rfl
    _ = ρ (s, 1) x := by
          have hp' : ρ (1, p') x = x := by
            change ((ρ.comp (MonoidHom.inr S P)) p') x = x
            exact isTrivial_apply (ρ.comp (MonoidHom.inr S P)) p' x
          simp [hp']
    _ = ((ρ.comp (MonoidHom.inl S P)).comp (MonoidHom.fst S P)) (s, p') x := rfl

omit [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: after killing the right `p`-group factor, a simple
`S × P`-representation comes from an irreducible left-factor representation. -/
theorem split_product_simple_factorization
    {S : Type u} [Group S] {P : Type u} [Group P]
    (τ : FDRep k (S × P)) [Simple τ]
    (hTriv : Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P))) :
    ∃ ρS : Representation k S τ, Representation.IsIrreducible ρS ∧
      τ.ρ = ρS.comp (MonoidHom.fst S P) := by
  let ρS : Representation k S τ := τ.ρ.comp (MonoidHom.inl S P)
  letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
  letI : Representation.IsTrivial (τ.ρ.comp (MonoidHom.inr S P)) := hTriv
  have hρS_irreducible : Representation.IsIrreducible ρS := by
    classical
    -- Pull a nonzero `ρS`-subrepresentation back to an `S × P`-stable subrepresentation of `τ`.
    letI : Nontrivial (Subrepresentation ρS) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro hbot
      have hbot' : (⊥ : Subrepresentation τ.ρ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        simpa [ρS] using congrArg Subrepresentation.toSubmodule hbot
      exact IsSimpleOrder.bot_ne_top hbot'
    refine IsSimpleOrder.of_forall_eq_top ?_
    intro W hW
    let W' : Subrepresentation τ.ρ :=
      { toSubmodule := W.toSubmodule
        apply_mem_toSubmodule := by
          intro g x hx
          rcases g with ⟨s, p'⟩
          have hp' : τ.ρ (1, p') x = x := by
            change ((τ.ρ.comp (MonoidHom.inr S P)) p') x = x
            exact isTrivial_apply (τ.ρ.comp (MonoidHom.inr S P)) p' x
          have hact : τ.ρ (s, p') x = ρS s x := by
            calc
              τ.ρ (s, p') x = τ.ρ ((s, 1) * (1, p')) x := by simp
              _ = τ.ρ (s, 1) (τ.ρ (1, p') x) := by
                    rw [map_mul]
                    rfl
              _ = τ.ρ (s, 1) x := by simp [hp']
              _ = ρS s x := rfl
          exact hact ▸ W.apply_mem_toSubmodule s hx }
    have hW'_ne_bot : W' ≠ ⊥ := by
      intro hW'
      apply hW
      apply Subrepresentation.toSubmodule_injective
      simpa [W', ρS] using congrArg Subrepresentation.toSubmodule hW'
    have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
    apply Subrepresentation.toSubmodule_injective
    simpa [W', ρS] using congrArg Subrepresentation.toSubmodule hW'_top
  -- The triviality of the right factor identifies the full action with inflation from `S`.
  refine ⟨ρS, hρS_irreducible, ?_⟩
  exact representation_eq_comp_inl_comp_fst_of_trivial_right (k := k) τ.ρ hTriv


include instAlgClosedK in
/-- Helper for Theorem 16-16.1-5: for a simple class on an elementary subgroup, Serre's `S × P`
decomposition directly produces the local Cartan witness of size `ordProj[p] |H|`. -/
private theorem simple_class_ordProj_nsmul_mem_cartan_range_of_elementary
    [Finite G] (H : Subgroup G) (hH : IsElementary H)
    (τ : FDRep k H) (hτ : Simple τ) :
    ((ordProj[p] (Nat.card H) : ℕ) • [τ]₀) ∈ (cartanHom k H).range := by
  classical
  haveI : Simple τ := hτ
  haveI : Finite ↥H := Finite.of_injective H.subtype H.subtype_injective
  -- Serre's elementary decomposition `H ≅ S × P` with `S` prime-to-`p` and `P` a `p`-group.
  obtain ⟨S, P, hS, hP, hSPcent, hSPcomp⟩ :=
    elementary_primeToP_pGroup_complement_forSurjectivity (p := p) H hH
  haveI : Finite ↥S := Finite.of_injective S.subtype S.subtype_injective
  haveI : Finite ↥P := Finite.of_injective P.subtype P.subtype_injective
  have hcomm : ∀ s : S, ∀ p' : P, Commute ((s : ↥H)) ((p' : ↥H)) := by
    intro s p'
    exact (Subgroup.mem_centralizer_iff.mp (hSPcent s.2) (p' : ↥H) p'.2).symm
  let e : (S × P) ≃* ↥H := hSPcomp.prodMulEquiv hcomm
  -- Pull `τ` back to `S × P`; it stays simple and the right `p`-group factor acts trivially.
  haveI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
  let τprod : FDRep k (S × P) := FDRep.of (τ.ρ.comp e.toMonoidHom)
  haveI hτprodIrr : Representation.IsIrreducible τprod.ρ :=
    isIrreducible_comp_mulEquiv_forSurjectivity e τ.ρ
  haveI : Simple τprod := FDRep.simple_of_isIrreducible τprod
  have hTriv : Representation.IsTrivial (τprod.ρ.comp (MonoidHom.inr S P)) :=
    simple_right_factor_isTrivial_of_isPGroup (p := p) hP τprod
  obtain ⟨ρS, hρSirr, hfact⟩ := split_product_simple_factorization τprod hTriv
  -- The irreducible left factor `U` on the prime-to-`p` group `S`.
  let U : FDRep k S := FDRep.of ρS
  haveI : Representation.IsIrreducible U.ρ := hρSirr
  haveI : Simple U := FDRep.simple_of_isIrreducible U
  -- A finite projective owner of `U` on `S` (Maschke: `p ∤ |S|`).
  obtain ⟨Q, hQ⟩ := exists_projective_owner_of_simple_of_order_prime_to_p (p := p) hS U
  -- The inflation identity `(U.ρ ∘ fst) ∘ e⁻¹ = τ.ρ` recovering `τ` from the left factor.
  have hrep_eq :
      (U.ρ.comp (MonoidHom.fst S P)).comp e.symm.toMonoidHom = τ.ρ := by
    have hfact' : U.ρ.comp (MonoidHom.fst S P) = τ.ρ.comp e.toMonoidHom := hfact.symm
    rw [hfact']
    ext g x
    show τ.ρ (e.toMonoidHom (e.symm.toMonoidHom g)) x = τ.ρ g x
    simp
  -- The key class identity `[Ind_S^H U]₀ = (Nat.card P) • [τ]₀`.
  have hidentity :
      [FDRep.subgroupInduction (k := k) (G := ↥H) (H := S) U]₀ = (Nat.card P : ℕ) • [τ]₀ := by
    -- Step A: the induced representation is the external tensor `U ⊠ r_P` pulled back along `e`.
    haveI : Module.Finite k (Representation.IndV S.subtype U.ρ) :=
      FDRep.subgroupInduction_finite U
    have hEquiv :
        Representation.Equiv (Representation.ind S.subtype U.ρ)
          ((U.ρ ⊠ leftRegular k P).comp e.symm.toMonoidHom) :=
      isomorphic_to_externalTensor_left_regular_of_induced_of_direct_product
        S P (Representation.ind S.subtype U.ρ) U.ρ
        (Representation.Equiv.refl _) hSPcomp hcomm
    have hcls1 :
        [FDRep.subgroupInduction (k := k) (G := ↥H) (H := S) U]₀ =
          [FDRep.of ((U.ρ ⊠ leftRegular k P).comp e.symm.toMonoidHom)]₀ :=
      finiteRepGrothendieckClass_eq_of_representationEquiv
        (Representation.ind S.subtype U.ρ)
        ((U.ρ ⊠ leftRegular k P).comp e.symm.toMonoidHom) hEquiv
    -- Step B: write as `precompose ∘ extTensorLeft`, collapse the `p`-group regular rep.
    have hcollapse :
        [FDRep.of (leftRegular k P)]₀ = (Nat.card P : ℕ) • [𝟙_ (FDRep k P)]₀ := by
      rw [fdRep_class_eq_finrank_nsmul_trivial_of_isPGroup (p := p) hP
        (FDRep.of (leftRegular k P))]
      congr 1
      letI : Fintype ↥P := Fintype.ofFinite ↥P
      rw [show Module.finrank k (FDRep.of (leftRegular k P)) = Fintype.card ↥P from by
            simpa [Representation.leftRegular] using
              (Module.finrank_finsupp_self (R := k) (ι := (P : Type u)))]
      simp [Nat.card_eq_fintype_card]
    -- The induced class factors through `precompose ∘ extTensorLeft` definitionally.
    have hpre :
        [FDRep.of ((U.ρ ⊠ leftRegular k P).comp e.symm.toMonoidHom)]₀ =
          finiteRepGrothendieckPrecompose e.symm.toMonoidHom
            (extTensorLeft U [FDRep.of (leftRegular k P)]₀) := rfl
    have hunit :
        finiteRepGrothendieckPrecompose e.symm.toMonoidHom
            (extTensorLeft U [𝟙_ (FDRep k P)]₀) =
          [FDRep.of ((U.ρ.comp (MonoidHom.fst S P)).comp e.symm.toMonoidHom)]₀ := by
      simp only [extTensorLeft_apply_class, externalTensor_unit_class_eq_comp_fst,
        finiteRepGrothendieckPrecompose_apply_class, FDRep.of_ρ']
    -- `FDRep.of τ.ρ` has the same underlying representation as `τ`, hence the same class.
    have hτof : [FDRep.of τ.ρ]₀ = [τ]₀ := by
      refine finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := ↥H) ⟨?_⟩
      let fRep : (forget₂ (FDRep k ↥H) (Rep k ↥H)).obj (FDRep.of τ.ρ) ⟶
          (forget₂ (FDRep k ↥H) (Rep k ↥H)).obj τ :=
        Rep.ofHom ⟨LinearMap.id, fun g => by ext x; rfl⟩
      let gRep : (forget₂ (FDRep k ↥H) (Rep k ↥H)).obj τ ⟶
          (forget₂ (FDRep k ↥H) (Rep k ↥H)).obj (FDRep.of τ.ρ) :=
        Rep.ofHom ⟨LinearMap.id, fun g => by ext x; rfl⟩
      refine ⟨(FDRep.forget₂HomLinearEquiv _ _) fRep,
        (FDRep.forget₂HomLinearEquiv _ _) gRep, ?_, ?_⟩
      · apply (forget₂ (FDRep k ↥H) (Rep k ↥H)).map_injective
        ext x; rfl
      · apply (forget₂ (FDRep k ↥H) (Rep k ↥H)).map_injective
        ext x; rfl
    rw [hcls1, hpre, hcollapse, map_nsmul, map_nsmul, hunit, hrep_eq, hτof]
  -- A Cartan preimage for `[Ind_S^H U]₀`, via inducing the projective owner `Q`.
  obtain ⟨x', hx'⟩ :
      ∃ x' : P₀[k](↥H), cartanHom k ↥H x' =
        finiteRep_subgroupInduction (k := k) (G := ↥H) S (cartanHom k S [Q]ₚ₀) :=
    exists_subgroupInduction_cartan_preimage (k := k) (G := ↥H) S [Q]ₚ₀
  have hwit :
      cartanHom k ↥H x' = [FDRep.subgroupInduction (k := k) (G := ↥H) (H := S) U]₀ := by
    rw [hx', hQ, finiteRep_subgroupInduction_apply_class]
  -- `ordProj[p] |H| = |P|`, then assemble.
  have hcard : ordProj[p] (Nat.card H) = Nat.card P := by
    rw [show Nat.card H = Nat.card (S × P) from Nat.card_congr e.toEquiv.symm]
    exact ordProj_card_prod_eq_card_right_of_coprime_left (p := p) hS hP
  rw [hcard, ← hidentity]
  exact ⟨x', hwit⟩

omit [CharP k p] [Fact p.Prime] [IsAlgClosed k] in
/-- Helper for Theorem 16-16.1-5: the simple-basis extension lemma WITHOUT a finiteness hypothesis
on the index type. The proof only sums over the finitely-supported basis expansion, so it applies
over a field of characteristic `p` (where `IsCompleteIrreducibleFamily.finite_index`, which needs
`NeZero (Nat.card G : k)`, is unavailable). -/
private theorem addMonoidHom_nsmul_mem_range_of_simple_basis_local'
    [Finite G] {ι : Type (u + 1)}
    (f : A →+ R₀[k](G))
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (N : ℕ)
    (hπ_range : ∀ i, (N : ℕ) • [π i]₀ ∈ f.range)
    (y : R₀[k](G)) :
    (N : ℕ) • y ∈ f.range := by
  classical
  let b : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hb : ∀ i, (N : ℕ) • b i ∈ f.range := by
    intro i
    simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using hπ_range i
  choose x hx using hb
  refine ⟨(b.repr y).sum fun i a ↦ a • x i, ?_⟩
  calc
    f ((b.repr y).sum fun i a ↦ a • x i)
        = (b.repr y).sum fun i a ↦ a • f (x i) := by
            simp [Finsupp.sum, map_sum, map_zsmul]
    _ = (b.repr y).sum fun i a ↦ a • ((N : ℕ) • b i) := by
          simp [Finsupp.sum, hx]
    _ = (b.repr y).sum fun i a ↦ (N : ℕ) • (a • b i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using (smul_comm (b.repr y i) (N : ℕ) (b i))
    _ = (N : ℕ) • ((b.repr y).sum fun i a ↦ a • b i) := by
          simpa [Finsupp.sum] using
            (Finset.smul_sum
              (s := (b.repr y).support) (f := fun i ↦ (b.repr y i) • b i) (r := (N : ℕ))).symm
    _ = (N : ℕ) • y := by
          rw [show (b.repr y).sum (fun i a ↦ a • b i) = y by
            simpa [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr y]

/-- Helper for Theorem 16-16.1-5: on an elementary subgroup, the `p`-part of the subgroup order
times any modular class belongs to the local Cartan image. -/
private theorem elementary_ordProj_nsmul_mem_cartan_range
    [Finite G] (H : Subgroup G) (hH : IsElementary H) (y : R₀[k](H)) :
    ((ordProj[p] (Nat.card H) : ℕ) • y) ∈ (cartanHom k H).range := by
  classical
  haveI : Finite ↥H := Finite.of_injective H.subtype H.subtype_injective
  -- Choose a complete family of pairwise-nonisomorphic simple representatives on `H`.  We do NOT
  -- need the index type to be finite (the simple-basis argument only sums over a `Finsupp`), which
  -- is essential here since `H` has order divisible by `p`.
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_basis_local (k := k) (G := ↥H)
  -- Each simple representative is handled by the simple-case theorem; the simple-basis lemma then
  -- promotes the multiple to every class.
  refine addMonoidHom_nsmul_mem_range_of_simple_basis_local'
    (G := ↥H) (f := cartanHom k ↥H) (π := π) hπ_pairwise hπ_complete
    (ordProj[p] (Nat.card H)) ?_ y
  intro i
  exact simple_class_ordProj_nsmul_mem_cartan_range_of_elementary
    (p := p) H hH (π i) (hπ_complete.isSimple i)

/-- Helper for Theorem 16-16.1-5: a local Cartan witness on a subgroup stays a Cartan witness
after applying subgroup induction to both the projective source and the finite-dimensional class. -/
private theorem subgroup_induction_nsmul_mem_cartan_range
    [Finite G] (H : Subgroup G) (N : ℕ) (z : R₀[k](H))
    (hlocal : ((N : ℕ) • z) ∈ (cartanHom k H).range) :
    ((N : ℕ) • finiteRep_subgroupInduction (k := k) (G := G) H z) ∈
      (cartanHom k G).range := by
  rcases hlocal with ⟨x, hx⟩
  rcases exists_subgroupInduction_cartan_preimage (k := k) (G := G) H x with ⟨x', hx'⟩
  refine ⟨x', ?_⟩
  -- Choose an induced projective preimage and then rewrite the given local Cartan witness.
  calc
    cartanHom k G x' =
        finiteRep_subgroupInduction (k := k) (G := G) H (cartanHom k H x) := hx'
    _ =
        finiteRep_subgroupInduction (k := k) (G := G) H ((N : ℕ) • z) := by
          rw [hx]
    _ =
        ((N : ℕ) • finiteRep_subgroupInduction (k := k) (G := G) H z) := by
          rw [map_nsmul]

/-- Helper for Theorem 16-16.1-5: after the source-faithful elementary decomposition, Serre's
argument assembles the local Cartan witnesses into a global `p ^ n` witness on `G`. -/
private theorem p_part_nsmul_mem_cartan_range_of_card_factorization
    [Finite G]
    (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m)
    (y : R₀[k](G)) :
    ((p ^ n : ℕ) • y) ∈ (cartanHom k G).range := by
  classical
  letI : AddCommMonoid (R₀[k](G)) :=
    (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
  letI : AddCommGroup (R₀[k](G)) :=
    QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)
  letI : Module ℤ (R₀[k](G)) := AddCommGroup.toIntModule (R₀[k](G))
  obtain ⟨ι, hι, H, hH, z, hz⟩ :=
    grothendieckClass_exists_sum_of_elementary_subgroup_inductions_local
      (k := k) (G := G) y
  letI : Fintype ι := hι
  have hG_ordProj : ordProj[p] (Nat.card G) = p ^ n :=
    ordProj_card_eq_p_pow_of_card_factorization
      (p := p) (G := G) n m hcard hm
  have hterm :
      ∀ i,
        ((p ^ n : ℕ) •
            finiteRep_subgroupInduction (k := k) (G := G) (H i) (z i)) ∈
          (cartanHom k G).range := by
    intro i
    -- First produce the local elementary Cartan witness of size `ordProj[p] |H i|`.
    have hlocal :
        ((ordProj[p] (Nat.card (H i)) : ℕ) • z i) ∈ (cartanHom k (H i)).range :=
      elementary_ordProj_nsmul_mem_cartan_range
        (p := p) (k := k) (G := G) (H := H i) (hH := hH i) (y := z i)
    have hinduced :
        ((ordProj[p] (Nat.card (H i)) : ℕ) •
            finiteRep_subgroupInduction (k := k) (G := G) (H i) (z i)) ∈
          (cartanHom k G).range := by
      -- Transport that local witness to `G` by functoriality of subgroup induction.
      exact
        subgroup_induction_nsmul_mem_cartan_range
          (k := k) (G := G) (H := H i) (N := ordProj[p] (Nat.card (H i)))
          (z := z i) hlocal
    have hcard_dvd : Nat.card (H i) ∣ Nat.card G :=
      by
        simpa using (Subgroup.card_dvd_of_le (show H i ≤ ⊤ from le_top))
    have hord_dvd :
        ordProj[p] (Nat.card (H i)) ∣ ordProj[p] (Nat.card G) :=
      Nat.ordProj_dvd_ordProj_of_dvd Nat.card_pos.ne' hcard_dvd p
    have hpow_dvd : ordProj[p] (Nat.card (H i)) ∣ p ^ n := by
      rw [← hG_ordProj]
      exact hord_dvd
    have hterm₀ :=
      nsmul_mem_cartan_range_of_dvd (k := k) (G := G) hpow_dvd hinduced
    exact hterm₀
  have hsum :
      (∑ i, (p ^ n : ℕ) •
          finiteRep_subgroupInduction (k := k) (G := G) (H i) (z i)) ∈
        (cartanHom k G).range := by
    exact AddSubgroup.sum_mem _ fun i _ ↦ hterm i
  have hsum' :
      ((p ^ n : ℕ) •
          ∑ i, finiteRep_subgroupInduction (k := k) (G := G) (H i) (z i)) ∈
        (cartanHom k G).range := by
    -- Use the finite-sum scalar distribution lemma to match the already assembled termwise witness.
    rw [grothendieck_nsmul_sum
      (k := k) (H := G) (N := p ^ n)
      (f := fun i ↦ finiteRep_subgroupInduction (k := k) (G := G) (H i) (z i))]
    exact hsum
  -- Sum the induced elementary witnesses and rewrite back to the original class `y`.
  simpa [hz] using hsum'

-- Proof sketch: this is Serre's theorem on the `p`-part of the Cartan image, assembled from the
-- elementary-subgroup decomposition and the local Cartan witness on each elementary source. -/
/-- Theorem 16-16.1-5: if `Nat.card G = p ^ n * m` with `m` prime to `p`, then every element of
`R_k(G)` divisible by `p ^ n` lies in the image of the Cartan homomorphism
`c : P_k(G) → R_k(G)`. In Lean, this is recorded as membership in `(cartanHom k G).range`. -/
theorem cartanHom_surjective_on_p_part_multiples
    (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m)
    (y : R₀[k](G)) :
    letI : Finite G := finite_of_card_eq_mul_of_coprime hcard hm
    (p ^ n) • y ∈ (cartanHom k G).range := by
  letI : Finite G := finite_of_card_eq_mul_of_coprime hcard hm
  -- Route correction: the proof now follows the Chapter 17 elementary-induction route directly in
  -- the natural-number scalar owner.
  exact
    p_part_nsmul_mem_cartan_range_of_card_factorization
      (p := p) (k := k) (G := G) n m hcard hm y

-- Proof sketch: represent a cokernel class by some `y : R_k(G)`. The previous theorem places
-- `(p ^ n) • y` in `(cartanHom k G).range`, so the image of `(p ^ n) • y` vanishes in the
-- quotient `R_k(G) ⧸ (cartanHom k G).range`.
/-- If `Nat.card G = p ^ n * m` with `m` prime to `p`, then the cokernel of the Cartan
homomorphism `c : P_k(G) → R_k(G)` is annihilated by `p ^ n`. In Lean, every class in
`cartanCokernel k G` is killed by `p ^ n`. -/
theorem cartanHom_cokernel_annihilated_by_p_part
    (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m) :
    letI : Finite G := finite_of_card_eq_mul_of_coprime hcard hm
    ∀ x : cartanCokernel k G, (p ^ n) • x = 0 := by
  letI : Finite G := finite_of_card_eq_mul_of_coprime hcard hm
  intro x
  -- Descend to a representative in `R₀[k](G)` and apply the range-membership theorem above.
  refine QuotientAddGroup.induction_on x fun y ↦ ?_
  change (p ^ n) • (QuotientAddGroup.mk' (cartanHom k G).range y) = (0 : cartanCokernel k G)
  have hmk :
      QuotientAddGroup.mk' (cartanHom k G).range ((p ^ n) • y) =
        (p ^ n) • (QuotientAddGroup.mk' (cartanHom k G).range y) := by
    exact (QuotientAddGroup.mk' (cartanHom k G).range).map_nsmul y (p ^ n)
  rw [← hmk]
  exact
    cartan_cokernel_p_part_eq_zero (k := k) (G := G) n y
      (cartanHom_surjective_on_p_part_multiples (p := p) (k := k) (G := G) n m hcard hm y)

end

end Representation
