import Serre.Chap14.Proposition_14_14_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped Representation

namespace Representation

section GrothendieckGroup

/-
Domain-style sampling for this item:
* `finiteRepGrothendieckGroup` and `finiteRepGrothendieckClass` in Proposition `14-14.1-1` are
  the source-facing owners for `R₀[L](G)` and its classes.
* `simple_finiteRep_classes_basis_of_complete_family` in Proposition `14-14.1-1` is the chapter's
  canonical basis owner: equality in `R₀[L](G)` is controlled by coefficients in the simple-class
  basis.
* Mathlib's `IsSemisimpleRepresentation` together with the Maschke instance under
  `[NeZero (Nat.card G : K)]` is the canonical semisimplicity owner reused by the
  characteristic-zero specialization below.

Primitive data vs derived API:
* primitive data: the Grothendieck group owner `R₀[L](G)` and semisimplicity of the two
  finite-dimensional representations.
* derived API: the isomorphism criterion in `R₀[L](G)` and its characteristic-zero specialization.

Layer triage:
* source-facing: the characteristic-zero remark that equal Grothendieck classes force
  isomorphism.
* core/canonical in this file:
  `finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple`.
* bridge/view: the characteristic-zero specialization supplying Maschke semisimplicity.
-/

section

variable {L : Type u} {G : Type u} [Field L] [Monoid G]

/-- Helper for Remark 14-14.1-2: an `L[G]`-linear equivalence of owner modules upgrades to a
representation equivalence. -/
private theorem nonempty_equiv_of_asModuleLinearEquiv
    {V : Type u} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    {W : Type u} [AddCommGroup W] [Module L W]
    [FiniteDimensional L W]
    {ρ : Representation L G V} {σ : Representation L G W}
    (e : ρ.asModule ≃ₗ[MonoidAlgebra L G] σ.asModule) :
    Nonempty (ρ.Equiv σ) := by
  -- View the `L[G]`-linear equivalence as an intertwiner, then package it as a representation
  -- equivalence.
  let f : ρ.IntertwiningMap σ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := σ)).symm
      e.toLinearMap
  exact ⟨Representation.Equiv.mk (e.restrictScalars L) f.isIntertwining'⟩

/-- Helper for Remark 14-14.1-2: an `L[G]`-linear equivalence of owner modules preserves the
Grothendieck class. -/
private theorem finiteRepGrothendieckClass_eq_of_asModuleLinearEquiv
    {V : Type u} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    {W : Type u} [AddCommGroup W] [Module L W]
    [FiniteDimensional L W]
    {ρ : Representation L G V} {σ : Representation L G W}
    (e : ρ.asModule ≃ₗ[MonoidAlgebra L G] σ.asModule) :
    [FDRep.of ρ]₀ = [FDRep.of σ]₀ := by
  -- First upgrade the module equivalence to a representation equivalence, then pass to `FDRep`.
  rcases nonempty_equiv_of_asModuleLinearEquiv (L := L) (G := G) e with ⟨eρσ⟩
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G)
    ⟨Representation.Equiv.toFDRepIso eρσ⟩

/-- Helper for Remark 14-14.1-2: the Grothendieck class of a simple finite-dimensional
representation is nonzero. -/
private theorem simple_finiteRep_class_ne_zero
    (τ : FDRep L G) [Simple τ] :
    [τ]₀ ≠ (0 : R₀[L](G)) := by
  let π : Fin 1 → FDRep L G := fun _ ↦ τ
  have hπ_simple : ∀ i, Simple (π i) := by
    intro i
    simpa [π] using (inferInstance : Simple τ)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro i j hij
    exact (False.elim (hij (Subsingleton.elim _ _)))
  have hlin :
      LinearIndependent ℤ (fun i : Fin 1 ↦ [π i]₀) :=
    linearIndependent_simple_finiteRep_classes_of_pairwise_nonisomorphic
      (L := L) (G := G) π hπ_simple hπ_pairwise
  -- Apply linear independence to the unique basis vector in the singleton family.
  simpa [π] using hlin.ne_zero (0 : Fin 1)

/-- Helper for Remark 14-14.1-2: the `L[G]`-module underlying a finite-dimensional
representation. -/
private noncomputable abbrev fdRepAsModule_local (τ : FDRep L G) : ModuleCat (MonoidAlgebra L G) :=
  Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep L G) (Rep L G)).obj τ)

/-- Helper for Remark 14-14.1-2: the underlying representation attached to a finite-dimensional
representation object. -/
private noncomputable abbrev fdRepOwnerRepresentation_local
    (τ : FDRep L G) : Representation L G τ :=
  τ.ρ

/-- Helper for Remark 14-14.1-2: the raw owner type underlying a finite-dimensional
representation, viewed as an `L[G]`-module. -/
private noncomputable abbrev fdRepOwnerModule_local (τ : FDRep L G) :=
  (fdRepOwnerRepresentation_local (L := L) (G := G) τ).asModule

/-- Helper for Remark 14-14.1-2: the owner-module abbreviation inherits the ambient `L`-module
structure. -/
private instance fdRep_owner_module_module_over_field_local (τ : FDRep L G) :
    Module L (fdRepOwnerModule_local (L := L) (G := G) τ) := by
  change Module L ((fdRepOwnerRepresentation_local (L := L) (G := G) τ).asModule)
  infer_instance

/-- Helper for Remark 14-14.1-2: the owner-module abbreviation inherits the `L[G]`-module
structure. -/
private instance fdRep_owner_module_module_over_group_algebra_local (τ : FDRep L G) :
    Module (MonoidAlgebra L G) (fdRepOwnerModule_local (L := L) (G := G) τ) := by
  change Module (MonoidAlgebra L G)
    ((fdRepOwnerRepresentation_local (L := L) (G := G) τ).asModule)
  infer_instance

/-- Helper for Remark 14-14.1-2: the scalar tower on the owner-module abbreviation is the
transported one from the underlying representation. -/
private instance fdRep_owner_module_isScalarTower_local (τ : FDRep L G) :
    IsScalarTower L (MonoidAlgebra L G) (fdRepOwnerModule_local (L := L) (G := G) τ) := by
  let ρτ : Representation L G τ := τ.ρ
  -- Reduce the abbreviation to the canonical `Representation.asModule` owner and reuse the
  -- ambient scalar-tower instance there.
  change IsScalarTower L (MonoidAlgebra L G) (Representation.asModule ρτ)
  letI : Module (MonoidAlgebra L G) (Representation.asModule ρτ) :=
    Representation.instModuleMonoidAlgebraAsModule (ρ := ρτ)
  set_option backward.isDefEq.respectTransparency false in
    exact
      { smul_assoc := by
          intro t x v
          revert t
          apply x.induction_on
          · simp
          · intro y z hy hz
            simp [add_smul, hy, hz]
          · intro s y hy t
            rw [← smul_assoc, smul_eq_mul, hy (t * s), ← smul_eq_mul, smul_assoc]
            aesop }

/-- Helper for Remark 14-14.1-2: the owner-module abbreviation is still finite as an `L`-vector
space. -/
private instance fdRep_owner_module_finite_over_field_local (E : FDRep L G) :
    Module.Finite L (fdRepOwnerModule_local (L := L) (G := G) E) := by
  change Module.Finite L E
  infer_instance

/-- Helper for Remark 14-14.1-2: an `L[G]`-submodule inherits the ambient `L`-module structure by
restricting scalars. -/
private instance groupAlgebra_submodule_module_over_field_local
    {M : Type u} [AddCommGroup M] [Module L M] [Module (MonoidAlgebra L G) M]
    [IsScalarTower L (MonoidAlgebra L G) M]
    (N : Submodule (MonoidAlgebra L G) M) :
    Module L N := by
  let N' : Submodule L M := Submodule.restrictScalars L N
  change Module L N'
  infer_instance

/-- Helper for Remark 14-14.1-2: restricting scalars along `L → L[G]` also gives the inherited
scalar tower on a submodule. -/
private instance groupAlgebra_submodule_isScalarTower_local
    {M : Type u} [AddCommGroup M] [Module L M] [Module (MonoidAlgebra L G) M]
    [IsScalarTower L (MonoidAlgebra L G) M]
    (N : Submodule (MonoidAlgebra L G) M) :
    IsScalarTower L (MonoidAlgebra L G) N := by
  let N' : Submodule L M := Submodule.restrictScalars L N
  change IsScalarTower L (MonoidAlgebra L G) N'
  infer_instance

/-- Helper for Remark 14-14.1-2: choose one representative of each isomorphism class of simple
finite-dimensional `L`-representations of `G`. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep L G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep L G // Simple τ }
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
  let π : ι → FDRep L G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- If two quotient representatives are isomorphic, their quotient classes coincide.
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
      have hqeq : (⟦Quotient.out q⟧ : ι) = (⟦⟨τ, hτ⟩⟧ : ι) := by
        simpa [q] using (Quotient.out_eq q)
      have hq :
          Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact hqeq
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Remark 14-14.1-2: the Grothendieck class of a binary product representation is the
sum of the classes of its two factors. -/
private theorem finiteRepGrothendieckClass_prod_eq_add
    (E F : FDRep L G) :
    [FDRep.of (Representation.prod E.ρ F.ρ)]₀ = [E]₀ + [F]₀ := by
  let P : FDRep L G := FDRep.of (Representation.prod E.ρ F.ρ)
  let fRep :
      ((forget₂ (FDRep L G) (Rep L G)).obj E ⟶ (forget₂ (FDRep L G) (Rep L G)).obj P) :=
    Rep.ofHom ⟨LinearMap.inl L E.V F.V, by
      -- The left inclusion intertwines the two actions because the product action is
      -- coordinatewise.
      intro g
      ext x
      change
        LinearMap.inl L E.V F.V (E.ρ g x) =
          ((E.ρ g).prodMap (F.ρ g)) (LinearMap.inl L E.V F.V x)
      simp [LinearMap.prodMap]⟩
  let gRep :
      ((forget₂ (FDRep L G) (Rep L G)).obj P ⟶ (forget₂ (FDRep L G) (Rep L G)).obj F) :=
    Rep.ofHom ⟨LinearMap.snd L E.V F.V, by
      -- The right projection is likewise equivariant for the coordinatewise product action.
      intro g
      ext x <;> rfl⟩
  let f : E ⟶ P := (FDRep.forget₂HomLinearEquiv E P) fRep
  let g : P ⟶ F := (FDRep.forget₂HomLinearEquiv P F) gRep
  let S : ShortComplex (FDRep L G) := ShortComplex.mk f g (by
    -- The composite vanishes already on the underlying representation maps.
    apply (forget₂ (FDRep L G) (Rep L G)).map_injective
    ext x <;> rfl)
  let SRep : ShortComplex (Rep L G) := ShortComplex.mk fRep gRep (by ext x <;> rfl)
  have hRepMap : ((SRep.map (forget₂ (Rep L G) (ModuleCat L))).ShortExact) := by
    let SMod : ShortComplex (ModuleCat L) :=
      CategoryTheory.ShortComplex.moduleCatMk
        (LinearMap.inl L E.V F.V)
        (LinearMap.snd L E.V F.V)
        (by ext x <;> rfl)
    have hSMod : SMod.ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · -- In `ModuleCat`, exactness is the concrete statement `range(inl) = ker(snd)`.
        exact CategoryTheory.ShortComplex.Exact.moduleCat_of_range_eq_ker
          (ModuleCat.ofHom (LinearMap.inl L E.V F.V))
          (ModuleCat.ofHom (LinearMap.snd L E.V F.V))
          (by
            ext x
            constructor
            · rintro ⟨y, rfl⟩
              simp
            · intro hx
              refine ⟨x.1, ?_⟩
              ext
              · rfl
              · simpa using hx.symm)
      · -- The left inclusion is injective.
        exact (ModuleCat.mono_iff_injective _).mpr fun x y h => by
          exact congrArg Prod.fst h
      · -- The right projection is surjective.
        exact (ModuleCat.epi_iff_surjective _).mpr fun z => ⟨(0, z), rfl⟩
    -- Forgetting from `Rep` to `ModuleCat` preserves and reflects short exactness.
    simpa [SRep, SMod, fRep, gRep] using hSMod
  have hRepShort : SRep.ShortExact := by
    -- Reflect the concrete module short exactness back to `Rep`.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := SRep) (F := forget₂ (Rep L G) (ModuleCat L))).1 hRepMap
  have hRep : ((S.map (forget₂ (FDRep L G) (Rep L G))).ShortExact) := by
    -- The explicit `Rep` short complex is definitionally the image of the `FDRep` short complex.
    simpa [S, SRep, f, g, fRep, gRep] using hRepShort
  have hS : S.ShortExact := by
    -- Forgetting from `FDRep` to `Rep` preserves and reflects short exactness as well.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := S) (F := forget₂ (FDRep L G) (Rep L G))).1 hRep
  -- Proposition `14-14.1-1` turns the verified split short exact sequence into the class relation.
  simpa [S, P] using finiteRepGrothendieckClass_middle_eq_left_add_right (L := L) (G := G) S hS

/-- Helper for Remark 14-14.1-2: for a module viewed through `Representation.ofModule'`, the
induced group-algebra action is the original `L[G]`-scalar multiplication. -/
private theorem ofModule'_asAlgebraHom_apply_local
    (M : Type u) [AddCommGroup M] [Module L M]
    [Module (MonoidAlgebra L G) M] [IsScalarTower L (MonoidAlgebra L G) M]
    (r : MonoidAlgebra L G) (m : M) :
    ((Representation.ofModule' (k := L) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and reduce to monomials.
  refine MonoidAlgebra.induction_on
    (p := fun s : MonoidAlgebra L G =>
      ((Representation.ofModule' (k := L) (G := G) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Remark 14-14.1-2: the owner module of `Representation.ofModule' M` is canonically
the original `L[G]`-module `M`. -/
private theorem nonempty_ofModule'_asModuleLinearEquiv_local
    (M : Type u) [AddCommGroup M] [Module L M] [Module (MonoidAlgebra L G) M]
    [IsScalarTower L (MonoidAlgebra L G) M] :
    Nonempty ((Representation.ofModule' (k := L) (G := G) M).asModule ≃ₗ[MonoidAlgebra L G] M) := by
  -- Use `asModuleEquiv` and then verify compatibility with the original `L[G]`-action.
  let toFun : (Representation.ofModule' (k := L) (G := G) M).asModule → M :=
    fun x => (Representation.ofModule' (k := L) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := L) (G := G) M).asModule :=
    fun x => (Representation.ofModule' (k := L) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : MonoidAlgebra L G) x, toFun (r • x) = r • toFun x := by
    intro r x
    -- Rewrite the transported action through `asModuleEquiv`, then identify it with the original
    -- `L[G]`-action on `M`.
    calc
      (Representation.ofModule' (k := L) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := L) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := L) (G := G) M).asModuleEquiv x) := by
                simpa using
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := L) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := L) (G := G) M).asModuleEquiv x := by
            simpa [toFun] using
              (ofModule'_asAlgebraHom_apply_local (L := L) (G := G) M r
                ((Representation.ofModule' (k := L) (G := G) M).asModuleEquiv x))
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

/-- Helper for Remark 14-14.1-2: a simple `L[G]`-module viewed through `Representation.ofModule'`
is irreducible. -/
private theorem ofModule'_isIrreducible_of_isSimpleModule_local
    (M : Type u) [AddCommGroup M] [Module L M] [Module (MonoidAlgebra L G) M]
    [IsScalarTower L (MonoidAlgebra L G) M] [IsSimpleModule (MonoidAlgebra L G) M] :
    (Representation.ofModule' (k := L) (G := G) M).IsIrreducible := by
  -- Transport simplicity across the canonical owner-module equivalence and then apply the
  -- irreducibility/simple-module bridge.
  rcases nonempty_ofModule'_asModuleLinearEquiv_local (L := L) (G := G) M with ⟨eM⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := L) (G := G) M)).2
      (@IsSimpleModule.congr (MonoidAlgebra L G) inferInstance
        ((Representation.ofModule' (k := L) (G := G) M).asModule)
        (Representation.ofModule' (k := L) (G := G) M).instAddCommGroupAsModule
        (Representation.ofModule' (k := L) (G := G) M).instModuleMonoidAlgebraAsModule
        M inferInstance inferInstance eM inferInstance)

/-- Helper for Remark 14-14.1-2: a subsingleton finite-dimensional `L[G]`-module defines the zero
Grothendieck class. -/
private theorem finiteRepGrothendieckClass_ofModule'_eq_zero_of_subsingleton_local
    (M : Type u) [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    [Module (MonoidAlgebra L G) M] [IsScalarTower L (MonoidAlgebra L G) M] [Subsingleton M] :
    [FDRep.of (Representation.ofModule' (k := L) (G := G) M)]₀ = 0 := by
  let Z : FDRep L G := FDRep.of (Representation.ofModule' (k := L) (G := G) M)
  -- A subsingleton owner has zero identity, so it is isomorphic to the zero object in `FDRep`.
  have hId : (𝟙 Z : Z ⟶ Z) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hZero : CategoryTheory.Limits.IsZero Z :=
    (CategoryTheory.Limits.IsZero.iff_id_eq_zero Z).2 hId
  simpa [Z] using
    (finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G)
      (V := Z) ⟨CategoryTheory.Limits.IsZero.isoZero hZero⟩)

/-- Helper for Remark 14-14.1-2: the Grothendieck class of a finite direct sum of owner modules is
the sum of the classes of its summands. -/
private theorem finiteRepGrothendieckClass_dfinsupp_eq_sum
    {n : ℕ} (S : Fin n → Type u)
    [∀ i, AddCommGroup (S i)] [∀ i, Module L (S i)] [∀ i, FiniteDimensional L (S i)]
    [∀ i, Module (MonoidAlgebra L G) (S i)]
    [∀ i, IsScalarTower L (MonoidAlgebra L G) (S i)] :
    [FDRep.of (Representation.ofModule' (k := L) (G := G) (Π₀ i : Fin n, S i))]₀ =
      ∑ i, [FDRep.of (Representation.ofModule' (k := L) (G := G) (S i))]₀ := by
  induction n with
  | zero =>
      -- The empty direct sum is a subsingleton owner, so its class is zero.
      simpa using
        (finiteRepGrothendieckClass_ofModule'_eq_zero_of_subsingleton_local
          (L := L) (G := G) (M := Π₀ i : Fin 0, S i))
  | succ n ih =>
      -- Split the `Fin (n + 1)`-indexed direct sum into its head and tail pieces.
      rcases nonempty_ofModule'_asModuleLinearEquiv_local
          (L := L) (G := G) (M := Π₀ i : Fin (n + 1), S i) with
        ⟨eSrc⟩
      rcases nonempty_ofModule'_asModuleLinearEquiv_local
          (L := L) (G := G) (M := S 0 × Π₀ i : Fin n, S i.succ) with
        ⟨eTgt⟩
      let eRaw :
          (Π₀ i : Fin (n + 1), S i) ≃ₗ[MonoidAlgebra L G]
            (S 0 × Π₀ i : Fin n, S i.succ) :=
        (DirectSum.lequivCongrLeft (MonoidAlgebra L G) (finSuccEquiv n)).trans
          (DirectSum.lequivProdDirectSum (R := MonoidAlgebra L G)
            (α := fun o : Option (Fin n) => S ((finSuccEquiv n).symm o)))
      let eSplit :
          (Representation.ofModule' (k := L) (G := G) (Π₀ i : Fin (n + 1), S i)).asModule
            ≃ₗ[MonoidAlgebra L G]
          (Representation.ofModule' (k := L) (G := G) (S 0 × Π₀ i : Fin n, S i.succ)).asModule :=
        eSrc.trans (eRaw.trans eTgt.symm)
      let eProd :
          (Representation.ofModule' (k := L) (G := G) (S 0 × Π₀ i : Fin n, S i.succ)).asModule
            ≃ₗ[MonoidAlgebra L G]
          ((Representation.prod
              (Representation.ofModule' (k := L) (G := G) (S 0))
              (Representation.ofModule' (k := L) (G := G) (Π₀ i : Fin n, S i.succ))).asModule) :=
        { toFun := fun x => x
          invFun := fun x => x
          left_inv := by
            intro x
            rfl
          right_inv := by
            intro x
            rfl
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro r x
            rfl }
      calc
        [FDRep.of (Representation.ofModule' (k := L) (G := G) (Π₀ i : Fin (n + 1), S i))]₀
            = [FDRep.of (Representation.ofModule' (k := L) (G := G)
                (S 0 × Π₀ i : Fin n, S i.succ))]₀ := by
                  exact finiteRepGrothendieckClass_eq_of_asModuleLinearEquiv
                    (L := L) (G := G) eSplit
        _ = [FDRep.of
              (Representation.prod
                (Representation.ofModule' (k := L) (G := G) (S 0))
                (Representation.ofModule' (k := L) (G := G) (Π₀ i : Fin n, S i.succ)))]₀ := by
              exact finiteRepGrothendieckClass_eq_of_asModuleLinearEquiv
                (L := L) (G := G) eProd
        _ = [FDRep.of (Representation.ofModule' (k := L) (G := G) (S 0))]₀ +
              [FDRep.of (Representation.ofModule' (k := L) (G := G)
                (Π₀ i : Fin n, S i.succ))]₀ := by
                  simpa using
                    (finiteRepGrothendieckClass_prod_eq_add (L := L) (G := G)
                      (FDRep.of (Representation.ofModule' (k := L) (G := G) (S 0)))
                      (FDRep.of (Representation.ofModule' (k := L) (G := G)
                        (Π₀ i : Fin n, S i.succ))))
        _ = [FDRep.of (Representation.ofModule' (k := L) (G := G) (S 0))]₀ +
              ∑ i, [FDRep.of
                (Representation.ofModule' (k := L) (G := G) ((fun i : Fin n => S i.succ) i))]₀ := by
                  rw [ih (fun i : Fin n => S i.succ)]
        _ = ∑ i, [FDRep.of (Representation.ofModule' (k := L) (G := G) (S i))]₀ := by
              simpa [Fin.sum_univ_succ]

/-- Helper for Remark 14-14.1-2: the owner module of a finite-dimensional representation is a
finite `L[G]`-module. -/
private instance fdRep_owner_module_finite_local (E : FDRep L G) :
    Module.Finite (MonoidAlgebra L G) (fdRepOwnerModule_local (L := L) (G := G) E) := by
  -- Restrict scalars to the ambient field and transport finite dimensionality back to `L[G]`.
  exact Module.Finite.of_restrictScalars_finite L (MonoidAlgebra L G)
    (fdRepOwnerModule_local (L := L) (G := G) E)

/-- Helper for Remark 14-14.1-2: the bundled `L[G]`-module attached to `E` is definitionally the
same owner module as `E.ρ.asModule`. -/
private noncomputable abbrev fdRep_asModule_linearEquiv_owner_local (E : FDRep L G) :
    fdRepAsModule_local (L := L) (G := G) E ≃ₗ[MonoidAlgebra L G]
      fdRepOwnerModule_local (L := L) (G := G) E :=
  LinearEquiv.refl (MonoidAlgebra L G) (fdRepAsModule_local (L := L) (G := G) E)

/-- Helper for Remark 14-14.1-2: the bundled `L[G]`-module attached to `E` inherits the ambient
`L`-module structure. -/
private instance fdRep_asModule_module_over_field_local (E : FDRep L G) :
    Module L (fdRepAsModule_local (L := L) (G := G) E) := by
  -- Reduce the bundled module object back to the owner-module abbreviation and reuse its
  -- restricted scalar action.
  simpa [fdRepAsModule_local, fdRepOwnerModule_local, fdRepOwnerRepresentation_local] using
    (fdRep_owner_module_module_over_field_local (L := L) (G := G) E)

/-- Helper for Remark 14-14.1-2: the bundled `L[G]`-module attached to `E` inherits the usual
scalar tower `L → L[G] → E`. -/
private instance fdRep_asModule_isScalarTower_local (E : FDRep L G) :
    IsScalarTower L (MonoidAlgebra L G) (fdRepAsModule_local (L := L) (G := G) E) := by
  -- The bundled carrier is definitionally the same owner module, so the scalar tower transports
  -- without further work.
  simpa [fdRepAsModule_local, fdRepOwnerModule_local, fdRepOwnerRepresentation_local] using
    (fdRep_owner_module_isScalarTower_local (L := L) (G := G) E)

/-- Helper for Remark 14-14.1-2: the bundled `L[G]`-module attached to `E` is still finite over
the base field `L`. -/
private theorem fdRep_asModule_finite_over_field_local (E : FDRep L G) :
    Module.Finite L (fdRepAsModule_local (L := L) (G := G) E) := by
  -- Transport the finite-dimensional `L`-vector-space structure from the owner-module view.
  simpa [fdRepAsModule_local, fdRepOwnerModule_local, fdRepOwnerRepresentation_local] using
    (fdRep_owner_module_finite_over_field_local (L := L) (G := G) E)

/-- Helper for Remark 14-14.1-2: semisimplicity of `E.ρ` can be read directly on the bundled
`L[G]`-module `fdRepAsModule_local E`. -/
private theorem fdRep_asModule_semisimple_local
    (E : FDRep L G) (hE : IsSemisimpleRepresentation E.ρ) :
    IsSemisimpleModule (MonoidAlgebra L G) (fdRepAsModule_local (L := L) (G := G) E) := by
  -- Move semisimplicity from `Representation.asModule` onto the bundled module object.
  simpa [fdRepAsModule_local, fdRepOwnerRepresentation_local] using
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule E.ρ).mp hE

/-- Helper for Remark 14-14.1-2: the bundled `L[G]`-module attached to a finite-dimensional
representation is finite over `L[G]`. -/
private theorem fdRep_asModule_finite_local (E : FDRep L G) :
    Module.Finite (MonoidAlgebra L G) (fdRepAsModule_local (L := L) (G := G) E) := by
  -- Reuse the finiteness statement already proved for the owner-module abbreviation.
  simpa [fdRepAsModule_local, fdRepOwnerModule_local, fdRepOwnerRepresentation_local] using
    (fdRep_owner_module_finite_local (L := L) (G := G) E)

/-- Helper for Remark 14-14.1-2: an isomorphism in `FDRep` yields an `L[G]`-linear equivalence of
the underlying owner modules. -/
private theorem nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso_local
    {τ σ : FDRep L G} (h : Nonempty (τ ≅ σ)) :
    Nonempty (fdRepOwnerModule_local (L := L) (G := G) τ ≃ₗ[MonoidAlgebra L G]
      fdRepOwnerModule_local (L := L) (G := G) σ) := by
  -- Apply the forgetful functor to `ModuleCat (L[G])` and read the resulting isomorphism as a
  -- linear equivalence.
  rcases h with ⟨e⟩
  exact ⟨(((forget₂ (FDRep L G) (Rep L G)) ⋙ Rep.toModuleMonoidAlgebra
    (k := L) (G := G)).mapIso e).toLinearEquiv⟩

/-- Helper for Remark 14-14.1-2: every simple summand of a semisimple representation is
`L[G]`-linearly equivalent to a member of a fixed complete irreducible family. -/
private theorem simple_summand_linearEquiv_complete_family_local
    {ι : Type (u + 1)} (π : ι → FDRep L G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {S : Type u} [AddCommGroup S] [Module L S] [FiniteDimensional L S]
    [Module (MonoidAlgebra L G) S] [IsScalarTower L (MonoidAlgebra L G) S]
    [IsSimpleModule (MonoidAlgebra L G) S] :
    ∃ i, Nonempty (S ≃ₗ[MonoidAlgebra L G] fdRepOwnerModule_local (L := L) (G := G) (π i)) := by
  -- Rebundle the simple module as a representation, identify it with a member of the complete
  -- family, and forget back to the owner-module equivalence.
  have hS_irreducible :
      (Representation.ofModule' (k := L) (G := G) S).IsIrreducible :=
    ofModule'_isIrreducible_of_isSimpleModule_local (L := L) (G := G) S
  rcases IsCompleteIrreducibleFamily.exists_iso_of_representation π hπ_complete
      (Representation.ofModule' (k := L) (G := G) S) hS_irreducible with
    ⟨i, hi⟩
  rcases nonempty_ofModule'_asModuleLinearEquiv_local (L := L) (G := G) S with ⟨eS⟩
  rcases nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso_local (L := L) (G := G) hi with
    ⟨eπ⟩
  exact ⟨i, ⟨eS.symm.trans eπ⟩⟩

/-- Helper for Remark 14-14.1-2: an `L[G]`-submodule of a finite-dimensional owner module remains
finite-dimensional over `L`. -/
private theorem finiteDimensional_of_groupAlgebra_submodule_local
    (M : Type u) [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    [Module (MonoidAlgebra L G) M] [IsScalarTower L (MonoidAlgebra L G) M]
    (N : Submodule (MonoidAlgebra L G) M) :
    FiniteDimensional L N := by
  -- Restrict scalars to view the subtype as an `L`-subspace of a finite-dimensional `L`-space.
  simpa using
    FiniteDimensional.of_injective (Submodule.restrictScalars L N).subtype
      (Submodule.injective_subtype (Submodule.restrictScalars L N))

/-- Helper for Remark 14-14.1-2: a finite family of simple summands is `L[G]`-linearly
equivalent, summandwise and hence on the direct sum, to members of a complete simple family. -/
private theorem complete_family_dfinsupp_linearEquiv_of_simple_summands_local
    {ι : Type (u + 1)} (π : ι → FDRep L G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {M : Type u} [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    [Module (MonoidAlgebra L G) M] [IsScalarTower L (MonoidAlgebra L G) M]
    {n : ℕ}
    (S : Fin n → Submodule (MonoidAlgebra L G) M)
    (hSsimple : ∀ i, IsSimpleModule (MonoidAlgebra L G) (S i)) :
    ∃ q : Fin n → ι,
      (∀ i, Nonempty (S i ≃ₗ[MonoidAlgebra L G]
        fdRepOwnerModule_local (L := L) (G := G) (π (q i)))) ∧
      Nonempty ((Π₀ i : Fin n, S i) ≃ₗ[MonoidAlgebra L G]
        Π₀ i : Fin n, fdRepOwnerModule_local (L := L) (G := G) (π (q i))) := by
  classical
  -- Choose a complete-family representative for each simple summand independently.
  have hchoose :
      ∀ i, ∃ j, Nonempty (S i ≃ₗ[MonoidAlgebra L G]
        fdRepOwnerModule_local (L := L) (G := G) (π j)) := by
    intro i
    let N' : Submodule L M := Submodule.restrictScalars L (S i)
    letI : FiniteDimensional L N' := by
      simpa [N'] using
        finiteDimensional_of_groupAlgebra_submodule_local (L := L) (G := G) M (S i)
    have hNsimple : IsSimpleModule (MonoidAlgebra L G) N' := by
      simpa [N'] using hSsimple i
    -- Each simple summand is itself a simple finite-dimensional representation.
    simpa [N'] using
      (simple_summand_linearEquiv_complete_family_local
        (L := L) (G := G) π hπ_pairwise hπ_complete (S := N'))
  choose q hq using hchoose
  -- Assemble the fiberwise equivalences into a direct-sum equivalence.
  refine ⟨q, hq, ?_⟩
  exact ⟨DFinsupp.mapRange.linearEquiv fun i ↦ (hq i).some⟩

/-- Helper for Remark 14-14.1-2: the Grothendieck class of a finite direct sum over any finite
index type is the sum of the classes of its summands. -/
private theorem finiteRepGrothendieckClass_dfinsupp_eq_sum_finite_local
    {κ : Type u} [Fintype κ] (S : κ → Type u)
    [∀ i, AddCommGroup (S i)] [∀ i, Module L (S i)] [∀ i, FiniteDimensional L (S i)]
    [∀ i, Module (MonoidAlgebra L G) (S i)]
    [∀ i, IsScalarTower L (MonoidAlgebra L G) (S i)] :
    [FDRep.of (Representation.ofModule' (k := L) (G := G) (Π₀ i : κ, S i))]₀ =
      ∑ i, [FDRep.of (Representation.ofModule' (k := L) (G := G) (S i))]₀ := by
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  rcases nonempty_ofModule'_asModuleLinearEquiv_local
      (L := L) (G := G) (M := Π₀ i : κ, S i) with
    ⟨eSrc⟩
  rcases nonempty_ofModule'_asModuleLinearEquiv_local
      (L := L) (G := G) (M := Π₀ i : Fin (Fintype.card κ), S (e.symm i)) with
    ⟨eTgt⟩
  let eReindex :
      (Π₀ i : κ, S i) ≃ₗ[MonoidAlgebra L G] (Π₀ i : Fin (Fintype.card κ), S (e.symm i)) :=
    DirectSum.lequivCongrLeft (MonoidAlgebra L G) e
  let eOfModule :
      (Representation.ofModule' (k := L) (G := G) (Π₀ i : κ, S i)).asModule
        ≃ₗ[MonoidAlgebra L G]
      (Representation.ofModule' (k := L) (G := G)
        (Π₀ i : Fin (Fintype.card κ), S (e.symm i))).asModule :=
    eSrc.trans (eReindex.trans eTgt.symm)
  calc
    [FDRep.of (Representation.ofModule' (k := L) (G := G) (Π₀ i : κ, S i))]₀
        = [FDRep.of (Representation.ofModule' (k := L) (G := G)
            (Π₀ i : Fin (Fintype.card κ), S (e.symm i)))]₀ := by
              exact finiteRepGrothendieckClass_eq_of_asModuleLinearEquiv
                (L := L) (G := G) eOfModule
    _ = ∑ i, [FDRep.of (Representation.ofModule' (k := L) (G := G) (S (e.symm i)))]₀ := by
          simpa using
            (finiteRepGrothendieckClass_dfinsupp_eq_sum (L := L) (G := G)
              (S := fun i : Fin (Fintype.card κ) => S (e.symm i)))
    _ = ∑ i, [FDRep.of (Representation.ofModule' (k := L) (G := G) (S i))]₀ := by
          simpa using
            (Equiv.sum_comp e.symm
              (fun i : κ => [FDRep.of (Representation.ofModule' (k := L) (G := G) (S i))]₀))

/-- Helper for Remark 14-14.1-2: the basis coordinates of a multiplicity-weighted sum of simple
classes recover the multiplicity function. -/
private theorem simple_family_basis_repr_eq_multiplicity_local
    {ι : Type (u + 1)} [Fintype ι] (π : ι → FDRep L G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ) (i : ι) :
    (simple_finiteRep_classes_basis_of_complete_family (L := L) (G := G)
      π hπ_pairwise hπ_complete).repr
        (∑ j, (m j : ℤ) • [π j]₀) i = m i := by
  classical
  let b := simple_finiteRep_classes_basis_of_complete_family (L := L) (G := G)
    π hπ_pairwise hπ_complete
  have hrepr :
      ∀ j, b.repr [π j]₀ = Finsupp.single j (1 : ℤ) := by
    intro j
    simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using b.repr_self j
  -- Expand the sum in basis coordinates and use that `b.repr` sends each basis vector to the
  -- corresponding singleton coordinate.
  calc
    b.repr (∑ j, (m j : ℤ) • [π j]₀) i
        = (∑ j, (m j : ℤ) • b.repr [π j]₀) i := by
            simp
    _ = (∑ j, (m j : ℤ) • (Finsupp.single j (1 : ℤ))) i := by
          simp [hrepr]
    _ = m i := by
          simp [Finsupp.single_apply, Finset.mem_univ]

/-- Helper for Remark 14-14.1-2: once each summand in a finite direct sum is identified with a
member of the chosen complete simple family, the class of the whole direct sum is the sum of the
corresponding simple classes. -/
private theorem complete_family_dfinsupp_class_eq_sum_local
    {ι : Type (u + 1)} (π : ι → FDRep L G)
    {n : ℕ} (q : Fin n → ι)
    (S : Fin n → Type u)
    [∀ a, AddCommGroup (S a)] [∀ a, Module L (S a)] [∀ a, FiniteDimensional L (S a)]
    [∀ a, Module (MonoidAlgebra L G) (S a)]
    [∀ a, IsScalarTower L (MonoidAlgebra L G) (S a)]
    (hq : ∀ a, Nonempty (S a ≃ₗ[MonoidAlgebra L G]
      fdRepOwnerModule_local (L := L) (G := G) (π (q a)))) :
    [FDRep.of (Representation.ofModule' (k := L) (G := G) (Π₀ a : Fin n, S a))]₀ =
      ∑ a, [π (q a)]₀ := by
  classical
  -- First rewrite the class of the direct sum as the sum of the classes of its summands.
  calc
    [FDRep.of (Representation.ofModule' (k := L) (G := G) (Π₀ a : Fin n, S a))]₀
        = ∑ a, [FDRep.of (Representation.ofModule' (k := L) (G := G) (S a))]₀ := by
            exact
              finiteRepGrothendieckClass_dfinsupp_eq_sum
                (L := L) (G := G) (S := S)
    _ = ∑ a, [π (q a)]₀ := by
          -- Replace each summand by its matching representative from the complete simple family.
          refine Finset.sum_congr rfl ?_
          intro a ha
          rcases nonempty_ofModule'_asModuleLinearEquiv_local
              (L := L) (G := G) (M := S a) with
            ⟨eOf⟩
          rcases hq a with ⟨eπ⟩
          have hclass :
              [FDRep.of (Representation.ofModule' (k := L) (G := G) (S a))]₀ =
                [FDRep.of (π (q a)).ρ]₀ :=
            finiteRepGrothendieckClass_eq_of_asModuleLinearEquiv
              (L := L) (G := G)
              (ρ := Representation.ofModule' (k := L) (G := G) (S a))
              (σ := (π (q a)).ρ)
              (eOf.trans eπ)
          simpa using hclass

/-- Helper for Remark 14-14.1-2: a semisimple finite-dimensional representation is a finite direct
sum of members of a fixed complete simple family. -/
private theorem semisimple_complete_family_decomposition_local
    {ι : Type (u + 1)} (π : ι → FDRep L G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (E : FDRep L G) (hE : IsSemisimpleRepresentation E.ρ) :
    ∃ (n : ℕ) (q : Fin n → ι),
      Nonempty (fdRepOwnerModule_local (L := L) (G := G) E ≃ₗ[MonoidAlgebra L G]
        Π₀ a : Fin n, fdRepOwnerModule_local (L := L) (G := G) (π (q a))) ∧
      [E]₀ = ∑ a, [π (q a)]₀ := by
  classical
  let M : ModuleCat (MonoidAlgebra L G) := fdRepAsModule_local (L := L) (G := G) E
  letI : Module L M := fdRep_asModule_module_over_field_local (L := L) (G := G) E
  letI : IsScalarTower L (MonoidAlgebra L G) M :=
    fdRep_asModule_isScalarTower_local (L := L) (G := G) E
  letI : Module.Finite L M := fdRep_asModule_finite_over_field_local (L := L) (G := G) E
  letI : IsSemisimpleModule (MonoidAlgebra L G) M :=
    fdRep_asModule_semisimple_local (L := L) (G := G) E hE
  letI : Module.Finite (MonoidAlgebra L G) M :=
    fdRep_asModule_finite_local (L := L) (G := G) E
  -- Route correction: decompose the semisimple representation on the bundled `ModuleCat`
  -- carrier, then compare each simple summand with the chosen complete irreducible family.
  obtain ⟨n, S, eS, hSsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (MonoidAlgebra L G) M
  obtain ⟨q, hq, hProd⟩ :=
    complete_family_dfinsupp_linearEquiv_of_simple_summands_local
      (L := L) (G := G) π hπ_pairwise hπ_complete (M := M) S hSsimple
  rcases hProd with ⟨eProd⟩
  refine ⟨n, q, ?_, ?_⟩
  · -- Convert the bundled-module equivalence back to the owner-module notation used elsewhere in
    -- this file.
    exact ⟨(fdRep_asModule_linearEquiv_owner_local (L := L) (G := G) E).symm.trans
      (eS.trans eProd)⟩
  · -- Re-register the scalar-tower data on the DFinsupp carrier so `ofModule'` sees the same
    -- restricted `L`-action as the direct-sum lemmas.
    letI : ∀ a : Fin n, Module L ↥(S a) := fun a ↦
      groupAlgebra_submodule_module_over_field_local (L := L) (G := G) (M := M) (S a)
    have hTowerSub : ∀ a : Fin n, IsScalarTower L (MonoidAlgebra L G) ↥(S a) := by
      intro a
      exact groupAlgebra_submodule_isScalarTower_local (L := L) (G := G) (M := M) (S a)
    letI : ∀ a : Fin n, IsScalarTower L (MonoidAlgebra L G) ↥(S a) := hTowerSub
    letI : ∀ a : Fin n, FiniteDimensional L ↥(S a) := fun a ↦
      finiteDimensional_of_groupAlgebra_submodule_local (L := L) (G := G) M (S a)
    letI : IsScalarTower L (MonoidAlgebra L G) (Π₀ a : Fin n, ↥(S a)) := by
      refine IsScalarTower.of_algebraMap_smul ?_
      intro t x
      ext a
      exact congrArg Subtype.val
        (@algebraMap_smul L _ (MonoidAlgebra L G) _ _ ↥(S a) _ _ _ (hTowerSub a) t
          (x a : ↥(S a)))
    letI : Module.Finite L (Π₀ a : Fin n, ↥(S a)) := by
      infer_instance
    have hq' :
        ∀ a, Nonempty (↥(S a) ≃ₗ[MonoidAlgebra L G]
          fdRepOwnerModule_local (L := L) (G := G) (π (q a))) := by
      intro a
      simpa using hq a
    rcases nonempty_ofModule'_asModuleLinearEquiv_local
        (L := L) (G := G) (M := Π₀ a : Fin n, ↥(S a)) with
      ⟨eOf⟩
    have hClassDecomp :
        [E]₀ = [FDRep.of (Representation.ofModule' (k := L) (G := G) (Π₀ a : Fin n, ↥(S a)))]₀ := by
      -- Identify `E` with the direct sum of its simple summands inside the Grothendieck group.
      exact
        finiteRepGrothendieckClass_eq_of_asModuleLinearEquiv
          (L := L) (G := G)
          (ρ := E.ρ)
          (σ := Representation.ofModule' (k := L) (G := G) (Π₀ a : Fin n, ↥(S a)))
          (((fdRep_asModule_linearEquiv_owner_local (L := L) (G := G) E).symm.trans eS).trans
            eOf.symm)
    -- Rewrite the class of the direct sum into the sum of the matched simple-family classes.
    calc
      [E]₀ = [FDRep.of (Representation.ofModule' (k := L) (G := G) (Π₀ a : Fin n, ↥(S a)))]₀ :=
        hClassDecomp
      _ = ∑ a, [π (q a)]₀ := by
        exact
          @complete_family_dfinsupp_class_eq_sum_local
            L G _ _ ι π n q (fun a ↦ ↥(S a))
            (fun a ↦ inferInstance)
            (fun a ↦
              groupAlgebra_submodule_module_over_field_local
                (L := L) (G := G) (M := M) (S a))
            (fun a ↦
              finiteDimensional_of_groupAlgebra_submodule_local
                (L := L) (G := G) M (S a))
            (fun a ↦ inferInstance)
            (fun a ↦
              groupAlgebra_submodule_isScalarTower_local
                (L := L) (G := G) (M := M) (S a))
            hq'

-- Proof sketch: choose a complete family of pairwise nonisomorphic simple representations from
-- Proposition `14-14.1-1`. In a semisimple representation, the coefficients of the Grothendieck
-- class in that basis are exactly the multiplicities of the simple summands. Equality of classes
-- therefore forces equality of multiplicities, and conversely an isomorphism identifies the two
-- classes in the Grothendieck group.
/-- Canonical owner form: two semisimple finite-dimensional `L`-representations of the monoid `G`
have the same class in `R₀[L](G)` if and only if they are isomorphic. -/
theorem finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple
    {E E' : FDRep L G}
    (hE : IsSemisimpleRepresentation E.ρ)
    (hE' : IsSemisimpleRepresentation E'.ρ) :
    [E]₀ = [E']₀ ↔ Nonempty (E ≅ E') := by
  classical
  constructor
  · intro hclass
    -- Route correction: the forward implication has been pivoted to the complete-family basis
    -- route. This file now has a local complete pairwise-nonisomorphic simple family, so the
    -- remaining work is to compare two finite simple decompositions by their basis coordinates,
    -- not to restart a cancellation induction on arbitrary summand lists.
    rcases exists_complete_pairwise_nonisomorphic_simple_family_local (L := L) (G := G) with
      ⟨ι, π, hπ_pairwise, hπ_complete⟩
    let b := simple_finiteRep_classes_basis_of_complete_family (L := L) (G := G)
      π hπ_pairwise hπ_complete
    rcases semisimple_complete_family_decomposition_local
        (L := L) (G := G) π hπ_pairwise hπ_complete E hE with
      ⟨n, q, hEqv, hEclass⟩
    rcases semisimple_complete_family_decomposition_local
        (L := L) (G := G) π hπ_pairwise hπ_complete E' hE' with
      ⟨n', q', hEqv', hE'class⟩
    let m : ι →₀ ℤ := ∑ a, Finsupp.single (q a) (1 : ℤ)
    let m' : ι →₀ ℤ := ∑ a, Finsupp.single (q' a) (1 : ℤ)
    have hreprπ : ∀ j, b.repr [π j]₀ = Finsupp.single j (1 : ℤ) := by
      intro j
      simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using b.repr_self j
    have hm_repr : b.repr [E]₀ = m := by
      ext i
      -- Read the class of `E` in the simple basis by summing the singleton coordinates of its
      -- finite simple decomposition.
      calc
        b.repr [E]₀ i = b.repr (∑ a, [π (q a)]₀) i := by rw [hEclass]
        _ = (∑ a, b.repr [π (q a)]₀) i := by simp
        _ = (∑ a, Finsupp.single (q a) (1 : ℤ)) i := by simp [hreprπ]
        _ = m i := by simp [m]
    have hm'_repr : b.repr [E']₀ = m' := by
      ext i
      calc
        b.repr [E']₀ i = b.repr (∑ a, [π (q' a)]₀) i := by rw [hE'class]
        _ = (∑ a, b.repr [π (q' a)]₀) i := by simp
        _ = (∑ a, Finsupp.single (q' a) (1 : ℤ)) i := by simp [hreprπ]
        _ = m' i := by simp [m']
    have hm : m = m' := by
      calc
        m = b.repr [E]₀ := hm_repr.symm
        _ = b.repr [E']₀ := congrArg b.repr hclass
        _ = m' := hm'_repr
    have hcardEq :
        ∀ i, Fintype.card { a : Fin n // q a = i } = Fintype.card { a : Fin n' // q' a = i } := by
      intro i
      have hmi : m i = m' i := by simpa using congrArg (fun f : ι →₀ ℤ => f i) hm
      have hleft : m i = (Fintype.card { a : Fin n // q a = i } : ℤ) := by
        rw [Fintype.card_subtype, Finset.card_filter]
        simp [m, Finsupp.single_apply, eq_comm]
      have hright : m' i = (Fintype.card { a : Fin n' // q' a = i } : ℤ) := by
        rw [Fintype.card_subtype, Finset.card_filter]
        simp [m', Finsupp.single_apply, eq_comm]
      apply Int.ofNat.inj
      calc
        (Fintype.card { a : Fin n // q a = i } : ℤ) = m i := hleft.symm
        _ = m' i := hmi
        _ = (Fintype.card { a : Fin n' // q' a = i } : ℤ) := hright
    let eFib : ∀ i, { a : Fin n // q a = i } ≃ { a : Fin n' // q' a = i } := fun i =>
      (Fintype.equivFin { a : Fin n // q a = i }).trans
        ((finCongr (hcardEq i)).trans (Fintype.equivFin { a : Fin n' // q' a = i }).symm)
    let eIdx : Fin n ≃ Fin n' := Equiv.ofFiberEquiv eFib
    have heIdx : ∀ a : Fin n', q (eIdx.symm a) = q' a := by
      intro a
      calc
        q (eIdx.symm a) = q' (eIdx (eIdx.symm a)) := (Equiv.ofFiberEquiv_map eFib (eIdx.symm a)).symm
        _ = q' a := by rw [eIdx.apply_symm_apply]
    let eIdxCongr :
        (Π₀ a : Fin n, fdRepOwnerModule_local (L := L) (G := G) (π (q a))) ≃ₗ[MonoidAlgebra L G]
          Π₀ a : Fin n', fdRepOwnerModule_local (L := L) (G := G) (π (q' a)) := by
      let eRaw :
          (Π₀ a : Fin n, fdRepOwnerModule_local (L := L) (G := G) (π (q a))) ≃ₗ[MonoidAlgebra L G]
            Π₀ a : Fin n', fdRepOwnerModule_local (L := L) (G := G) (π (q (eIdx.symm a))) :=
        DirectSum.lequivCongrLeft (MonoidAlgebra L G) eIdx
      let eCast :
          (Π₀ a : Fin n', fdRepOwnerModule_local (L := L) (G := G) (π (q (eIdx.symm a))))
            ≃ₗ[MonoidAlgebra L G]
          Π₀ a : Fin n', fdRepOwnerModule_local (L := L) (G := G) (π (q' a)) :=
        DFinsupp.mapRange.linearEquiv (R := MonoidAlgebra L G) fun a =>
          LinearEquiv.cast
            (R := MonoidAlgebra L G)
            (M := fun i : ι => fdRepOwnerModule_local (L := L) (G := G) (π i))
            (heIdx a)
      exact eRaw.trans eCast
    rcases hEqv with ⟨eE⟩
    rcases hEqv' with ⟨eE'⟩
    let eFinal :
        fdRepOwnerModule_local (L := L) (G := G) E ≃ₗ[MonoidAlgebra L G]
          fdRepOwnerModule_local (L := L) (G := G) E' :=
      eE.trans (eIdxCongr.trans eE'.symm)
    -- Transport the canonical owner-module equivalence back to an isomorphism in `FDRep`.
    rcases nonempty_equiv_of_asModuleLinearEquiv (L := L) (G := G)
        (ρ := E.ρ) (σ := E'.ρ) eFinal with
      ⟨eρ⟩
    exact ⟨Representation.Equiv.toFDRepIso eρ⟩
  · rintro ⟨e⟩
    -- An isomorphism identifies the two Grothendieck classes by Proposition 14-14.1-1.
    exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G) ⟨e⟩

end

section

variable {K : Type u} {G : Type u} [Field K] [CharZero K] [Group G] [Finite G]

/-- Remark 14-14.1-2: if two finite-dimensional `K`-representations of a finite group have the
same class in `R_K(G)`, then they are isomorphic; this uses semisimplicity, and the analogous
modular statement can fail when nonsemisimple modules exist. -/
-- Proof sketch: Maschke's theorem gives semisimplicity of every finite-dimensional
-- `K`-representation of the finite group `G` in characteristic zero. Apply the canonical owner
-- theorem `finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple`.
theorem finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_charZero
    {E E' : FDRep K G} :
    [E]₀ = [E']₀ ↔ Nonempty (E ≅ E') := by
  letI : NeZero (Nat.card G : K) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  have hE : IsSemisimpleRepresentation E.ρ := inferInstance
  have hE' : IsSemisimpleRepresentation E'.ρ := inferInstance
  exact finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple hE hE'

end

end GrothendieckGroup

end Representation
