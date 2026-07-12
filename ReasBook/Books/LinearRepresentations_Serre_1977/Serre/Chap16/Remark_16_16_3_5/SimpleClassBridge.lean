import LinearRepresentations_Serre_1977.Chap16.Remark_16_16_3_5.ReverseDirection

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped Pointwise Representation TensorProduct MonoidAlgebra ZeroObject

universe u

namespace Representation

/-- Helper for Remark 16-16.3-5: choose one representative for each simple finite-dimensional
representation over an arbitrary field. -/
theorem exists_complete_pairwise_nonisomorphic_simple_family_over_field
    {F : Type u} [Field F] {H : Type u} [Group H] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep F H),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  -- Index the family by isomorphism classes of simple finite representations.
  let SimpleRep : Type (u + 1) := { τ : FDRep F H // CategoryTheory.Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨CategoryTheory.Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep F H := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot contain isomorphic representatives.
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
    -- Every simple object is represented by its own quotient class.
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

/-- Helper for Remark 16-16.3-5: a finite-dimensional representation with subsingleton carrier
has zero Grothendieck class. -/
private theorem finiteRepGrothendieckClass_eq_zero_of_subsingleton_fdRep
    {L : Type u} [Field L] {G : Type u} [Group G] (T : FDRep L G) [Subsingleton T] :
    [T]₀ = 0 := by
  -- A subsingleton carrier makes the identity morphism zero, so the object is a zero object.
  let Z : FDRep L G := T
  have hId : (𝟙 Z : Z ⟶ Z) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hZero : IsZero Z := (IsZero.iff_id_eq_zero Z).2 hId
  simpa [Z] using
    (finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G)
      (V := Z) (W := 0) ⟨hZero.iso (isZero_zero (FDRep L G))⟩)

/-- Helper for Remark 16-16.3-5: for a module viewed through `Representation.ofModule'`,
the induced group-algebra action is the original scalar multiplication. -/
private theorem ofModule'_asAlgebraHom_apply
    {L : Type u} [Field L] {G : Type u} [Group G]
    (M : Type u) [AddCommGroup M] [Module L M] [Module L[G] M] [IsScalarTower L L[G] M]
    (r : L[G]) (m : M) :
    ((Representation.ofModule' (k := L) (G := G) M).asAlgebraHom r) m = r • m := by
  refine MonoidAlgebra.induction_on
    (p := fun s : L[G] =>
      ((Representation.ofModule' (k := L) (G := G) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Remark 16-16.3-5: the owner module of `Representation.ofModule' M` is
canonically the original `L[G]`-module. -/
private theorem nonempty_ofModule'_asModuleLinearEquiv
    {L : Type u} [Field L] {G : Type u} [Group G]
    (M : Type u) [AddCommGroup M] [Module L M] [Module L[G] M] [IsScalarTower L L[G] M] :
    Nonempty ((Representation.ofModule' (k := L) (G := G) M).asModule ≃ₗ[L[G]] M) := by
  let toFun : (Representation.ofModule' (k := L) (G := G) M).asModule → M :=
    fun x ↦ (Representation.ofModule' (k := L) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := L) (G := G) M).asModule :=
    fun x ↦ (Representation.ofModule' (k := L) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : L[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    calc
      (Representation.ofModule' (k := L) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := L) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := L) (G := G) M).asModuleEquiv x) := by
                simpa using
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := L) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := L) (G := G) M).asModuleEquiv x := by
            simpa [toFun] using
              (ofModule'_asAlgebraHom_apply (L := L) (G := G) M r
                ((Representation.ofModule' (k := L) (G := G) M).asModuleEquiv x))
  exact ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

/-- Helper for Remark 16-16.3-5: viewing the owner module `ρ.asModule` through
`Representation.ofModule'` recovers `ρ` up to equivalence. -/
private theorem nonempty_equiv_of_ofModule'_asModule
    {L : Type u} [Field L] {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) :
    Nonempty ((Representation.ofModule' (k := L) (G := G) ρ.asModule).Equiv ρ) := by
  refine ⟨Representation.Equiv.mk ?_ ?_⟩
  · exact ρ.asModuleEquiv
  · intro g
    ext x
    change ρ.asModuleEquiv ((MonoidAlgebra.of L G g) • x) = (ρ g) (ρ.asModuleEquiv x)
    convert (Representation.single_smul (ρ := ρ) (t := (1 : L)) g x) using 1
    simp

/-- Helper for Remark 16-16.3-5: a simple `L[G]`-module viewed through
`Representation.ofModule'` is irreducible. -/
private theorem ofModule'_isIrreducible_of_isSimpleModule
    {L : Type u} [Field L] {G : Type u} [Group G]
    (M : Type u) [AddCommGroup M] [Module L M] [Module L[G] M] [IsScalarTower L L[G] M]
    [IsSimpleModule L[G] M] :
    (Representation.ofModule' (k := L) (G := G) M).IsIrreducible := by
  rcases nonempty_ofModule'_asModuleLinearEquiv (L := L) (G := G) M with ⟨eM⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := L) (G := G) M)).2
      (@IsSimpleModule.congr (L[G]) inferInstance
        ((Representation.ofModule' (k := L) (G := G) M).asModule)
      (Representation.ofModule' (k := L) (G := G) M).instAddCommGroupAsModule
        (Representation.ofModule' (k := L) (G := G) M).instModuleMonoidAlgebraAsModule
        M inferInstance inferInstance eM inferInstance)

/-- Helper for Remark 16-16.3-5: a group-algebra submodule inherits the restricted
base-field module structure. -/
private instance groupAlgebraSubmoduleModuleBase
    {L : Type u} [Field L] {G : Type u} [Group G]
    {M : Type u} [AddCommGroup M] [Module L M] [Module L[G] M]
    [IsScalarTower L L[G] M]
    (N : Submodule L[G] M) : Module L N :=
  Module.compHom N (algebraMap L L[G])

/-- Helper for Remark 16-16.3-5: an `L[G]`-submodule of a finite-dimensional module remains
finite-dimensional over `L`. -/
private theorem finiteDimensional_of_groupAlgebra_submodule
    {L : Type u} [Field L] {G : Type u} [Group G]
    (M : Type u) [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    [Module L[G] M] [IsScalarTower L L[G] M]
    (N : Submodule L[G] M) :
    FiniteDimensional L N := by
  let f : N →ₗ[L] M :=
    { toFun := fun x ↦ (x : M)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        exact IsScalarTower.algebraMap_smul (L[G]) a (x : M) }
  exact FiniteDimensional.of_injective f (by
    intro x y hxy
    exact Subtype.ext hxy)

/-- Helper for Remark 16-16.3-5: the quotient by an `L[G]`-submodule of a finite-dimensional
module remains finite-dimensional over `L`. -/
private theorem finiteDimensional_of_groupAlgebra_quotient
    {L : Type u} [Field L] {G : Type u} [Group G]
    (M : Type u) [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    [Module L[G] M] [IsScalarTower L L[G] M]
    (N : Submodule L[G] M) :
    FiniteDimensional L (M ⧸ N) := by
  infer_instance

/-- Helper for Remark 16-16.3-5: the owner module of a finite representation is finite over the
base field. -/
private theorem moduleFinite_asModule
    {L : Type u} [Field L] {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module L V] [Module.Finite L V]
    (ρ : Representation L G V) :
    @Module.Finite L ρ.asModule _ (Representation.instAddCommMonoidAsModule ρ)
      (Representation.instModuleAsModule ρ) := by
  change Module.Finite L V
  infer_instance

/-- Helper for Remark 16-16.3-5: the owner module of a finite representation is
finite-dimensional over the base field. -/
private theorem finiteDimensional_asModule
    {L : Type u} [Field L] {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module L V] [Module.Finite L V]
    (ρ : Representation L G V) :
    @FiniteDimensional L ρ.asModule _ (Representation.instAddCommGroupAsModule ρ)
      (Representation.instModuleAsModule ρ) := by
  change FiniteDimensional L V
  infer_instance

/-- Helper for Remark 16-16.3-5: in `R₀[L](G)`, the class of a module viewed through
`Representation.ofModule'` splits as the sum of the classes of a submodule and the quotient. -/
private theorem finiteRepGrothendieckClass_ofModule'_eq_submodule_add_quotient
    {L : Type u} [Field L] {G : Type u} [Group G]
    (M : Type u) [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    [Module L[G] M] [IsScalarTower L L[G] M]
    (N : Submodule L[G] M)
    [FiniteDimensional L (M ⧸ N)] :
    ∃ XN : FDRep L G,
      [FDRep.of (Representation.ofModule' (k := L) (G := G) M)]₀ =
        [XN]₀ + [FDRep.of (Representation.ofModule' (k := L) (G := G) (M ⧸ N))]₀ ∧
      (Subsingleton XN → Subsingleton N) := by
  let instLN : Module L N := groupAlgebraSubmoduleModuleBase (L := L) (G := G) (M := M) N
  let instLGN : Module L[G] N := inferInstance
  letI : Module L N := instLN
  let fLinear : N →ₗ[L] M :=
    { toFun := fun x ↦ (x : M)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        exact IsScalarTower.algebraMap_smul (L[G]) a (x : M) }
  have hfLinear : Function.Injective fLinear := by
    intro x y hxy
    exact Subtype.ext hxy
  let instFiniteN : Module.Finite L N := FiniteDimensional.of_injective fLinear hfLinear
  have hTowerN : @IsScalarTower L L[G] N inferInstance instLGN.toSMul instLN.toSMul :=
    @IsScalarTower.of_algebraMap_smul L L[G] N inferInstance inferInstance inferInstance
      instLGN.toMulAction instLN.toSMul
      (fun _ _ ↦ by
        ext
        rfl)
  let ρN : Representation L G N :=
    @Representation.ofModule' L G inferInstance inferInstance N inferInstance instLN instLGN
      hTowerN
  let X₁ : FDRep L G := @FDRep.of L G inferInstance inferInstance N inferInstance instLN
    instFiniteN ρN
  let X₂ : FDRep L G := FDRep.of (Representation.ofModule' (k := L) (G := G) M)
  let X₃ : FDRep L G := FDRep.of (Representation.ofModule' (k := L) (G := G) (M ⧸ N))
  let fRep :
      ((forget₂ (FDRep L G) (Rep L G)).obj X₁ ⟶
        (forget₂ (FDRep L G) (Rep L G)).obj X₂) :=
    Rep.ofHom ⟨fLinear, fun g ↦ by
      ext x
      rfl⟩
  let gRep :
      ((forget₂ (FDRep L G) (Rep L G)).obj X₂ ⟶
        (forget₂ (FDRep L G) (Rep L G)).obj X₃) :=
    Rep.ofHom ⟨N.mkQ.restrictScalars L, fun g ↦ by
      ext x
      rfl⟩
  let f : X₁ ⟶ X₂ := (FDRep.forget₂HomLinearEquiv X₁ X₂) fRep
  let g : X₂ ⟶ X₃ := (FDRep.forget₂HomLinearEquiv X₂ X₃) gRep
  have hf : (forget₂ (FDRep L G) (Rep L G)).map f = fRep := by
    change (FDRep.forget₂HomLinearEquiv X₁ X₂).symm
        ((FDRep.forget₂HomLinearEquiv X₁ X₂) fRep) = fRep
    exact (FDRep.forget₂HomLinearEquiv X₁ X₂).left_inv fRep
  have hg : (forget₂ (FDRep L G) (Rep L G)).map g = gRep := by
    change (FDRep.forget₂HomLinearEquiv X₂ X₃).symm
        ((FDRep.forget₂HomLinearEquiv X₂ X₃) gRep) = gRep
    exact (FDRep.forget₂HomLinearEquiv X₂ X₃).left_inv gRep
  let S : ShortComplex (FDRep L G) := ShortComplex.mk f g (by
    apply (forget₂ (FDRep L G) (Rep L G)).map_injective
    rw [Functor.map_comp, hf, hg]
    ext x
    change N.mkQ (N.subtype x) = 0
    simp)
  let SRep : ShortComplex (Rep L G) := ShortComplex.mk fRep gRep (by
    ext x
    change N.mkQ (N.subtype x) = 0
    simp)
  have hMod : (SRep.map (forget₂ (Rep L G) (ModuleCat L))).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change N.mkQ x = 0 at hx
      simpa using hx
    · rw [ModuleCat.mono_iff_injective]
      intro x y hxy
      exact Subtype.ext hxy
    · rw [ModuleCat.epi_iff_surjective]
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N x
      exact ⟨y, rfl⟩
  have hRep' : SRep.ShortExact := by
    apply (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SRep) (F := forget₂ (Rep L G) (ModuleCat L))).1
    simpa using hMod
  have hRep : (S.map (forget₂ (FDRep L G) (Rep L G))).ShortExact := by
    simpa [S, SRep, hf, hg] using hRep'
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        ((S.exact_map_iff_of_faithful (forget₂ (FDRep L G) (Rep L G))).1 hRep.exact)
    · exact (forget₂ (FDRep L G) (Rep L G)).mono_of_mono_map hRep.mono_f
    · exact (forget₂ (FDRep L G) (Rep L G)).epi_of_epi_map hRep.epi_g
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := L) (G := G) S hS
  refine ⟨X₁, ?_, ?_⟩
  · simpa [S, X₁, X₂, X₃] using hrelation
  · intro hX₁
    simpa [X₁, ρN] using hX₁

/-- Helper for Remark 16-16.3-5: rebuild an `FDRep` from the canonical owner module of its
underlying representation, with the finite-module instance supplied explicitly. -/
private abbrev fdRepOfAsModule
    {L : Type u} [Field L] {G : Type u} [Group G] (T : FDRep L G) : FDRep L G :=
  let ρT : Representation L G T := T.ρ
  @FDRep.of L G inferInstance inferInstance ρT.asModule
    (Representation.instAddCommGroupAsModule ρT)
    (Representation.instModuleAsModule ρT)
    (moduleFinite_asModule ρT)
    (@Representation.ofModule' L G inferInstance inferInstance ρT.asModule
      inferInstance inferInstance inferInstance inferInstance)

/-- Helper for Remark 16-16.3-5: the class of an `FDRep` is unchanged after rebuilding it from
the canonical owner `L[G]`-module attached to its representation. -/
private theorem finiteRepGrothendieckClass_ofModule_asModule_eq_fdRep
    {L : Type u} [Field L] {G : Type u} [Group G] (T : FDRep L G) :
    [fdRepOfAsModule (L := L) (G := G) T]₀ = [T]₀ := by
  -- Compare the rebuilt owner module with `T.ρ`, then compare `FDRep.of T.ρ` with `T`.
  let ρT : Representation L G T := T.ρ
  obtain ⟨eρ⟩ := nonempty_equiv_of_ofModule'_asModule (L := L) (G := G) ρT
  let eT := fdRepIsoOfRho (K := L) (G := G) T
  have hrebuilt : fdRepOfAsModule (L := L) (G := G) T ≅ FDRep.of ρT := by
    exact @Representation.Equiv.toFDRepIso L inferInstance G inferInstance
      ρT.asModule (Representation.instAddCommGroupAsModule ρT)
      (Representation.instModuleAsModule ρT) (moduleFinite_asModule ρT)
      T inferInstance inferInstance inferInstance
      (Representation.ofModule' (k := L) (G := G) ρT.asModule) ρT eρ
  have hclass : [fdRepOfAsModule (L := L) (G := G) T]₀ = [T]₀ := by
    exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G)
      ⟨hrebuilt.trans eT.symm⟩
  simpa [ρT] using hclass

/-- Helper for Remark 16-16.3-5: a simple finite representation has nontrivial carrier. -/
private theorem not_subsingleton_of_simple_fdRep
    {L : Type u} [Field L] {G : Type u} [Group G] (S : FDRep L G) (hS : Simple S) :
    ¬ Subsingleton S := by
  -- Translate categorical simplicity to simple-module irreducibility, where nontriviality is API.
  intro hsub
  letI : Simple S := hS
  let ρS : Representation L G S := S.ρ
  have hIrr : ρS.IsIrreducible := by
    simpa [ρS] using FDRep.isIrreducible_of_simple S
  letI := Representation.instAddCommGroupAsModule ρS
  letI := Representation.instModuleMonoidAlgebraAsModule ρS
  have hsimpleModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρS).1 hIrr
  have hnontrivial : Nontrivial ρS.asModule :=
    @IsSimpleModule.nontrivial L[G] inferInstance ρS.asModule
      (Representation.instAddCommGroupAsModule ρS)
      (Representation.instModuleMonoidAlgebraAsModule ρS) hsimpleModule
  have hsub' : Subsingleton ρS.asModule := by
    simpa [ρS, Representation.asModule] using hsub
  exact (not_subsingleton_iff_nontrivial.2 hnontrivial) hsub'

/-- Helper for Remark 16-16.3-5: a nonzero finite `L[G]`-module has a strictly positive
coordinate in any complete simple-class basis. -/
private theorem ofModule_class_repr_pos_of_not_subsingleton
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    {ι : Type*}
    (π : ι → FDRep L G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (M : Type u) [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    [Module L[G] M] [IsScalarTower L L[G] M]
    (hM : ¬ Subsingleton M) :
    ∃ i, 0 <
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete).repr
        [FDRep.of (Representation.ofModule' (k := L) (G := G) M)]₀ i := by
  classical
  let b : Module.Basis ι ℤ (R₀[L](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hlength : IsFiniteLength L[G] M :=
    (isFiniteLength_iff_isNoetherian_isArtinian).2
      ⟨isNoetherian_of_tower L inferInstance, isArtinian_of_tower L inferInstance⟩
  cases hlength with
  | of_subsingleton =>
      exact (hM inferInstance).elim
  | @of_simple_quotient M _ _ N _ _ =>
      letI : FiniteDimensional L (M ⧸ N) :=
        finiteDimensional_of_groupAlgebra_quotient (L := L) (G := G) M N
      let ρQ : Representation L G (M ⧸ N) :=
        Representation.ofModule' (k := L) (G := G) (M ⧸ N)
      obtain ⟨XN, hsplit, _⟩ :=
        finiteRepGrothendieckClass_ofModule'_eq_submodule_add_quotient
          (L := L) (G := G) M N
      have hquot_irr : ρQ.IsIrreducible :=
        ofModule'_isIrreducible_of_isSimpleModule (L := L) (G := G) (M := M ⧸ N)
      obtain ⟨i, hi⟩ :=
        IsCompleteIrreducibleFamily.exists_iso_of_representation
          (π := π) hπ_complete (τ := ρQ) hquot_irr
      refine ⟨i, ?_⟩
      have hcoord :
          b.repr [FDRep.of (Representation.ofModule' (k := L) (G := G) M)]₀ i =
            b.repr [XN]₀ i + b.repr [FDRep.of ρQ]₀ i := by
        simpa [b] using congrArg (fun x : R₀[L](G) ↦ b.repr x i) hsplit
      have hN_nonneg : 0 ≤ b.repr [XN]₀ i := by
        simpa [b] using
          simple_finiteRep_classes_basis_repr_class_nonneg
            (L := L) (G := G) π hπ_pairwise hπ_complete XN i
      have hQ_coord : b.repr [FDRep.of ρQ]₀ i = 1 := by
        have hclassQ : [FDRep.of ρQ]₀ = [π i]₀ :=
          finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G) hi
        have hbself : b.repr [π i]₀ = Finsupp.single i (1 : ℤ) := by
          simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
            b.repr_self i
        calc
          b.repr [FDRep.of ρQ]₀ i = b.repr [π i]₀ i := by rw [hclassQ]
          _ = 1 := by
            simpa using congrArg (fun f : ι →₀ ℤ ↦ f i) hbself
      have hpos :
          0 < b.repr [FDRep.of (Representation.ofModule' (k := L) (G := G) M)]₀ i := by
        omega
      simpa [b] using hpos

/-- Helper for Remark 16-16.3-5: a nonzero finite representation has a strictly positive
coordinate in any complete simple-class basis. -/
private theorem finiteRepClass_repr_pos_of_not_subsingleton
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    {ι : Type*}
    (π : ι → FDRep L G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (T : FDRep L G) (hT : ¬ Subsingleton T) :
    ∃ i, 0 <
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete).repr [T]₀ i := by
  -- Apply the module-level positive-coordinate lemma to the canonical owner module of `T`.
  let ρT : Representation L G T := T.ρ
  letI := Representation.instAddCommGroupAsModule ρT
  letI := Representation.instModuleAsModule ρT
  letI := Representation.instModuleMonoidAlgebraAsModule ρT
  letI :=
    Representation.instIsScalarTowerMonoidAlgebraAsModule ρT
  have hmodule : ¬ Subsingleton ρT.asModule := by
    intro hsub
    apply hT
    simpa [ρT, Representation.asModule] using hsub
  rcases
      @ofModule_class_repr_pos_of_not_subsingleton
        L inferInstance G inferInstance inferInstance ι
        π hπ_pairwise hπ_complete ρT.asModule
        (Representation.instAddCommGroupAsModule ρT)
        (Representation.instModuleAsModule ρT)
        (finiteDimensional_asModule ρT)
        (Representation.instModuleMonoidAlgebraAsModule ρT)
        (Representation.instIsScalarTowerMonoidAlgebraAsModule ρT)
        hmodule with
    ⟨i, hi⟩
  refine ⟨i, ?_⟩
  have hi' :
      0 <
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete).repr
          [fdRepOfAsModule (L := L) (G := G) T]₀ i := by
    simpa [fdRepOfAsModule, ρT] using hi
  have hmodel : [fdRepOfAsModule (L := L) (G := G) T]₀ = [T]₀ :=
      finiteRepGrothendieckClass_ofModule_asModule_eq_fdRep (L := L) (G := G) T
  rwa [hmodel] at hi'

/-- Helper for Remark 16-16.3-5: equality of two simple finite-representation classes is induced
by an isomorphism. -/
private theorem simpleClass_eq_simpleClass_nonemptyIso
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    (T S : FDRep L G) [Simple T] [Simple S] (hclass : [T]₀ = [S]₀) :
    Nonempty (T ≅ S) := by
  classical
  -- Separate simple classes in a complete simple-class basis.
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field
      (F := L) (H := G)
  let b : Module.Basis ι ℤ (R₀[L](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let ρT : Representation L G T := T.ρ
  let ρS : Representation L G S := S.ρ
  have hTirr : ρT.IsIrreducible := by
    simpa [ρT] using FDRep.isIrreducible_of_simple T
  have hSirr : ρS.IsIrreducible := by
    simpa [ρS] using FDRep.isIrreducible_of_simple S
  obtain ⟨iT, hiT⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := π) hπ_complete (τ := ρT) hTirr
  obtain ⟨iS, hiS⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := π) hπ_complete (τ := ρS) hSirr
  let eT₀ := fdRepIsoOfRho (K := L) (G := G) T
  let eS₀ := fdRepIsoOfRho (K := L) (G := G) S
  rcases hiT with ⟨eTπ⟩
  rcases hiS with ⟨eSπ⟩
  let eT : T ≅ π iT := eT₀.trans eTπ
  let eS : S ≅ π iS := eS₀.trans eSπ
  have hπclass : [π iT]₀ = [π iS]₀ := by
    calc
      [π iT]₀ = [T]₀ :=
        (finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G) ⟨eT⟩).symm
      _ = [S]₀ := hclass
      _ = [π iS]₀ :=
        finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G) ⟨eS⟩
  have hidx : iT = iS := by
    by_contra hne
    have hcoord := congrArg (fun x : R₀[L](G) ↦ b.repr x iT) hπclass
    have hleft : b.repr [π iT]₀ iT = 1 := by
      have hbself : b.repr [π iT]₀ = Finsupp.single iT (1 : ℤ) := by
        simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
          b.repr_self iT
      simpa using congrArg (fun f : ι →₀ ℤ ↦ f iT) hbself
    have hright : b.repr [π iS]₀ iT = 0 := by
      have hbself : b.repr [π iS]₀ = Finsupp.single iS (1 : ℤ) := by
        simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
          b.repr_self iS
      calc
        b.repr [π iS]₀ iT = (Finsupp.single iS (1 : ℤ)) iT :=
          congrArg (fun f : ι →₀ ℤ ↦ f iT) hbself
        _ = 0 := Finsupp.single_eq_of_ne hne
    have hbad : (1 : ℤ) = 0 := by
      simpa [hleft, hright] using hcoord
    omega
  subst iS
  exact ⟨eT.trans eS.symm⟩

/-- Helper for Remark 16-16.3-5: a sum of two actual classes cannot equal one simple class unless
one summand is carried by a zero object. -/
private theorem finiteRepClass_add_eq_simpleClass_forces_subsingleton
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    (N Q S : FDRep L G) (hS : Simple S)
    (h : [N]₀ + [Q]₀ = ([S]₀ : R₀[L](G))) :
    Subsingleton N ∨ Subsingleton Q := by
  classical
  -- If both summands are nonzero, their positive basis coordinates contradict the single
  -- coordinate vector of a simple class.
  by_contra hnone
  have hNnot : ¬ Subsingleton N := fun hN ↦ hnone (Or.inl hN)
  have hQnot : ¬ Subsingleton Q := fun hQ ↦ hnone (Or.inr hQ)
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field
      (F := L) (H := G)
  let b : Module.Basis ι ℤ (R₀[L](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  letI : Simple S := hS
  let ρS : Representation L G S := S.ρ
  have hSirr : ρS.IsIrreducible := by
    simpa [ρS] using FDRep.isIrreducible_of_simple S
  obtain ⟨iS, hiS⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := π) hπ_complete (τ := ρS) hSirr
  let eS₀ := fdRepIsoOfRho (K := L) (G := G) S
  rcases hiS with ⟨eSπ⟩
  let eS : S ≅ π iS := eS₀.trans eSπ
  have hScoord : ∀ j, b.repr [S]₀ j = if iS = j then 1 else 0 := by
    intro j
    have hclassS : [S]₀ = [π iS]₀ :=
      finiteRepGrothendieckClass_eq_of_nonempty_iso (L := L) (G := G) ⟨eS⟩
    have hbself : b.repr [π iS]₀ = Finsupp.single iS (1 : ℤ) := by
      simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
        b.repr_self iS
    calc
      b.repr [S]₀ j = b.repr [π iS]₀ j := by rw [hclassS]
      _ = if iS = j then 1 else 0 := by
        simpa [Finsupp.single_apply] using congrArg (fun f : ι →₀ ℤ ↦ f j) hbself
  have hcoord : ∀ j, b.repr [N]₀ j + b.repr [Q]₀ j = b.repr [S]₀ j := by
    intro j
    simpa [b] using congrArg (fun x : R₀[L](G) ↦ b.repr x j) h
  have hNnonneg : ∀ j, 0 ≤ b.repr [N]₀ j := by
    intro j
    simpa [b] using
      simple_finiteRep_classes_basis_repr_class_nonneg
        (L := L) (G := G) π hπ_pairwise hπ_complete N j
  have hQnonneg : ∀ j, 0 ≤ b.repr [Q]₀ j := by
    intro j
    simpa [b] using
      simple_finiteRep_classes_basis_repr_class_nonneg
        (L := L) (G := G) π hπ_pairwise hπ_complete Q j
  obtain ⟨iN, hNpos⟩ :=
    finiteRepClass_repr_pos_of_not_subsingleton
      (L := L) (G := G) π hπ_pairwise hπ_complete N hNnot
  obtain ⟨iQ, hQpos⟩ :=
    finiteRepClass_repr_pos_of_not_subsingleton
      (L := L) (G := G) π hπ_pairwise hπ_complete Q hQnot
  by_cases hNi : iN = iS
  · by_cases hQi : iQ = iS
    · have hsum := hcoord iS
      have hs : b.repr [S]₀ iS = 1 := by
        simpa using hScoord iS
      have hNpos' : 0 < b.repr [N]₀ iS := by
        simpa [b, hNi] using hNpos
      have hQpos' : 0 < b.repr [Q]₀ iS := by
        simpa [b, hQi] using hQpos
      have hsum' : b.repr [N]₀ iS + b.repr [Q]₀ iS = 1 := by
        simpa [hs] using hsum
      omega
    · have hsum := hcoord iQ
      have hSzero : b.repr [S]₀ iQ = 0 := by
        have hSiQ : iS ≠ iQ := fun h' ↦ hQi h'.symm
        simpa [hSiQ] using hScoord iQ
      have hNnonneg' := hNnonneg iQ
      have hQpos' : 0 < b.repr [Q]₀ iQ := by
        simpa [b] using hQpos
      have hsum' : b.repr [N]₀ iQ + b.repr [Q]₀ iQ = 0 := by
        simpa [hSzero] using hsum
      omega
  · have hsum := hcoord iN
    have hSzero : b.repr [S]₀ iN = 0 := by
      have hSiN : iS ≠ iN := fun h' ↦ hNi h'.symm
      simpa [hSiN] using hScoord iN
    have hQnonneg' := hQnonneg iN
    have hNpos' : 0 < b.repr [N]₀ iN := by
      simpa [b] using hNpos
    have hsum' : b.repr [N]₀ iN + b.repr [Q]₀ iN = 0 := by
      simpa [hSzero] using hsum
    omega

/-- Helper for Remark 16-16.3-5: a class equal to a simple finite-representation class is
represented by a nonzero object. -/
private theorem not_subsingleton_of_finiteRepClass_eq_simple
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    (T S : FDRep L G) (hS : Simple S) (hclass : [T]₀ = [S]₀) :
    ¬ Subsingleton T := by
  -- A zero carrier would force the simple class to have all zero basis coordinates.
  intro hT
  letI : Subsingleton T := hT
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field
      (F := L) (H := G)
  let b : Module.Basis ι ℤ (R₀[L](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  obtain ⟨i, hi⟩ :=
    finiteRepClass_repr_pos_of_not_subsingleton
      (L := L) (G := G) π hπ_pairwise hπ_complete S
      (not_subsingleton_of_simple_fdRep (L := L) (G := G) S hS)
  have hSzero : [S]₀ = (0 : R₀[L](G)) := by
    calc
      [S]₀ = [T]₀ := hclass.symm
      _ = 0 := finiteRepGrothendieckClass_eq_zero_of_subsingleton_fdRep
        (L := L) (G := G) T
  have hcoordZero := congrArg (fun x : R₀[L](G) ↦ b.repr x i) hSzero
  simp at hcoordZero
  have hi' : 0 < b.repr [S]₀ i := by
    simpa [b] using hi
  omega

/-- Helper for Remark 16-16.3-5: a finite module whose class is a simple class is itself simple
as an `L[G]`-module. -/
private theorem ofModule_isSimpleModule_of_finiteRepClass_eq_simple
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    (M : Type u) [AddCommGroup M] [Module L M] [FiniteDimensional L M]
    [Module L[G] M] [IsScalarTower L L[G] M]
    (S : FDRep L G) (hS : Simple S)
    (hM : ¬ Subsingleton M)
    (hclass :
      [FDRep.of (Representation.ofModule' (k := L) (G := G) M)]₀ = ([S]₀ : R₀[L](G))) :
    IsSimpleModule L[G] M := by
  -- Split the finite-length module; a nonzero kernel and simple quotient would split one simple
  -- Grothendieck class into two nonzero actual classes.
  have hlength : IsFiniteLength L[G] M :=
    (isFiniteLength_iff_isNoetherian_isArtinian).2
      ⟨isNoetherian_of_tower L inferInstance, isArtinian_of_tower L inferInstance⟩
  cases hlength with
  | of_subsingleton =>
      exact (hM inferInstance).elim
  | @of_simple_quotient M _ _ N _ _ =>
      by_cases hNsub : Subsingleton N
      · letI : Subsingleton N := hNsub
        have hNbot : N = ⊥ := Submodule.eq_bot_of_subsingleton
        let eQ : (M ⧸ N) ≃ₗ[L[G]] M := Submodule.quotEquivOfEqBot N hNbot
        exact (LinearEquiv.isSimpleModule_iff eQ).1
          (inferInstance : IsSimpleModule L[G] (M ⧸ N))
      · letI : Module L N := inferInstance
        letI : FiniteDimensional L (M ⧸ N) :=
          finiteDimensional_of_groupAlgebra_quotient (L := L) (G := G) M N
        let ρQ : Representation L G (M ⧸ N) :=
          Representation.ofModule' (k := L) (G := G) (M ⧸ N)
        let XQ : FDRep L G := FDRep.of ρQ
        obtain ⟨XN, hsplit, hXN_subsingleton⟩ :=
          finiteRepGrothendieckClass_ofModule'_eq_submodule_add_quotient
            (L := L) (G := G) M N
        have hsplit' :
            [FDRep.of (Representation.ofModule' (k := L) (G := G) M)]₀ =
            [XN]₀ + [XQ]₀ := by
          simpa [XQ, ρQ] using hsplit
        have hsum : [XN]₀ + [XQ]₀ = ([S]₀ : R₀[L](G)) := by
          calc
            [XN]₀ + [XQ]₀ =
                [FDRep.of (Representation.ofModule' (k := L) (G := G) M)]₀ := hsplit'.symm
            _ = [S]₀ := hclass
        rcases finiteRepClass_add_eq_simpleClass_forces_subsingleton
            (L := L) (G := G) XN XQ S hS hsum with
          hXN | hXQ
        · have hNsub' : Subsingleton N := hXN_subsingleton hXN
          exact (hNsub hNsub').elim
        · have hQsub : Subsingleton (M ⧸ N) := by
            simpa [XQ, ρQ] using hXQ
          have hQnontrivial : Nontrivial (M ⧸ N) :=
            IsSimpleModule.nontrivial (R := L[G]) (M := M ⧸ N)
          exact ((not_subsingleton_iff_nontrivial.2 hQnontrivial) hQsub).elim

/-- Helper for Remark 16-16.3-5: if a finite-dimensional class equals a simple class in `R₀`,
then the two finite representations are isomorphic. -/
private theorem finiteRepClass_eq_simple_nonemptyIso
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    (T S : FDRep L G) (hS : Simple S) (hclass : [T]₀ = [S]₀) :
    Nonempty (T ≅ S) := by
  classical
  -- First prove that `T` is simple: a nonzero simple quotient with a nonzero kernel would split
  -- the class of `T` as a sum of two nonzero positive classes, impossible for `[S]₀`.
  have hTnotSub : ¬ Subsingleton T :=
    not_subsingleton_of_finiteRepClass_eq_simple (L := L) (G := G) T S hS hclass
  have hTsimple : Simple T := by
    let ρT : Representation L G T := T.ρ
    have hMnot : ¬ Subsingleton ρT.asModule := by
      intro hsub
      apply hTnotSub
      simpa [ρT, Representation.asModule] using hsub
    have hMsimple :
        @IsSimpleModule L[G] inferInstance ρT.asModule
          (Representation.instAddCommGroupAsModule ρT)
          (Representation.instModuleMonoidAlgebraAsModule ρT) := by
      refine @ofModule_isSimpleModule_of_finiteRepClass_eq_simple
        L inferInstance G inferInstance inferInstance ρT.asModule
        (Representation.instAddCommGroupAsModule ρT)
        (Representation.instModuleAsModule ρT)
        (finiteDimensional_asModule ρT)
        (Representation.instModuleMonoidAlgebraAsModule ρT)
        (Representation.instIsScalarTowerMonoidAlgebraAsModule ρT)
        S hS hMnot ?_
      -- Rewrite the rebuilt owner-module class back to the original finite representation `T`.
      simpa [fdRepOfAsModule, ρT] using
        (finiteRepGrothendieckClass_ofModule_asModule_eq_fdRep
          (L := L) (G := G) T).trans hclass
    have hIrr : ρT.IsIrreducible :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρT).2 hMsimple
    letI : Representation.IsIrreducible T.ρ := by
      simpa [ρT] using hIrr
    exact FDRep.simple_of_isIrreducible T
  letI : Simple T := hTsimple
  letI : Simple S := hS
  -- Once both sides are simple, complete-family basis separation gives the actual isomorphism.
  exact simpleClass_eq_simpleClass_nonemptyIso (L := L) (G := G) T S hclass

/-- Helper for Remark 16-16.3-5: a positive generic class whose decomposition is a simple
residue class yields an `(R')` lift. -/
theorem hasRPrimeLiftOfPositiveDecompositionClassEqSimple
    {A : Type u} [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    {G : Type u} [Group G]
    [IsDomain A] [IsDiscreteValuationRing A] [Finite G]
    (S : FDRep (IsLocalRing.ResidueField A) G) (hS : Simple S)
    {x : R₀[K](G)}
    (hxpos : x ∈ R⁺[K](G))
    (hxdec : decompositionHom A K G x = [S]₀) :
    FDRep.HasRPrimeLift S K := by
  -- Replace the positive class by an actual finite representation over the fraction field.
  rcases (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).1 hxpos with ⟨X, hXclass⟩
  obtain ⟨L⟩ := Representation.exists_stableLattice A X.ρ
  have hredClass :
      [FDRep.of L.reductionRepresentation]₀ = ([S]₀ : R₀[IsLocalRing.ResidueField A](G)) := by
    calc
      [FDRep.of L.reductionRepresentation]₀ =
          decompositionHom A K G [X]₀ := by
            exact (decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) X L).symm
      _ = decompositionHom A K G x := by rw [hXclass]
      _ = [S]₀ := hxdec
  have hredIso : Nonempty (FDRep.of L.reductionRepresentation ≅ S) :=
    finiteRepClass_eq_simple_nonemptyIso
      (G := G) (FDRep.of L.reductionRepresentation) S hS hredClass
  letI : Simple S := hS
  haveI : Simple (FDRep.of L.reductionRepresentation) :=
    Simple.of_iso hredIso.some
  have hredIrr : L.reductionRepresentation.IsIrreducible :=
    FDRep.isIrreducible_of_simple (FDRep.of L.reductionRepresentation)
  have hXIrr : Representation.IsIrreducible X.ρ :=
    simple_reduction_implies_isIrreducible (A := A) (K := K) (G := G) X.ρ L hredIrr
  letI : Representation.IsIrreducible X.ρ := hXIrr
  have hXsimple : Simple X :=
    FDRep.simple_of_isIrreducible X
  -- Package the simple generic representation, the stable lattice, and the reduction isomorphism.
  exact ⟨X, hXsimple, L, hredIso⟩

end Representation
