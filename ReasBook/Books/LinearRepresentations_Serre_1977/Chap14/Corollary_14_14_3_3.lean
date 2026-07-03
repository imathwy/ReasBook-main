import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_2
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_2
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open scoped MonoidAlgebra Representation

namespace Representation

section ProjectiveGrothendieckGroup

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type w}
local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: for `Representation.ofModule'`, the induced `k[G]`-action is
the original scalar action on the module. -/
private theorem ofModule'_asAlgebraHom_apply
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (r : k[G]) (m : M) :
    ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and check the identity on monomials.
  refine MonoidAlgebra.induction_on
    (p := fun s : k[G] =>
      ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: the owner module of `Representation.ofModule' M` is
canonically the original `k[G]`-module `M`. -/
private theorem nonempty_ofModule'_asModuleLinearEquiv
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M] :
    Nonempty ((Representation.ofModule' (k := k) (G := G) M).asModule ≃ₗ[k[G]] M) := by
  -- Use the standard `asModuleEquiv` and verify that it respects the original `k[G]`-action.
  let toFun : (Representation.ofModule' (k := k) (G := G) M).asModule → M :=
    fun x => (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := k) (G := G) M).asModule :=
    fun x => (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : k[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    -- Rewrite the transported action through `asModuleEquiv`, then identify it with the
    -- original `k[G]`-action on `M`.
    calc
      (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x) := by
                exact
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := k) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x := by
            simp [Representation.ofModule'_asAlgebraHom_apply]
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: a simple `k[G]`-module viewed through
`Representation.ofModule'` is irreducible. -/
private theorem ofModule'_isIrreducible_of_isSimpleModule
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    [IsSimpleModule k[G] M] :
    (Representation.ofModule' (k := k) (G := G) M).IsIrreducible := by
  -- Transfer simplicity across the canonical owner-module equivalence and then use the
  -- irreducibility/simple-module bridge.
  rcases nonempty_ofModule'_asModuleLinearEquiv (k := k) (G := G) M with ⟨eM⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := k) (G := G) M)).2
      (@IsSimpleModule.congr (k[G]) inferInstance
        ((Representation.ofModule' (k := k) (G := G) M).asModule)
        (Representation.ofModule' (k := k) (G := G) M).instAddCommGroupAsModule
        (Representation.ofModule' (k := k) (G := G) M).instModuleMonoidAlgebraAsModule
        M inferInstance inferInstance eM inferInstance)

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: an `L[G]`-linear equivalence of owner modules upgrades to a
representation equivalence. -/
private theorem nonempty_equiv_of_asModuleLinearEquiv
    {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.asModule ≃ₗ[k[G]] σ.asModule) :
    Nonempty (ρ.Equiv σ) := by
  -- View the `k[G]`-linear equivalence as an intertwiner and repackage it as a representation
  -- equivalence.
  let f : ρ.IntertwiningMap σ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := σ)).symm
      e.toLinearMap
  exact ⟨Representation.Equiv.mk (e.restrictScalars k) f.isIntertwining'⟩

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: an isomorphism of finite-dimensional representations induces
an equivalence of the underlying `k[G]`-modules. -/
private theorem nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso
    (τ σ : FDRep k G) (hτσ : Nonempty (τ ≅ σ)) :
    Nonempty (asModule τ.ρ ≃ₗ[k[G]] asModule σ.ρ) := by
  -- Forget the `FDRep` isomorphism to `Rep`, then read its image in `ModuleCat k[G]` as the
  -- required owner-module equivalence.
  rcases hτσ with ⟨e⟩
  exact ⟨by
    simpa using
      (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra
        (k := k) (G := G)).mapIso e).toLinearEquiv⟩

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: the largest semisimple quotient of a chosen projective
envelope is linearly equivalent to its simple target. -/
private theorem projectiveEnvelope_largestSemisimpleQuotient_linearEquiv_target
    (π : ι → FDRep k G)
    (hπ_simple : ∀ i, Simple (π i))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i : ι) :
    Nonempty (((P i).V ⧸ Module.jacobson k[G] (P i).V) ≃ₗ[k[G]] asModule (π i).ρ) := by
  letI : Simple (π i) := hπ_simple i
  let ρi : Representation k G (π i) := (π i).ρ
  let M : ModuleCat k[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj (π i))
  let f : (P i).V →ₗ[k[G]] M := by
    simpa [M, Rep.toModuleMonoidAlgebra] using (Classical.choose (hP_envelope i))
  have hf : f.IsProjectiveEnvelope := by
    simpa [M, Rep.toModuleMonoidAlgebra] using (Classical.choose_spec (hP_envelope i))
  letI : f.IsProjectiveEnvelope := hf
  have hsimple :
      IsSimpleModule k[G] M := by
    have hρi_irred : ρi.IsIrreducible := by
      simpa [ρi] using (FDRep.isIrreducible_of_simple (π i))
    simpa [M, Rep.toModuleMonoidAlgebra] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρi).mp hρi_irred
  letI : IsSimpleModule k[G] M := hsimple
  -- Compare the kernel of the envelope map with the Jacobson radical from both sides.
  have hjac_le : Module.jacobson k[G] (P i).V ≤ LinearMap.ker f := by
    have hcomap :
        Module.jacobson k[G] (P i).V ≤ Submodule.comap f (Module.jacobson k[G] M) :=
      Module.le_comap_jacobson (f := f)
    have hEq : Submodule.comap f (Module.jacobson k[G] M) = LinearMap.ker f := by
      rw [IsSimpleModule.jacobson_eq_bot (R := k[G]) (M := M), LinearMap.ker]
    exact hEq ▸ hcomap
  have hker_le : LinearMap.ker f ≤ Module.jacobson k[G] (P i).V := by
    exact hf.toIsEssential.ker_le_jacobson hf.surjective
  have hker : Module.jacobson k[G] (P i).V = LinearMap.ker f := le_antisymm hjac_le hker_le
  refine ⟨?_⟩
  simpa [M, Rep.toModuleMonoidAlgebra] using
    (Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective f hf.surjective)

/-- Helper for Corollary 14-14.3-3: the Jacobson quotient of a finite projective `k[G]`-module is
finite-dimensional over `k`. -/
private theorem largestSemisimpleQuotient_moduleFinite
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Finite k (P.V ⧸ Module.jacobson k[G] P.V) := by
  -- The quotient map is surjective, so finite generation descends from `P.V`.
  let _ : Module.Finite k P.V := P.finite
  exact
    Module.Finite.of_surjective
      ((Module.jacobson k[G] P.V).mkQ.restrictScalars k)
      (by
        intro x
        rcases Submodule.mkQ_surjective (Module.jacobson k[G] P.V) x with ⟨y, rfl⟩
        exact ⟨y, rfl⟩)

/-- Helper for Corollary 14-14.3-3: every finite-dimensional representation is canonically
isomorphic to the `FDRep.of` object rebuilt from its bundled representation. -/
private noncomputable def fdRepIsoOfRho
    (τ : FDRep k G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    -- Rebundling preserves the underlying carrier and action exactly.
    ext x
    rfl

/-- Helper for Corollary 14-14.3-3: rebundle the largest semisimple quotient of a finite
projective `k[G]`-module as a finite-dimensional representation. -/
private abbrev largestSemisimpleQuotient_fdRep
    (P : FiniteProjectiveGroupAlgebraModule k G) : FDRep k G :=
  let _ : Module.Finite k
      (Rep.ofModuleMonoidAlgebra.obj
        (ModuleCat.of k[G] (P.V ⧸ Module.jacobson k[G] P.V))) :=
    by
      simpa using largestSemisimpleQuotient_moduleFinite (k := k) (G := G) P
  FDRep.of
    (Rep.ofModuleMonoidAlgebra.obj
      (ModuleCat.of k[G] (P.V ⧸ Module.jacobson k[G] P.V))).ρ

/-- Helper for Corollary 14-14.3-3: the product of the two largest semisimple quotient modules is
again finite-dimensional over `k`. -/
private theorem largestSemisimpleQuotient_prod_toRep_moduleFinite
    (P Q : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Finite k
      (Rep.ofModuleMonoidAlgebra.obj
        (ModuleCat.of k[G]
          (((P.V ⧸ Module.jacobson k[G] P.V : Type u) ×
            (Q.V ⧸ Module.jacobson k[G] Q.V : Type u) : Type u)))) := by
  -- Finite-dimensionality is preserved under binary products.
  let _ : Module.Finite k (P.V ⧸ Module.jacobson k[G] P.V) :=
    largestSemisimpleQuotient_moduleFinite (k := k) (G := G) P
  let _ : Module.Finite k (Q.V ⧸ Module.jacobson k[G] Q.V) :=
    largestSemisimpleQuotient_moduleFinite (k := k) (G := G) Q
  simpa using
    (inferInstance :
      Module.Finite k
        ((P.V ⧸ Module.jacobson k[G] P.V) × (Q.V ⧸ Module.jacobson k[G] Q.V)))

/-- Helper for Corollary 14-14.3-3: package the product of the two largest semisimple quotient
modules as a finite-dimensional representation. -/
private abbrev largestSemisimpleQuotient_prod_fdRep
    (P Q : FiniteProjectiveGroupAlgebraModule k G) : FDRep k G :=
  let _ : Module.Finite k
      (Rep.ofModuleMonoidAlgebra.obj
        (ModuleCat.of k[G]
          (((P.V ⧸ Module.jacobson k[G] P.V : Type u) ×
            (Q.V ⧸ Module.jacobson k[G] Q.V : Type u) : Type u)))) :=
    largestSemisimpleQuotient_prod_toRep_moduleFinite (k := k) (G := G) P Q
  FDRep.of
    (Rep.ofModuleMonoidAlgebra.obj
      (ModuleCat.of k[G]
        (((P.V ⧸ Module.jacobson k[G] P.V : Type u) ×
          (Q.V ⧸ Module.jacobson k[G] Q.V : Type u) : Type u)))).ρ

/-- Helper for Corollary 14-14.3-3: the concrete product owner on the two largest semisimple
quotients realizes addition in `R₀[k](G)`. -/
private theorem largestSemisimpleQuotient_prod_fdRep_class_eq_add
    (P Q : FiniteProjectiveGroupAlgebraModule k G) :
    [largestSemisimpleQuotient_prod_fdRep (k := k) (G := G) P Q]₀ =
      [largestSemisimpleQuotient_fdRep (k := k) (G := G) P]₀ +
        [largestSemisimpleQuotient_fdRep (k := k) (G := G) Q]₀ := by
  let X₁ : FDRep k G := largestSemisimpleQuotient_fdRep (k := k) (G := G) P
  let X₂ : FDRep k G := largestSemisimpleQuotient_prod_fdRep (k := k) (G := G) P Q
  let X₃ : FDRep k G := largestSemisimpleQuotient_fdRep (k := k) (G := G) Q
  let Pquot : ModuleCat k[G] :=
    ModuleCat.of k[G] (P.V ⧸ Module.jacobson k[G] P.V : Type u)
  let Qquot : ModuleCat k[G] :=
    ModuleCat.of k[G] (Q.V ⧸ Module.jacobson k[G] Q.V : Type u)
  let Yquot : ModuleCat k[G] :=
    ModuleCat.of k[G]
      (((P.V ⧸ Module.jacobson k[G] P.V : Type u) ×
        (Q.V ⧸ Module.jacobson k[G] Q.V : Type u) : Type u))
  let FRep : ModuleCat k[G] ⥤ Rep k G := Rep.ofModuleMonoidAlgebra
  let fRep :
      (forget₂ (FDRep k G) (Rep k G)).obj X₁ ⟶
        (forget₂ (FDRep k G) (Rep k G)).obj X₂ :=
    FRep.map (ModuleCat.ofHom (LinearMap.inl k[G] Pquot Qquot))
  let gRep :
      (forget₂ (FDRep k G) (Rep k G)).obj X₂ ⟶
        (forget₂ (FDRep k G) (Rep k G)).obj X₃ :=
    FRep.map (ModuleCat.ofHom (LinearMap.snd k[G] Pquot Qquot))
  let f : X₁ ⟶ X₂ := (FDRep.forget₂HomLinearEquiv X₁ X₂) fRep
  let g : X₂ ⟶ X₃ := (FDRep.forget₂HomLinearEquiv X₂ X₃) gRep
  have hf : (forget₂ (FDRep k G) (Rep k G)).map f = fRep := by
    change (FDRep.forget₂HomLinearEquiv X₁ X₂).symm
        ((FDRep.forget₂HomLinearEquiv X₁ X₂) fRep) = fRep
    exact (FDRep.forget₂HomLinearEquiv X₁ X₂).left_inv fRep
  have hg : (forget₂ (FDRep k G) (Rep k G)).map g = gRep := by
    change (FDRep.forget₂HomLinearEquiv X₂ X₃).symm
        ((FDRep.forget₂HomLinearEquiv X₂ X₃) gRep) = gRep
    exact (FDRep.forget₂HomLinearEquiv X₂ X₃).left_inv gRep
  let S : ShortComplex (FDRep k G) := ShortComplex.mk f g (by
    apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    rw [Functor.map_comp, hf, hg]
    ext x
    rfl)
  let SRep : ShortComplex (Rep k G) := ShortComplex.mk fRep gRep (by
    ext x
    rfl)
  have hMod : (SRep.map (forget₂ (Rep k G) (ModuleCat k))).ShortExact := by
    -- Forget to `ModuleCat k`, where the quotient product sequence is split exact.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.moduleCat_exact_iff]
      intro y hy
      rcases y with ⟨y₁, y₂⟩
      change y₂ = 0 at hy
      refine ⟨y₁, ?_⟩
      cases hy
      rfl
    · rw [ModuleCat.mono_iff_injective]
      intro x y hxy
      simpa using congrArg Prod.fst hxy
    · rw [ModuleCat.epi_iff_surjective]
      intro y
      exact ⟨(0, y), rfl⟩
  have hRep' : SRep.ShortExact := by
    -- Reflect short exactness from the underlying `k`-modules back to `Rep k G`.
    apply (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SRep) (F := forget₂ (Rep k G) (ModuleCat k))).1
    simpa using hMod
  have hRep : (S.map (forget₂ (FDRep k G) (Rep k G))).ShortExact := by
    -- The `Rep`-image of the `FDRep` short complex is definitionally the same sequence.
    simpa [S, SRep, hf, hg] using hRep'
  have hS : S.ShortExact := by
    -- Reflect exactness and mono/epi back to `FDRep`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        ((S.exact_map_iff_of_faithful (forget₂ (FDRep k G) (Rep k G))).1 hRep.exact)
    · exact (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map hRep.mono_f
    · exact (forget₂ (FDRep k G) (Rep k G)).epi_of_epi_map hRep.epi_g
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := G) S hS
  simpa [X₁, X₂, X₃, S] using hrelation

/-- Helper for Corollary 14-14.3-3: a split exact sequence of modules identifies the middle term
with the product of the two outer terms. -/
private noncomputable def linearEquivProdOfRightSplitExact
    {R : Type u} [Ring R]
    {X₁ : Type w} [AddCommGroup X₁] [Module R X₁]
    {X₂ : Type w} [AddCommGroup X₂] [Module R X₂]
    {X₃ : Type w} [AddCommGroup X₃] [Module R X₃]
    (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hf : Function.Injective f) (hexact : Function.Exact f g)
    (s : X₃ →ₗ[R] X₂) (hs : g.comp s = LinearMap.id) :
    (X₁ × X₃) ≃ₗ[R] X₂ := by
  -- Package the split exact sequence as a biproduct decomposition in `ModuleCat`.
  let hexact' : LinearMap.range f = LinearMap.ker g := by
    simpa [LinearMap.exact_iff, eq_comm] using hexact
  exact
    ((ShortComplex.Splitting.ofExactOfSection _
      (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom f)
        (ModuleCat.ofHom g) hexact')
      (ModuleCat.ofHom s) (ModuleCat.hom_ext hs)
      (by simpa only [ModuleCat.mono_iff_injective] using hf)).isoBinaryBiproduct ≪≫
      ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv

/-- Helper for Corollary 14-14.3-3: a short exact sequence in `ModuleCat` with projective right
term splits, so the middle term is linearly equivalent to the product of the outer terms. -/
private theorem moduleCat_shortExact_middle_nonempty_linearEquiv_prod
    {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat R)) [Module.Projective R S.X₃] (hS : S.ShortExact) :
    Nonempty ((↑S.X₁ × ↑S.X₃) ≃ₗ[R] ↑S.X₂) := by
  have hsurj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hinj : Function.Injective S.f.hom := hS.moduleCat_injective_f
  have hexact : Function.Exact S.f.hom S.g.hom :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S := S)).1 hS.exact
  -- Choose a section of the right map and apply the split-exact decomposition.
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property S.g.hom (LinearMap.id : S.X₃ →ₗ[R] S.X₃) hsurj
  exact ⟨linearEquivProdOfRightSplitExact S.f.hom S.g.hom hinj hexact s hs⟩

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: forgetting a short complex of finite projective `k[G]`-modules
to `ModuleCat k[G]` preserves the relation `g ∘ f = 0`. -/
private theorem finiteProjective_underlying_moduleCat_zero
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    S.f.hom.hom ≫ S.g.hom.hom = 0 := by
  let F : FiniteProjectiveGroupAlgebraModule k G ⥤ ModuleCat k[G] :=
    (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
      (ModuleCat.isFG k[G]).ι
  -- The mapped short complex has the same concrete structure maps.
  simpa using (S.map F).zero

/-- Helper for Corollary 14-14.3-3: the forgotten `ModuleCat k[G]` object of a finite projective
module is categorically projective. -/
private theorem finiteProjective_projective_moduleCat
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Projective ((ModuleCat.isFG k[G]).ι.obj P.obj) := by
  -- The module-theoretic projectivity assumption on `P` matches the categorical projectivity
  -- statement in `ModuleCat k[G]`.
  letI : Module.Projective k[G] ((ModuleCat.isFG k[G]).ι.obj P.obj) := by
    simpa using P.property
  infer_instance

/-- Helper for Corollary 14-14.3-3: the cyclic map generated by `x` in a `k[G]`-module sends
`1` to `x`. -/
private theorem regular_module_generated_map_apply_one
    {M : Type w} [AddCommGroup M] [Module k[G] M] (x : M) :
    (((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x) 1 : M) = x := by
  simp

/-- Helper for Corollary 14-14.3-3: if `x` lies in the kernel of `g`, then the cyclic map
`r ↦ r • x` from the regular module also lands in that kernel. -/
private theorem regular_module_generated_map_comp_zero
    {M : Type w} [AddCommGroup M] [Module k[G] M]
    {N : Type w} [AddCommGroup N] [Module k[G] N]
    (g : M →ₗ[k[G]] N) (x : M) (hx : g x = 0) :
    g.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x) = 0 := by
  ext
  simp [hx]

/-- Helper for Corollary 14-14.3-3: the regular `k[G]`-module viewed in the finite-projective
owner category. -/
private abbrev finiteProjective_regular_owner :
    FiniteProjectiveGroupAlgebraModule k G :=
  ⟨FGModuleCat.of k[G] k[G], inferInstance⟩

/-- Helper for Corollary 14-14.3-3: a `k`-linear functional on a `k[G]`-module determines a
`k[G]`-linear map to the regular module by reading coefficients after translating the input. -/
private noncomputable def reconstruct_from_coeff_one_module
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (L : M →ₗ[k] k) : M →ₗ[k[G]] k[G] := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine
    { toFun := fun m => Finsupp.equivFunOnFinite.symm fun t => L ((MonoidAlgebra.of k G t⁻¹) • m)
      map_add' := by
        intro x y
        apply Finsupp.equivFunOnFinite.injective
        funext t
        simp [smul_add, map_add]
      map_smul' := ?_ }
  intro a m
  let h : k[G] := Finsupp.equivFunOnFinite.symm fun t => L ((MonoidAlgebra.of k G t⁻¹) • m)
  apply Finsupp.equivFunOnFinite.injective
  funext t
  let P : k[G] → Prop := fun b => L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) = (b * h) t
  have hPa : P a := by
    refine MonoidAlgebra.induction_on a ?_ ?_ ?_
    · intro g
      have hsmul :
          MonoidAlgebra.single t⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m =
            (MonoidAlgebra.single (t⁻¹ * g) (1 : k) : k[G]) • m := by
        simpa using
          (smul_assoc (MonoidAlgebra.single t⁻¹ (1 : k)) (MonoidAlgebra.single g (1 : k)) m).symm
      -- Read the translated coefficient on the basis vector `g`.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((MonoidAlgebra.of k G g) • m)) =
            L (MonoidAlgebra.single t⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m) := by
              simp [MonoidAlgebra.of_apply]
        _ = L ((MonoidAlgebra.single (t⁻¹ * g) (1 : k) : k[G]) • m) := by
              exact congrArg L hsmul
        _ = (((MonoidAlgebra.of k G g) * h : k[G]) t) := by
              simp [h, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply]
    · intro b c hb hc
      -- Additivity of the functional matches additivity of the reconstructed regular-module map.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((b + c) • m)) =
            L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) +
              L ((MonoidAlgebra.of k G t⁻¹) • (c • m)) := by
                simp [add_smul, map_add]
        _ = (b * h) t + (c * h) t := by rw [hb, hc]
        _ = ((b + c) * h) t := by simp [add_mul]
    · intro r b hb
      -- Scalar multiples commute with the translated coefficient reconstruction.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((r • b) • m)) =
            r * L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
              have hs :
                  (MonoidAlgebra.of k G t⁻¹) • ((r • b) • m) =
                    r • ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
                calc
                  (MonoidAlgebra.of k G t⁻¹) • ((r • b) • m) =
                      (((MonoidAlgebra.of k G t⁻¹) * (r • b)) : k[G]) • m := by
                        simpa using
                          (smul_assoc (MonoidAlgebra.of k G t⁻¹) (r • b) m).symm
                  _ = (r • (((MonoidAlgebra.of k G t⁻¹) * b : k[G]))) • m := by
                        rw [mul_smul_comm]
                  _ = r • ((((MonoidAlgebra.of k G t⁻¹) * b : k[G])) • m) := by
                        simpa using
                          (smul_assoc r (((MonoidAlgebra.of k G t⁻¹) * b : k[G])) m)
                  _ = r • ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
                        simpa [smul_eq_mul] using
                          congrArg (fun x : M => r • x) (smul_assoc (MonoidAlgebra.of k G t⁻¹) b m)
              calc
                L ((MonoidAlgebra.of k G t⁻¹) • ((r • b) • m)) =
                    L (r • ((MonoidAlgebra.of k G t⁻¹) • (b • m))) := by
                      exact congrArg L hs
                _ = r * L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by simp
        _ = r * (b * h) t := by rw [hb]
        _ = ((r • b) * h) t := by simp
  exact hPa

/-- Helper for Corollary 14-14.3-3: evaluating the reconstructed regular-module map at `t`
recovers the chosen translated coefficient. -/
@[simp] private theorem reconstruct_from_coeff_one_module_apply
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (L : M →ₗ[k] k) (m : M) (t : G) :
    reconstruct_from_coeff_one_module (k := k) (G := G) (M := M) L m t =
      L ((MonoidAlgebra.of k G t⁻¹) • m) :=
  rfl

/-- Helper for Corollary 14-14.3-3: a nontrivial finite `k[G]`-module admits a nonzero map to the
regular module `k[G]`. -/
private theorem exists_nonzero_map_to_regular_of_nontrivial
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    [Module.Finite k M] [Nontrivial M] :
    ∃ φ : M →ₗ[k[G]] k[G], φ ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hrepr_ne : b.repr m ≠ 0 := by
    intro hrepr
    exact hm ((LinearEquiv.map_eq_zero_iff b.repr).1 hrepr)
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.1 hrepr_ne
  let L : M →ₗ[k] k := (Finsupp.lapply t).comp b.repr.toLinearMap
  let φ : M →ₗ[k[G]] k[G] := reconstruct_from_coeff_one_module (k := k) (G := G) L
  refine ⟨φ, ?_⟩
  intro hφ
  have hφm : φ m = 0 := by
    simpa [hφ]
  have hLm' : L ((MonoidAlgebra.of k G (1 : G)⁻¹) • m) = 0 := by
    simpa [φ, reconstruct_from_coeff_one_module_apply] using
      congrArg (fun z : k[G] => z 1) hφm
  have hof_one : (MonoidAlgebra.of k G ((1 : G)⁻¹) : k[G]) = 1 := by
    ext g
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.one_def]
  have hsingle_one_smul : (MonoidAlgebra.single 1 (1 : k) : k[G]) • m = m := by
    simpa [MonoidAlgebra.one_def] using (one_smul k[G] m)
  have hLm : L m = 0 := by
    have hLm'' : L ((MonoidAlgebra.single 1 (1 : k) : k[G]) • m) = 0 := by
      simpa [hof_one, MonoidAlgebra.one_def] using hLm'
    simpa [hsingle_one_smul] using hLm''
  exact ht (by simpa [L] using hLm)

/-- Helper for Corollary 14-14.3-3: an epimorphism in the finite-projective owner category should
already be surjective on the underlying `k[G]`-linear map. -/
private theorem finiteProjective_underlying_surjective_of_epi
    {E X : FiniteProjectiveGroupAlgebraModule k G} (e : E ⟶ X) [Epi e] :
    Function.Surjective e.hom.hom.hom := by
  let eLin : E.V →ₗ[k[G]] X.V := e.hom.hom.hom
  by_contra hnsurj
  let Q : Type u := X.V ⧸ LinearMap.range eLin
  let q : X.V →ₗ[k[G]] Q := (LinearMap.range eLin).mkQ
  have hQ_nontrivial : Nontrivial Q := by
    -- Route correction: use the nonzero quotient `X.V / range(e)` directly, then probe it with a
    -- map to the regular module instead of transporting epimorphisms out of the owner category.
    apply not_subsingleton_iff_nontrivial.mp
    intro hQ_sub
    apply hnsurj
    exact LinearMap.range_eq_top.mp ((Submodule.Quotient.subsingleton_iff).mp hQ_sub)
  letI : Nontrivial Q := hQ_nontrivial
  letI : Module k Q := Module.compHom Q (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Finite k Q := by
    let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
    exact Module.Finite.trans k[G] Q
  obtain ⟨η, hη_nonzero⟩ :=
    exists_nonzero_map_to_regular_of_nontrivial (k := k) (G := G) (M := Q)
  let gLin : X.V →ₗ[k[G]] k[G] := η.comp q
  have hq_comp : q.comp eLin = 0 := by
    -- The quotient map kills the range of `e`.
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hgLin_comp : gLin.comp eLin = 0 := by
    -- Therefore the induced map to the regular module annihilates `e` exactly.
    ext x t
    have hηx : η (q (eLin x)) = 0 := by
      rw [show q (eLin x) = 0 by exact LinearMap.congr_fun hq_comp x, LinearMap.map_zero]
    simpa [gLin, LinearMap.comp_apply] using congrArg (fun z : k[G] => z t) hηx
  have hgLin_nonzero : gLin ≠ 0 := by
    -- Surjectivity of the quotient map turns a zero composite back into a zero probe map on `Q`.
    intro hgLin_zero
    have hη_zero : η = (0 : Q →ₗ[k[G]] k[G]) := by
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range eLin) y
      exact LinearMap.congr_fun hgLin_zero x
    exact hη_nonzero hη_zero
  let g : X ⟶ finiteProjective_regular_owner (k := k) (G := G) :=
    ObjectProperty.homMk (FGModuleCat.ofHom gLin)
  have hg_nonzero : g ≠ 0 := by
    -- Read zero in the owner category back as zero on the underlying `k[G]`-linear map.
    intro hg_zero
    have hg_hom_zero : g.hom = 0 := by
      simpa using
        congrArg (fun f : X ⟶ finiteProjective_regular_owner (k := k) (G := G) => f.hom) hg_zero
    rw [show g = ObjectProperty.homMk (FGModuleCat.ofHom gLin) by rfl] at hg_hom_zero
    have hg_lin_zero : gLin = 0 := by
      ext x t
      have h0 :=
        congrArg
          (fun f : X.obj ⟶ (finiteProjective_regular_owner (k := k) (G := G)).obj =>
            (f.hom.hom x) t)
          hg_hom_zero
      simpa [FGModuleCat.ofHom] using h0
    exact hgLin_nonzero hg_lin_zero
  have hge : e ≫ g = 0 := by
    -- Package the annihilating linear-map identity as an equality in the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x t
    simpa [g, FGModuleCat.ofHom, LinearMap.comp_apply] using
      congrArg (fun z : k[G] => z t) (LinearMap.congr_fun hgLin_comp x)
  have : g = 0 := (cancel_epi e).1 (by simpa using hge)
  exact hg_nonzero this

/-- Helper for Corollary 14-14.3-3: the regular owner is projective in the finite-projective
category because an owner epimorphism is already surjective on underlying `k[G]`-modules. -/
private theorem regular_owner_projective :
    Projective (finiteProjective_regular_owner (k := k) (G := G)) := by
  refine ⟨?_⟩
  intro E X f e hepi
  letI : Epi e := hepi
  let eLin : E.V →ₗ[k[G]] X.V := e.hom.hom.hom
  let fLin : k[G] →ₗ[k[G]] X.V := f.hom.hom.hom
  have hsurj : Function.Surjective eLin := by
    -- The owner epi already induces an epi in `FGModuleCat`, hence a surjective linear map.
    simpa [eLin] using finiteProjective_underlying_surjective_of_epi (k := k) (G := G) e
  obtain ⟨l, hl⟩ := Module.projective_lifting_property eLin fLin hsurj
  refine ⟨ObjectProperty.homMk (FGModuleCat.ofHom l), ?_⟩
  -- Repackage the linear lift as a morphism in the owner category.
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  simpa [eLin, fLin] using hl

/-- Helper for Corollary 14-14.3-3: a kernel element of the forgotten right map comes from the
forgotten left map by lifting the regular cyclic map through the source exactness witness. -/
private theorem finiteProjective_regular_owner_lift_of_kernel_element
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact)
    (x₂ : S.X₂.V) (hx₂ : S.g.hom.hom x₂ = 0) :
    ∃ x₁ : S.X₁.V, S.f.hom.hom x₁ = x₂ := by
  haveI : Projective (finiteProjective_regular_owner (k := k) (G := G)) :=
    regular_owner_projective (k := k) (G := G)
  haveI : S.HasHomology := hS.exact.hasHomology
  let hLeft := S.leftHomologyData
  let ψ₂ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₂ :=
    ObjectProperty.homMk (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂))
  have hψ₂_zero_lin :
      S.g.hom.hom.hom.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) = 0 := by
    exact regular_module_generated_map_comp_zero (k := k) (G := G) S.g.hom.hom.hom x₂ hx₂
  have hψ₂_zero : ψ₂ ≫ S.g = 0 := by
    -- The cyclic map lands in cycles because `x₂` is in the kernel of `g`.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    simpa [ψ₂, FGModuleCat.ofHom] using hψ₂_zero_lin
  let ψK : finiteProjective_regular_owner (k := k) (G := G) ⟶ hLeft.K :=
    hLeft.liftK ψ₂ hψ₂_zero
  haveI : Epi hLeft.f' := hS.exact.epi_f' hLeft
  let ψ₁ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₁ :=
    Projective.factorThru ψK hLeft.f'
  have hψ₁_factor : ψ₁ ≫ hLeft.f' = ψK := by
    simpa [ψ₁] using (Projective.factorThru_comp ψK hLeft.f')
  have hψ₁f : ψ₁ ≫ S.f = ψ₂ := by
    -- Compare both morphisms after factoring through the chosen cycles object `K`.
    calc
      ψ₁ ≫ S.f = ψ₁ ≫ hLeft.f' ≫ hLeft.i := by
        simp [hLeft.f'_i]
      _ = ψK ≫ hLeft.i := by
        simpa [Category.assoc] using congrArg (fun φ => φ ≫ hLeft.i) hψ₁_factor
      _ = ψ₂ := by
        simpa [ψK] using hLeft.liftK_i ψ₂ hψ₂_zero
  refine ⟨ψ₁.hom.hom.hom 1, ?_⟩
  -- Evaluating the lifted equality at `1` recovers the desired preimage of `x₂`.
  have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ₁f) 1
  have hEval' :
      S.f.hom.hom.hom (ψ₁.hom.hom.hom 1) =
        ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) 1 := by
    have hψ₂_eval :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂)).hom) 1 =
          ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) 1 := rfl
    exact hEval.trans hψ₂_eval
  simpa [regular_module_generated_map_apply_one (k := k) (x := x₂)] using hEval'

/-- Helper for Corollary 14-14.3-3: owner-category exactness is already exactness of the
underlying `k[G]`-linear maps. -/
private theorem finiteProjective_underlying_function_exact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    Function.Exact S.f.hom.hom S.g.hom.hom := by
  intro x₂
  constructor
  · intro hx₂
    -- Route correction: use the regular cyclic map and left-homology factorization, rather than
    -- an unavailable functorial exactness bridge from the owner category.
    exact
      finiteProjective_regular_owner_lift_of_kernel_element
        (k := k) (G := G) S hS x₂ hx₂
  · intro hx₂
    -- The easy direction is just `g ∘ f = 0` on underlying elements.
    rcases hx₂ with ⟨x₁, hx₁⟩
    have hzero : S.g.hom.hom (S.f.hom.hom x₁) = 0 := by
      simpa using
        ConcreteCategory.congr_hom
          (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S) x₁
    simpa [hx₁] using hzero

/-- Helper for Corollary 14-14.3-3: mono and epi in the finite-projective owner category remain
injective and surjective on the forgotten `k[G]`-linear maps. -/
private theorem finiteProjective_underlying_injective_surjective_bridge
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    Function.Injective S.f.hom.hom ∧ Function.Surjective S.g.hom.hom := by
  constructor
  · -- A kernel element for `f` gives a cyclic owner morphism killed by `f`; mono forces it to be
    -- zero, so evaluation at `1` shows the element itself vanishes.
    intro x y hxy
    let ψ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₁ :=
      ObjectProperty.homMk
        (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)))
    have hψ_zero_lin :
        S.f.hom.hom.hom.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) = 0 := by
      ext z
      simp [hxy]
    have hψ_zero : ψ ≫ S.f = 0 := by
      apply ObjectProperty.hom_ext
      apply FGModuleCat.hom_ext
      simpa [ψ, FGModuleCat.ofHom] using hψ_zero_lin
    letI : Mono S.f := hS.mono_f
    have hψ_eq_zero : ψ = 0 := by
      exact (cancel_mono S.f).1 (by simpa using hψ_zero)
    have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ_eq_zero) 1
    have hEval' :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y))).hom) 1 =
          0 := by
      -- Read the equality `ψ = 0` at `1`, then identify both sides concretely.
      simpa [ψ] using hEval
    have hEval'' :
        ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) 1 = 0 := by
      have hψ_eval :
          (ConcreteCategory.hom
              (FGModuleCat.ofHom
                ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y))).hom) 1 =
            ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) 1 := rfl
      exact hψ_eval.symm.trans hEval'
    have hdiff : x - y = 0 := by
      simpa [regular_module_generated_map_apply_one (k := k) (x := x - y)] using hEval''
    exact sub_eq_zero.mp hdiff
  · -- The surjective half is the same owner-to-underlying epi bridge needed for the lift proof.
    letI : Epi S.g := hS.epi_g
    simpa using finiteProjective_underlying_surjective_of_epi (k := k) (G := G) S.g

/-- Helper for Corollary 14-14.3-3: the underlying `ModuleCat k[G]` short complex of a short
exact sequence of finite projective `k[G]`-modules is itself short exact. -/
private theorem finiteProjective_shortExact_underlying_moduleCat_shortExact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)).ShortExact := by
  obtain ⟨hf, hg⟩ :=
    finiteProjective_underlying_injective_surjective_bridge (k := k) (G := G) S hS
  -- Package the rebuilt exactness and the forgotten mono/epi data into ambient short exactness.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact finiteProjective_underlying_function_exact (k := k) (G := G) S hS
  · rw [ModuleCat.mono_iff_injective]
    exact hf
  · rw [ModuleCat.epi_iff_surjective]
    exact hg

/-- Helper for Corollary 14-14.3-3: a short exact sequence of finite projective `k[G]`-modules
splits after forgetting to `ModuleCat k[G]`. -/
private noncomputable def finiteProjective_underlying_moduleCat_splitting
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)).Splitting :=
  let Smod : ShortComplex (ModuleCat k[G]) :=
    ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)
  let _ : Projective Smod.X₃ :=
    finiteProjective_projective_moduleCat (k := k) (G := G) S.X₃
  -- Once the forgotten sequence is short exact, LinearRepresentations_Serre_1977's source route is exactly that the
  -- projective right term splits it.
  (finiteProjective_shortExact_underlying_moduleCat_shortExact
      (k := k) (G := G) S hS).splittingOfProjective

/-- Helper for Corollary 14-14.3-3: the underlying `ModuleCat k[G]` short complex of a short
exact sequence of finite projective `k[G]`-modules is exact. -/
private theorem finiteProjective_exact_underlying_moduleCat
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)).Exact := by
  -- Exactness is the exact component of the rebuilt ambient short exact sequence.
  exact
    (finiteProjective_shortExact_underlying_moduleCat_shortExact
      (k := k) (G := G) S hS).exact

/-- Helper for Corollary 14-14.3-3: the largest semisimple quotient of the middle term of a short
exact sequence is the product of the outer largest semisimple quotients. -/
private theorem largestSemisimpleQuotient_middle_nonempty_linearEquiv_prod
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G))
    (hUnderlying :
      (ShortComplex.mk S.f.hom.hom S.g.hom.hom
        (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)).ShortExact) :
    Nonempty
      ((S.X₂.V ⧸ Module.jacobson k[G] S.X₂.V) ≃ₗ[k[G]]
        (S.X₁.V ⧸ Module.jacobson k[G] S.X₁.V) ×
          (S.X₃.V ⧸ Module.jacobson k[G] S.X₃.V)) := by
  let Smod : ShortComplex (ModuleCat k[G]) :=
    ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)
  -- Split the middle term in `ModuleCat`, then descend that splitting to Jacobson quotients.
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  let _ : IsArtinian k[G] S.X₁.V := by infer_instance
  let _ : IsArtinian k[G] S.X₃.V := by infer_instance
  obtain ⟨e⟩ :=
    moduleCat_shortExact_middle_nonempty_linearEquiv_prod (R := k[G]) (S := Smod) hUnderlying
  let q :
      S.X₁.V × S.X₃.V →ₗ[k[G]]
        S.X₂.V ⧸ Module.jacobson k[G] S.X₂.V :=
    (Module.jacobson k[G] S.X₂.V).mkQ.comp e.toLinearMap
  have hq_surj : Function.Surjective q := by
    intro y
    obtain ⟨x₂, rfl⟩ := Submodule.mkQ_surjective (Module.jacobson k[G] S.X₂.V) y
    obtain ⟨x, rfl⟩ := e.surjective x₂
    exact ⟨x, rfl⟩
  have hker :
      q.ker = Module.jacobson k[G] (S.X₁.V × S.X₃.V) := by
    -- Transport the Jacobson radical through the split equivalence.
    calc
      q.ker = Submodule.comap e.toLinearMap (Module.jacobson k[G] S.X₂.V) := by
        simpa [q] using
          (LinearMap.ker_comp e.toLinearMap (Module.jacobson k[G] S.X₂.V).mkQ)
      _ = Module.jacobson k[G] (S.X₁.V × S.X₃.V) := by
        simpa using
          (Module.comap_jacobson_of_bijective
            (R := k[G]) (R₂ := k[G]) (τ₁₂ := RingHom.id k[G]) (f := e.toLinearMap)
            e.bijective)
  have hquot :
      ((S.X₁.V × S.X₃.V) ⧸ Module.jacobson k[G] (S.X₁.V × S.X₃.V)) ≃ₗ[k[G]]
        (S.X₂.V ⧸ Module.jacobson k[G] S.X₂.V) := by
    -- Replace the Jacobson quotient by the quotient through `ker q`.
    exact
      (Submodule.quotEquivOfEq
        (Module.jacobson k[G] (S.X₁.V × S.X₃.V)) q.ker hker.symm).trans
        (LinearMap.quotKerEquivOfSurjective q hq_surj)
  obtain ⟨eprod⟩ := largestSemisimpleQuotient_prod_linearEquiv
    (R := k[G]) (P := S.X₁.V) (Q := S.X₃.V)
  exact ⟨hquot.symm.trans eprod⟩

/-- Helper for Corollary 14-14.3-3: on a short exact sequence of finite projective `k[G]`-modules,
taking largest semisimple quotients yields the corresponding additive relation in `R₀[k](G)`. -/
private theorem largestSemisimpleQuotient_class_middle_eq_left_add_right
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    [largestSemisimpleQuotient_fdRep (k := k) (G := G) S.X₂]₀ =
      [largestSemisimpleQuotient_fdRep (k := k) (G := G) S.X₁]₀ +
        [largestSemisimpleQuotient_fdRep (k := k) (G := G) S.X₃]₀ := by
  let Smod : ShortComplex (ModuleCat k[G]) :=
    ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)
  have hUnderlying :
      Smod.ShortExact :=
    finiteProjective_shortExact_underlying_moduleCat_shortExact (k := k) (G := G) S hS
  obtain ⟨equot⟩ :=
    largestSemisimpleQuotient_middle_nonempty_linearEquiv_prod (k := k) (G := G) S hUnderlying
  have hprod_iso :
      Nonempty
        (largestSemisimpleQuotient_fdRep (k := k) (G := G) S.X₂ ≅
          largestSemisimpleQuotient_prod_fdRep (k := k) (G := G) S.X₁ S.X₃) := by
    let FRep : ModuleCat k[G] ⥤ Rep k G := Rep.ofModuleMonoidAlgebra
    let _ :
        Module.Finite k
          (FRep.obj (ModuleCat.of k[G] (S.X₂.V ⧸ Module.jacobson k[G] S.X₂.V))) :=
      largestSemisimpleQuotient_moduleFinite (k := k) (G := G) S.X₂
    let _ :
        Module.Finite k
          (FRep.obj
            (ModuleCat.of k[G]
              ((S.X₁.V ⧸ Module.jacobson k[G] S.X₁.V) ×
                (S.X₃.V ⧸ Module.jacobson k[G] S.X₃.V)))) :=
      largestSemisimpleQuotient_prod_toRep_moduleFinite (k := k) (G := G) S.X₁ S.X₃
    let iRep :
        FRep.obj (ModuleCat.of k[G] (S.X₂.V ⧸ Module.jacobson k[G] S.X₂.V)) ≅
          FRep.obj
            (ModuleCat.of k[G]
              ((S.X₁.V ⧸ Module.jacobson k[G] S.X₁.V) ×
                (S.X₃.V ⧸ Module.jacobson k[G] S.X₃.V))) :=
      FRep.mapIso equot.toModuleIso
    exact
      ⟨by
        simpa [largestSemisimpleQuotient_fdRep, largestSemisimpleQuotient_prod_fdRep] using
          (Representation.Equiv.toFDRepIso (Representation.equivOfIso iRep))⟩
  have hmid :
      [largestSemisimpleQuotient_fdRep (k := k) (G := G) S.X₂]₀ =
        [largestSemisimpleQuotient_prod_fdRep (k := k) (G := G) S.X₁ S.X₃]₀ := by
    exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hprod_iso
  calc
    [largestSemisimpleQuotient_fdRep (k := k) (G := G) S.X₂]₀ =
        [largestSemisimpleQuotient_prod_fdRep (k := k) (G := G) S.X₁ S.X₃]₀ := hmid
    _ = [largestSemisimpleQuotient_fdRep (k := k) (G := G) S.X₁]₀ +
          [largestSemisimpleQuotient_fdRep (k := k) (G := G) S.X₃]₀ :=
      largestSemisimpleQuotient_prod_fdRep_class_eq_add (k := k) (G := G) S.X₁ S.X₃

/-- Helper for Corollary 14-14.3-3: the free lift sending a projective class to the class of its
largest semisimple quotient. -/
private abbrev largestSemisimpleQuotientLift :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k G) →+ R₀[k](G) :=
  FreeAbelianGroup.lift fun P ↦ [largestSemisimpleQuotient_fdRep (k := k) (G := G) P]₀

/-- Helper for Corollary 14-14.3-3: the defining projective Grothendieck relations vanish after
passing to largest semisimple quotients. -/
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_largestSemisimpleQuotientLift_ker :
    finiteProjectiveGroupAlgebraGrothendieckRelations (A := k) (G := G) ≤
      largestSemisimpleQuotientLift (k := k) (G := G).ker := by
  -- Evaluate the free lift on each generator relation and rewrite it using the quotient class
  -- additivity theorem above.
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    largestSemisimpleQuotientLift (k := k) (G := G)
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [largestSemisimpleQuotientLift, map_sub]
  rw [sub_eq_zero, sub_eq_iff_eq_add, add_comm]
  exact largestSemisimpleQuotient_class_middle_eq_left_add_right (k := k) (G := G) S hS

/-- Helper for Corollary 14-14.3-3: passage to the largest semisimple quotient descends to a
homomorphism `P₀[k](G) → R₀[k](G)`. -/
private def largestSemisimpleQuotientHom :
    P₀[k](G) →+ R₀[k](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations (A := k) (G := G))
    (largestSemisimpleQuotientLift (k := k) (G := G))
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_largestSemisimpleQuotientLift_ker
      (k := k) (G := G))

/-- Helper for Corollary 14-14.3-3: the largest-semisimple-quotient homomorphism sends a
projective generator class to the class of its largest semisimple quotient. -/
@[simp] private theorem largestSemisimpleQuotientHom_projectiveClass_eq
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    largestSemisimpleQuotientHom (k := k) (G := G) [P]ₚ₀ =
      [largestSemisimpleQuotient_fdRep (k := k) (G := G) P]₀ := by
  -- The descended homomorphism agrees with the free lift on generators.
  rfl

/-- Helper for Corollary 14-14.3-3: the largest semisimple quotient of a chosen envelope source
is isomorphic, as an `FDRep`, to the corresponding simple target. -/
private theorem projectiveEnvelope_largestSemisimpleQuotient_nonempty_iso_target
    (π : ι → FDRep k G)
    (hπ_simple : ∀ i, Simple (π i))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i : ι) :
    Nonempty (largestSemisimpleQuotient_fdRep (k := k) (G := G) (P i) ≅ π i) := by
  -- Turn the quotient-module equivalence into an isomorphism of rebuilt representations, then
  -- compare that rebuilt target with the original `FDRep` owner.
  obtain ⟨eLin⟩ :=
    projectiveEnvelope_largestSemisimpleQuotient_linearEquiv_target
      (k := k) (G := G) π hπ_simple P hP_envelope i
  let eRep :
      (forget₂ (FDRep k G) (Rep k G)).obj
          (largestSemisimpleQuotient_fdRep (k := k) (G := G) (P i)) ≅
        (forget₂ (FDRep k G) (Rep k G)).obj (π i) := by
    simpa [largestSemisimpleQuotient_fdRep] using
      (Rep.ofModuleMonoidAlgebra.mapIso eLin.toModuleIso ≪≫
        (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj (π i))).symm)
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv
      (largestSemisimpleQuotient_fdRep (k := k) (G := G) (P i)) (π i)) eRep.hom,
    (FDRep.forget₂HomLinearEquiv (π i)
      (largestSemisimpleQuotient_fdRep (k := k) (G := G) (P i))) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Corollary 14-14.3-3: on a chosen projective envelope, the largest-semisimple-
quotient hom recovers the corresponding simple class. -/
@[simp] private theorem projectiveEnvelope_largestSemisimpleQuotientHom_projectiveClass_eq
    (π : ι → FDRep k G)
    (hπ_simple : ∀ i, Simple (π i))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i : ι) :
    largestSemisimpleQuotientHom (k := k) (G := G) [P i]ₚ₀ = [π i]₀ := by
  -- Identify the quotient class with the target simple class through the envelope quotient
  -- equivalence.
  calc
    largestSemisimpleQuotientHom (k := k) (G := G) [P i]ₚ₀ =
        [largestSemisimpleQuotient_fdRep (k := k) (G := G) (P i)]₀ :=
      largestSemisimpleQuotientHom_projectiveClass_eq (k := k) (G := G) (P i)
    _ = [π i]₀ := by
      exact
        finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G)
          (projectiveEnvelope_largestSemisimpleQuotient_nonempty_iso_target
            (k := k) (G := G) π hπ_simple P hP_envelope i)

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: the class of the product of two finite projective modules is
the sum of their classes in `P₀[k](G)`. -/
private theorem projective_class_prod_eq_add
    (Q R : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule k G,
      Nonempty (W.V ≃ₗ[k[G]] (Q.V × R.V)) ∧
      [W]ₚ₀ = [Q]ₚ₀ + [R]ₚ₀ := by
  let W0 : ModuleCat k[G] := ModuleCat.of k[G] (Q.V × R.V)
  have hfinite : Module.Finite k[G] W0 := by
    change Module.Finite k[G] (Q.V × R.V)
    infer_instance
  let Wfg : FGModuleCat k[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective k[G] Wfg := by
    change Module.Projective k[G] (Q.V × R.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule k G := ⟨Wfg, hproj⟩
  let f : Q ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inl k[G] Q.V R.V))
  let g : W ⟶ R :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.snd k[G] Q.V R.V))
  let r : W ⟶ Q :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.fst k[G] Q.V R.V))
  let s : R ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inr k[G] Q.V R.V))
  let T : ShortComplex (FiniteProjectiveGroupAlgebraModule k G) :=
    ShortComplex.mk f g (by
      ext x
      rfl)
  have hsplit : T.Splitting := by
    -- The product projections and inclusions give the standard splitting.
    refine
      { r := r
        s := s
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.fst k[G] Q.V R.V) ((LinearMap.inl k[G] Q.V R.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.snd k[G] Q.V R.V) ((LinearMap.inr k[G] Q.V R.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change
        (LinearMap.inl k[G] Q.V R.V ((LinearMap.fst k[G] Q.V R.V) (x, y)) +
            LinearMap.inr k[G] Q.V R.V ((LinearMap.snd k[G] Q.V R.V) (x, y))) =
          (x, y)
      simp
  have hT : T.ShortExact := hsplit.shortExact
  have hclass :=
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := k) (G := G) T hT
  refine ⟨W, ?_, ?_⟩
  · -- The chosen owner of `W` is the product module itself.
    exact ⟨by
      change W0 ≃ₗ[k[G]] Q.V × R.V
      exact LinearEquiv.refl k[G] (Q.V × R.V)⟩
  · simpa [T, W, Wfg, W0] using hclass

omit [Finite G] in
/-- Helper for Corollary 14-14.3-3: if every member of a finite family of projectives has class in
a submodule `S`, then so does a projective representative of their finite product. -/
private theorem projective_fin_family_class_mem_submodule
    (S : Submodule ℤ (P₀[k](G))) :
    ∀ {n : ℕ} (Q : Fin n → FiniteProjectiveGroupAlgebraModule k G),
      (∀ i, [Q i]ₚ₀ ∈ S) →
      ∃ W : FiniteProjectiveGroupAlgebraModule k G,
        Nonempty (W.V ≃ₗ[k[G]] ((i : Fin n) → (Q i).V)) ∧ [W]ₚ₀ ∈ S
  | 0, Q, hQ => by
      let W0 : ModuleCat k[G] := ModuleCat.of k[G] (ULift.{u, 0} PUnit)
      have hfinite : Module.Finite k[G] W0 := by
        change Module.Finite k[G] (ULift.{u, 0} PUnit)
        infer_instance
      let Wfg : FGModuleCat k[G] := ⟨W0, hfinite⟩
      have hproj : Module.Projective k[G] Wfg := by
        change Module.Projective k[G] (ULift.{u, 0} PUnit)
        infer_instance
      let W : FiniteProjectiveGroupAlgebraModule k G := ⟨Wfg, hproj⟩
      refine ⟨W, ?_, ?_⟩
      · -- The empty product is the zero module.
        refine ⟨by
          change W0 ≃ₗ[k[G]] ((i : Fin 0) → (Q i).V)
          exact LinearEquiv.ofSubsingleton _ _⟩
      · -- The zero projective class belongs to every submodule.
        have hW0_zero : IsZero W0 := by
          exact
            (ModuleCat.isZero_of_iff_subsingleton (R := k[G]) (M := ULift.{u, 0} PUnit)).2
              inferInstance
        have hWfg_zero : IsZero Wfg := by
          exact IsZero.of_full_of_faithful_of_isZero (ModuleCat.isFG k[G]).ι Wfg hW0_zero
        have hW_zero : IsZero W := by
          exact
            IsZero.of_full_of_faithful_of_isZero
              (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M))
              W hWfg_zero
        have hWclass :
            [W]ₚ₀ = 0 := by
          calc
            [W]ₚ₀ = [(0 : FiniteProjectiveGroupAlgebraModule k G)]ₚ₀ := by
              exact
                finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
                  (A := k) (G := G) ⟨hW_zero.isoZero⟩
            _ = 0 := finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := k) (G := G)
        rw [hWclass]
        exact S.zero_mem
  | n + 1, Q, hQ => by
      obtain ⟨Wtail, hWtail_equiv, hWtail_mem⟩ :=
        projective_fin_family_class_mem_submodule (S := S) (Q := fun i : Fin n ↦ Q i.succ)
          (fun i ↦ hQ i.succ)
      obtain ⟨W, hW_equiv, hW_class⟩ := projective_class_prod_eq_add (k := k) (G := G) (Q 0) Wtail
      refine ⟨W, ?_, ?_⟩
      · rcases hW_equiv with ⟨eW⟩
        rcases hWtail_equiv with ⟨eTail⟩
        -- First separate the head factor, then identify the tail with the inductive product.
        let eProd : W.V ≃ₗ[k[G]] ((Q 0).V × ((i : Fin n) → (Q i.succ).V)) :=
          eW.trans ((LinearEquiv.refl k[G] (Q 0).V).prodCongr eTail)
        let eFinal : W.V ≃ₗ[k[G]] ((i : Fin (n + 1)) → (Q i).V) :=
          eProd.trans (Fin.consLinearEquiv k[G] (fun i : Fin (n + 1) ↦ (Q i).V))
        exact ⟨eFinal⟩
      · -- Additivity of projective classes keeps the product owner inside `S`.
        rw [hW_class]
        exact S.add_mem (hQ 0) hWtail_mem

/-- Helper for Corollary 14-14.3-3: if a finite projective has simple top, then completeness of
the simple family places its Grothendieck class in the span of the chosen envelope classes. -/
private theorem projective_class_mem_span_of_simple_top
    (π : ι → FDRep k G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (Q : FiniteProjectiveGroupAlgebraModule k G)
    [IsSimpleModule k[G] (Q.V ⧸ Module.jacobson k[G] Q.V)] :
    [Q]ₚ₀ ∈ Submodule.span ℤ (Set.range fun i ↦ [P i]ₚ₀) := by
  classical
  let M : Type u := Q.V ⧸ Module.jacobson k[G] Q.V
  let _ : Module.Finite k M := largestSemisimpleQuotient_moduleFinite (k := k) (G := G) Q
  let τ : Representation k G M := Representation.ofModule' (k := k) (G := G) M
  have hτ_irred : τ.IsIrreducible := by
    -- The simple top gives an irreducible representation after rebundling.
    simpa [τ, M] using
      ofModule'_isIrreducible_of_isSimpleModule (k := k) (G := G) M
  obtain ⟨i, hτi⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (K := k) (G := G) π hπ_complete τ hτ_irred
  obtain ⟨eτ⟩ :=
    nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso (k := k) (G := G) (FDRep.of τ) (π i) hτi
  obtain ⟨eM⟩ := nonempty_ofModule'_asModuleLinearEquiv (k := k) (G := G) M
  let ρπ : Representation k G (π i) := (π i).ρ
  let Mπ : Type u := asModule ρπ
  letI : AddCommGroup Mπ := ρπ.instAddCommGroupAsModule
  letI : Module k[G] Mπ := ρπ.instModuleMonoidAlgebraAsModule
  let eQuot : M ≃ₗ[k[G]] Mπ := by
    -- Transport the quotient module across the rebuilt representation and then into `π i`.
    simpa [τ, M] using eM.symm.trans eτ
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  let _ : IsArtinian k[G] Q.V := by infer_instance
  let qQ : Q.V →ₗ[k[G]] M := (Module.jacobson k[G] Q.V).mkQ
  have hqQ : qQ.IsProjectiveEnvelope := by
    -- The canonical Jacobson quotient map is the reference projective envelope of `Q`.
    simpa [qQ, M] using
      (show ((Module.jacobson k[G] Q.V).mkQ :
          Q.V →ₗ[k[G]] Q.V ⧸ Module.jacobson k[G] Q.V).IsProjectiveEnvelope
        from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
  let fP : (P i).V →ₗ[k[G]] Mπ := Classical.choose (hP_envelope i)
  have hfP : fP.IsProjectiveEnvelope := Classical.choose_spec (hP_envelope i)
  let fP' : (P i).V →ₗ[k[G]] M := eQuot.symm.toLinearMap.comp fP
  have hfP' : fP'.IsProjectiveEnvelope := by
    letI : fP'.IsEssential := by
      refine ⟨?_⟩
      intro N hN
      have hmap : (N.map fP).map eQuot.symm.toLinearMap = ⊤ := by
        simpa [fP', Submodule.map_comp] using hN
      have hNmap : N.map fP = ⊤ := by
        exact (Submodule.map_eq_top_iff (p := N.map fP) (e := eQuot.symm)).1 hmap
      exact hfP.toIsEssential.eq_top_of_map_eq_top N hNmap
    -- Surjectivity transports back across the target equivalence `eQuot`.
    refine LinearMap.IsProjectiveEnvelope.mk ?_
    intro y
    obtain ⟨x, hx⟩ := hfP.surjective (eQuot y)
    refine ⟨x, ?_⟩
    simpa [fP', hx]
  obtain ⟨eSrc, _⟩ := LinearMap.isProjectiveEnvelope_unique hqQ hfP'
  have hIso : Nonempty (Q ≅ P i) := by
    -- Two projective envelopes of the same simple top are isomorphic on their sources.
      exact
        (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
          (A := k) (G := G) Q (P i)).2 ⟨eSrc⟩
  -- After identifying `Q` with the chosen envelope `P i`, the class is one of the span
  -- generators.
  rw [finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
    (A := k) (G := G) hIso]
  exact Submodule.subset_span ⟨i, rfl⟩

-- Source/core/bridge triage:
-- * source-facing: linear independence for projective envelopes of a family of simple modules.
-- * core/canonical owner reused upstream in this chapter: `IsCompleteIrreducibleFamily π`.
-- * bridge/view used below: the basis theorem derives the primitive simplicity data from the
--   complete-family owner, but this linear-independence statement itself should only require the
--   primitive source data it actually uses.
-- Proof sketch: if a nontrivial integer relation among the projective-envelope classes existed,
-- Corollary `14-14.3-4` would force a corresponding isomorphism relation among finite direct sums
-- of the projective envelopes. Comparing largest semisimple quotients then yields an isomorphism
-- relation among finite direct sums of the pairwise nonisomorphic simples, so every coefficient
-- vanishes.
/-- For a pairwise nonisomorphic family of simple finite-dimensional `k[G]`-representations, the
classes of their projective envelopes are `ℤ`-linearly independent in `P_k(G)`. -/
theorem linearIndependent_projectiveEnvelope_classes_of_pairwise_nonisomorphic
    (π : ι → FDRep k G)
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    LinearIndependent ℤ (fun i ↦ [P i]ₚ₀) := by
  let f : P₀[k](G) →ₗ[ℤ] R₀[k](G) :=
    (largestSemisimpleQuotientHom (k := k) (G := G)).toIntLinearMap
  -- Push the envelope classes through the largest-semisimple-quotient map and compare with the
  -- already independent family of simple classes.
  refine LinearIndependent.of_comp (f := f) ?_
  convert
    linearIndependent_simple_finiteRep_classes_of_pairwise_nonisomorphic
      (L := k) (G := G) π hπ_simple hπ_pairwise using 1
  ext i
  simpa [f] using
    projectiveEnvelope_largestSemisimpleQuotientHom_projectiveClass_eq
      (k := k) (G := G) π hπ_simple P hP_envelope i

-- Proof sketch: every indecomposable finite projective `k[G]`-module is a projective envelope of
-- a simple finite-dimensional `k[G]`-module by Corollary `14-14.3-2`, and completeness of `π`
-- identifies that simple with some `π i`. Since duplicates do not change `Set.range`, the
-- projective-envelope classes span all of `P_k(G)` without any pairwise-nonisomorphism
-- assumption.
/-- For a complete family of simple finite-dimensional `k[G]`-representations, the classes of
their projective envelopes span `P_k(G)`. -/
theorem span_projectiveEnvelope_classes_eq_top_of_complete_family
    (π : ι → FDRep k G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    Submodule.span ℤ (Set.range fun i ↦ [P i]ₚ₀) = ⊤ := by
  classical
  let S : Submodule ℤ (P₀[k](G)) := Submodule.span ℤ (Set.range fun i ↦ [P i]ₚ₀)
  have hgenerator : ∀ Q : FiniteProjectiveGroupAlgebraModule k G, [Q]ₚ₀ ∈ S := by
    intro Q
    obtain ⟨κ, _, Qdec, eQ, hQdec⟩ :
        ∃ (κ : Type w) (_ : Finite κ) (Qdec : κ → ModuleCat k[G]) (_ : Q.V ≅ ⨁ Qdec),
          ∀ j, Module.Finite k[G] (Qdec j) ∧
            Module.Projective k[G] (Qdec j) ∧ Indecomposable (Qdec j) := by
      simpa using
        (finite_projective_module_exists_indecomposable_decomposition
          (k := k) (G := G) (M := Q.V))
    letI : Fintype κ := Fintype.ofFinite κ
    let n : ℕ := Fintype.card κ
    let eκ : κ ≃ Fin n := Fintype.equivFin κ
    let Qfin : Fin n → ModuleCat k[G] := fun j ↦ Qdec (eκ.symm j)
    have hQwhisker (j : κ) : Qfin (eκ j) ≅ Qdec j := by
      simpa [Qfin] using Iso.refl (Qdec j)
    let eQfin : Q.V ≅ ⨁ Qfin := eQ ≪≫ biproduct.whiskerEquiv eκ hQwhisker
    let Qproj : Fin n → FiniteProjectiveGroupAlgebraModule k G := fun j ↦
      ⟨⟨Qfin j, (hQdec (eκ.symm j)).1⟩, (hQdec (eκ.symm j)).2.1⟩
    have hQproj_mem : ∀ j, [Qproj j]ₚ₀ ∈ S := by
      intro j
      letI : Module.Finite k[G] (Qfin j) := (hQdec (eκ.symm j)).1
      letI : Module.Projective k[G] (Qfin j) := (hQdec (eκ.symm j)).2.1
      have hsimple :
          IsSimpleModule k[G] ((Qproj j).V ⧸ Module.jacobson k[G] (Qproj j).V) := by
        -- Indecomposable projective summands have simple largest semisimple quotient.
        simpa [Qproj, Qfin] using
          (indecomposable_projective_module_iff_simple_largestSemisimpleQuotient
            (k := k) (G := G) (P := Qfin j)).1
            ((hQdec (eκ.symm j)).2.2)
      letI :
          IsSimpleModule k[G] ((Qproj j).V ⧸ Module.jacobson k[G] (Qproj j).V) := hsimple
      simpa [S] using
        projective_class_mem_span_of_simple_top
          (k := k) (G := G) π hπ_complete P hP_envelope (Qproj j)
    obtain ⟨W, hW_equiv, hW_mem⟩ :=
      projective_fin_family_class_mem_submodule (k := k) (G := G) S Qproj hQproj_mem
    let eQpi : Q.V ≅ ModuleCat.of k[G] ((j : Fin n) → Qfin j) :=
      eQfin ≪≫ ModuleCat.biproductIsoPi Qfin
    rcases hW_equiv with ⟨eW⟩
    have hIso : Nonempty (Q ≅ W) := by
      -- Rebuild the decomposed finite family as one projective object and compare it with `Q`.
      refine
        (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
          (A := k) (G := G) Q W).2 ?_
      let eDec : ((j : Fin n) → Qfin j) ≃ₗ[k[G]] W.V := by
        simpa [Qproj, Qfin] using eW.symm
      exact ⟨eQpi.toLinearEquiv.trans eDec⟩
    rw [finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
      (A := k) (G := G) hIso]
    exact hW_mem
  -- Quotient induction reduces the top-span claim to the generator case above.
  refine top_unique ?_
  intro z hz
  refine QuotientAddGroup.induction_on z ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · exact Submodule.zero_mem S
  · intro Q
    simpa [S, finiteProjectiveGroupAlgebraGrothendieckClass] using hgenerator Q
  · intro a ha
    simpa [S] using Submodule.neg_mem S ha
  · intro a b ha hb
    simpa [S] using Submodule.add_mem S ha hb

/-- Corollary 14-14.3-3: for a finite group `G`, if `π` is a complete family of pairwise
nonisomorphic finite-dimensional simple `k[G]`-representations and `P i` is a projective
envelope of `π i`, then the classes `[P i]` form a `ℤ`-basis of LinearRepresentations_Serre_1977's projective Grothendieck
group `P_k(G)`. -/
def projectiveEnvelope_classes_basis_of_complete_family
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    Module.Basis ι ℤ (P₀[k](G)) :=
  Module.Basis.mk
    (linearIndependent_projectiveEnvelope_classes_of_pairwise_nonisomorphic
      π hπ_complete.isSimple hπ_pairwise P hP_envelope)
    (span_projectiveEnvelope_classes_eq_top_of_complete_family
      π hπ_complete P hP_envelope).ge

/-- Evaluating the projective-envelope basis from Corollary `14-14.3-3` at `i` returns the class
of `P i`. -/
@[simp] theorem projectiveEnvelope_classes_basis_of_complete_family_apply
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i : ι) :
    projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope i =
      [P i]ₚ₀ := by
  change
      Module.Basis.mk
          (linearIndependent_projectiveEnvelope_classes_of_pairwise_nonisomorphic
            π hπ_complete.isSimple hπ_pairwise P hP_envelope)
          (span_projectiveEnvelope_classes_eq_top_of_complete_family
            π hπ_complete P hP_envelope).ge i =
        (fun j ↦ [P j]ₚ₀) i
  exact
    Module.Basis.mk_apply
      (linearIndependent_projectiveEnvelope_classes_of_pairwise_nonisomorphic
        π hπ_complete.isSimple hπ_pairwise P hP_envelope)
      (span_projectiveEnvelope_classes_eq_top_of_complete_family
        π hπ_complete P hP_envelope).ge
      i

end ProjectiveGrothendieckGroup

end Representation
