import StacksProject_2024.Chap10.Lemma_10_134_12.Index
open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent TensorProduct

universe u v w

noncomputable section

section

variable (A : Type u) (B : Type v) (Bg : Type v)
variable [CommRing A] [CommRing B] [CommRing Bg]
variable [Algebra A B] [Algebra A Bg] [Algebra B Bg]
variable [IsScalarTower A B Bg]
variable (g : B) [IsLocalization.Away g Bg]

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] TensorProduct.rightAlgebra


/-- Helper for Lemma 10.134.12: the two degree-`0` basis maps compose to the identity on the
reindexed localization-away cotangent-space term. -/
private theorem localizationAway_reindex_cotangentSpace_left_comp :
    (localizationAway_reindex_cotangentSpace_backward B Bg g) ∘ₗ
        (localizationAway_reindex_cotangentSpace_forward B Bg g) =
      LinearMap.id := by
  -- Both maps are defined by the unique basis vector, so it is enough to compare that vector.
  let b := (localizationAwayGenerators B Bg g).cotangentSpaceBasis
  apply b.ext
  intro i
  cases i
  rw [LinearMap.comp_apply]
  rw [localizationAway_reindex_cotangentSpace_forward,
    localizationAway_reindex_cotangentSpace_backward]
  rw [Module.Basis.constr_basis, Module.Basis.constr_basis]
  rfl

/-- Helper for Lemma 10.134.12: the two degree-`0` basis maps compose to the identity on the
standard localization-away cotangent-space term. -/
private theorem localizationAway_reindex_cotangentSpace_right_comp :
    (localizationAway_reindex_cotangentSpace_forward B Bg g) ∘ₗ
        (localizationAway_reindex_cotangentSpace_backward B Bg g) =
      LinearMap.id := by
  -- The same rank-one basis computation proves the reverse composite.
  let b := (Generators.localizationAway Bg g).cotangentSpaceBasis
  apply b.ext
  intro i
  cases i
  rw [LinearMap.comp_apply]
  rw [localizationAway_reindex_cotangentSpace_forward,
    localizationAway_reindex_cotangentSpace_backward]
  rw [Module.Basis.constr_basis, Module.Basis.constr_basis]
  rfl

/-- Helper for Lemma 10.134.12: the degree-`0` terms of the reindexed and standard
localization-away presentations are canonically equivalent by matching their unique basis
vectors. -/
private noncomputable def localizationAway_reindex_cotangentSpace_equiv :
    (localizationAwayGenerators B Bg g).toExtension.CotangentSpace ≃ₗ[Bg]
      (Generators.localizationAway Bg g).toExtension.CotangentSpace :=
  -- Package the two inverse basis maps as the degree-`0` linear equivalence.
  LinearEquiv.ofLinear
    (localizationAway_reindex_cotangentSpace_forward B Bg g)
    (localizationAway_reindex_cotangentSpace_backward B Bg g)
    (localizationAway_reindex_cotangentSpace_right_comp B Bg g)
    (localizationAway_reindex_cotangentSpace_left_comp B Bg g)

/-- Helper for Lemma 10.134.12: the polynomial-renaming hom from the `ULift`-reindexed
localization-away presentation to the standard one. -/
private noncomputable def localizationAway_reindex_hom :
    (localizationAwayGenerators B Bg g).Hom (Generators.localizationAway Bg g) where
  val i := MvPolynomial.X i.down
  aeval_val i := by
    -- The reindexed generator has the same value as the standard generator after lowering `ULift`.
    cases i
    simp [localizationAwayGenerators, Generators.reindex]

/-- Helper for Lemma 10.134.12: the inverse polynomial-renaming hom from the standard
localization-away presentation to the `ULift`-reindexed one. -/
private noncomputable def localizationAway_reindex_invHom :
    (Generators.localizationAway Bg g).Hom (localizationAwayGenerators B Bg g) where
  val i := MvPolynomial.X (ULift.up i)
  aeval_val i := by
    -- Raising the unique variable gives the inverse reindexing of the same generator.
    cases i
    simp [localizationAwayGenerators, Generators.reindex]

/-- Helper for Lemma 10.134.12: the inverse reindex hom followed by the forward reindex hom is the
identity on the `ULift`-reindexed localization-away presentation. -/
private theorem localizationAway_reindex_invHom_comp_hom :
    (localizationAway_reindex_invHom B Bg g).comp (localizationAway_reindex_hom B Bg g) =
      Generators.Hom.id (localizationAwayGenerators B Bg g) := by
  -- It is enough to check the unique variable, where the two renamings cancel.
  ext i
  cases i
  simp [localizationAway_reindex_hom, localizationAway_reindex_invHom]

/-- Helper for Lemma 10.134.12: the forward reindex hom followed by the inverse reindex hom is the
identity on the standard localization-away presentation. -/
private theorem localizationAway_reindex_hom_comp_invHom :
    (localizationAway_reindex_hom B Bg g).comp (localizationAway_reindex_invHom B Bg g) =
      Generators.Hom.id (Generators.localizationAway Bg g) := by
  -- The standard presentation also has a single variable, and lowering after raising is trivial.
  ext i
  cases i
  simp [localizationAway_reindex_hom, localizationAway_reindex_invHom]

/-- Helper for Lemma 10.134.12: the induced conormal maps compose to the identity on the
`ULift`-reindexed localization-away conormal term. -/
private theorem localizationAway_reindex_cotangent_left_comp :
    Extension.Cotangent.map ((localizationAway_reindex_invHom B Bg g).toExtensionHom) ∘ₗ
        Extension.Cotangent.map ((localizationAway_reindex_hom B Bg g).toExtensionHom) =
      LinearMap.id := by
  -- Functoriality of `Extension.Cotangent.map` reduces the conormal composite to the generator
  -- hom composite just proved.
  have hmap :
      Extension.Cotangent.map
          (((localizationAway_reindex_invHom B Bg g).comp
            (localizationAway_reindex_hom B Bg g)).toExtensionHom) =
        Extension.Cotangent.map ((localizationAway_reindex_invHom B Bg g).toExtensionHom) ∘ₗ
          Extension.Cotangent.map ((localizationAway_reindex_hom B Bg g).toExtensionHom) := by
    rw [Generators.Hom.toExtensionHom_comp]
    rw [Extension.Cotangent.map_comp]
    rfl
  rw [← hmap]
  rw [localizationAway_reindex_invHom_comp_hom]
  rw [Generators.Hom.toExtensionHom_id, Extension.Cotangent.map_id]

/-- Helper for Lemma 10.134.12: the induced conormal maps compose to the identity on the standard
localization-away conormal term. -/
private theorem localizationAway_reindex_cotangent_right_comp :
    Extension.Cotangent.map ((localizationAway_reindex_hom B Bg g).toExtensionHom) ∘ₗ
        Extension.Cotangent.map ((localizationAway_reindex_invHom B Bg g).toExtensionHom) =
      LinearMap.id := by
  -- The reverse conormal composite is controlled by the reverse generator-hom composite.
  have hmap :
      Extension.Cotangent.map
          (((localizationAway_reindex_hom B Bg g).comp
            (localizationAway_reindex_invHom B Bg g)).toExtensionHom) =
        Extension.Cotangent.map ((localizationAway_reindex_hom B Bg g).toExtensionHom) ∘ₗ
          Extension.Cotangent.map ((localizationAway_reindex_invHom B Bg g).toExtensionHom) := by
    rw [Generators.Hom.toExtensionHom_comp]
    rw [Extension.Cotangent.map_comp]
    rfl
  rw [← hmap]
  rw [localizationAway_reindex_hom_comp_invHom]
  rw [Generators.Hom.toExtensionHom_id, Extension.Cotangent.map_id]

/-- Helper for Lemma 10.134.12: the `ULift` reindex on the localization-away presentation also
identifies the conormal term once both presentations are recognized as localizations. -/
private noncomputable def localizationAway_reindex_cotangent_equiv :
    (localizationAwayGenerators B Bg g).toExtension.Cotangent ≃ₗ[Bg]
      (Generators.localizationAway Bg g).toExtension.Cotangent :=
  -- Apply the two inverse polynomial-renaming homs to conormal modules and package functoriality.
  LinearEquiv.ofLinear
    (Extension.Cotangent.map ((localizationAway_reindex_hom B Bg g).toExtensionHom))
    (Extension.Cotangent.map ((localizationAway_reindex_invHom B Bg g).toExtensionHom))
    (localizationAway_reindex_cotangent_right_comp B Bg g)
    (localizationAway_reindex_cotangent_left_comp B Bg g)

/-- Helper for Lemma 10.134.12: the cotangent-space map induced by the reindex hom is the
rank-one basis map used in degree `0`. -/
private theorem localizationAway_reindex_cotangentSpace_map_hom :
    Extension.CotangentSpace.map ((localizationAway_reindex_hom B Bg g).toExtensionHom) =
      localizationAway_reindex_cotangentSpace_forward B Bg g := by
  -- Compare the maps on the unique basis vector, then compare the image in the target basis.
  let b := (localizationAwayGenerators B Bg g).cotangentSpaceBasis
  apply b.ext
  intro i
  cases i
  apply (Generators.localizationAway Bg g).cotangentSpaceBasis.repr.injective
  apply Finsupp.ext
  intro j
  cases j
  rw [Generators.repr_CotangentSpaceMap]
  rw [localizationAway_reindex_cotangentSpace_forward]
  rw [Module.Basis.constr_basis]
  rw [Module.Basis.repr_self_apply]
  simp [localizationAway_reindex_hom]

/-- Helper for Lemma 10.134.12: the lifted conormal-term equivalence induced by the `ULift`
reindex. -/
private noncomputable def localizationAway_reindex_degree1_linearEquiv :
    ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) ≃ₗ[Bg]
      ((Generators.localizationAway Bg g).toExtension.naiveCotangentChainComplex.X 1) := by
  -- Degree `1` is the `ULift` of the conormal module, so lift the conormal reindex equivalence.
  simpa [Extension.naiveCotangentChainComplex] using
    (ULift.moduleEquiv.trans
      ((localizationAway_reindex_cotangent_equiv B Bg g).trans ULift.moduleEquiv.symm))

/-- Helper for Lemma 10.134.12: the `ULift` reindex on the localization-away presentation and the
standard presentation have canonically identified degree-`0` terms. -/
private noncomputable def localizationAway_reindex_degree0_iso :
    ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 0) ≅
      ((Generators.localizationAway Bg g).toExtension.naiveCotangentChainComplex.X 0) :=
  (localizationAway_reindex_cotangentSpace_equiv B Bg g).toModuleIso

/-- Helper for Lemma 10.134.12: the degree-`1` and degree-`0` identifications for the `ULift`
reindex intertwine the localization-away differential. -/
private theorem localizationAway_reindex_cotangent_equiv_comm :
    ((Generators.localizationAway Bg g).toExtension.cotangentComplex) ∘ₗ
        (localizationAway_reindex_cotangent_equiv B Bg g).toLinearMap =
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap) ∘ₗ
        ((localizationAwayGenerators B Bg g).toExtension.cotangentComplex) := by
  -- Naturality of the cotangent complex for the reindex hom gives the square; the degree-`0`
  -- side is exactly the basis map packaged above.
  have hspace := localizationAway_reindex_cotangentSpace_map_hom B Bg g
  have hcomm :=
    Extension.CotangentSpace.map_comp_cotangentComplex
      ((localizationAway_reindex_hom B Bg g).toExtensionHom)
  have hspaceEquiv :
      (localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap =
        Extension.CotangentSpace.map ((localizationAway_reindex_hom B Bg g).toExtensionHom) := by
    simpa [localizationAway_reindex_cotangentSpace_equiv] using hspace.symm
  have hcotangentEquiv :
      (localizationAway_reindex_cotangent_equiv B Bg g).toLinearMap =
        Extension.Cotangent.map ((localizationAway_reindex_hom B Bg g).toExtensionHom) := by
    rfl
  rw [hspaceEquiv, hcotangentEquiv]
  simpa using hcomm.symm

/-- Helper for Lemma 10.134.12: objectwise biproduct coordinates send the chain-level left
inclusion to the ordinary left product coordinate. -/
private theorem biprodXIso_biprodIsoProd_hom_inl_apply
    (X Y : ChainComplex (ModuleCat Bg) ℕ) (n : ℕ) (x : X.X n) :
    ((ModuleCat.biprodIsoProd (X.X n) (Y.X n)).hom.hom)
      ((HomologicalComplex.biprodXIso X Y n).hom.hom
        (((biprod.inl : X ⟶ X ⊞ Y).f n).hom x)) =
    (x, 0) := by
  -- First pass through the chain-level objectwise biproduct comparison, then use the explicit
  -- `ModuleCat` product comparison.
  have h :
      (biprod.inl : X ⟶ X ⊞ Y).f n ≫ (HomologicalComplex.biprodXIso X Y n).hom =
        (biprod.inl : X.X n ⟶ X.X n ⊞ Y.X n) := by
    rw [← HomologicalComplex.inl_biprodXIso_inv_assoc X Y n
      (HomologicalComplex.biprodXIso X Y n).hom]
    simp
  rw [← LinearMap.comp_apply]
  change
    (((((biprod.inl : X ⟶ X ⊞ Y).f n ≫
          (HomologicalComplex.biprodXIso X Y n).hom) ≫
        (ModuleCat.biprodIsoProd (X.X n) (Y.X n)).hom).hom) x) = (x, 0)
  rw [h]
  exact @biprodIsoProd_hom_inl_apply _ _ (X.X n) (Y.X n) x

/-- Helper for Lemma 10.134.12: after the objectwise biproduct and product comparisons, the
differential of a chain-complex biproduct is computed componentwise. -/
private theorem biprodXIso_biprodIsoProd_d_apply
    (X Y : ChainComplex (ModuleCat Bg) ℕ) (i j : ℕ)
    (x : (X ⊞ Y).X i) :
    let xi :=
      ((ModuleCat.biprodIsoProd (X.X i) (Y.X i)).hom.hom)
        ((HomologicalComplex.biprodXIso X Y i).hom.hom x)
    ((ModuleCat.biprodIsoProd (X.X j) (Y.X j)).hom.hom)
        ((HomologicalComplex.biprodXIso X Y j).hom.hom (((X ⊞ Y).d i j).hom x)) =
      (((X.d i j).hom xi.1), ((Y.d i j).hom xi.2)) := by
  -- Compare the two product coordinates by composing with the objectwise projections; the chain
  -- map identities for `biprod.fst` and `biprod.snd` give the two component formulas.
  dsimp
  have hfst (k : ℕ) :
      (HomologicalComplex.biprodXIso X Y k).hom ≫
          (ModuleCat.biprodIsoProd (X.X k) (Y.X k)).hom ≫
            ModuleCat.ofHom (LinearMap.fst Bg (X.X k) (Y.X k)) =
        (biprod.fst : X ⊞ Y ⟶ X).f k := by
    simpa [Category.assoc, biprodIsoProd_hom_comp_fst] using
      HomologicalComplex.biprodXIso_hom_fst X Y k
  have hsnd (k : ℕ) :
      (HomologicalComplex.biprodXIso X Y k).hom ≫
          (ModuleCat.biprodIsoProd (X.X k) (Y.X k)).hom ≫
            ModuleCat.ofHom (LinearMap.snd Bg (X.X k) (Y.X k)) =
        (biprod.snd : X ⊞ Y ⟶ Y).f k := by
    simpa [Category.assoc, biprodIsoProd_hom_comp_snd] using
      HomologicalComplex.biprodXIso_hom_snd X Y k
  apply Prod.ext
  · have hmorph :
        (X ⊞ Y).d i j ≫ (HomologicalComplex.biprodXIso X Y j).hom ≫
            (ModuleCat.biprodIsoProd (X.X j) (Y.X j)).hom ≫
              ModuleCat.ofHom (LinearMap.fst Bg (X.X j) (Y.X j)) =
          (HomologicalComplex.biprodXIso X Y i).hom ≫
            (ModuleCat.biprodIsoProd (X.X i) (Y.X i)).hom ≫
              ModuleCat.ofHom (LinearMap.fst Bg (X.X i) (Y.X i)) ≫ X.d i j := by
      calc
        (X ⊞ Y).d i j ≫ (HomologicalComplex.biprodXIso X Y j).hom ≫
            (ModuleCat.biprodIsoProd (X.X j) (Y.X j)).hom ≫
              ModuleCat.ofHom (LinearMap.fst Bg (X.X j) (Y.X j)) =
            (X ⊞ Y).d i j ≫ (biprod.fst : X ⊞ Y ⟶ X).f j := by
              rw [hfst]
        _ = (biprod.fst : X ⊞ Y ⟶ X).f i ≫ X.d i j := by
              rw [← (biprod.fst : X ⊞ Y ⟶ X).comm i j]
        _ = (HomologicalComplex.biprodXIso X Y i).hom ≫
            (ModuleCat.biprodIsoProd (X.X i) (Y.X i)).hom ≫
              ModuleCat.ofHom (LinearMap.fst Bg (X.X i) (Y.X i)) ≫ X.d i j := by
              simpa [Category.assoc] using congrArg (fun f ↦ f ≫ X.d i j) (hfst i).symm
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun f : (X ⊞ Y).X i ⟶ X.X j ↦ f.hom x) hmorph
  · have hmorph :
        (X ⊞ Y).d i j ≫ (HomologicalComplex.biprodXIso X Y j).hom ≫
            (ModuleCat.biprodIsoProd (X.X j) (Y.X j)).hom ≫
              ModuleCat.ofHom (LinearMap.snd Bg (X.X j) (Y.X j)) =
          (HomologicalComplex.biprodXIso X Y i).hom ≫
            (ModuleCat.biprodIsoProd (X.X i) (Y.X i)).hom ≫
              ModuleCat.ofHom (LinearMap.snd Bg (X.X i) (Y.X i)) ≫ Y.d i j := by
      calc
        (X ⊞ Y).d i j ≫ (HomologicalComplex.biprodXIso X Y j).hom ≫
            (ModuleCat.biprodIsoProd (X.X j) (Y.X j)).hom ≫
              ModuleCat.ofHom (LinearMap.snd Bg (X.X j) (Y.X j)) =
            (X ⊞ Y).d i j ≫ (biprod.snd : X ⊞ Y ⟶ Y).f j := by
              rw [hsnd]
        _ = (biprod.snd : X ⊞ Y ⟶ Y).f i ≫ Y.d i j := by
              rw [← (biprod.snd : X ⊞ Y ⟶ Y).comm i j]
        _ = (HomologicalComplex.biprodXIso X Y i).hom ≫
            (ModuleCat.biprodIsoProd (X.X i) (Y.X i)).hom ≫
              ModuleCat.ofHom (LinearMap.snd Bg (X.X i) (Y.X i)) ≫ Y.d i j := by
              simpa [Category.assoc] using congrArg (fun f ↦ f ≫ Y.d i j) (hsnd i).symm
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun f : (X ⊞ Y).X i ⟶ Y.X j ↦ f.hom x) hmorph

omit [Algebra A Bg] [IsScalarTower A B Bg] in
/-- Helper for Lemma 10.134.12: every degree `n + 2` term of the source biproduct complex is
subsingleton, because both summands already have zero tails. -/
private theorem localizedSelfPresentation_source_X_succ_succ_subsingleton
    (n : ℕ) :
    Subsingleton
      ((tensorNaiveCotangentAwayModel A B Bg ⊞
          (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X
        (n + 2)) := by
  -- Identify the component of the chain-complex biproduct with the ordinary module biproduct.
  let X := tensorNaiveCotangentAwayModel A B Bg
  let Y := (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex
  letI : Subsingleton (X.X (n + 2)) :=
    tensorNaiveCotangentAwayModel_X_succ_succ_subsingleton A B Bg n
  letI : Subsingleton (Y.X (n + 2)) :=
    localizationAway_reindex_X_succ_succ_subsingleton B Bg g n
  refine ⟨fun x y ↦ ?_⟩
  let e₁ := HomologicalComplex.biprodXIso X Y (n + 2)
  let e₂ := ModuleCat.biprodIsoProd (X.X (n + 2)) (Y.X (n + 2))
  have hprod : e₂.hom.hom (e₁.hom.hom x) = e₂.hom.hom (e₁.hom.hom y) := by
    ext <;> exact Subsingleton.elim _ _
  have hbiprod : e₁.hom.hom x = e₁.hom.hom y := by
    calc
      e₁.hom.hom x = e₂.inv.hom (e₂.hom.hom (e₁.hom.hom x)) := by
        simpa using congrArg
          (fun f : X.X (n + 2) ⊞ Y.X (n + 2) ⟶
              X.X (n + 2) ⊞ Y.X (n + 2) ↦ f.hom (e₁.hom.hom x))
          e₂.hom_inv_id.symm
      _ = e₂.inv.hom (e₂.hom.hom (e₁.hom.hom y)) := by rw [hprod]
      _ = e₁.hom.hom y := by
        simpa using congrArg
          (fun f : X.X (n + 2) ⊞ Y.X (n + 2) ⟶
              X.X (n + 2) ⊞ Y.X (n + 2) ↦ f.hom (e₁.hom.hom y))
          e₂.hom_inv_id
  calc
    x = e₁.inv.hom (e₁.hom.hom x) := by
      simpa using congrArg
        (fun f : (X ⊞ Y).X (n + 2) ⟶ (X ⊞ Y).X (n + 2) ↦ f.hom x)
        e₁.hom_inv_id.symm
    _ = e₁.inv.hom (e₁.hom.hom y) := by rw [hbiprod]
    _ = y := by
      simpa using congrArg
        (fun f : (X ⊞ Y).X (n + 2) ⟶ (X ⊞ Y).X (n + 2) ↦ f.hom y)
        e₁.hom_inv_id

/-- Helper for Lemma 10.134.12: the degree-`0` source product maps to the localized
self-presentation degree-`0` term through the normalized product splitting. -/
private noncomputable def localizedSelfPresentationDegree0ProductEquiv :
    (Bg ⊗[B] (selfExtension A B).CotangentSpace ×
        (localizationAwayGenerators B Bg g).toExtension.CotangentSpace) ≃ₗ[Bg]
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X 0 :=
  -- Keep the public surface in chain-component coordinates; the body is the source-proof
  -- product ordering, reindex, shear, and Jacobi-Zariski cotangent-space split.
  (LinearEquiv.prodComm Bg
      (Bg ⊗[B] (selfExtension A B).CotangentSpace)
      (localizationAwayGenerators B Bg g).toExtension.CotangentSpace).trans
    ((LinearEquiv.prodCongr
        (localizationAway_reindex_cotangentSpace_equiv B Bg g)
        (LinearEquiv.refl Bg (Bg ⊗[B] (selfExtension A B).CotangentSpace))).trans
      ((localized_self_degree0_shear_equiv_on_product A B Bg g).symm.trans
        (CotangentSpace.compEquiv
          (Generators.localizationAway Bg g) (Generators.self A B)).symm))

/-- Helper for Lemma 10.134.12: applying the Jacobi-Zariski cotangent-space splitting after the
degree-`0` product equivalence gives the reindexed localization coordinate and the sheared tensor
coordinate. -/
private theorem localizedSelfPresentationDegree0ProductEquiv_compEquiv_apply
    (z : Bg ⊗[B] (selfExtension A B).CotangentSpace ×
        (localizationAwayGenerators B Bg g).toExtension.CotangentSpace) :
    CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((localizedSelfPresentationDegree0ProductEquiv A B Bg g).toLinearMap z) =
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap z.2,
        z.1 +
          localized_self_degree0_shear A B Bg g
          ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap z.2)) := by
  -- Stay in the owner product coordinates: the equivalence is product-commute, reindex,
  -- inverse shear, and then the inverse cotangent-space splitting.
  simp only [localizedSelfPresentationDegree0ProductEquiv, LinearEquiv.trans_apply,
    LinearEquiv.prodComm_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    localized_self_degree0_shear_equiv_on_product_symm_apply, LinearEquiv.coe_coe]
  exact LinearEquiv.apply_symm_apply
    (CotangentSpace.compEquiv (Generators.localizationAway Bg g) (Generators.self A B)) _

/-- Helper for Chap10 Lemma 10 134 12: after applying the degree-`0` shear, the localized
self-presentation product coordinates are exactly the localization and tensor coordinates. -/
private theorem localizedSelfPresentationDegree0ProductEquiv_normalized_apply
    (z : Bg ⊗[B] (selfExtension A B).CotangentSpace ×
        (localizationAwayGenerators B Bg g).toExtension.CotangentSpace) :
    localized_self_degree0_shear_equiv_on_product A B Bg g
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((localizedSelfPresentationDegree0ProductEquiv A B Bg g).toLinearMap z)) =
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap z.2, z.1) := by
  -- The shear was chosen to remove exactly the tensor correction term in the product splitting.
  rw [localizedSelfPresentationDegree0ProductEquiv_compEquiv_apply]
  rw [localized_self_degree0_shear_equiv_on_product_apply]
  ext <;> simp

/-- Helper for Chap10 Lemma 10 134 12: the coerced `LinearEquiv` spelling produced by
`LinearEquiv.toModuleIso` has normalized degree-`0` coordinates on the left tensor summand. -/
private theorem localizedSelfPresentationDegree0ProductEquiv_coeOfHom_compEquiv_chain_left_apply
    (x : (tensorNaiveCotangentAwayModel A B Bg).X 0) :
    CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((ModuleCat.Hom.hom
          (ModuleCat.ofHom
            (localizedSelfPresentationDegree0ProductEquiv A B Bg g :
              (Bg ⊗[B] (selfExtension A B).CotangentSpace ×
                (localizationAwayGenerators B Bg g).toExtension.CotangentSpace) →ₗ[Bg]
                (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X 0)))
          (x, 0)) =
      (0, x) := by
  -- This matches the exact coerced-linear-map spelling left by `LinearEquiv.toModuleIso_hom`.
  rw [ModuleCat.hom_ofHom]
  refine
    (LinearEquiv.injective
      (localized_self_degree0_shear_equiv_on_product A B Bg g)) ?_
  rw [localizedSelfPresentationDegree0ProductEquiv_normalized_apply]
  simp [localized_self_degree0_shear_equiv_on_product_apply]

/-- Helper for Chap10 Lemma 10 134 12: the coerced `ModuleCat.ofHom` form of the degree-`0`
product equivalence sends the left tensor coordinate to the base-changed comparison map. -/
private theorem localizedSelfPresentationDegree0ProductEquiv_coeOfHom_left_apply
    (x : (tensorNaiveCotangentAwayModel A B Bg).X 0) :
    (ModuleCat.Hom.hom
      (ModuleCat.ofHom
        (localizedSelfPresentationDegree0ProductEquiv A B Bg g :
          (Bg ⊗[B] (selfExtension A B).CotangentSpace ×
            (localizationAwayGenerators B Bg g).toExtension.CotangentSpace) →ₗ[Bg]
            (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X 0)))
      (x, 0) =
      (LinearMap.liftBaseChange Bg
        (Extension.CotangentSpace.map ((Generators.localizationAway Bg g).toComp
          (Generators.self A B)).toExtensionHom)) x := by
  -- Compare after the cotangent-space split and then use the already normalized product
  -- coordinates for this exact coerced-map spelling.
  refine
    (LinearEquiv.injective
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g) (Generators.self A B))) ?_
  rw [localized_self_compEquiv_apply_map_toComp]
  rw [ModuleCat.hom_ofHom]
  refine
    (LinearEquiv.injective
      (localized_self_degree0_shear_equiv_on_product A B Bg g)) ?_
  rw [localizedSelfPresentationDegree0ProductEquiv_normalized_apply]
  simp [localized_self_degree0_shear_equiv_on_product_apply]

/-- Helper for Lemma 10.134.12: the degree-`0` component of the canonical biproduct split for the
localized self-presentation. -/
private noncomputable def localizedSelfPresentation_biprod_XIso_zero :
    (tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X 0 ≅
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X 0 :=
  let X := tensorNaiveCotangentAwayModel A B Bg
  let Y := (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex
  HomologicalComplex.biprodXIso X Y 0 ≪≫
    ModuleCat.biprodIsoProd (X.X 0) (Y.X 0) ≪≫
      LinearEquiv.toModuleIso (localizedSelfPresentationDegree0ProductEquiv A B Bg g)

/-- Helper for Chap10 Lemma 10 134 12: explicit formula for the degree-`0` biproduct component
of the localized self-presentation split. -/
private theorem localizedSelfPresentation_biprod_XIso_zero_def :
    localizedSelfPresentation_biprod_XIso_zero A B Bg g =
      let X := tensorNaiveCotangentAwayModel A B Bg
      let Y := (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex
      HomologicalComplex.biprodXIso X Y 0 ≪≫
        ModuleCat.biprodIsoProd (X.X 0) (Y.X 0) ≪≫
          LinearEquiv.toModuleIso (localizedSelfPresentationDegree0ProductEquiv A B Bg g) := by
  rfl

/-- Helper for Chap10 Lemma 10 134 12: the degree-`0` component hom of the biproduct split is the
named composite through `biprodXIso`, `biprodIsoProd`, and the normalized product equivalence. -/
private theorem localizedSelfPresentation_biprod_XIso_zero_hom_eq :
    (localizedSelfPresentation_biprod_XIso_zero A B Bg g).hom =
      (HomologicalComplex.biprodXIso
          (tensorNaiveCotangentAwayModel A B Bg)
          ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
          0).hom ≫
        (ModuleCat.biprodIsoProd
          ((tensorNaiveCotangentAwayModel A B Bg).X 0)
          ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 0)).hom ≫
        (LinearEquiv.toModuleIso (localizedSelfPresentationDegree0ProductEquiv A B Bg g)).hom := by
  -- This is the morphism-level form of the degree-`0` component definition, used to avoid
  -- recursive wrapper reduction when evaluating the map on an element.
  rw [localizedSelfPresentation_biprod_XIso_zero_def]
  rfl

/-- Helper for Lemma 10.134.12: the degree-`1` source product maps to the localized
self-presentation degree-`1` term through the normalized conormal splitting. -/
private noncomputable def localizedSelfPresentationDegree1ProductEquiv :
    ((tensorNaiveCotangentAwayModel A B Bg).X 1 ×
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) ≃ₗ[Bg]
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X 1 :=
  -- Degree `1` uses the conormal splitting and keeps the `ULift` normalization inside this
  -- product-coordinate equivalence.
  (LinearEquiv.prodCongr
      (LinearEquiv.refl Bg (Bg ⊗[B] (selfExtension A B).Cotangent))
      ((localizationAway_reindex_degree1_linearEquiv B Bg g).trans ULift.moduleEquiv)).trans
    (((cotangentCompLocalizationAwayEquiv g (Generators.self A B)
        (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm).trans
      ULift.moduleEquiv.symm)

omit [Algebra A Bg] [IsScalarTower A B Bg] in
/-- Helper for Chap10 Lemma 10 134 12: every degree-`1` product input splits into its tensor and
localization coordinates. -/
private theorem localizedSelfPresentationDegree1Product_split
    (z : (tensorNaiveCotangentAwayModel A B Bg).X 1 ×
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    z = (z.1, 0) + (0, z.2) := by
  -- This is the additive decomposition used to normalize the unique `1 → 0` square.
  ext <;> simp

/-- Helper for Lemma 10.134.12: the degree-`1` component of the canonical biproduct split for the
localized self-presentation. -/
private noncomputable def localizedSelfPresentation_biprod_XIso_one :
    (tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X 1 ≅
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X 1 :=
  let X := tensorNaiveCotangentAwayModel A B Bg
  let Y := (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex
  HomologicalComplex.biprodXIso X Y 1 ≪≫
    ModuleCat.biprodIsoProd (X.X 1) (Y.X 1) ≪≫
      LinearEquiv.toModuleIso (localizedSelfPresentationDegree1ProductEquiv A B Bg g)

/-- Helper for Chap10 Lemma 10 134 12: explicit formula for the degree-`1` biproduct component
of the localized self-presentation split. -/
private theorem localizedSelfPresentation_biprod_XIso_one_def :
    localizedSelfPresentation_biprod_XIso_one A B Bg g =
      let X := tensorNaiveCotangentAwayModel A B Bg
      let Y := (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex
      HomologicalComplex.biprodXIso X Y 1 ≪≫
        ModuleCat.biprodIsoProd (X.X 1) (Y.X 1) ≪≫
          LinearEquiv.toModuleIso (localizedSelfPresentationDegree1ProductEquiv A B Bg g) := by
  rfl

/-- Helper for Chap10 Lemma 10 134 12: a biproduct component followed by a product-valued
linear equivalence evaluates as the corresponding `ModuleCat.ofHom` map on product coordinates. -/
private theorem moduleCat_biprodProductLinearEquiv_hom_apply
    {M X Y Z : ModuleCat Bg} (e : M ≅ X ⊞ Y) (L : (X × Y) ≃ₗ[Bg] Z)
    (z : M) :
    ((e ≪≫ ModuleCat.biprodIsoProd X Y ≪≫ LinearEquiv.toModuleIso L).hom.hom) z =
      (ModuleCat.Hom.hom (ModuleCat.ofHom (L : (X × Y) →ₗ[Bg] Z)))
        (((ModuleCat.biprodIsoProd X Y).hom.hom) (e.hom.hom z)) := by
  -- Evaluate the categorical composite once, then read the final component as `ModuleCat.ofHom`.
  rw [Iso.trans_hom, Iso.trans_hom]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]

/-- Helper for Chap10 Lemma 10 134 12: the degree-`0` component of the biproduct split is the
explicit product-coordinate map obtained from `biprodXIso`, `biprodIsoProd`, and the normalized
degree-`0` product equivalence. -/
private theorem localizedSelfPresentation_biprod_XIso_zero_apply_eq_product
    (z : (tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X 0) :
    ((localizedSelfPresentation_biprod_XIso_zero A B Bg g).hom.hom) z =
      (ModuleCat.Hom.hom
        (ModuleCat.ofHom
          ((localizedSelfPresentationDegree0ProductEquiv A B Bg g).toLinearMap)))
        (((ModuleCat.biprodIsoProd
            ((tensorNaiveCotangentAwayModel A B Bg).X 0)
            ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 0)).hom.hom)
          (((HomologicalComplex.biprodXIso
              (tensorNaiveCotangentAwayModel A B Bg)
              ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
              0).hom.hom) z)) := by
  -- Route correction: rewrite only the named component definition, then hand the resulting goal
  -- to the generic biproduct/product evaluator instead of closing by reflexivity.
  rw [localizedSelfPresentation_biprod_XIso_zero_hom_eq]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [ModuleCat.hom_ofHom]
  rfl

/-- Helper for Chap10 Lemma 10 134 12: the degree-`0` biproduct split sends the left inclusion
to the explicit left product coordinate. -/
private theorem localizedSelfPresentation_biprod_XIso_zero_hom_inl_eq_product_apply
    (x : (tensorNaiveCotangentAwayModel A B Bg).X 0) :
    ((localizedSelfPresentation_biprod_XIso_zero A B Bg g).hom.hom)
      (((biprod.inl :
        tensorNaiveCotangentAwayModel A B Bg ⟶
          tensorNaiveCotangentAwayModel A B Bg ⊞
            (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).f 0).hom x) =
      (LinearMap.liftBaseChange Bg
        (Extension.CotangentSpace.map ((Generators.localizationAway Bg g).toComp
          (Generators.self A B)).toExtensionHom)) x := by
  -- Route correction: rewrite the degree-`0` component once to stable product coordinates, so the
  -- left inclusion becomes `(x, 0)` and the remaining comparison is the dedicated owner lemma.
  rw [localizedSelfPresentation_biprod_XIso_zero_apply_eq_product]
  rw [biprodXIso_biprodIsoProd_hom_inl_apply]
  rw [ModuleCat.hom_ofHom]
  exact localizedSelfPresentationDegree0ProductEquiv_coeOfHom_left_apply A B Bg g x

/-- Helper for Chap10 Lemma 10 134 12: the degree-`0` biproduct split becomes the normalized
product-coordinate identification after applying the cotangent-space split and shear. -/
private theorem localizedSelfPresentation_biprod_XIso_zero_normalized_apply
    (z : (tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X 0) :
    localized_self_degree0_shear_equiv_on_product A B Bg g
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        (((localizedSelfPresentation_biprod_XIso_zero A B Bg g).hom.hom) z)) =
      let xi :=
        ((ModuleCat.biprodIsoProd
            ((tensorNaiveCotangentAwayModel A B Bg).X 0)
            ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 0)).hom.hom)
          (((HomologicalComplex.biprodXIso
              (tensorNaiveCotangentAwayModel A B Bg)
              ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
              0).hom.hom) z)
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap xi.2, xi.1) := by
  -- Rewrite once to the already packaged product coordinates, then reuse the normalized degree-`0`
  -- product formula in exactly the downstream consumer spelling.
  rw [localizedSelfPresentation_biprod_XIso_zero_apply_eq_product]
  rw [ModuleCat.hom_ofHom]
  rw [localizedSelfPresentationDegree0ProductEquiv_normalized_apply A B Bg g
    (((ModuleCat.biprodIsoProd
      ((tensorNaiveCotangentAwayModel A B Bg).X 0)
      ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 0)).hom.hom)
      (((HomologicalComplex.biprodXIso
        (tensorNaiveCotangentAwayModel A B Bg)
        ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
        0).hom.hom) z))]
  rfl

/-- Helper for Chap10 Lemma 10 134 12: the degree-`1` component of the biproduct split is the
explicit product-coordinate map obtained from `biprodXIso`, `biprodIsoProd`, and the normalized
degree-`1` product equivalence. -/
private theorem localizedSelfPresentation_biprod_XIso_one_apply_eq_product
    (z : (tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X 1) :
    ((localizedSelfPresentation_biprod_XIso_one A B Bg g).hom.hom) z =
      (ModuleCat.Hom.hom
        (ModuleCat.ofHom
          ((localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap)))
        (((ModuleCat.biprodIsoProd
            ((tensorNaiveCotangentAwayModel A B Bg).X 1)
            ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1)).hom.hom)
          (((HomologicalComplex.biprodXIso
              (tensorNaiveCotangentAwayModel A B Bg)
              ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
              1).hom.hom) z)) := by
  -- Rewrite through the named degree-`1` component formula, then read the result in product
  -- coordinates.
  rw [localizedSelfPresentation_biprod_XIso_one_def]
  rw [Iso.trans_hom, Iso.trans_hom]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [ModuleCat.hom_ofHom]
  rfl

/-- Helper for Lemma 10.134.12: every higher-degree component of the canonical biproduct split is
the unique isomorphism between two subsingleton `ModuleCat` objects. -/
private noncomputable def localizedSelfPresentation_biprod_XIso_succ_succ
    (n : ℕ) :
    (tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X (n + 2) ≅
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X (n + 2) := by
  -- Both higher-degree terms are zero-tail `PUnit` terms, so the unique linear equivalence
  -- between subsingleton modules gives the component isomorphism.
  letI : Subsingleton
      ((tensorNaiveCotangentAwayModel A B Bg ⊞
          (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X
        (n + 2)) :=
    localizedSelfPresentation_source_X_succ_succ_subsingleton A B Bg g n
  letI : Subsingleton
      ((localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X (n + 2)) :=
    localized_self_X_succ_succ_subsingleton A B Bg g n
  exact
    (LinearEquiv.ofSubsingleton
      ((tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X (n + 2))
      ((localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X (n + 2))).toModuleIso

/-- Helper for Lemma 10.134.12: the localized self-presentation splits as the tensorized old
presentation plus the contractible localization-away summand, degree by degree. -/
private noncomputable def localizedSelfPresentation_biprod_XIso :
    ∀ n : ℕ,
      (tensorNaiveCotangentAwayModel A B Bg ⊞
          (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X n ≅
        (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X n
  | 0 => localizedSelfPresentation_biprod_XIso_zero A B Bg g
  | 1 => localizedSelfPresentation_biprod_XIso_one A B Bg g
  | n + 2 => localizedSelfPresentation_biprod_XIso_succ_succ A B Bg g n

/-- Helper for Lemma 10.134.12: in chain-component spelling, the degree-`1` product equivalence
sends the left tensor coordinate to the base-changed conormal comparison map. -/
private theorem localizedSelfPresentationDegree1ProductEquiv_left_apply
    (x : (tensorNaiveCotangentAwayModel A B Bg).X 1) :
    (localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap
        (x, (0 :
          (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1)) =
      let C := (localizedSelfGenerators A B Bg g).toExtension
      (((ULift.moduleEquiv : ULift C.Cotangent ≃ₗ[Bg] C.Cotangent).symm.toLinearMap) ∘ₗ
        LinearMap.liftBaseChange Bg
          (Extension.Cotangent.map ((Generators.localizationAway Bg g).toComp
            (Generators.self A B)).toExtensionHom)) x := by
  -- Move the product input through the conormal splitting; the zero localization coordinate lets
  -- the canonical left-summand formula close the comparison immediately.
  change
    ((cotangentCompLocalizationAwayEquiv g (Generators.self A B)
      (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm.trans
        ULift.moduleEquiv.symm)
      (((LinearEquiv.refl Bg (Bg ⊗[B] (selfExtension A B).Cotangent)).prodCongr
        ((localizationAway_reindex_degree1_linearEquiv B Bg g).trans ULift.moduleEquiv))
          (x, (0 :
            (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1))) =
      (((ULift.moduleEquiv :
            ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
              (localizedSelfGenerators A B Bg g).toExtension.Cotangent).symm.toLinearMap) ∘ₗ
        LinearMap.liftBaseChange Bg
          (Extension.Cotangent.map ((Generators.localizationAway Bg g).toComp
            (Generators.self A B)).toExtensionHom)) x
  rw [LinearEquiv.prodCongr_apply]
  simp only [LinearEquiv.refl_apply, map_zero]
  rw [LinearEquiv.trans_apply]
  rw [Generators.cotangentCompLocalizationAwayEquiv_symm_inl]
  rfl

/-- Helper for Chap10 Lemma 10 134 12: the degree-`1` reindex identification turns the standard
localization differential into the reindexed degree-`0` differential. -/
private theorem localizationAway_reindex_degree1_degree0_apply
    (y : (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    (Generators.localizationAway Bg g).toExtension.cotangentComplex
        (((localizationAway_reindex_degree1_linearEquiv B Bg g).trans ULift.moduleEquiv) y) =
      (localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap
        (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom y) := by
  -- Degree `1` is an `ULift` of the conormal module, so unpack the lift and reuse the already
  -- normalized conormal/cotangent-space square.
  rcases y with ⟨y⟩
  simpa [localizationAway_reindex_degree1_linearEquiv, Extension.naiveCotangentChainComplex,
    localizationAway_reindex_degree0_iso, LinearEquiv.trans_apply]
    using LinearMap.congr_fun (localizationAway_reindex_cotangent_equiv_comm B Bg g) y

/-- Helper for Chap10 Lemma 10 134 12: in chain-component spelling, the degree-`1` product
equivalence sends the localization-away coordinate to the standard localization summand. -/
private theorem localizedSelfPresentationDegree1ProductEquiv_right_apply
    (y : (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    (localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap (0, y) =
      ((ULift.moduleEquiv :
          ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
            (localizedSelfGenerators A B Bg g).toExtension.Cotangent).symm.toLinearMap)
        (((cotangentCompLocalizationAwayEquiv g (Generators.self A B)
            (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm)
          (0, ((localizationAway_reindex_degree1_linearEquiv B Bg g).trans ULift.moduleEquiv) y)) := by
  -- The right coordinate is already in the exact normal form of the product equivalence.
  change
    ((cotangentCompLocalizationAwayEquiv g (Generators.self A B)
      (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm.trans
        ULift.moduleEquiv.symm)
      (((LinearEquiv.refl Bg (Bg ⊗[B] (selfExtension A B).Cotangent)).prodCongr
        ((localizationAway_reindex_degree1_linearEquiv B Bg g).trans ULift.moduleEquiv))
          (0, y)) =
      ((ULift.moduleEquiv :
            ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
              (localizedSelfGenerators A B Bg g).toExtension.Cotangent).symm.toLinearMap)
        (((cotangentCompLocalizationAwayEquiv g (Generators.self A B)
            (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm)
          (0, ((localizationAway_reindex_degree1_linearEquiv B Bg g).trans ULift.moduleEquiv) y))
  rw [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]
  simp

/-- Helper for Chap10 Lemma 10 134 12: the normalized target differential on degree-`1`
product coordinates. -/
private noncomputable def localizedSelfPresentationDegree1NormalizedMap :
    ((tensorNaiveCotangentAwayModel A B Bg).X 1 ×
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) →ₗ[Bg]
      ((Generators.localizationAway Bg g).toExtension.CotangentSpace ×
        (Bg ⊗[B] (selfExtension A B).CotangentSpace)) :=
  (localized_self_degree0_shear_equiv_on_product A B Bg g).toLinearMap.comp
    ((CotangentSpace.compEquiv
      (Generators.localizationAway Bg g)
      (Generators.self A B)).toLinearMap.comp
      (((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex).comp
        (((ULift.moduleEquiv :
              ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
                (localizedSelfGenerators A B Bg g).toExtension.Cotangent).toLinearMap).comp
          ((localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap))))

/-- Helper for Chap10 Lemma 10 134 12: the normalized degree-`1` map unfolds to the single
whole composite used for both coordinate computations. -/
private theorem localizedSelfPresentationDegree1NormalizedMap_apply
    (z : (tensorNaiveCotangentAwayModel A B Bg).X 1 ×
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    localizedSelfPresentationDegree1NormalizedMap A B Bg g z =
      localized_self_degree0_shear_equiv_on_product A B Bg g
        (CotangentSpace.compEquiv
          (Generators.localizationAway Bg g)
          (Generators.self A B)
          ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex
            ((ULift.moduleEquiv :
                ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
                  (localizedSelfGenerators A B Bg g).toExtension.Cotangent)
              ((localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap z)))) := by
  -- This is only a top-level application rule for the named composite; downstream proofs rewrite
  -- through this lemma instead of unfolding under `DFunLike` coercions repeatedly.
  rfl

/-- Helper for Chap10 Lemma 10 134 12: the exact degree-`1` chain-consumer spelling used in the
`1 → 0` square is the named normalized degree-`1` map. -/
private theorem localizedSelfPresentationDegree1ProductEquiv_coe_apply
    (z : (tensorNaiveCotangentAwayModel A B Bg).X 1 ×
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    (ModuleCat.Hom.hom
      (ModuleCat.ofHom
        ((localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap))) z =
      (localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap z := by
  -- As in degree `0`, the `ModuleCat.ofHom` wrapper leaves the underlying linear map unchanged.
  rfl

/-- Helper for Chap10 Lemma 10 134 12: the exact degree-`1` chain-consumer spelling used in the
`1 → 0` square is the named normalized degree-`1` map. -/
private theorem localizedSelfPresentationDegree1NormalizedMap_chain_consumer
    (z : (tensorNaiveCotangentAwayModel A B Bg).X 1 ×
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    localized_self_degree0_shear_equiv_on_product A B Bg g
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex
          ((ULift.moduleEquiv :
              ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
                (localizedSelfGenerators A B Bg g).toExtension.Cotangent)
          ((ModuleCat.Hom.hom
              (ModuleCat.ofHom
                ((localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap))) z)))) =
      localizedSelfPresentationDegree1NormalizedMap A B Bg g z := by
  -- Collapse the wrapped consumer to the underlying linear map and unfold the named composite.
  rw [localizedSelfPresentationDegree1ProductEquiv_coe_apply]
  exact localizedSelfPresentationDegree1NormalizedMap_apply A B Bg g z

/-- Helper for Chap10 Lemma 10 134 12: the tensor coordinate of the normalized degree-`1` map
is the standard base-changed conormal differential. -/
private theorem localizedSelfPresentationDegree1NormalizedMap_left_baseChange_apply
    (x : (tensorNaiveCotangentAwayModel A B Bg).X 1) :
    localizedSelfPresentationDegree1NormalizedMap A B Bg g (x, 0) =
      (0, LinearMap.baseChange Bg (selfExtension A B).cotangentComplex x) := by
  -- Move the left coordinate through the conormal product equivalence, cancel the `ULift`
  -- normalization, and then apply the owner shear-normalization lemma.
  rw [localizedSelfPresentationDegree1NormalizedMap_apply]
  rw [localizedSelfPresentationDegree1ProductEquiv_left_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  simpa using localized_self_degree0_shear_equiv_normalizes_tensor A B Bg g x

/-- Helper for Chap10 Lemma 10 134 12: the localization coordinate of the normalized degree-`1`
map is the standard localization-away differential before reindexing back to the local model. -/
private theorem localizedSelfPresentationDegree1NormalizedMap_right_standard_apply
    (y : (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    localizedSelfPresentationDegree1NormalizedMap A B Bg g (0, y) =
      (((Generators.localizationAway Bg g).toExtension.cotangentComplex
          (((localizationAway_reindex_degree1_linearEquiv B Bg g).trans ULift.moduleEquiv) y)),
        0) := by
  -- The right coordinate is first expressed in the standard localization-away presentation, where
  -- the existing shear-normalization lemma computes the differential directly.
  let y' :=
    ((localizationAway_reindex_degree1_linearEquiv B Bg g).trans ULift.moduleEquiv) y
  rw [localizedSelfPresentationDegree1NormalizedMap_apply]
  rw [localizedSelfPresentationDegree1ProductEquiv_right_apply]
  have hcancel :
      (ULift.moduleEquiv :
          ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
            (localizedSelfGenerators A B Bg g).toExtension.Cotangent)
        (((ULift.moduleEquiv :
            ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
              (localizedSelfGenerators A B Bg g).toExtension.Cotangent).symm.toLinearMap)
          (((cotangentCompLocalizationAwayEquiv g (Generators.self A B)
              (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm) (0, y'))) =
        (((cotangentCompLocalizationAwayEquiv g (Generators.self A B)
            (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm) (0, y')) := by
    simp
  rw [hcancel]
  simpa [y'] using
    localized_self_degree0_shear_equiv_normalizes_localization A B Bg g y'

/-- Helper for Chap10 Lemma 10 134 12: the tensor coordinate of the degree-`1` product
equivalence satisfies the normalized `1 → 0` differential square. -/
private theorem localizedSelfPresentationDegree1ProductEquiv_normalized_left_apply
    (x : (tensorNaiveCotangentAwayModel A B Bg).X 1) :
    localizedSelfPresentationDegree1NormalizedMap A B Bg g (x, 0) =
      (0, ((tensorNaiveCotangentAwayModel A B Bg).d 1 0).hom x) := by
  -- First compute in the standard base-change normal form, then fold back to the tensor-model
  -- chain differential at the wrapper boundary.
  rw [localizedSelfPresentationDegree1NormalizedMap_left_baseChange_apply]
  rfl

/-- Helper for Chap10 Lemma 10 134 12: the localization coordinate of the degree-`1` product
equivalence satisfies the normalized `1 → 0` differential square. -/
private theorem localizedSelfPresentationDegree1ProductEquiv_normalized_right_apply
    (y : (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    localizedSelfPresentationDegree1NormalizedMap A B Bg g (0, y) =
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap
          (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom y),
        0) := by
  -- Rewrite the product splitting to the localization summand, normalize it, and translate the
  -- standard localization differential back to the reindexed localization-away presentation.
  rw [localizedSelfPresentationDegree1NormalizedMap_right_standard_apply]
  rw [localizationAway_reindex_degree1_degree0_apply]

/-- Helper for Chap10 Lemma 10 134 12: after applying the target differential and the degree-`0`
normalization, the degree-`1` product equivalence recovers the two source differentials in
product coordinates. -/
private theorem localizedSelfPresentationDegree1ProductEquiv_normalized_cotangentComplex_apply
    (z : (tensorNaiveCotangentAwayModel A B Bg).X 1 ×
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    localizedSelfPresentationDegree1NormalizedMap A B Bg g z =
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap
          (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom
            z.2),
        ((tensorNaiveCotangentAwayModel A B Bg).d 1 0).hom z.1) := by
  -- Split the product input into tensor and localization coordinates, compute each coordinate
  -- separately, and add the two normalized differential values.
  rw [localizedSelfPresentationDegree1Product_split A B Bg g z]
  rw [map_add]
  rw [localizedSelfPresentationDegree1ProductEquiv_normalized_left_apply,
    localizedSelfPresentationDegree1ProductEquiv_normalized_right_apply]
  ext <;> simp

/-- Helper for Chap10 Lemma 10 134 12: the degree-`1 → 0` differential of the localized
self-presentation is the cotangent map composed with the standard `ULift` identification. -/
private theorem localizedSelf_naiveCotangent_d_one_zero_apply
    (x : (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    (((localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom) x =
      (localizedSelfGenerators A B Bg g).toExtension.cotangentComplex
        ((ULift.moduleEquiv :
            ULift (localizedSelfGenerators A B Bg g).toExtension.Cotangent ≃ₗ[Bg]
              (localizedSelfGenerators A B Bg g).toExtension.Cotangent) x) := by
  -- Route correction: rewrite the chain differential with the owner `d 1 0` lemma so the target
  -- is literally the cotangent complex applied to the `ULift`-normalized degree-`1` input.
  rw [Extension.naiveCotangentChainComplex_d_1_0]
  rfl

/-- Helper for Chap10 Lemma 10 134 12: the normalized degree-`1` differential already matches the
exact chain-complex spelling consumed by the unique nontrivial square. -/
private theorem localizedSelfPresentationDegree1ProductEquiv_normalized_chain_apply
    (z : (tensorNaiveCotangentAwayModel A B Bg).X 1 ×
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1) :
    localized_self_degree0_shear_equiv_on_product A B Bg g
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        (((localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom
          ((ModuleCat.Hom.hom
            (ModuleCat.ofHom
              ((localizedSelfPresentationDegree1ProductEquiv A B Bg g).toLinearMap))) z))) =
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap
        (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom
            z.2),
        ((tensorNaiveCotangentAwayModel A B Bg).d 1 0).hom z.1) := by
  -- Rewrite the target differential to the cotangent-complex spelling used by the normalized
  -- degree-`1` map, then close with the existing normalized computation lemma.
  rw [localizedSelf_naiveCotangent_d_one_zero_apply]
  rw [localizedSelfPresentationDegree1NormalizedMap_chain_consumer]
  exact
    localizedSelfPresentationDegree1ProductEquiv_normalized_cotangentComplex_apply A B Bg g z

/-- Helper for Chap10 Lemma 10 134 12: after taking the source `1 → 0` differential, the
degree-`0` biproduct split has the expected normalized product coordinates. -/
private theorem localizedSelfPresentation_biprod_XIso_zero_after_d_normalized
    (z : (tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X 1) :
    localized_self_degree0_shear_equiv_on_product A B Bg g
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        (((localizedSelfPresentation_biprod_XIso_zero A B Bg g).hom.hom)
          (((tensorNaiveCotangentAwayModel A B Bg ⊞
              (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).d 1 0).hom
            z))) =
      let xi :=
        ((ModuleCat.biprodIsoProd
            ((tensorNaiveCotangentAwayModel A B Bg).X 1)
            ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1)).hom.hom)
          (((HomologicalComplex.biprodXIso
              (tensorNaiveCotangentAwayModel A B Bg)
              ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
              1).hom.hom) z)
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap
          (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom
            xi.2),
        ((tensorNaiveCotangentAwayModel A B Bg).d 1 0).hom xi.1) := by
  -- Apply the degree-`0` normalization to the source differential, then rewrite the resulting
  -- degree-`0` product coordinates componentwise through the biproduct differential formula.
  let z' :=
    (((tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).d 1 0).hom z)
  have hnorm := localizedSelfPresentation_biprod_XIso_zero_normalized_apply A B Bg g z'
  simpa [z',
    biprodXIso_biprodIsoProd_d_apply
      Bg (tensorNaiveCotangentAwayModel A B Bg)
      ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
      1 0 z] using hnorm

/-- Helper for Chap10 Lemma 10 134 12: after applying the target `1 → 0` differential and the
degree-`0` normalization, the degree-`1` biproduct split yields the same source-coordinate pair
as the source differential. -/
private theorem localizedSelfPresentation_biprod_XIso_comm_one_zero_normalized
    (z : (tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X 1) :
    localized_self_degree0_shear_equiv_on_product A B Bg g
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        (((localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom
          (((localizedSelfPresentation_biprod_XIso_one A B Bg g).hom.hom) z))) =
      let xi :=
        ((ModuleCat.biprodIsoProd
            ((tensorNaiveCotangentAwayModel A B Bg).X 1)
            ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1)).hom.hom)
          (((HomologicalComplex.biprodXIso
              (tensorNaiveCotangentAwayModel A B Bg)
              ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
              1).hom.hom) z)
      ((localizationAway_reindex_cotangentSpace_equiv B Bg g).toLinearMap
          (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.d 1 0).hom
            xi.2),
        ((tensorNaiveCotangentAwayModel A B Bg).d 1 0).hom xi.1) := by
  -- Rewrite the degree-`1` component once into product coordinates and recognize the resulting
  -- expression as the named normalized degree-`1` map on those coordinates.
  let xi :=
    ((ModuleCat.biprodIsoProd
        ((tensorNaiveCotangentAwayModel A B Bg).X 1)
        ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X 1)).hom.hom)
      (((HomologicalComplex.biprodXIso
          (tensorNaiveCotangentAwayModel A B Bg)
          ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
          1).hom.hom) z)
  -- Use the exact chain-spelling normalization lemma to avoid another transport-heavy rewrite.
  simpa [xi, localizedSelfPresentation_biprod_XIso_one_apply_eq_product A B Bg g z,
    ModuleCat.hom_ofHom] using
    localizedSelfPresentationDegree1ProductEquiv_normalized_chain_apply A B Bg g xi

/-- Helper for Lemma 10.134.12: the degreewise biproduct split commutes with the differentials of
the localized self-presentation. -/
private theorem localizedSelfPresentation_biprod_XIso_comm :
    ∀ i j (_ : (ComplexShape.down ℕ).Rel i j),
      (localizedSelfPresentation_biprod_XIso A B Bg g i).hom ≫
        (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.d i j =
        (tensorNaiveCotangentAwayModel A B Bg ⊞
            (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).d i j ≫
          (localizedSelfPresentation_biprod_XIso A B Bg g j).hom := by
  -- Route correction: prove the unique nontrivial `1 → 0` square after the degree-`0`
  -- normalization, and use zero-tail subsingletons to dispatch every higher square.
  intro i j hij
  subst i
  cases j with
  | zero =>
      ext z
      refine
        (LinearEquiv.injective
          ((CotangentSpace.compEquiv
            (Generators.localizationAway Bg g)
            (Generators.self A B)).trans
            (localized_self_degree0_shear_equiv_on_product A B Bg g))) ?_
      -- Compare the two sides after the normalized degree-`0` coordinates; both sides are already
      -- computed by the dedicated `1 → 0` normalization lemmas.
      simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using
        (localizedSelfPresentation_biprod_XIso_comm_one_zero_normalized A B Bg g z).trans
          (localizedSelfPresentation_biprod_XIso_zero_after_d_normalized A B Bg g z).symm
  | succ j =>
      letI :
          Subsingleton
            ((tensorNaiveCotangentAwayModel A B Bg ⊞
                (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex).X
              (j + 2)) :=
        localizedSelfPresentation_source_X_succ_succ_subsingleton A B Bg g j
      ext z
      have hz : z = 0 := Subsingleton.elim _ _
      subst hz
      simp [ModuleCat.hom_comp, LinearMap.comp_apply]

/-- Helper for Lemma 10.134.12: the localized self-presentation splits as the tensorized old
presentation plus the contractible localization-away summand. -/
private noncomputable def localizedSelfPresentation_biprod_iso :
    tensorNaiveCotangentAwayModel A B Bg ⊞
        (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex ≅
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex :=
  -- Package the already-separated degreewise maps and differential compatibility into the chain
  -- isomorphism used by the final homotopy-equivalence argument.
  HomologicalComplex.Hom.isoOfComponents
    (localizedSelfPresentation_biprod_XIso A B Bg g)
    (localizedSelfPresentation_biprod_XIso_comm A B Bg g)

/-- Helper for Chap10 Lemma 10 134 12: the reindexed localization-away summand is contractible
because it is presentation-independent from the owner localization complex, which is null-homotopic
by Lemma `10.134.10`. -/
private noncomputable def localizationAway_reindex_naiveCotangent_contractible :
    Homotopy
      (𝟙 ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex))
      0 := by
  let Y := (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex
  let e₁ :
      HomotopyEquiv
        Y
        (Generators.self B Bg).toExtension.naiveCotangentChainComplex :=
    Generators.naiveCotangentChainHomotopyEquiv
      (localizationAwayGenerators B Bg g)
      (Generators.self B Bg)
  let e₂ :
      HomotopyEquiv
        (Generators.self B Bg).toExtension.naiveCotangentChainComplex
        (HomologicalComplex.zero : ChainComplex (ModuleCat Bg) ℕ) := by
    simpa [Algebra.naiveCotangent] using
      (show
          HomotopyEquiv
            (Generators.self B Bg).toExtension.naiveCotangentChainComplex
            (HomologicalComplex.zero : ChainComplex (ModuleCat Bg) ℕ)
        from localization_naiveCotangentComplex_homotopyEquiv_zero (Submonoid.powers g))
  let e := e₁.trans e₂
  have hzero : e.hom ≫ e.inv = 0 := by
    -- The zero complex has no nonzero morphisms into it, so the round-trip composite vanishes.
    ext i
    have hhom : e.hom.f i = 0 := by
      exact (Limits.isZero_zero (ModuleCat Bg)).eq_of_tgt _ _
    simp [hhom]
  have hId :
      Homotopy
        (𝟙 ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex))
        (e.hom ≫ e.inv) := e.homotopyHomInvId.symm
  exact
    (show Homotopy
        (𝟙 ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)) 0 from
      hId.trans (Homotopy.ofEq hzero))

/-- Helper for Chap10 Lemma 10 134 12: the localization-away summand is contractible in the
native chain-complex category before any ambient-universe transport is applied. -/
private noncomputable def localizedSelfTensorRightSummandContractibleNative :
    Homotopy
      (𝟙 ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex))
      0 := by
  -- This is the exact concrete contraction produced by the reindexed localization-away model.
  simpa using localizationAway_reindex_naiveCotangent_contractible B Bg g

/-- Helper for Chap10 Lemma 10 134 12: every higher-degree term of an `A`-to-`Bg` presentation
naive cotangent complex is zero. -/
private abbrev LiftCotangent (P : Extension.{w} A Bg) :=
  ULift.{v, w} P.Cotangent

/-- Helper for Chap10 Lemma 10 134 12: the canonical identification between the lifted cotangent
term and the ordinary cotangent term over `Bg`. -/
private noncomputable abbrev liftCotangentEquiv
    (P : Extension.{w} A Bg) :
    LiftCotangent A Bg P ≃ₗ[Bg] P.Cotangent :=
  ULift.moduleEquiv

/-- Helper for Chap10 Lemma 10 134 12: every higher-degree term of an `A`-to-`Bg` presentation
naive cotangent complex is a subsingleton. -/
private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension.{w} A Bg) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  -- Transport the unique `PUnit` element back through the standard high-degree tail isomorphism.
  let e := extension_naiveCotangentChainComplex_X_succ_succ_iso_punit P i
  refine ⟨fun x y ↦ ?_⟩
  simpa using congrArg e.inv.hom (Subsingleton.elim (e.hom.hom x) (e.hom.hom y))

/-- Helper for Chap10 Lemma 10 134 12: the degree-`0` to degree-`1` homotopy component comparing
two extension-induced maps on naive cotangent complexes over `Bg`. -/
private noncomputable abbrev liftCotangentHomotopyMap
    {P Q : Extension.{w} A Bg} (f₁ f₂ : P.Hom Q) :
    P.CotangentSpace →ₗ[Bg] LiftCotangent A Bg Q :=
  (liftCotangentEquiv A Bg Q).symm.toLinearMap ∘ₗ f₁.sub f₂

/-- Helper for Chap10 Lemma 10 134 12: the unique nontrivial relation in the downward shape from
degree `1` to degree `0`. -/
private theorem naiveCotangent_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
  -- This is the basic successor relation of the downward complex shape.
  simp [ComplexShape.down]

/-- Helper for Chap10 Lemma 10 134 12: the next higher relation in the downward shape from degree
`2` to degree `1`. -/
private theorem naiveCotangent_rel21 : (ComplexShape.down ℕ).Rel 2 1 := by
  -- This is used only to write the degree-`1` component of the null-homotopy.
  simp [ComplexShape.down]

/-- Helper for Chap10 Lemma 10 134 12: no relation in the downward shape starts at degree `0`. -/
private theorem naiveCotangent_not_rel0 (j : ℕ) : ¬ (ComplexShape.down ℕ).Rel 0 j := by
  -- Degree `0` is terminal in the displayed portion of a downward complex.
  simp [ComplexShape.down]

/-- Helper for Chap10 Lemma 10 134 12: the raw homotopy matrix comparing two extension-induced maps
on naive cotangent complexes over `Bg`. -/
private noncomputable def naiveCotangentChainHomotopyHomAnyUniverse
    {P Q : Extension.{w} A Bg} (f₁ f₂ : P.Hom Q)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    P.naiveCotangentChainComplex.X i ⟶ Q.naiveCotangentChainComplex.X j :=
  match i with
  | 0 =>
      match j with
      | 0 => 0
      | 1 => ModuleCat.ofHom (liftCotangentHomotopyMap A Bg f₁ f₂)
      | _ + 2 => 0
  | _ + 1 => 0

/-- Helper for Chap10 Lemma 10 134 12: two extension-induced maps on naive cotangent complexes
over `Bg` differ by the null-homotopic map attached to the raw homotopy matrix. -/
private theorem naiveCotangentChainMap_sub_eq_nullHomotopicMap_anyUniverse
    {P Q : Extension.{w} A Bg} (f₁ f₂ : P.Hom Q) :
    Extension.naiveCotangentChainMap f₁ - Extension.naiveCotangentChainMap f₂ =
      Homotopy.nullHomotopicMap'
        (naiveCotangentChainHomotopyHomAnyUniverse A Bg f₁ f₂) := by
  -- Check the equality degree by degree; degrees above `1` are subsingleton tails.
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change (Extension.naiveCotangentChainMap f₁ - Extension.naiveCotangentChainMap f₂).f 0 =
        (Homotopy.nullHomotopicMap'
          (naiveCotangentChainHomotopyHomAnyUniverse A Bg f₁ f₂)).f 0
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left naiveCotangent_rel10
        naiveCotangent_not_rel0
        (naiveCotangentChainHomotopyHomAnyUniverse A Bg f₁ f₂)]
      ext x
      simpa [Extension.naiveCotangentChainMap, naiveCotangentChainHomotopyHomAnyUniverse,
        Algebra.Extension.naiveCotangentChainComplex, liftCotangentHomotopyMap,
        LinearMap.comp_assoc] using
        LinearMap.congr_fun (Extension.CotangentSpace.map_sub_map f₁ f₂) x
  | succ i =>
      cases i with
      | zero =>
          change (Extension.naiveCotangentChainMap f₁ - Extension.naiveCotangentChainMap f₂).f 1 =
            (Homotopy.nullHomotopicMap'
              (naiveCotangentChainHomotopyHomAnyUniverse A Bg f₁ f₂)).f 1
          rw [Homotopy.nullHomotopicMap'_f naiveCotangent_rel21 naiveCotangent_rel10
            (naiveCotangentChainHomotopyHomAnyUniverse A Bg f₁ f₂)]
          ext x
          rcases x with ⟨x⟩
          change ULift.up ((Cotangent.map f₁ - Cotangent.map f₂) x) =
            (ModuleCat.Hom.hom
                (P.naiveCotangentChainComplex.d 1 0 ≫
                  naiveCotangentChainHomotopyHomAnyUniverse A Bg f₁ f₂ 0 1
                    naiveCotangent_rel10 +
                naiveCotangentChainHomotopyHomAnyUniverse A Bg f₁ f₂ 1 2
                    naiveCotangent_rel21 ≫
                  Q.naiveCotangentChainComplex.d 2 1))
              { down := x }
          rw [Extension.naiveCotangentChainComplex_d_succ_succ Q 0,
            Extension.naiveCotangentChainComplex_d_1_0 P]
          simp only [naiveCotangentChainHomotopyHomAnyUniverse, liftCotangentHomotopyMap,
            LinearMap.sub_apply, comp_zero, add_zero, ModuleCat.hom_comp, LinearMap.coe_comp,
            Function.comp_apply]
          change ULift.up ((Cotangent.map f₁ - Cotangent.map f₂) x) =
            ULift.up ((f₁.sub f₂) (P.cotangentComplex x))
          rw [LinearMap.congr_fun (Extension.Cotangent.map_sub_map f₁ f₂) x]
          rfl
      | succ i =>
          letI : Subsingleton (Q.naiveCotangentChainComplex.X (i + 2)) :=
            naiveCotangentChainComplex_subsingleton_of_succ_succ A Bg Q i
          ext x
          exact Subsingleton.elim _ _

/-- Helper for Chap10 Lemma 10 134 12: any two extension maps over `Bg` induce homotopic maps on
naive cotangent complexes. -/
private noncomputable def naiveCotangentChainMapHomotopyAnyUniverse
    {P Q : Extension.{w} A Bg} (f₁ f₂ : P.Hom Q) :
    Homotopy (Extension.naiveCotangentChainMap f₁) (Extension.naiveCotangentChainMap f₂) :=
  -- Rewrite the difference as a null-homotopic map and then discard the zero summand.
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq
        (naiveCotangentChainMap_sub_eq_nullHomotopicMap_anyUniverse A Bg f₁ f₂)).trans
      (Homotopy.nullHomotopy'
        (naiveCotangentChainHomotopyHomAnyUniverse A Bg f₁ f₂)))

/-- Helper for Chap10 Lemma 10 134 12: the default comparison between two presentations of `Bg`,
viewed at the extension level. -/
private noncomputable abbrev defaultExtensionHomAnyUniverseAux
    {ι ι' : Type v} (P : Generators A Bg ι) (Q : Generators A Bg ι') :
    P.toExtension.Hom Q.toExtension :=
  (Generators.defaultHom P Q).toExtensionHom

/-- Helper for Chap10 Lemma 10 134 12: the presentation-independence homotopy for extension maps
over `Bg`, with the unused local parameters omitted from the interface. -/
private noncomputable abbrev naiveCotangentChainMapHomotopyAnyUniverseAux
    {P Q : Extension.{w} A Bg} (f₁ f₂ : P.Hom Q) :
    Homotopy (Extension.naiveCotangentChainMap f₁) (Extension.naiveCotangentChainMap f₂) :=
  naiveCotangentChainMapHomotopyAnyUniverse A Bg f₁ f₂

/-- Helper for Chap10 Lemma 10 134 12: arbitrary `A`-presentations of `Bg` have homotopy
equivalent naive cotangent complexes without requiring their generator universes to match `u`. -/
private noncomputable def generatorsNaiveCotangentChainHomotopyEquivAnyUniverse
    {ι ι' : Type v} (P : Generators A Bg ι) (Q : Generators A Bg ι') :
    HomotopyEquiv P.toExtension.naiveCotangentChainComplex Q.toExtension.naiveCotangentChainComplex where
  hom := Extension.naiveCotangentChainMap (defaultExtensionHomAnyUniverseAux A Bg P Q)
  inv := Extension.naiveCotangentChainMap (defaultExtensionHomAnyUniverseAux A Bg Q P)
  homotopyHomInvId := by
    -- Compose the two default maps, then contract the result to the identity-induced chain map.
    let f := defaultExtensionHomAnyUniverseAux A Bg P Q
    let g' := defaultExtensionHomAnyUniverseAux A Bg Q P
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp f g').symm).trans
        ((naiveCotangentChainMapHomotopyAnyUniverseAux A Bg (g'.comp f)
            (.id P.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id P.toExtension)))
  homotopyInvHomId := by
    -- The inverse-side homotopy is the same argument with the two presentations interchanged.
    let f := defaultExtensionHomAnyUniverseAux A Bg P Q
    let g' := defaultExtensionHomAnyUniverseAux A Bg Q P
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp g' f).symm).trans
        ((naiveCotangentChainMapHomotopyAnyUniverseAux A Bg (f.comp g')
            (.id Q.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id Q.toExtension)))

/-- Helper for Chap10 Lemma 10 134 12: presentation-independence identifies the localized
self-presentation with the owner naive cotangent complex of `Bg`. -/
private noncomputable def localizedSelfOwnerHomotopyEquiv :
    HomotopyEquiv
      (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex
      (Generators.self A Bg).toExtension.naiveCotangentChainComplex := by
  let P : Generators A Bg (Unit ⊕ B) := localizedSelfGenerators A B Bg g
  let Q : Generators A Bg Bg := Generators.self A Bg
  -- Use the any-universe presentation-independence bridge with explicit generator index types.
  exact
    (show HomotopyEquiv P.toExtension.naiveCotangentChainComplex
        Q.toExtension.naiveCotangentChainComplex from
      generatorsNaiveCotangentChainHomotopyEquivAnyUniverse A Bg P Q)

/-- Helper for Chap10 Lemma 10 134 12: the tensorized naive cotangent model is homotopy
equivalent to its biproduct with the contractible localization-away summand. -/
private noncomputable def localizedSelfTensorInlHomotopyEquivNative :
    HomotopyEquiv
      ((tensorNaiveCotangentAwayModel A B Bg : ChainComplex (ModuleCat Bg) ℕ))
      (((tensorNaiveCotangentAwayModel A B Bg : ChainComplex (ModuleCat Bg) ℕ)) ⊞
        (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex :
          ChainComplex (ModuleCat Bg) ℕ))) :=
  by
    let X := tensorNaiveCotangentAwayModel A B Bg
    let P : Extension.{max u v} B Bg :=
      (localizationAwayGenerators B Bg g).toExtension
    let Y :
        ChainComplex.{max u v, max v ((max u v) + 1), 0} (ModuleCat Bg) ℕ :=
      P.naiveCotangentChainComplex
    have hY : Homotopy (𝟙 Y) 0 := by
      letI : Algebra.FormallyEtale B Bg := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
      letI : Subsingleton (H1Cotangent B Bg) := Algebra.FormallyEtale.subsingleton_h1Cotangent
      letI : Subsingleton P.H1Cotangent :=
        ((localizationAwayGenerators B Bg g).equivH1Cotangent).injective.subsingleton
      letI : Subsingleton Ω[Bg⁄B] := Algebra.FormallyEtale.subsingleton_kaehlerDifferential
      let e :
          P.Cotangent ≃ₗ[Bg] P.CotangentSpace :=
        cotangentComplexEquiv_of_subsingleton_h1_and_kaehler P
      let σ :
          P.CotangentSpace →ₗ[Bg] LiftCotangent B Bg P :=
        (liftCotangentEquiv B Bg P).symm.toLinearMap ∘ₗ e.symm.toLinearMap
      let s
          (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
          P.naiveCotangentChainComplex.X i ⟶ P.naiveCotangentChainComplex.X j :=
        match i with
        | 0 =>
            match j with
            | 0 => 0
            | 1 => ModuleCat.ofHom σ
            | _ + 2 => 0
        | _ + 1 => 0
      have hs :
          𝟙 P.naiveCotangentChainComplex = Homotopy.nullHomotopicMap' s := by
        apply HomologicalComplex.hom_ext
        intro i
        cases i with
        | zero =>
            rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
              naiveCotangent_rel10 naiveCotangent_not_rel0 s]
            rw [Extension.naiveCotangentChainComplex_d_1_0]
            ext x
            simp only [s, σ, ModuleCat.ofHom_comp]
            change x = e (e.symm x)
            exact (e.apply_symm_apply x).symm
        | succ i =>
            cases i with
            | zero =>
                rw [Homotopy.nullHomotopicMap'_f naiveCotangent_rel21 naiveCotangent_rel10 s]
                rw [Extension.naiveCotangentChainComplex_d_succ_succ P 0,
                  Extension.naiveCotangentChainComplex_d_1_0 P]
                ext x
                cases x with
                | up x =>
                    simp only [s, σ, Extension.naiveCotangentChainComplex, ModuleCat.ofHom_comp]
                    change ULift.up x = ULift.up (e.symm (e x)) + 0
                    rw [add_zero]
                    exact congrArg ULift.up (e.symm_apply_apply x).symm
            | succ i =>
                haveI :=
                  naiveCotangentChainComplex_subsingleton_of_succ_succ B Bg P i
                ext x
                exact Subsingleton.elim _ _
      exact
        (show Homotopy (𝟙 P.naiveCotangentChainComplex) 0 from
          (Homotopy.ofEq hs).trans (Homotopy.nullHomotopy' s))
    simpa [X, Y] using
      (biprod_inl_homotopyEquiv_of_right_contractible Bg X Y hY)

/-- Helper for Chap10 Lemma 10 134 12: the tensorized naive cotangent model is homotopy
equivalent to its biproduct with the contractible localization-away summand. -/
private noncomputable def localizedSelfTensorInlHomotopyEquiv :
    HomotopyEquiv
      ((tensorNaiveCotangentAwayModel A B Bg : ChainComplex (ModuleCat Bg) ℕ))
      (((tensorNaiveCotangentAwayModel A B Bg : ChainComplex (ModuleCat Bg) ℕ)) ⊞
        (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex :
          ChainComplex (ModuleCat Bg) ℕ))) :=
  -- Route correction: expose the native biproduct equivalence first and reuse it directly in the
  -- exact outer spelling consumed by the final composite.
  (show HomotopyEquiv
      ((tensorNaiveCotangentAwayModel A B Bg : ChainComplex (ModuleCat Bg) ℕ))
      (((tensorNaiveCotangentAwayModel A B Bg : ChainComplex (ModuleCat Bg) ℕ)) ⊞
        (((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex :
          ChainComplex (ModuleCat Bg) ℕ))) from
    localizedSelfTensorInlHomotopyEquivNative A B Bg g)

/-- Companion for Chap10 Lemma 10 134 12: a chosen homotopy equivalence witnessing that the
canonical comparison map
`NL_{B⁄A} ⊗[B] Bg ⟶ NL_{Bg⁄A}`
is an equivalence after passing to the homotopy category. -/
noncomputable def naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv :
    HomotopyEquiv
      (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (NL_{B⁄A}))
      NL_{Bg⁄A} :=
  let eTensor :
      HomotopyEquiv
        (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (NL_{B⁄A}))
        (tensorNaiveCotangentAwayModel A B Bg) :=
    -- Route correction: move first to the typed tensor model, so the remaining comparison stays in
    -- one stable chain-complex spelling.
    HomotopyEquiv.ofIso (naiveCotangentTensorToTensorModelIso A B Bg)
  let eInl :
      HomotopyEquiv
        (tensorNaiveCotangentAwayModel A B Bg)
        (tensorNaiveCotangentAwayModel A B Bg ⊞
          (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex) :=
    localizedSelfTensorInlHomotopyEquiv A B Bg g
  let eSplit :
      HomotopyEquiv
        (tensorNaiveCotangentAwayModel A B Bg ⊞
          (localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex)
        (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex :=
    HomotopyEquiv.ofIso (localizedSelfPresentation_biprod_iso A B Bg g)
  let eOwner :
      HomotopyEquiv
        (localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex
        (Generators.self A Bg).toExtension.naiveCotangentChainComplex :=
    localizedSelfOwnerHomotopyEquiv A B Bg g
  -- Compose the tensor-model identification, the contractible-summand split, the biproduct
  -- presentation isomorphism, and the owner presentation-independence comparison.
  eTensor.trans eInl |>.trans eSplit |>.trans eOwner

/-- The canonical chain map
`NL_{B⁄A} ⊗[B] Bg ⟶ NL_{Bg⁄A}` obtained by localizing the
canonical self-presentation of `B` away from `g` and then comparing that localized presentation
with the owner self-presentation of the chosen away-localization target `Bg`. -/
noncomputable def naiveCotangent_tensor_comparison_of_isLocalizationAway :
    (((ModuleCat.extendScalars (algebraMap B Bg)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (NL_{B⁄A})) ⟶
      NL_{Bg⁄A} :=
  (naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv A B Bg g).hom

-- Proof sketch: let `P := Generators.self A B`, and let `β` be the localized presentation
-- `(Generators.localizationAway Bg g).comp P` of `Bg` obtained by adjoining an inverse of `g`.
-- Mathlib's `cotangentCompLocalizationAwayEquiv` and `CotangentSpace.compEquiv` identify the
-- conormal and cotangent-space terms of `β` with the tensorized terms of `NL_{B⁄A}` plus the
-- contractible localization-away summand. The resulting comparison
-- `NL_{B⁄A} ⊗[B] Bg → β.naiveCotangentChainComplex` is therefore a homotopy equivalence, and the
-- canonical presentation-independence map from `β.naiveCotangentChainComplex` to the owner
-- `NL_{Bg⁄A}` is a homotopy equivalence as well. Passing to the homotopy category packages the
-- source statement as the claim that the canonical comparison morphism becomes an isomorphism.
private theorem naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso_aux :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map
        (naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g)) := by
  -- The comparison map is the hom of the canonical homotopy-equivalence composite, so its image
  -- in the homotopy category is the hom of `HomotopyCategory.isoOfHomotopyEquiv`.
  let e := naiveCotangent_tensor_comparison_of_isLocalizationAway_homotopyEquiv A B Bg g
  change IsIso ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map
    (naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g))
  change IsIso (HomotopyCategory.isoOfHomotopyEquiv e).hom
  infer_instance

/-- Chap10 Lemma 10 134 12: for any away-localization target `Bg` of `B` at `g`, the canonical
comparison map
`NL_{B⁄A} ⊗[B] Bg ⟶ NL_{Bg⁄A}`
becomes an isomorphism in the homotopy category. -/
@[stacks 08JZ]
theorem naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat Bg) (ComplexShape.down ℕ)).map
        (naiveCotangent_tensor_comparison_of_isLocalizationAway A B Bg g)) :=
  naiveCotangent_tensor_comparison_of_isLocalizationAway_isIso_aux A B Bg g

end
