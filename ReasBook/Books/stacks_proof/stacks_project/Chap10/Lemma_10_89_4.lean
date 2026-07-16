import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_11_1
import stacks_proof.stacks_project.Chap10.Lemma_10_11_3
import stacks_proof.stacks_project.Chap10.Lemma_10_88_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
open ULift

noncomputable section

/- Domain-style sampling for Lemma 10.89.4:
- primary domain: finitely presented modules, filtered-colimit presentations in `ModuleCat`, and
  tensoring a factored map with a fixed module;
- sampled owner declarations:
  `module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented`,
  `module_finitePresentation_iff_isFinitelyPresentable`,
  `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit`,
  `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`;
- best owner abstraction: this lemma is a source-facing factorization statement, but its proof
  should run through the canonical owners `ObjectProperty.ind`, `IsFinitelyPresentable`, and the
  tensor functor `tensorRight` on `ModuleCat`;
- primitive data: the map `f : P →ₗ[R] M`, the finitely presented source `P`, the module `Q`, and
  the tensor element `x` lying in `ker (f.rTensor Q)`;
- derived API: the finitely presented stage `P' : ModuleCat.{w} R` in a filtered presentation of
  `M`, together with the induced factorization through that stage and the eventual vanishing of `x`
  after tensoring.

Source/core/bridge triage:
- `source-facing`: the theorem below, which extracts one finitely presented factorization killing a
  chosen tensor-kernel element;
- `core/canonical`: filtered colimit presentations of `ModuleCat` and finite presentability via
  `IsFinitelyPresentable`;
- `bridge/view`: the mapped colimit presentation under `tensorRight (ModuleCat.of R Q)`.
-/

-- Proof sketch: write `M` as a filtered colimit of finitely presented modules. Since `P` is
-- finitely presented, the map `f` factors through one stage `M_j`. The element `x` then maps to an
-- element of `M_j ⊗[R] Q` that dies in the colimit `M ⊗[R] Q`, so after passing to a later stage
-- `M_{j'}` it already dies there. Take `P' = M_{j'}` and let `f'` be the induced composite.
/-- Helper for Lemma 10.89.4: after lifting `M` into the common universe `max u w`, the lifted
module admits a filtered colimit presentation by finitely presented stages. -/
private lemma ulift_finite_presentation_stage_presentation_common_universe
    {R : Type u} [CommRing R]
    {M : Type w} [AddCommGroup M] [Module R M] :
    ∃ (J : Type (max u w)) (_ : SmallCategory J) (_ : IsFiltered J)
      (pres : ColimitPresentation J (ModuleCat.of.{max u w} R (ULift.{u} M))),
        ∀ j, Module.FinitePresentation R (pres.diag.obj j) := by
  let QM : ModuleCat.{max u w} R := ModuleCat.of.{max u w} R (ULift.{u} M)
  -- Reuse the owner theorem in the smallest universe where both the ring and the target module
  -- already live, avoiding the larger source-universe parameters from the main statement.
  simpa [CategoryTheory.ObjectProperty.ind] using
    (show CategoryTheory.ObjectProperty.ind.{max u w}
        (fun N : ModuleCat.{max u w} R ↦ Module.FinitePresentation R N)
        QM from
      (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented.{u, max u w}
        (R := R) (M := QM)))

/-- Helper for Lemma 10.89.4: right tensoring by `Q` sends identity morphisms in `ModuleCat` to
identity morphisms. -/
private lemma rTensor_functor_unbundled_map_id
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {Q : Type z} [AddCommGroup Q] [Module R Q] :
    ModuleCat.ofHom ((LinearMap.id : V →ₗ[R] V).rTensor Q) =
      𝟙 (ModuleCat.of.{max v z} R (V ⊗[R] Q)) := by
  -- The tensor functor acts as the identity on pure tensors, hence on the whole tensor product.
  apply ModuleCat.hom_ext
  ext x y
  rfl

/-- Helper for Lemma 10.89.4: right tensoring by `Q` is compatible with composition in
`ModuleCat`. -/
private lemma rTensor_functor_unbundled_map_comp
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type v} [AddCommGroup W] [Module R W]
    {X : Type v} [AddCommGroup X] [Module R X]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (f : V →ₗ[R] W) (g : W →ₗ[R] X) :
    ModuleCat.ofHom ((g.comp f).rTensor Q) =
      (ModuleCat.ofHom (f.rTensor Q) : ModuleCat.of.{max v z} R (V ⊗[R] Q) ⟶
          ModuleCat.of.{max v z} R (W ⊗[R] Q)) ≫
        ModuleCat.ofHom (g.rTensor Q) := by
  -- Both composites act identically on pure tensors, so the corresponding morphisms agree.
  apply ModuleCat.hom_ext
  ext x y
  rfl

/-- Helper for Lemma 10.89.4: right tensoring by a fixed module defines a universe-flexible
endofunctor on `ModuleCat`. -/
private def rTensor_functor_unbundled
    {R : Type u} [CommRing R]
    (Q : Type z) [AddCommGroup Q] [Module R Q] :
    ModuleCat.{v} R ⥤ ModuleCat.{max v z} R where
  obj N := ModuleCat.of.{max v z} R (N ⊗[R] Q)
  map φ := ModuleCat.ofHom (φ.hom.rTensor Q)
  map_id X := rTensor_functor_unbundled_map_id (R := R) (V := X) (Q := Q)
  map_comp f g := rTensor_functor_unbundled_map_comp (R := R) (Q := Q) f.hom g.hom

/-- Helper for Lemma 10.89.4: left tensoring by `Q` sends identity morphisms in `ModuleCat` to
identity morphisms. -/
private lemma lTensor_functor_unbundled_map_id
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {Q : Type z} [AddCommGroup Q] [Module R Q] :
    ModuleCat.ofHom ((LinearMap.id : V →ₗ[R] V).lTensor Q) =
      𝟙 (ModuleCat.of.{max v z} R (Q ⊗[R] V)) := by
  -- The left-tensor identity fixes each pure tensor, hence the whole tensor product.
  apply ModuleCat.hom_ext
  ext q v
  rfl

/-- Helper for Lemma 10.89.4: left tensoring by `Q` is compatible with composition in
`ModuleCat`. -/
private lemma lTensor_functor_unbundled_map_comp
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type v} [AddCommGroup W] [Module R W]
    {X : Type v} [AddCommGroup X] [Module R X]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (f : V →ₗ[R] W) (g : W →ₗ[R] X) :
    ModuleCat.ofHom ((g.comp f).lTensor Q) =
      (ModuleCat.ofHom (f.lTensor Q) : ModuleCat.of.{max v z} R (Q ⊗[R] V) ⟶
          ModuleCat.of.{max v z} R (Q ⊗[R] W)) ≫
        ModuleCat.ofHom (g.lTensor Q) := by
  -- Both sides act on pure tensors by applying `f` and then `g` to the right tensor factor.
  apply ModuleCat.hom_ext
  ext q v
  rfl

/-- Helper for Lemma 10.89.4: left tensoring by a fixed module defines a universe-flexible
functor on `ModuleCat`. -/
private def lTensor_functor_unbundled
    {R : Type u} [CommRing R]
    (Q : Type z) [AddCommGroup Q] [Module R Q] :
    ModuleCat.{v} R ⥤ ModuleCat.{max v z} R where
  obj N := ModuleCat.of.{max v z} R (Q ⊗[R] N)
  map φ := ModuleCat.ofHom (φ.hom.lTensor Q)
  map_id X := lTensor_functor_unbundled_map_id (R := R) (V := X) (Q := Q)
  map_comp f g := lTensor_functor_unbundled_map_comp (R := R) (Q := Q) f.hom g.hom

/-- Helper for Lemma 10.89.4: the forgetful functor from the lifted `ModuleCat` universe preserves
the filtered colimits used after ULifting the presentation. -/
private lemma modulecat_forget_preserves_colimit_filtered_lifted
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat.{max v z} R) :
    PreservesColimit F (forget (ModuleCat.{max v z} R)) := by
  -- Route correction: direct instance search for `forget (ModuleCat.{max v z} R)` is too rigid
  -- in the shape universe, so split the forgetful functor through `AddCommGrpCat`.
  letI : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat.{max v z}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max v z})
  -- The module-to-additive-group forgetful functor preserves these colimits, and the shrunk
  -- additive forgetful preservation supplies the second half of the composite.
  have hcomp : PreservesColimit F
      (forget₂ (ModuleCat.{max v z} R) AddCommGrpCat.{max v z} ⋙
        forget AddCommGrpCat.{max v z}) := inferInstance
  -- The composite is definitionally the ordinary forgetful functor from modules to types.
  simpa using hcomp

/-- Helper for Lemma 10.89.4: two maps out of a quotient of a finite free module agree once their
composites with the quotient map agree. -/
private lemma linearMap_eq_of_comp_mkQ_eq
    {R : Type u} [CommRing R]
    {n : ℕ} {K : Submodule R (Fin n → R)} {P : Type (max u w)}
    [AddCommGroup P] [Module R P]
    {f g : ((Fin n → R) ⧸ K) →ₗ[R] P}
    (h : f.comp (Submodule.mkQ K) = g.comp (Submodule.mkQ K)) :
    f = g := by
  -- The quotient map is surjective, so it is enough to compare both maps on representatives.
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K q
  simpa using LinearMap.congr_fun h x

/-- Helper for Lemma 10.89.4: a map from a finite free module into a filtered colimit factors
through one stage. -/
private lemma linearMap_from_fin_factor_through_filtered_colimit_stage
    {R : Type u} [CommRing R]
    {J : Type (max u w)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u w} R)
    (c : Cocone F) (hc : IsColimit c)
    (n : ℕ) (f : (Fin n → R) →ₗ[R] c.pt) :
    ∃ (j : J) (g : (Fin n → R) →ₗ[R] F.obj j), (c.ι.app j).hom.comp g = f := by
  classical
  letI : PreservesColimit F (forget (ModuleCat.{max u w} R)) :=
    modulecat_forget_preserves_colimit_filtered (R := R) F
  let hc :
      IsColimit ((forget (ModuleCat.{max u w} R)).mapCocone c) :=
    isColimitOfPreserves (forget (ModuleCat.{max u w} R)) hc
  choose j x hx using fun i : Fin n =>
    Types.jointly_surjective_of_isColimit hc (f ((Pi.basisFun R (Fin n)) i))
  obtain ⟨k, ⟨u⟩⟩ : ∃ k : J, Nonempty (∀ i : Fin n, j i ⟶ k) := by
    -- Filteredness merges the finitely many basis lifts into one common stage.
    have : ∃ k : J, ∀ i : Fin n, Nonempty (j i ⟶ k) := by
      simpa using IsFiltered.sup_objs_exists (Finset.univ.image j)
    simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using this
  let g : (Fin n → R) →ₗ[R] F.obj k :=
    { toFun := fun z => ∑ i, z i • (F.map (u i)) (x i)
      map_add' := by
        intro z z'
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro r z
        simp [Finset.smul_sum, mul_smul] }
  refine ⟨k, g, ?_⟩
  -- The constructed map matches `f` on the standard basis, hence everywhere.
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  have htransport :
      (c.ι.app k).hom ((F.map (u i)) (x i)) =
        (c.ι.app (j i)).hom (x i) := by
    -- Naturality transports the chosen lift of the `i`-th basis vector to the common stage.
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (c.w (u i))) (x i)
  have hx_i' : (c.ι.app (j i)).hom (x i) = f ((Pi.basisFun R (Fin n)) i) := by
    simpa using hx i
  have hg_basis : g ((Pi.basisFun R (Fin n)) i) = (F.map (u i)) (x i) := by
    simp [g, Pi.basisFun_apply]
  calc
    ((c.ι.app k).hom.comp g) ((Pi.basisFun R (Fin n)) i)
        = (c.ι.app k).hom (g ((Pi.basisFun R (Fin n)) i)) := by
            rfl
    _ = (c.ι.app k).hom ((F.map (u i)) (x i)) := by
          rw [hg_basis]
    _ = f ((Pi.basisFun R (Fin n)) i) := htransport.trans hx_i'

/-- Helper for Lemma 10.89.4: if a finitely generated relation module already vanishes in the
colimit, then it vanishes at some later stage. -/
private lemma fg_submodule_eventually_le_ker_of_colimit_vanishing
    {R : Type u} [CommRing R]
    {n : ℕ} {K : Submodule R (Fin n → R)} (hK : K.FG)
    {J : Type (max u w)} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u w} R)
    (c : Cocone F) (hc : IsColimit c)
    {i : J}
    (g : (Fin n → R) →ₗ[R] F.obj i)
    (hg : K ≤ LinearMap.ker ((c.ι.app i).hom.comp g)) :
    ∃ (j : J) (u : i ⟶ j), K ≤ LinearMap.ker ((F.map u).hom.comp g) := by
  letI : Module.Finite R K := Module.Finite.of_fg hK
  let a : ModuleCat.of R (ULift.{w} K) ⟶ F.obj i :=
    ModuleCat.ofHom (((g.comp K.subtype).comp ULift.moduleEquiv.toLinearMap))
  let b : ModuleCat.of R (ULift.{w} K) ⟶ F.obj i := 0
  have ha_cocone : a ≫ c.ι.app i = b ≫ c.ι.app i := by
    apply ModuleCat.hom_ext
    ext x
    -- The restricted map is zero in the colimit because every chosen relation already vanishes.
    have hx0 : (c.ι.app i).hom (g (K.subtype x.down)) = 0 := hg x.down.property
    simpa [a, b, Category.assoc] using hx0
  let colimDesc : c.pt ⟶ colimit F := hc.desc (colimit.cocone F)
  have ha_colim : a ≫ colimit.ι F i = b ≫ colimit.ι F i := by
    -- Compose the cocone equality into the chosen colimit to use the existing eventual-equality
    -- lemma from Lemma 10.11.1.
    have hdesc :=
      congrArg (fun k ↦ k ≫ colimDesc) ha_cocone
    calc
      a ≫ colimit.ι F i = a ≫ c.ι.app i ≫ colimDesc := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ a ≫ k) (hc.fac (colimit.cocone F) i).symm
      _ = b ≫ c.ι.app i ≫ colimDesc := by
        simpa [Category.assoc] using hdesc
      _ = b ≫ colimit.ι F i := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ b ≫ k) (hc.fac (colimit.cocone F) i)
  obtain ⟨j, u, hu⟩ :=
    eventually_equal_of_hom_to_colimit_of_finite_module
      (R := R) (N := ModuleCat.of R (ULift.{w} K)) F a b ha_colim
  refine ⟨j, u, ?_⟩
  intro x hx
  let xK : K := ⟨x, hx⟩
  have hxu :
      ((a ≫ F.map u).hom) (ULift.up xK) =
        ((b ≫ F.map u).hom) (ULift.up xK) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hu) (ULift.up xK)
  -- Evaluating the eventual equality on one relation yields the desired kernel bound.
  simpa [a, b, Category.assoc] using hxu

/-- Helper for Lemma 10.89.4: a map from a finitely presented module into the common-universe
filtered presentation of `M` factors through one stage after descending along the quotient
presentation of the source. -/
private lemma exists_factorization_through_stage_of_finitePresentation_unbundled
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    {J : Type (max u w)} [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J (ModuleCat.of.{max u w} R (ULift.{u} M)))
    (f : P →ₗ[R] M) :
    ∃ (j : J) (f0 : P →ₗ[R] pres.diag.obj j),
      moduleEquiv.symm.toLinearMap.comp f = (pres.ι.app j).hom.comp f0 := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin (R := R) (M := P)
  let fQ : ((Fin n → R) ⧸ K) →ₗ[R] ULift.{u} M :=
    moduleEquiv.symm.toLinearMap.comp (f.comp e.symm.toLinearMap)
  let fFree : (Fin n → R) →ₗ[R] ULift.{u} M := fQ.comp (Submodule.mkQ K)
  obtain ⟨j, g, hg⟩ :=
    linearMap_from_fin_factor_through_filtered_colimit_stage
      (R := R) (F := pres.diag) pres.cocone pres.isColimit n fFree
  have hvanish : K ≤ LinearMap.ker ((pres.ι.app j).hom.comp g) := by
    intro x hx
    -- The free-stage factorization kills every relation because the quotient map sends it to zero.
    have hxq : (Submodule.mkQ K) x = 0 := by
      simp [hx]
    have hxg :
        ((pres.ι.app j).hom.comp g) x = fQ ((Submodule.mkQ K) x) := by
      simpa [fFree] using LinearMap.congr_fun hg x
    rw [hxq] at hxg
    simpa using hxg
  obtain ⟨j', w, hw⟩ :=
    fg_submodule_eventually_le_ker_of_colimit_vanishing
      (R := R) (hK := hK) (F := pres.diag) pres.cocone pres.isColimit (g := g) hvanish
  let f0Q : ((Fin n → R) ⧸ K) →ₗ[R] pres.diag.obj j' :=
    K.liftQ ((pres.diag.map w).hom.comp g) hw
  let f0 : P →ₗ[R] pres.diag.obj j' := f0Q.comp e.toLinearMap
  have hw_nat :
      (pres.ι.app j').hom.comp (pres.diag.map w).hom = (pres.ι.app j).hom := by
    simpa using congrArg ModuleCat.Hom.hom (pres.w w)
  have hg_stage :
      (pres.ι.app j).hom.comp g = fQ.comp (Submodule.mkQ K) := by
    simpa [fFree] using hg
  have hstage_free :
      (pres.ι.app j').hom.comp ((pres.diag.map w).hom.comp g) = fQ.comp (Submodule.mkQ K) := by
    -- Naturality pushes the free-stage factorization forward to the later stage where the
    -- relations vanish.
    have hcomp :
        (pres.ι.app j').hom.comp ((pres.diag.map w).hom.comp g) =
          ((pres.ι.app j').hom.comp (pres.diag.map w).hom).comp g := by
      rfl
    have hnat_comp :
        ((pres.ι.app j').hom.comp (pres.diag.map w).hom).comp g =
          (pres.ι.app j).hom.comp g := by
      simpa [LinearMap.comp_assoc] using congrArg (fun k ↦ k.comp g) hw_nat
    exact hcomp.trans (hnat_comp.trans hg_stage)
  have hf0Q :
      (pres.ι.app j').hom.comp f0Q = fQ := by
    apply linearMap_eq_of_comp_mkQ_eq
    -- The quotient lift agrees with the original quotient map after composing with `mkQ`.
    simpa [f0Q, LinearMap.comp_assoc] using hstage_free
  refine ⟨j', f0, ?_⟩
  -- Finally descend from the quotient presentation of `P` back along the chosen equivalence.
  have hsource :
      moduleEquiv.symm.toLinearMap.comp f = fQ.comp e.toLinearMap := by
    ext x
    simp [fQ, LinearMap.comp_assoc]
  have hfactor :
    fQ.comp e.toLinearMap = ((pres.ι.app j').hom.comp f0Q).comp e.toLinearMap := by
    simpa [LinearMap.comp_assoc] using congrArg (fun k ↦ k.comp e.toLinearMap) hf0Q.symm
  exact hsource.trans (hfactor.trans rfl)

/-- Helper for Lemma 10.89.4: transporting through `TensorProduct.congr` removes the `ULift`
inserted by `ModuleCat.uliftFunctor.map` before left tensoring. -/
private lemma uliftFunctorPreservesColimitsOfShape
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{z, v} R) := by
  let e :
      ModuleCat.uliftFunctor.{z, v} R ⋙
          forget₂ (ModuleCat.{max v z} R) AddCommGrpCat.{max v z} ≅
        forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ AddCommGrpCat.uliftFunctor.{z, v} := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro X Y f
    ext x
    rfl
  letI : PreservesColimitsOfShape J
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ AddCommGrpCat.uliftFunctor.{z, v}) := by
    infer_instance
  letI : PreservesColimitsOfShape J
      (ModuleCat.uliftFunctor.{z, v} R ⋙
        forget₂ (ModuleCat.{max v z} R) AddCommGrpCat.{max v z}) :=
    preservesColimitsOfShape_of_natIso e.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (ModuleCat.uliftFunctor.{z, v} R)
    (forget₂ (ModuleCat.{max v z} R) AddCommGrpCat.{max v z})

/-- Helper for Lemma 10.89.4: transporting through `TensorProduct.congr` removes the `ULift`
inserted by `ModuleCat.uliftFunctor.map` before left tensoring. -/
private lemma uliftFunctor_map_lTensor_transport
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type v} [AddCommGroup W] [Module R W]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (f : V →ₗ[R] W) :
    let eV : Q ⊗[R] ULift.{z} V ≃ₗ[R] Q ⊗[R] V :=
      TensorProduct.congr (LinearEquiv.refl R Q)
        (ULift.moduleEquiv : ULift.{z} V ≃ₗ[R] V)
    let eW : Q ⊗[R] ULift.{z} W ≃ₗ[R] Q ⊗[R] W :=
      TensorProduct.congr (LinearEquiv.refl R Q)
        (ULift.moduleEquiv : ULift.{z} W ≃ₗ[R] W)
    eW.toLinearMap.comp
        ((((ModuleCat.uliftFunctor.{z, v} R).map (ModuleCat.ofHom f)).hom).lTensor Q) =
      (f.lTensor Q).comp eV.toLinearMap := by
  -- Both sides agree on pure tensors, so the transported maps coincide.
  ext q v
  rfl

/-- Helper for Lemma 10.89.4: transporting through `TensorProduct.congr` removes `ULift` from
both tensor factors after applying `ModuleCat.uliftFunctor` to the right factor. -/
private lemma uliftFunctor_map_lTensor_bothFactors_transport
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type v} [AddCommGroup W] [Module R W]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (f : V →ₗ[R] W) :
    let eV : ULift.{v} Q ⊗[R] ULift.{z} V ≃ₗ[R] Q ⊗[R] V :=
      TensorProduct.congr
        (ULift.moduleEquiv : ULift.{v} Q ≃ₗ[R] Q)
        (ULift.moduleEquiv : ULift.{z} V ≃ₗ[R] V)
    let eW : ULift.{v} Q ⊗[R] ULift.{z} W ≃ₗ[R] Q ⊗[R] W :=
      TensorProduct.congr
        (ULift.moduleEquiv : ULift.{v} Q ≃ₗ[R] Q)
        (ULift.moduleEquiv : ULift.{z} W ≃ₗ[R] W)
    eW.toLinearMap.comp
        ((((ModuleCat.uliftFunctor.{z, v} R).map (ModuleCat.ofHom f)).hom).lTensor
          (ULift.{v} Q)) =
      (f.lTensor Q).comp eV.toLinearMap := by
  -- Both sides send a pure tensor of lifted elements to `q ⊗ f v`.
  ext q v
  rfl

/-- Helper for Lemma 10.89.4: tensoring on the left and on the right commute for linear maps on
different factors. -/
private lemma lTensor_rTensor_apply
    {R : Type u} [CommRing R]
    {A : Type w} [AddCommGroup A] [Module R A]
    {B : Type z} [AddCommGroup B] [Module R B]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type v} [AddCommGroup W] [Module R W]
    (i : A →ₗ[R] B) (f : V →ₗ[R] W) (z : A ⊗[R] V) :
    ((f.lTensor B) ((i.rTensor V) z)) = ((i.rTensor W) ((f.lTensor A) z)) := by
  -- Both composites are the same tensor-product map, so they agree on every tensor element.
  calc
    ((f.lTensor B) ((i.rTensor V) z))
        = (((f.lTensor B).comp (i.rTensor V)) z) := rfl
    _ = (((i.rTensor W).comp (f.lTensor A)) z) := by
          congr 1
          calc
            (f.lTensor B).comp (i.rTensor V) = TensorProduct.map i f := by
              simpa using (LinearMap.lTensor_comp_rTensor (f := i) (g := f))
            _ = (i.rTensor W).comp (f.lTensor A) := by
              simpa using (LinearMap.rTensor_comp_lTensor (f := i) (g := f)).symm
    _ = ((i.rTensor W) ((f.lTensor A) z)) := rfl

/-- Helper for Lemma 10.89.4: fixing the left tensor factor of a cocone over `Q ⊗ -` gives a
cocone over the original diagram. -/
@[reducible]
private noncomputable def lTensor_fixedLeftCocone
    {R : Type u} [CommRing R]
    {J : Type w} [SmallCategory J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    (s : Cocone (pres.diag ⋙ lTensor_functor_unbundled (R := R) Q)) (q : Q) :
    Cocone pres.diag where
  pt := s.pt
  ι :=
    { app := fun j =>
        ModuleCat.ofHom
          { toFun := fun v => (s.ι.app j).hom (q ⊗ₜ[R] v)
            map_add' := by
              intro v v'
              simpa [TensorProduct.tmul_add] using
                map_add (s.ι.app j).hom (q ⊗ₜ[R] v) (q ⊗ₜ[R] v')
            map_smul' := by
              intro r v
              simpa [TensorProduct.smul_tmul'] using
                map_smul (s.ι.app j).hom r (q ⊗ₜ[R] v) }
      naturality := by
        intro i j f
        -- Naturality of the tensorized cocone, evaluated on `q ⊗ₜ v`, is exactly the
        -- compatibility condition for this fixed-left-factor cocone.
        apply ModuleCat.hom_ext
        ext v
        have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (s.w f)) (q ⊗ₜ[R] v)
        simpa [lTensor_functor_unbundled] using h }

/-- Helper for Lemma 10.89.4: the descriptor from the original colimit to a fixed-left-factor
cocone evaluates on stage elements as the tensorized cocone leg. -/
private lemma lTensor_fixedLeftCocone_desc_apply
    {R : Type u} [CommRing R]
    {J : Type w} [SmallCategory J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    (s : Cocone (pres.diag ⋙ lTensor_functor_unbundled (R := R) Q))
    (q : Q) (j : J) (m : pres.diag.obj j) :
    (pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q)).hom
        ((pres.ι.app j).hom m) =
      (s.ι.app j).hom (q ⊗ₜ[R] m) := by
  -- This is the original colimit's fac equation, evaluated on a stage element.
  have h :=
    LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
      (pres.isColimit.fac (lTensor_fixedLeftCocone (R := R) pres s q) j)) m
  simpa [lTensor_fixedLeftCocone, Category.assoc] using h

/-- Helper for Lemma 10.89.4: the fixed-left-factor descriptor is additive in the fixed tensor
factor, evaluated at a colimit element. -/
private lemma lTensor_fixedLeftCocone_desc_add_apply
    {R : Type u} [CommRing R]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    (s : Cocone (pres.diag ⋙ lTensor_functor_unbundled (R := R) Q))
    (q₁ q₂ : Q) (m : M) :
    (pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s (q₁ + q₂))).hom m =
      ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q₁)).hom m : s.pt) +
        ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q₂)).hom m : s.pt) := by
  let rhs : M →ₗ[R] s.pt :=
    { toFun := fun m =>
        ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q₁)).hom m : s.pt) +
          ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q₂)).hom m : s.pt)
      map_add' := by
        intro m₁ m₂
        simp only [map_add]
        abel
      map_smul' := by
        intro r m
        rw [map_smul, map_smul]
        exact (smul_add r
          ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q₁)).hom m)
          ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q₂)).hom m)).symm }
  have hcat :
      pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s (q₁ + q₂)) =
        ModuleCat.ofHom rhs := by
    -- Compare the two candidate maps out of the original colimit after every stage leg.
    apply pres.isColimit.hom_ext
    intro j
    apply ModuleCat.hom_ext
    ext mj
    have h0 :
        ((pres.ι.app j ≫
              pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s (q₁ + q₂))).hom) mj =
          (s.ι.app j).hom ((q₁ + q₂) ⊗ₜ[R] mj) :=
      lTensor_fixedLeftCocone_desc_apply (R := R) pres s (q₁ + q₂) j mj
    have h1 :
        (s.ι.app j).hom ((q₁ + q₂) ⊗ₜ[R] mj) =
          (s.ι.app j).hom (q₁ ⊗ₜ[R] mj) + (s.ι.app j).hom (q₂ ⊗ₜ[R] mj) := by
      simpa [TensorProduct.add_tmul] using
        map_add (s.ι.app j).hom (q₁ ⊗ₜ[R] mj) (q₂ ⊗ₜ[R] mj)
    have h2 :
        rhs ((pres.ι.app j).hom mj) =
          (s.ι.app j).hom (q₁ ⊗ₜ[R] mj) + (s.ι.app j).hom (q₂ ⊗ₜ[R] mj) := by
      dsimp [rhs]
      exact congrArg₂ (fun a b => a + b)
        (lTensor_fixedLeftCocone_desc_apply (R := R) pres s q₁ j mj)
        (lTensor_fixedLeftCocone_desc_apply (R := R) pres s q₂ j mj)
    exact h0.trans (h1.trans h2.symm)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcat) m

/-- Helper for Lemma 10.89.4: the fixed-left-factor descriptor is linear in the fixed tensor
factor, evaluated at a colimit element. -/
private lemma lTensor_fixedLeftCocone_desc_smul_apply
    {R : Type u} [CommRing R]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    (s : Cocone (pres.diag ⋙ lTensor_functor_unbundled (R := R) Q))
    (r : R) (q : Q) (m : M) :
    (pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s (r • q))).hom m =
      r • ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q)).hom m : s.pt) := by
  let rhs : M →ₗ[R] s.pt :=
    { toFun := fun m =>
        r • ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q)).hom m : s.pt)
      map_add' := by
        intro m₁ m₂
        simp only [map_add, smul_add]
      map_smul' := by
        intro a m
        rw [map_smul]
        exact smul_comm r a
          ((pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q)).hom m) }
  have hcat :
      pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s (r • q)) =
        ModuleCat.ofHom rhs := by
    -- Compare the two candidate maps out of the original colimit after every stage leg.
    apply pres.isColimit.hom_ext
    intro j
    apply ModuleCat.hom_ext
    ext mj
    have h0 :
        ((pres.ι.app j ≫
              pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s (r • q))).hom) mj =
          (s.ι.app j).hom ((r • q) ⊗ₜ[R] mj) :=
      lTensor_fixedLeftCocone_desc_apply (R := R) pres s (r • q) j mj
    have h1 :
        (s.ι.app j).hom ((r • q) ⊗ₜ[R] mj) =
          r • (s.ι.app j).hom (q ⊗ₜ[R] mj) := by
      simpa [TensorProduct.smul_tmul'] using
        map_smul (s.ι.app j).hom r (q ⊗ₜ[R] mj)
    have h2 :
        rhs ((pres.ι.app j).hom mj) =
          r • (s.ι.app j).hom (q ⊗ₜ[R] mj) := by
      dsimp [rhs]
      exact congrArg (fun x => r • x)
        (lTensor_fixedLeftCocone_desc_apply (R := R) pres s q j mj)
    exact h0.trans (h1.trans h2.symm)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcat) m

/-- Helper for Lemma 10.89.4: a competing map with the tensorized fac equations agrees with the
fixed-left-factor descriptor on each pure left tensor factor. -/
private lemma lTensor_fixedLeftCocone_desc_eq_of_fac_apply
    {R : Type u} [CommRing R]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    (s : Cocone (pres.diag ⋙ lTensor_functor_unbundled (R := R) Q))
    (m : ((lTensor_functor_unbundled (R := R) Q).mapCocone pres.cocone).pt ⟶ s.pt)
    (hm : ∀ j, ((lTensor_functor_unbundled (R := R) Q).mapCocone pres.cocone).ι.app j ≫ m =
      s.ι.app j)
    (q : Q) (x : M) :
    m.hom (q ⊗ₜ[R] x) =
      (pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q)).hom x := by
  let candidate : M →ₗ[R] s.pt :=
    { toFun := fun x => m.hom (q ⊗ₜ[R] x)
      map_add' := by
        intro x y
        rw [TensorProduct.tmul_add]
        exact map_add m.hom (q ⊗ₜ[R] x) (q ⊗ₜ[R] y)
      map_smul' := by
        intro r x
        simpa [TensorProduct.smul_tmul'] using
          map_smul m.hom r (q ⊗ₜ[R] x) }
  have hcat :
      ModuleCat.ofHom candidate =
        pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q) := by
    -- The competing map and the descriptor have the same composites with every original stage.
    apply pres.isColimit.hom_ext
    intro j
    apply ModuleCat.hom_ext
    ext xj
    have hfac :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hm j)) (q ⊗ₜ[R] xj)
    have h0 :
        ((pres.ι.app j ≫ ModuleCat.ofHom candidate).hom) xj =
          m.hom (((pres.ι.app j).hom.lTensor Q) (q ⊗ₜ[R] xj)) := rfl
    have h1 :
        m.hom (((pres.ι.app j).hom.lTensor Q) (q ⊗ₜ[R] xj)) =
          (s.ι.app j).hom (q ⊗ₜ[R] xj) := by
      simpa [lTensor_functor_unbundled] using hfac
    have h2 :
        (s.ι.app j).hom (q ⊗ₜ[R] xj) =
          ((pres.ι.app j ≫
            pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q)).hom) xj :=
      (lTensor_fixedLeftCocone_desc_apply (R := R) pres s q j xj).symm
    exact h0.trans (h1.trans h2)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcat) x

/-- Helper for Lemma 10.89.4: the mixed-universe left-tensor functor sends a filtered colimit
presentation in `ModuleCat` to a colimit presentation. -/
private noncomputable def lTensor_functor_unbundled_mapCocone_isColimit
    {R : Type u} [CommRing R]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M)) :
    IsColimit ((lTensor_functor_unbundled (R := R) Q).mapCocone pres.cocone) := by
  -- The descriptor is obtained by currying: for each `q : Q`, the original colimit gives the
  -- unique map out of `M` whose stagewise values are `v ↦ s.ι.app j (q ⊗ₜ v)`.
  refine
    { desc := ?desc
      fac := ?fac
      uniq := ?uniq }
  · intro s
    refine ModuleCat.ofHom (TensorProduct.lift ?_)
    refine
      { toFun := fun q => (pres.isColimit.desc (lTensor_fixedLeftCocone (R := R) pres s q)).hom
        map_add' := ?_
        map_smul' := ?_ }
    · intro q₁ q₂
      apply LinearMap.ext
      intro m
      exact lTensor_fixedLeftCocone_desc_add_apply (R := R) pres s q₁ q₂ m
    · intro r q
      apply LinearMap.ext
      intro m
      exact lTensor_fixedLeftCocone_desc_smul_apply (R := R) pres s r q m
  · intro s j
    -- On pure tensors, the constructed descriptor has exactly the prescribed cocone leg.
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext q m
    simpa using lTensor_fixedLeftCocone_desc_apply (R := R) pres s q j m
  · intro s m hm
    -- A map out of the tensor product is determined on pure tensors; fixing the left factor
    -- reduces uniqueness to the original colimit uniqueness.
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext q x
    exact lTensor_fixedLeftCocone_desc_eq_of_fac_apply (R := R) pres s m hm q x

/-- Helper for Lemma 10.89.4: if a left-tensor element vanishes in the tensorized filtered
colimit, then it already vanishes at some later stage. -/
private lemma exists_later_stage_lTensor_eq_zero_unbundled
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    {j : J} {y : Q ⊗[R] pres.diag.obj j}
    (hy : ((pres.ι.app j).hom.lTensor Q) y = 0) :
    ∃ (j' : J) (w : j ⟶ j'), ((pres.diag.map w).hom.lTensor Q) y = 0 := by
  -- Lift both tensor factors into the common universe `max v z`; the same-universe colimit
  -- helper then gives eventual vanishing, and the final step transports back through `ULift`.
  letI : PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{z, v} R) :=
    uliftFunctorPreservesColimitsOfShape (R := R) (J := J)
  let presU : ColimitPresentation J (ModuleCat.of.{max v z} R (ULift.{z} M)) :=
    ColimitPresentation.map pres (ModuleCat.uliftFunctor.{z, v} R)
  let QL : Type (max v z) := ULift.{v} Q
  let eStage : QL ⊗[R] presU.diag.obj j ≃ₗ[R] Q ⊗[R] pres.diag.obj j :=
    TensorProduct.congr
      (ULift.moduleEquiv : ULift.{v} Q ≃ₗ[R] Q)
      (ULift.moduleEquiv : ULift.{z} (pres.diag.obj j) ≃ₗ[R] pres.diag.obj j)
  let eTarget : QL ⊗[R] ULift.{z} M ≃ₗ[R] Q ⊗[R] M :=
    TensorProduct.congr
      (ULift.moduleEquiv : ULift.{v} Q ≃ₗ[R] Q)
      (ULift.moduleEquiv : ULift.{z} M ≃ₗ[R] M)
  let yU : QL ⊗[R] presU.diag.obj j := eStage.symm y
  have hleg_transport :
      eTarget.toLinearMap.comp ((presU.ι.app j).hom.lTensor QL) =
        ((pres.ι.app j).hom.lTensor Q).comp eStage.toLinearMap := by
    -- The lifted leg is the original leg with `ULift` on both tensor factors.
    simpa [presU, QL, eStage, eTarget] using
      (uliftFunctor_map_lTensor_bothFactors_transport (R := R) (Q := Q) ((pres.ι.app j).hom))
  have hyU : ((presU.ι.app j).hom.lTensor QL) yU = 0 := by
    apply eTarget.injective
    calc
      eTarget (((presU.ι.app j).hom.lTensor QL) yU)
          = ((pres.ι.app j).hom.lTensor Q) (eStage yU) := by
              simpa [LinearMap.comp_apply] using congrArg (fun k ↦ k yU) hleg_transport
      _ = 0 := by
            simpa [yU] using hy
  let T : ModuleCat.{max v z} R ⥤ ModuleCat.{max v z} R :=
    lTensor_functor_unbundled (R := R) QL
  let tensorCocone : Cocone (presU.diag ⋙ T) := T.mapCocone presU.cocone
  have htensorCocone : IsColimit tensorCocone := by
    simpa [T, tensorCocone] using
      (lTensor_functor_unbundled_mapCocone_isColimit (R := R) (Q := QL) presU)
  letI : PreservesColimit (presU.diag ⋙ T) (forget (ModuleCat.{max v z} R)) :=
    modulecat_forget_preserves_colimit_filtered_lifted (R := R) (F := presU.diag ⋙ T)
  have hUnderlying :
      IsColimit ((forget (ModuleCat.{max v z} R)).mapCocone tensorCocone) :=
    isColimitOfPreserves (forget (ModuleCat.{max v z} R)) htensorCocone
  have hy_eq :
      ((forget (ModuleCat.{max v z} R)).map (tensorCocone.ι.app j)) yU =
        ((forget (ModuleCat.{max v z} R)).map (tensorCocone.ι.app j)) (0 : QL ⊗[R] presU.diag.obj j) := by
    simpa [tensorCocone, T, QL] using hyU
  obtain ⟨j', w, hwU⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hUnderlying yU 0).1 hy_eq
  let eLater : QL ⊗[R] presU.diag.obj j' ≃ₗ[R] Q ⊗[R] pres.diag.obj j' :=
    TensorProduct.congr
      (ULift.moduleEquiv : ULift.{v} Q ≃ₗ[R] Q)
      (ULift.moduleEquiv : ULift.{z} (pres.diag.obj j') ≃ₗ[R] pres.diag.obj j')
  have hmap_transport :
      eLater.toLinearMap.comp ((presU.diag.map w).hom.lTensor QL) =
        ((pres.diag.map w).hom.lTensor Q).comp eStage.toLinearMap := by
    -- The same transport comparison identifies the lifted transition with the original one.
    apply LinearMap.ext
    intro t
    refine t.induction_on ?_ ?_ ?_
    · simp
    · intro q x
      rfl
    · intro x y hx hy
      rw [map_add, map_add]
      rw [hx, hy]
  have hwU_zero : ((presU.diag.map w).hom.lTensor QL) yU = 0 := by
    simpa [T, tensorCocone, QL, lTensor_functor_unbundled] using hwU
  refine ⟨j', w, ?_⟩
  calc
    ((pres.diag.map w).hom.lTensor Q) y
        = eLater (((presU.diag.map w).hom.lTensor QL) yU) := by
            symm
            simpa [LinearMap.comp_apply, yU] using congrArg (fun k ↦ k yU) hmap_transport
    _ = 0 := by
          simpa using congrArg (fun t ↦ eLater t) hwU_zero

/-- Helper for Lemma 10.89.4: commutation with `TensorProduct.comm` converts eventual vanishing of
right-tensor maps to the left-tensor stabilization theorem from Lemma 10.88.3. -/
private lemma exists_later_stage_rTensor_eq_zero_via_lTensor_comm
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    {j : J} {y : pres.diag.obj j ⊗[R] Q}
    (hy : ((pres.ι.app j).hom.rTensor Q) y = 0) :
    ∃ (j' : J) (w : j ⟶ j'), ((pres.diag.map w).hom.rTensor Q) y = 0 := by
  let ycomm : Q ⊗[R] pres.diag.obj j := TensorProduct.comm R _ _ y
  have hy_comm_zero : ((pres.ι.app j).hom.lTensor Q) ycomm = 0 := by
    -- Commute the right-tensor vanishing hypothesis to the left-tensor setting of
    -- Lemma `10.88.3`.
    have hy_comm :
        TensorProduct.comm R Q M (((pres.ι.app j).hom.lTensor Q) ycomm) = 0 := by
      calc
        TensorProduct.comm R Q M (((pres.ι.app j).hom.lTensor Q) ycomm)
            = ((pres.ι.app j).hom.rTensor Q) y := by
                simpa [ycomm] using
                  (LinearMap.rTensor_comm (N := Q) ((pres.ι.app j).hom) ycomm).symm
        _ = 0 := hy
    exact (TensorProduct.comm R Q M).injective (by simpa using hy_comm)
  obtain ⟨j', w, hw_zero⟩ :=
    exists_later_stage_lTensor_eq_zero_unbundled (R := R) (Q := Q) (pres := pres) (j := j)
      hy_comm_zero
  refine ⟨j', w, ?_⟩
  -- Commute the later left-tensor vanishing back to the desired right-tensor equality.
  calc
    ((pres.diag.map w).hom.rTensor Q) y
        = TensorProduct.comm R Q (pres.diag.obj j')
            (((pres.diag.map w).hom.lTensor Q) ycomm) := by
              simpa [ycomm] using
                (LinearMap.rTensor_comm (N := Q) ((pres.diag.map w).hom) ycomm)
    _ = 0 := by simp [hw_zero]

/-- Helper for Lemma 10.89.4: if a stagewise tensor element maps to zero in the tensor colimit,
then it is already zero at some later stage. -/
private lemma exists_later_stage_rTensor_eq_zero_unbundled
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    {j : J} {y : pres.diag.obj j ⊗[R] Q}
    (hy : ((pres.ι.app j).hom.rTensor Q) y = 0) :
    ∃ (j' : J) (w : j ⟶ j'), ((pres.diag.map w).hom.rTensor Q) y = 0 := by
  -- Route correction: commute right tensor to left tensor and reuse Lemma `10.88.3` directly,
  -- instead of proving a separate mixed-universe tensor-colimit statement.
  exact exists_later_stage_rTensor_eq_zero_via_lTensor_comm (R := R) (Q := Q) pres hy

/-- Helper for Lemma 10.89.4: a finitely presented module is small in the universe needed for the
final witness module. -/
private lemma smallOfFinitePresentation
    {R : Type u} [CommRing R]
    {S : Type (max u w)} [AddCommGroup S] [Module R S]
    [Module.FinitePresentation R S] :
    Small.{max u w} S := by
  infer_instance

/-- Helper for Lemma 10.89.4: a finitely presented module whose carrier is already small in
universe `max u w` can be replaced by an equivalent witness in `ModuleCat.{max u w} R`. -/
private lemma finitePresentation_small_model_of_small
    {R : Type u} [CommRing R]
    {S : Type (max u w)} [AddCommGroup S] [Module R S]
    [Module.FinitePresentation R S] [Small.{w} S] :
    ∃ (P' : ModuleCat.{w} R), Module.FinitePresentation R P' ∧
      Nonempty (S ≃ₗ[R] P') := by
  let P' : ModuleCat.{w} R := ModuleCat.of R (Shrink.{w} S)
  let e : S ≃ₗ[R] P' := (Shrink.linearEquiv R S).symm
  let _ : Module.FinitePresentation R P' := Module.FinitePresentation.of_equiv e
  -- Shrinking only changes the carrier universe, so finite presentation transfers across the
  -- canonical linear equivalence.
  exact ⟨P', inferInstance, ⟨e⟩⟩

/-- Helper for Lemma 10.89.4: once the later common-universe stage is known to be small in
universe `w`, its factorization data can be transported to the target witness `P' : ModuleCat.{w}
R`. -/
private lemma factorization_through_small_model
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    {S : Type (max u w)} [AddCommGroup S] [Module R S]
    [Module.FinitePresentation R S] [Small.{w} S]
    (f : P →ₗ[R] M) (f1 : P →ₗ[R] S) (g1 : S →ₗ[R] ULift.{u} M)
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    {x : P ⊗[R] Q}
    (hf1 : moduleEquiv.symm.toLinearMap.comp f = g1.comp f1)
    (hx_stage_mem : x ∈ LinearMap.ker (f1.rTensor Q)) :
    ∃ (P' : ModuleCat.{w} R) (_ : Module.FinitePresentation R P')
      (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
        f = g.comp f' ∧ x ∈ LinearMap.ker (f'.rTensor Q) := by
  obtain ⟨P', hP', ⟨e⟩⟩ := finitePresentation_small_model_of_small (R := R) (S := S)
  let f' : P →ₗ[R] P' := e.toLinearMap.comp f1
  let g : P' →ₗ[R] M := moduleEquiv.toLinearMap.comp (g1.comp e.symm.toLinearMap)
  refine ⟨P', hP', f', g, ?_⟩
  constructor
  · -- Compare the two maps after lifting back to `ULift M`, where the given factorization lives.
    apply LinearMap.ext
    intro p
    apply (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.injective
    have hcomp :
        moduleEquiv.symm.toLinearMap.comp (g.comp f') = moduleEquiv.symm.toLinearMap.comp f := by
      calc
        moduleEquiv.symm.toLinearMap.comp (g.comp f')
            = (g1.comp e.symm.toLinearMap).comp f' := by
                simp [g, LinearMap.comp_assoc]
        _ = g1.comp f1 := by
              ext q
              simp [f', LinearMap.comp_assoc]
        _ = moduleEquiv.symm.toLinearMap.comp f := hf1.symm
    simpa [g, f', LinearMap.comp_apply] using (LinearMap.congr_fun hcomp p).symm
  · -- Transport kernel membership across the linear equivalence from the common-universe stage to
    -- the target-universe model.
    have hx_zero : (f1.rTensor Q) x = 0 := by
      simpa [LinearMap.mem_ker] using hx_stage_mem
    have hx_zero' : (f'.rTensor Q) x = 0 := by
      calc
        (f'.rTensor Q) x = (e.toLinearMap.rTensor Q) ((f1.rTensor Q) x) := by
          simpa [f'] using
            (LinearMap.rTensor_comp_apply (M := Q) (f := f1) (g := e.toLinearMap) (x := x))
        _ = 0 := by simp [hx_zero]
    simpa [LinearMap.mem_ker] using hx_zero'

/-- Helper for Lemma 10.89.4: package the later common-universe finitely presented stage
itself as the source-facing witness.  The original lemma asks for some finitely presented module,
not for one living in the same universe as `M`. -/
private lemma later_stage_factorization_descends_to_target_universe
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    {S : Type (max u w)} [AddCommGroup S] [Module R S]
    [Module.FinitePresentation R S]
    (f : P →ₗ[R] M) (f1 : P →ₗ[R] S) (g1 : S →ₗ[R] ULift.{u} M)
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    {x : P ⊗[R] Q}
    (hf1 : moduleEquiv.symm.toLinearMap.comp f = g1.comp f1)
    (hx_stage_mem : x ∈ LinearMap.ker (f1.rTensor Q)) :
    ∃ (P' : ModuleCat.{max u w} R) (_ : Module.FinitePresentation R P')
      (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
        f = g.comp f' ∧ x ∈ LinearMap.ker (f'.rTensor Q) := by
  let P' : ModuleCat.{max u w} R := ModuleCat.of R S
  let f' : P →ₗ[R] P' := f1
  let g : P' →ₗ[R] M := (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).toLinearMap.comp g1
  refine ⟨P', inferInstance, f', g, ?_⟩
  constructor
  · apply LinearMap.ext
    intro p
    simpa [f', g, LinearMap.comp_apply] using congrArg ULift.down (LinearMap.congr_fun hf1 p)
  · simpa [f'] using hx_stage_mem

/-- Chap10 Lemma 10 89 4: if `x` lies in the kernel of the tensor map induced by `f : P → M`, then `f`
factors through a finitely presented module `P'` in such a way that `x` already lies in the kernel
of the induced map `P ⊗[R] Q → P' ⊗[R] Q`. -/
@[stacks 059L]
theorem exists_finitePresentation_factorization_of_mem_ker_rTensor
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    (f : P →ₗ[R] M)
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    {x : P ⊗[R] Q} (hx : x ∈ LinearMap.ker (f.rTensor Q)) :
    ∃ (P' : ModuleCat.{max u w} R) (_ : Module.FinitePresentation R P')
      (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
        f = g.comp f' ∧ x ∈ LinearMap.ker (f'.rTensor Q) := by
  obtain ⟨J, _, _, pres, hpres⟩ :=
    ulift_finite_presentation_stage_presentation_common_universe (R := R) (M := M)
  have hx_zero : (f.rTensor Q) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  -- Route correction: the old route got stuck on universe-rigid categorical owners. The proof now
  -- follows the source argument with explicit unbundled factorization and tensor-stabilization
  -- lemmas in the common universe of the filtered presentation.
  obtain ⟨j, f0, hf0⟩ :=
    exists_factorization_through_stage_of_finitePresentation_unbundled
      (R := R) (pres := pres) f
  let y : pres.diag.obj j ⊗[R] Q := (f0.rTensor Q) x
  have hy_zero : ((pres.ι.app j).hom.rTensor Q) y = 0 := by
    have hx_zero_lifted : ((moduleEquiv.symm.toLinearMap.comp f).rTensor Q) x = 0 := by
      -- Tensoring the lift `M → ULift M` with `Q` preserves the given vanishing of `x`.
      simpa [LinearMap.rTensor_comp, hx_zero]
    have hy_eq :
        ((moduleEquiv.symm.toLinearMap.comp f).rTensor Q) x =
          ((pres.ι.app j).hom.rTensor Q) y := by
      rw [hf0]
      simpa [y] using
        (LinearMap.rTensor_comp_apply (M := Q) (f := f0)
          (g := (pres.ι.app j).hom) (x := x))
    calc
      ((pres.ι.app j).hom.rTensor Q) y
          = ((moduleEquiv.symm.toLinearMap.comp f).rTensor Q) x := hy_eq.symm
      _ = 0 := hx_zero_lifted
  obtain ⟨j', wj, hw_zero⟩ :=
    exists_later_stage_rTensor_eq_zero_unbundled
      (R := R) (pres := pres) (Q := Q) (j := j) hy_zero
  let f1 : P →ₗ[R] pres.diag.obj j' := (pres.diag.map wj).hom.comp f0
  have hf1 : moduleEquiv.symm.toLinearMap.comp f = (pres.ι.app j').hom.comp f1 := by
    have hw_nat :
        (pres.ι.app j').hom.comp (pres.diag.map wj).hom = (pres.ι.app j).hom := by
      simpa using congrArg ModuleCat.Hom.hom (pres.w wj)
    have hstep : (pres.ι.app j).hom.comp f0 = (pres.ι.app j').hom.comp f1 := by
      -- Naturality of the cocone upgrades the original stage factorization to the later stage.
      simpa [f1] using congrArg (fun k ↦ k.comp f0) hw_nat.symm
    exact hf0.trans hstep
  have hx_stage_zero : (f1.rTensor Q) x = 0 := by
    -- The later-stage transition already kills the tensor element `y`.
    calc
      (f1.rTensor Q) x = ((pres.diag.map wj).hom.rTensor Q) ((f0.rTensor Q) x) := by
        simpa [f1] using
          (LinearMap.rTensor_comp_apply (M := Q) (f := f0)
            (g := (pres.diag.map wj).hom) (x := x))
      _ = 0 := hw_zero
  have hx_stage_mem : x ∈ LinearMap.ker (f1.rTensor Q) := by
    simpa [LinearMap.mem_ker] using hx_stage_zero
  -- The remaining endgame is now isolated as a dedicated descent step from the actual later-stage
  -- factorization data, matching the source proof more faithfully than the earlier blanket
  -- smallness detour.
  exact later_stage_factorization_descends_to_target_universe
    (R := R) (Q := Q) (x := x) (f := f) (f1 := f1) (g1 := (pres.ι.app j').hom) hf1 hx_stage_mem
