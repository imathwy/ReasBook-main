import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_89_4 (from Chap10) -/
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

/-- Helper for Lemma 10.89.4: commutation with `TensorProduct.comm` converts eventual vanishing of
right-tensor maps to the left-tensor stabilization theorem from Lemma 10.88.3. -/
private lemma lTensor_functor_unbundled_map_id
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {Q : Type z} [AddCommGroup Q] [Module R Q] :
    ModuleCat.ofHom ((LinearMap.id : V →ₗ[R] V).lTensor Q) =
      𝟙 (ModuleCat.of.{max v z} R (Q ⊗[R] V)) := by
  -- The unbundled left-tensor functor acts trivially on identity maps.
  apply ModuleCat.hom_ext
  ext x y
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
  -- Both composites send each pure tensor to the same image, so the morphisms coincide.
  apply ModuleCat.hom_ext
  ext x y
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
  -- TODO: implement the common-universe lift all the way up to the ring universe. Lifting only
  -- the stage modules by `ModuleCat.uliftFunctor` is not enough, because the available monoidal
  -- closed `tensorLeft` API on `ModuleCat` is only exposed in the same universe as the ring.
  -- The next plan should therefore build the filtered presentation over `ULift.{max u v z} R`,
  -- transport `y` through one tensor `ULift` equivalence, apply the same-universe stabilization
  -- route there, and then descend the resulting later-stage vanishing back to the original
  -- statement.
  sorry

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

/-- Helper for Lemma 10.89.4: a finitely presented module whose carrier is already small in
universe `w` can be replaced by an equivalent witness in `ModuleCat.{w} R`. -/
private lemma finitePresentation_small_model_of_small
    {R : Type u} [CommRing R]
    {S : Type (max u w)} [AddCommGroup S] [Module R S]
    [Module.FinitePresentation R S] [Small.{w} S] :
    ∃ (P' : ModuleCat.{w} R), Module.FinitePresentation R P' ∧ Nonempty (S ≃ₗ[R] P') := by
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

/-- Lemma 10.89.4: if `x` lies in the kernel of the tensor map induced by `f : P → M`, then `f`
factors through a finitely presented module `P'` in such a way that `x` already lies in the kernel
of the induced map `P ⊗[R] Q → P' ⊗[R] Q`. -/
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
  let _ : ∀ j, Module.FinitePresentation R (pres.diag.obj j) := hpres
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

/-! ### Proposition_10_89_5 (from Chap10) -/
universe u v w x

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: for the forward implication, choose a directed colimit presentation of `M` by
-- finitely presented modules with eventual factorization and reduce injectivity to the finitely
-- presented case using Proposition `10.89.3`. For the converse, test the injectivity hypothesis on
-- the families built from kernels of tensor maps out of finitely presented modules and use Lemma
-- `10.89.4`, Lemma `10.88.3`, and Proposition `10.88.6` to recover the eventual domination
-- condition in a finitely presented presentation of `M`.
/-- Proposition 10.89.5: an `R`-module `M` is Mittag-Leffler if and only if for every family
`(Q α)`, the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is injective. -/
theorem mittagLeffler_iff_tensorProduct_piRight_injective :
    MittagLeffler R M ↔
      ∀ (A : Type w) (Q : A → Type x) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
        Function.Injective (TensorProduct.piRightHom R R M Q) := sorry

end

end Module

/-! ### Lemma_10_89_6 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M] [MittagLeffler R M]
variable {F : Type w} [AddCommGroup F] [Module R F]

-- Proof sketch: let `I` be the set of submodules `F' ≤ F` such that `x` lies in the range of
-- `F'.subtype.rTensor M`. Apply the tensor-product injectivity criterion from Proposition
-- `10.89.5` to the family of quotients `F ⧸ F'` indexed by `I`, so that `x` maps to zero in the
-- product of the quotient tensors and hence in the tensor with the product. Flatness identifies
-- the kernel of the induced map with the tensor of the intersection `sInf I`, giving the smallest
-- supporting submodule. A finite expression of `x` as a sum of pure tensors then shows this
-- smallest submodule is finitely generated, hence finite.
/-- Lemma 10.89.6: for a flat Mittag-Leffler module `M`, every tensor `x : F ⊗[R] M` is supported
by a smallest submodule `F' ≤ F`, and this smallest supporting submodule is finite. In Lean, the
support condition is expressed by `x ∈ LinearMap.range (F'.subtype.rTensor M)`. -/
theorem exists_smallest_finite_submodule_of_mem_tensorProduct
    (x : F ⊗[R] M) :
    ∃ F' : Submodule R F,
      IsLeast { F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M) } F' ∧
        Module.Finite R F' := sorry

end

end Module

/-! ### Lemma_10_89_7 (from Chap10) -/
open scoped TensorProduct

universe u v w x

namespace CategoryTheory.ShortComplex

/- Domain triage:
- primary domain: universally exact short complexes of modules and the owner property
  `Module.MittagLeffler`;
- sampled owner declarations: `CategoryTheory.ShortComplex.UniversallyExact`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective`,
  `CategoryTheory.ShortComplex.UniversallyExact.flat_X₁`;
- primitive data vs. derived API: `UniversallyExact S` is the primitive short-complex datum, and
  propagation of the owner property `Module.MittagLeffler` along it is derived API belonging in
  the `UniversallyExact` namespace.
-/

namespace UniversallyExact

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: for every family `(Q α)` of `R`-modules, tensor the universally exact short exact
-- sequence `S` with `∏ α, Q α` and compare it with the product of the tensor sequences. The top
-- horizontal map is injective by universal exactness, and the right vertical map is injective by
-- Proposition `10.89.5` for `S.X₂`, so the left vertical map is injective as well.
/-- Lemma 10.89.7 (1): in a universally exact short exact sequence of `R`-modules, if the middle
term is Mittag-Leffler, then the left term is Mittag-Leffler. -/
theorem mittagLeffler_X₁ [Module.MittagLeffler R S.X₂] (hS : UniversallyExact S) :
    Module.MittagLeffler R S.X₁ := sorry

-- Proof sketch: for every family `(Q α)`, compare the tensor sequence with `∏ α, Q α` to the
-- product of the tensor sequences with each `Q α`. If an element of the middle tensor maps to zero
-- in the product, its image in the right tensor also maps to zero, hence vanishes by
-- Mittag-Leffler for `S.X₃`. Exactness of the tensor sequence lifts it from the left tensor, and
-- injectivity on the left term from universal exactness plus Mittag-Leffler for `S.X₁` forces the
-- original element to vanish.
/-- Lemma 10.89.7 (2): in a universally exact short exact sequence of `R`-modules, if the left and
right terms are Mittag-Leffler, then the middle term is Mittag-Leffler. -/
theorem mittagLeffler_X₂ [Module.MittagLeffler R S.X₁] [Module.MittagLeffler R S.X₃]
    (hS : UniversallyExact S) : Module.MittagLeffler R S.X₂ := sorry

end

end UniversallyExact
end CategoryTheory.ShortComplex

/-! ### Lemma_10_89_8 (from Chap10) -/
open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: for any family `(Q a)`, tensor the exact sequence `S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` with
-- `∀ a, Q a` and compare it to the product of the exact sequences obtained by tensoring with each
-- `Q a`. Proposition `10.89.2` makes the left vertical map surjective because `S.X₁` is finite,
-- and Proposition `10.89.5` makes the middle vertical map injective because `S.X₂` is
-- Mittag-Leffler. A diagram chase gives injectivity on the right vertical map, and Proposition
-- `10.89.5` then shows that `S.X₃` is Mittag-Leffler.
/-- Lemma 10.89.8: if `S : ShortComplex (ModuleCat R)` is exact, `S.g` is surjective, `S.X₁` is
finite, and `S.X₂` is Mittag-Leffler, then `S.X₃` is Mittag-Leffler. -/
theorem mittagLeffler_X₃_of_exact_of_finite_of_mittagLeffler
    (hS : S.Exact) (hSurj : Function.Surjective S.g) [Module.Finite R S.X₁]
    [Module.MittagLeffler R S.X₂] :
    Module.MittagLeffler R S.X₃ := sorry

end

end CategoryTheory.ShortComplex

/-! ### Lemma_10_89_9 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/- Domain-style sampling:
* primary domain: Mittag-Leffler modules over a commutative ring, organized around the chapter
  owner `Module.MittagLeffler`.
* inspected owner declarations:
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `LinearMap.UniversallyInjective` from `Definition_10_82_1`,
  `mittagLeffler_iff_tensorProduct_piRight_injective` from `Proposition_10_89_5`, and
  `CategoryTheory.ShortComplex.universallyExact_colimit_of_isFiltered` from `Example_10_82_2`.
* best owner abstraction: the chapter owners `Module.MittagLeffler` and
  `LinearMap.UniversallyInjective`; this lemma should build directly on them rather than introduce
  a local wrapper for directed systems with tensor-injective transition maps.
* layer: `source-facing`; the theorem records the directed-colimit closure statement from the
  source, not a new owner abstraction.
* primitive data: the directed diagram `F` and the universally injective transition-map
  hypothesis `hF`.
* derived API: the induced Mittag-Leffler structure on the colimit module `colimit F`.
-/
-- Proof sketch: by Proposition `10.89.5`, it is enough to show injectivity of the canonical map
-- `M ⊗[R] ∏ Q_α → ∏ (M ⊗[R] Q_α)` for the colimit module `M = colimit F`. Tensor product with a
-- fixed module commutes with filtered colimits, so this reduces to the corresponding injectivity at
-- each stage `F.obj i`, where it holds because `F.obj i` is Mittag-Leffler. The maps into the
-- product of the colimit tensors are injective because the transition maps are universally
-- injective after tensoring with each `Q_α`.
/-- Lemma 10.89.9: the colimit of a directed system of Mittag-Leffler `R`-modules with
universally injective transition maps is a Mittag-Leffler `R`-module. -/
theorem mittagLeffler_colimit_of_directedSystem
    (F : I ⥤ ModuleCat R)
    [∀ i, MittagLeffler R (F.obj i)]
    (hF :
      ∀ ⦃i j : I⦄ (hij : i ≤ j),
        LinearMap.UniversallyInjective ((F.map (homOfLE hij)).hom)) :
    MittagLeffler R ((colimit F : ModuleCat R)) := sorry

end

end Module

/-! ### Lemma_10_89_10 (from Chap10) -/
open scoped DirectSum

universe u v w

namespace Module

namespace MittagLeffler

section DirectSum

/- Domain-style sampling:
- primary domain: the owner class `Module.MittagLeffler` and its closure properties;
- sampled declarations of the same kind:
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective` from `Proposition_10_89_5`,
  `CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₂` from `Lemma_10_89_7`,
  `Module.mittagLeffler_colimit_of_directedSystem` from `Lemma_10_89_9`,
  together with the owner-shaped mathlib declarations `Module.Flat.directSum_iff`,
  `Module.Flat.directSum`, and the definitional companion `Module.Flat.dfinsupp_iff`.
- best owner abstraction: `Module.MittagLeffler`; the direct-sum statement is derived API of this
  owner, not a separate local wrapper notion.
- layer: `source-facing` theorem stated through the canonical owner.
- primitive data: the family of summands `M`.
- derived API: the direct-sum characterization/instance, with the `Π₀` formulation only as a thin
  definitional companion.
-/

section

variable {R : Type u} [CommRing R]
variable {I : Type v} {M : I → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

-- Proof sketch: for the forward implication, each summand is a direct summand of the direct sum,
-- so apply Lemma `10.89.7 (1)` to the split universally exact sequence coming from the projection
-- onto the `i`-th summand. For the reverse implication, express `Π₀ i, M i` as the directed
-- colimit of its finite partial sums; each finite partial sum is Mittag-Leffler by repeated use of
-- Lemma `10.89.7 (2)`, and Lemma `10.89.9` finishes the passage to the full direct sum.
/-- Lemma 10.89.10: a direct sum `⨁ i, M i` of `R`-modules is Mittag-Leffler if and only if each
summand `M i` is Mittag-Leffler. -/
theorem directSum_iff :
    Module.MittagLeffler R (⨁ i, M i) ↔ ∀ i, Module.MittagLeffler R (M i) := sorry

/-- The `Π₀` presentation is a definitional companion to `directSum_iff`. -/
theorem dfinsupp_iff :
    Module.MittagLeffler R (Π₀ i, M i) ↔ ∀ i, Module.MittagLeffler R (M i) :=
  directSum_iff ..

/-- A direct sum of Mittag-Leffler `R`-modules is Mittag-Leffler. -/
instance directSum [∀ i, Module.MittagLeffler R (M i)] :
    Module.MittagLeffler R (⨁ i, M i) :=
  directSum_iff.2 ‹_›

instance dfinsupp [∀ i, Module.MittagLeffler R (M i)] :
    Module.MittagLeffler R (Π₀ i, M i) :=
  dfinsupp_iff.2 ‹_›

end

end DirectSum

end MittagLeffler

end Module

/-! ### Lemma_10_89_11 (from Chap10) -/
universe u v w x y

namespace Module

section

open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

private theorem piRightHom_restrictScalars_factor
    {A : Type x} (Q : A → Type y) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    (LinearEquiv.piCongrRight fun a ↦ cancelBaseChange R S S M (Q a)).toLinearMap ∘ₗ
        TensorProduct.piRightHom S S M (fun a ↦ S ⊗[R] Q a) ∘ₗ
        lTensor S M (TensorProduct.piRightHom R S S Q) ∘ₗ
        (cancelBaseChange R S S M ((a : A) → Q a)).symm.toLinearMap =
      TensorProduct.piRightHom R S M Q := by
  ext m q a
  simp

private theorem piRightHom_restrictScalars_injective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    {A : Type x} (Q : A → Type y) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    [MittagLeffler R S] [Module.Flat S M] [MittagLeffler S M] :
    Function.Injective (TensorProduct.piRightHom R R M Q) := by
  let eDom := cancelBaseChange R S S M ((a : A) → Q a)
  let eCod := LinearEquiv.piCongrRight fun a ↦ cancelBaseChange R S S M (Q a)
  have hCriterionS :
      MittagLeffler R S ↔
        ∀ (A : Type x) (Q : A → Type y) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Injective (TensorProduct.piRightHom R R S Q) :=
    mittagLeffler_iff_tensorProduct_piRight_injective
  have hS :
      Function.Injective (TensorProduct.piRightHom R S S Q) := by
    simpa using hCriterionS.1 (inferInstance : MittagLeffler R S) A Q
  have hTensor :
      Function.Injective (lTensor S M (TensorProduct.piRightHom R S S Q)) := by
    simpa using
      Module.Flat.lTensor_preserves_injective_linearMap (TensorProduct.piRightHom R S S Q) hS
  have hCriterionM :
      MittagLeffler S M ↔
        ∀ (A : Type x) (Q : A → Type (max v y)) [∀ a, AddCommGroup (Q a)]
          [∀ a, Module S (Q a)],
          Function.Injective (TensorProduct.piRightHom S S M Q) :=
    mittagLeffler_iff_tensorProduct_piRight_injective
  have hM :
      Function.Injective (TensorProduct.piRightHom S S M (fun a ↦ S ⊗[R] Q a)) := by
    simpa using hCriterionM.1 (inferInstance : MittagLeffler S M) A (fun a ↦ S ⊗[R] Q a)
  have hComp :
      Function.Injective
        (eCod.toLinearMap ∘ₗ
          TensorProduct.piRightHom S S M (fun a ↦ S ⊗[R] Q a) ∘ₗ
          lTensor S M (TensorProduct.piRightHom R S S Q) ∘ₗ
          eDom.symm.toLinearMap) :=
    eCod.injective.comp <| hM.comp <| hTensor.comp eDom.symm.injective
  have hRS : Function.Injective (TensorProduct.piRightHom R S M Q) := by
    rw [← piRightHom_restrictScalars_factor Q]
    simpa [eDom, eCod] using hComp
  simpa using hRS

-- Proof sketch: by Proposition `10.89.5`, it is enough to test injectivity of the canonical map
-- `M ⊗[R] ∏ Q_α → ∏ (M ⊗[R] Q_α)` for every family of `R`-modules. Rewrite this map as the
-- composite obtained by first tensoring the injective map
-- `S ⊗[R] ∏ Q_α → ∏ (S ⊗[R] Q_α)` with the `S`-flat module `M`, and then applying the injective
-- `S`-Mittag-Leffler map for the family `α ↦ S ⊗[R] Q_α`.
/-- Lemma 10.89.11: if `S` is a Mittag-Leffler `R`-module and `M` is flat and Mittag-Leffler as
an `S`-module, then `M` is Mittag-Leffler as an `R`-module. -/
theorem mittagLeffler_restrictScalars_of_mittagLeffler_of_flat [MittagLeffler R S]
    [Module.Flat S M] [MittagLeffler S M] :
    MittagLeffler R M := by
  have hCriterion :
      MittagLeffler R M ↔
        ∀ (A : Type w) (Q : A → Type w) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Injective (TensorProduct.piRightHom R R M Q) :=
    mittagLeffler_iff_tensorProduct_piRight_injective
  refine hCriterion.2 ?_
  intro (A : Type w) (Q : A → Type w) _ _
  exact piRightHom_restrictScalars_injective R S M Q

end

end Module
