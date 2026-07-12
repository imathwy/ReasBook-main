import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap20.«20_10_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Helper for Lemma 20.10.1: `ModuleCat` has products in the universe needed for the local Čech
construction. -/
private abbrev moduleCatHasProducts {R : Type u} [Ring R] :
    HasProducts.{w} (ModuleCat.{w} R) := by
  let _ : HasLimits (ModuleCat.{w} R) := ModuleCat.hasLimitsOfSize.{w, w, w, u}
  infer_instance

/-- Helper for Lemma 20.10.1: exact functors remain exact after composition. -/
private theorem exactFunctor_comp
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {D : Type u₃} [Category.{v₃} D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F) (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Exactness is preservation of finite limits and finite colimits, and both properties compose.
  rw [exactFunctor_iff] at hF hG ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  let _ : PreservesFiniteLimits G := hG.1
  let _ : PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 20.10.1: evaluations on a functor category jointly reflect isomorphisms. -/
private theorem evaluation_jointlyReflectsIsomorphisms
    (D : Type u₁) [Category.{v₁} D] (A : Type u₂) [Category.{v₂} A] :
    JointlyReflectIsomorphisms ((evaluation D A).obj : D → (D ⥤ A) ⥤ A) := by
  -- A natural transformation is an isomorphism exactly when all of its components are.
  refine ⟨fun {F G} α hα ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  simpa using (inferInstance : IsIso (((evaluation D A).obj d).map α))

/-- Helper for Lemma 20.10.1: a short exact sequence in a functor category stays short exact after
evaluation at any object. -/
private theorem evaluation_shortExact_of_shortExact
    {D : Type u₁} [Category.{v₁} D]
    {A : Type u₂} [Category.{v₂} A] [Abelian A]
    {S : ShortComplex (D ⥤ A)} (hS : S.ShortExact) (d : D) :
    (S.map ((evaluation D A).obj d)).ShortExact := by
  let hEval := evaluation_jointlyReflectsIsomorphisms D A
  -- Exactness, monomorphy, and epimorphy in a functor category are all detected pointwise.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (hEval.exact_iff S).1 hS.exact d
  · exact (NatTrans.mono_iff_mono_app S.f).1 hS.mono_f d
  · exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g d

/-- Helper for Lemma 20.10.1: precomposition along any functor is exact on functor categories with
abelian codomain. -/
private theorem whiskeringLeft_exact
    {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E]
    {A : Type u₃} [Category.{v₃} A] [Abelian A] (G : D ⥤ E) :
    exactFunctor (E ⥤ A) (D ⥤ A)
      ((Functor.whiskeringLeft D E A).obj G) := by
  let F : (E ⥤ A) ⥤ D ⥤ A := (Functor.whiskeringLeft D E A).obj G
  let hEval := evaluation_jointlyReflectsIsomorphisms D A
  letI : F.Additive := by infer_instance
  letI : F.PreservesZeroMorphisms := by infer_instance
  -- After evaluating at `d`, precomposition is just evaluation of the original short exact
  -- sequence at `G.obj d`.
  refine ((Functor.exact_tfae F).out 3 0).2 ?_
  intro S hS
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (hEval.exact_iff (S.map F)).2 fun d ↦ by
      simpa [F] using (evaluation_shortExact_of_shortExact hS (G.obj d)).exact
  · exact (NatTrans.mono_iff_mono_app (S.map F).f).2 fun d ↦ by
      simpa [F] using (evaluation_shortExact_of_shortExact hS (G.obj d)).mono_f
  · exact (NatTrans.epi_iff_epi_app (S.map F).g).2 fun d ↦ by
      simpa [F] using (evaluation_shortExact_of_shortExact hS (G.obj d)).epi_g

/-- Helper for Lemma 20.10.1: evaluating a pushed-forward presheaf of modules is just evaluation at
the transported object. -/
private theorem pushforward₀_evalExact
    {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat) (Y : Cᵒᵖ) :
    exactFunctor _ _
      (PresheafOfModules.pushforward₀ F R ⋙ PresheafOfModules.evaluation (F.op ⋙ R) Y) := by
  -- Evaluating after pushforward is definitionally evaluation at the corresponding source object.
  simpa using
    (ExactFunctor.of (PresheafOfModules.evaluation R (F.op.obj Y))).property

/-- Helper for Lemma 20.10.1: the restricted-sections functor is additive. -/
private instance ringedSiteModuleSectionsOnOverPresheaf_additive
    (𝒪 : Sheaf J RingCat) (U : C) :
    (ringedSiteModuleSectionsOnOverPresheaf 𝒪 U).Additive := by
  -- Every stage of the restricted-sections construction acts componentwise on natural
  -- transformations, so additivity is checked pointwise.
  refine ⟨?_⟩
  intro M N α β
  apply NatTrans.ext
  funext V
  rfl

/-- Helper for Lemma 20.10.1: evaluating the restricted-sections functor at `V` is the same as
evaluating after pushforward and then restricting scalars from `𝒪(V)` to `𝒪(U)`. -/
private theorem ringedSiteModuleSectionsOnOverPresheaf_eval_eq
    (𝒪 : Sheaf J RingCat) (U : C) (V : Over U) :
    (ringedSiteModuleSectionsOnOverPresheaf 𝒪 U ⋙
        (evaluation (Over U)ᵒᵖ (ModuleCat.{u} (𝒪.obj.obj (op U)))).obj (op V)) =
      ((PresheafOfModules.pushforward₀ (Over.forget U) 𝒪.obj ⋙
          PresheafOfModules.evaluation ((Over.forget U).op ⋙ 𝒪.obj) (op V)) ⋙
        ModuleCat.restrictScalars
          ((((Over.forget U).op ⋙ 𝒪.obj).map (Over.mkIdTerminal.op.to (op V))).hom)) := by
  rfl

/-- The restricted-sections functor on `Over U` sending a presheaf of `𝒪`-modules to the
resulting presheaf of `𝒪(U)`-modules by restriction of scalars is exact. -/
theorem ringedSiteModuleSectionsOnOverPresheaf_exact
    (𝒪 : Sheaf J RingCat) (U : C) :
    exactFunctor (PresheafOfModules 𝒪.obj)
      ((Over U)ᵒᵖ ⥤ ModuleCat (𝒪.obj.obj (op U)))
      (ringedSiteModuleSectionsOnOverPresheaf 𝒪 U) := by
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · exact preservesFiniteLimits_of_evaluation (ringedSiteModuleSectionsOnOverPresheaf 𝒪 U)
      fun V ↦ by
        let hPush := pushforward₀_evalExact (Over.forget U) 𝒪.obj V
        let hRestrict := restrictScalars_exact
          ((((Over.forget U).op ⋙ 𝒪.obj).map (Over.mkIdTerminal.op.to V)).hom)
        let hComp := exactFunctor_comp hPush hRestrict
        simpa [ringedSiteModuleSectionsOnOverPresheaf_eval_eq] using hComp.1
  · exact preservesFiniteColimits_of_evaluation (ringedSiteModuleSectionsOnOverPresheaf 𝒪 U)
      fun V ↦ by
        let hPush := pushforward₀_evalExact (Over.forget U) 𝒪.obj V
        let hRestrict := restrictScalars_exact
          ((((Over.forget U).op ⋙ 𝒪.obj).map (Over.mkIdTerminal.op.to V)).hom)
        let hComp := exactFunctor_comp hPush hRestrict
        simpa [ringedSiteModuleSectionsOnOverPresheaf_eval_eq] using hComp.2

/-- Helper for Lemma 20.10.1: the discrete diagram of componentwise evaluations attached to a
formal coproduct of objects of `Over U`. -/
private abbrev formal_coproduct_componentwise_diagram
    {R : Type _} [Ring R] {U : C} [HasProducts.{w} (ModuleCat.{w} R)]
    (X : FormalCoproduct.{w} (Over U)) :
    ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Discrete X.I ⥤ ModuleCat.{w} R :=
  (Functor.whiskeringLeft (Discrete X.I) (Over U)ᵒᵖ (ModuleCat.{w} R)).obj
    (Discrete.functor (fun i : X.I ↦ Opposite.op (X.obj i)))

/-- Helper for Lemma 20.10.1: the product of the componentwise evaluations of a formal coproduct
in a module category. -/
private abbrev formal_coproduct_componentwise_functor
    {R : Type _} [Ring R] {U : C} [HasProducts.{w} (ModuleCat.{w} R)]
    (X : FormalCoproduct.{w} (Over U)) :
    ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
  (formal_coproduct_componentwise_diagram (R := R) X) ⋙
    (lim : (Discrete X.I ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R)

/-- Helper for Lemma 20.10.1: the product functor on a discrete diagram of modules is exact. -/
private theorem discreteLimitFunctor_exact
    {R : Type _} [Ring R] [HasProducts.{w} (ModuleCat.{w} R)] (I : Type w) :
    exactFunctor (Discrete I ⥤ ModuleCat.{w} R) (ModuleCat.{w} R)
      (lim : (Discrete I ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R) := by
  rw [exactFunctor_iff]
  let _ : HasExactLimitsOfShape (Finset (Discrete I))ᵒᵖ (ModuleCat.{w} R) :=
    hasExactLimitsOfShape_discrete_finite (C := ModuleCat.{w} R)
      (J := (Finset (Discrete I))ᵒᵖ)
  let _ : HasExactLimitsOfShape (Discrete I) (ModuleCat.{w} R) :=
    hasExactLimitsOfShape_discrete_of_hasExactLimitsOfShape_finset_discrete_op
      (C := ModuleCat.{w} R) I
  -- `ModuleCat` satisfies `AB4*`, so arbitrary products are exact.
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 20.10.1: the product of the componentwise evaluations of a formal coproduct is
exact. -/
private theorem formal_coproduct_componentwise_exact
    {R : Type _} [Ring R] {U : C} [HasProducts.{w} (ModuleCat.{w} R)]
    (X : FormalCoproduct.{w} (Over U)) :
    exactFunctor ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) (ModuleCat.{w} R)
      (formal_coproduct_componentwise_functor (R := R) X) := by
  let hPrecomp :
      exactFunctor ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) (Discrete X.I ⥤ ModuleCat.{w} R)
      (formal_coproduct_componentwise_diagram (R := R) X) := by
    -- Precomposition with the discrete component diagram is exact.
    simpa [formal_coproduct_componentwise_diagram] using whiskeringLeft_exact
      (Discrete.functor (fun i : X.I ↦ Opposite.op (X.obj i)))
  let hLim : exactFunctor (Discrete X.I ⥤ ModuleCat.{w} R) (ModuleCat.{w} R)
      (lim : (Discrete X.I ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R) :=
    discreteLimitFunctor_exact (R := R) X.I
  -- Exactness is stable under composing the evaluation diagram with the product functor.
  simpa [formal_coproduct_componentwise_functor] using exactFunctor_comp hPrecomp hLim

/-- Helper for Lemma 20.10.1: fixed-object evaluation of `FormalCoproduct.evalOp` is the product
of the componentwise evaluations. -/
private noncomputable def formal_coproduct_eval_iso_componentwise_limit
    {R : Type _} [Ring R] {U : C} [HasProducts.{w} (ModuleCat.{w} R)]
    (X : FormalCoproduct.{w} (Over U)) (P : (Over U)ᵒᵖ ⥤ ModuleCat.{w} R) :
    (((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)).obj P).obj (Opposite.op X)) ≅
      ((formal_coproduct_componentwise_functor (R := R) X).obj P) := by
  let G := formal_coproduct_componentwise_diagram (R := R) X
  -- The value of `evalOp` at `X` is the product of the evaluations at the components of `X`.
  simpa [formal_coproduct_componentwise_functor, formal_coproduct_componentwise_diagram,
    G, FormalCoproduct.evalOp] using (Pi.isoLimit (G.obj P))

/-- Helper for Lemma 20.10.1: the previous comparison identifies the universal projection maps. -/
private theorem formal_coproduct_eval_iso_componentwise_limit_hom_π
    {R : Type _} [Ring R] {U : C} [HasProducts.{w} (ModuleCat.{w} R)]
    (X : FormalCoproduct.{w} (Over U)) (P : (Over U)ᵒᵖ ⥤ ModuleCat.{w} R) (i : X.I) :
    (formal_coproduct_eval_iso_componentwise_limit (R := R) X P).hom ≫
        limit.π ((formal_coproduct_componentwise_diagram (R := R) X).obj P) (Discrete.mk i) =
      Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i := by
  simpa [formal_coproduct_eval_iso_componentwise_limit] using
    (Pi.isoLimit_hom_π ((formal_coproduct_componentwise_diagram (R := R) X).obj P) i)

/-- Helper for Lemma 20.10.1: the fixed-object comparison is natural in a map of presheaves. -/
private theorem formal_coproduct_eval_iso_componentwise_limit_naturality
    {R : Type _} [Ring R] {U : C} [HasProducts.{w} (ModuleCat.{w} R)]
    (X : FormalCoproduct.{w} (Over U))
    {P Q : (Over U)ᵒᵖ ⥤ ModuleCat.{w} R} (α : P ⟶ Q) :
    (((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)).map α).app (Opposite.op X)) ≫
        (formal_coproduct_eval_iso_componentwise_limit (R := R) X Q).hom =
      (formal_coproduct_eval_iso_componentwise_limit (R := R) X P).hom ≫
        (formal_coproduct_componentwise_functor (R := R) X).map α := by
  apply limit.hom_ext
  rintro ⟨i⟩
  have hleft :
      ((((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)).map α).app (Opposite.op X)) ≫
          (formal_coproduct_eval_iso_componentwise_limit (R := R) X Q).hom) ≫
        limit.π ((formal_coproduct_componentwise_diagram (R := R) X).obj Q) (Discrete.mk i) =
      Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i ≫ α.app (Opposite.op (X.obj i)) := by
    rw [Category.assoc, formal_coproduct_eval_iso_componentwise_limit_hom_π]
    change Limits.Pi.map (fun k : X.I ↦ α.app (Opposite.op (X.obj k))) ≫
        Pi.π (fun k : X.I ↦ Q.obj (Opposite.op (X.obj k))) i =
      Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i ≫ α.app (Opposite.op (X.obj i))
    exact Pi.map_π (fun k : X.I ↦ α.app (Opposite.op (X.obj k))) i
  have hright :
      (((formal_coproduct_eval_iso_componentwise_limit (R := R) X P).hom ≫
            (formal_coproduct_componentwise_functor (R := R) X).map α) ≫
          limit.π ((formal_coproduct_componentwise_diagram (R := R) X).obj Q) (Discrete.mk i)) =
        Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i ≫ α.app (Opposite.op (X.obj i)) := by
    have hπ :
        ((formal_coproduct_eval_iso_componentwise_limit (R := R) X P).hom ≫
            limit.π ((formal_coproduct_componentwise_diagram (R := R) X).obj P) (Discrete.mk i)) ≫
          α.app (Opposite.op (X.obj i)) =
        Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i ≫ α.app (Opposite.op (X.obj i)) := by
      simpa [Category.assoc] using
        congrArg (fun m ↦ m ≫ α.app (Opposite.op (X.obj i)))
          (formal_coproduct_eval_iso_componentwise_limit_hom_π (R := R) X P i)
    have hmid :
        (((formal_coproduct_eval_iso_componentwise_limit (R := R) X P).hom ≫
              (formal_coproduct_componentwise_functor (R := R) X).map α) ≫
            limit.π ((formal_coproduct_componentwise_diagram (R := R) X).obj Q) (Discrete.mk i)) =
          ((formal_coproduct_eval_iso_componentwise_limit (R := R) X P).hom ≫
              limit.π ((formal_coproduct_componentwise_diagram (R := R) X).obj P) (Discrete.mk i)) ≫
            α.app (Opposite.op (X.obj i)) := by
      simp [Category.assoc]
      simpa using congrArg
        (fun m ↦ (formal_coproduct_eval_iso_componentwise_limit (R := R) X P).hom ≫ m)
        (limMap_π ((Discrete.functor fun k : X.I ↦ Opposite.op (X.obj k)).whiskerLeft α)
          (Discrete.mk i))
    exact hmid.trans hπ
  exact hleft.trans hright.symm

/-- Helper for Lemma 20.10.1: fixed-object evaluation of `FormalCoproduct.evalOp` is naturally the
product of the componentwise evaluations. -/
private noncomputable def formal_coproduct_eval_natIso_componentwise_limit
    {R : Type _} [Ring R] {U : C} [HasProducts.{w} (ModuleCat.{w} R)]
    (X : FormalCoproduct.{w} (Over U)) :
    ((((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)) ⋙
        (evaluation (FormalCoproduct.{w} (Over U))ᵒᵖ (ModuleCat.{w} R)).obj (Opposite.op X)) :
      ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R)) ≅
      formal_coproduct_componentwise_functor (R := R) X :=
  NatIso.ofComponents
    (formal_coproduct_eval_iso_componentwise_limit (R := R) X)
    (fun α ↦ formal_coproduct_eval_iso_componentwise_limit_naturality (R := R) X α)

/-- Helper for Lemma 20.10.1: fixed-object evaluation of `FormalCoproduct.evalOp` is exact because
it is naturally isomorphic to the exact product of the componentwise evaluations. -/
private theorem formal_coproduct_evalExact
    {R : Type _} [Ring R] {U : C} [HasProducts.{w} (ModuleCat.{w} R)]
    (X : FormalCoproduct.{w} (Over U)) :
    exactFunctor ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) (ModuleCat.{w} R)
      ((((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)) ⋙
          (evaluation (FormalCoproduct.{w} (Over U))ᵒᵖ (ModuleCat.{w} R)).obj
            (Opposite.op X)) :
        ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R)) := by
  let Fprod :
      ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
    formal_coproduct_componentwise_functor (R := R) X
  let hFprod := formal_coproduct_componentwise_exact (R := R) X
  let hPres := (exactFunctor_iff Fprod).1 hFprod
  letI : PreservesFiniteLimits Fprod := hPres.1
  letI : PreservesFiniteColimits Fprod := hPres.2
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · exact preservesFiniteLimits_of_natIso
      (formal_coproduct_eval_natIso_componentwise_limit (R := R) X).symm
  · exact preservesFiniteColimits_of_natIso
      (formal_coproduct_eval_natIso_componentwise_limit (R := R) X).symm

/-- Helper for Lemma 20.10.1: the canonical Čech cochain complex functor is exact for
module-valued presheaves on `Over U`. -/
private theorem moduleCatCechComplexFunctor_exact
    (U : C) [HasFiniteProducts (Over U)] {R : Type _} [Ring R] {ι : Type w}
    (family : ι → Over U) :
    exactFunctor ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R)
      (CochainComplex (ModuleCat R) ℕ) (cechComplexFunctor family) := by
  let _ : HasProducts.{w} (ModuleCat.{w} R) := moduleCatHasProducts
  let F : ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ CochainComplex (ModuleCat.{w} R) ℕ :=
    cechComplexFunctor family
  let E : SimplicialObject (FormalCoproduct.{w} (Over U)) := (FormalCoproduct.mk _ family).cech
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · refine ⟨fun J _ _ ↦ ?_⟩
    exact HomologicalComplex.preservesLimitsOfShape_of_eval F fun n ↦ by
      let hFn := formal_coproduct_evalExact (R := R)
        (E.obj (Opposite.op (SimplexCategory.mk n)))
      let hPres := (exactFunctor_iff _).1 hFn
      letI : PreservesFiniteLimits
          ((((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)) ⋙
              (evaluation (FormalCoproduct.{w} (Over U))ᵒᵖ (ModuleCat.{w} R)).obj
                (Opposite.op (E.obj (Opposite.op (SimplexCategory.mk n))))) :
            ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R)) := hPres.1
      simpa [F, cechComplexFunctor, E, FormalCoproduct.cochainComplexFunctor,
        FormalCoproduct.cosimplicialObjectFunctor] using
        (show PreservesLimitsOfShape J
          ((((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)) ⋙
              (evaluation (FormalCoproduct.{w} (Over U))ᵒᵖ (ModuleCat.{w} R)).obj
                (Opposite.op (E.obj (Opposite.op (SimplexCategory.mk n))))) :
            ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R)) from inferInstance)
  · refine ⟨fun J _ _ ↦ ?_⟩
    exact HomologicalComplex.preservesColimitsOfShape_of_eval F fun n ↦ by
      let hFn := formal_coproduct_evalExact (R := R)
        (E.obj (Opposite.op (SimplexCategory.mk n)))
      let hPres := (exactFunctor_iff _).1 hFn
      letI : PreservesFiniteColimits
          ((((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)) ⋙
              (evaluation (FormalCoproduct.{w} (Over U))ᵒᵖ (ModuleCat.{w} R)).obj
                (Opposite.op (E.obj (Opposite.op (SimplexCategory.mk n))))) :
            ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R)) := hPres.2
      simpa [F, cechComplexFunctor, E, FormalCoproduct.cochainComplexFunctor,
        FormalCoproduct.cosimplicialObjectFunctor] using
        (show PreservesColimitsOfShape J
          ((((FormalCoproduct.evalOp.{w} (Over U) (ModuleCat.{w} R)) ⋙
              (evaluation (FormalCoproduct.{w} (Over U))ᵒᵖ (ModuleCat.{w} R)).obj
                (Opposite.op (E.obj (Opposite.op (SimplexCategory.mk n))))) :
            ((Over U)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ ModuleCat.{w} R)) from inferInstance)

/-- For a family `family : ι → Over U`, the ringed-site Čech complex functor with coefficients in
presheaf `𝒪`-modules is exact. -/
theorem ringedSiteModuleCechComplexFunctor_exact
    (𝒪 : Sheaf J RingCat) (U : C) [HasFiniteProducts (Over U)] {ι : Type w}
    (family : ι → Over U) :
    exactFunctor (PresheafOfModules 𝒪.obj)
      (CochainComplex (ModuleCat (𝒪.obj.obj (op U))) ℕ)
      (ringedSiteModuleCechComplexFunctor 𝒪 U family) := by
  let _ : Ring ↑(𝒪.obj.obj (op U)) := inferInstance
  let _ : HasProducts.{w} (ModuleCat.{w} ↑(𝒪.obj.obj (op U))) := moduleCatHasProducts
  -- The source-facing Čech functor is the composite of exact restricted sections and exact Čech
  -- construction on `Over U`.
  simpa [ringedSiteModuleCechComplexFunctor] using
    exactFunctor_comp
      (ringedSiteModuleSectionsOnOverPresheaf_exact 𝒪 U)
      (moduleCatCechComplexFunctor_exact (R := ↑(𝒪.obj.obj (op U))) U family)

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

variable (U : Opens X.carrier) {ι : Type u}

local notation "ModU" => ModuleCat (X.presheaf.obj (op U))

/- Domain-style sampling for Lemma 20.10.1:
- primary domain: exact functors between abelian categories, specialized to presheaves of
  `𝒪_X`-modules and their Čech complexes on `Over U`;
- sampled owner declarations:
  `CategoryTheory.exactFunctor`,
  `CategoryTheory.ExactFunctor.of`,
  `ringedSpaceModuleCechComplexFunctor`,
  `CategoryTheory.cechComplexFunctor`;
- best owner abstraction: the exactness notion is owned by `exactFunctor`, with bundled form
  `ExactFunctor.of`; the source-facing item in this file is the specialized exactness statement for
  the chapter's canonical Čech functor `ringedSpaceModuleCechComplexFunctor U 𝒰`;
- primitive data: the functor `ringedSpaceModuleCechComplexFunctor U 𝒰` defined in `20.10.0.1`;
- derived API: the exactness predicate below.

Source/core/bridge triage:
- `source-facing`: the exactness statement for the ringed-space Čech complex functor;
- `core/canonical`: `exactFunctor`, `ExactFunctor.of`, and the owner functor
  `ringedSpaceModuleCechComplexFunctor`;
- `bridge/view`: this theorem, which records the source statement in the canonical exactness
  predicate without introducing a parallel exact-functor wrapper.
-/
-- Proof sketch: by `20.10.0.1`, the functor is the composite of the generic ringed-site
-- restricted-sections functor
-- `CategoryTheory.ringedSiteModuleSectionsOnOverPresheaf X.ringCatSheaf U`
-- with the Čech complex functor on `(Over U)ᵒᵖ`. For each `V : Over U`, evaluation at `V` is
-- exact on presheaves of modules, and restriction of scalars is exact on module categories. Hence
-- `CategoryTheory.ringedSiteModuleSectionsOnOverPresheaf X.ringCatSheaf U` is exact. The functor
-- `CategoryTheory.cechComplexFunctor 𝒰` is exact because each degree is a product of exact
-- evaluation functors, and finite limits and colimits in cochain complexes are computed
-- degreewise. Therefore the composite is exact.
/-- Lemma 20.10.1: for an indexed family `𝒰` of objects of `Over U`, the Čech complex functor of
Equation `20.10.0.1`
`ringedSpaceModuleCechComplexFunctor U 𝒰 :
  PMod(𝒪_X) ⥤ CochainComplex (Mod(𝒪_X(U))) ℕ`
is an exact functor. -/
@[stacks 01EJ]
theorem ringedSpaceModuleCechComplexFunctor_exact [HasFiniteProducts (Over U)]
    (𝒰 : ι → Over U) :
    exactFunctor (RingedSpace.PresheafModules X) (CochainComplex ModU ℕ)
      (ringedSpaceModuleCechComplexFunctor U 𝒰) := by
  simpa [ringedSpaceModuleCechComplexFunctor] using
    (CategoryTheory.ringedSiteModuleCechComplexFunctor_exact (RingedSpace.ringCatSheaf X) U 𝒰)

end AlgebraicGeometry.RingedSpace
