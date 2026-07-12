import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksProject_2024.Chap21.«21_9_0_1»

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

/-- Helper for Lemma 21.9.1: exact functors remain exact after composition. -/
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

/-- Helper for Lemma 21.9.1: evaluations on a functor category jointly reflect isomorphisms. -/
private theorem evaluation_jointlyReflectsIsomorphisms
    (D : Type u₁) [Category.{v₁} D] (A : Type u₂) [Category.{v₂} A] :
    JointlyReflectIsomorphisms ((evaluation D A).obj : D → (D ⥤ A) ⥤ A) := by
  -- A natural transformation is an isomorphism exactly when all of its components are.
  refine ⟨fun {F G} α hα ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  simpa using (inferInstance : IsIso (((evaluation D A).obj d).map α))

/-- Helper for Lemma 21.9.1: a short exact sequence in a functor category stays short exact after
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

private theorem whiskeringLeft_exact_aux
    {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E]
    {A : Type u₃} [Category.{v₃} A] [Abelian A] (G : D ⥤ E) :
    exactFunctor (E ⥤ A) (D ⥤ A)
      ((Functor.whiskeringLeft D E A).obj G) := by
  refine ((Functor.exact_tfae ((Functor.whiskeringLeft D E A).obj G)).out 3 0).2 ?_
  intro S hS
  let hEval := evaluation_jointlyReflectsIsomorphisms D A
  -- After evaluating at `d`, precomposition is just evaluation of the original short exact
  -- sequence at `G.obj d`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (hEval.exact_iff (S.map ((Functor.whiskeringLeft D E A).obj G))).2
      fun d ↦ by
        simpa using (evaluation_shortExact_of_shortExact hS (G.obj d)).exact
  · exact
      (NatTrans.mono_iff_mono_app
        (S.map ((Functor.whiskeringLeft D E A).obj G)).f).2 fun d ↦ by
          simpa using (evaluation_shortExact_of_shortExact hS (G.obj d)).mono_f
  · exact
      (NatTrans.epi_iff_epi_app
        (S.map ((Functor.whiskeringLeft D E A).obj G)).g).2 fun d ↦ by
          simpa using (evaluation_shortExact_of_shortExact hS (G.obj d)).epi_g

/-- Precomposition along any functor is exact on functor categories with abelian codomain. -/
theorem whiskeringLeft_exact
    {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E]
    {A : Type u₃} [Category.{v₃} A] [Abelian A] (G : D ⥤ E) :
    exactFunctor (E ⥤ A) (D ⥤ A)
      ((Functor.whiskeringLeft D E A).obj G) := by
  exact whiskeringLeft_exact_aux G

/-- Restricting abelian presheaves along `(Over.forget U).op` is exact. -/
theorem restrictPresheafToOver_exact
    {C : Type u} [Category.{v} C] (U : C) :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})
      (restrictPresheafToOver U) := by
  -- This is the generic exactness of precomposition, specialized to the forgetful functor.
  simpa [restrictPresheafToOver] using whiskeringLeft_exact ((Over.forget U).op)

/-- Helper for Lemma 21.9.1: the discrete diagram of componentwise evaluations attached to a
formal coproduct. -/
private abbrev formal_coproduct_componentwise_diagram
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] (X : FormalCoproduct.{w} C) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ Discrete X.I ⥤ AddCommGrpCat.{v} :=
  (Functor.whiskeringLeft (Discrete X.I) Cᵒᵖ AddCommGrpCat.{v}).obj
    (Discrete.functor (fun i : X.I ↦ Opposite.op (X.obj i)))

/-- Helper for Lemma 21.9.1: the product of the componentwise evaluations of a formal coproduct. -/
private abbrev formal_coproduct_componentwise_functor
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] (X : FormalCoproduct.{w} C) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v} :=
  (formal_coproduct_componentwise_diagram X) ⋙
    (lim : (Discrete X.I ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v})

/-- Helper for Lemma 21.9.1: the product functor on a discrete diagram of abelian groups is exact. -/
private noncomputable instance discreteLimitFunctor_preservesEpimorphisms
    [HasProducts AddCommGrpCat.{v}] (I : Type w) :
    (lim : (Discrete I ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    let y' : limit (Y ⋙ forget AddCommGrpCat.{v}) :=
      (preservesLimitIso (forget AddCommGrpCat.{v}) Y).hom y
    let sy : (Y ⋙ forget AddCommGrpCat.{v}).sections :=
      (Types.limitEquivSections (Y ⋙ forget AddCommGrpCat.{v})) y'
    let sx : (X ⋙ forget AddCommGrpCat.{v}).sections := {
      val := fun j ↦
        Classical.choose ((AddCommGrpCat.epi_iff_surjective (f.app j)).mp inferInstance (sy.val j))
      property := by
        intro i j g
        cases i
        cases j
        rcases g with ⟨h⟩
        rcases h with ⟨e⟩
        cases e
        simp
    }
    let x' := ((Types.limitEquivSections (X ⋙ forget AddCommGrpCat.{v})).symm sx)
    let x : (forget AddCommGrpCat.{v}).obj (limit X) :=
      (preservesLimitIso (forget AddCommGrpCat.{v}) X).inv x'
    refine ⟨x, ?_⟩
    apply Concrete.limit_ext
    intro j
    have hx' := ConcreteCategory.congr_hom
      (preservesLimitIso_inv_π (forget AddCommGrpCat.{v}) X j) x'
    have hx'' :
        (ConcreteCategory.hom (limit.π (X ⋙ forget AddCommGrpCat.{v}) j)) x' = sx.val j := by
      simpa [x', sx] using
        (Types.limitEquivSections_symm_apply (X ⋙ forget AddCommGrpCat.{v}) sx j)
    have hx : (ConcreteCategory.hom (limit.π X j)) x = sx.val j := hx'.trans hx''
    have hy' := ConcreteCategory.congr_hom
      (preservesLimitIso_hom_π (forget AddCommGrpCat.{v}) Y j) y
    have hy'' :
        (ConcreteCategory.hom (limit.π (Y ⋙ forget AddCommGrpCat.{v}) j)) y' = sy.val j := by
      simpa [y', sy] using
        (Types.limitEquivSections_apply (Y ⋙ forget AddCommGrpCat.{v}) y' j)
    have hy : (ConcreteCategory.hom (limit.π Y j)) y = sy.val j := hy'.symm.trans hy''
    have hcomp :
        (ConcreteCategory.hom (limit.π Y j)) ((ConcreteCategory.hom (lim.map f)) x) =
          (ConcreteCategory.hom (f.app j)) ((ConcreteCategory.hom (limit.π X j)) x) := by
      exact ConcreteCategory.congr_hom (limMap_π f j) x
    have hchoose : (ConcreteCategory.hom (f.app j)) (sx.val j) = sy.val j := by
      simpa [sx, sy] using
        (Classical.choose_spec
          ((AddCommGrpCat.epi_iff_surjective (f.app j)).mp inferInstance (sy.val j)))
    exact hcomp.trans ((by rw [hx] : _ = _).trans (hchoose.trans hy.symm))

private theorem discreteLimitFunctor_exact [HasProducts AddCommGrpCat.{v}] (I : Type w) :
    exactFunctor (Discrete I ⥤ AddCommGrpCat.{v}) AddCommGrpCat.{v}
      (lim : (Discrete I ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}) := by
  rw [exactFunctor_iff]
  let _ : (lim : (Discrete I ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).PreservesEpimorphisms :=
    discreteLimitFunctor_preservesEpimorphisms I
  let _ : HasExactLimitsOfShape (Discrete I) AddCommGrpCat.{v} :=
    hasExactLimitsOfShape_of_preservesEpi AddCommGrpCat.{v} (Discrete I)
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 21.9.1: the componentwise evaluation diagram followed by the product functor
is exact. -/
private theorem formal_coproduct_componentwise_exact
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] (X : FormalCoproduct.{w} C) :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v}) AddCommGrpCat.{v}
      (formal_coproduct_componentwise_functor X) := by
  let hPrecomp :
      exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v}) (Discrete X.I ⥤ AddCommGrpCat.{v})
      (formal_coproduct_componentwise_diagram X) := by
    -- Precomposition with the discrete component diagram is exact.
    simpa [formal_coproduct_componentwise_diagram] using whiskeringLeft_exact
      (Discrete.functor (fun i : X.I ↦ Opposite.op (X.obj i)))
  let hLim : exactFunctor (Discrete X.I ⥤ AddCommGrpCat.{v}) AddCommGrpCat.{v}
      (lim : (Discrete X.I ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}) :=
    discreteLimitFunctor_exact X.I
  -- Exactness is stable under composing the evaluation diagram with the product functor.
  simpa [formal_coproduct_componentwise_functor] using exactFunctor_comp hPrecomp hLim

/-- Helper for Lemma 21.9.1: formal-coproduct evaluation is additive on natural transformations. -/
private theorem formal_coproduct_evalOp_map_add_projection
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}]
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (α β : P ⟶ Q) (X : FormalCoproduct.{w} C) (i : X.I) :
    ((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}).map (α + β)).app (Opposite.op X) ≫
        Pi.π (fun j : X.I ↦ Q.obj (Opposite.op (X.obj j))) i =
      ((((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}).map α).app (Opposite.op X)) +
          (((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}).map β).app (Opposite.op X))) ≫
        Pi.π (fun j : X.I ↦ Q.obj (Opposite.op (X.obj j))) i := by
  change
    Limits.Pi.map (fun j : X.I ↦ (α + β).app (Opposite.op (X.obj j))) ≫
        Pi.π (fun j : X.I ↦ Q.obj (Opposite.op (X.obj j))) i =
      (Limits.Pi.map (fun j : X.I ↦ α.app (Opposite.op (X.obj j))) +
          Limits.Pi.map (fun j : X.I ↦ β.app (Opposite.op (X.obj j)))) ≫
        Pi.π (fun j : X.I ↦ Q.obj (Opposite.op (X.obj j))) i
  rw [Preadditive.add_comp, Pi.map_π, Pi.map_π, Pi.map_π]
  simp

/-- Helper for Lemma 21.9.1: formal-coproduct evaluation preserves addition projectionwise. -/
private instance formal_coproduct_evalOp_additive
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] :
    (FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}).Additive where
  map_add := by
    intro P Q α β
    apply NatTrans.ext
    funext X
    apply Pi.hom_ext
    intro i
    simpa [NatTrans.app_add] using
      formal_coproduct_evalOp_map_add_projection α β (Opposite.unop X) i

/-- Helper for Lemma 21.9.1: evaluation on formal coproducts preserves zero morphisms. -/
private instance formal_coproduct_evalOp_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] :
    (FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}).PreservesZeroMorphisms := by
  -- Once additivity is available, zero morphisms are preserved automatically.
  infer_instance

/-- Helper for Lemma 21.9.1: evaluation at a fixed formal coproduct is the product of the
componentwise evaluations. -/
private noncomputable def formal_coproduct_eval_iso_componentwise_limit
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}]
    (X : FormalCoproduct.{w} C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}).obj P).obj (Opposite.op X)) ≅
      ((formal_coproduct_componentwise_functor X).obj P) := by
  let G := formal_coproduct_componentwise_diagram X
  -- The value of `evalOp` at `X` is the product of the evaluations at the components of `X`.
  simpa [formal_coproduct_componentwise_functor, formal_coproduct_componentwise_diagram,
    G, FormalCoproduct.evalOp] using (Pi.isoLimit (G.obj P))

private theorem formal_coproduct_eval_iso_componentwise_limit_hom_π
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}]
    (X : FormalCoproduct.{w} C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (i : X.I) :
    (formal_coproduct_eval_iso_componentwise_limit X P).hom ≫
        limit.π ((formal_coproduct_componentwise_diagram X).obj P) (Discrete.mk i) =
      Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i := by
  simpa [formal_coproduct_eval_iso_componentwise_limit] using
    (Pi.isoLimit_hom_π ((formal_coproduct_componentwise_diagram X).obj P) i)

private theorem formal_coproduct_eval_iso_componentwise_limit_inv_π
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}]
    (X : FormalCoproduct.{w} C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (i : X.I) :
    (formal_coproduct_eval_iso_componentwise_limit X P).inv ≫
        Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i =
      limit.π ((formal_coproduct_componentwise_diagram X).obj P) (Discrete.mk i) := by
  simpa [formal_coproduct_eval_iso_componentwise_limit] using
    (Pi.isoLimit_inv_π ((formal_coproduct_componentwise_diagram X).obj P) i)

/-- Helper for Lemma 21.9.1: the fixed-object comparison above is compatible with a map of
presheaves. -/
private theorem formal_coproduct_eval_iso_componentwise_limit_naturality
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] (X : FormalCoproduct.{w} C)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (α : P ⟶ Q) :
    (((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}).map α).app (Opposite.op X)) ≫
        (formal_coproduct_eval_iso_componentwise_limit X Q).hom =
      (formal_coproduct_eval_iso_componentwise_limit X P).hom ≫
        (formal_coproduct_componentwise_functor X).map α := by
  apply limit.hom_ext
  rintro ⟨i⟩
  have hleft :
      ((((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}).map α).app (Opposite.op X)) ≫
          (formal_coproduct_eval_iso_componentwise_limit X Q).hom) ≫
        limit.π ((formal_coproduct_componentwise_diagram X).obj Q) (Discrete.mk i) =
      Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i ≫ α.app (Opposite.op (X.obj i)) := by
    rw [Category.assoc, formal_coproduct_eval_iso_componentwise_limit_hom_π]
    change Limits.Pi.map (fun k : X.I ↦ α.app (Opposite.op (X.obj k))) ≫
        Pi.π (fun k : X.I ↦ Q.obj (Opposite.op (X.obj k))) i =
      Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i ≫ α.app (Opposite.op (X.obj i))
    simpa using Pi.map_π (fun k : X.I ↦ α.app (Opposite.op (X.obj k))) i
  have hright :
      (((formal_coproduct_eval_iso_componentwise_limit X P).hom ≫
            (formal_coproduct_componentwise_functor X).map α) ≫
          limit.π ((formal_coproduct_componentwise_diagram X).obj Q) (Discrete.mk i)) =
        Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i ≫ α.app (Opposite.op (X.obj i)) := by
    have hπ :
        ((formal_coproduct_eval_iso_componentwise_limit X P).hom ≫
            limit.π ((formal_coproduct_componentwise_diagram X).obj P) (Discrete.mk i)) ≫
          α.app (Opposite.op (X.obj i)) =
        Pi.π (fun k : X.I ↦ P.obj (Opposite.op (X.obj k))) i ≫ α.app (Opposite.op (X.obj i)) := by
      simpa [Category.assoc] using
        congrArg (fun m ↦ m ≫ α.app (Opposite.op (X.obj i)))
          (formal_coproduct_eval_iso_componentwise_limit_hom_π X P i)
    have hmid :
        (((formal_coproduct_eval_iso_componentwise_limit X P).hom ≫
              (formal_coproduct_componentwise_functor X).map α) ≫
            limit.π ((formal_coproduct_componentwise_diagram X).obj Q) (Discrete.mk i)) =
          ((formal_coproduct_eval_iso_componentwise_limit X P).hom ≫
              limit.π ((formal_coproduct_componentwise_diagram X).obj P) (Discrete.mk i)) ≫
            α.app (Opposite.op (X.obj i)) := by
      simp [Category.assoc]
      simpa using congrArg
        (fun m ↦ (formal_coproduct_eval_iso_componentwise_limit X P).hom ≫ m)
        (limMap_π ((Discrete.functor fun k : X.I ↦ Opposite.op (X.obj k)).whiskerLeft α)
          (Discrete.mk i))
    exact hmid.trans hπ
  exact hleft.trans hright.symm

/-- Helper for Lemma 21.9.1: fixed-object evaluation of `FormalCoproduct.evalOp` is naturally the
product of the componentwise evaluations. -/
private noncomputable def formal_coproduct_eval_natIso_componentwise_limit
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] (X : FormalCoproduct.{w} C) :
    ((((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}) ⋙
        (evaluation (FormalCoproduct.{w} C)ᵒᵖ AddCommGrpCat.{v}).obj (Opposite.op X)) :
      (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v})) ≅
      formal_coproduct_componentwise_functor X :=
  NatIso.ofComponents
    (formal_coproduct_eval_iso_componentwise_limit X)
    (fun α ↦ formal_coproduct_eval_iso_componentwise_limit_naturality X α)

/-- Helper for Lemma 21.9.1: the product of componentwise evaluations preserves zero morphisms. -/
private instance formal_coproduct_componentwise_functor_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] (X : FormalCoproduct.{w} C) :
    (formal_coproduct_componentwise_functor X).PreservesZeroMorphisms := by
  -- The componentwise diagram and the product functor both preserve zero morphisms.
  dsimp [formal_coproduct_componentwise_functor, formal_coproduct_componentwise_diagram]
  infer_instance

/-- Helper for Lemma 21.9.1: evaluation at a fixed formal coproduct sends short exact sequences of
presheaves to short exact sequences of abelian groups. -/
private theorem formal_coproduct_componentwise_shortExact_of_shortExact
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] (X : FormalCoproduct.{w} C)
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v})} (hS : S.ShortExact) :
    (S.map (formal_coproduct_componentwise_functor X)).ShortExact := by
  let Fcomp := formal_coproduct_componentwise_functor X
  let hFcomp := formal_coproduct_componentwise_exact X
  letI : Fcomp.PreservesZeroMorphisms :=
    formal_coproduct_componentwise_functor_preservesZeroMorphisms X
  letI : Fcomp.Additive :=
    (exactFunctor_le_additiveFunctor
      (Cᵒᵖ ⥤ AddCommGrpCat.{v}) AddCommGrpCat.{v}) Fcomp hFcomp
  let hMap := (Functor.exact_tfae Fcomp).out 3 0 |>.1 <| by
    simpa [Fcomp, exactFunctor_iff] using hFcomp
  -- This is the source proof's "products of exact evaluations are exact", frozen in one functor.
  simpa [Fcomp] using hMap S hS

/-- Helper for Lemma 21.9.1: evaluation at a fixed formal coproduct sends short exact sequences of
presheaves to short exact sequences of abelian groups. -/
private theorem formal_coproduct_eval_shortExact_of_shortExact
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}] (X : FormalCoproduct.{w} C)
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v})} (hS : S.ShortExact) :
    (S.map ((((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}) ⋙
        (evaluation (FormalCoproduct.{w} C)ᵒᵖ AddCommGrpCat.{v}).obj (Opposite.op X)) :
      (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}))).ShortExact := by
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (formal_coproduct_eval_natIso_componentwise_limit X)).symm
    (formal_coproduct_componentwise_shortExact_of_shortExact X hS)

/-- Helper for Lemma 21.9.1: the formal-coproduct cochain complex functor is additive degreewise. -/
private instance formal_coproduct_cochainComplexFunctor_additive
    {C : Type u} [Category.{v} C] [HasProducts AddCommGrpCat.{v}]
    {E : SimplicialObject (FormalCoproduct.{w} C)} :
    ((FormalCoproduct.cochainComplexFunctor E :
        (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ CochainComplex AddCommGrpCat.{v} ℕ)).Additive where
  map_add := by
    intro P Q α β
    -- Route correction: the complex map is determined degreewise, so we reduce to the additive
    -- computation for fixed-object `evalOp`.
    apply HomologicalComplex.Hom.ext
    funext n
    let F :
        (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v} :=
      ((FormalCoproduct.evalOp.{w} C AddCommGrpCat.{v}) ⋙
        (evaluation (FormalCoproduct.{w} C)ᵒᵖ AddCommGrpCat.{v}).obj
          (Opposite.op (E.obj (Opposite.op (SimplexCategory.mk n)))))
    simpa [FormalCoproduct.cochainComplexFunctor, FormalCoproduct.cosimplicialObjectFunctor, F]
      using Functor.map_add F

/-- Helper for Lemma 21.9.1: the canonical Čech cochain complex functor on `Over U` is exact. -/
theorem cechComplexFunctor_exact
    {C : Type u} [Category.{v} C] (U : C) [HasFiniteProducts (Over U)]
    [HasProducts AddCommGrpCat.{v}] {ι : Type w}
    (family : ι → Over U) :
    exactFunctor ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}) (CochainComplex AddCommGrpCat.{v} ℕ)
      (cechComplexFunctor family) := by
  let F : ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
    cechComplexFunctor family
  let E : SimplicialObject (FormalCoproduct.{w} (Over U)) := (FormalCoproduct.mk _ family).cech
  letI : F.Additive := by
    simpa [F, cechComplexFunctor, E] using
      (inferInstance :
        ((FormalCoproduct.cochainComplexFunctor E :
            ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ CochainComplex AddCommGrpCat.{v} ℕ)).Additive)
  change exactFunctor _ _ F
  refine ((Functor.exact_tfae F).out 3 0).2 ?_
  intro S hS
  -- A short exact sequence of cochain complexes is equivalent to short exactness in each degree.
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  -- In degree `n`, the Čech complex is exactly evaluation at the `n`-th Čech formal coproduct.
  simpa [F, cechComplexFunctor, E, FormalCoproduct.cochainComplexFunctor,
    FormalCoproduct.cosimplicialObjectFunctor] using
    formal_coproduct_eval_shortExact_of_shortExact (E.obj (Opposite.op (SimplexCategory.mk n))) hS

/- Domain-style sampling for Lemma 21.9.1:
- primary domain: Čech complexes of abelian presheaves on a slice site and exact functors between
  abelian categories;
- sampled owner declarations:
  `cechComplexOnPresheaves`,
  `CategoryTheory.cechComplexFunctor`,
  `restrictPresheafToOver`,
  `CategoryTheory.exactFunctor`,
  `CategoryTheory.exactFunctor_iff`;
- best owner abstraction: the `source-facing` owner for this lemma is
  `cechComplexOnPresheaves U family`, already introduced in `21.9.0.1`; the underlying
  `cechComplexFunctor family` on `Over U` is the `core/canonical` owner, while restriction along
  `(Over.forget U).op` is the essential bridge and must remain visible in the public statement.
- primitive data: the base object `U`, the family `family : ι → Over U`, and the exact-functor
  predicate.
- derived API: the exactness witness below.

Source/core/bridge triage:
- `source-facing`: the exactness statement for the restriction-plus-Čech complex functor on
  abelian presheaves over `C`;
- `core/canonical`: `cechComplexFunctor family` and `exactFunctor`;
- `bridge/view`: `restrictPresheafToOver U`.
-/
/-- Lemma 21.9.1: for a family `family : ι → Over U`, the functor of `21.9.0.1`, namely
`cechComplexOnPresheaves U family`, is exact on abelian presheaves on `C`. -/
-- Proof sketch: restriction along `(Over.forget U).op` is exact on abelian presheaves, and the
-- Čech complex functor on `Over U` is exact degreewise because each term is a product of exact
-- evaluation functors. Exactness is stable under composition, so the source-facing composite
-- `cechComplexOnPresheaves U family` is exact.
@[stacks 03AQ]
theorem cechComplexOnPresheaves_exact
    {C : Type u} [Category.{v} C] (U : C) [HasFiniteProducts (Over U)]
    [HasProducts AddCommGrpCat.{v}] {ι : Type w}
    (family : ι → Over U) :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{v}) (CochainComplex AddCommGrpCat.{v} ℕ)
      (cechComplexOnPresheaves U family) := by
  let hRestr := restrictPresheafToOver_exact U
  let hCech := cechComplexFunctor_exact U family
  -- The source-facing functor is the composite of exact restriction and exact Čech construction.
  simpa [cechComplexOnPresheaves] using exactFunctor_comp hRestr hCech

end CategoryTheory
