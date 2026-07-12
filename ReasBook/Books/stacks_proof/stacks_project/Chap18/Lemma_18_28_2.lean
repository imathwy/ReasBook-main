import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_12
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite MonoidalCategory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/- Domain-style sampling for Lemma 18.28.2:
- primary domain: flatness of presheaves of modules, owned by exactness of tensoring with a fixed
  presheaf module;
- sampled owner declarations:
  `PresheafOfModules.IsFlat`,
  `CategoryTheory.exactFunctor`,
  `Module.Flat.iff_preservesFiniteLimits_tensorRight`,
  `ringPresheaf`;
- best owner abstraction: `PresheafOfModules.IsFlat` from `Definition_18_28_1`, whose primitive
  data is exactness of the tensor-right endofunctor on `PresheafOfModules (ringPresheaf 𝒪)`;
- primitive data: a presheaf module `ℱ : PresheafOfModules (ringPresheaf 𝒪)` and the sectionwise
  module-flatness hypothesis;
- derived API: the owner-side flatness instance `IsFlat ℱ`.

Source/core/bridge triage:
- `source-facing`: the textbook criterion that sectionwise flatness implies flatness of the
  presheaf;
- `core/canonical`: `PresheafOfModules.IsFlat`;
- `bridge/view`: the objectwise-module criterion below upgrading sectionwise flatness to the
  canonical owner.

There is no upstream theorem in the chapter or mathlib with this exact interface, so this file
should keep the source-facing bridge theorem rather than introduce a parallel owner wrapper or try
to collapse the statement to a bare recall.
-/

-- Proof sketch: map a short exact complex by `tensorRight ℱ` and evaluate at each object `X`.
-- Objectwise this is the ordinary functor `tensorRight (ℱ(X))` on `ModuleCat (𝒪(X))`, so
-- sectionwise flatness makes the evaluated complex short exact. Exactness is then reflected back
-- by the evaluation family, while pointwise injectivity and surjectivity give the required mono
-- and epi statements on presheaves.
/-- Helper for Lemma 18.28.2: the inverse of an objectwise isomorphism of presheaf modules,
viewed at a single object. -/
private def evaluation_inverse_app
    {M N : PresheafOfModules (ringPresheaf 𝒪)}
    (f : M ⟶ N)
    (hf : ∀ X : Cᵒᵖ, IsIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f))
    (X : Cᵒᵖ) : N.obj X ⟶ M.obj X :=
  let _ : IsIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f) := hf X
  (asIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f)).inv

/-- Helper for Lemma 18.28.2: the objectwise inverse composed after the original map is the
identity. -/
private theorem evaluation_hom_comp_inverse
    {M N : PresheafOfModules (ringPresheaf 𝒪)}
    (f : M ⟶ N)
    (hf : ∀ X : Cᵒᵖ, IsIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f))
    (X : Cᵒᵖ) :
    f.app X ≫ evaluation_inverse_app (𝒪 := 𝒪) f hf X = 𝟙 (M.obj X) := by
  -- This is the objectwise `hom_inv_id` identity for the evaluated isomorphism.
  let _ : IsIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f) := hf X
  simpa [evaluation_inverse_app] using
    (asIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f)).hom_inv_id

/-- Helper for Lemma 18.28.2: the original map composed after the objectwise inverse is the
identity. -/
private theorem evaluation_inverse_comp_hom
    {M N : PresheafOfModules (ringPresheaf 𝒪)}
    (f : M ⟶ N)
    (hf : ∀ X : Cᵒᵖ, IsIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f))
    (X : Cᵒᵖ) :
    evaluation_inverse_app (𝒪 := 𝒪) f hf X ≫ f.app X = 𝟙 (N.obj X) := by
  -- This is the objectwise `inv_hom_id` identity for the evaluated isomorphism.
  let _ : IsIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f) := hf X
  simpa [evaluation_inverse_app] using
    (asIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f)).inv_hom_id

/-- Helper for Lemma 18.28.2: the objectwise inverses of an objectwise isomorphism assemble into a
presheaf-module morphism. -/
private theorem evaluation_inverse_app_natural
    {M N : PresheafOfModules (ringPresheaf 𝒪)}
    (f : M ⟶ N)
    (hf : ∀ X : Cᵒᵖ, IsIso ((PresheafOfModules.evaluation (ringPresheaf 𝒪) X).map f))
    {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    N.map g ≫
        ((ModuleCat.restrictScalars (RingCat.Hom.hom ((ringPresheaf 𝒪).map g))).map
          (evaluation_inverse_app (𝒪 := 𝒪) f hf Y)) =
      evaluation_inverse_app (𝒪 := 𝒪) f hf X ≫ M.map g := by
  -- Postcompose with `f.app Y`; the inverse identities and naturality of `f` then match both
  -- sides, so cancellation proves the desired naturality for the inverse family.
  let restrictFunctor :=
    ModuleCat.restrictScalars (RingCat.Hom.hom ((ringPresheaf 𝒪).map g))
  letI : IsIso (restrictFunctor.map (f.app Y)) := by
    let _ : IsIso (f.app Y) := hf Y
    infer_instance
  apply (cancel_mono (restrictFunctor.map (f.app Y))).1
  calc
    N.map g ≫
        ((restrictFunctor.map (evaluation_inverse_app (𝒪 := 𝒪) f hf Y)) ≫
          restrictFunctor.map (f.app Y)) =
      N.map g := by
        rw [← Functor.map_comp, evaluation_inverse_comp_hom]
        have hmap_id : restrictFunctor.map (𝟙 (N.obj Y)) = 𝟙 _ := by
          simp
        rw [hmap_id, Category.comp_id]
    _ = (evaluation_inverse_app (𝒪 := 𝒪) f hf X ≫ f.app X) ≫ N.map g := by
        rw [evaluation_inverse_comp_hom]
        rw [Category.id_comp]
    _ = evaluation_inverse_app (𝒪 := 𝒪) f hf X ≫
          (f.app X ≫ N.map g) := by
        rfl
    _ = evaluation_inverse_app (𝒪 := 𝒪) f hf X ≫
          (M.map g ≫ restrictFunctor.map (f.app Y)) := by
        rw [PresheafOfModules.Hom.naturality f g]
    _ = evaluation_inverse_app (𝒪 := 𝒪) f hf X ≫ M.map g ≫
          restrictFunctor.map (f.app Y) := by
        simp

/-- Helper for Lemma 18.28.2: evaluation at all objects jointly reflects isomorphisms of
presheaves of modules. -/
private theorem evaluation_jointly_reflects_isomorphisms :
    JointlyReflectIsomorphisms
      (fun X : Cᵒᵖ ↦ PresheafOfModules.evaluation (ringPresheaf 𝒪) X) := by
  refine ⟨fun {M N} f hf ↦ ?_⟩
  let g : N ⟶ M :=
    { app := evaluation_inverse_app (𝒪 := 𝒪) f hf
      naturality := evaluation_inverse_app_natural (𝒪 := 𝒪) f hf }
  -- The objectwise inverse family gives a two-sided inverse of `f`.
  refine ⟨⟨g, ?_, ?_⟩⟩
  · ext X x
    simpa [g] using congrArg (fun u : M.obj X ⟶ M.obj X => (ModuleCat.Hom.hom u) x)
      (evaluation_hom_comp_inverse (𝒪 := 𝒪) f hf X)
  · ext X x
    simpa [g] using congrArg (fun u : N.obj X ⟶ N.obj X => (ModuleCat.Hom.hom u) x)
      (evaluation_inverse_comp_hom (𝒪 := 𝒪) f hf X)

/-- Helper for Lemma 18.28.2: evaluation functors on an ordinary functor category jointly reflect
isomorphisms. -/
private theorem functorEvaluationJointlyReflectsIsomorphisms
    {J A : Type*} [Category J] [Category A] :
    JointlyReflectIsomorphisms
      ((CategoryTheory.evaluation J A).obj : J → (J ⥤ A) ⥤ A) := by
  -- A natural transformation is an isomorphism once all of its components are.
  refine ⟨fun {F G} α _ ↦ ?_⟩
  -- Route correction: use the direct iff constructor instead of rewriting the goal, so the
  -- objectwise `IsIso` instances assemble without an extra goal-shape change.
  refine (NatTrans.isIso_iff_isIso_app α).2 ?_
  intro j
  simpa using (inferInstance : IsIso (((CategoryTheory.evaluation J A).obj j).map α))

/-- Helper for Lemma 18.28.2: evaluating a short exact row in a functor category stays short
exact. -/
private theorem shortExactEvalFunctorCategory
    {J A : Type*} [Category J] [Category A] [Abelian A]
    {S : ShortComplex (J ⥤ A)} (hS : S.ShortExact) (j : J) :
    (S.map ((CategoryTheory.evaluation J A).obj j)).ShortExact := by
  -- Exactness, monomorphy, and epimorphy in a functor category are all checked componentwise.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      ((functorEvaluationJointlyReflectsIsomorphisms (J := J) (A := A)).exact_iff S).1
        hS.exact j
  · exact (NatTrans.mono_iff_mono_app S.f).1 hS.mono_f j
  · exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g j

/-- Helper for Lemma 18.28.2: evaluating a short exact row of presheaf modules at a fixed object
gives a short exact row of section modules. -/
private theorem evaluationShortExactOfShortExact
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact) (X : Cᵒᵖ) :
    (S.map (PresheafOfModules.evaluation (ringPresheaf 𝒪) X)).ShortExact := by
  let F := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
  let G : ModuleCat ((ringPresheaf 𝒪).obj X) ⥤ AddCommGrpCat.{max u v} :=
    forget (ModuleCat ((ringPresheaf 𝒪).obj X))
  have hToPresheaf :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
        (PresheafOfModules.toPresheaf (ringPresheaf 𝒪)) :=
    (ExactFunctor.of (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).property
  have hUnderlying :
      (S.map (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).ShortExact := by
    -- First forget to additive presheaves, where evaluation is literal functor evaluation.
    exact
      ((Functor.exact_tfae (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).out 3 0).1
        (by simpa [exactFunctor_iff] using hToPresheaf) S hS
  have hForget : ((S.map F).map G).ShortExact := by
    -- After forgetting the module structure, evaluating is exactly ordinary functor evaluation.
    change
      ((S.map (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).map
        ((CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj X)).ShortExact
    exact
      shortExactEvalFunctorCategory
        (S := S.map (PresheafOfModules.toPresheaf (ringPresheaf 𝒪)))
        hUnderlying X
  -- Faithfulness of the forgetful functor reflects the short exactness back to modules.
  exact ShortComplex.reflects_shortExact_of_faithful G hForget

/-- Helper for Lemma 18.28.2: after evaluating at `X`, tensoring with `ℱ` becomes right tensoring
with the flat module `ℱ(X)`, so short exact sequences stay short exact. -/
private theorem evaluation_tensorRight_shortExact
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ U : C, Module.Flat (𝒪.obj (op U)) (ℱ.obj (op U)))
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact) (X : Cᵒᵖ) :
    ((S.map (tensorRight ℱ)).map (PresheafOfModules.evaluation (ringPresheaf 𝒪) X)).ShortExact := by
  let evalX := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
  letI : MonoidalCategory (ModuleCat ((ringPresheaf 𝒪).obj X)) := inferInstance
  have hSX : (S.map evalX).ShortExact :=
    evaluationShortExactOfShortExact (𝒪 := 𝒪) hS X
  letI : Module.Flat ((ringPresheaf 𝒪).obj X) (ℱ.obj X) := by
    simpa using hflat (unop X)
  have hExact : ((S.map evalX).map (tensorRight (ℱ.obj X))).Exact := by
    -- Flatness of the section module preserves exactness after evaluation.
    exact Module.Flat.rTensor_shortComplex_exact (M := ℱ.obj X) (S.map evalX) hSX.exact
  have hMono : Mono (((S.map evalX).map (tensorRight (ℱ.obj X))).f) := by
    -- Tensoring on the right by a flat module preserves injectivity of the left map.
    refine (ModuleCat.mono_iff_injective _).2 ?_
    have hf : Function.Injective (ModuleCat.Hom.hom (S.map evalX).f) :=
      (ModuleCat.mono_iff_injective _).1 hSX.mono_f
    simpa using
      Module.Flat.rTensor_preserves_injective_linearMap (M := ℱ.obj X)
        (ModuleCat.Hom.hom (S.map evalX).f) hf
  have hEpi : Epi (((S.map evalX).map (tensorRight (ℱ.obj X))).g) := by
    -- Tensor products are right exact, so surjectivity of the right map is preserved.
    refine (ModuleCat.epi_iff_surjective _).2 ?_
    have hg : Function.Surjective (ModuleCat.Hom.hom (S.map evalX).g) :=
      (ModuleCat.epi_iff_surjective _).1 hSX.epi_g
    simpa using LinearMap.rTensor_surjective (Q := ℱ.obj X) hg
  have hMapped : ((S.map evalX).map (tensorRight (ℱ.obj X))).ShortExact := by
    -- Assemble exactness, monomorphy, and epimorphy into the mapped short exact row.
    exact ShortComplex.ShortExact.mk' hExact hMono hEpi
  -- Evaluating after tensoring with a presheaf module is the pointwise tensor product.
  change ((S.map evalX).map (tensorRight (ℱ.obj X))).ShortExact
  exact hMapped

/-- Helper for Lemma 18.28.2: tensoring on the right by a sectionwise flat presheaf module sends
short exact complexes to exact complexes with mono first map and epi second map. -/
private theorem tensorRight_maps_shortExact_of_flat_sections
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ U : C, Module.Flat (𝒪.obj (op U)) (ℱ.obj (op U)))
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight ℱ).map S.f) ((tensorRight ℱ).map S.g)).Exact ∧
      Mono ((tensorRight ℱ).map S.f) ∧ Epi ((tensorRight ℱ).map S.g) := by
  let T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) := S.map (tensorRight ℱ)
  have hT_exact : T.Exact := by
    letI : ∀ X : Cᵒᵖ, (PresheafOfModules.evaluation (ringPresheaf 𝒪) X).Additive := fun X ↦ by
      infer_instance
    letI :
        ∀ X : Cᵒᵖ,
          (PresheafOfModules.evaluation (ringPresheaf 𝒪) X).PreservesZeroMorphisms := fun X ↦ by
        letI : (PresheafOfModules.evaluation (ringPresheaf 𝒪) X).Additive := by
          infer_instance
        infer_instance
    -- Exactness is detected sectionwise because evaluation jointly reflects isomorphisms.
    exact ((evaluation_jointly_reflects_isomorphisms (𝒪 := 𝒪)).exact_iff T).2
      fun X ↦ (evaluation_tensorRight_shortExact (ℱ := ℱ) hflat S hS X).exact
  have hT_mono : Mono T.f := by
    -- Monomorphisms of presheaves of modules are detected pointwise by injectivity.
    refine PresheafOfModules.mono_of_injective ?_
    intro X
    let evalX := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
    let hTX := evaluation_tensorRight_shortExact (ℱ := ℱ) hflat S hS X
    letI : Mono ((T.map evalX).f) := hTX.mono_f
    simpa [T, evalX] using (ModuleCat.mono_iff_injective ((T.map evalX).f)).1 inferInstance
  have hT_epi : Epi T.g := by
    -- Epimorphisms of presheaves of modules are detected pointwise by surjectivity.
    refine PresheafOfModules.epi_of_surjective ?_
    intro X
    let evalX := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
    let hTX := evaluation_tensorRight_shortExact (ℱ := ℱ) hflat S hS X
    letI : Epi ((T.map evalX).g) := hTX.epi_g
    simpa [T, evalX] using (ModuleCat.epi_iff_surjective ((T.map evalX).g)).1 inferInstance
  -- Package the three conditions in the exact-functor criterion from Chapter 12.
  refine ⟨?_, hT_mono, hT_epi⟩
  simpa [T] using (T.exact_iff_exact_toComposableArrows).1 hT_exact

/-- Helper for Lemma 18.28.2: the tensor-right endofunctor is exact once all section modules of
`ℱ` are flat. -/
private theorem tensorRight_exact_of_flat_sections
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ U : C, Module.Flat (𝒪.obj (op U)) (ℱ.obj (op U))) :
    exactFunctor
      (PresheafOfModules (ringPresheaf 𝒪))
      (PresheafOfModules (ringPresheaf 𝒪))
      (tensorRight ℱ) := by
  -- Apply the Chapter 12 exact-functor criterion using the short-exactness package above.
  exact
    (CategoryTheory.functor_exact_iff_maps_shortExact_to_exact_mono_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorRight ℱ)).2
      fun S hS ↦ tensorRight_maps_shortExact_of_flat_sections (ℱ := ℱ) hflat S hS

/-- Lemma 18.28.2: if each section module `\mathcal F(U)` is flat over `\mathcal O(U)`, then the
presheaf `\mathcal F` is flat in the canonical owner `PresheafOfModules.IsFlat`. -/
@[stacks 03ES]
theorem isFlat_of_flat_obj
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ U : C, Module.Flat (𝒪.obj (op U)) (ℱ.obj (op U))) :
    IsFlat ℱ := by
  -- Route correction: the old prerequisite-repair route was stale; the source-faithful proof is
  -- to detect exactness objectwise after evaluation and then reassemble it on presheaves.
  -- The extracted helper packages the exact-functor criterion for tensoring with `ℱ`.
  refine ⟨?_⟩
  exact tensorRight_exact_of_flat_sections (ℱ := ℱ) hflat

end PresheafOfModules
