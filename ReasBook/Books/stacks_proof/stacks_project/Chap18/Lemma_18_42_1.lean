import Mathlib
import Mathlib.CategoryTheory.Sites.LeftExact

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open Opposite

variable {C : Type u} [Category.{v} C]
/- Domain-style sampling:
- primary domain: constant presheaves/sheaves of abelian groups on a site and preservation of
  short exact sequences by exact functors;
- sampled owner declarations:
  `Functor.const`,
  `constantSheaf`,
  `presheafToSheaf`,
  `sheafToPresheaf`,
  `(evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj`,
  `ShortComplex.ShortExact.map_of_exact`;
- best owner abstraction: the exact-functor factorization
  `Functor.const Cᵒᵖ ⋙ presheafToSheaf J AddCommGrpCat.{max u v}`, whose sheaf-level owner is
  `constantSheaf J AddCommGrpCat.{max u v}`, with the source-facing presheaf/sections views
  obtained by composing with `sheafToPresheaf` and evaluation at `op U`;
- primitive data: the short exact sequence `S` in `AddCommGrpCat`, plus the site `J` for the
  sheafification stage;
- derived API: the constant-presheaf step is the internal bridge supplied directly by
  `ShortComplex.ShortExact.map_of_exact`; the sheaf-level theorem is obtained by applying exact
  sheafification, while the presheaf/sections clauses are expressed using the canonical underlying
  presheaf and evaluation functors.

Source/core/bridge triage:
- `source-facing`: `shortExact_constantAbelianSheaf` together with the presheaf/sections
  companions below;
- `core/canonical`: `Functor.const Cᵒᵖ`, `constantSheaf J AddCommGrpCat.{max u v}`,
  `presheafToSheaf J AddCommGrpCat.{max u v}`, `sheafToPresheaf J AddCommGrpCat.{max u v}`,
  `(evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj`, and
  `ShortComplex.ShortExact.map_of_exact`;
- `bridge/view`: the intermediate constant-presheaf short exactness step
  `hS.map_of_exact (Functor.const Cᵒᵖ)` together with its images under
  `sheafToPresheaf` and evaluation.

The source statement is about constant sheaves on a site, so the main labeled entry remains at the
`constantSheaf` owner. Since the textbook lemma also records exactness after forgetting to abelian
presheaves, the file should expose that bridge explicitly rather than silently collapsing to the
sheaf-category statement. The underlying-presheaf and sectionwise clauses therefore appear as
separate source-facing companions, phrased via `sheafToPresheaf` and evaluation. -/

variable {J : GrothendieckTopology C}

local instance constantSheaf_preservesZeroMorphisms
    [HasWeakSheafify J AddCommGrpCat.{max u v}] :
    (constantSheaf J AddCommGrpCat.{max u v}).PreservesZeroMorphisms := by
  dsimp [constantSheaf]
  infer_instance

-- Proof sketch: `constantSheaf J AddCommGrpCat` is `Functor.const Cᵒᵖ ⋙ presheafToSheaf`, so the
-- sheaf statement follows from the presheaf bridge together with exactness of `presheafToSheaf`.
/-- Lemma 18.42.1: for a site `(\mathcal C, J)`, a short exact sequence of abelian groups remains
short exact after applying the constant abelian sheaf functor
`constantSheaf J AddCommGrpCat`. -/
@[stacks 093J]
theorem shortExact_constantAbelianSheaf
    (S : ShortComplex AddCommGrpCat.{max u v}) (hS : S.ShortExact) :
    (S.map (constantSheaf J AddCommGrpCat.{max u v})).ShortExact := by
  have hPresheaf :
      (S.map
        (Functor.const Cᵒᵖ :
          AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v})).ShortExact := by
    simpa using
      hS.map_of_exact
        (Functor.const Cᵒᵖ :
          AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
  simpa [constantSheaf] using
    (hPresheaf.map_of_exact
      (presheafToSheaf J AddCommGrpCat.{max u v}))

/-- Helper for Lemma 18.42.1: a set-theoretic section of the original surjection induces a
sectionwise right inverse on the underlying set-valued constant sheaf map. -/
lemma constant_abelian_sheaf_app_surjective
    (S : ShortComplex AddCommGrpCat.{max u v}) (s : S.X₃ → S.X₂)
    (hs : Function.RightInverse s S.g.hom) (U : C) :
    Function.Surjective
      ((((S.map (constantSheaf J AddCommGrpCat.{max u v})).map
          (sheafToPresheaf J AddCommGrpCat.{max u v})).map
          ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U))).g).hom := by
  let E := constantCommuteCompose J (forget AddCommGrpCat.{max u v})
  let e₂ :=
    ((sheafToPresheaf J (Type (max u v))).mapIso (E.app S.X₂)).app (op U)
  let e₃ :=
    ((sheafToPresheaf J (Type (max u v))).mapIso (E.app S.X₃)).app (op U)
  let σ :
      (constantSheaf J (Type (max u v))).obj ((forget AddCommGrpCat.{max u v}).obj S.X₃) ⟶
        (constantSheaf J (Type (max u v))).obj ((forget AddCommGrpCat.{max u v}).obj S.X₂) :=
    (constantSheaf J (Type (max u v))).map s
  let T :=
    (((S.map (constantSheaf J AddCommGrpCat.{max u v})).map
        (sheafToPresheaf J AddCommGrpCat.{max u v})).map
        ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)))
  intro y
  let x :
      T.X₂ :=
    e₂.inv ((σ.hom.app (op U)) (e₃.hom y))
  refine ⟨x, ?_⟩
  have he₃ :
      Function.LeftInverse e₃.inv e₃.hom := by
    intro z
    exact CategoryTheory.hom_inv_id_apply e₃ z
  apply he₃.injective
  -- Compare the underlying constant abelian-sheaf map with the constant sheaf map in `Type`.
  have hnat :
      e₃.hom (T.g.hom x) =
        (((constantSheaf J (Type (max u v))).map
          ((forget AddCommGrpCat.{max u v}).map S.g)).hom.app (op U))
          (e₂.hom x) := by
    have hnat' :
        ((((constantSheaf J AddCommGrpCat.{max u v}) ⋙
            sheafCompose J (forget AddCommGrpCat.{max u v})).map S.g) ≫
            (E.hom.app S.X₃)).hom.app (op U) =
          (((E.hom.app S.X₂) ≫
            ((forget AddCommGrpCat.{max u v}) ⋙
              constantSheaf J (Type (max u v))).map S.g).hom.app (op U)) := by
      exact
        congrArg
          (fun α :
            ((constantSheaf J AddCommGrpCat.{max u v} ⋙
                sheafCompose J (forget AddCommGrpCat.{max u v})).obj S.X₂) ⟶
              ((forget AddCommGrpCat.{max u v} ⋙
                  constantSheaf J (Type (max u v))).obj S.X₃) =>
            α.hom.app (op U))
          (E.hom.naturality S.g)
    simpa [T, E, e₂, e₃] using ConcreteCategory.congr_hom hnat' x
  have he₂ :
      e₂.hom x =
        (σ.hom.app (op U)) (e₃.hom y) := by
    exact CategoryTheory.inv_hom_id_apply e₂ ((σ.hom.app (op U)) (e₃.hom y))
  have hs_comp :
      s ≫ (forget AddCommGrpCat.{max u v}).map S.g =
        𝟙 ((forget AddCommGrpCat.{max u v}).obj S.X₃) := by
    ext z
    exact hs z
  -- Apply functoriality of the constant sheaf in `Type` to the right inverse relation.
  have hσ :
      (((constantSheaf J (Type (max u v))).map
          ((forget AddCommGrpCat.{max u v}).map S.g)).hom.app (op U))
          ((σ.hom.app (op U)) (e₃.hom y)) =
        e₃.hom y := by
    have hmap :
        σ ≫
            (constantSheaf J (Type (max u v))).map
              ((forget AddCommGrpCat.{max u v}).map S.g) =
          𝟙 _ := by
      have hmapComp :
          (constantSheaf J (Type (max u v))).map
              (s ≫ (forget AddCommGrpCat.{max u v}).map S.g) =
            (constantSheaf J (Type (max u v))).map (𝟙 ((forget AddCommGrpCat.{max u v}).obj S.X₃)) :=
        congrArg ((constantSheaf J (Type (max u v))).map) hs_comp
      have hmap₁ :
          σ ≫
              (constantSheaf J (Type (max u v))).map
                ((forget AddCommGrpCat.{max u v}).map S.g) =
            (constantSheaf J (Type (max u v))).map
              (s ≫ (forget AddCommGrpCat.{max u v}).map S.g) := by
        rw [← Functor.map_comp]
        rfl
      exact hmap₁.trans (hmapComp.trans (by rw [Functor.map_id]))
    have hσ' :
        ((σ ≫
            (constantSheaf J (Type (max u v))).map
              ((forget AddCommGrpCat.{max u v}).map S.g)).hom.app (op U)) =
          𝟙 _ := by
      exact
        congrArg
          (fun α :
            (constantSheaf J (Type (max u v))).obj
                ((forget AddCommGrpCat.{max u v}).obj S.X₃) ⟶
              (constantSheaf J (Type (max u v))).obj
                ((forget AddCommGrpCat.{max u v}).obj S.X₃) =>
            α.hom.app (op U))
          hmap
    simpa using ConcreteCategory.congr_hom hσ' (e₃.hom y)
  have hmid :
      e₃.hom (T.g.hom x) =
        (((constantSheaf J (Type (max u v))).map
          ((forget AddCommGrpCat.{max u v}).map S.g)).hom.app (op U))
          ((σ.hom.app (op U)) (e₃.hom y)) := by
    rw [hnat, he₂]
  exact hmid.trans hσ

/-- Lemma 18.42.1, sectionwise form: for every `U : C`, evaluating the constant-sheaf sequence on
`U` gives a short exact sequence of abelian groups. -/
@[stacks 093J]
theorem shortExact_constantAbelianSheaf_app
    (S : ShortComplex AddCommGrpCat.{max u v}) (hS : S.ShortExact) (U : C) :
    (((S.map (constantSheaf J AddCommGrpCat.{max u v})).map
        (sheafToPresheaf J AddCommGrpCat.{max u v})).map
        ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U))).ShortExact := by
  let T :=
    (((S.map (constantSheaf J AddCommGrpCat.{max u v})).map
        (sheafToPresheaf J AddCommGrpCat.{max u v})).map
        ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)))
  have hSheaf := shortExact_constantAbelianSheaf (J := J) S hS
  -- Preserve the kernel presentation of the left map to recover exactness and monicity sectionwise.
  have hKernel : IsLimit (KernelFork.ofι T.f T.zero) := by
    let G :=
      (sheafToPresheaf J AddCommGrpCat.{max u v}) ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
    simpa [T, G] using KernelFork.mapIsLimit (G := G) _ hSheaf.fIsKernel
  have hExact : T.Exact := T.exact_of_f_is_kernel hKernel
  have hMono : Mono T.f := mono_of_isLimit_fork hKernel
  classical
  have hgSurj : Function.Surjective S.g.hom :=
    (AddCommGrpCat.epi_iff_surjective S.g).1 hS.epi_g
  let s : S.X₃ → S.X₂ := fun z ↦ Classical.choose (hgSurj z)
  have hs : Function.RightInverse s S.g.hom := by
    intro z
    exact Classical.choose_spec (hgSurj z)
  -- The textbook's set-theoretic section gives the missing sectionwise surjectivity.
  have hEpi : Epi T.g :=
    (AddCommGrpCat.epi_iff_surjective T.g).2
      (constant_abelian_sheaf_app_surjective (J := J) S s hs U)
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- Lemma 18.42.1, presheaf form: the underlying abelian presheaf sequence of the constant sheaf
sequence is short exact. -/
@[stacks 093J]
theorem shortExact_constantAbelianSheaf_presheaf
    (S : ShortComplex AddCommGrpCat.{max u v}) (hS : S.ShortExact) :
    ((S.map (constantSheaf J AddCommGrpCat.{max u v})).map
      (sheafToPresheaf J AddCommGrpCat.{max u v})).ShortExact := by
  let T :=
    ((S.map (constantSheaf J AddCommGrpCat.{max u v})).map
      (sheafToPresheaf J AddCommGrpCat.{max u v}))
  let hEvalFaithful :
      JointlyFaithful
        (fun V : Cᵒᵖ => (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj V) := by
    refine ⟨?_⟩
    intro X Y f g hfg
    ext V x
    exact ConcreteCategory.congr_hom (hfg V) x
  let hEval :
      JointlyReflectIsomorphisms
        (fun V : Cᵒᵖ => (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj V) :=
    hEvalFaithful.jointlyReflectsIsomorphisms
  -- Reflect short exactness from all section functors back to the presheaf category.
  rw [JointlyReflectIsomorphisms.shortExact_iff (hP := hEval) T]
  intro V
  simpa [T] using shortExact_constantAbelianSheaf_app (J := J) S hS V.unop

end CategoryTheory
