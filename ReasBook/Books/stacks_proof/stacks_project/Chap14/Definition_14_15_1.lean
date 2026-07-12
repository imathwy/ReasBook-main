import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{w} D]
variable (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C)
variable [∀ d : D, HasProductsOfShape (U.obj d) C]

/-
Domain-style sampling for Definition 14.15.1:
- primary domain: source-facing cotensors of a presheaf by a set-valued copresheaf, implemented
  degreewise by categorical products;
- inspected owner declarations:
  `CategoryTheory.Limits.piObj`,
  `CategoryTheory.Limits.Pi.π`,
  `CategoryTheory.Limits.Pi.map'`,
  `CategoryTheory.evaluationRightAdjoint`;
- target layer: `source-facing`;
- owner abstraction:
  the public owner here is the source-facing presheaf `homFromCosimplicialSet U V`, but its
  minimal canonical implementation under the source assumptions is the degreewise product functor
  assembled from mathlib's product owner `∏ᶜ` and the reindexing map `Pi.map'`;
- primitive-vs-derived split:
  primitive data are the indexing category `D`, the set-valued copresheaf `U`, the presheaf `V`,
  and the product-shape hypotheses `[HasProductsOfShape (U.obj d) C]`;
  the product objects and their reindexing maps are derived from `∏ᶜ`, `Pi.map'`, and the
  composition/projection formulas `Pi.map'_comp_map'` and `Pi.map'_comp_π`;
  the source's degreewise finiteness and nonemptiness are sufficient conditions for these product
  shapes to exist, but they are not primitive data of the canonical owner and therefore do not
  belong in the refined public API;
  the object and structure-map formulas themselves are definitional data of the owner, so the
  refined public API keeps only the source-facing owner together with the projection square and
  morphism-level naturality bridge.
- notation decision:
  the obvious textbook surfaces `Hom(U, V)` and exponent-style notation are too ambiguous here,
  since they clash with ordinary morphism notation and internal-hom/exponential readings in Lean;
  the short owner name `homFromCosimplicialSet` is therefore kept as the public surface.

Source/core/bridge triage:
- `source-facing`: `homFromCosimplicialSet U V`;
- `core/canonical`: the degreewise product object
  `Δ ↦ ∏ᶜ (fun _ : U.obj (unop Δ) ↦ V.obj Δ)` with structure maps
  `Pi.map' (U.map f.unop) (fun _ ↦ V.map f)`;
- `bridge/view`: `homFromCosimplicialSet_map_π`.
-/

/-- Definition 14.15.1: assuming the products indexed by the sets `U.obj d` exist in `C`,
`homFromCosimplicialSet U V` is the presheaf whose value at `Δ : Dᵒᵖ` is the product of
`U.obj (unop Δ)` copies of `V.obj Δ`, with structure maps induced by precomposition with `U` and
postcomposition with `V`. -/
@[stacks 0B15]
def homFromCosimplicialSet : Dᵒᵖ ⥤ C where
  obj Δ := ∏ᶜ (fun _ : U.obj (unop Δ) ↦ V.obj Δ)
  map f := Pi.map' (U.map f.unop) (fun _ ↦ V.map f)
  map_id Δ := by
    ext u
    simp
  map_comp {Δ₁ Δ₂ Δ₃} f g := by
    ext u
    simp [Category.assoc]

/-- The structure map of `homFromCosimplicialSet U V` and the corresponding projections form the
canonical commutative square induced by reindexing on `U` and the presheaf structure map on
`V`. -/
theorem homFromCosimplicialSet_map_π
    {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) (u : U.obj (unop Δ₂)) :
    CommSq
      ((homFromCosimplicialSet U V).map f)
      (Pi.π (fun _ : U.obj (unop Δ₁) ↦ V.obj Δ₁) (U.map f.unop u))
      (Pi.π (fun _ : U.obj (unop Δ₂) ↦ V.obj Δ₂) u)
      (V.map f) := by
  refine ⟨?_⟩
  simpa [homFromCosimplicialSet] using
    (Pi.map'_comp_π (U.map f.unop) (fun _ ↦ V.map f) u)

/-- A morphism into `homFromCosimplicialSet U V` is componentwise natural with respect to the
indexing morphisms. -/
theorem homFromCosimplicialSet_hom_naturality
    {X : Dᵒᵖ ⥤ C}
    (h : X ⟶ homFromCosimplicialSet U V)
    {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) (u : U.obj (unop Δ₂)) :
    CommSq
      (X.map f)
      (h.app Δ₁ ≫ Pi.π (fun _ : U.obj (unop Δ₁) ↦ V.obj Δ₁) (U.map f.unop u))
      (h.app Δ₂ ≫ Pi.π (fun _ : U.obj (unop Δ₂) ↦ V.obj Δ₂) u)
      (V.map f) := by
  simpa using
    (CommSq.vert_comp
      (CommSq.mk (h.naturality f))
      (homFromCosimplicialSet_map_π U V f u))

section Coyoneda

variable {E : Type w} [Category.{w} E]
variable (d : E)
variable [∀ a : E, HasProductsOfShape ((coyoneda.obj (op d)).obj a) C]
variable [∀ a b : Eᵒᵖ, HasProductsOfShape (a ⟶ b) C]

private noncomputable def homFromCoyonedaEvaluationComponent
    (X : C) (Δ : Eᵒᵖ) :
    (homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).obj Δ ≅
      ((evaluationRightAdjoint C (op d)).obj X).obj Δ where
  hom :=
    Pi.lift (fun g : Δ ⟶ op d ↦
      Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (op d)) g))
  inv :=
    Pi.lift (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
      Pi.π (fun _ : Δ ⟶ op d ↦ X) ((opEquiv Δ (op d)).symm g))
  hom_inv_id := by
    apply Pi.hom_ext
    intro g
    have h₁ :=
      congrArg
        (fun t ↦
          Pi.lift (fun g : Δ ⟶ op d ↦
              Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X)
                ((opEquiv Δ (op d)) g)) ≫
            t)
        (Pi.lift_π
          (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
            Pi.π (fun _ : Δ ⟶ op d ↦ X) ((opEquiv Δ (op d)).symm g))
          g)
    have h₂ :=
      Pi.lift_π
        (fun g : Δ ⟶ op d ↦
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X)
            ((opEquiv Δ (op d)) g))
        ((opEquiv Δ (op d)).symm g)
    have h₁' := by simpa [Category.assoc] using h₁
    have h₂' := by simpa [Category.assoc] using h₂
    have hcomp := h₁'.trans h₂'
    have hid :
        Pi.π
            (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ ((Functor.const Eᵒᵖ).obj X).obj Δ)
            g =
          𝟙 ((homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).obj Δ) ≫
            Pi.π
              (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ ((Functor.const Eᵒᵖ).obj X).obj Δ)
              g := by
      simpa [homFromCosimplicialSet] using (Category.id_comp
        (Pi.π
          (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ ((Functor.const Eᵒᵖ).obj X).obj Δ)
          g)).symm
    convert hcomp.trans hid using 1 <;> simp [Category.assoc, homFromCosimplicialSet]
  inv_hom_id := by
    apply Pi.hom_ext
    intro g
    have h₁ :=
      congrArg
        (fun t ↦
          Pi.lift (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
              Pi.π (fun _ : Δ ⟶ op d ↦ X) ((opEquiv Δ (op d)).symm g)) ≫
            t)
        (Pi.lift_π
          (fun g : Δ ⟶ op d ↦
            Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X)
              ((opEquiv Δ (op d)) g))
          g)
    have h₂ :=
      Pi.lift_π
        (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
          Pi.π (fun _ : Δ ⟶ op d ↦ X) ((opEquiv Δ (op d)).symm g))
        ((opEquiv Δ (op d)) g)
    have h₁' := by simpa [Category.assoc] using h₁
    have h₂' := by simpa [Category.assoc] using h₂
    simpa using h₁'.trans h₂'

/-- For a representable copresheaf, `homFromCosimplicialSet` is canonically the evaluation right
adjoint at the representing object. -/
noncomputable def homFromCoyonedaIsoEvaluationRightAdjoint (X : C) :
    homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X) ≅
      (evaluationRightAdjoint C (op d)).obj X :=
  NatIso.ofComponents
    (homFromCoyonedaEvaluationComponent d X)
    (by
      intro Δ₁ Δ₂ f
      apply Pi.hom_ext
      intro g
      have h₁ :
          (homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).map f ≫
              (homFromCoyonedaEvaluationComponent d X Δ₂).hom ≫
              Pi.π (fun _ : Δ₂ ⟶ op d ↦ X) g
            =
          (homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).map f ≫
            Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₂) ↦ X)
              ((opEquiv Δ₂ (op d)) g) := by
        simpa [homFromCoyonedaEvaluationComponent, Category.assoc] using
          congrArg
            (fun k ↦
              (homFromCosimplicialSet (coyoneda.obj (op d))
                ((Functor.const Eᵒᵖ).obj X)).map f ≫ k)
            (Pi.lift_π
              (fun g : Δ₂ ⟶ op d ↦
                Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₂) ↦ X)
                  ((opEquiv Δ₂ (op d)) g))
              g)
      have h₂ :
          (homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).map f ≫
              Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₂) ↦ X)
                ((opEquiv Δ₂ (op d)) g)
            =
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
            (((coyoneda.obj (op d)).map f.unop) ((opEquiv Δ₂ (op d)) g)) := by
        simpa [Category.assoc] using
          (homFromCosimplicialSet_map_π
            (coyoneda.obj (op d))
            ((Functor.const Eᵒᵖ).obj X)
            f
            ((opEquiv Δ₂ (op d)) g)).w
      have h₃ :
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
              (((coyoneda.obj (op d)).map f.unop) ((opEquiv Δ₂ (op d)) g))
            =
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
            ((opEquiv Δ₁ (op d)) (f ≫ g)) := by
        rfl
      have h₄ :
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
              ((opEquiv Δ₁ (op d)) (f ≫ g))
            =
          (homFromCoyonedaEvaluationComponent d X Δ₁).hom ≫
            Pi.π (fun _ : Δ₁ ⟶ op d ↦ X) (f ≫ g) := by
        simpa [homFromCoyonedaEvaluationComponent, Category.assoc] using
          (Pi.lift_π
            (fun g : Δ₁ ⟶ op d ↦
              Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
                ((opEquiv Δ₁ (op d)) g))
            (f ≫ g)).symm
      have h₅ :
          Pi.π (fun _ : Δ₁ ⟶ op d ↦ X) (f ≫ g) =
            ((evaluationRightAdjoint C (op d)).obj X).map f ≫
              Pi.π (fun _ : Δ₂ ⟶ op d ↦ X) g := by
        dsimp [evaluationRightAdjoint]
        exact
          (Pi.lift_π
            (fun g' : Δ₂ ⟶ op d ↦
              Pi.π (fun _ : Δ₁ ⟶ op d ↦ X) (f ≫ g'))
            g).symm
      have h₆ :
          (homFromCoyonedaEvaluationComponent d X Δ₁).hom ≫
              Pi.π (fun _ : Δ₁ ⟶ op d ↦ X) (f ≫ g)
            =
          (homFromCoyonedaEvaluationComponent d X Δ₁).hom ≫
            ((evaluationRightAdjoint C (op d)).obj X).map f ≫
              Pi.π (fun _ : Δ₂ ⟶ op d ↦ X) g := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ (homFromCoyonedaEvaluationComponent d X Δ₁).hom ≫ k) h₅
      simpa [Category.assoc] using h₁.trans (h₂.trans (h₃.trans (h₄.trans h₆))))

/-- On each component, `homFromCoyonedaIsoEvaluationRightAdjoint` reindexes the product factors by
the canonical equivalence between arrows into `op d` and arrows out of `d`. -/
theorem homFromCoyonedaIsoEvaluationRightAdjoint_hom_app_π
    (X : C) (Δ : Eᵒᵖ) (g : Δ ⟶ op d) :
    (homFromCoyonedaIsoEvaluationRightAdjoint d X).hom.app Δ ≫
        Pi.π (fun _ : Δ ⟶ op d ↦ X) g =
      Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (op d)) g) := by
  change
    Pi.lift
        (fun g' : Δ ⟶ op d ↦
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X)
            ((opEquiv Δ (op d)) g')) ≫
      Pi.π (fun _ : Δ ⟶ op d ↦ X) g =
    Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (op d)) g)
  simpa using
    Pi.lift_π
      (fun g' : Δ ⟶ op d ↦
        Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (op d)) g'))
      g

end Coyoneda

end CategoryTheory
