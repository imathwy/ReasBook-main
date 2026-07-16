import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Point.Presheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.stacks_project.Chap07.Lemma_7_40_1
import StacksProject_2024.stacks_project.Chap19.Theorem_19_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Example 21.42.1:
- primary domain: global sheaf cohomology on the chaotic topology, computed from the explicit
  source-facing complex `K^•(F)` indexed by composable chains
  `U₀ ⟶ ⋯ ⟶ Uₙ`;
- sampled owner declarations:
  `Sheaf.H`,
  `Sheaf.globalCohomology_isomorphic_to_homology_globalSections_of_injectiveResolution`,
  `ComposableArrows`,
  `nerve`,
  `alternatingCofaceMapComplex`;
- best owner abstraction: the source-facing object is the cosimplicial abelian group whose
  `n`-th term is the product over `ComposableArrows C n` of the values `F(U₀)`, and its
  cochain complex is the canonical owner application of `alternatingCofaceMapComplex`;
- primitive data: a sheaf `F`, a simplex `Δ`, and a composable chain
  `x : ComposableArrows C Δ.len`;
- derived API: the explicit complex `K^•(F)`, its positive-degree acyclicity on
  point skyscraper sheaves, and the comparison theorem computing `Sheaf.H` from that complex.

Source/core/bridge triage:
- `source-facing`: `categoryCohomologyCosimplicialObject` and `categoryCohomologyComplex`;
- `core/canonical`: `Sheaf.H`;
- `bridge/view`: the theorem-level comparison
  `globalCohomology_isomorphic_homology_categoryCohomologyComplex`, comparing the source-facing
  complex to the canonical global-cohomology owner without introducing a separate chosen
  `Iso` wrapper. -/

private abbrev categoryCohomologyChain (C : Type u) [Category.{v} C] (Δ : SimplexCategory) :=
  ComposableArrows C Δ.len

private abbrev categoryCohomologyFirstObject (C : Type u) [Category.{v} C]
    {Δ : SimplexCategory} (x : categoryCohomologyChain C Δ) : C :=
  x.obj 0

private abbrev categoryCohomologyChainPrecomp (C : Type u) [Category.{v} C]
    {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') (x : categoryCohomologyChain C Δ') :
    categoryCohomologyChain C Δ :=
  (nerve C).map f.op x

@[simp] private lemma categoryCohomologyChainPrecomp_id {Δ : SimplexCategory}
    (x : categoryCohomologyChain C Δ) :
    categoryCohomologyChainPrecomp C (𝟙 Δ) x = x :=
  rfl

@[simp] private lemma categoryCohomologyChainPrecomp_comp
    {Δ₁ Δ₂ Δ₃ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) (g : Δ₂ ⟶ Δ₃)
    (x : categoryCohomologyChain C Δ₃) :
    categoryCohomologyChainPrecomp C (f ≫ g) x =
      categoryCohomologyChainPrecomp C f
        (categoryCohomologyChainPrecomp C g x) :=
  rfl

private abbrev categoryCohomologyInitialMap (C : Type u) [Category.{v} C]
    {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') (x : categoryCohomologyChain C Δ') :
    categoryCohomologyFirstObject C x ⟶
      categoryCohomologyFirstObject C (categoryCohomologyChainPrecomp C f x) :=
  x.map (show (0 : Fin (Δ'.len + 1)) ⟶ f.toOrderHom 0 from homOfLE (Fin.zero_le _))

@[simp] private lemma categoryCohomologyInitialMap_id {Δ : SimplexCategory}
    (x : categoryCohomologyChain C Δ) :
    categoryCohomologyInitialMap C (𝟙 Δ) x =
      𝟙 (categoryCohomologyFirstObject C x) := by
  -- For the identity simplex map, the first-vertex arrow in the chain is the identity.
  change x.map (𝟙 (0 : Fin (Δ.len + 1))) = 𝟙 (x.obj 0)
  simpa using Functor.map_id x (0 : Fin (Δ.len + 1))

private lemma categoryCohomologyInitialMap_comp {Δ₁ Δ₂ Δ₃ : SimplexCategory}
    (f : Δ₁ ⟶ Δ₂) (g : Δ₂ ⟶ Δ₃)
    (x : categoryCohomologyChain C Δ₃) :
    categoryCohomologyInitialMap C (f ≫ g) x =
      categoryCohomologyInitialMap C g x ≫
        categoryCohomologyInitialMap C f
          (categoryCohomologyChainPrecomp C g x) := by
  -- Composition on the first vertex is exactly composition of the corresponding chain arrows.
  change
    x.map
        ((show (0 : Fin (Δ₃.len + 1)) ⟶ g.toOrderHom 0 from homOfLE (Fin.zero_le _)) ≫
          (show g.toOrderHom 0 ⟶ g.toOrderHom (f.toOrderHom 0) from
            homOfLE (g.toOrderHom.monotone (Fin.zero_le _)))) =
      x.map (show (0 : Fin (Δ₃.len + 1)) ⟶ g.toOrderHom 0 from homOfLE (Fin.zero_le _)) ≫
        x.map (show g.toOrderHom 0 ⟶ g.toOrderHom (f.toOrderHom 0) from
          homOfLE (g.toOrderHom.monotone (Fin.zero_le _)))
  simpa using
    Functor.map_comp x
      (show (0 : Fin (Δ₃.len + 1)) ⟶ g.toOrderHom 0 from homOfLE (Fin.zero_le _))
      (show g.toOrderHom 0 ⟶ g.toOrderHom (f.toOrderHom 0) from
        homOfLE (g.toOrderHom.monotone (Fin.zero_le _)))

/-- Example 21.42.1: the source-facing cosimplicial abelian group whose `n`-th term is the
product of `F(U₀)` over all composable chains `U₀ ⟶ ⋯ ⟶ Uₙ` in `C`. -/
noncomputable def categoryCohomologyCosimplicialObject
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}) :
    CosimplicialObject AddCommGrpCat.{max u v} where
  obj Δ := ∏ᶜ fun x : categoryCohomologyChain C Δ ↦
    F.1.obj (op (categoryCohomologyFirstObject C x))
  map f :=
    Pi.lift fun x ↦
      Pi.π
          (fun y : categoryCohomologyChain C _ ↦
            F.1.obj (op (categoryCohomologyFirstObject C y)))
          (categoryCohomologyChainPrecomp C f x) ≫
        F.1.map (categoryCohomologyInitialMap C f x).op
  map_id := by
    -- Check the identity after composing with each product projection.
    intro Δ
    apply Pi.hom_ext
    intro x
    rw [Pi.lift_π]
    simp
  map_comp := by
    -- Project to each chain component, where the composition law becomes the presheaf
    -- functoriality of restriction along the initial-vertex maps.
    intro Δ₁ Δ₂ Δ₃ f g
    refine Pi.hom_ext _ _ fun x ↦ by
      rw [Pi.lift_π, Category.assoc, Pi.lift_π, ←Category.assoc, Pi.lift_π]
      simp [categoryCohomologyChainPrecomp_comp, categoryCohomologyInitialMap_comp,
        Category.assoc]

/-- Example 21.42.1: the explicit complex `K^•(F)` attached to a sheaf on the
chaotic site, obtained from the source-facing cosimplicial object by the canonical owner
`alternatingCofaceMapComplex`. -/
noncomputable abbrev categoryCohomologyComplex
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v}).obj
    (categoryCohomologyCosimplicialObject F)

/-- Helper for Example 21.42.1 (Computing cohomology): the cosimplicial restriction map is
computed projectionwise by restricting along the initial-vertex morphism of the chain. -/
@[simp] private theorem categoryCohomologyCosimplicialObject_map_π
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
    {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') (x : categoryCohomologyChain C Δ') :
    (categoryCohomologyCosimplicialObject F).map f ≫
        Pi.π
          (fun y : categoryCohomologyChain C Δ' ↦
            F.1.obj (op (categoryCohomologyFirstObject C y)))
          x =
      Pi.π
          (fun y : categoryCohomologyChain C Δ ↦
            F.1.obj (op (categoryCohomologyFirstObject C y)))
          (categoryCohomologyChainPrecomp C f x) ≫
        F.1.map (categoryCohomologyInitialMap C f x).op := by
  -- This is the defining component formula of the product-valued restriction map.
  simpa [categoryCohomologyCosimplicialObject] using
    (Pi.lift_π
      (fun x' : categoryCohomologyChain C Δ' ↦
        Pi.π
            (fun y : categoryCohomologyChain C Δ ↦
              F.1.obj (op (categoryCohomologyFirstObject C y)))
            (categoryCohomologyChainPrecomp C f x') ≫
          F.1.map (categoryCohomologyInitialMap C f x').op)
      x)

/-- Helper for Example 21.42.1 (Computing cohomology): after postcomposing with a fixed
projection, naturality of the sheaf map reduces to the ordinary presheaf naturality square. -/
private theorem categoryCohomologyCosimplicialFunctor_component_naturality
    {F G : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}}
    (η : F ⟶ G) {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ')
    (x : categoryCohomologyChain C Δ') :
    ((categoryCohomologyCosimplicialObject F).map f ≫
        Pi.lift
          (fun y : categoryCohomologyChain C Δ' ↦
            Pi.π
                (fun z : categoryCohomologyChain C Δ' ↦
                  F.1.obj (op (categoryCohomologyFirstObject C z)))
                y ≫
              η.1.app (op (categoryCohomologyFirstObject C y)))) ≫
        Pi.π
          (fun y : categoryCohomologyChain C Δ' ↦
            G.1.obj (op (categoryCohomologyFirstObject C y)))
          x =
      (Pi.lift
          (fun y : categoryCohomologyChain C Δ ↦
            Pi.π
                (fun z : categoryCohomologyChain C Δ ↦
                  F.1.obj (op (categoryCohomologyFirstObject C z)))
                y ≫
              η.1.app (op (categoryCohomologyFirstObject C y))) ≫
        (categoryCohomologyCosimplicialObject G).map f) ≫
          Pi.π
            (fun y : categoryCohomologyChain C Δ' ↦
              G.1.obj (op (categoryCohomologyFirstObject C y)))
            x := by
  -- Route correction: the earlier direct `rw [Pi.lift_π]` route stalled on reassociation.
  -- We first expose the two projection formulas, then close with the sheaf-map naturality square.
  calc
    ((categoryCohomologyCosimplicialObject F).map f ≫
          Pi.lift
            (fun y : categoryCohomologyChain C Δ' ↦
              Pi.π
                  (fun z : categoryCohomologyChain C Δ' ↦
                    F.1.obj (op (categoryCohomologyFirstObject C z)))
                  y ≫
                η.1.app (op (categoryCohomologyFirstObject C y)))) ≫
          Pi.π
            (fun y : categoryCohomologyChain C Δ' ↦
              G.1.obj (op (categoryCohomologyFirstObject C y)))
            x
        = (Pi.π
              (fun y : categoryCohomologyChain C Δ ↦
                F.1.obj (op (categoryCohomologyFirstObject C y)))
              (categoryCohomologyChainPrecomp C f x) ≫
            F.1.map (categoryCohomologyInitialMap C f x).op) ≫
              η.1.app (op (categoryCohomologyFirstObject C x)) := by
          rw [Category.assoc, Pi.lift_π, ← Category.assoc,
            categoryCohomologyCosimplicialObject_map_π F f x]
          rfl
    _ = Pi.π
            (fun y : categoryCohomologyChain C Δ ↦
              F.1.obj (op (categoryCohomologyFirstObject C y)))
            (categoryCohomologyChainPrecomp C f x) ≫
          (η.1.app
              (op
                (categoryCohomologyFirstObject
                  C
                  (categoryCohomologyChainPrecomp C f x))) ≫
            G.1.map (categoryCohomologyInitialMap C f x).op) := by
          rw [Category.assoc]
          rw [η.1.naturality (categoryCohomologyInitialMap C f x).op]
    _ = (Pi.π
            (fun y : categoryCohomologyChain C Δ ↦
              F.1.obj (op (categoryCohomologyFirstObject C y)))
            (categoryCohomologyChainPrecomp C f x) ≫
          η.1.app
            (op
              (categoryCohomologyFirstObject C (categoryCohomologyChainPrecomp C f x)))) ≫
            G.1.map (categoryCohomologyInitialMap C f x).op := by
          rw [← Category.assoc]
    _ = ((Pi.lift
            (fun y : categoryCohomologyChain C Δ ↦
              Pi.π
                  (fun z : categoryCohomologyChain C Δ ↦
                    F.1.obj (op (categoryCohomologyFirstObject C z)))
                  y ≫
                η.1.app (op (categoryCohomologyFirstObject C y))) ≫
          (categoryCohomologyCosimplicialObject G).map f) ≫
            Pi.π
              (fun y : categoryCohomologyChain C Δ' ↦
                G.1.obj (op (categoryCohomologyFirstObject C y)))
              x) := by
          rw [← Pi.lift_π
                (fun y : categoryCohomologyChain C Δ ↦
                  Pi.π
                      (fun z : categoryCohomologyChain C Δ ↦
                        F.1.obj (op (categoryCohomologyFirstObject C z)))
                      y ≫
                    η.1.app (op (categoryCohomologyFirstObject C y)))
                (categoryCohomologyChainPrecomp C f x),
            Category.assoc,
            ← categoryCohomologyCosimplicialObject_map_π G f x]
          exact
            (Category.assoc
              (Pi.lift
                (fun y : categoryCohomologyChain C Δ ↦
                  Pi.π
                      (fun z : categoryCohomologyChain C Δ ↦
                        F.1.obj (op (categoryCohomologyFirstObject C z)))
                      y ≫
                    η.1.app (op (categoryCohomologyFirstObject C y))))
              ((categoryCohomologyCosimplicialObject G).map f)
              (Pi.π
                (fun y : categoryCohomologyChain C Δ' ↦
                  G.1.obj (op (categoryCohomologyFirstObject C y)))
                x)).symm

/-- Helper for Example 21.42.1 (Computing cohomology): the source-facing cosimplicial-object
construction is functorial in the sheaf. -/
private theorem categoryCohomologyCosimplicialFunctor_naturality
    {F G : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}}
    (η : F ⟶ G) {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') :
    (categoryCohomologyCosimplicialObject F).map f ≫
        Pi.lift
          (fun x : categoryCohomologyChain C Δ' ↦
            Pi.π
                (fun y : categoryCohomologyChain C Δ' ↦
                  F.1.obj (op (categoryCohomologyFirstObject C y)))
                x ≫
              η.1.app (op (categoryCohomologyFirstObject C x))) =
      Pi.lift
          (fun x : categoryCohomologyChain C Δ ↦
            Pi.π
                (fun y : categoryCohomologyChain C Δ ↦
                  F.1.obj (op (categoryCohomologyFirstObject C y)))
                x ≫
              η.1.app (op (categoryCohomologyFirstObject C x))) ≫
        (categoryCohomologyCosimplicialObject G).map f := by
  -- Project to each chain component, where the statement is the component naturality lemma above.
  apply Pi.hom_ext
  intro x
  simpa using categoryCohomologyCosimplicialFunctor_component_naturality η f x

/-- Helper for Example 21.42.1 (Computing cohomology): the source-facing cosimplicial-object
construction is functorial in the sheaf. -/
private noncomputable def categoryCohomologyCosimplicialFunctor :
    Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
      CosimplicialObject AddCommGrpCat.{max u v} where
  obj F := categoryCohomologyCosimplicialObject F
  map := fun {F G} η ↦
    { app := fun Δ ↦
        Pi.lift fun x ↦
          Pi.π
              (fun y : categoryCohomologyChain C Δ ↦
                F.1.obj (op (categoryCohomologyFirstObject C y)))
              x ≫
            η.1.app (op (categoryCohomologyFirstObject C x))
      naturality := by
        -- Use the dedicated componentwise naturality calculation.
        intro Δ Δ' f
        simpa using categoryCohomologyCosimplicialFunctor_naturality η f }
  map_id := by
    -- Check identity componentwise on each chain projection.
    intro F
    refine NatTrans.ext (funext fun Δ ↦ ?_)
    apply Pi.hom_ext
    intro x
    rw [Pi.lift_π]
    exact
      (Category.id_comp
        (Pi.π
          (fun y : categoryCohomologyChain C Δ ↦
            F.1.obj (op (categoryCohomologyFirstObject C y)))
          x)).symm
  map_comp := by
    -- Again it is enough to test each component projection, where the statement is the ordinary
    -- composition law of the sheaf morphism components.
    intro F G H η θ
    refine NatTrans.ext (funext fun Δ ↦ ?_)
    apply Pi.hom_ext
    intro x
    rw [Pi.lift_π]
    calc
      Pi.π
            (fun y : categoryCohomologyChain C Δ ↦
              F.1.obj (op (categoryCohomologyFirstObject C y)))
            x ≫
          η.1.app (op (categoryCohomologyFirstObject C x)) ≫
            θ.1.app (op (categoryCohomologyFirstObject C x))
          =
        (Pi.π
              (fun y : categoryCohomologyChain C Δ ↦
                F.1.obj (op (categoryCohomologyFirstObject C y)))
              x ≫
            η.1.app (op (categoryCohomologyFirstObject C x))) ≫
          θ.1.app (op (categoryCohomologyFirstObject C x)) := by
            rw [Category.assoc]
      _ =
        ((Pi.lift
              (fun x : categoryCohomologyChain C Δ ↦
                Pi.π
                    (fun y : categoryCohomologyChain C Δ ↦
                      F.1.obj (op (categoryCohomologyFirstObject C y)))
                    x ≫
                  η.1.app (op (categoryCohomologyFirstObject C x))) ≫
            Pi.π
              (fun x : categoryCohomologyChain C Δ ↦
                G.1.obj (op (categoryCohomologyFirstObject C x)))
              x) ≫
          θ.1.app (op (categoryCohomologyFirstObject C x))) := by
            rw [Pi.lift_π]
      _ =
        (Pi.lift
              (fun x : categoryCohomologyChain C Δ ↦
                Pi.π
                    (fun y : categoryCohomologyChain C Δ ↦
                      F.1.obj (op (categoryCohomologyFirstObject C y)))
                    x ≫
                  η.1.app (op (categoryCohomologyFirstObject C x))) ≫
            (Pi.π
                (fun x : categoryCohomologyChain C Δ ↦
                  G.1.obj (op (categoryCohomologyFirstObject C x)))
                x ≫
              θ.1.app (op (categoryCohomologyFirstObject C x)))) := by
            rw [← Category.assoc]
      _ =
        (Pi.lift
              (fun x : categoryCohomologyChain C Δ ↦
                Pi.π
                    (fun y : categoryCohomologyChain C Δ ↦
                      F.1.obj (op (categoryCohomologyFirstObject C y)))
                    x ≫
                  η.1.app (op (categoryCohomologyFirstObject C x))) ≫
            (Pi.lift
                (fun x : categoryCohomologyChain C Δ ↦
                  Pi.π
                      (fun y : categoryCohomologyChain C Δ ↦
                        G.1.obj (op (categoryCohomologyFirstObject C y)))
                      x ≫
                    θ.1.app (op (categoryCohomologyFirstObject C x))) ≫
              Pi.π
                (fun x : categoryCohomologyChain C Δ ↦
                  H.1.obj (op (categoryCohomologyFirstObject C x)))
                x)) := by
            rw [Pi.lift_π]
      _ =
        ((Pi.lift
              (fun x : categoryCohomologyChain C Δ ↦
                Pi.π
                    (fun y : categoryCohomologyChain C Δ ↦
                      F.1.obj (op (categoryCohomologyFirstObject C y)))
                    x ≫
                  η.1.app (op (categoryCohomologyFirstObject C x))) ≫
            Pi.lift
              (fun x : categoryCohomologyChain C Δ ↦
                Pi.π
                    (fun y : categoryCohomologyChain C Δ ↦
                      G.1.obj (op (categoryCohomologyFirstObject C y)))
                    x ≫
                  θ.1.app (op (categoryCohomologyFirstObject C x)))) ≫
          Pi.π
            (fun x : categoryCohomologyChain C Δ ↦
              H.1.obj (op (categoryCohomologyFirstObject C x)))
            x) := by
            rw [Category.assoc]

/-- Helper for Example 21.42.1 (Computing cohomology): the functorial map on the cosimplicial
object is computed componentwise on each chain projection. -/
@[simp] private theorem categoryCohomologyCosimplicialFunctor_map_app_π
    {F G : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}}
    (η : F ⟶ G) (Δ : SimplexCategory) (x : categoryCohomologyChain C Δ) :
    ((categoryCohomologyCosimplicialFunctor.map η).app Δ) ≫
        Pi.π
          (fun y : categoryCohomologyChain C Δ ↦
            G.1.obj (op (categoryCohomologyFirstObject C y)))
          x =
      Pi.π
          (fun y : categoryCohomologyChain C Δ ↦
            F.1.obj (op (categoryCohomologyFirstObject C y)))
          x ≫
        η.1.app (op (categoryCohomologyFirstObject C x)) := by
  -- This is the defining component formula of the product map.
  simpa [categoryCohomologyCosimplicialFunctor] using
    (Pi.lift_π
      (fun x' : categoryCohomologyChain C Δ ↦
        Pi.π
            (fun y : categoryCohomologyChain C Δ ↦
              F.1.obj (op (categoryCohomologyFirstObject C y)))
            x' ≫
          η.1.app (op (categoryCohomologyFirstObject C x')))
      x)

/-- Helper for Example 21.42.1 (Computing cohomology): the explicit complex construction is the
functor obtained by postcomposing the cosimplicial construction with
`alternatingCofaceMapComplex`. -/
private noncomputable abbrev categoryCohomologyComplexFunctor :
    Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
      CochainComplex AddCommGrpCat.{max u v} ℕ :=
  categoryCohomologyCosimplicialFunctor ⋙
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v})

/-- Helper for Example 21.42.1 (Computing cohomology): exact functors remain exact after
composition. -/
private theorem exactFunctor_comp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F) (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both properties
  -- are stable under functor composition.
  rw [exactFunctor_iff] at hF hG ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  let _ : PreservesFiniteLimits G := hG.1
  let _ : PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Example 21.42.1 (Computing cohomology): evaluations on a functor category jointly
reflect isomorphisms. -/
private theorem evaluation_jointlyReflectsIsomorphisms
    (D : Type*) [Category D] (A : Type*) [Category A] :
    JointlyReflectIsomorphisms ((evaluation D A).obj : D → (D ⥤ A) ⥤ A) := by
  -- Proof comment: a natural transformation is an isomorphism exactly when all of its components
  -- are isomorphisms.
  refine ⟨fun {F G} α hα ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  simpa using (inferInstance : IsIso (((evaluation D A).obj d).map α))

/-- Helper for Example 21.42.1 (Computing cohomology): a short exact sequence of abelian sheaves
on the bottom topology is short exact on sections over every object. -/
private theorem sectionwise_shortExact_of_bot_sheaf_shortExact
    {S : ShortComplex (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})}
    (hS : S.ShortExact) (U : C) :
    (((S.map (sheafToPresheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})).map
      ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)))).ShortExact := by
  let G :=
    (sheafToPresheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}) ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
  let T := S.map G
  have hKernel : IsLimit (KernelFork.ofι T.f T.zero) := by
    -- Proof comment: pass the kernel presentation of `S.f` through the underlying-presheaf and
    -- evaluation functors.
    simpa [G, T] using KernelFork.mapIsLimit _ hS.fIsKernel G
  have hExact : T.Exact := T.exact_of_f_is_kernel hKernel
  have hMono : Mono T.f := mono_of_isLimit_fork hKernel
  have hEpi : Epi T.g := by
    -- Proof comment: epimorphisms of abelian sheaves are surjective on each section group.
    refine (AddCommGrpCat.epi_iff_surjective T.g).2 ?_
    letI : Sheaf.IsLocallySurjective S.g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} S.g).2 hS.epi_g
    intro y
    have htop :
        Presheaf.imageSieve S.g.hom y = ⊤ := by
      exact
        GrothendieckTopology.bot_covering.mp
          (Presheaf.imageSieve_mem (⊥ : GrothendieckTopology C) S.g.hom y)
    have hid : Presheaf.imageSieve S.g.hom y (𝟙 U) := by
      simpa [htop]
    rcases hid with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [G, T] using hx
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- Helper for Example 21.42.1 (Computing cohomology): the chain-indexed diagram whose `x`-entry is
the fiber at the point corresponding to the initial object of the chain `x`. -/
private noncomputable def categoryCohomologyComponentDiagramFunctor
    (Δ : SimplexCategory) :
    Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
      Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v} :=
  (sheafToPresheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}) ⋙
    (Functor.whiskeringLeft
      (Discrete (categoryCohomologyChain C Δ))
      Cᵒᵖ
      AddCommGrpCat.{max u v}).obj
        (Discrete.functor fun x : categoryCohomologyChain C Δ ↦
          op (categoryCohomologyFirstObject C x))

/-- Helper for Example 21.42.1 (Computing cohomology): the chain-indexed point-fiber diagram
preserves zero morphisms. -/
private instance categoryCohomologyComponentDiagramFunctor_preservesZeroMorphisms
    (Δ : SimplexCategory) :
    (categoryCohomologyComponentDiagramFunctor Δ :
      Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
        Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}).PreservesZeroMorphisms := by
  refine ⟨?_⟩
  intro F G
  -- Proof comment: the composite diagram functor evaluates a zero sheaf morphism objectwise on
  -- the underlying presheaf, so every component is zero.
  ext x
  rfl

/-- Helper for Example 21.42.1 (Computing cohomology): the chain-indexed point-fiber diagram is
additive in the sheaf variable, since it is a composite of additive functors. -/
private instance categoryCohomologyComponentDiagramFunctor_additive
    (Δ : SimplexCategory) :
    (categoryCohomologyComponentDiagramFunctor Δ :
      Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
        Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}).Additive := by
  refine ⟨?_⟩
  intro F G α β
  -- Proof comment: addition is computed objectwise on the underlying presheaf sections.
  ext x
  rfl

/-- Helper for Example 21.42.1 (Computing cohomology): the componentwise point-fiber product
functor preserves zero morphisms. -/
private instance categoryCohomologyComponentwiseLimitFunctor_preservesZeroMorphisms
    (Δ : SimplexCategory) :
    ((categoryCohomologyComponentDiagramFunctor Δ :
        Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
          Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⋙
      (ExactFunctor.of
        (lim :
          (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
            AddCommGrpCat.{max u v})).obj).PreservesZeroMorphisms := by
  -- Proof comment: the limit functor on a discrete diagram is exact, hence additive, so the
  -- composite again preserves zero morphisms.
  let G :
      (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
        AddCommGrpCat.{max u v} :=
    (ExactFunctor.of
      (lim :
        (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
          AddCommGrpCat.{max u v})).obj
  letI : G.Additive :=
    (exactFunctor_le_additiveFunctor
      (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v})
      AddCommGrpCat.{max u v}) G
      (ExactFunctor.of
        (lim :
          (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
            AddCommGrpCat.{max u v})).property
  infer_instance

/-- Helper for Example 21.42.1 (Computing cohomology): the chain-indexed point-fiber diagram is
exact in the sheaf variable. -/
private theorem categoryCohomologyComponentDiagramFunctor_exact
    (Δ : SimplexCategory) :
    exactFunctor
      (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
      (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v})
      (categoryCohomologyComponentDiagramFunctor Δ) := by
  -- Route correction: rather than trying to synthesize exactness of `sheafToPresheaf` globally,
  -- prove mapped short exactness directly from the sectionwise short exactness bridge above.
  refine ((Functor.exact_tfae
    (categoryCohomologyComponentDiagramFunctor Δ)).out 3 0).2 ?_
  intro S hS
  let hEval := evaluation_jointlyReflectsIsomorphisms
    (Discrete (categoryCohomologyChain C Δ)) AddCommGrpCat.{max u v}
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      (hEval.exact_iff (S.map (categoryCohomologyComponentDiagramFunctor Δ))).2
        fun x ↦ by
          simpa [categoryCohomologyComponentDiagramFunctor] using
            (sectionwise_shortExact_of_bot_sheaf_shortExact hS
              (categoryCohomologyFirstObject C x.as)).exact
  · exact
        (NatTrans.mono_iff_mono_app
          (S.map (categoryCohomologyComponentDiagramFunctor Δ)).f).2 fun x ↦ by
          simpa [categoryCohomologyComponentDiagramFunctor] using
            (sectionwise_shortExact_of_bot_sheaf_shortExact hS
              (categoryCohomologyFirstObject C x.as)).mono_f
  · exact
        (NatTrans.epi_iff_epi_app
          (S.map (categoryCohomologyComponentDiagramFunctor Δ)).g).2 fun x ↦ by
          simpa [categoryCohomologyComponentDiagramFunctor] using
            (sectionwise_shortExact_of_bot_sheaf_shortExact hS
              (categoryCohomologyFirstObject C x.as)).epi_g

/-- Helper for Example 21.42.1 (Computing cohomology): after taking the chain-indexed point-fiber
diagram, the exact product functor still preserves short exact sequences. -/
private theorem categoryCohomologyComponentwiseLimitFunctor_exact
    (Δ : SimplexCategory) :
    exactFunctor
      (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
      AddCommGrpCat.{max u v}
      (categoryCohomologyComponentDiagramFunctor Δ ⋙
        (ExactFunctor.of
          (lim :
            (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
              AddCommGrpCat.{max u v})).obj) := by
  let hDiagram :
      exactFunctor
        (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
        (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v})
        (categoryCohomologyComponentDiagramFunctor Δ) :=
    categoryCohomologyComponentDiagramFunctor_exact Δ
  let hLimit :
      exactFunctor
        (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v})
        AddCommGrpCat.{max u v}
        ((ExactFunctor.of
          (lim :
            (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
              AddCommGrpCat.{max u v})).obj) :=
    (ExactFunctor.of
      (lim :
        (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
          AddCommGrpCat.{max u v})).property
  -- Proof comment: the discrete product functor is exact, so exactness survives composition.
  simpa using exactFunctor_comp hDiagram hLimit

/-- Helper for Example 21.42.1 (Computing cohomology): the componentwise point-fiber product at a
fixed simplex sends short exact sequences of sheaves to short exact sequences of abelian groups. -/
private theorem categoryCohomologyComponentwiseLimit_map_shortExact
    (Δ : SimplexCategory)
    {S : ShortComplex (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})}
    (hS : S.ShortExact) :
    (S.map
        (categoryCohomologyComponentDiagramFunctor Δ ⋙
          (ExactFunctor.of
            (lim :
              (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
                AddCommGrpCat.{max u v})).obj)).ShortExact := by
  let Fcomp :=
    categoryCohomologyComponentDiagramFunctor Δ ⋙
      (ExactFunctor.of
        (lim :
          (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
            AddCommGrpCat.{max u v})).obj
  let hExact :
      exactFunctor
        (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
        AddCommGrpCat.{max u v}
        (categoryCohomologyComponentDiagramFunctor Δ ⋙
          (ExactFunctor.of
            (lim :
              (Discrete (categoryCohomologyChain C Δ) ⥤ AddCommGrpCat.{max u v}) ⥤
                AddCommGrpCat.{max u v})).obj) :=
    categoryCohomologyComponentwiseLimitFunctor_exact Δ
  let _ : Fcomp.Additive :=
    (exactFunctor_le_additiveFunctor
      (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
      AddCommGrpCat.{max u v}) Fcomp hExact
  let _ : PreservesFiniteLimits Fcomp := (exactFunctor_iff _).mp hExact |>.1
  let _ : PreservesFiniteColimits Fcomp := (exactFunctor_iff _).mp hExact |>.2
  -- Proof comment: once the composite functor is exact, `map_of_exact` upgrades short exactness
  -- formally.
  simpa [Fcomp] using hS.map_of_exact Fcomp

/-- Helper for Example 21.42.1 (Computing cohomology): the explicit complex functor
`F ↦ K^•(F)` is additive in the sheaf variable. -/
private instance categoryCohomologyComplexFunctor_additive :
    (categoryCohomologyComplexFunctor :
      Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
        CochainComplex AddCommGrpCat.{max u v} ℕ).Additive where
  map_add := by
    intro F G α β
    apply HomologicalComplex.Hom.ext
    funext n
    apply Pi.hom_ext
    intro x
    -- Project to each chain factor, where additivity is just additivity of the sheaf morphism
    -- component at the initial object of the chain.
    change
      (categoryCohomologyCosimplicialFunctor.map (α + β)).app (SimplexCategory.mk n) ≫
          Pi.π
            (fun y : categoryCohomologyChain C (SimplexCategory.mk n) ↦
              G.1.obj (op (categoryCohomologyFirstObject C y)))
            x =
        ((categoryCohomologyCosimplicialFunctor.map α).app (SimplexCategory.mk n) +
            (categoryCohomologyCosimplicialFunctor.map β).app (SimplexCategory.mk n)) ≫
          Pi.π
            (fun y : categoryCohomologyChain C (SimplexCategory.mk n) ↦
              G.1.obj (op (categoryCohomologyFirstObject C y)))
            x
    rw [Preadditive.add_comp]
    simp [categoryCohomologyCosimplicialFunctor_map_app_π, Preadditive.comp_add]
    rfl

/-- Helper for Example 21.42.1 (Computing cohomology): the explicit complex functor
`F ↦ K^•(F)` is exact. -/
private noncomputable def categoryCohomologyComplexFunctor_eval_iso_component
    (n : ℕ)
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}) :
    ((categoryCohomologyComplexFunctor.obj F).X n) ≅
      (((categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n)) ⋙
        (ExactFunctor.of
          (lim :
            (Discrete (categoryCohomologyChain C (SimplexCategory.mk n)) ⥤
              AddCommGrpCat.{max u v}) ⥤
                AddCommGrpCat.{max u v})).obj).obj F) := by
  let G :
      Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
        Discrete (categoryCohomologyChain C (SimplexCategory.mk n)) ⥤ AddCommGrpCat.{max u v} :=
    categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n)
  -- Proof comment: degree `n` of `K^•(F)` is the product over the `n`-chains, and the
  -- componentwise limit functor is the same product written through the owner `lim`.
  simpa [categoryCohomologyComplexFunctor, categoryCohomologyComponentDiagramFunctor, G] using
    (Pi.isoLimit (G.obj F))

/-- Helper for Example 21.42.1 (Computing cohomology): the degreewise comparison above is
compatible with projection to a fixed chain component. -/
private theorem categoryCohomologyComplexFunctor_eval_iso_projection_naturality
    (n : ℕ)
    {F G : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}}
    (η : F ⟶ G)
    (x : categoryCohomologyChain C (SimplexCategory.mk n)) :
    ((categoryCohomologyComplexFunctor.map η).f n) ≫
        (categoryCohomologyComplexFunctor_eval_iso_component n G).hom ≫
        limit.π
          ((categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n)).obj G)
          (Discrete.mk x) =
      (categoryCohomologyComplexFunctor_eval_iso_component n F).hom ≫
        limit.π
          ((categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n)).obj F)
          (Discrete.mk x) ≫
        η.1.app (op (categoryCohomologyFirstObject C x)) := by
  -- Proof comment: after rewriting both comparison maps by `Pi.isoLimit_hom_π`, the statement is
  -- exactly the explicit projection formula for the cosimplicial functor map.
  rw [show
      (categoryCohomologyComplexFunctor_eval_iso_component n G).hom ≫
          limit.π
            ((categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n)).obj G)
            (Discrete.mk x) =
        Pi.π
          (fun y : categoryCohomologyChain C (SimplexCategory.mk n) ↦
            G.1.obj (op (categoryCohomologyFirstObject C y)))
          x by
        simpa [categoryCohomologyComplexFunctor_eval_iso_component,
          categoryCohomologyComponentDiagramFunctor] using
          (Pi.isoLimit_hom_π
            ((categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n)).obj G) x)]
  conv_rhs => rw [← Category.assoc]
  rw [show
      (categoryCohomologyComplexFunctor_eval_iso_component n F).hom ≫
          limit.π
            ((categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n)).obj F)
            (Discrete.mk x) =
        Pi.π
          (fun y : categoryCohomologyChain C (SimplexCategory.mk n) ↦
            F.1.obj (op (categoryCohomologyFirstObject C y)))
          x by
        simpa [categoryCohomologyComplexFunctor_eval_iso_component,
          categoryCohomologyComponentDiagramFunctor] using
          (Pi.isoLimit_hom_π
            ((categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n)).obj F) x)]
  -- Route correction: the exactness blocker is an owner-API transport issue, so we rewrite the
  -- degree-`n` complex map to the corresponding cosimplicial component instead of adding a second
  -- exactness theorem.
  change
    ((categoryCohomologyCosimplicialFunctor.map η).app (SimplexCategory.mk n)) ≫
        Pi.π
          (fun y : categoryCohomologyChain C (SimplexCategory.mk n) ↦
            G.1.obj (op (categoryCohomologyFirstObject C y)))
          x =
      Pi.π
          (fun y : categoryCohomologyChain C (SimplexCategory.mk n) ↦
            F.1.obj (op (categoryCohomologyFirstObject C y)))
          x ≫
        η.1.app (op (categoryCohomologyFirstObject C x))
  simpa using
    categoryCohomologyCosimplicialFunctor_map_app_π η (SimplexCategory.mk n) x

/-- Helper for Example 21.42.1 (Computing cohomology): degreewise evaluation of the explicit
complex functor agrees naturally with the chain-indexed product functor. -/
private noncomputable def categoryCohomologyComplexFunctor_eval_iso
    (n : ℕ) :
    categoryCohomologyComplexFunctor ⋙
      HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n ≅
    categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n) ⋙
      (ExactFunctor.of
        (lim :
          (Discrete (categoryCohomologyChain C (SimplexCategory.mk n)) ⥤
            AddCommGrpCat.{max u v}) ⥤
              AddCommGrpCat.{max u v})).obj := by
  refine NatIso.ofComponents
    (fun F ↦ categoryCohomologyComplexFunctor_eval_iso_component n F) ?_
  intro F G η
  apply limit.hom_ext
  intro x
  rcases x with ⟨x⟩
  simpa [Category.assoc, limMap_π] using
    categoryCohomologyComplexFunctor_eval_iso_projection_naturality n η x

/-- Helper for Example 21.42.1 (Computing cohomology): the explicit complex functor
`F ↦ K^•(F)` is exact. -/
private theorem categoryCohomologyComplexFunctor_degreewise_shortExact
    {S : ShortComplex (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})}
    (hS : S.ShortExact) (n : ℕ) :
    ((S.map categoryCohomologyComplexFunctor).map
      (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n)).ShortExact := by
  let e :
      categoryCohomologyComplexFunctor ⋙
        HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n ≅
      categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n) ⋙
        (ExactFunctor.of
          (lim :
            (Discrete (categoryCohomologyChain C (SimplexCategory.mk n)) ⥤
              AddCommGrpCat.{max u v}) ⥤
                AddCommGrpCat.{max u v})).obj :=
    categoryCohomologyComplexFunctor_eval_iso n
  let i :
      (S.map
          (categoryCohomologyComponentDiagramFunctor (SimplexCategory.mk n) ⋙
            (ExactFunctor.of
              (lim :
                (Discrete (categoryCohomologyChain C (SimplexCategory.mk n)) ⥤
                  AddCommGrpCat.{max u v}) ⥤
                    AddCommGrpCat.{max u v})).obj)) ≅
        ((S.map categoryCohomologyComplexFunctor).map
          (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n)) :=
    ShortComplex.isoMk
      ((e.app S.X₁).symm)
      ((e.app S.X₂).symm)
      ((e.app S.X₃).symm)
      (by simpa using (e.inv.naturality S.f).symm)
      (by simpa using (e.inv.naturality S.g).symm)
  -- Proof comment: the degree-`n` exactness statement is now exactly the already-proved
  -- componentwise product exactness, transported across the evaluation comparison.
  exact ShortComplex.shortExact_of_iso i
    (categoryCohomologyComponentwiseLimit_map_shortExact
      (SimplexCategory.mk n) hS)

/-- Helper for Example 21.42.1 (Computing cohomology): the explicit complex functor
`F ↦ K^•(F)` is exact. -/
private theorem categoryCohomologyComplexFunctor_exact :
    exactFunctor
      (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})
      (CochainComplex AddCommGrpCat.{max u v} ℕ)
      categoryCohomologyComplexFunctor := by
  letI :
      (categoryCohomologyComplexFunctor :
        Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v} ⥤
          CochainComplex AddCommGrpCat.{max u v} ℕ).Additive := inferInstance
  refine ((Functor.exact_tfae categoryCohomologyComplexFunctor).out 3 0).2 ?_
  intro S hS
  -- Reduce short exactness of cochain complexes to short exactness in each degree, where the
  -- already-proved componentwise product exactness theorem applies.
  refine (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (S.map categoryCohomologyComplexFunctor)).2 ?_
  intro n
  exact categoryCohomologyComplexFunctor_degreewise_shortExact hS n

namespace CategoryCohomology

@[inherit_doc categoryCohomologyComplex]
scoped notation3:max "K^•(" F ")" => CategoryTheory.categoryCohomologyComplex F

end CategoryCohomology

open scoped CategoryCohomology

section

/-- Helper for Example 21.42.1 (Computing cohomology): every object of the chaotic site is weakly
contractible, because a locally surjective morphism is already surjective on the identity arrow of
the unique covering sieve. -/
private theorem bot_isWeaklyContractible (U : C) :
    (⊥ : GrothendieckTopology C).IsWeaklyContractible U := by
  refine ⟨?_⟩
  intro ℱ 𝒢 π hπ y
  letI : Sheaf.IsLocallySurjective π := hπ
  have htop :
      Presheaf.imageSieve π.hom y = ⊤ := by
    exact
      GrothendieckTopology.bot_covering.mp
        (Presheaf.imageSieve_mem (⊥ : GrothendieckTopology C) π.hom y)
  -- The identity arrow belongs to the top covering sieve, so its chosen local preimage is a
  -- genuine section over `U`.
  have hid : Presheaf.imageSieve π.hom y (𝟙 U) := by
    simpa [htop]
  rcases hid with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa using hx

/-- Helper for Example 21.42.1 (Computing cohomology): the point fiber of `pointBot U` over an
object `X` is the ordinary hom-set `U ⟶ X`. -/
private noncomputable abbrev pointBot_fiber_equiv_hom
    (U X : C) :
    (GrothendieckTopology.pointBot.{max u v} U).fiber.obj X ≃ (U ⟶ X) :=
  -- Proof comment: `pointBot U` is the flipped shrunk Yoneda point, so its fibers are exactly the
  -- shrunk hom-sets out of `U`; `shrinkYonedaObjObjEquiv` removes the shrink.
  CategoryTheory.shrinkYonedaObjObjEquiv

-- Proof sketch: for a point skyscraper sheaf, the cosimplicial abelian group
-- `n ↦ ∏_{U₀ ⟶ ⋯ ⟶ Uₙ} F(U₀)` is the cochain complex of the contractible
-- simplicial set of chains starting at the chosen point object, so its positive-degree homology
-- vanishes.
/-- Point skyscraper sheaves are acyclic in positive degree for the explicit complex
`K^•(F)`. -/
theorem pointBot_skyscraperSheaf_categoryCohomologyComplex_homology_isZero_of_pos
    (U : C) (A : AddCommGrpCat.{max u v}) {n : ℕ} (hn : 0 < n) :
    IsZero
      ((K^•(((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A))).homology n) := by
  -- TODO: first assemble the degreewise sigma-currying isomorphism starting from
  -- `pointBot_fiber_equiv_hom`, then package the resulting product-to-function-space equivalence
  -- and its naturality to identify the whole cosimplicial object with the `A`-valued cochains on
  -- the source contractible simplicial set of chains starting at `U`. After that, transport the
  -- explicit contraction through
  -- `alternatingCofaceMapComplex_map_homotopic` to deduce positive-degree homology vanishing.
  sorry

end

section

variable [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})]

omit [HasExt (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v})]
  [HasGlobalSectionsFunctor (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}] in
/-- Helper for Example 21.42.1 (Computing cohomology): enough injectives on abelian sheaves for
the chaotic topology give the injective resolutions needed by the global-cohomology owner. -/
private theorem bot_sheaf_has_injective_resolutions :
    HasInjectiveResolutions
      (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}) := by
  -- Proof comment: expose the earlier enough-injectives theorem directly to avoid the same
  -- typeclass search timeout that appears when elaborating `F.H`.
  let _ : EnoughInjectives
      (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}) :=
    siteAbelianSheaf_hasEnoughInjectives (⊥ : GrothendieckTopology C)
  infer_instance

-- Proof sketch: the source-facing complex `K^•(F)` is functorial in
-- `F`, and the previous theorem gives the point-skyscraper acyclicity hypothesis needed
-- for the universal `δ`-functor comparison with the canonical owner `Sheaf.H`.
/-- Example 21.42.1 (Computing cohomology): the homology of the explicit complex
`K^•(F)` computes the global sheaf cohomology object `AddCommGrpCat.of (F.H n)` for the chaotic
topology. -/
@[stacks 08RZ]
theorem globalCohomology_isomorphic_homology_categoryCohomologyComplex
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (F.H n))
      ((K^•(F)).homology n) := by
  -- TODO: package `F ↦ (K^•(F)).homology n` into a cohomological `δ`-functor, prove degree-zero
  -- agreement with global sections and weak effaceability via products of point skyscraper
  -- sheaves, then apply universal-delta-functor uniqueness against `Sheaf.H`.
  sorry

-- Proof sketch: combine the source-facing computation theorem with the point-skyscraper
-- acyclicity of `K^•(F)`.
/-- Point skyscraper sheaves for the chaotic topology are acyclic for positive global
cohomology. -/
theorem pointBot_skyscraperSheaf_H_isZero_of_pos
    (U : C) (A : AddCommGrpCat.{max u v}) {n : ℕ} (hn : 0 < n) :
    IsZero
      (AddCommGrpCat.of
        (((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A).H n)) := by
  -- TODO: once `globalCohomology_isomorphic_homology_categoryCohomologyComplex` is proved,
  -- transport the already-established explicit-complex acyclicity along the chosen comparison
  -- isomorphism. The current blocker is the same universal-`δ`-functor comparison as in the main
  -- theorem, so keeping this helper behind the same frontier avoids duplicating that heavy route.
  sorry

end

end

end CategoryTheory
