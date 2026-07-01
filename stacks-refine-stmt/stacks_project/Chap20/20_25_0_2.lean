import Mathlib
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import stacks_project.Chap20.«20_9_0_1»

open CategoryTheory Opposite TopologicalSpace ComplexShape HomologicalComplex₂
open CategoryTheory.Limits

noncomputable section

universe u v

variable {X : TopCat.{u}} {I J : Type v}

/- Domain-style sampling for 20.25.0.2:
- primary domain: refinement functoriality of Čech complexes and the induced maps on rowwise total
  Čech double complexes of presheaf complexes;
- sampled owner declarations:
  `cechComplexFunctor`,
  `Functor.mapHomologicalComplex`,
  `NatTrans.mapHomologicalComplex`,
  `opensHasFiniteProducts`;
- best owner abstraction: the extended rowwise Čech construction should be organized around the
  functor `cechRowFunctor 𝒰`, with the double complex obtained canonically by
  `(cechRowFunctor 𝒰).mapHomologicalComplex (ComplexShape.up ℤ)`;
- primitive data: an indexed family of opens `𝒰`, a refinement witness `IsRefinement 𝒰 𝒱 t`, and
  a coefficient complex `F`;
- derived API: the extended row map, the resulting double complex, the induced morphism of double
  complexes, and the total refinement map.

Source/core/bridge triage:
- `source-facing`: `IsRefinement` and `cechTotalRefinementMap`;
- `core/canonical`: `cechComplexFunctor`, `Functor.mapHomologicalComplex`,
  `NatTrans.mapHomologicalComplex`, and the earlier chapter owner `opensHasFiniteProducts`;
- `bridge/view`: `refinementHom`, the induced Čech row map, and its whiskered/nested
  `mapHomologicalComplex` realizations.

The former version rebuilt the rowwise double complex and its refinement map entrywise via
`CochainComplex.of` and `CochainComplex.ofHom`. The refined file keeps the same source semantics
but promotes the rowwise Čech functor to the owner level and derives the double-complex API
canonically from functoriality.
-/

local instance : OrderTop (Opens X) := opensOrderTop X
local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/-- A map `t : J → I` exhibits `𝒱` as a refinement of `𝒰` if `V_j ⊆ U_{t(j)}` for every `j`. -/
def IsRefinement (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) : Prop :=
  ∀ j : J, 𝒱 j ≤ 𝒰 (t j)

/-- The morphism of formal coproducts attached to a refinement map of indexed open covers. -/
def refinementHom (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) :
    (⟨J, 𝒱⟩ : FormalCoproduct (Opens X)) ⟶ (⟨I, 𝒰⟩ : FormalCoproduct (Opens X)) where
  f := t
  φ j := homOfLE (ht j)

/-- The extended Čech row functor attached to the indexed family `𝒰`. -/
abbrev cechRowFunctor (𝒰 : I → Opens X) :
    X.Presheaf AddCommGrpCat.{max u v} ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ :=
  cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒰 ⋙
    (ComplexShape.embeddingUpNat).extendFunctor AddCommGrpCat.{max u v}

/-- The Čech complex functor preserves zero morphisms. -/
instance cechComplexFunctor_preservesZeroMorphisms (𝒰 : I → Opens X) :
    (cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒰).PreservesZeroMorphisms where
  map_zero F G := by
    ext n i
    rw [show Limits.Pi.map (fun i ↦ (0 : F.obj (op (∏ᶜ 𝒰 ∘ i)) ⟶ G.obj (op (∏ᶜ 𝒰 ∘ i)))) = (0 : _)
      by
        ext j x
        simp]
    rfl

/-- The extended Čech row functor preserves zero morphisms. -/
instance cechRowFunctor_preservesZeroMorphisms (𝒰 : I → Opens X) :
    (cechRowFunctor 𝒰).PreservesZeroMorphisms where
  map_zero F G := by
    change HomologicalComplex.extendMap
        ((cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒰).map
          (0 : F ⟶ G))
        ComplexShape.embeddingUpNat = 0
    rw [Functor.map_zero, HomologicalComplex.extendMap_zero]

/-- The natural transformation of Čech complexes induced by a refinement of indexed open covers. -/
noncomputable def cechRefinementNatTrans (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) :
    cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒰 ⟶
      cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒱 :=
  by
    simpa [CategoryTheory.cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor] using
      (Functor.whiskerRight
        (((Functor.whiskeringLeft SimplexCategory
            ((FormalCoproduct (Opens X))ᵒᵖ) AddCommGrpCat.{max u v}).map
          ((FormalCoproduct.cechFunctor.map (refinementHom 𝒰 𝒱 t ht)).rightOp)))
        (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v}))

/-- The rowwise Čech double-complex functor attached to `𝒰`. -/
abbrev cechDoubleComplexFunctor (𝒰 : I → Opens X) :
    CochainComplex (X.Presheaf AddCommGrpCat.{max u v}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u v}
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (cechRowFunctor 𝒰).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The map of Čech complexes induced by a refinement of indexed open covers. -/
noncomputable def cechRefinementMap (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒰).obj F ⟶
      (cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒱).obj F :=
  (cechRefinementNatTrans 𝒰 𝒱 t ht).app F

/-- The refinement map is natural in the presheaf argument. -/
theorem cechRefinementMap_naturality (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (φ : F ⟶ G) :
    (cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒰).map φ ≫
        cechRefinementMap 𝒰 𝒱 t ht G =
      cechRefinementMap 𝒰 𝒱 t ht F ≫
        (cechComplexFunctor (C := Opens X) (A := AddCommGrpCat.{max u v}) 𝒱).map φ := by
  simpa [cechRefinementMap] using (cechRefinementNatTrans 𝒰 𝒱 t ht).naturality φ

/-- The refinement induces a natural transformation between the extended Čech row functors. -/
noncomputable def cechRowFunctorMap (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) :
    cechRowFunctor 𝒰 ⟶ cechRowFunctor 𝒱 :=
  Functor.whiskerRight (cechRefinementNatTrans 𝒰 𝒱 t ht)
    ((ComplexShape.embeddingUpNat).extendFunctor AddCommGrpCat.{max u v})

/-- The refinement map between Čech complexes after extending the Čech direction from `ℕ` to `ℤ`.
-/
abbrev cechRefinementMapExt (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    ((cechComplexFunctor 𝒰).obj F).extend ComplexShape.embeddingUpNat ⟶
      ((cechComplexFunctor 𝒱).obj F).extend ComplexShape.embeddingUpNat :=
  (cechRowFunctorMap 𝒰 𝒱 t ht).app F

/-- The double complex obtained by applying the Čech complex rowwise to a cochain complex of
presheaves and extending the Čech grading to `ℤ`. -/
abbrev cechDoubleComplex (𝒰 : I → Opens X)
    (F : CochainComplex (X.Presheaf AddCommGrpCat.{max u v}) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{max u v} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (cechDoubleComplexFunctor 𝒰).obj F

/-- The morphism of Čech double complexes induced by a refinement of indexed open covers. -/
abbrev cechDoubleComplexMap (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t)
    (F : CochainComplex (X.Presheaf AddCommGrpCat.{max u v}) ℤ) :
    cechDoubleComplex 𝒰 F ⟶ cechDoubleComplex 𝒱 F :=
  (NatTrans.mapHomologicalComplex (cechRowFunctorMap 𝒰 𝒱 t ht) (ComplexShape.up ℤ)).app F

/-- 20.25.0.2: if `𝒱` is a refinement of `𝒰` via `t : J → I`, then `t` induces the canonical map
`T_t : Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal F^\bullet)) ⟶
Tot(\check{\mathcal C}^\bullet(\mathcal V, \mathcal F^\bullet))` on the associated total Čech
complexes of a cochain complex of presheaves of abelian groups. -/
noncomputable def cechTotalRefinementMap (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t)
    (F : CochainComplex (X.Presheaf AddCommGrpCat.{max u v}) ℤ)
    [((cechDoubleComplex 𝒰 F)).HasTotal (ComplexShape.up ℤ)]
    [((cechDoubleComplex 𝒱 F)).HasTotal (ComplexShape.up ℤ)] :
    (cechDoubleComplex 𝒰 F).total (ComplexShape.up ℤ) ⟶
      (cechDoubleComplex 𝒱 F).total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (cechDoubleComplexMap 𝒰 𝒱 t ht F) (ComplexShape.up ℤ)

-- Proof sketch: unfold `cechTotalRefinementMap`; it is defined by applying
-- `HomologicalComplex₂.total.map` to the refinement morphism of Čech double complexes.
/-- The total Čech refinement map is the totalization of the morphism of Čech double complexes
coming from the refinement `t`. -/
theorem cechTotalRefinementMap_def (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t)
    (F : CochainComplex (X.Presheaf AddCommGrpCat.{max u v}) ℤ)
    [((cechDoubleComplex 𝒰 F)).HasTotal (ComplexShape.up ℤ)]
    [((cechDoubleComplex 𝒱 F)).HasTotal (ComplexShape.up ℤ)] :
    cechTotalRefinementMap 𝒰 𝒱 t ht F =
      HomologicalComplex₂.total.map (cechDoubleComplexMap 𝒰 𝒱 t ht F) (ComplexShape.up ℤ) := rfl
