import Mathlib
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import stacks_project.Chap20.«20_9_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace ComplexShape HomologicalComplex₂
open CategoryTheory.Limits

noncomputable section

universe u v

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}} {ι : Type v}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]

local instance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
  HasSheafify.isRightAdjoint

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X
local instance : OrderTop (Opens X) := opensOrderTop X

/-- The category of abelian sheaves on `X` is preadditive. -/
noncomputable instance sheafAddCommGrpPreadditive (X : TopCat.{u}) :
    Preadditive (X.Sheaf AddCommGrpCat.{max u v}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}))

/- Domain-style sampling for 20.40.0.1:
- primary domain: the global-sections-to-extended alternating Čech comparison for unbounded
  cochain complexes of abelian sheaves on a topological space;
- sampled owner declarations:
  `Sheaf.Γ`,
  `Sheaf.ΓRes`,
  `CategoryTheory.cechComplexFunctor`,
  `ComplexShape.embeddingUpNat.extendFunctor`,
  `Functor.mapHomologicalComplex`,
  `HomologicalComplex₂.totalFunctor`;
- best owner abstraction: the public comparison should be built from the canonical global-sections
  owner `Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat` and the canonical restriction maps
  `Sheaf.ΓRes`; the rowwise Čech construction remains the order-free `cechComplexFunctor 𝒰`
  extended along `embeddingUpNat`, and its rows are exposed explicitly as the source-facing
  alternating Čech owner recalled in Definition `20.23.1`;
- primitive data: only the space `X`, the indexed family of opens `𝒰`, and the unbounded sheaf
  complex `ℱ`;
- derived API: the extended rowwise Čech bicomplex underlying the alternating comparison, its total
  complex, the canonical comparison morphism from the global-sections complex, and the row
  identification with the alternating owner from Definition `20.23.1`.

Source/core/bridge triage:
- `source-facing`: `alternatingCechDoubleComplexFunctor`,
  `alternatingCechTotalComplexFunctor`, and
  `globalSectionsToAlternatingCechTotalMap`;
- `core/canonical`: `Sheaf.Γ`, `Sheaf.ΓRes`, `cechComplexFunctor`,
  `embeddingUpNat.extendFunctor`, `Functor.mapHomologicalComplex`, and
  `HomologicalComplex₂.totalFunctor`;
- `bridge/view`: the internal order-free rowwise sheaf-Čech functor obtained by composing
  `sheafToPresheaf`, `cechComplexFunctor`, and `embeddingUpNat.extendFunctor`, together with the
  row-identification theorem `alternatingCechDoubleComplexFunctor_obj_X`.

This file therefore reuses the canonical global-sections owner `Sheaf.Γ` and the restriction maps
`Sheaf.ΓRes`, instead of keeping a raw evaluation-at-`⊤` presentation of global sections. It also
exposes the rowwise `cechComplexFunctor` construction directly as the recalled alternating Čech
owner from Definition `20.23.1`, instead of leaving that source-facing semantics implicit. -/

private instance sheafGamma_preservesZeroMorphisms :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).PreservesZeroMorphisms := by
  sorry

private abbrev cechZeroIntersection (𝒰 : ι → Opens X) (σ : Fin 1 → ι) : Opens X :=
  ∏ᶜ (𝒰 ∘ σ)

private abbrev sheafCechRowFunctor (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    X.Sheaf AddCommGrpCat.{max u v} ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ :=
  CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} ⋙
    CategoryTheory.cechComplexFunctor 𝒰 ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{max u v}

private instance sheafCechRowFunctor_preservesZeroMorphisms
    (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    (sheafCechRowFunctor X 𝒰).PreservesZeroMorphisms := by
  sorry

/-- The rowwise alternating Čech bicomplex attached to an unbounded complex of abelian sheaves. -/
abbrev alternatingCechDoubleComplexFunctor (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u v}
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (sheafCechRowFunctor X 𝒰).mapHomologicalComplex (ComplexShape.up ℤ)

private abbrev cechRowComplex (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : X.Sheaf AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (CategoryTheory.cechComplexFunctor 𝒰).obj
    ((CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v}).obj ℱ)

private abbrev cechRowComplexZeroIso (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ) (n : ℤ) :
    (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).X n).X 0 ≅
      (cechRowComplex X 𝒰 (ℱ.X n)).X 0 :=
  by
    simpa [alternatingCechDoubleComplexFunctor, sheafCechRowFunctor, cechRowComplex] using
      (cechRowComplex X 𝒰 (ℱ.X n)).extendXIso embeddingUpNat rfl

/-- Each row of `alternatingCechDoubleComplexFunctor` is exactly the extension to `ℤ` of the
alternating Čech complex owner recalled in Definition `20.23.1`, specialized to the underlying
presheaf of the corresponding sheaf term. -/
theorem alternatingCechDoubleComplexFunctor_obj_X (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ) (n : ℤ) :
    ((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).X n =
      (((CategoryTheory.cechComplexFunctor 𝒰).obj
          ((CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{max u v}).obj (ℱ.X n))).extend embeddingUpNat) :=
  rfl

/-- The total alternating Čech complex attached to an unbounded complex of abelian sheaves and an
indexed family of opens. -/
abbrev alternatingCechTotalComplexFunctor (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ ⥤
      CochainComplex AddCommGrpCat.{max u v} ℤ :=
  alternatingCechDoubleComplexFunctor X 𝒰 ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{max u v}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

private def globalSectionsToAlternatingCechZeroComponent (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ) (n : ℤ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (ℱ.X n) ⟶
      (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).X n).X 0 :=
  (Pi.lift fun σ : Fin 1 → ι ↦
    Sheaf.ΓRes (J := Opens.grothendieckTopology X) (A := AddCommGrpCat.{max u v})
      (ℱ.X n) (op (cechZeroIntersection 𝒰 σ))) ≫
    (cechRowComplexZeroIso X 𝒰 ℱ n).inv

/-- The degree-`n` component of the canonical map from global sections to the total alternating
Čech complex. -/
def globalSectionsToAlternatingCechTotalComponent (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ) (n : ℤ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (ℱ.X n) ⟶
      ((alternatingCechTotalComplexFunctor X 𝒰).obj ℱ).X n :=
  globalSectionsToAlternatingCechZeroComponent X 𝒰 ℱ n ≫
    (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).ιTotal
      (ComplexShape.up ℤ) n 0 n
      (show (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n by
        simp))

-- Proof sketch: the total differential is the sum of the horizontal differential from the sheaf
-- complex and the vertical alternating Čech differential. Since the component lands in Čech degree
-- `0`, compatibility reduces to naturality of restriction maps with respect to the differentials
-- of `ℱ`.
/-- The degreewise maps from global sections to the total alternating Čech complex commute with the
differentials. -/
theorem globalSectionsToAlternatingCechTotalComponent_comm (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ) {n n' : ℤ}
    (h : (ComplexShape.up ℤ).Rel n n') :
    globalSectionsToAlternatingCechTotalComponent X 𝒰 ℱ n ≫
        ((alternatingCechTotalComplexFunctor X 𝒰).obj ℱ).d n n' =
      (((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ℱ).d n n' ≫
        globalSectionsToAlternatingCechTotalComponent X 𝒰 ℱ n' := sorry

/-- 20.40.0.1: the canonical morphism
`Γ(X, \mathcal F^\bullet) ⟶ \operatorname{Tot}(\check{\mathcal C}^\bullet_{alt}(\mathcal U,
\mathcal F^\bullet))` from the global-sections complex of an unbounded complex of abelian sheaves
to the total alternating Čech complex associated to the indexed family `𝒰`. -/
def globalSectionsToAlternatingCechTotalMap (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ) :
    ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ℱ ⟶
      (alternatingCechTotalComplexFunctor X 𝒰).obj ℱ where
  f n := globalSectionsToAlternatingCechTotalComponent X 𝒰 ℱ n
  comm' _ _ h := globalSectionsToAlternatingCechTotalComponent_comm X 𝒰 ℱ h

-- Proof sketch: this is immediate from the definition of
-- `globalSectionsToAlternatingCechTotalMap`; the degree-`n` component is the degree-zero Čech
-- restriction map followed by the inclusion of the `(n, 0)` summand into the total complex.
/-- The degree-`n` component of the global-sections-to-alternating-Čech comparison map. -/
theorem globalSectionsToAlternatingCechTotalMap_f (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{max u v}) ℤ) (n : ℤ) :
    (globalSectionsToAlternatingCechTotalMap X 𝒰 ℱ).f n =
      globalSectionsToAlternatingCechTotalComponent X 𝒰 ℱ n :=
  rfl

end

end TopCat.Sheaf
