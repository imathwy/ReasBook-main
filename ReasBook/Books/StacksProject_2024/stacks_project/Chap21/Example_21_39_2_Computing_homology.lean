import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import StacksProject_2024.stacks_project.Chap21.Example_21_39_1_Category_over_point

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory

open scoped CategoryTheory.CategoryHomology

/-
Domain-style sampling for Example 21.39.2:
- primary domain: category homology of abelian presheaves, computed by the explicit simplicial bar
  construction on composable arrows;
- sampled owner declarations:
  `ComposableArrows`,
  `nerve`,
  `AlgebraicTopology.alternatingFaceMapComplex`,
  `ProjectiveResolution.isoLeftDerivedObj`;
- best owner abstraction: the source-facing object is the simplicial abelian group whose `n`-th
  term is the coproduct over `ComposableArrows C n` of the values `ℱ(Uₙ)`, and the chain complex
  `K_•(ℱ)` is the canonical owner application of
  `alternatingFaceMapComplex`;
- primitive data: a category `C`, an abelian presheaf `ℱ : Cᵒᵖ ⥤ AddCommGrpCat`, a simplex, and a
  composable chain `U₀ ⟶ ⋯ ⟶ Uₙ`;
- derived API: the explicit simplicial object `categoryHomologySimplicialObject`, the chain
  complex `K_•(ℱ)`, and the proposition-level comparison theorem from its homology to the
  canonical owner `H_[n](C, ℱ)`.

Source/core/bridge triage:
- `source-facing`: `categoryHomologySimplicialObject` and `categoryHomologyComplex`;
- `core/canonical`: `H_[n](C, ℱ) = (colim.leftDerived n).obj ℱ`;
- `bridge/view`: the computation theorem
  `categoryHomology_isomorphic_homology_categoryHomologyComplex`, whose proof may use
  `ProjectiveResolution.isoLeftDerivedObj` but whose public statement keeps the Stacks bar
  complex visible. The source-facing comparison remains proposition-valued until an explicit
  concrete comparison morphism is constructed. -/

section

variable {C : Type u} [Category.{v} C]

/-- The induced map from the terminal object of `(nerve C).map f x` to that of `x`. -/
abbrev categoryHomologyTerminalMap (C : Type u) [Category.{v} C]
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (x : ComposableArrows C Δ.unop.len) :
    ((nerve C).map f x).right ⟶ x.right :=
  show x.obj ((f.unop.toOrderHom (Fin.last Δ'.unop.len))) ⟶ x.right from
    x.map
      (show (f.unop.toOrderHom (Fin.last Δ'.unop.len)) ⟶ Fin.last Δ.unop.len from
        homOfLE (Fin.le_last _))

@[simp] theorem categoryHomologyTerminalMap_id {Δ : SimplexCategoryᵒᵖ}
    (x : ComposableArrows C Δ.unop.len) :
    categoryHomologyTerminalMap C (𝟙 Δ) x = 𝟙 x.right := by
  sorry

theorem categoryHomologyTerminalMap_comp
    {Δ₀ Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (f : Δ₀ ⟶ Δ₁) (g : Δ₁ ⟶ Δ₂)
    (x : ComposableArrows C Δ₀.unop.len) :
    categoryHomologyTerminalMap C (f ≫ g) x =
      categoryHomologyTerminalMap C g ((nerve C).map f x) ≫
        categoryHomologyTerminalMap C f x := by
  sorry

/-- Example 21.39.2: the source-facing simplicial abelian group whose `n`-th term is the
coproduct of `ℱ(Uₙ)` over all composable chains `U₀ ⟶ ⋯ ⟶ Uₙ` in `C`. -/
noncomputable def categoryHomologySimplicialObject
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    SimplicialObject AddCommGrpCat.{max u v w} where
  obj Δ := ∐ fun x : ComposableArrows C Δ.unop.len ↦
    ℱ.obj (op x.right)
  map := fun {Δ Δ'} f ↦
    Limits.Sigma.desc fun x : ComposableArrows C Δ.unop.len ↦
      ℱ.map (categoryHomologyTerminalMap C f x).op ≫
        Sigma.ι
          (fun y : ComposableArrows C Δ'.unop.len ↦ ℱ.obj (op y.right))
          ((nerve C).map f x)
  map_id := by
    sorry
  map_comp := by
    sorry

/-- Example 21.39.2: the explicit chain complex `K_•(ℱ)` attached to an abelian presheaf on `C`,
obtained from the source-facing simplicial object by the canonical owner
`alternatingFaceMapComplex`. -/
noncomputable abbrev categoryHomologyComplex
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    ChainComplex AddCommGrpCat.{max u v w} ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{max u v w}).obj
    (categoryHomologySimplicialObject ℱ)

namespace CategoryHomology

@[inherit_doc categoryHomologyComplex]
scoped notation3:max "K_•(" ℱ ")" => CategoryTheory.categoryHomologyComplex ℱ

end CategoryHomology

section

variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{max u v w}]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})]

open scoped CategoryHomology

-- Proof sketch: compare the source-facing bar complex `K_•(ℱ)` with the chain complex
-- obtained from a projective resolution of `ℱ` by applying colimits termwise; the latter
-- computes `H_[n](C, ℱ)` by `ProjectiveResolution.isoLeftDerivedObj`.
/-- Example 21.39.2 (Computing homology): the homology of the explicit complex `K_•(ℱ)` computes
the category homology `H_[n](C, ℱ)`. This source-facing comparison is kept at the
proposition-level owner `IsIsomorphic` until a concrete comparison morphism is constructed. -/
@[stacks 08PG]
theorem categoryHomology_isomorphic_homology_categoryHomologyComplex
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (n : ℕ) :
    IsIsomorphic (H_[n](C, ℱ)) ((K_•(ℱ)).homology n) := by
  sorry

/-- Companion orientation of Example 21.39.2. -/
theorem homology_categoryHomologyComplex_isomorphic_categoryHomology
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (n : ℕ) :
    IsIsomorphic ((K_•(ℱ)).homology n) (H_[n](C, ℱ)) := by
  rcases categoryHomology_isomorphic_homology_categoryHomologyComplex ℱ n with ⟨e⟩
  exact ⟨e.symm⟩

end

end

end CategoryTheory
