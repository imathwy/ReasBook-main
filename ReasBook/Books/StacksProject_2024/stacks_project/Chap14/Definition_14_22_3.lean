import Mathlib
import StacksProject_2024.Chap14.Lemma_14_21_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Abelian.DoldKan
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open HomologicalComplex
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory

section Concentrated

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜] [HasZeroMorphisms 𝒜]

/- Domain-style sampling for Definition 14.22.3:
- primary domain: truncated simplicial objects as functors on `(SimplexCategory.Truncated k)ᵒᵖ`,
  together with the simplicial operators on the top truncated simplex;
- sampled owner declarations:
  `SimplexCategory.Truncated`,
  `SimplexCategory.eq_σ_comp_of_not_injective`,
  `SimplexCategory.eq_id_of_mono`,
  `SimplicialObject.Truncated.sk`;
- best owner abstraction:
  `source-facing`: the `k`-truncated simplicial object concentrated in degree `k` with value `A`,
    whose non-identity endomorphisms of the top simplex act trivially because they factor through
    lower degrees;
  `core/canonical`: `SimplicialObject.Truncated 𝒜 k`;
  `bridge/view`: the skeleton extension `SimplicialObject.Truncated.sk k` and the Dold-Kan
    comparison at the end of the file.
- primitive data: only the object `A` and the degree `k`;
- derived API: the top-degree evaluation lemma, the skeleton extension
  `eilenberg_maclane_object A k`, and its comparison with `Γ.obj ((single ...).obj A)`.

Source/core/bridge triage:
- `source-facing`: `single_degree_truncated`;
- `core/canonical`: the functor-category owner `SimplicialObject.Truncated 𝒜 k`;
- `bridge/view`: the skeleton and Dold-Kan comparison. -/

/-- The object part of the `k`-truncated simplicial object concentrated in degree `k` with value
`A`. -/
private def single_degree_truncated_obj (A : 𝒜) (k : ℕ) : (SimplexCategory.Truncated k)ᵒᵖ → 𝒜 :=
  fun X ↦ if X.unop.1.len = k then A else ⊥_ 𝒜

-- Proof sketch: unfold `single_degree_truncated_obj`; the hypothesis forces the `if` to reduce to
-- the branch with value `A`.
/-- At the top degree `k`, the concentrated truncated simplicial object has value `A`. -/
private theorem single_degree_truncated_obj_eq_top
    (A : 𝒜) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ)
    (hX : X.unop.1.len = k) :
    single_degree_truncated_obj A k X = A := sorry

private theorem truncated_simplex_eq_top
    {k : ℕ} {X : (SimplexCategory.Truncated k)ᵒᵖ} (hX : X.unop.1.len = k) :
    X.unop.1 = ⦋k⦌ := by
  simpa [hX] using (SimplexCategory.mk_len X.unop.1).symm

/-- Transport a top-degree morphism of the truncated simplex category to an endomorphism of
`[k]`. -/
private def single_degree_truncated_top_endo {k : ℕ}
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y)
    (hX : X.unop.1.len = k) (hY : Y.unop.1.len = k) : ⦋k⦌ ⟶ ⦋k⦌ :=
  eqToHom (truncated_simplex_eq_top hY).symm ≫ f.unop.hom ≫
    eqToHom (truncated_simplex_eq_top hX)

/-- The morphism part of the `k`-truncated simplicial object concentrated in degree `k` with value
`A`. The canonical identity of the top simplex acts by `𝟙 A`, while every other top-degree
operator acts by `0` because it factors through lower degrees. -/
private def single_degree_truncated_map (A : 𝒜) (k : ℕ)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) :
    single_degree_truncated_obj A k X ⟶ single_degree_truncated_obj A k Y :=
  if hX : X.unop.1.len = k then
    if hY : Y.unop.1.len = k then
      if single_degree_truncated_top_endo f hX hY = 𝟙 ⦋k⦌ then
        eqToHom (single_degree_truncated_obj_eq_top A k X hX) ≫
          eqToHom (single_degree_truncated_obj_eq_top A k Y hY).symm
      else 0
    else 0
  else 0

-- Proof sketch: after transporting a top-degree morphism to an endomorphism of `⦋k⦌`, only the
-- canonical identity acts by `𝟙 A`; every other top-degree operator is sent to `0`, and outside
-- the top degree the functor is already zero.
/-- The concentrated degree-`k` map assignment preserves identities. -/
private theorem single_degree_truncated_map_id
    (A : 𝒜) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    single_degree_truncated_map A k (𝟙 X) = 𝟙 (single_degree_truncated_obj A k X) := sorry

-- Proof sketch: check the cases according to whether each object is in degree `k`; away from the
-- top degree all maps are zero, and in top degree the transported endomorphism monoid acts by the
-- indicator of the canonical identity endomorphism.
/-- The concentrated degree-`k` map assignment preserves composition. -/
private theorem single_degree_truncated_map_comp
    (A : 𝒜) (k : ℕ) {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    single_degree_truncated_map A k (f ≫ g) =
      single_degree_truncated_map A k f ≫ single_degree_truncated_map A k g := sorry

/-- The `k`-truncated simplicial object concentrated in degree `k` with value `A`. -/
def single_degree_truncated (A : 𝒜) (k : ℕ) : SimplicialObject.Truncated 𝒜 k where
  obj := single_degree_truncated_obj A k
  map f := single_degree_truncated_map A k f
  map_id X := single_degree_truncated_map_id A k X
  map_comp f g := single_degree_truncated_map_comp A k f g

/-- The concentrated truncated simplicial object has value `A` in top degree. -/
@[simp] theorem single_degree_truncated_obj_top (A : 𝒜) (k : ℕ) :
    (single_degree_truncated A k).obj (Opposite.op ⦋k, le_rfl⦌ₖ) = A :=
  single_degree_truncated_obj_eq_top A k (Opposite.op ⦋k, le_rfl⦌ₖ) rfl

end Concentrated

section EilenbergMacLane

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜] [HasZeroMorphisms 𝒜]
variable [HasFiniteColimits 𝒜]

/-- Definition 14.22.3: the source defines the Eilenberg-MacLane object in an abelian category,
but the underlying skeleton construction already makes sense in any category with zero morphisms,
a zero object, and finite colimits. -/
noncomputable def eilenberg_maclane_object (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  (SimplicialObject.Truncated.sk k).obj (single_degree_truncated A k)

/-- Textbook notation for the Eilenberg-MacLane simplicial object. -/
scoped[Simplicial] notation:max "K(" A ", " k ")" => eilenberg_maclane_object A k

end EilenbergMacLane

section DoldKan

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The Eilenberg-MacLane object is the Dold-Kan image of the single complex concentrated in
degree `k`. -/
private theorem eilenberg_maclane_object_eq_gamma_single (A : 𝒜) (k : ℕ) :
    K(A, k) = Γ.obj ((single 𝒜 (ComplexShape.down ℕ) k).obj A) := by
  sorry

/-- The canonical isomorphism from the Eilenberg-MacLane object to the Dold-Kan image of the
single complex concentrated in degree `k`. -/
noncomputable abbrev eilenbergMacLaneObjectIsoDoldKanSingle (A : 𝒜) (k : ℕ) :
    K(A, k) ≅ Γ.obj ((single 𝒜 (ComplexShape.down ℕ) k).obj A) :=
  eqToIso (eilenberg_maclane_object_eq_gamma_single A k)

/-- The canonical comparison from the normalized Moore complex of `K(A, k)` to the single complex
concentrated in degree `k`. -/
noncomputable def eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle
    (A : 𝒜) (k : ℕ) :
    (AlgebraicTopology.normalizedMooreComplex 𝒜).obj (K(A, k)) ≅
      (single 𝒜 (ComplexShape.down ℕ) k).obj A :=
  (AlgebraicTopology.normalizedMooreComplex 𝒜).mapIso
      (eilenbergMacLaneObjectIsoDoldKanSingle A k) ≪≫
    equivalence.counitIso.app ((single 𝒜 (ComplexShape.down ℕ) k).obj A)

end DoldKan

end CategoryTheory
