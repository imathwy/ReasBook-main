import Mathlib
import StacksProject_2024.Chap14.Lemma_14_21_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Abelian.DoldKan
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open HomologicalComplex
open Opposite
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
    single_degree_truncated_obj A k X = A := by
  -- The length hypothesis selects the top-degree branch of the object definition.
  simp [single_degree_truncated_obj, hX]

/-- Helper for Chap14 Definition 14 22 3: away from the top degree, the concentrated truncated
simplicial object is the zero object. -/
private theorem single_degree_truncated_obj_eq_zero_of_not_top
    (A : 𝒜) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ)
    (hX : X.unop.1.len ≠ k) :
    single_degree_truncated_obj A k X = ⊥_ 𝒜 := by
  -- The non-top hypothesis selects the zero-object branch of the object definition.
  simp [single_degree_truncated_obj, hX]

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

/-- Helper for Chap14 Definition 14 22 3: transporting the identity top-degree simplex map gives
the identity endomorphism of `⦋k⦌`. -/
private theorem single_degree_truncated_top_endo_id {k : ℕ}
    {X : (SimplexCategory.Truncated k)ᵒᵖ} (hX : X.unop.1.len = k) :
    single_degree_truncated_top_endo (𝟙 X) hX hX = 𝟙 ⦋k⦌ := by
  -- The transport only inserts inverse `eqToHom` factors, which cancel on the identity.
  simp [single_degree_truncated_top_endo]

/-- Helper for Chap14 Definition 14 22 3: transporting a composite top-degree simplex map is the
composite of the transported endomorphisms, in the order forced by `.unop`. -/
private theorem single_degree_truncated_top_endo_comp {k : ℕ}
    {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : X.unop.1.len = k) (hY : Y.unop.1.len = k) (hZ : Z.unop.1.len = k) :
    single_degree_truncated_top_endo (f ≫ g) hX hZ =
      single_degree_truncated_top_endo g hY hZ ≫ single_degree_truncated_top_endo f hX hY := by
  -- Unfold the transport wrapper and use functoriality of `unop` together with `eqToHom`
  -- cancellation.
  simp [single_degree_truncated_top_endo, Category.assoc]

/-- Helper for Chap14 Definition 14 22 3: if the transported composite top-degree endomorphism is
the identity, then each transported factor is already the identity. -/
private theorem single_degree_truncated_top_endo_factors_eq_id {k : ℕ}
    {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : X.unop.1.len = k) (hY : Y.unop.1.len = k) (hZ : Z.unop.1.len = k)
    (hcomp : single_degree_truncated_top_endo (f ≫ g) hX hZ = 𝟙 ⦋k⦌) :
    single_degree_truncated_top_endo f hX hY = 𝟙 ⦋k⦌ ∧
      single_degree_truncated_top_endo g hY hZ = 𝟙 ⦋k⦌ := by
  -- Normalize the transported composite and read off `Epi`/`Mono` information from the identity.
  have hcomp' :
      single_degree_truncated_top_endo g hY hZ ≫
        single_degree_truncated_top_endo f hX hY = 𝟙 ⦋k⦌ := by
    rw [single_degree_truncated_top_endo_comp f g hX hY hZ] at hcomp
    exact hcomp
  constructor
  · haveI :
        Epi
          (single_degree_truncated_top_endo g hY hZ ≫
            single_degree_truncated_top_endo f hX hY) := by
      rw [hcomp']
      infer_instance
    haveI : Epi (single_degree_truncated_top_endo f hX hY) :=
      CategoryTheory.epi_of_epi
        (single_degree_truncated_top_endo g hY hZ)
        (single_degree_truncated_top_endo f hX hY)
    exact SimplexCategory.eq_id_of_epi _
  · haveI :
        Mono
          (single_degree_truncated_top_endo g hY hZ ≫
            single_degree_truncated_top_endo f hX hY) := by
      rw [hcomp']
      infer_instance
    haveI : Mono (single_degree_truncated_top_endo g hY hZ) :=
      CategoryTheory.mono_of_mono
        (single_degree_truncated_top_endo g hY hZ)
        (single_degree_truncated_top_endo f hX hY)
    exact SimplexCategory.eq_id_of_mono _

/-- Helper for Chap14 Definition 14 22 3: if a transported top-degree composite is the identity,
then the intermediate truncated simplex is also in top degree. -/
private theorem single_degree_truncated_middle_eq_top_of_comp_eq_id {k : ℕ}
    {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : X.unop.1.len = k) (hZ : Z.unop.1.len = k)
    (hcomp : single_degree_truncated_top_endo (f ≫ g) hX hZ = 𝟙 ⦋k⦌) :
    Y.unop.1.len = k := by
  -- The composite becomes the identity only if the factor through the middle simplex is mono.
  -- Since that factor starts at `⦋k⦌`, monotonicity of lengths forces the middle simplex to have
  -- top length as well.
  have hcomp' :
      ((eqToHom (truncated_simplex_eq_top hZ).symm ≫ g.unop.hom) ≫ f.unop.hom) ≫
        eqToHom (truncated_simplex_eq_top hX) = 𝟙 ⦋k⦌ := by
    simpa [single_degree_truncated_top_endo, Category.assoc] using hcomp
  haveI :
      Mono
        (((eqToHom (truncated_simplex_eq_top hZ).symm ≫ g.unop.hom) ≫ f.unop.hom) ≫
          eqToHom (truncated_simplex_eq_top hX)) := by
    rw [hcomp']
    infer_instance
  haveI : Mono ((eqToHom (truncated_simplex_eq_top hZ).symm ≫ g.unop.hom) ≫ f.unop.hom) :=
    CategoryTheory.mono_of_mono
      ((eqToHom (truncated_simplex_eq_top hZ).symm ≫ g.unop.hom) ≫ f.unop.hom)
      (eqToHom (truncated_simplex_eq_top hX))
  haveI : Mono (eqToHom (truncated_simplex_eq_top hZ).symm ≫ g.unop.hom) :=
    CategoryTheory.mono_of_mono
      (eqToHom (truncated_simplex_eq_top hZ).symm ≫ g.unop.hom)
      f.unop.hom
  have hk_le : k ≤ Y.unop.1.len := by
    change SimplexCategory.len ⦋k⦌ ≤ SimplexCategory.len Y.unop.1
    simpa using
      (SimplexCategory.len_le_of_mono
        (eqToHom (truncated_simplex_eq_top hZ).symm ≫ g.unop.hom) :
          SimplexCategory.len ⦋k⦌ ≤ SimplexCategory.len Y.unop.1)
  exact le_antisymm Y.unop.2 hk_le

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

/-- Helper for Chap14 Definition 14 22 3: any map out of an off-top source object is zero. -/
private theorem single_degree_truncated_map_eq_zero_of_src_not_top
    (A : 𝒜) (k : ℕ) {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y)
    (hX : X.unop.1.len ≠ k) :
    single_degree_truncated_map A k f = 0 := by
  -- The outer degree test of `single_degree_truncated_map` already kills the source-off-top case.
  simp [single_degree_truncated_map, hX]

/-- Helper for Chap14 Definition 14 22 3: any map into an off-top target object is zero. -/
private theorem single_degree_truncated_map_eq_zero_of_tgt_not_top
    (A : 𝒜) (k : ℕ) {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y)
    (hY : Y.unop.1.len ≠ k) :
    single_degree_truncated_map A k f = 0 := by
  -- Once the source degree is split, the inner target test forces the map to be zero.
  by_cases hX : X.unop.1.len = k
  · simp [single_degree_truncated_map, hX, hY]
  · simp [single_degree_truncated_map, hX]

-- Proof sketch: after transporting a top-degree morphism to an endomorphism of `⦋k⦌`, only the
-- canonical identity acts by `𝟙 A`; every other top-degree operator is sent to `0`, and outside
-- the top degree the functor is already zero.
/-- The concentrated degree-`k` map assignment preserves identities. -/
private theorem single_degree_truncated_map_id
    (A : 𝒜) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    single_degree_truncated_map A k (𝟙 X) = 𝟙 (single_degree_truncated_obj A k X) := by
  by_cases hX : X.unop.1.len = k
  · -- In top degree, the transported identity simplex map acts by the identity on `A`.
    simp [single_degree_truncated_obj_eq_top A k X hX, single_degree_truncated_map, hX,
      single_degree_truncated_top_endo_id]
  · -- Off top degree, first rewrite the object to `⊥`, so both sides become the zero morphism.
    have hzeroObj : IsZero (single_degree_truncated_obj A k X) := by
      rw [single_degree_truncated_obj_eq_zero_of_not_top A k X hX]
      exact (Limits.isZero_zero 𝒜).of_iso HasZeroObject.zeroIsoInitial.symm
    rw [single_degree_truncated_map_eq_zero_of_src_not_top A k (𝟙 X) hX]
    exact hzeroObj.eq_of_src _ _

/-- Helper for Chap14 Definition 14 22 3: once the source and target are both in top degree,
composition reduces to the transported endomorphism test and the middle degree split. -/
private theorem single_degree_truncated_map_comp_of_src_tgt_top
    (A : 𝒜) (k : ℕ) {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : X.unop.1.len = k) (hZ : Z.unop.1.len = k) :
    single_degree_truncated_map A k (f ≫ g) =
      single_degree_truncated_map A k f ≫ single_degree_truncated_map A k g := by
  by_cases hY : Y.unop.1.len = k
  · by_cases hcomp : single_degree_truncated_top_endo (f ≫ g) hX hZ = 𝟙 ⦋k⦌
    · -- If the transported composite is the identity, both transported factors are identities.
      rcases single_degree_truncated_top_endo_factors_eq_id f g hX hY hZ hcomp with ⟨hf, hg⟩
      simp [single_degree_truncated_map, hX, hY, hZ, hcomp, hf, hg]
    · -- If the transported composite is not the identity, at least one factor map is already zero.
      by_cases hf : single_degree_truncated_top_endo f hX hY = 𝟙 ⦋k⦌
      · by_cases hg : single_degree_truncated_top_endo g hY hZ = 𝟙 ⦋k⦌
        · have hcomp' : single_degree_truncated_top_endo (f ≫ g) hX hZ = 𝟙 ⦋k⦌ := by
            rw [single_degree_truncated_top_endo_comp f g hX hY hZ, hf, hg]
            simp
          exact (hcomp hcomp').elim
        · simp [single_degree_truncated_map, hX, hY, hZ, hcomp, hf, hg]
      · simp [single_degree_truncated_map, hX, hY, hZ, hcomp, hf]
  · -- Route correction: when the middle simplex is off top degree, an identity composite is
    -- impossible, so every surviving branch collapses to zero.
    by_cases hcomp : single_degree_truncated_top_endo (f ≫ g) hX hZ = 𝟙 ⦋k⦌
    · exact (hY (single_degree_truncated_middle_eq_top_of_comp_eq_id f g hX hZ hcomp)).elim
    · rw [single_degree_truncated_map_eq_zero_of_tgt_not_top A k f hY,
        single_degree_truncated_map_eq_zero_of_src_not_top A k g hY]
      simp [single_degree_truncated_map, hX, hZ, hcomp]

-- Proof sketch: check the cases according to whether each object is in degree `k`; away from the
-- top degree all maps are zero, and in top degree the transported endomorphism monoid acts by the
-- indicator of the canonical identity endomorphism.
/-- The concentrated degree-`k` map assignment preserves composition. -/
private theorem single_degree_truncated_map_comp
    (A : 𝒜) (k : ℕ) {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    single_degree_truncated_map A k (f ≫ g) =
      single_degree_truncated_map A k f ≫ single_degree_truncated_map A k g := by
  by_cases hX : X.unop.1.len = k
  · by_cases hZ : Z.unop.1.len = k
    · -- Only the source-top/target-top branch is nontrivial; isolate it in the helper above.
      exact single_degree_truncated_map_comp_of_src_tgt_top A k f g hX hZ
    · -- If the target is off top degree, the composite and the second factor are both zero.
      rw [single_degree_truncated_map_eq_zero_of_tgt_not_top A k (f ≫ g) hZ,
        single_degree_truncated_map_eq_zero_of_tgt_not_top A k g hZ]
      simp
  · -- If the source is off top degree, the composite and the first factor are both zero.
    rw [single_degree_truncated_map_eq_zero_of_src_not_top A k (f ≫ g) hX,
      single_degree_truncated_map_eq_zero_of_src_not_top A k f hX]
    simp

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
@[stacks 0191]
noncomputable def eilenberg_maclane_object (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  (SimplicialObject.Truncated.sk k).obj (single_degree_truncated A k)

/-- Textbook notation for the Eilenberg-MacLane simplicial object. -/
scoped[Simplicial] notation:max "K(" A ", " k ")" => eilenberg_maclane_object A k

end EilenbergMacLane

section DoldKan

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local instance : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts

/-- Helper for Chap14 Definition 14 22 3: the surviving degree-`n` generators are indexed by the
epimorphisms `⦋n⦌ ⟶ ⦋k⦌`. -/
private abbrev topEpiIndex (k n : ℕ) := { θ : ⦋n⦌ ⟶ ⦋k⦌ // Epi θ }

/-- Helper for Chap14 Definition 14 22 3: the index set of surviving generators is finite. -/
private instance topEpiIndex_fintype (k n : ℕ) : Fintype (topEpiIndex k n) :=
  Fintype.ofFinite _

/-- Helper for Chap14 Definition 14 22 3: a surviving generator remembers its epimorphism
structure as an instance. -/
private instance topEpiIndex_epi {k n : ℕ} (α : topEpiIndex k n) : Epi α.1 :=
  α.2

/-- Helper for Chap14 Definition 14 22 3: the Dold-Kan inverse functor comes with its canonical
splitting. -/
private noncomputable def gammaSplitting (K : ChainComplex 𝒜 ℕ) :
    SimplicialObject.Splitting (Γ.obj K) := by
  simpa [Abelian.DoldKan.Γ, Idempotents.DoldKan.Γ, AlgebraicTopology.DoldKan.Γ₀] using
    (AlgebraicTopology.DoldKan.Γ₀.splitting K)

/-- Helper for Chap14 Definition 14 22 3: an index of the splitting of `Γ(single A[k])` lies over
the top degree exactly when it determines an epimorphism `⦋n⦌ ⟶ ⦋k⦌`. -/
private noncomputable def gammaTopEpiIndex {k n : ℕ}
    (B : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) (h : B.1.unop.len = k) :
    topEpiIndex k n :=
  by
    -- The splitting index already carries an epi `B.e`, and transport to `⦋k⦌` preserves epi.
    let θ : ⦋n⦌ ⟶ ⦋k⦌ := B.e ≫ eqToHom (SimplexCategory.ext h)
    haveI : Epi θ := by
      dsimp [θ]
      infer_instance
    exact ⟨θ, inferInstance⟩

/-- Helper for Chap14 Definition 14 22 3: taking the associated top-degree epimorphism of a
canonical splitting index and rebuilding the splitting index gives back the original summand. -/
private theorem gammaTopEpiIndex_mk {k n : ℕ} (α : topEpiIndex k n) :
    gammaTopEpiIndex (SimplicialObject.Splitting.IndexSet.mk α.1) rfl = α := by
  -- The round-trip keeps the same underlying epi `⦋n⦌ ⟶ ⦋k⦌`, so the subtype equality is
  -- immediate.
  apply Subtype.ext
  change (SimplicialObject.Splitting.IndexSet.mk α.1).e ≫ eqToHom (SimplexCategory.ext rfl) = α.1
  rw [eqToHom_refl]
  change α.1 ≫ 𝟙 _ = α.1
  simp

/-- Helper for Chap14 Definition 14 22 3: a top-degree splitting index is exactly the one attached
to its associated epimorphism `⦋n⦌ ⟶ ⦋k⦌`. -/
private theorem gammaIndex_eq_mk {k n : ℕ}
    (B : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) (h : B.1.unop.len = k) :
    B = SimplicialObject.Splitting.IndexSet.mk (gammaTopEpiIndex B h).1 :=
  by
    -- Route correction: normalize every top-degree splitting index to the canonical `IndexSet.mk`
    -- spelling before comparing maps out of the corresponding summand.
    refine SimplicialObject.Splitting.IndexSet.ext B
      (SimplicialObject.Splitting.IndexSet.mk (gammaTopEpiIndex B h).1) ?_ ?_
    · -- The top-degree hypothesis identifies the target simplex with `⦋k⦌`.
      simpa using congrArg Opposite.op (SimplexCategory.ext h)
    · -- After that identification, both epimorphisms are literally `B.e` followed by the same
      -- transport to `⦋k⦌`.
      rfl

/-- Helper for Chap14 Definition 14 22 3: if a splitting summand of `Γ(single A[k])` comes from a
degree other than `k`, then that summand is zero. -/
private theorem gammaSingleCofanInj_eq_zero
    (A : 𝒜) (k : ℕ) {Δ : SimplexCategoryᵒᵖ}
    (B : SimplicialObject.Splitting.IndexSet Δ) (h : B.1.unop.len ≠ k) :
    ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) k).obj A)).cofan Δ).inj B = 0 := by
  -- Off the top degree, the single complex already vanishes.
  let hzero :=
    isZero_single_obj_X (ComplexShape.down ℕ) k A B.1.unop.len h
  exact hzero.eq_of_src _ _

/-- Helper for Chap14 Definition 14 22 3: the forward map from `Γ(single A[k])_n` to the
top-degree biproduct keeps exactly the splitting summands that lie in degree `k`. -/
private noncomputable def gammaSingleObjIsoHom (A : 𝒜) (k n : ℕ) :
    (Γ.obj ((single 𝒜 (ComplexShape.down ℕ) k).obj A)) _⦋n⦌ ⟶
      ⨁ fun _ : topEpiIndex k n ↦ A :=
  (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) k).obj A)).desc _ fun B =>
    if h : B.1.unop.len = k then
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.down ℕ) k A B.1.unop.len h).hom ≫
        biproduct.ι (fun _ : topEpiIndex k n ↦ A) (gammaTopEpiIndex B h)
    else 0

/-- Helper for Chap14 Definition 14 22 3: the forward map kills every splitting summand away from
the top degree. -/
private theorem gammaSingleObjIsoHom_inj_eq_zero_of_not_top
    (A : 𝒜) (k n : ℕ) (B : SimplicialObject.Splitting.IndexSet (op ⦋n⦌))
    (h : B.1.unop.len ≠ k) :
    ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) k).obj A)).cofan _).inj B ≫
      gammaSingleObjIsoHom A k n = 0 := by
  -- The splitting desc formula reduces this to the `if`-branch, which is zero off the top degree.
  rw [gammaSingleObjIsoHom, SimplicialObject.Splitting.ι_desc]
  simp [h]
  rfl

/-- Helper for Chap14 Definition 14 22 3: on a top-degree splitting summand, the forward map is
the transported inclusion into the corresponding biproduct factor. -/
private theorem gammaSingleObjIsoHom_inj_eq_of_top
    (A : 𝒜) (k n : ℕ) (B : SimplicialObject.Splitting.IndexSet (op ⦋n⦌))
    (h : B.1.unop.len = k) :
    ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) k).obj A)).cofan _).inj B ≫
      gammaSingleObjIsoHom A k n =
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.down ℕ) k A B.1.unop.len h).hom ≫
          biproduct.ι (fun _ : topEpiIndex k n ↦ A) (gammaTopEpiIndex B h) := by
  -- Once the degree test is positive, the forward map is literally the chosen branch of the desc.
  rw [gammaSingleObjIsoHom, SimplicialObject.Splitting.ι_desc]
  subst h
  rw [dif_pos rfl]
  let β :
      ((single 𝒜 (ComplexShape.down ℕ) B.1.unop.len).obj A).X B.1.unop.len ⟶
        ⨁ fun _ : topEpiIndex B.1.unop.len n ↦ A :=
    (HomologicalComplex.singleObjXIsoOfEq
        (ComplexShape.down ℕ) B.1.unop.len A B.1.unop.len rfl).hom ≫
      biproduct.ι (fun _ : topEpiIndex B.1.unop.len n ↦ A) (gammaTopEpiIndex B rfl)
  change β = β
  rfl

/-- Helper for Chap14 Definition 14 22 3: the inverse map from the top-degree biproduct sends each
factor back to the canonical top-degree splitting summand. -/
private noncomputable def gammaSingleObjIsoInv (A : 𝒜) (k n : ℕ) :
    (⨁ fun _ : topEpiIndex k n ↦ A) ⟶
      (Γ.obj ((single 𝒜 (ComplexShape.down ℕ) k).obj A)) _⦋n⦌ :=
  biproduct.desc fun α =>
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) k A).inv ≫
      ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) k).obj A)).cofan _).inj
        (SimplicialObject.Splitting.IndexSet.mk α.1)

/-- Helper for Chap14 Definition 14 22 3: precomposing the inverse map with a biproduct injection
recovers the corresponding canonical top-degree splitting summand. -/
private theorem biproduct_ι_gammaSingleObjIsoInv
    (A : 𝒜) (k n : ℕ) (α : topEpiIndex k n) :
    biproduct.ι (fun _ : topEpiIndex k n ↦ A) α ≫ gammaSingleObjIsoInv A k n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) k A).inv ≫
        ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) k).obj A)).cofan _).inj
          (SimplicialObject.Splitting.IndexSet.mk α.1) := by
  -- The inverse is a biproduct desc, so each injection selects its defining branch.
  rw [gammaSingleObjIsoInv, biproduct.ι_desc]
  rfl

/-- Helper for Chap14 Definition 14 22 3: degree `n` of `Γ(single A[k])` is the biproduct of the
top-degree summands indexed by epimorphisms `⦋n⦌ ⟶ ⦋k⦌`. -/
private noncomputable def gammaSingleObjIso (A : 𝒜) (k n : ℕ) :
    (Γ.obj ((single 𝒜 (ComplexShape.down ℕ) k).obj A)) _⦋n⦌ ≅
      ⨁ fun _ : topEpiIndex k n ↦ A :=
  -- TODO: the forward and inverse maps are now factored as `gammaSingleObjIsoHom` and
  -- `gammaSingleObjIsoInv`. Finish the proof by:
  -- 1. `Splitting.hom_ext'` on `hom ≫ inv = 𝟙`, using
  --    `gammaSingleObjIsoHom_inj_eq_zero_of_not_top`, `gammaSingleObjIsoHom_inj_eq_of_top`,
  --    `gammaIndex_eq_mk`, and `biproduct.ι_desc`;
  -- 2. `biproduct.hom_ext'` on `inv ≫ hom = 𝟙`, using `biproduct_ι_gammaSingleObjIsoInv` and
  --    `gammaTopEpiIndex_mk`.
  sorry

/-- The canonical isomorphism from the Eilenberg-MacLane object to the Dold-Kan image of the
single complex concentrated in degree `k`. -/
noncomputable def eilenbergMacLaneObjectIsoDoldKanSingle (A : 𝒜) (k : ℕ) :
    K(A, k) ≅ Γ.obj ((single 𝒜 (ComplexShape.down ℕ) k).obj A) :=
by
  -- The skeleton model and the explicit Dold-Kan model are not definitionally equal. The comparison
  -- is an isomorphism, obtained degreewise by identifying both sides with the coproduct indexed by
  -- the epimorphisms `⦋n⦌ ⟶ ⦋k⦌`.
  -- TODO: compare `K(A,k)` and `Γ(single A[k])` through a common epi-indexed biproduct model, or
  -- equivalently prove that `normalizedMooreComplex.obj (K(A,k))` is the single complex and reflect
  -- the resulting degreewise isomorphism back across the Dold-Kan unit.
  sorry

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
