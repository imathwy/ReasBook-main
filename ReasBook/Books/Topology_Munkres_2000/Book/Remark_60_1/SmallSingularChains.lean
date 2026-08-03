module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Sets.OpenCover

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory Simplicial

universe u v

/-- Helper for Remark 60.1: the canonical inclusion of a subspace into its ambient
topological space. -/
def singularSubspaceInclusion (X : TopCat) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))

/-- Helper for Remark 60.1: the canonical subspace inclusion is the map of the
associated topological pair. -/
lemma singularSubspaceInclusion_eq_ofSubset_map (X : TopCat) (A : Set X) :
    singularSubspaceInclusion X A = (TopPair.ofSubset A).map := by
  -- Both constructions bundle the subtype projection with its continuity proof.
  rfl

/-- Helper for Remark 60.1: forgetting the bundled subspace inclusion gives the
usual continuous subtype projection. -/
lemma singularSubspaceInclusion_hom (X : TopCat) (A : Set X) :
    (singularSubspaceInclusion X A).hom =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) := by
  -- This is the defining continuous map of the bundled inclusion.
  rfl

/-- Helper for Remark 60.1: postcomposing a map into a subspace with its
canonical inclusion forgets the subtype after applying the first map. -/
lemma hom_comp_singularSubspaceInclusion {Y : TopCat} (X : TopCat) (A : Set X)
    (f : Y ⟶ TopCat.of A) :
    (f ≫ singularSubspaceInclusion X A).hom =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp f.hom := by
  -- Expand categorical composition, then use the inclusion's owner computation rule.
  rw [TopCat.hom_comp, singularSubspaceInclusion_hom]

/-- Helper for Remark 60.1: the singular-simplex equivalence carries the map of a
continuous function to postcomposition by that function. -/
lemma toSSetObjEquiv_map {X Y : TopCat} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n σ) =
      f.hom.comp (X.toSSetObjEquiv n σ) := by
  -- Both sides are the defining postcomposition action of the restricted Yoneda functor.
  rfl

/-- Helper for Remark 60.1: a continuous map factors through a subspace exactly
when its range lies in that subspace. -/
lemma continuousMap_factorsThrough_subtype_iff
    {Y : Type u} {X : Type v} [TopologicalSpace Y] [TopologicalSpace X]
    (A : Set X) (σ : C(Y, X)) :
    (∃ τ : C(Y, A),
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp τ = σ) ↔
      Set.range σ ⊆ A := by
  constructor
  · rintro ⟨τ, rfl⟩
    -- A map into the subtype lands in the defining set after forgetting the subtype.
    exact Set.range_subset_iff.mpr fun y ↦ (τ y).property
  · intro hσ
    -- Bundle the range-containment hypothesis as a continuous map into the subtype.
    let τ : C(Y, A) :=
      ⟨fun y ↦ ⟨σ y, hσ (Set.mem_range_self y)⟩, σ.continuous.subtype_mk _⟩
    have hτ :
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp τ = σ := by
      ext y
      rfl
    exact ⟨τ, hτ⟩

/-- Helper for Remark 60.1: the singular simplices that factor through one member
of a family of subspaces. -/
def smallSingularSubcomplex {ι : Type} (X : TopCat) (U : ι → Set X) :
    (TopCat.toSSet.obj X).Subcomplex :=
  ⨆ i, SSet.Subcomplex.range
    (TopCat.toSSet.map (singularSubspaceInclusion X (U i)))

/-- Helper for Remark 60.1: for two open subspaces, the small singular
subcomplex is the supremum of their two singular ranges. -/
lemma smallSingularSubcomplex_opens_bool (X : TopCat)
    (A B : TopologicalSpace.Opens X) :
    smallSingularSubcomplex X (fun b : Bool ↦ (Bool.rec A B b : Set X)) =
      SSet.Subcomplex.range
          (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X))) ⊔
        SSet.Subcomplex.range
          (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))) := by
  -- The Boolean supremum lists the `true` branch before the `false` branch.
  unfold smallSingularSubcomplex
  rw [iSup_bool_eq]

/-- Helper for Remark 60.1: membership in the small singular subcomplex is exactly
factorization through one member of the family. -/
lemma mem_smallSingularSubcomplex_iff_exists
    {ι : Type} (X : TopCat) (U : ι → Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (smallSingularSubcomplex X U).obj n ↔
      ∃ i τ, (TopCat.toSSet.map (singularSubspaceInclusion X (U i))).app n τ = σ := by
  -- Evaluate the supremum and then the range subcomplex at the chosen simplex degree.
  simp only [smallSingularSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subfunctor.range_obj, Set.mem_range]

/-- Helper for Remark 60.1: a singular simplex is cover-small exactly when its
continuous representative has image in one member of the family. -/
lemma mem_smallSingularSubcomplex_iff_range_subset
    {ι : Type} (X : TopCat) (U : ι → Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (smallSingularSubcomplex X U).obj n ↔
      ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i := by
  -- First replace subcomplex membership by factorization of the singular simplex.
  rw [mem_smallSingularSubcomplex_iff_exists]
  constructor
  · rintro ⟨i, τ, hτ⟩
    refine ⟨i, ?_⟩
    -- Transport the factorization across the singular-simplex equivalence.
    have hcomp :
        (singularSubspaceInclusion X (U i)).hom.comp
            ((TopCat.of (U i)).toSSetObjEquiv n τ) =
          X.toSSetObjEquiv n σ := by
      rw [← hτ, toSSetObjEquiv_map]
    have hfactor :
        ∃ τ : C(stdSimplex ℝ (Fin (n.unop.len + 1)), U i),
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X)).comp τ =
            X.toSSetObjEquiv n σ := by
      refine ⟨(TopCat.of (U i)).toSSetObjEquiv n τ, ?_⟩
      simpa only [singularSubspaceInclusion, TopCat.hom_ofHom] using hcomp
    exact (continuousMap_factorsThrough_subtype_iff (U i)
      (X.toSSetObjEquiv n σ)).mp hfactor
  · rintro ⟨i, hi⟩
    -- Bundle containment as a subtype-valued simplex and transport it back.
    obtain ⟨τ, hτ⟩ :=
      (continuousMap_factorsThrough_subtype_iff (U i)
        (X.toSSetObjEquiv n σ)).mpr hi
    let τ' := ((TopCat.of (U i)).toSSetObjEquiv n).symm τ
    refine ⟨i, τ', ?_⟩
    apply (X.toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map, Equiv.apply_symm_apply]
    simpa only [singularSubspaceInclusion, TopCat.hom_ofHom] using hτ

/-- Helper for Remark 60.1: the integral chain inclusion from cover-small singular
chains to all singular chains. -/
abbrev integralSmallSingularChainInclusion
    {ι : Type} (X : TopCat) (U : ι → Set X) :
    (smallSingularSubcomplex X U : SSet).chainComplex (ModuleCat.of ℤ ℤ) ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ) :=
  SSet.chainComplexMap (smallSingularSubcomplex X U).ι (ModuleCat.of ℤ ℤ)

/-- Helper for Remark 60.1: integral simplicial chains preserve monomorphisms of
simplicial sets. -/
lemma integralSimplicialChainComplex_preservesMonomorphisms :
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).PreservesMonomorphisms := by
  constructor
  intro X Y f hf
  -- Pass monicity through the free-module simplicial object and alternating complex.
  have hfree :
      Mono
        (((Limits.sigmaConst ⋙
          SimplicialObject.whiskering (Type) (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map f) := by
    have happ : ∀ n,
        Mono
          ((((Limits.sigmaConst ⋙
            SimplicialObject.whiskering (Type) (ModuleCat ℤ)).obj
              (ModuleCat.of ℤ ℤ)).map f).app n) := by
      intro n
      change Mono
        ((Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (f.app n))
      apply Functor.map_mono
    exact (NatTrans.mono_iff_mono_app _).mpr happ
  exact Functor.map_mono (alternatingFaceMapComplex (ModuleCat ℤ)) _

/-- Helper for Remark 60.1: the inclusion of cover-small integral singular chains
is monic. -/
lemma integralSmallSingularChainInclusion_mono
    {ι : Type} (X : TopCat) (U : ι → Set X) :
    Mono (integralSmallSingularChainInclusion X U) := by
  -- Simplicial chains preserve the monic inclusion of a simplicial subcomplex.
  letI := integralSimplicialChainComplex_preservesMonomorphisms
  infer_instance

/-- Helper for Remark 60.1: the cover-small chain inclusion is injective in every
degree. -/
lemma integralSmallSingularChainInclusion_injective
    {ι : Type} (X : TopCat) (U : ι → Set X) (n : ℕ) :
    Function.Injective ((integralSmallSingularChainInclusion X U).f n) := by
  -- Evaluate the monic chain map and use the concrete criterion for module maps.
  letI : Mono (integralSmallSingularChainInclusion X U) :=
    integralSmallSingularChainInclusion_mono X U
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- Helper for Remark 60.1: the small-chain inclusion sends each small simplex
generator to the corresponding ambient singular-simplex generator. -/
lemma integralSmallSingularChainInclusion_ι
    {ι : Type} (X : TopCat) (U : ι → Set X) (n : ℕ)
    (σ : (smallSingularSubcomplex X U : SSet) _⦋n⦌) :
    (smallSingularSubcomplex X U : SSet).ιChainComplex σ ≫
        (integralSmallSingularChainInclusion X U).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ.1 := by
  -- Apply the standard generator computation rule for a simplicial chain map.
  exact SSet.ι_chainComplexMap_f
    (smallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X)
      (smallSingularSubcomplex X U).ι (ModuleCat.of ℤ ℤ) σ

end AlgebraicTopology
