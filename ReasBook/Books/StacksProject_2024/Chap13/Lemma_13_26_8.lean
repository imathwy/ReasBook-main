import Mathlib
import StacksProject_2024.Chap13.Lemma_13_26_6

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)]

local instance instCategoryWithHomologyGradedObjectInt_13_26_8 :
    CategoryWithHomology (GradedObject ℤ 𝒜) := by
  have hzero : (Preadditive.preadditiveHasZeroMorphisms :
      HasZeroMorphisms (GradedObject ℤ 𝒜)) = GradedObject.hasZeroMorphisms ℤ :=
    HasZeroMorphisms.ext _ _
  exact hzero ▸
    (@_root_.CategoryTheory.categoryWithHomology_of_abelian (GradedObject ℤ 𝒜) _ _)

namespace CochainComplex

local notation "FilF" => Fil^f(𝒜)
local notation "FiltInjPlus" => FilteredInjectivePlus 𝒜
local notation "single₀" => CochainComplex.singleFunctor FilF (0 : ℤ)
local notation "ιFiltInjPlus" => CochainComplex.PlusWithTermsIn.ι IsFilteredInjective
private abbrev assocGraded := finiteFilteredObjectAssociatedGradedCochainFunctor 𝒜

/- Domain-style sampling for Lemma `13.26.8`.
- primary domain: horseshoe diagrams in the bounded-below filtered-complex category
  `CochainComplex.Plus (Fil^f(𝒜))`, with filtered-injective rows and filtered quasi-isomorphism
  comparison maps;
- sampled owner declarations:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.PlusWithTermsIn.ι`,
  `CategoryTheory.ShortComplex`,
  `ShortComplex.Hom`,
  `ShortComplex.ShortExact`,
  `finiteFilteredObjectAssociatedGradedCochainFunctor`;
- best owner abstraction: the lower row is canonically owned by
  `ShortComplex (CochainComplex.FilteredInjectivePlus 𝒜)`, its comparison with the degree-zero
  short exact sequence is owned by `ShortComplex.Hom`, and short exactness is owned by
  `ShortComplex.ShortExact`, while the source-facing termwise-split conclusion is owned by the
  degreewise family `∀ n, (T.map (HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting`
  on the underlying short complex `T`;
- primitive data: the prescribed outer filtered-injective complexes and outer vertical maps, a
  lower short complex in `CochainComplex.FilteredInjectivePlus 𝒜`, and the comparison morphism
  from `S.map single₀` to its image after applying the canonical inclusion
  `CochainComplex.PlusWithTermsIn.ι`, together with the
  degreewise splitting of the lower row;
- derived API: the lower-row short exactness deduced from the degreewise splitting family, and the
  middle filtered quasi-isomorphism deduced from that short exactness plus the outer filtered
  quasi-isomorphisms;
- source/core/bridge triage:
  `source-facing`: the existence theorem below, stated with prescribed outer filtered
    quasi-isomorphisms and an explicit degreewise-splitting conclusion;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus`,
    `CochainComplex.PlusWithTermsIn.ι`,
    `ShortComplex`, `ShortComplex.Hom`, `ShortComplex.ShortExact`, and the associated-graded
    functor on `CochainComplex (Fil^f(𝒜)) ℤ`;
  `bridge/view`: the canonical bounded-below inclusion
    `CochainComplex.PlusWithTermsIn.ι`. -/

omit [EnoughInjectives 𝒜] in
/-- For a morphism between two short exact rows, if the outer vertical components are filtered
quasi-isomorphisms, then so is the middle component. -/
theorem quasiIso_middle {S : ShortComplex FilF} (hS : S.ShortExact)
    {T : ShortComplex FiltInjPlus} (φ : S.map single₀ ⟶ T.map ιFiltInjPlus)
    (hrow : (T.map ιFiltInjPlus).ShortExact)
    (hτ₁ : QuasiIso (assocGraded.map φ.τ₁))
    (hτ₃ : QuasiIso (assocGraded.map φ.τ₃)) :
    QuasiIso (assocGraded.map φ.τ₂) := by
  sorry

-- Proof sketch: starting from the prescribed filtered quasi-isomorphisms on the outer terms, lift
-- the outer objects into bounded-below filtered-injective complexes, build the middle
-- filtered-injective complex degreewise by extension, and assemble the lower row directly as a
-- short complex in `CochainComplex.FilteredInjectivePlus 𝒜` together with a single comparison
-- morphism from the degree-zero short exact sequence. The lower row is recorded by the canonical
-- degreewise splitting family, which is the source-facing termwise-split conclusion.
/-- Lemma 13.26.8: given a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Fil^f(𝒜)` and prescribed
filtered quasi-isomorphisms from `A[0]` and `C[0]` into bounded-below complexes of filtered
injective objects, there exists a filtered horseshoe diagram whose lower row is termwise split
and whose outer comparison maps are exactly the prescribed maps. -/
theorem exists_filtered_horseshoe_diagram
    (S : ShortComplex FilF) (hS : S.ShortExact)
    {I J : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    (hτ₁ : QuasiIso (assocGraded.map a))
    (hτ₃ : QuasiIso (assocGraded.map c)) :
    ∃ (K : FiltInjPlus) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (φ : S.map single₀ ⟶ (ShortComplex.mk i p hip).map ιFiltInjPlus)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (ιFiltInjPlus ⋙ HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c := by
  sorry

-- Proof sketch: first build the horseshoe diagram from `exists_filtered_horseshoe_diagram`.
-- The degreewise splitting family implies short exactness of the lower row, so
-- `quasiIso_middle` applies to the resulting short-complex morphism and the prescribed outer
-- filtered quasi-isomorphisms.
/-- Companion consequence to Lemma 13.26.8: if the prescribed outer comparison maps are filtered
quasi-isomorphisms, then the horseshoe diagram can be chosen so that the middle comparison map is
also a filtered quasi-isomorphism. -/
theorem exists_filtered_horseshoe_diagram_of_outer_quasiIso
    (S : ShortComplex FilF) (hS : S.ShortExact)
    {I J : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    (hτ₁ : QuasiIso (assocGraded.map a))
    (hτ₃ : QuasiIso (assocGraded.map c)) :
    ∃ (K : FiltInjPlus) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (φ : S.map single₀ ⟶ (ShortComplex.mk i p hip).map ιFiltInjPlus)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (ιFiltInjPlus ⋙ HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c ∧
          QuasiIso (assocGraded.map φ.τ₂) := by
  sorry

end CochainComplex

end CategoryTheory
