import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical closed-subscheme owner
-- `Scheme.IdealSheafData` together with `Scheme.IdealSheafData.support`,
-- `Scheme.IdealSheafData.range_subschemeι`, `IsClosedImmersion.lift`, and
-- `StableUnderGeneralization`. The source-facing statements below therefore keep the Stacks item
-- on ideal-sheaf-defined closed subschemes and their underlying closed subsets.

/-- A flat closed subscheme has underlying closed subset stable under generalizations. -/
theorem stableUnderGeneralization_support_of_flat_subscheme
    {X : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) :
    StableUnderGeneralization (I.support : Set X) := sorry

/-- Lemma 29.26.1 (1): for a scheme `X`, sending a flat closed subscheme of `X` to its
underlying closed subset defines a bijection from flat closed subschemes of `X` to closed subsets
of `X` that are closed under generalizations. -/
@[stacks 04PW]
theorem flat_closed_subscheme_support_bijective
    (X : Scheme.{u}) :
    Function.Bijective
      (fun I : { I : X.IdealSheafData // Flat I.subschemeι } ↦
        (⟨I.1.support, stableUnderGeneralization_support_of_flat_subscheme I.1 I.2⟩ :
          { Z : TopologicalSpace.Closeds X // StableUnderGeneralization (Z : Set X) })) := sorry

/-- Lemma 29.26.1 (2): if `I` is a flat closed subscheme of `X`, then every morphism of schemes
`g : Y ⟶ X` whose set-theoretic image is contained in the underlying closed subset of `I`
factors scheme-theoretically through `I`. -/
@[stacks 04PW]
theorem exists_factor_through_flat_closed_subscheme_of_range_subset
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) (g : Y ⟶ X)
    (hg : Set.range ⇑(ConcreteCategory.hom g.base) ⊆ (I.support : Set X)) :
    ∃ g' : Y ⟶ I.subscheme, g' ≫ I.subschemeι = g := sorry

end AlgebraicGeometry
