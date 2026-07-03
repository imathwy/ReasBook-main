import Mathlib
import StacksProject_2024.Chap20.Definition_20_46_1
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u}}

/-- Restriction of `\mathcal O_X`-modules to an open subset is additive. -/
local instance moduleSheafRestrictionToOpen_additive (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).Additive := sorry

-- Proof sketch: represent the derived morphism by a roof `E → G ← F`, use Lemma `20.46.7`
-- locally to lift the map from the strictly perfect source through a quasi-isomorphism to an
-- actual morphism of restricted complexes, and then rewrite the resulting equality in the
-- restricted derived category via `mapDerivedCategoryFactors`.
/-- Lemma 20.46.8 (1): if `\mathcal E^\bullet` is strictly perfect, then every morphism
`\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` in `D(\mathcal O_X)` is locally represented
by a morphism of complexes after restricting to a suitable open neighborhood. -/
theorem exists_open_neighborhood_restriction_eq_Q_map_of_isStrictlyPerfect
    (E F : CochainComplex (RingedSpace.Modules X) ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      ∃ αU :
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E) ⟶
            (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F),
        ((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategory).map α =
          ((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategoryFactors.hom.app E) ≫
            DerivedCategory.Q.map αU ≫
            ((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategoryFactors.inv.app F) :=
  sorry

-- Proof sketch: the vanishing of `DerivedCategory.Q.map α` means the morphism of complexes
-- becomes zero in the derived category. Apply part `(1)` to the zero morphism and use the local
-- null-homotopy criterion from the strictly perfect case to conclude that the restricted map is
-- homotopic to zero on a neighborhood of each point.
/-- Lemma 20.46.8 (2): if `\mathcal E^\bullet` is strictly perfect and a morphism of complexes
`\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` becomes zero in `D(\mathcal O_X)`, then
after restricting to a suitable open neighborhood it is homotopic to zero. -/
theorem exists_open_neighborhood_homotopy_zero_of_Q_map_eq_zero_of_isStrictlyPerfect
    (E F : CochainComplex (RingedSpace.Modules X) ℤ) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hα : DerivedCategory.Q.map α = 0) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      Nonempty
        (Homotopy
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)
          0) := sorry

end AlgebraicGeometry.RingedSpace
