import Mathlib
import StacksProject_2024.Chap20.Definition_20_46_1
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

-- Proof sketch: for each point `x`, restrict to a sufficiently small open neighborhood `U`
-- where the finite free summands appearing in the strictly perfect complex split termwise. On
-- `U`, boundedness plus the acyclicity of the target implies the restricted source complex is
-- K-projective, so the restricted morphism is homotopic to zero.
/-- Lemma 20.46.6 (1): if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` is a morphism of
complexes of `\mathcal O_X`-modules with `\mathcal E^\bullet` strictly perfect and
`\mathcal F^\bullet` acyclic, then `\alpha` is locally on `X` homotopic to zero. -/
theorem exists_open_neighborhood_homotopy_zero_of_isStrictlyPerfect_of_acyclic
    (E F : CochainComplex (RingedSpace.Modules X) ℤ) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E) (hF : F.Acyclic) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      Nonempty
        (Homotopy
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)
          0) := sorry

-- Proof sketch: work by induction on the length of the strictly perfect complex `E`. For the
-- top nonzero degree, `H^i(F^\bullet)=0` for `i ≥ a` makes the cocycle sheaf a local quotient of
-- the previous term, so Lemma `20.46.5` gives a local null-homotopy on the top summand. Removing
-- that degree yields a shorter strictly perfect complex, and the induction closes.
/-- Lemma 20.46.6 (2): if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` is a morphism of
complexes of `\mathcal O_X`-modules with `\mathcal E^\bullet` strictly perfect,
`\mathcal E^i = 0` for `i < a`, and `H^i(\mathcal F^\bullet) = 0` for `i \ge a`, then
`\alpha` is locally on `X` homotopic to zero. -/
theorem exists_open_neighborhood_homotopy_zero_of_isStrictlyPerfect_of_isStrictlyGE_of_homology_isZero
    [CategoryWithHomology (RingedSpace.Modules X)]
    (E F : CochainComplex (RingedSpace.Modules X) ℤ) (α : E ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      Nonempty
        (Homotopy
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)
          0) := sorry

end AlgebraicGeometry.RingedSpace
