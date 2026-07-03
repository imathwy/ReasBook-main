import Mathlib
import StacksProject_2024.Chap13.Definition_13_37_1
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [CompactSpace X.carrier] [PrespectralSpace X.carrier] [QuasiSeparatedSpace X.carrier]
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} (RingedSpace.Modules X)]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "ιPlus" =>
  ObjectProperty.ι (fun M : DMod ↦ ∃ n : ℤ, DerivedCategory.IsGE M n)

-- Proof sketch: let `Kᵛ` be the derived dual of `K` from Lemma `20.50.5`. For bounded-below
-- objects, the functor `- ⊗^L Kᵛ` preserves arbitrary direct sums, and Lemma `20.19.1` together
-- with Lemma `20.53.1` shows that `RΓ(X, -)` preserves those same direct sums under the stated
-- topological hypotheses. The identification
-- `Hom_{D(\mathcal O_X)}(K, M) ≅ H^0(X, Kᵛ ⊗^L M)` then gives preservation of coproducts by
-- `Hom(K, -)` on `D^+(\mathcal O_X)`.
/-- Lemma 20.53.2 (1): if the underlying topological space of the ringed space `X` is
quasi-compact, has a basis of quasi-compact opens, and intersections of quasi-compact opens are
quasi-compact, then for a perfect object `K` of `D(\mathcal O_X)` the functor
`Hom_{D(\mathcal O_X)}(K, -)` preserves arbitrary direct sums on the bounded-below derived
subcategory `D^+(\mathcal O_X)`. -/
theorem perfect_preserves_boundedBelowCoproducts
    (K : DMod) (hK : DerivedCategory.IsPerfect K) (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (ιPlus ⋙ preadditiveCoyoneda.obj (op K)) := sorry

-- Proof sketch: apply part `(1)` to reduce compactness to the preservation of direct sums by
-- `RΓ(X, -)` on all of `D(\mathcal O_X)`. The finite cohomological-dimension hypothesis is
-- exactly the input needed in Lemma `20.53.1` for the top open `U = X`, which upgrades the
-- bounded-below compactness statement to the full compact-object statement in the derived
-- category.
/-- Lemma 20.53.2 (2): under the same topological hypotheses, if there exists an integer `d` such
that `H^i(X, \mathcal F) = 0` for all `i > d` and all `\mathcal O_X`-modules `\mathcal F`, then
every perfect object `K` of `D(\mathcal O_X)` is a compact object of `D(\mathcal O_X)`. -/
theorem perfect_isCompactObject_of_finiteCohomologicalDimension
    (K : DMod) (hK : DerivedCategory.IsPerfect K)
    (hcd :
      ∃ d : ℤ,
        ∀ (p : ℕ), d < p → ∀ ℱ : (RingedSpace.Modules X),
          IsZero (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).H' p
            (⊤ : Opens X.carrier))) :
    CategoryTheory.IsCompactObject K := sorry

end

end AlgebraicGeometry.RingedSpace
