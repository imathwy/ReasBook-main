import Mathlib
import stacks_project.Chap20.Lemma_20_35_1

open Opposite
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ (ModuleCat A) AddCommGrpCat)]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)

/-- For fixed `n`, this is the inverse system `m ↦ H^p(X, I^n \mathcal F_{m+1})`, modeled by
the chosen tower `powSheaf n`. -/
abbrev topologicalSpaceModuleCohomologyIdealPowerTower
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf) (p n : ℕ) : ℕᵒᵖ ⥤ Type u :=
  (powSheaf n ⋙ topologicalSpaceModuleCohomologyFunctor p) ⋙ forget AddCommGrpCat

-- Proof sketch: unfold `topologicalSpaceModuleCohomologyIdealPowerTower`; evaluating at `op m`
-- just computes degree-`p` cohomology of the `m`-th stage of the chosen ideal-power tower.
/-- Evaluating the ideal-power cohomology tower at `op m` gives the degree-`p` cohomology of the
corresponding stage of `powSheaf n`. -/
theorem topologicalSpaceModuleCohomologyIdealPowerTower_obj
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf) (p n m : ℕ) :
    (topologicalSpaceModuleCohomologyIdealPowerTower powSheaf p n).obj (op m) =
      (topologicalSpaceModuleCohomologyFunctor p).obj ((powSheaf n).obj (op m)) := sorry

/-- For fixed `n`, this is the subgroup `N_n` from the source, encoded as the eventual range of
the tower `m ↦ H^{p+1}(X, I^n \mathcal F_{m+1})` at stage `n`. -/
abbrev topologicalSpaceModuleCohomologyIdealPowerEventualRange
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n : ℕ) : Set ((topologicalSpaceModuleCohomologyIdealPowerTower powSheaf (p + 1) n).obj
      (op n)) :=
  (topologicalSpaceModuleCohomologyIdealPowerTower powSheaf (p + 1) n).eventualRange (op n)

/-- The graded object `\bigoplus N_n` from the source, realized as the direct sum of the
eventual-range pieces. The additive structure on each graded piece is supplied explicitly as a
parameter when this construction is used. -/
abbrev topologicalSpaceIdealPowerEventualRangeDirectSum
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf) (p : ℕ)
    [∀ n : ℕ, AddCommMonoid (topologicalSpaceModuleCohomologyIdealPowerEventualRange powSheaf p n)] :
    Type u :=
  DirectSum ℕ fun n ↦ topologicalSpaceModuleCohomologyIdealPowerEventualRange powSheaf p n

-- Proof sketch: argue exactly as in Lemma `20.35.1`, replacing the full graded cohomology direct
-- sum by the graded submodule `⊕ N_n` of eventual ranges. The boundary maps land in `N_n`, and
-- multiplication by classes in `I^k / I^{k+1}` sends `N_n` into `N_{n+k}`; the Noetherian
-- hypothesis then forces stabilization of the images in the cohomology tower.
/-- Lemma 20.35.2: let `I` be an ideal of a ring `A`, let `X` be a topological space, and let
`(\mathcal F_n)_n` be a sequential inverse system of sheaves of `A`-modules on `X`. For each
`n`, let `powSheaf n` model the inverse system `m ↦ I^n \mathcal F_{m+1}` and write
`N_n = topologicalSpaceModuleCohomologyIdealPowerEventualRange powSheaf p n`, so that `N_n` is
the intersection of the images of the maps
`H^{p+1}(X, I^n \mathcal F_{m+1}) → H^{p+1}(X, I^n \mathcal F_{n+1})` for `m ≥ n`. Assume the
short exact sequences `0 → I^n \mathcal F_{m+1} → \mathcal F_{m+1} → \mathcal F_n → 0` are
encoded by `ses`, and assume the graded direct sum `\bigoplus N_n` is Noetherian over the
associated graded ring `\bigoplus_{n \ge 0} I^n / I^{n+1}`. Then the inverse system
`M_n = H^p(X, \mathcal F_n)` satisfies the Mittag-Leffler condition `2`, expressed here by the
standard categorical predicate `IsMittagLeffler`. -/
theorem topologicalSpace_moduleCohomologyTower_isMittagLeffler_of_idealPower_eventualRange_ascending_chain_condition
    (I : Ideal A)
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (ses : ∀ n m : ℕ, n ≤ m → ShortComplex ModSheaf)
    (hses : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).ShortExact)
    (ses_left_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₁ ≅ (powSheaf n).obj (op m))
    (ses_middle_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₂ ≅ ℱ.obj (op (m + 1)))
    (ses_right_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₃ ≅ ℱ.obj (op n))
    (p : ℕ)
    [∀ n : ℕ, AddCommMonoid (topologicalSpaceModuleCohomologyIdealPowerEventualRange powSheaf p n)]
    [Module (idealAssociatedGradedRing I) (topologicalSpaceIdealPowerEventualRangeDirectSum powSheaf p)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (topologicalSpaceIdealPowerEventualRangeDirectSum powSheaf p)] :
    ((topologicalSpaceModuleCohomologyTower ℱ p) ⋙ forget AddCommGrpCat).IsMittagLeffler := sorry

end

end CategoryTheory
