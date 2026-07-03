import Mathlib
import stacks_project.Chap20.Lemma_20_35_2
import stacks_project.Chap20.Lemma_20_35_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
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

/-- For fixed `n`, this is the subgroup `N_n` from the source in degree `p`, encoded as the
eventual range of the tower `m ↦ H^p(X, I^n \mathcal F_{m+1})` at stage `n`. -/
abbrev topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n : ℕ) : Set ((topologicalSpaceModuleCohomologyIdealPowerTower powSheaf p n).obj (op n)) :=
  (topologicalSpaceModuleCohomologyIdealPowerTower powSheaf p n).eventualRange (op n)

/-- The graded object `\bigoplus N_n` from the source, realized as the direct sum of the
degree-`p` eventual-range pieces. The additive structure on each graded piece is supplied
explicitly when this construction is used. -/
abbrev topologicalSpaceIdealPowerEventualRangeDirectSumAtDegree
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf) (p : ℕ)
    [∀ n : ℕ, AddCommMonoid
      (topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree powSheaf p n)] :
    Type u :=
  DirectSum ℕ fun n ↦ topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree powSheaf p n

-- Proof sketch: use the abstract topology statement of Lemma `20.35.3` with
-- `cohomologySystem` modeling `H^p(X, \mathcal F_n)` as `A`-modules. The proof from the source
-- shows that the degree-`p` eventual ranges `N_n` form a graded submodule of
-- `⊕_n H^p(X, I^n \mathcal F_{n+1})` and that the successive quotients of the kernel filtration on
-- `lim_n H^p(X, \mathcal F_n)` are controlled by the images of the `N_n`; the Noetherian
-- hypothesis on `⊕_n N_n` then forces the inverse-limit topology to agree with the `I`-adic
-- topology.
/-- Lemma 20.35.4: let `I` be an ideal of a ring `A`, let `X` be a topological space, and let
`(\mathcal F_n)_n` be an inverse system of sheaves of `A`-modules on `X` such that
`\mathcal F_n = \mathcal F_{n + 1} / I^n \mathcal F_{n + 1}`. Let `cohomologySystem` model the
inverse system `n ↦ H^p(X, \mathcal F_n)` as `A`-modules, and for each `n` let
`N_n = topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree powSheaf p n`, where
`powSheaf n` models the tower `m ↦ I^n \mathcal F_{m + 1}`. If the graded direct sum
`\bigoplus N_n` satisfies the ascending chain condition over the associated graded ring
`\bigoplus_{n \ge 0} I^n / I^{n + 1}`, then the inverse-limit topology on
`M = \lim_n H^p(X, \mathcal F_n)` is the `I`-adic topology. -/
theorem topologicalSpace_moduleCohomology_inverseLimitTopology_eq_adicModuleTopology_of_idealPower_eventualRange_ascending_chain_condition
    (I : Ideal A)
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (p : ℕ)
    (cohomologySystemIso :
      cohomologySystem ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat ≅
        topologicalSpaceModuleCohomologyTower ℱ p)
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (ses : ∀ n m : ℕ, n ≤ m → ShortComplex ModSheaf)
    (hses : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).ShortExact)
    (ses_left_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₁ ≅ (powSheaf n).obj (op m))
    (ses_middle_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₂ ≅ ℱ.obj (op (m + 1)))
    (ses_right_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₃ ≅ ℱ.obj (op n))
    [∀ n : ℕ, AddCommMonoid
      (topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree powSheaf p n)]
    [Module (_root_.idealAssociatedGradedRing I)
      (topologicalSpaceIdealPowerEventualRangeDirectSumAtDegree powSheaf p)]
    [IsNoetherian (_root_.idealAssociatedGradedRing I)
      (topologicalSpaceIdealPowerEventualRangeDirectSumAtDegree powSheaf p)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I ↥(limit cohomologySystem) := sorry

end

end CategoryTheory
