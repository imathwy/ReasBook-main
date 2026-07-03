import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap13.Lemma_13_23_6
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap21.Situation_21_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open CategoryTheory.GrothendieckTopology
open DerivedCategory.TStructure

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

variable (X : RingedSite.{u, v})
variable [HasWeakSheafify X.siteTopology AddCommGrpCat]
variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat]

local notation "ModX" => RingedSiteModuleCat X

variable [Abelian ModX]
variable [CategoryWithHomology ModX]
variable [IsGrothendieckAbelian ModX]

variable (A : ObjectProperty ModX)
variable [A.ContainsZero] [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels]
variable [A.IsClosedUnderExtensions]

-- Proof sketch: use the bounded-cohomology basis from Situation `21.25.1` to reduce to basis
-- objects with uniformly bounded higher cohomology for `A`-valued sheaves. For a fixed degree `j`
-- and basis object `V`, compare the spectral sequences computing `H^*(V, K_n)` from the
-- cohomology sheaves `H^q(K_n)`; bounded-below hypotheses and eventual constancy of the
-- cohomology sheaves force the groups `H^(j-1)(V, K_n)` and `H^j(V, K_n)` to stabilize. Lemma
-- `21.23.6` then gives injectivity of the Milnor comparison map on the cohomology sheaf of
-- `R lim K_n`, and Lemmas `21.20.3` and `21.23.2` give surjectivity after passing to a covering,
-- yielding the claimed identification of cohomology sheaves.
/-- Lemma 21.25.3: in Situation `21.25.1`, let `(K_n)` be a sequential inverse system in
`D^+_\mathcal A(\mathcal O_X)` and let `K` be a derived limit of this tower. If for every degree
`j` the cohomology sheaves `H^j(K_n)` all lie in `\mathcal A` and are eventually constant with
eventual value `ℋ j`, then the degree-`j` cohomology sheaf of `K = R \!\varprojlim_n K_n` is
isomorphic to `ℋ j`. -/
lemma derivedLimit_cohomology_isomorphic_of_eventually_constant
    (basis : bounded_cohomology_basis X.structureSheaf A)
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory ModX)
    (K : DerivedCategory ModX)
    (ℋ : ℤ → ModX)
    (hK : IsDerivedLimit Ksys K)
    (hboundedBelow : ∀ n : ℕ,
      (t.plus : ObjectProperty (DerivedCategory ModX)) (Ksys.obj (op n)))
    (hcohomology_mem : ∀ n : ℕ, ∀ j : ℤ,
      A ((DerivedCategory.homologyFunctor ModX j).obj (Ksys.obj (op n))))
    (hℋ_mem : ∀ j : ℤ, A (ℋ j))
    (heventually_constant : ∀ j : ℤ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsIsomorphic
        ((DerivedCategory.homologyFunctor ModX j).obj (Ksys.obj (op n)))
        (ℋ j)) :
    ∀ j : ℤ, IsIsomorphic ((DerivedCategory.homologyFunctor ModX j).obj K) (ℋ j) := sorry

end
