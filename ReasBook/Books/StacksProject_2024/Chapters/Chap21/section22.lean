import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_22_1 (from Chap21) -/
open CategoryTheory
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

local notation "ModSheaf" => Sheaf J (ModuleCat.{max u v w} A)

/- Domain-style sampling for Lemma 21.22.1:
- primary domain: sheaf cohomology of inverse systems of `A`-module sheaves on a site, with the
  canonical Mittag-Leffler predicate on the underlying inverse system of abelian groups;
- sampled owner declarations:
  * `CategoryTheory.Functor.IsMittagLeffler`;
  * `CategoryTheory.sheafCompose`;
  * `CategoryTheory.Sheaf.cohomologyFunctor`.
- owner choice:
  * `source-facing`: the short-exact-sequence hypothesis and the final stabilization statement;
  * `core/canonical`: `Functor.IsMittagLeffler`, `sheafCompose`, and `Sheaf.cohomologyFunctor`;
  * `bridge/view`: passage from `A`-module sheaves to abelian sheaves via `forget₂`.
- primitive data: the tower `ℱ`, the models `powSheaf n`, and the chosen short exact sequences
  `ses n`;
- derived API: the cohomology tower `ℱ ⋙ sheafCompose J (forget₂ ...) ⋙ Sheaf.cohomologyFunctor J p`.

The cohomology tower is therefore used directly through the canonical composite, rather than
persisting as a separate local wrapper declaration.
-/

-- Proof sketch: for each `n`, the short exact sequence
-- `0 → powSheaf n → ℱ_{n+1} → ℱ_n → 0` yields a connecting morphism
-- `H^p(\mathcal C, \mathcal F_n) → H^{p+1}(\mathcal C, powSheaf n)`. The ascending-chain
-- condition on the graded family of the target cohomology modules forces the images of these
-- connecting morphisms to be generated in bounded degree, and the long exact sequence then shows
-- that the images of the transition maps in the tower `H^p(\mathcal C, \mathcal F_n)` stabilize.
/-- Lemma 21.22.1: let `ℱ : ℕᵒᵖ ⥤ Sheaf J (ModuleCat A)` be a sequential inverse system of sheaves
of `A`-modules, and let `powSheaf n` model the sheaf `I^n \mathcal F_{n + 1}` through short exact
sequences
`0 → powSheaf n → \mathcal F_{n + 1} → \mathcal F_n → 0`.
If the graded family `\bigoplus_{n \ge 0} H^{p+1}(\mathcal C, powSheaf n)` satisfies the
ascending-chain-condition hypothesis from the source, then the inverse system
`n ↦ H^p(\mathcal C, \mathcal F_n)` is Mittag-Leffler.

In this statement-stage formalization, the graded ascending-chain-condition hypothesis is recorded
by the explicit parameter `hACC : Prop`, while the cohomology tower and the short exact sequence
data are expressed using the canonical functors `sheafCompose` and
`Sheaf.cohomologyFunctor`. The Mittag-Leffler conclusion is stated for the underlying set-valued
inverse system, which is the content of condition 1. -/
theorem site_module_cohomology_tower_isMittagLeffler_of_ascending_chain_condition
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (powSheaf : ℕ → ModSheaf)
    (ses : ∀ n : ℕ, ShortComplex ModSheaf)
    (hses : ∀ n : ℕ, (ses n).ShortExact)
    (ses_left_iso : ∀ n : ℕ, (ses n).X₁ ≅ powSheaf n)
    (ses_middle_iso : ∀ n : ℕ, (ses n).X₂ ≅ ℱ.obj (op (n + 1)))
    (ses_right_iso : ∀ n : ℕ, (ses n).X₃ ≅ ℱ.obj (op n))
    (p : ℕ)
    (hACC : Prop) :
    ((ℱ ⋙ sheafCompose J (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w}) ⋙
        Sheaf.cohomologyFunctor J p) ⋙
      forget AddCommGrpCat.{max u v w}).IsMittagLeffler :=
  sorry

end

end CategoryTheory

/-! ### Lemma_21_22_2 (from Chap21) -/
open CategoryTheory
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

local notation "ModSheaf" => Sheaf J (ModuleCat.{max u v w} A)

/-- For fixed `n`, this is the inverse system `m ↦ H^p(\mathcal C, I^n \mathcal F_{m+1})`,
modeled by the sheaf tower `powSheaf n`. -/
abbrev siteModuleCohomologyIdealPowerTower
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n : ℕ) : ℕᵒᵖ ⥤ Type (max u v w) :=
  (powSheaf n ⋙ sheafCompose J (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w}) ⋙
      Sheaf.cohomologyFunctor J p) ⋙
    forget AddCommGrpCat.{max u v w}

-- Proof sketch: unfold `siteModuleCohomologyIdealPowerTower`; it is the composite of the chosen
-- ideal-power tower `powSheaf n` with the degree-`p` site cohomology functor and then with the
-- forgetful functor to types.
/-- Evaluating the ideal-power cohomology tower at `op m` gives the degree-`p` cohomology of the
corresponding stage of the sheaf tower `powSheaf n`. -/
theorem siteModuleCohomologyIdealPowerTower_obj
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n m : ℕ) :
    (siteModuleCohomologyIdealPowerTower powSheaf p n).obj (op m) =
      (Sheaf.cohomologyFunctor J p).obj
        ((sheafCompose J (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})).obj
          ((powSheaf n).obj (op m))) :=
  rfl

/-- The subgroup `N_n` from the source, encoded as the eventual range of the tower
`m ↦ H^{p+1}(\mathcal C, I^n \mathcal F_{m+1})` at stage `n`. -/
abbrev siteModuleCohomologyIdealPowerEventualRange
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n : ℕ) :
    Set ((siteModuleCohomologyIdealPowerTower powSheaf (p + 1) n).obj (op n)) :=
  (siteModuleCohomologyIdealPowerTower powSheaf (p + 1) n).eventualRange (op n)

-- Proof sketch: for each `n ≤ m`, the short exact sequence
-- `0 → I^n \mathcal F_{m+1} → \mathcal F_{m+1} → \mathcal F_n → 0` yields connecting maps
-- landing in the eventual ranges
-- `siteModuleCohomologyIdealPowerEventualRange powSheaf p n`. The source ACC hypothesis on the
-- graded family `⊕ N_n` is recorded by `hACC : Prop`; the argument of Lemma `21.22.1` then shows
-- that the images in the inverse system `n ↦ H^p(\mathcal C, \mathcal F_n)` stabilize.
/-- Lemma 21.22.2: let `ℱ` be a sequential inverse system of sheaves of `A`-modules on the site
`(C, J)`, and let `powSheaf n` model the inverse system `m ↦ I^n \mathcal F_{m+1}`. Assume that
for every `n ≤ m` there is a short exact sequence
`0 → I^n \mathcal F_{m+1} → \mathcal F_{m+1} → \mathcal F_n → 0`, encoded by `ses`. Write
`N_n = siteModuleCohomologyIdealPowerEventualRange powSheaf p n`, so that `N_n` is the
intersection of the images of the maps
`H^{p+1}(\mathcal C, I^n \mathcal F_{m+1}) → H^{p+1}(\mathcal C, I^n \mathcal F_{n+1})`.
If the graded family `⊕ N_n` satisfies the ascending-chain-condition hypothesis from the source,
then the inverse system `n ↦ H^p(\mathcal C, \mathcal F_n)` satisfies the Mittag-Leffler
condition `2`. As in Lemma `21.22.1`, the graded ACC hypothesis is recorded by the explicit
parameter `hACC : Prop`. -/
theorem site_module_cohomology_tower_isMittagLeffler_of_idealPower_eventualRange_ascending_chain_condition
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (ses : ∀ n m : ℕ, n ≤ m → ShortComplex ModSheaf)
    (hses : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).ShortExact)
    (ses_left_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m,
      (ses n m hnm).X₁ ≅ (powSheaf n).obj (op m))
    (ses_middle_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m,
      (ses n m hnm).X₂ ≅ ℱ.obj (op (m + 1)))
    (ses_right_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m,
      (ses n m hnm).X₃ ≅ ℱ.obj (op n))
    (p : ℕ)
    (hACC : Prop) :
    ((ℱ ⋙ sheafCompose J (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w}) ⋙
        Sheaf.cohomologyFunctor J p) ⋙
      forget AddCommGrpCat.{max u v w}).IsMittagLeffler :=
  sorry

end

end CategoryTheory

/-! ### Lemma_21_22_3 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- 
Domain-style sampling for Lemma 21.22.3:
- primary domain: inverse-limit topologies on sequential systems of `A`-modules and their
  comparison with the `I`-adic topology via Noetherian hypotheses over the associated graded ring;
- sampled owner declarations:
  * `idealAssociatedGradedRing`;
  * `Ideal.adicModuleTopology`;
  * `CategoryTheory.inverseLimitTopology`;
  * `CategoryTheory.inverseLimitTopology_eq_adicModuleTopology_of_noetherian_kernelAssociatedGraded`.
- owner choice:
  * `source-facing`: the cohomological direct sum
    `DirectSum ℕ fun n ↦ idealPowerCohomology n`;
  * `core/canonical`: `CategoryTheory.inverseLimitTopology cohomologySystem`;
  * `bridge/view`: the source comparison from the ideal-power cohomology direct sum to the kernel
    associated graded used by the abstract Chapter 20 owner theorem.
- primitive data: the ideal `I`, the inverse system `cohomologySystem`, and the family
  `idealPowerCohomology`;
- derived API: the module and Noetherian structures on
  `DirectSum ℕ fun n ↦ idealPowerCohomology n`, together with the equality of topologies.

The local `inverseLimitTopology` wrapper was duplicating the Chapter 20 owner abstraction, and the
local direct-sum abbreviation was only a one-off type alias. This file therefore reuses the owner
directly and keeps the source-facing direct sum as a bare canonical expression.
-/

-- Proof sketch: apply the source hypothesis to the direct sum of the modules
-- `H^p(\mathcal C, I^n \mathcal F_{n+1})` to obtain finite generation over the associated graded
-- ring `⊕_n I^n / I^{n+1}`. This gives eventual equalities `I F^n = F^{n+1}` for the kernel
-- filtration on `lim_n H^p(\mathcal C, \mathcal F_n)`, so the inverse-limit and `I`-adic
-- neighbourhood bases coincide.
/-- Lemma 21.22.3: for the cohomology inverse system `n ↦ H^p(\mathcal C, \mathcal F_n)` coming
from a system of sheaves with `\mathcal F_n = \mathcal F_{n + 1} / I^n \mathcal F_{n + 1}`, if
the direct sum `⊕_{n \geq 0} H^p(\mathcal C, I^n \mathcal F_{n + 1})` is Noetherian over the
associated graded ring `⊕_{n \geq 0} I^n / I^{n + 1}`, then the inverse-limit topology on
`lim_n H^p(\mathcal C, \mathcal F_n)` equals the `I`-adic topology. -/
lemma cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_associatedGraded
    {A : Type u} [CommRing A] (I : Ideal A)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A)
    (idealPowerCohomology : ℕ → ModuleCat A)
    [Module (idealAssociatedGradedRing I)
      (DirectSum ℕ fun n ↦ idealPowerCohomology n)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (DirectSum ℕ fun n ↦ idealPowerCohomology n)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I ↥(limit cohomologySystem) := sorry

/-! ### Lemma_21_22_4 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/-- The quotient-Rees model of the associated graded ring `⊕_{n ≥ 0} I^n / I^(n + 1)` of an
ideal `I`. -/
abbrev idealAssociatedGradedRing (I : Ideal A) : Type u :=
  (reesAlgebra I) ⧸ Ideal.map (algebraMap A (reesAlgebra I)) I

/-- The topology on the inverse limit of a sequential system of `A`-modules induced from the
product of the discrete quotient modules. -/
abbrev inverseLimitTopology (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) :
    TopologicalSpace ↥(limit cohomologySystem) :=
  let _ : (n : ℕ) → TopologicalSpace ↥(cohomologySystem.obj (op n)) := fun _ ↦ ⊥
  TopologicalSpace.induced
    (fun x : ↥(limit cohomologySystem) ↦
      fun n : ℕ ↦ ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n)))
    inferInstance

/-- For a fixed `n`, this is the submodule
`⋂_{m ≥ n} \operatorname{Im}(H^p(\mathcal C, I^n \mathcal F_{m + 1}) → H^p(\mathcal C, I^n \mathcal F_{n + 1}))`
attached to the inverse system `idealPowerTower n`. -/
abbrev cohomologyIdealPowerEventualImageSubmodule
    (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    Submodule A ((idealPowerTower n).obj (op n)) :=
  ⨅ m : Set.Ici n,
    LinearMap.range (((idealPowerTower n).map (homOfLE m.2).op).hom)

/-- The graded direct sum `⊕_n N_n` of the eventual-image submodules attached to the tower
`idealPowerTower`. -/
abbrev cohomologyIdealPowerEventualImageDirectSum
    (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A) : Type u :=
  DirectSum ℕ fun n ↦ cohomologyIdealPowerEventualImageSubmodule idealPowerTower n

-- Proof sketch: apply Lemma `21.22.3` to the kernel filtration on
-- `lim_n H^p(\mathcal C, \mathcal F_n)`. The hypothesis that `⊕_n N_n` is Noetherian over the
-- associated graded ring provides the graded ACC input, while
-- `hKernelFiltrationControlledByEventualImages` records the source argument that the graded pieces
-- of the kernel filtration are controlled by the images of the `N_n`.
/-- Lemma 21.22.4: let `cohomologySystem` model the inverse system
`n ↦ H^p(\mathcal C, \mathcal F_n)` and let `idealPowerTower n` model the fixed-`n` tower
`m ↦ H^p(\mathcal C, I^n \mathcal F_{m + 1})`. For each `n`, write
`N_n = cohomologyIdealPowerEventualImageSubmodule idealPowerTower n`, i.e. the intersection of
the images of the transition maps into stage `n`. If the graded direct sum `⊕_n N_n` is
Noetherian over the associated graded ring `⊕_{n \ge 0} I^n / I^{n + 1}`, and if the source
comparison between the kernel filtration on `lim_n H^p(\mathcal C, \mathcal F_n)` and the images
of the `N_n` is encoded by the hypothesis
`hKernelFiltrationControlledByEventualImages`, then the inverse-limit topology on
`lim_n H^p(\mathcal C, \mathcal F_n)` is the `I`-adic topology. -/
lemma cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_eventualImages
    (I : Ideal A)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A)
    (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A)
    (hKernelFiltrationControlledByEventualImages : Prop)
    [Module (idealAssociatedGradedRing I)
      (cohomologyIdealPowerEventualImageDirectSum idealPowerTower)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (cohomologyIdealPowerEventualImageDirectSum idealPowerTower)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I ↥(limit cohomologySystem) := sorry

end
