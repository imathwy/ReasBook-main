import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_22_1

open Opposite
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace CategoryTheory

section

variable {T : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat)]
variable [(Opens.grothendieckTopology T).HasSheafCompose
  (forget₂ (ModuleCat A) AddCommGrpCat)]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology T) (ModuleCat A)

/- Domain-style sampling for Lemma 20.35.1:
- primary domain: sheaf cohomology of inverse systems of `A`-module sheaves on the site
  `Opens.grothendieckTopology T`, together with the graded `gr_I(A)`-module
  `⨁ n, H^{p+1}(T, I^n ℱ_{n+1})` from the source statement;
- sampled owner declarations:
  * `siteModuleCohomologyFunctor`;
  * `siteModuleCohomologyTower`;
  * `idealPowerCohomologyPiece`;
  * `siteModuleCohomologyTower_isMittagLeffler_of_noetherian_associatedGraded`.
- source/core/bridge triage:
  * `source-facing`: the full graded direct sum
    `⨁ n, H^{p+1}(T, I^n ℱ_{n+1})` and the resulting Mittag-Leffler statement for
    `n ↦ H^p(T, ℱ_n)`;
  * `core/canonical`: the Chapter 21 owners `siteModuleCohomologyTower`,
    `idealPowerCohomologyPiece`, and
    `siteModuleCohomologyTower_isMittagLeffler_of_noetherian_associatedGraded`;
  * `bridge/view`: the source proof step that `⊕_n im(δ_n)` is a graded submodule of the full
    cohomology direct sum, so Noetherianity of the latter transfers to the owner theorem's
    boundary-image hypothesis.
- primitive data: the ideal `I`, the inverse system `ℱ`, the chosen models `idealPowerSheaf n`
  for `I^n ℱ_{n + 1}`, the maps `idealPowerι n`, and the short exact rows
  `idealPowerRow ℱ idealPowerSheaf idealPowerι idealPower_comp_zero n`;
- derived API: the degree-`n` cohomology pieces `idealPowerCohomologyPiece idealPowerSheaf p n`,
  the canonical tower `siteModuleCohomologyTower ℱ p`, the owner boundary-image direct sum
  `idealPowerConnectingDirectSum ...`, and the Mittag-Leffler conclusion.

The public statement in this file must therefore remain source-facing: the source hypothesis is
Noetherianity of the full graded cohomology direct sum, not merely of the smaller direct sum of
boundary images used in the Chapter 21 owner theorem.
-/

/- Lemma 20.35.1 uses the canonical degree-`p` site cohomology functor on sheaves of `A`-modules
on `Opens.grothendieckTopology T`. -/
recall siteModuleCohomologyFunctor

/- Lemma 20.35.1 uses the canonical inverse system `n ↦ H^p(T, ℱ_n)`, formalized by the
site-level owner `siteModuleCohomologyTower`. -/
recall siteModuleCohomologyTower

/- The source hypothesis is expressed using the canonical degree-`n` term
`H^{p+1}(T, I^n ℱ_{n+1})`, formalized by `idealPowerCohomologyPiece`. -/
recall idealPowerCohomologyPiece

/-- The source full graded cohomology object
`⨁ n, H^{p + 1}(T, I^n ℱ_{n + 1})`, before passing to the boundary-image subobject
used by the Chapter 21 owner theorem. -/
abbrev idealPowerCohomologyDirectSum
    (idealPowerSheaf : ℕ → ModSheaf) (p : ℕ) : Type u :=
  ⨁ n : ℕ, idealPowerCohomologyPiece idealPowerSheaf p n

/-- The degree-`n` homogeneous subgroup of the source full cohomology direct sum
`idealPowerCohomologyDirectSum idealPowerSheaf p`. -/
abbrev idealPowerCohomologyGrading
    (idealPowerSheaf : ℕ → ModSheaf) (p n : ℕ) :
    AddSubgroup (idealPowerCohomologyDirectSum idealPowerSheaf p) :=
  AddMonoidHom.range
    (DirectSum.of
      (fun n ↦ idealPowerCohomologyPiece idealPowerSheaf p n)
      n)

/-- The source full cohomology direct sum inherits its scalar action from any ambient
`idealAssociatedGradedRing I`-module structure. This keeps the source-facing theorem inferable
without adding a redundant explicit `SMul` hypothesis. -/
instance idealPowerCohomologyDirectSum_smul
    (I : Ideal A) (idealPowerSheaf : ℕ → ModSheaf) (p : ℕ)
    [hModule : Module (idealAssociatedGradedRing I)
      (idealPowerCohomologyDirectSum idealPowerSheaf p)] :
    SMul (idealAssociatedGradedRing I)
      (idealPowerCohomologyDirectSum idealPowerSheaf p) :=
  hModule.toSMul

/-- The Chapter 21 boundary-image direct sum `⨁ n, im(δ_n)` sits canonically inside the full
source direct sum `⨁ n, H^{p + 1}(T, I^n ℱ_{n + 1})`. This is the concrete bridge used
to transfer the source Noetherian hypothesis to the owner theorem on boundary images. -/
def idealPowerConnectingDirectSumToCohomologyDirectSum
    (ℱ : SequentialInverseSystem ModSheaf) (idealPowerSheaf : ℕ → ModSheaf) (p : ℕ)
    (δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n))) :
    idealPowerConnectingDirectSum ℱ idealPowerSheaf p δ →+
      idealPowerCohomologyDirectSum idealPowerSheaf p :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (fun n ↦ idealPowerCohomologyPiece idealPowerSheaf p n) n).comp
      (idealPowerConnectingRange ℱ idealPowerSheaf p δ n).subtype

@[simp] theorem idealPowerConnectingDirectSumToCohomologyDirectSum_of
    (ℱ : SequentialInverseSystem ModSheaf) (idealPowerSheaf : ℕ → ModSheaf) (p n : ℕ)
    (δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n)))
    (x : idealPowerConnectingRange ℱ idealPowerSheaf p δ n) :
    idealPowerConnectingDirectSumToCohomologyDirectSum ℱ idealPowerSheaf p δ
        (DirectSum.of
          (fun n ↦ idealPowerConnectingRange ℱ idealPowerSheaf p δ n)
          n x) =
      DirectSum.of (fun n ↦ idealPowerCohomologyPiece idealPowerSheaf p n) n x.1 :=
  by
    simp [idealPowerConnectingDirectSumToCohomologyDirectSum]

/-- Lemma 20.35.1: let `I` be an ideal of `A`, let `ℱ` be a sequential inverse system of sheaves
of `A`-modules on `T`, and suppose `idealPowerSheaf n` models `I^n ℱ_{n + 1}` with short exact
rows `0 → I^n ℱ_{n + 1} → ℱ_{n + 1} → ℱ_n → 0`.
If the graded direct sum `⨁ n, H^{p + 1}(T, I^n ℱ_{n + 1})`, formalized by
`idealPowerCohomologyDirectSum idealPowerSheaf p`, is Noetherian over the associated graded ring
`⨁ n, I^n / I^{n + 1}` and its grading is compatible with that action, then the cohomology tower
`n ↦ H^p(T, ℱ_n)`, formalized by `siteModuleCohomologyTower ℱ p`,
satisfies the Mittag-Leffler condition. This is the source-facing topological-space form of the
Stacks statement. The Chapter 21 owner theorem is used only after the internal bridge step that
the graded boundary-image direct sum `⊕_n im(δ_n)` inherits the needed `gr_I(A)`-module
structure and Noetherianity from `IdealPowerCohomologyDirectSum`; that bridge data is not part of
the public source statement. -/
@[stacks 0GYK]
theorem topologicalSpace_siteModuleCohomologyTower_isMittagLeffler_of_noetherian_idealPowerCohomology
    (I : Ideal A)
    (ℱ : SequentialInverseSystem ModSheaf)
    (idealPowerSheaf : ℕ → ModSheaf)
    (idealPowerι : ∀ n : ℕ, idealPowerSheaf n ⟶ ℱ.obj (op (n + 1)))
    (idealPower_comp_zero : ∀ n : ℕ, idealPowerι n ≫ ℱ.stepMap n = 0)
    (p : ℕ)
    (hidealPower_exact : ∀ n : ℕ,
      (idealPowerRow ℱ idealPowerSheaf idealPowerι idealPower_comp_zero n).ShortExact)
    [Module (idealAssociatedGradedRing I) (idealPowerCohomologyDirectSum idealPowerSheaf p)]
    [SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
      (idealPowerCohomologyGrading idealPowerSheaf p)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (idealPowerCohomologyDirectSum idealPowerSheaf p)] :
    SequentialInverseSystem.IsMittagLeffler (siteModuleCohomologyTower ℱ p) := sorry

/- Companion recall: the Chapter 21 owner theorem applies once the source proof has transferred
Noetherianity from `IdealPowerCohomologyDirectSum` to the smaller graded boundary-image direct sum
`idealPowerConnectingDirectSum ...`. -/
recall siteModuleCohomologyTower_isMittagLeffler_of_noetherian_associatedGraded

end

end CategoryTheory
