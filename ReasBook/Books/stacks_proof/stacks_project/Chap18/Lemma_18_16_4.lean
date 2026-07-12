import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_21_7

open Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (G : C ⥤ D)
variable [G.Full] [G.Faithful]

/- Domain-style sampling for Lemma 18.16.4:
- primary domain: unit and counit isomorphisms for sheaf adjunctions induced by a fully faithful
  functor of sites;
- sampled owner API:
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`,
  `unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful`,
  `counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful`;
- best owner abstractions: the adjunction owners
  `G.sheafAdjunctionContinuous AddCommGrpCat J K` and
  `G.sheafAdjunctionCocontinuous AddCommGrpCat J K`;
- source/core/bridge triage:
  `source-facing`: the canonical maps `ℱ ⟶ g⁻¹(g_! ℱ)` and `g⁻¹(g_* ℱ) ⟶ ℱ` for abelian sheaves;
  `core/canonical`: the general owner-level `IsIso` instances from
    `Chap07/Lemma_7_21_7`;
  `bridge/view`: this file is only the `AddCommGrpCat` specialization of those instances, so its
    public surface should be direct recall/reuse rather than fresh wrapper instance names.

Primitive data are the site functor `G`, its full faithfulness, and the owner-specific adjunction
existence hypotheses: for clause `(1)`, weak sheafification on `K` and left Kan extensions along
`G.op`; for clause `(2)`, pointwise right Kan extensions along `G.op`. The `IsIso` facts are
derived API owned by `Lemma_7_21_7`, so this file should expose only the specialized canonical
inference, not a second parallel instance layer. -/

section

variable [G.IsContinuous J K]
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}, G.op.HasLeftKanExtension F]
variable (ℱ : Sheaf J AddCommGrpCat.{max u v})

/- Lemma 18.16.4 (1): for an abelian sheaf `ℱ` on `C`, the canonical map
`ℱ ⟶ g⁻¹(g_! ℱ)`, i.e. the unit component of
`G.sheafAdjunctionContinuous AddCommGrpCat J K`, is an isomorphism. This is the direct
`AddCommGrpCat` specialization of the chapter-level owner instance. -/
recall unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful

#synth IsIso ((G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K).unit.app ℱ)

end

section

variable [G.IsContinuous J K] [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}, G.op.HasPointwiseRightKanExtension F]
variable (ℱ : Sheaf J AddCommGrpCat.{max u v})

/- Lemma 18.16.4 (2): for an abelian sheaf `ℱ` on `C`, the canonical map
`g⁻¹(g_* ℱ) ⟶ ℱ`, i.e. the counit component of
`G.sheafAdjunctionCocontinuous AddCommGrpCat J K`, is an isomorphism. This is the direct
`AddCommGrpCat` specialization of the chapter-level owner instance. -/
recall counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful

#synth IsIso ((G.sheafAdjunctionCocontinuous AddCommGrpCat.{max u v} J K).counit.app ℱ)

end

end CategoryTheory
