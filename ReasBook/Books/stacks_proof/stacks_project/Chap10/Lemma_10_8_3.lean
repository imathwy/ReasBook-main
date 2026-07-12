import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ModuleCat

universe u v

noncomputable section

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (M : I → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (μ : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable [DirectedSystem M (μ · · ·)]

/-
Layering for this item:
* source-facing: the explicit eventual-equality model of the directed colimit.
* core/canonical owners: `directLimitDiagram`, `directLimitCocone`, `directLimitIsColimit`, and
  `Module.DirectLimit.linearEquiv`.
* bridge/view: identify the chosen categorical colimit with the textbook quotient-of-the-disjoint-
  union model.
-/
local notation "M∞" => DirectLimit M μ
local notation "of∞" => DirectLimit.Module.of R I M μ

local instance directLimit_eventualEq_decidableEqIndex : DecidableEq I := Classical.decEq I

/-- Lemma 10.8.3 (1): in the quotient-of-the-disjoint-union model of the direct limit, two stage
elements agree exactly when they become equal in some later stage of the directed system. -/
@[stacks 00D6]
theorem directLimit_stageMap_eq_iff {i j : I} {x : M i} {y : M j} :
    of∞ i x = of∞ j y ↔ ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k, μ i k hik x = μ j k hjk y := by
  change (⟦⟨i, x⟩⟧ : M∞) = ⟦⟨j, y⟩⟧ ↔ _
  exact Quotient.eq

/-- Lemma 10.8.3 (2): the categorical colimit of a directed system of modules is canonically
isomorphic to the textbook quotient of the disjoint union by eventual equality. -/
@[stacks 00D6]
noncomputable def colimit_iso_eventualEqQuotient :
    colimit (directLimitDiagram M μ) ≅ ModuleCat.of R M∞ :=
  colimit.isoColimitCocone
      (⟨directLimitCocone M μ, directLimitIsColimit M μ⟩ :
        ColimitCocone (directLimitDiagram M μ)) ≪≫
    (Module.DirectLimit.linearEquiv M μ).toModuleIso

/-- Lemma 10.8.3 (3): under `colimit_iso_eventualEqQuotient`, the colimit structure map from stage `i` is the
canonical map from `M i` to the quotient of the disjoint union. -/
@[stacks 00D6]
theorem colimit_iso_eventualEqQuotient_ι (i : I) :
    colimit.ι (directLimitDiagram M μ) i ≫ (colimit_iso_eventualEqQuotient M μ).hom =
      ModuleCat.ofHom (of∞ i) := by
  change
    colimit.ι (directLimitDiagram M μ) i ≫
        (colimit.isoColimitCocone
          (⟨directLimitCocone M μ, directLimitIsColimit M μ⟩ :
            ColimitCocone (directLimitDiagram M μ))).hom ≫
        (Module.DirectLimit.linearEquiv M μ).toModuleIso.hom =
      ModuleCat.ofHom (of∞ i)
  rw [← Category.assoc, colimit.isoColimitCocone_ι_hom]
  ext x
  simpa [DirectLimit.Module.of] using
    (Module.DirectLimit.linearEquiv_of M μ :
      (Module.DirectLimit.linearEquiv M μ) ((Module.DirectLimit.of R I M μ i) x) =
        DirectLimit.Module.of R I M μ i x)

end
