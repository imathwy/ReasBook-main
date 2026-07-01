import Mathlib
import stacks_project.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for inverse-image sheaves on the small, big-Zariski, and qc sites:
- primary domain: inverse-image functors on sheaf topoi and topological pullback sheaves;
- inspected declarations: `piInverseType`, `epsilonInverseType`, `CategoryTheory.Functor.sheafPullback`,
  `CategoryTheory.Functor.sheafPushforwardContinuousId`,
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'`, and `TopCat.Sheaf.pullback`;
- owner abstraction: the chapter owners `piInverseType JZar πFunctor` and
  `epsilonInverseType JZar JQc`, implemented by the canonical `sheafPullback` functors, together
  with the topological owner `TopCat.Sheaf.pullback`;
- primitive data: the small sheaf `ℱ`, an object `Y : Over X`, and the topological pullback sheaf
  `Y.hom.hom ⁻¹ ℱ`;
- derived API: the objectwise section equivalences, with the global-sections type of the
  topological pullback sheaf written directly rather than through a one-off alias.
- source/core/bridge triage: the source-facing content is the objectwise section formula; the core
  owners are the canonical inverse-image functors above; the bridge is the resulting equivalence
  between their values at `Y` and `Γ(Y, Y.hom.hom ⁻¹ ℱ)`.
-/

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

section

variable {X : LCCat.{u}}
variable (JZar JQc : GrothendieckTopology (Over X))
variable (πFunctor : Opens X.obj ⥤ Over X)
variable [Functor.IsContinuous πFunctor (Opens.grothendieckTopology X.obj) JZar]
variable [(πFunctor.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
  JZar).IsRightAdjoint]
variable [Functor.IsContinuous (𝟭 (Over X)) JZar JQc]
variable [((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint]

-- Proof sketch: this is the Zariski part of the lemma. The morphism of sites `π_X` is set up so
-- that evaluating `π_X^{-1}ℱ` on an object `f : Y ⟶ X` identifies with the global sections of the
-- usual topological pullback sheaf `f^{-1}ℱ` on `Y`.
/-- The big-Zariski inverse image is objectwise the rule `Y ↦ Γ(Y, f^{-1}\mathcal F)`. -/
theorem piInverseOnLCZar_hasPullbackSections
    (ℱ : TopCat.Sheaf (Type u) X.obj) (Y : Over X) :
    IsIsomorphic
      (((πFunctor.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) JZar).obj ℱ).obj.obj
        (op Y))
      (((TopCat.Sheaf.pullback (Type u) Y.hom.hom).obj ℱ).obj.obj (op ⊤)) := sorry

-- Proof sketch: `ε_X^{-1}` is the inverse-image functor for the topology comparison from qc to
-- Zariski. Applying it to the Zariski inverse image `π_X^{-1}ℱ` preserves the objectwise
-- description by sections of the ordinary pullback sheaf, so the resulting qc sheaf still has
-- value `Γ(Y, f^{-1}ℱ)` on every object `f : Y ⟶ X`.
/-- Lemma 21.31.6: the qc inverse image `ε_X^{-1} π_X^{-1} \mathcal F` on `LC_qc/X` is
objectwise the rule `(f : Y ⟶ X) ↦ Γ(Y, f^{-1}\mathcal F)`. Consequently this rule defines a
sheaf on `LC_qc/X`, and its restriction to `LC_Zar/X` is `π_X^{-1}\mathcal F`. -/
theorem epsilonInversePiInverseOnLCQc_hasPullbackSections
    (ℱ : TopCat.Sheaf (Type u) X.obj) (Y : Over X) :
    IsIsomorphic
      ((((𝟭 (Over X)).sheafPullback (Type u) JZar JQc).obj
          ((πFunctor.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) JZar).obj ℱ)).obj.obj
        (op Y))
      (((TopCat.Sheaf.pullback (Type u) Y.hom.hom).obj ℱ).obj.obj (op ⊤)) := sorry

end
