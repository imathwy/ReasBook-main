import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
