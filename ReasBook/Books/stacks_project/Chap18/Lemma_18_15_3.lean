import Mathlib
import stacks_project.Chap07.Lemma_7_42_6
import stacks_project.Chap18.Lemma_18_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 18.15.3:
- primary domain: exactness of direct-image functors on sheaves of abelian groups and on sheaves
  of modules over a ringed morphism of sites;
- sampled owner declarations:
  `Functor.sheafPushforwardContinuous`,
  `exactFunctor`,
  `SheafOfModules.pushforward`,
  `moduleSheaf_toSheaf_exact`;
- best owner abstraction:
  the abelian-sheaf exactness owner
  `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat JC JD)`;
- primitive-vs-derived split:
  the primitive data are the continuous functor `u`, the almost-cocontinuity hypothesis, the
  two ring sheaves, and the structure-sheaf morphism `φ`;
  the weak sheafification and locally-bijective hypotheses on `JC` and `JD` are ambient
  infrastructure needed for the canonical abelian and module sheaf owners, while almost
  cocontinuity supplies the finite-connected-colimit preservation used to recover exactness of
  the abelian pushforward owner, and the module statement is then a bridge through
  `moduleSheaf_toSheaf_exact`.

Source/core/bridge triage:
- `source-facing`: the Stacks exactness statements for `f_*` on abelian sheaves and on module
  sheaves under almost cocontinuity;
- `core/canonical`: the exactness owner
  `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat JC JD)`;
- `bridge/view`: the epimorphism-preservation step obtained from almost cocontinuity for clause
  `(1)` and the forgetful comparison through `SheafOfModules.toSheaf` for clause `(2)`.

This file should therefore keep the abelian pushforward at the canonical owner level
`exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat JC JD)` and treat the module
statement as a bridge on top of that owner, rather than introducing any wrapper data. -/

section Exactness

variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JD AddCommGrpCat.{w}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]

-- Proof sketch: use the canonical owner `u.sheafPushforwardContinuous AddCommGrpCat JC JD`;
-- almost cocontinuity supplies the finite-connected-colimit preservation input, and the standard
-- exact-functor criterion upgrades this to exactness.
/-- Lemma 18.15.3 (1): if `f : \mathcal D \to \mathcal C` is the morphism of sites associated to
the continuous functor `u : \mathcal C \to \mathcal D` and `u` is almost cocontinuous, then the
direct image functor `f_*`, identified here with
`u.sheafPushforwardContinuous AddCommGrpCat JC JD`, is exact on sheaves of abelian groups. -/
theorem sheafPushforwardContinuous_exact_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    exactFunctor (Sheaf JD AddCommGrpCat.{w}) (Sheaf JC AddCommGrpCat.{w})
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD) := sorry

-- Proof sketch: the module pushforward is a right adjoint, so it is left exact. To obtain right
-- exactness, first show that its composition with the faithful forgetful functor
-- `SheafOfModules.toSheaf 𝒪C` preserves epimorphisms; this composition is definitionally the
-- composite of `SheafOfModules.toSheaf 𝒪D` with the exact abelian pushforward from clause `(1)`.
-- Since `SheafOfModules.toSheaf 𝒪C` reflects epimorphisms, the module pushforward preserves epis,
-- and the standard homology criterion upgrades this to exactness.
/-- Lemma 18.15.3 (2): if `f^\sharp : f^{-1}\mathcal O_\mathcal C \to \mathcal O_\mathcal D` is
given so that `f` becomes a morphism of ringed sites, encoded in Lean by a morphism
`φ : \mathcal O_\mathcal C \to u_* \mathcal O_\mathcal D`, then the direct image functor
`f_* = SheafOfModules.pushforward φ` is exact on sheaves of modules. -/
theorem sheafOfModules_pushforward_exact_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{w}) (𝒪D : Sheaf JD RingCat.{w})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{w} JC JD).obj 𝒪D) :
    exactFunctor (SheafOfModules 𝒪D) (SheafOfModules 𝒪C)
      (SheafOfModules.pushforward φ) := sorry

end Exactness

end CategoryTheory.Functor
