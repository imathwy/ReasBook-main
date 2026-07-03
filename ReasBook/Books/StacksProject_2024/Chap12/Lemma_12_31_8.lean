import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

local notation "AbCochainComplex" => CochainComplex AddCommGrpCat ℤ

variable {α : Ordinal.{u}}

/- Domain-style sampling for Lemma 12.31.8:
- primary domain: inverse limits of ordinal-indexed systems of cochain complexes of abelian groups;
- sampled core/canonical declarations:
  `HomologicalComplex.Acyclic`,
  `PrincipalSeg.cocone`,
  `coneOfCoconeRightOp`,
  `Functor.IsWellOrderContinuous.isColimitOfIsWellOrderContinuous`;
- best owner abstraction for the predecessor comparison map at `β`:
  the canonical predecessor cocone `(Set.principalSegIio β).cocone K.rightOp` and its standard
  opposite-side bridge `coneOfCoconeRightOp`;
- primitive data: the inverse system `K` and the canonical predecessor cocones indexed by
  `Set.principalSegIio β`;
- derived API: the canonical predecessor comparison morphism
  `ordinalCochainPredecessorComparison K β`, obtained by applying `limit.lift` to
  `coneOfCoconeRightOp ((Set.principalSegIio β).cocone K.rightOp)`;
- source/core/bridge triage:
  `source-facing`: the acyclicity lemma for the inverse-limit complex;
  `core/canonical`: `HomologicalComplex.Acyclic`, `PrincipalSeg.cocone`, and
    `coneOfCoconeRightOp`;
  `bridge/view`: the canonical comparison morphism
    `K.obj (op β) ⟶ limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K)` obtained from
    `limit.lift` on that canonical cone, used in the surjectivity hypothesis.

The file should therefore keep the canonical predecessor cocone direct, while naming only the
resulting comparison morphism that recurs in the source-facing surjectivity hypothesis. -/

-- Proof sketch: argue by transfinite induction on `β < α`. At successor stages, lift a
-- primitive for a cocycle and correct it using acyclicity of the previous stage together with
-- surjectivity in degree `n - 1`. At limit stages, use the inductive acyclicity of the
-- predecessor inverse limit together with the assumed degreewise surjectivity of the canonical
-- comparison morphism `K_β^\bullet ⟶ \lim_{\gamma < β} K_γ^\bullet` obtained from `limit.lift`
-- and the canonical predecessor cone `coneOfCoconeRightOp ((Set.principalSegIio β).cocone
-- K.rightOp)`.
-- The recursively constructed primitives assemble into a primitive in `limit K`.
/-- The canonical comparison morphism from the stage `β` of an ordinal-indexed inverse system of
cochain complexes to the inverse limit of the predecessor subsystem indexed by `γ < β`. -/
noncomputable def ordinalCochainPredecessorComparison
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex) (β : α.ToType) :
    K.obj (op β) ⟶ limit (((Set.principalSegIio β).monotone.functor.op) ⋙ K) :=
  limit.lift _ <|
    coneOfCoconeRightOp <|
      show Cocone ((((Set.principalSegIio β).monotone.functor.op) ⋙ K).rightOp) from
        (Set.principalSegIio β).cocone K.rightOp

/-- Lemma 12.31.8: if an ordinal-indexed inverse system of cochain complexes of abelian groups is
stagewise acyclic and each degree component of the canonical comparison morphism
`ordinalCochainPredecessorComparison K β`
is surjective in every degree, then the inverse limit complex is acyclic. Here
`β : α.ToType` ranges over the ordinals `< α`. -/
lemma ordinalCochainLimit_acyclic_of_stagewise_acyclic_of_surjective_predecessorComparison
    (K : α.ToTypeᵒᵖ ⥤ AbCochainComplex)
    (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
    (hsurj : ∀ (β : α.ToType) (n : ℤ),
      Function.Surjective (((ordinalCochainPredecessorComparison K β).f n).hom)) :
    (limit K).Acyclic := sorry
