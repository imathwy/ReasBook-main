import Mathlib
import stacks_project.Chap15.Lemma_15_87_6
import stacks_project.Chap15.Lemma_15_87_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SequentialProObjectMorphismRep

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat
local notation "DAbSeq" => DerivedCategory AbSeq

/- Domain-style sampling for Lemma 15.87.13:
- primary domain: stagewise towers in `D(Ab)` attached to objects of `D(Ab(\mathbf N))`, viewed as
  sequential pro-objects;
- sampled owner declarations:
  `stagewiseAbelianGroupDerivedTowerFunctor`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `abelianGroupDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`,
  `exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit`;
- best owner abstraction: the pro-object comparison should be owned by the Chapter 4/15 canonical
  representative type `SequentialProObjectMorphismRep` and its pro-morphism
  `(ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)).toProObjectHom`, not by a
  parallel local wrapper;
- primitive data: the stagewise towers
  `stagewiseAbelianGroupDerivedTower E` and `stagewiseAbelianGroupDerivedTower D`;
- derived API: the canonical stagewise tower functor
  `stagewiseAbelianGroupDerivedTowerFunctor`, the strict identity-reindex representative induced by
  `φ`, and the resulting morphism between the associated sequential pro-objects.

Source/core/bridge triage:
- `source-facing`: the theorem that a stagewise pro-isomorphism induces an isomorphism on `R lim`;
- `core/canonical`: `IsDerivedLimit` for the stagewise towers and `SequentialProObjectMorphismRep`
  together with `.toProObjectHom`;
- `bridge/view`: the canonical identity-reindex representative
  `ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)`. -/
-- Proof sketch: Lemma 15.87.9 identifies `R lim(E)` and `R lim(D)` with derived limits of the
-- stagewise towers `(E_n)` and `(D_n)`. Applying the Milnor short exact sequences of
-- Lemma 15.87.10 together with the pro-isomorphism invariance of `\varprojlim` and
-- `R^1 \!\varprojlim` from Lemma 15.87.4 shows that the induced map on every cohomology object is
-- an isomorphism, hence the canonical map on derived inverse limits is an isomorphism in
-- `D(\operatorname{Ab})`.
/-- Lemma 15.87.13: if a morphism `E ⟶ D` in `D(\operatorname{Ab}(\mathbf N))` induces an
isomorphism of the associated stagewise pro-objects `(E_n) ⟶ (D_n)` in
`D(\operatorname{Ab})`, then the induced morphism `R lim(E) ⟶ R lim(D)` is an isomorphism in
`D(\operatorname{Ab})`. -/
theorem isIso_map_derivedInverseLimit_of_stagewise_proIsomorphism
    {E D : DAbSeq} (φ : E ⟶ D)
    (hφ : IsIso (ofNatTrans (stagewiseAbelianGroupDerivedTowerFunctor.map φ)).toProObjectHom) :
    IsIso ((additiveFunctorTotalRightDerived (lim : AbSeq ⥤ AddCommGrpCat)).map φ) := sorry
