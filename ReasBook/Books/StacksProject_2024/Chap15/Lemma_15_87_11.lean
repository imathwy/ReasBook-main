import Mathlib
import StacksProject_2024.Chap15.«15_87_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 15.87.11 in the sequential derived inverse-system domain:
- sampled chapter owner declarations:
  * `stagewiseAbelianGroupDerivedEvaluation`
  * `stagewiseAbelianGroupDerivedTower`
  * `stagewiseAbelianGroupDerivedTowerFunctor`
  * `Functor.EssSurj`
- source/core/bridge triage:
  * `source-facing`: a tower `(K_n)` in `D(Ab)`
  * `core/canonical`: essential surjectivity of
    `stagewiseAbelianGroupDerivedTowerFunctor : D(Ab(\mathbf N)) ⥤ \mathbf N^{op} ⥤ D(Ab)`
  * `bridge/view`: the objectwise existence statement for a fixed tower `K`

The primitive data of the present item are only the tower `K`. The stagewise tower functor is
already provided by the upstream owner file `15_87_1_1`, and objectwise existence up to
isomorphism is canonically owned by `Functor.EssSurj`. The public statement should therefore live
at that owner level rather than as a parallel existential wrapper.
-/
-- Proof sketch: Lemma 15.87.11 says exactly that every tower `K` of objects of `D(Ab)` is
-- isomorphic to one in the image of the stagewise evaluation functor from `D(Ab(\mathbf N))`.
/-- Lemma 15.87.11: the stagewise evaluation functor from `D(\operatorname{Ab}(\mathbf N))` to
sequential inverse systems in `D(\operatorname{Ab})` is essentially surjective. -/
theorem stagewiseAbelianGroupDerivedTowerFunctor_essSurj :
    (stagewiseAbelianGroupDerivedTowerFunctor).EssSurj := sorry

end

end CategoryTheory
