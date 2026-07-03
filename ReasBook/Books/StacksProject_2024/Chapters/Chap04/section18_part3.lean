import Mathlib
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_18_6 (from Chap04) -/
universe w v u

namespace CategoryTheory.Limits

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Lemma 4.18.6:
- primary domain: finite nonempty colimits in `CategoryTheory.Limits`, viewed through passage to
  the opposite category;
- sampled owner API:
  `HasFiniteConnectedColimits`,
  `HasFiniteNonemptyLimits`,
  `hasColimitsOfShape_of_hasLimitsOfShape_op`,
  `hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers`,
  `hasCoequalizers_of_hasPushouts_and_binary_coproducts`;
- best owner abstraction: the source-facing colimit owner `HasFiniteNonemptyColimits`, with the
  opposite-category owner `HasFiniteNonemptyLimits Cᵒᵖ` as the internal core;
- primitive data: no new primitive data beyond the core owner `HasFiniteNonemptyLimits Cᵒᵖ`;
- derived API: the source-facing bridge owner, the finite-nonempty-shape colimit transfer
  instance, and the atomic `↔` reformulations below;
- layer triage:
  - `source-facing`: `HasFiniteNonemptyColimits` and the finite-nonempty-colimit statements of
    Lemma 4.18.6;
  - `core/canonical`: `HasFiniteNonemptyLimits` on the opposite category;
  - `bridge/view`: the instance transfer lemma and the source-facing colimit equivalences
    below. -/

/-- A category has finite nonempty colimits when its opposite has finite nonempty limits. -/
abbrev HasFiniteNonemptyColimits : Prop :=
  HasFiniteNonemptyLimits Cᵒᵖ

instance hasColimitsOfShape_of_hasFiniteNonemptyColimits
    [HasFiniteNonemptyColimits C] (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    HasColimitsOfShape J C := by
  let _ : HasLimitsOfShape Jᵒᵖ Cᵒᵖ := by infer_instance
  exact hasColimitsOfShape_of_hasLimitsOfShape_op

attribute [instance 100] hasColimitsOfShape_of_hasFiniteNonemptyColimits

/-- Lemma 4.18.6 (1): a category `C` has finite nonempty colimits if and only if it has binary
coproducts and coequalizers. -/
theorem finite_nonempty_colimits_iff_binary_coproducts_and_coequalizers :
    HasFiniteNonemptyColimits C ↔ HasBinaryCoproducts C ∧ HasCoequalizers C := by
  constructor
  · intro h
    let _ : HasFiniteNonemptyColimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hBC, hCE⟩
    let _ : HasBinaryCoproducts C := hBC
    let _ : HasCoequalizers C := hCE
    infer_instance

/-- Lemma 4.18.6 (2): a category `C` has finite nonempty colimits if and only if it has binary
coproducts and pushouts. -/
theorem finite_nonempty_colimits_iff_binary_coproducts_and_pushouts :
    HasFiniteNonemptyColimits C ↔ HasBinaryCoproducts C ∧ HasPushouts C := by
  constructor
  · intro h
    let _ : HasFiniteNonemptyColimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hBC, hPO⟩
    let _ : HasBinaryCoproducts C := hBC
    let _ : HasPushouts C := hPO
    infer_instance

end CategoryTheory.Limits

/-! ### Lemma_4_18_7 (from Chap04) -/
open CategoryTheory

universe v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Lemma 4.18.7:
- primary domain: finite colimits in `CategoryTheory.Limits`;
- sampled owner API:
  `HasFiniteColimits`,
  `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts`,
  `hasFiniteColimits_of_hasInitial_and_pushouts`,
  `has_colimits_of_hasCoequalizers_and_coproducts`;
- best owner abstraction: `HasFiniteColimits C`;
- primitive data: no new local primitive data should be introduced here; the source hypotheses are
  exactly the canonical constructor-side typeclasses `HasFiniteCoproducts C`, `HasCoequalizers C`,
  `HasInitial C`, and `HasPushouts C`;
- derived API: the two pairwise `iff` bridges and the textbook `TFAE` packaging below.

Source/core/bridge triage:
- `source-facing`: the two pairwise equivalences and the aggregate `finite_colimits_tfae`;
- `core/canonical`: the owner predicate `HasFiniteColimits C`;
- `bridge/view`: the reformulation of the owner in terms of finite coproducts plus coequalizers, or
  initial object plus pushouts.

There is no upstream theorem already exposing these exact equivalences, so this file should stay a
thin bridge to the canonical mathlib constructors rather than introducing any new wrapper owner. -/

/- Companion recall: the converse directions are already owned by the canonical constructor
theorems below. -/
recall hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
recall hasFiniteColimits_of_hasInitial_and_pushouts

/-- A category has finite coproducts and coequalizers. -/
class HasFiniteCoproductsCoequalizers : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasCoequalizers : HasCoequalizers C]

attribute [instance] HasFiniteCoproductsCoequalizers.hasFiniteCoproducts
attribute [instance] HasFiniteCoproductsCoequalizers.hasCoequalizers

/-- A category has an initial object and pushouts. -/
class HasInitialPushouts : Prop where
  [hasInitial : HasInitial C]
  [hasPushouts : HasPushouts C]

attribute [instance] HasInitialPushouts.hasInitial
attribute [instance] HasInitialPushouts.hasPushouts

/-- A category has finite colimits if and only if it has finite coproducts and coequalizers. -/
theorem finite_colimits_iff_finite_coproducts_and_coequalizers :
    HasFiniteColimits C ↔ HasFiniteCoproductsCoequalizers C := by
  constructor
  · intro h
    letI : HasFiniteColimits C := h
    exact ⟨⟩
  · intro h
    letI : HasFiniteCoproductsCoequalizers C := h
    exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/-- A category has finite colimits if and only if it has an initial object and pushouts. -/
theorem finite_colimits_iff_initial_and_pushouts :
    HasFiniteColimits C ↔ HasInitialPushouts C := by
  constructor
  · intro h
    letI : HasFiniteColimits C := h
    exact ⟨⟩
  · intro h
    letI : HasInitialPushouts C := h
    exact hasFiniteColimits_of_hasInitial_and_pushouts

/- Lemma 4.18.7 packages the standard source-facing characterizations of `HasFiniteColimits C`:

1. finite colimits;
2. finite coproducts and coequalizers;
3. an initial object and pushouts. -/
/-- Lemma 4.18.7: for a category `C`, the following are equivalent:

1. `C` has finite colimits;
2. `C` has finite coproducts and coequalizers;
3. `C` has an initial object and pushouts. -/
-- Proof sketch: use the two direct bridge equivalences above, whose converse directions are the
-- canonical mathlib constructor theorems
-- `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` and
-- `hasFiniteColimits_of_hasInitial_and_pushouts`.
theorem finite_colimits_tfae :
    [HasFiniteColimits C, HasFiniteCoproductsCoequalizers C,
      HasInitialPushouts C].TFAE := by
  tfae_have 1 ↔ 2 := finite_colimits_iff_finite_coproducts_and_coequalizers C
  tfae_have 1 ↔ 3 := finite_colimits_iff_initial_and_pushouts C
  tfae_finish

end CategoryTheory.Limits
