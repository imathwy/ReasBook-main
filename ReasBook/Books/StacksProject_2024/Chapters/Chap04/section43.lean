import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_43_1 (from Chap04) -/
namespace CategoryTheory

/- Domain sampling:
- Primary domain: monoidal category theory.
- Core/canonical declarations inspected:
  - `CategoryTheory.MonoidalCategory`
  - `CategoryTheory.MonoidalCategoryStruct`
  - `MonoidalCategory.associatorNatIso`
  - `MonoidalCategory.leftUnitorNatIso`
- Owner abstraction: `CategoryTheory.MonoidalCategory`.
- Layer triage:
  - `source-facing`: Definition 4.43.1 is a recall-only item for the standard notion of a
    monoidal category, with no extra source-defined data beyond the ambient owner;
  - `core/canonical`: `MonoidalCategory`, which is the bundled owner of the tensor product,
    tensor unit, associator, unitors, and coherence axioms;
  - `bridge/view`: none needed here; `MonoidalCategoryStruct` is only the auxiliary raw-data
    layer that `MonoidalCategory` extends.
- Primitive vs. derived:
  - primitive data: tensor product on objects and morphisms, whiskering, tensor unit,
    associator, left unitor, right unitor, and the coherence axioms stored by
    `MonoidalCategory`;
  - derived API: the functorial tensor constructions and the natural-isomorphism packaging
    `associatorNatIso`, `leftUnitorNatIso`, and `rightUnitorNatIso`.
-/

/- Definition 4.43.1: the Stacks notion of a monoidal category is the canonical mathlib owner
`CategoryTheory.MonoidalCategory`. The auxiliary `MonoidalCategoryStruct` isolates only the raw
data layer, so the public chapter API should recall the bundled owner directly. -/
recall MonoidalCategory

end CategoryTheory

/-! ### Definition_4_43_2 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/- Domain sampling:
- Primary domain: monoidal category theory, specifically monoidal functors.
- Core/canonical declarations inspected:
  - `CategoryTheory.Functor.Monoidal`
  - `CategoryTheory.Functor.LaxMonoidal`
  - `CategoryTheory.Functor.Monoidal.εIso`
  - `CategoryTheory.Functor.Monoidal.μIso`
- Owner abstraction: `Functor.Monoidal`.
- Layer triage:
  - `source-facing`: Definition 4.43.2 is a recall-only item for the standard notion of a
    monoidal functor, with no extra source-defined data beyond the ambient owner;
  - `core/canonical`: `Functor.Monoidal`, whose primitive data is the monoidal functor structure;
  - `bridge/view`: the comparison isomorphisms `Monoidal.εIso` and `Monoidal.μIso`, derived from
    that owner abstraction.
- Primitive vs. derived:
  - primitive data: a monoidal functor `F : C ⥤ D`, encoded by the typeclass `F.Monoidal`;
  - derived API: the unit and tensor comparison isomorphisms `Monoidal.εIso` and
    `Monoidal.μIso`. -/

/- Definition 4.43.2: a functor of monoidal categories is the canonical mathlib owner
`Functor.Monoidal`. For a functor `F : C ⥤ D`, the typeclass `F.Monoidal` is the primitive
structure; the unit and tensor comparison isomorphisms belong to its derived API, so no parallel
local wrapper is needed here. -/
recall Monoidal

/- Companion recall: the unit comparison isomorphism of a monoidal functor is the canonical
derived construction `Monoidal.εIso`. -/
recall Monoidal.εIso

/- Companion recall: the tensorator isomorphism of a monoidal functor is the canonical derived
construction `Monoidal.μIso`. -/
recall Monoidal.μIso

end Functor
end CategoryTheory

/-! ### Lemma_4_43_3 (from Chap04) -/
universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

noncomputable section

/-- A chosen two-sided tensor inverse for `X` makes left tensoring by `X` an equivalence. -/
private theorem tensorLeft_isEquivalence_of_exists_tensor_inverse
    {X : C}
    (hX : ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C)) :
    (tensorLeft X).IsEquivalence := by
  rcases hX with ⟨X', ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩
  exact Functor.IsEquivalence.mk' (tensorLeft X')
    ((leftUnitorNatIso C).symm ≪≫ (tensoringLeft C).mapIso e₂.symm ≪≫ tensorLeftTensor X' X)
    ((tensorLeftTensor X X').symm ≪≫ (tensoringLeft C).mapIso e₁ ≪≫ leftUnitorNatIso C)

/-- A chosen two-sided tensor inverse for `X` also makes right tensoring by `X` an equivalence. -/
private theorem tensorRight_isEquivalence_of_exists_tensor_inverse
    {X : C}
    (hX : ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C)) :
    (tensorRight X).IsEquivalence := by
  rcases hX with ⟨X', ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩
  exact Functor.IsEquivalence.mk' (tensorRight X')
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso e₁.symm ≪≫
      tensorRightTensor X X')
    ((tensorRightTensor X' X).symm ≪≫ (tensoringRight C).mapIso e₂ ≪≫ rightUnitorNatIso C)

/-- If left tensoring by `X` is an equivalence, applying a quasi-inverse to the tensor unit
produces a two-sided tensor inverse for `X`. -/
private theorem exists_tensor_inverse_of_tensorLeft_isEquivalence
    (X : C) (hX : (tensorLeft X).IsEquivalence) :
    ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) := by
  letI := hX
  let F : C ⥤ C := tensorLeft X
  let e : C ≌ C := F.asEquivalence
  let X' : C := F.inv.obj (𝟙_ C)
  let e₁ : X ⊗ X' ≅ 𝟙_ C := e.counitIso.app (𝟙_ C)
  let e₂ : X' ⊗ X ≅ 𝟙_ C :=
    F.preimageIso <|
      (tensorLeftTensor X X').symm.app X ≪≫
        whiskerRightIso e₁ X ≪≫ leftUnitor X ≪≫ (rightUnitor X).symm
  exact ⟨X', ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩

/-- The right-tensor analogue of `exists_tensor_inverse_of_tensorLeft_isEquivalence`. -/
private theorem exists_tensor_inverse_of_tensorRight_isEquivalence
    (X : C) (hX : (tensorRight X).IsEquivalence) :
    ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) := by
  letI := hX
  let F : C ⥤ C := tensorRight X
  let e : C ≌ C := F.asEquivalence
  let X' : C := F.inv.obj (𝟙_ C)
  let e₂ : X' ⊗ X ≅ 𝟙_ C := e.counitIso.app (𝟙_ C)
  let e₁ : X ⊗ X' ≅ 𝟙_ C :=
    F.preimageIso <|
      (tensorRightTensor X' X).symm.app X ≪≫
        whiskerLeftIso X e₂ ≪≫ rightUnitor X ≪≫ (leftUnitor X).symm
  exact ⟨X', ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩

/- Domain sampling:
- Primary domain: monoidal category theory, specifically invertibility of an object detected by
  tensoring endofunctors, with the two-sided inverse data organized upstream through
  `ExactPairing`.
- Core/canonical declarations inspected:
  - `ExactPairing`
  - `tensorLeftAdjunction`
  - `tensorRightAdjunction`
  - `Functor.IsEquivalence`
- Best owner abstraction: `(tensorLeft X).IsEquivalence`, later adopted in Definition `4.43.4`.
- Layer triage:
  - `source-facing`: the three equivalent textbook conditions in Lemma `4.43.3`;
  - `core/canonical`: `(tensorLeft X).IsEquivalence`;
  - `bridge/view`: the `ExactPairing`/adjunction route from two-sided inverse data to the tensor
    equivalence criteria.
- Primitive vs. derived:
  - primitive data: the source-facing two-sided tensor inverse data
    `∃ X', X ⊗ X' ≅ 𝟙_ C` and `X' ⊗ X ≅ 𝟙_ C`;
  - derived API: the source-facing `TFAE` statement, its atomic `↔` projections below, and the
    induced exact pairing/adjunction package.
-/

-- Proof sketch: if left tensoring by `X` is an equivalence, apply a quasi-inverse to the tensor
-- unit to obtain an object `X'` with `X ⊗ X' ≅ 𝟙_ C`, then compare that quasi-inverse with
-- tensoring by `X'` to obtain `X' ⊗ X ≅ 𝟙_ C`; the argument for right tensoring is dual.
-- Conversely, a two-sided tensor inverse for `X` gives the source-facing inverse data, from which
-- one obtains the corresponding exact-pairing/adjunction package and hence equivalences of both
-- `tensorLeft X` and `tensorRight X`.
/-- Lemma 4.43.3: for an object `X` of a monoidal category, the following are equivalent:
left tensoring by `X` is an equivalence, right tensoring by `X` is an equivalence, and there
exists an object `X'` such that `X ⊗ X' ≅ 𝟙_ C` and `X' ⊗ X ≅ 𝟙_ C`. -/
theorem tensor_left_right_equivalence_tfae (X : C) :
    List.TFAE [
      (tensorLeft X).IsEquivalence,
      (tensorRight X).IsEquivalence,
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C)
    ] := by
  tfae_have 1 → 3 := by
    intro hX
    exact exists_tensor_inverse_of_tensorLeft_isEquivalence X hX
  tfae_have 3 → 2 := by
    intro hX
    exact tensorRight_isEquivalence_of_exists_tensor_inverse hX
  tfae_have 2 → 1 := by
    intro hX
    exact tensorLeft_isEquivalence_of_exists_tensor_inverse <|
      exists_tensor_inverse_of_tensorRight_isEquivalence X hX
  tfae_finish

/-- Left tensoring by `X` is an equivalence exactly when right tensoring by `X` is. -/
theorem tensorLeft_isEquivalence_iff_tensorRight_isEquivalence (X : C) :
    (tensorLeft X).IsEquivalence ↔ (tensorRight X).IsEquivalence :=
  (tensor_left_right_equivalence_tfae X).out 0 1

/-- Left tensoring by `X` is an equivalence exactly when `X` admits a two-sided tensor inverse. -/
theorem tensorLeft_isEquivalence_iff_exists_tensor_inverse (X : C) :
    (tensorLeft X).IsEquivalence ↔
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) :=
  (tensor_left_right_equivalence_tfae X).out 0 2

/-- Right tensoring by `X` is an equivalence exactly when `X` admits a two-sided tensor inverse. -/
theorem tensorRight_isEquivalence_iff_exists_tensor_inverse (X : C) :
    (tensorRight X).IsEquivalence ↔
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) :=
  (tensor_left_right_equivalence_tfae X).out 1 2

end

end CategoryTheory

/-! ### Definition_4_43_4 (from Chap04) -/
universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X : C)

/- Domain sampling:
- Primary domain: monoidal category theory, specifically invertible objects detected by tensoring
  endofunctors.
- Core/canonical declarations inspected:
  - `tensorLeft`
  - `tensorRight`
  - `Functor.IsEquivalence`
  - `tensorLeft_isEquivalence_iff_tensorRight_isEquivalence`
  - `tensorLeft_isEquivalence_iff_exists_tensor_inverse`
- Owner abstraction: the canonical predicate is `(tensorLeft X).IsEquivalence`.
- Layer triage:
  - `source-facing`: the textbook invertibility predicate for the fixed object `X`;
  - `core/canonical`: `Functor.IsEquivalence`, specialized to `tensorLeft X`;
  - `bridge/view`: the imported companion theorems
    `tensorLeft_isEquivalence_iff_tensorRight_isEquivalence` and
    `tensorLeft_isEquivalence_iff_exists_tensor_inverse` from Lemma `4.43.3`.
- Primitive vs. derived:
  - primitive data: none beyond the owner predicate itself;
  - derived API: the imported bridge theorems relating that predicate to right tensoring and to
    two-sided tensor inverse data, with no additional local wrapper API needed here.
-/

/- Definition 4.43.4: the canonical predicate expressing that an object `X` of a monoidal
category is invertible is that tensoring on the left by `X` is an equivalence. By Lemma 4.43.3,
this is equivalent to tensoring on the right by `X` being an equivalence and to the existence of
a two-sided tensor inverse for `X`. -/
#check (tensorLeft X).IsEquivalence

/- Companion recall: the left-tensor criterion is equivalent to the right-tensor criterion. -/
recall tensorLeft_isEquivalence_iff_tensorRight_isEquivalence

/- Companion recall: the left-tensor criterion is equivalent to the existence of a two-sided
tensor inverse. -/
recall tensorLeft_isEquivalence_iff_exists_tensor_inverse

end CategoryTheory

/-! ### Definition_4_43_5 (from Chap04) -/
namespace CategoryTheory

/- Domain sampling:
- Primary domain: rigid monoidal category theory.
- Core/canonical declarations inspected:
  - `ExactPairing`
  - `HasLeftDual`
  - `HasRightDual`
  - `ExactPairing.coevaluation`
  - `ExactPairing.evaluation`
- Owner abstraction: `ExactPairing Y X`.
- Layer triage:
  - `source-facing`: the fixed-pair left-duality datum exhibiting `Y` as a left dual of `X`;
  - `core/canonical`: `ExactPairing Y X`;
  - `bridge/view`: `HasLeftDual X` and `HasRightDual Y` package only the existence of some chosen
    dual object, so they are downstream owner abstractions for later existence-style statements,
    not the main owner for this fixed-pair definition.
- Primitive vs. derived:
  - primitive data: the coevaluation, evaluation, and triangle identities stored by
    `ExactPairing`;
  - derived API: the accessors `η_`, `ε_`, the owner-level existence classes `HasLeftDual X` and
    `HasRightDual Y`, and the later hom-equivalence/adjunction constructions.
-/

/- Definition 4.43.5: the textbook datum of a left dual `Y` of `X` is exactly the canonical
mathlib owner `ExactPairing Y X`, whose primitive fields are the coevaluation,
evaluation, and the two triangle identities. -/
recall ExactPairing

end CategoryTheory

/-! ### Lemma_4_43_6 (from Chap04) -/
universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain-style sampling for Lemma 4.43.6:
- Primary domain: rigid monoidal category theory for a fixed exact pairing.
- Core/canonical declarations inspected:
  - `ExactPairing`
  - `tensorLeftHomEquiv`
  - `tensorRightHomEquiv`
  - `tensorLeftAdjunction`
- Owner abstraction first: `ExactPairing Y X`, already recalled in Definition `4.43.5`.
- Layer triage:
  - `source-facing`: the two textbook bijections associated to a fixed left dual `Y` of `X`;
  - `core/canonical`: the exact pairing `ExactPairing Y X`;
  - `bridge/view`: `tensorRightHomEquiv` and `tensorLeftHomEquiv`, functorially derived from the
    owner exact pairing, with naturality as companion theorem API.
- Primitive vs. derived:
  - primitive data: the exact pairing `ExactPairing Y X`;
  - derived API: `tensorRightHomEquiv`, `tensorLeftHomEquiv`, and their naturality theorems.
-/

/- Lemma 4.43.6: if `Y` is a left dual of `X`, then for every `Z` and `Z'` there is a canonical
bijection `Mor (X ⊗ Z', Z) ≃ Mor (Z', Y ⊗ Z)`. This is the specialization
`tensorLeftHomEquiv Z' Y X Z`. -/
recall tensorLeftHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)

/- The first bijection of Lemma 4.43.6 is natural in the target object `Z`. -/
recall tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y']
    (f : Y' ⊗ X ⟶ Z) (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) =
      (tensorLeftHomEquiv X Y Y' Z) f ≫ Y ◁ g

/- The inverse of the first bijection of Lemma 4.43.6 is natural in the source object `Z'`. -/
recall tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y']
    (f : X ⟶ X') (g : X' ⟶ Y ⊗ Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      Y' ◁ f ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g

/- Lemma 4.43.6 also gives the canonical bijection
`Mor (Z' ⊗ Y, Z) ≃ Mor (Z', Z ⊗ X)`. This is the specialization
`tensorRightHomEquiv Z' Y X Z`. -/
recall tensorRightHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')

/- The second bijection of Lemma 4.43.6 is natural in the target object `Z`. -/
recall tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y']
    (f : X ⊗ Y ⟶ Z) (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) =
      (tensorRightHomEquiv X Y Y' Z) f ≫ g ▷ Y'

/- The inverse of the second bijection of Lemma 4.43.6 is natural in the source object `Z'`. -/
recall tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y']
    (f : X ⟶ X') (g : X' ⟶ Z ⊗ Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      f ▷ Y ≫ (tensorRightHomEquiv X' Y Y' Z).symm g

end CategoryTheory

/-! ### Remark_4_43_7 (from Chap04) -/
universe v u

namespace CategoryTheory

open MonoidalCategory

noncomputable section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: rigid monoidal category theory, with `ExactPairing X Y` as the owner object for
  an object `X` together with a chosen right dual `Y`.
- Core/canonical declarations inspected:
  - `ExactPairing`
  - `tensorRightAdjunction`
  - `tensorRightHomEquiv_tensor`
  - `rightDualIso`
- Owner abstraction: `ExactPairing X Y` for the core rigid datum, and `Adjunction` for the
  bridge/view property imposed on an adjunction `tensorRight X ⊣ tensorRight Y`.
- Layer triage:
  - `core/canonical`: `ExactPairing`, `tensorRightAdjunction`, and `rightDualIso`;
  - `bridge/view`: `Adjunction.CompatibleWithLeftTensoring`, which expresses the source remark's
    extra compatibility condition on an adjunction `tensorRight X ⊣ tensorRight Y`, together with
    `Adjunction.toExactPairing` as the canonical bridge back to the owner exact pairing.
- Primitive vs. derived:
  - primitive data: the exact pairing `ExactPairing X Y`;
  - derived API: `tensorRightHomEquiv`, the induced adjunction `tensorRightAdjunction`,
    compatibility via `tensorRightHomEquiv_tensor`, uniqueness via `rightDualIso`, and the
    adjunction-to-pairing bridge `Adjunction.toExactPairing` used by the source-facing existence
    theorem `nonempty_exactPairing_iff_exists_compatible_tensorRightAdjunction`.
-/

/- Remark 4.43.7 first observes that a right dual `Y` of `X` makes `tensorRight Y` a right adjoint
to `tensorRight X`. This is the canonical adjunction `tensorRightAdjunction X Y`. -/
recall tensorRightAdjunction

/- Remark 4.43.7 also records that a right dual, if it exists, is unique up to unique isomorphism.
This is the canonical isomorphism `rightDualIso`. -/
recall rightDualIso

namespace Adjunction

variable {X Y : C}

/-- An adjunction `tensorRight X ⊣ tensorRight Y` is compatible with left tensoring when its
hom-set equivalence commutes with tensoring on the left by any object, up to the associators of
the ambient monoidal category. -/
def CompatibleWithLeftTensoring (adj : tensorRight X ⊣ tensorRight Y) : Prop :=
  ∀ ⦃W Z Z' : C⦄ (f : Z' ⊗ X ⟶ Z),
    adj.homEquiv (W ⊗ Z') (W ⊗ Z) ((α_ W Z' X).hom ≫ W ◁ f) =
      W ◁ adj.homEquiv Z' Z f ≫ (α_ W Z Y).inv

/-- An adjunction `tensorRight X ⊣ tensorRight Y` whose hom-set equivalence is compatible with
left tensoring determines the exact pairing exhibiting `Y` as a right dual of `X`. -/
@[implicit_reducible] def toExactPairing (adj : tensorRight X ⊣ tensorRight Y)
    (hcompat : adj.CompatibleWithLeftTensoring) : ExactPairing X Y where
  coevaluation' := adj.homEquiv (𝟙_ C) X (λ_ X).hom
  evaluation' := (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv
  coevaluation_evaluation' := by
    let η : 𝟙_ C ⟶ X ⊗ Y := adj.homEquiv (𝟙_ C) X (λ_ X).hom
    let ε : Y ⊗ X ⟶ 𝟙_ C := (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv
    apply (adj.homEquiv (Y ⊗ 𝟙_ C) (𝟙_ C)).symm.injective
    have hη :
        adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X) ((ρ_ Y).hom ▷ X) =
          Y ◁ η ≫ (α_ Y X Y).inv := by
      simpa [η] using hcompat ((λ_ X).hom : (𝟙_ C) ⊗ X ⟶ X)
    have hη' :
        (adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)).symm (Y ◁ η ≫ (α_ Y X Y).inv) =
          (ρ_ Y).hom ▷ X := by
      apply (adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)).injective
      rw [(adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)).apply_symm_apply]
      exact hη.symm
    have hρ :
        (adj.homEquiv (Y ⊗ 𝟙_ C) (𝟙_ C)).symm ((ρ_ Y).hom ≫ (λ_ Y).inv) =
          (ρ_ Y).hom ▷ X ≫ ε := by
      simpa [ε] using
        (adj.homEquiv_naturality_left_symm (ρ_ Y).hom (λ_ Y).inv)
    trans (adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)).symm (Y ◁ η ≫ (α_ Y X Y).inv) ≫ ε
    · simpa [ε] using
        (adj.homEquiv_naturality_right_symm (Y ◁ η ≫ (α_ Y X Y).inv) ε)
    trans (ρ_ Y).hom ▷ X ≫ ε
    · rw [hη']
    · exact hρ.symm
  evaluation_coevaluation' := by
    let η : 𝟙_ C ⟶ X ⊗ Y := adj.homEquiv (𝟙_ C) X (λ_ X).hom
    let ε : Y ⊗ X ⟶ 𝟙_ C := (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv
    apply (adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C)).injective
    have hε :
        adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C) ((α_ X Y X).hom ≫ X ◁ ε) =
          (ρ_ X).inv ▷ Y := by
      calc
        adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C) ((α_ X Y X).hom ≫ X ◁ ε)
          = X ◁ adj.homEquiv Y (𝟙_ C) ε ≫ (α_ X (𝟙_ C) Y).inv := by
              simpa using hcompat ε
        _ = X ◁ (λ_ Y).inv ≫ (α_ X (𝟙_ C) Y).inv := by
            simpa using
              congrArg (fun g ↦ X ◁ g ≫ (α_ X (𝟙_ C) Y).inv)
                ((adj.homEquiv Y (𝟙_ C)).apply_symm_apply (λ_ Y).inv)
        _ = (ρ_ X).inv ▷ Y := by monoidal
    have hLambda :
        adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C) ((λ_ X).hom ≫ (ρ_ X).inv) =
          η ≫ (ρ_ X).inv ▷ Y := by
      simpa [η] using
        (adj.homEquiv_naturality_right (λ_ X).hom (ρ_ X).inv)
    trans η ≫ adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C) ((α_ X Y X).hom ≫ X ◁ ε)
    · simpa [η] using
        (adj.homEquiv_naturality_left η ((α_ X Y X).hom ≫ X ◁ ε))
    trans η ≫ (ρ_ X).inv ▷ Y
    · rw [hε]
    · exact hLambda.symm

end Adjunction

/-- The canonical adjunction attached to an exact pairing is compatible with left tensoring. -/
theorem tensorRightAdjunction_compatibleWithLeftTensoring (X Y : C) [ExactPairing X Y] :
    (tensorRightAdjunction X Y).CompatibleWithLeftTensoring := by
  intro W Z Z' f
  simp only [tensorRightAdjunction]
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  have h :
      (tensorRightHomEquiv (W ⊗ Z') X Y (W ⊗ Z)).symm
          (((𝟙 W) ⊗ₘ (tensorRightHomEquiv Z' X Y Z) f) ≫ (α_ W Z Y).inv) =
        (α_ W Z' X).hom ≫
          ((𝟙 W) ⊗ₘ (tensorRightHomEquiv Z' X Y Z).symm ((tensorRightHomEquiv Z' X Y Z) f)) := by
    exact tensorRightHomEquiv_tensor ((tensorRightHomEquiv Z' X Y Z) f) (𝟙 W)
  simpa using h.symm

/-- Remark 4.43.7: an object `Y` is a right dual of `X` exactly when the functor
`Z' ↦ Z' ⊗ Y` is a right adjoint of `Z ↦ Z ⊗ X` via an adjunction whose hom-set equivalence is
compatible with tensoring on the left. This is the source-facing existence bridge, with
`Adjunction.toExactPairing` as its canonical reconstruction map. -/
theorem nonempty_exactPairing_iff_exists_compatible_tensorRightAdjunction (X Y : C) :
    Nonempty (ExactPairing X Y) ↔
      ∃ adj : tensorRight X ⊣ tensorRight Y,
        adj.CompatibleWithLeftTensoring := by
  constructor
  · rintro ⟨_⟩
    exact ⟨tensorRightAdjunction X Y, tensorRightAdjunction_compatibleWithLeftTensoring X Y⟩
  · rintro ⟨adj, hcompat⟩
    exact ⟨adj.toExactPairing hcompat⟩

end

end CategoryTheory

/-! ### Lemma_4_43_8 (from Chap04) -/
open CategoryTheory.MonoidalCategory

noncomputable section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: rigid monoidal category theory.
- Core/canonical declarations inspected:
  - `CategoryTheory.ExactPairing`
  - `CategoryTheory.tensorRightAdjunction`
  - `CategoryTheory.tensorRightTensor`
  - `CategoryTheory.Adjunction.toExactPairing`
- Owner abstraction: `ExactPairing Y X`.
- Layer triage:
  - `source-facing`: the fixed-pair statement that if `Y₁` is a left dual of `A` and `Y₂` is a
    left dual of `B`, then `Y₂ ⊗ Y₁` is a left dual of `A ⊗ B`;
  - `core/canonical`: `ExactPairing Y X`;
  - `bridge/view`: the tensor-right adjunctions `tensorRightAdjunction`, their tensor-product
    comparison isomorphisms `tensorRightTensor`, and the canonical reconstruction
    `Adjunction.toExactPairing`.
- Primitive vs. derived:
  - primitive data: the exact pairings `ExactPairing Y₁ A` and `ExactPairing Y₂ B`;
  - derived API: the composite tensor-right adjunction on `tensorRight (Y₂ ⊗ Y₁)` and the
    resulting exact pairing on `(Y₂ ⊗ Y₁, A ⊗ B)`, together with the induced
    `HasLeftDual (A ⊗ B)` instance for chosen duals.
-/

section

variable {A B Y₁ Y₂ : C} [ExactPairing Y₁ A] [ExactPairing Y₂ B]

namespace ExactPairing

private def tensorAdjunction :
    tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight (A ⊗ B) :=
  let adjComp : tensorRight Y₂ ⋙ tensorRight Y₁ ⊣ tensorRight A ⋙ tensorRight B :=
    (tensorRightAdjunction Y₂ B).comp (tensorRightAdjunction Y₁ A)
  let adjLeft : tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight A ⋙ tensorRight B :=
    adjComp.ofNatIsoLeft (tensorRightTensor Y₂ Y₁).symm
  adjLeft.ofNatIsoRight (tensorRightTensor A B).symm

/-- Helper for Lemma 4.43.8: expanding the transported composite adjunction rewrites its
hom-equivalence as the nested tensor-right hom-equivalences for the two input exact pairings. -/
private theorem tensorAdjunction_homEquiv_apply {Z Z' : C} (f : Z' ⊗ (Y₂ ⊗ Y₁) ⟶ Z) :
    tensorAdjunction.homEquiv Z' Z f =
      (tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A)
        ((tensorRightAdjunction Y₁ A).homEquiv (Z' ⊗ Y₂) Z ((α_ Z' Y₂ Y₁).hom ≫ f)) ≫
          (α_ Z A B).hom := by
  -- Expand the transported adjunction so the two underlying tensor-right adjunctions are visible.
  simp only [tensorAdjunction]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  rw [Adjunction.comp_homEquiv]
  rfl

/-- Helper for Lemma 4.43.8: the left-tensored input to the transported adjunction reassociates to
the exact shape needed to apply the compatibility of `tensorRightAdjunction Y₁ A`. -/
private theorem tensorAdjunction_input_reassociation {W Z Z' : C}
    (f : Z' ⊗ (Y₂ ⊗ Y₁) ⟶ Z) :
    (α_ (W ⊗ Z') Y₂ Y₁).hom ≫ (α_ W Z' (Y₂ ⊗ Y₁)).hom ≫ W ◁ f =
      ((α_ W Z' Y₂).hom ▷ Y₁) ≫ (α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f := by
  -- This is pure monoidal coherence: both sides are the canonical reassociation of `W ◁ f`.
  monoidal

/-- Helper for Lemma 4.43.8: after applying the two compatibility theorems, the remaining
associators combine to the target associator for `A ⊗ B`. -/
private theorem tensorAdjunction_output_reassociation {W Z Z' : C}
    (g : Z' ⟶ (Z ⊗ A) ⊗ B) :
    W ◁ g ≫ (α_ W (Z ⊗ A) B).inv ≫ ((α_ W Z A).inv ▷ B) ≫ (α_ (W ⊗ Z) A B).hom =
      W ◁ (g ≫ (α_ Z A B).hom) ≫ (α_ W Z (A ⊗ B)).inv := by
  -- This is the associator coherence relating the iterated tensor-right output to `A ⊗ B`.
  monoidal

private theorem tensorAdjunction_compatible :
    (tensorAdjunction : tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight (A ⊗ B)).CompatibleWithLeftTensoring := by
  -- Route correction: keep the source-faithful transported-composite adjunction and prove
  -- compatibility by expanding its `homEquiv`, then applying the two basic tensor-right
  -- compatibility theorems in sequence.
  intro W Z Z' f
  -- Rewrite both sides into the nested hom-equivalences for the two tensor-right adjunctions.
  rw [tensorAdjunction_homEquiv_apply]
  rw [tensorAdjunction_homEquiv_apply]
  let inner₀ : Z' ⊗ Y₂ ⟶ Z ⊗ A :=
    (tensorRightAdjunction Y₁ A).homEquiv (Z' ⊗ Y₂) Z ((α_ Z' Y₂ Y₁).hom ≫ f)
  have hinput :
      (α_ (W ⊗ Z') Y₂ Y₁).hom ≫ (α_ W Z' (Y₂ ⊗ Y₁)).hom ≫ W ◁ f =
        ((α_ W Z' Y₂).hom ▷ Y₁) ≫ (α_ W (Z' ⊗ Y₂) Y₁).hom ≫
          W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f := by
    -- Normalize the left-tensored source so the first compatibility theorem can be used.
    exact tensorAdjunction_input_reassociation (W := W) (Z := Z) (Z' := Z') (f := f)
  have hinner_reassoc :
      ((tensorRightAdjunction Y₁ A).homEquiv ((W ⊗ Z') ⊗ Y₂) (W ⊗ Z))
          (((α_ W Z' Y₂).hom ▷ Y₁) ≫ (α_ W (Z' ⊗ Y₂) Y₁).hom ≫
            W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f) =
        (α_ W Z' Y₂).hom ≫
          (tensorRightAdjunction Y₁ A).homEquiv (W ⊗ (Z' ⊗ Y₂)) (W ⊗ Z)
            ((α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f) := by
    -- Move the outer associator across the inner hom-equivalence via naturality in the source.
    simpa [Category.assoc] using
      (Adjunction.homEquiv_naturality_left (adj := tensorRightAdjunction Y₁ A)
        ((α_ W Z' Y₂).hom)
        ((α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f))
  have hinner_compat :
      (tensorRightAdjunction Y₁ A).homEquiv (W ⊗ (Z' ⊗ Y₂)) (W ⊗ Z)
          ((α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f) =
        W ◁ inner₀ ≫ (α_ W Z A).inv := by
    -- Apply the compatibility theorem for the first tensor-right adjunction.
    simpa [inner₀] using
      ((tensorRightAdjunction_compatibleWithLeftTensoring Y₁ A)
        (W := W) (Z := Z) (Z' := Z' ⊗ Y₂) ((α_ Z' Y₂ Y₁).hom ≫ f))
  have houter_naturality :
      (tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A)
          (((α_ W Z' Y₂).hom ≫ W ◁ inner₀) ≫ (α_ W Z A).inv) =
        (tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') (W ⊗ (Z ⊗ A))
            ((α_ W Z' Y₂).hom ≫ W ◁ inner₀) ≫
          ((α_ W Z A).inv ▷ B) := by
    -- Move the right-side associator through the outer hom-equivalence via naturality in the target.
    simpa [Category.assoc] using
      (Adjunction.homEquiv_naturality_right (adj := tensorRightAdjunction Y₂ B)
        ((α_ W Z' Y₂).hom ≫ W ◁ inner₀) (α_ W Z A).inv)
  have houter_compat :
      (tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') (W ⊗ (Z ⊗ A))
          ((α_ W Z' Y₂).hom ≫ W ◁ inner₀) =
        W ◁ ((tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A) inner₀) ≫
          (α_ W (Z ⊗ A) B).inv := by
    -- Apply the compatibility theorem for the second tensor-right adjunction.
    simpa [inner₀] using
      ((tensorRightAdjunction_compatibleWithLeftTensoring Y₂ B)
        (W := W) (Z := Z ⊗ A) (Z' := Z') inner₀)
  calc
    ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
          (((tensorRightAdjunction Y₁ A).homEquiv ((W ⊗ Z') ⊗ Y₂) (W ⊗ Z))
            ((α_ (W ⊗ Z') Y₂ Y₁).hom ≫ (α_ W Z' (Y₂ ⊗ Y₁)).hom ≫ W ◁ f)) ≫
        (α_ (W ⊗ Z) A B).hom
        =
      ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
          (((tensorRightAdjunction Y₁ A).homEquiv ((W ⊗ Z') ⊗ Y₂) (W ⊗ Z))
            (((α_ W Z' Y₂).hom ▷ Y₁) ≫ (α_ W (Z' ⊗ Y₂) Y₁).hom ≫
              W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Replace the inner source morphism by its reassociated form.
          exact congrArg
            (fun k =>
              ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
                (((tensorRightAdjunction Y₁ A).homEquiv ((W ⊗ Z') ⊗ Y₂) (W ⊗ Z)) k) ≫
                  (α_ (W ⊗ Z) A B).hom)
            hinput
    _ =
      ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
          ((α_ W Z' Y₂).hom ≫
            (tensorRightAdjunction Y₁ A).homEquiv (W ⊗ (Z' ⊗ Y₂)) (W ⊗ Z)
              ((α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Move the outer associator across the inner hom-equivalence.
          exact congrArg
            (fun k =>
              ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A)) k ≫
                (α_ (W ⊗ Z) A B).hom)
            hinner_reassoc
    _ =
      ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
          ((α_ W Z' Y₂).hom ≫ (W ◁ inner₀ ≫ (α_ W Z A).inv)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Substitute the first compatibility theorem.
          exact congrArg
            (fun k =>
              ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
                ((α_ W Z' Y₂).hom ≫ k) ≫ (α_ (W ⊗ Z) A B).hom)
            hinner_compat
    _ =
      ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') (W ⊗ (Z ⊗ A))
          ((α_ W Z' Y₂).hom ≫ W ◁ inner₀) ≫
        ((α_ W Z A).inv ▷ B)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Move the remaining target associator through the outer hom-equivalence.
          simpa [Category.assoc] using
            congrArg (fun k => k ≫ (α_ (W ⊗ Z) A B).hom) houter_naturality
    _ =
      (W ◁ ((tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A) inner₀) ≫
          (α_ W (Z ⊗ A) B).inv ≫ ((α_ W Z A).inv ▷ B)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Substitute the second compatibility theorem.
          simpa [Category.assoc] using
            congrArg
              (fun k => k ≫ ((α_ W Z A).inv ▷ B) ≫ (α_ (W ⊗ Z) A B).hom)
              houter_compat
    _ =
      W ◁
          (((tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A) inner₀) ≫
            (α_ Z A B).hom) ≫
        (α_ W Z (A ⊗ B)).inv := by
          -- Finish with the associator coherence relating the iterated right adjoints to `A ⊗ B`.
          simpa [inner₀, Category.assoc] using
            tensorAdjunction_output_reassociation (W := W) (Z := Z) (Z' := Z')
              ((tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A) inner₀)

/-- Lemma 4.43.8: if `Y₁` is a left dual of `A` and `Y₂` is a left dual of `B`, then
`Y₂ ⊗ Y₁` is a left dual of `A ⊗ B`. This exact pairing is canonically reconstructed from the
tensor-right adjunction of the two input pairings. -/
instance tensor : ExactPairing (Y₂ ⊗ Y₁) (A ⊗ B) :=
  tensorAdjunction.toExactPairing tensorAdjunction_compatible

end ExactPairing

end

section

variable {A B : C} [HasLeftDual A] [HasLeftDual B]

namespace HasLeftDual

/-- If two objects admit chosen left duals, then their tensor product admits the tensor product of
those duals, in reverse order, as a chosen left dual. -/
instance tensor : HasLeftDual (A ⊗ B) where
  leftDual := (ᘁB : C) ⊗ (ᘁA : C)
  exact := inferInstance

end HasLeftDual

end

end CategoryTheory

/-! ### Definition_4_43_9 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: monoidal category theory, specifically braided and symmetric monoidal
  categories.
- Relevant owner/style declarations inspected:
  - project style anchor `CategoryTheory.MonoidalCategory` from Definition `4.43.1`, where a
    textbook notion is refined to a direct owner recall rather than a local wrapper;
  - `CategoryTheory.BraidedCategory`;
  - `CategoryTheory.SymmetricCategory`;
  - `CategoryTheory.SymmetricCategory.braiding_swap_eq_inv_braiding`.
- Owner abstraction: `SymmetricCategory C`.
- Layer triage:
  - `core/canonical`: `SymmetricCategory C`, extending the braided owner by the symmetry axiom;
  - `bridge/view`: none needed here, since Definition 4.43.9 only recalls the canonical owner.
- Primitive vs. derived:
  - primitive data: the inherited braided structure together with the axiom
    `SymmetricCategory.symmetry`;
  - derived API: the source-facing comparison
    `SymmetricCategory.braiding_swap_eq_inv_braiding`.
-/

/- Definition 4.43.9: the Stacks notion of a symmetric monoidal category is the canonical
mathlib class `SymmetricCategory C`. Concretely, on top of the fixed monoidal structure, this is
a braided structure whose braiding is involutive. -/
recall SymmetricCategory

/- Companion recall: the source-facing symmetry condition is the canonical theorem saying that
the swapped braiding is the inverse braiding. -/
recall SymmetricCategory.braiding_swap_eq_inv_braiding

end CategoryTheory

/-! ### Lemma_4_43_10 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/- Domain sampling:
- Primary domain: rigid monoidal category theory in a braided/symmetric monoidal category.
- Core/canonical declarations inspected:
  - `CategoryTheory.ExactPairing`
  - `CategoryTheory.BraidedCategory.exactPairing_swap`
  - `CategoryTheory.SymmetricCategory`
- Owner abstraction: `ExactPairing X Y`, with `BraidedCategory.exactPairing_swap` as the canonical
  derived construction that swaps a dual pairing through the braiding.
- Layer triage:
  - `core/canonical`: `ExactPairing` and `BraidedCategory.exactPairing_swap`;
  - `bridge/view`: specializing the braided construction to the symmetric case via the instance
    `[SymmetricCategory C]`.
- Primitive vs. derived:
  - primitive data: an exact pairing `ExactPairing X Y`;
  - derived API: the swapped exact pairing supplied by `BraidedCategory.exactPairing_swap`.
-/

/- Lemma 4.43.10: in a symmetric monoidal category, the swapped coevaluation and evaluation again
form an exact pairing. This is exactly the symmetric special case of the canonical braided owner
declaration `BraidedCategory.exactPairing_swap`. -/
recall BraidedCategory.exactPairing_swap

end CategoryTheory

/-! ### Definition_4_43_11 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]

/- Domain sampling:
- Primary domain: monoidal category theory, specifically braided/symmetric monoidal functors.
- Core/canonical declarations inspected:
  - `CategoryTheory.Functor.Monoidal`
  - `CategoryTheory.Functor.LaxBraided`
  - `CategoryTheory.Functor.LaxBraided.braided`
  - `CategoryTheory.Functor.Braided`
- Owner abstraction: `Functor.Braided`.
- Layer triage:
  - `core/canonical`: `Functor.Braided`, whose primitive compatibility axiom is
    `Functor.LaxBraided.braided`;
  - `bridge/view`: the present item is only the symmetric specialization of that braided owner
    abstraction, so it should stay a direct recall rather than a separate local wrapper.
- Primitive vs. derived:
  - primitive data: a monoidal functor structure together with the braiding-compatibility axiom;
  - derived API: reassociated formulas such as `Functor.map_braiding`.
-/

/-
Definition 4.43.11 is the symmetric-monoidal special case of the canonical mathlib class
`Functor.Braided`: in a symmetric monoidal setting, no separate owner is needed beyond the
canonical braided-functor class. -/
recall Braided

/- Companion recall: the defining compatibility axiom is the canonical field
`Functor.LaxBraided.braided`, expressing that the tensorator commutes with the braiding. -/
recall LaxBraided.braided

/- Companion recall: in the strong-monoidal case this compatibility is also available in the
reassociated form `Functor.map_braiding`, derived from the same owner abstraction and specialized
here to symmetric source and target categories. -/
recall map_braiding

end Functor
end CategoryTheory

/-! ### Remark_4_43_12 (from Chap04) -/
universe v u

namespace CategoryTheory

open Adjunction
open MonoidalCategory
open Opposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: internal Homs in a monoidal category, viewed in the source orientation
  `Mor(W, hom(X, Y)) ≃ Mor(W ⊗ X, Y)`.
- Core/canonical declarations inspected:
  - `tensoringRight`
  - `ParametrizedAdjunction`
  - `ParametrizedAdjunction.homEquiv`
  - `Adjunction.rightAdjointUniq`
- Owner abstraction: a source-facing internal-Hom structure is a bifunctor
  `hom : Cᵒᵖ ⥤ C ⥤ C` equipped with a parametrized adjunction `tensoringRight C ⊣₂ hom`.
- Layer triage:
  - `source-facing`: `tensoringRight C ⊣₂ hom`, which is exactly the right-tensor adjunction
    `Mor(W, hom(X, Y)) ≃ Mor(W ⊗ X, Y)`;
  - `core/canonical`: `ParametrizedAdjunction` and its Hom-set bijection `homEquiv`;
  - `bridge/view`: pointwise uniqueness is supplied by `Adjunction.rightAdjointUniq`; in braided
    settings, the left-oriented mathlib owner
    `MonoidalClosed.internalHomAdjunction₂` can be transported to this source orientation, but
    that bridge is companion-only and must not replace the source-facing owner.
- Primitive vs. derived:
  - primitive data: the bifunctor `hom` and the parametrized adjunction `adj₂ : tensoringRight C ⊣₂ hom`;
  - derived API: the uniqueness isomorphism and the transposed composition/left-tensor/right-tensor
    maps below; the evaluation and coevaluation morphisms are used directly from the owner adjunction
    as `(adj₂.adj X).counit.app Y` and `(adj₂.adj X).unit.app Y`.
-/

namespace ParametrizedAdjunction

variable {hom : Cᵒᵖ ⥤ C ⥤ C}

set_option linter.unusedVariables false in
set_option quotPrecheck false in
notation X " ⟶[" hom "] " Y:10 => (hom.obj (op X)).obj Y

/- Remark 4.43.12: an internal Hom in the source sense is a bifunctor `hom` together with a
parametrized adjunction `tensoringRight C ⊣₂ hom`, whose defining bijection is
`adj₂.homEquiv : (W ⊗ X ⟶ Y) ≃ (W ⟶ X ⟶[hom] Y)`. The following maps are the
canonical constructions carried by that owner abstraction. -/

variable {hom' : Cᵒᵖ ⥤ C ⥤ C}

/-- Remark 4.43.12: if `hom` and `hom'` both realize the source-facing internal-Hom adjunction
`tensoringRight C ⊣₂ -`, then they are canonically naturally isomorphic. This is the Yoneda-style
uniqueness statement that the bifunctor `hom` is determined up to unique isomorphism by the
bijections `Mor(W ⊗ X, Y) ≃ Mor(W, hom(X, Y))`, obtained by applying
`Adjunction.rightAdjointUniq` pointwise in `X`. -/
noncomputable def rightAdjointUniq
    (adj₂ : tensoringRight C ⊣₂ hom) (adj₂' : tensoringRight C ⊣₂ hom') :
    hom ≅ hom' :=
  let e (X : Cᵒᵖ) : hom.obj X ≅ hom'.obj X :=
    (adj₂.adj (unop X)).rightAdjointUniq (adj₂'.adj (unop X))
  NatIso.ofComponents
    (fun X ↦ e X)
    (fun {X Y} f ↦ by
      ext Z
      apply ((adj₂'.adj (unop Y)).homEquiv _ _).symm.injective
      simp only [NatTrans.comp_app]
      rw [(adj₂'.adj (unop Y)).homEquiv_naturality_left_symm]
      have hright :
          ((adj₂'.adj (unop Y)).homEquiv ((hom.obj X).obj Z) Z).symm
              ((e X).hom.app Z ≫ (hom'.map f).app Z) =
            ((tensoringRight C).map f.unop).app ((hom.obj X).obj Z) ≫
              ((adj₂'.adj (unop X)).homEquiv ((hom.obj X).obj Z) Z).symm
                ((e X).hom.app Z) := by
        simpa [e] using
          (adj₂'.homEquiv_symm_naturality_one f.unop ((e X).hom.app Z))
      rw [hright]
      rw [homEquiv_symm_rightAdjointUniq_hom_app, homEquiv_symm_rightAdjointUniq_hom_app]
      simpa [e] using (NatTrans.congr_app (adj₂.whiskerLeft_map_counit f.unop) Z).symm)

/-- The component of `rightAdjointUniq adj₂ adj₂'` at `X` is the usual pointwise right-adjoint
uniqueness morphism for the adjunctions obtained by fixing `X`. -/
-- Proof sketch: unfold `rightAdjointUniq`; it was defined by `NatIso.ofComponents` using the
-- pointwise isomorphisms `(adj₂.adj (unop X)).rightAdjointUniq (adj₂'.adj (unop X))`.
theorem rightAdjointUniq_hom_app
    (adj₂ : tensoringRight C ⊣₂ hom) (adj₂' : tensoringRight C ⊣₂ hom') (X : Cᵒᵖ) :
    (rightAdjointUniq adj₂ adj₂').hom.app X =
      ((adj₂.adj (unop X)).rightAdjointUniq (adj₂'.adj (unop X))).hom := by
  -- Unfold the parametrized uniqueness isomorphism to expose its `NatIso.ofComponents` definition.
  delta rightAdjointUniq
  -- The `X`-component is definitionally the pointwise `Adjunction.rightAdjointUniq` morphism.
  rfl

variable (adj₂ : tensoringRight C ⊣₂ hom)

/-- The composition morphism `hom(Y, Z) ⊗ hom(X, Y) ⟶ hom(X, Z)` obtained by transposing the
obvious double-evaluation composite. -/
abbrev comp (X Y Z : C) :
    ((Y ⟶[hom] Z) ⊗ (X ⟶[hom] Y)) ⟶ (X ⟶[hom] Z) :=
  adj₂.homEquiv
    ((α_ (Y ⟶[hom] Z) (X ⟶[hom] Y) X).hom ≫
      ((Y ⟶[hom] Z) ◁ (adj₂.adj X).counit.app Y) ≫
      (adj₂.adj Y).counit.app Z)

/-- For every `Z`, tensoring on the left induces a canonical morphism
`Z ⊗ hom(X, Y) ⟶ hom(X, Z ⊗ Y)`. -/
abbrev tensorLeft (X Y Z : C) :
    (Z ⊗ (X ⟶[hom] Y)) ⟶ (X ⟶[hom] (Z ⊗ Y)) :=
  adj₂.homEquiv
    ((α_ Z (X ⟶[hom] Y) X).hom ≫
      (Z ◁ (adj₂.adj X).counit.app Y))

section Braided

variable [BraidedCategory C]

/-- In a braided monoidal category there is also a canonical morphism
`hom(Y, Z) ⊗ X ⟶ hom(hom(X, Y), Z)`, obtained by using the braiding to feed `X` into the
evaluation map `hom(X, Y) ⊗ X ⟶ Y`. -/
abbrev braidedTensorRight (X Y Z : C) :
    (((Y ⟶[hom] Z) ⊗ X) ⟶ ((X ⟶[hom] Y) ⟶[hom] Z)) :=
  adj₂.homEquiv
    ((α_ (Y ⟶[hom] Z) X (X ⟶[hom] Y)).hom ≫
      ((Y ⟶[hom] Z) ◁ (β_ X (X ⟶[hom] Y)).hom) ≫
      ((Y ⟶[hom] Z) ◁ (adj₂.adj X).counit.app Y) ≫
      (adj₂.adj Y).counit.app Z)

end Braided

end ParametrizedAdjunction

end CategoryTheory
