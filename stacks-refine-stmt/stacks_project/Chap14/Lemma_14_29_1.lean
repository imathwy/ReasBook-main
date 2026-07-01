import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Limits
open HomologicalComplex

universe v u

prefix:max "◇" => HomologicalComplex.cylinder

noncomputable section

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

open HomologicalComplex.cylinder

private abbrev downRel : ∀ j : ℕ, ∃ i, (ComplexShape.down ℕ).Rel i j :=
  fun j ↦ ⟨j + 1, rfl⟩

/-
Domain-style sampling:
- primary domain: chain-complex cylinders and the homotopy-cofiber universal property;
- sampled owner declarations: `HomologicalComplex.cylinder`,
  `HomologicalComplex.cylinder.desc`, `HomologicalComplex.cylinder.ι₀_desc`,
  `HomologicalComplex.cylinder.ι₁_desc`,
  `Functor.CorepresentableBy`, and `Functor.CorepresentableBy.homEquiv_symm_comp`;
- best owner abstraction: the source-facing Stacks cylinder `◇A`, written directly with the
  canonical mathlib owner `HomologicalComplex.cylinder`, with its universal property expressed by
  the canonical cylinder owner `cylinder.desc` and packaged by `Functor.CorepresentableBy`;
  mathlib does not provide a separate cylinder endofunctor owner here, so the public functoriality
  statement remains source-facing and should be derived from that owner data rather than replaced
  by a parallel local wrapper API;
- owner assumption layer: these owners live at the preadditive plus binary-biproduct level, so
  `[Abelian C]` would be redundant here.

Primitive-vs-derived split:
- primitive data: two chain maps `a, b : A ⟶ B` and a homotopy `Homotopy a b`;
- derived API: the resulting corepresentability witness and the induced cylinder map attached to a
  morphism `f : A ⟶ B`.

Source/core/bridge triage:
- `source-facing`: the homotopy functor represented by maps out of `◇A` and the functoriality of
  the Stacks cylinder construction `A ↦ ◇A`;
- `core/canonical`: `HomologicalComplex.cylinder`, `HomologicalComplex.cylinder.desc`,
  and `Functor.CorepresentableBy`;
- `bridge/view`: the corepresentability witness and the private map extracted from it.
-/

/-- The covariant functor sending `B` to triples `(a, b, h)` of maps `a, b : A ⟶ B` equipped
with a homotopy `h : Homotopy a b`. -/
noncomputable def homotopyFunctor
    (A : ChainComplex C ℕ) :
    ChainComplex C ℕ ⥤ Type v where
  obj B := Σ' a : A ⟶ B, Σ' b : A ⟶ B, Homotopy a b
  map {_ B₂} f x := ⟨x.1 ≫ f, x.2.1 ≫ f, x.2.2.compRight f⟩
  map_id B := by
    sorry
  map_comp f g := by
    sorry

/-- Lemma 14.29.1 (1): the Stacks cylinder `◇A` corepresents the functor sending a chain complex
`B` to triples `(a, b, h)` consisting of two maps `a, b : A ⟶ B` and a homotopy
`h : Homotopy a b`. -/
noncomputable def diamondCorepresentableByHomotopyFunctor
    (A : ChainComplex C ℕ) :
    (homotopyFunctor A).CorepresentableBy ◇A where
  homEquiv := fun {B} ↦
    { toFun := fun f ↦ ⟨ι₀ A ≫ f, ι₁ A ≫ f, (homotopy₀₁ A downRel).compRight f⟩
      invFun := fun x ↦ desc x.1 x.2.1 x.2.2
      left_inv := by
        sorry
      right_inv := by
        sorry }
  homEquiv_comp g f := by
    sorry

private noncomputable abbrev diamondMap {A B : ChainComplex C ℕ} (f : A ⟶ B) : ◇A ⟶ ◇B :=
  (diamondCorepresentableByHomotopyFunctor A).homEquiv.symm
    ⟨f ≫ ι₀ B, f ≫ ι₁ B, (homotopy₀₁ B downRel).compLeft f⟩

-- Proof sketch: apply the injectivity of the owner equivalence
-- `diamondCorepresentableByHomotopyFunctor A`. Under `homEquiv`, both
-- `diamondMap (𝟙 A)` and `𝟙 (◇A)` correspond to the canonical triple
-- `(ι₀ A, ι₁ A, homotopy₀₁ A downRel)`.
/-- The cylinder construction sends identity maps to identity maps. -/
private theorem diamondFunctor_map_id
    (A : ChainComplex C ℕ) :
    diamondMap (𝟙 A) = 𝟙 (◇A) := by
  sorry

-- Proof sketch: again use the injectivity of
-- `diamondCorepresentableByHomotopyFunctor A`. The two maps have the same `homEquiv` image,
-- namely the transported triple
-- `(f ≫ g ≫ ι₀ D, f ≫ g ≫ ι₁ D, ((homotopy₀₁ D downRel).compLeft g).compLeft f)`.
/-- The cylinder construction sends compositions to compositions. -/
private theorem diamondFunctor_map_comp
    {A B D : ChainComplex C ℕ} (f : A ⟶ B) (g : B ⟶ D) :
    diamondMap (f ≫ g) = diamondMap f ≫ diamondMap g := by
  sorry

/-- Lemma 14.29.1 (2): the Stacks cylinder construction `A ↦ ◇A` is functorial on `ℕ`-indexed
chain complexes in a preadditive category with binary biproducts. -/
noncomputable def diamondFunctor : ChainComplex C ℕ ⥤ ChainComplex C ℕ where
  obj A := ◇A
  map {_ _} f := diamondMap f
  map_id A := diamondFunctor_map_id A
  map_comp f g := diamondFunctor_map_comp f g

end ChainComplex
