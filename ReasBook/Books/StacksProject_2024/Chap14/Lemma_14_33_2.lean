import Mathlib
import stacks_project.Chap14.Example_14_33_1
import stacks_project.Chap14.Lemma_14_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open scoped Simplicial
open scoped IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section

variable {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)

/-
Domain-style sampling:
- primary domain: augmentations of simplicial objects of endofunctors, built from the iterated
  endofunctor formulas of `Example 14.33.1`;
- sampled owner declarations:
  `Definition_14_20_1`,
  `SimplicialObject.augment`,
  `SimplicialObject.augmentHomEquivZeroSimplex`,
  `SimplicialObject.augment_hom_zero`,
  `iteratedFaceMap`;
- best owner abstraction: for fixed `U` and target `𝟭 C`, the chapter's source-facing owner is the
  augmentation morphism `U ⟶ (const (C ⥤ C)).obj (𝟭 C)` from `Definition_14_20_1`; its canonical
  owner construction is `SimplicialObject.augment`, while the chapter bridge
  `SimplicialObject.augmentHomEquivZeroSimplex` repackages the same construction in terms of the
  primitive degree-`0` datum and its two-face relation;
- source/core/bridge triage:
  - `source-facing`: `IteratedEndofunctorRealization` and the existence/uniqueness statement for a
    simplicial object realizing the explicit formulas, together with the augmentation morphism
    `U ⟶ (const (C ⥤ C)).obj (𝟭 C)`;
  - `core/canonical`: `SimplicialObject.augment`;
  - `bridge/view`: `SimplicialObject.augmentHomEquivZeroSimplex`, together with the
    realization-specific degree-`0` map and its face-condition theorem;
- primitive data vs. derived API:
  primitive data are the realization equations and the degree-`0` map
  `U _⦋0⦌ ⟶ 𝟭 C`; the full augmentation morphism and higher-degree compatibility are derived from
  `SimplicialObject.augment`.
-/

local notation "X⦅" n:max "⦆" => Y⦅n⦆
local notation "d^⦅" n ", " j "⦆" => d[Y, d]⦅n, j⦆
local notation "s^⦅" n ", " j "⦆" => s[Y, s]⦅n, j⦆

/-- A simplicial object realizes the iterated endofunctor construction when its objects, face
maps, and degeneracy maps agree with the explicit formulas from `Example 14.33.1`. -/
structure IteratedEndofunctorRealization (U : SimplicialObject (C ⥤ C)) : Prop where
  /-- The degree-`n` term of `U` is `X⦅n⦆ = Y⦅n⦆`. -/
  obj_eq (n : ℕ) : U _⦋n⦌ = X⦅n⦆
  /-- The face maps of `U` are the explicit maps `d^⦅n, i⦆` obtained by inserting `d`. -/
  δ_eq {n : ℕ} (i : Fin (n + 2)) :
    eqToHom (obj_eq (n + 1)) ≫ d^⦅n, i⦆ =
      U.δ i ≫ eqToHom (obj_eq n)
  /-- The degeneracy maps of `U` are the explicit maps `s^⦅n, i⦆` obtained by inserting `s`. -/
  σ_eq {n : ℕ} (i : Fin (n + 1)) :
    eqToHom (obj_eq n) ≫ s^⦅n, i⦆ =
      U.σ i ≫ eqToHom (obj_eq (n + 1))

private theorem iteratedEndofunctorAugmentation_zeroSimplex_face_condition
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U) :
    U.δ 0 ≫ eqToHom (hU.obj_eq 0) ≫ d =
      U.δ 1 ≫ eqToHom (hU.obj_eq 0) ≫ d := by
  -- Proof sketch: transport the two composites with `U.δ 0` and `U.δ 1` to the explicit
  -- formulas from `Example 14.33.1`; both become the natural transformation `d ⋙ d`.
  sorry

-- Proof sketch: the relations
-- `1_Y = (d ⋆ 1_Y) ∘ s = (1_Y ⋆ d) ∘ s` and `(s ⋆ 1) ∘ s = (1 ⋆ s) ∘ s` are precisely the degree
-- `0` and degree `1` simplicial identities for the explicit face and degeneracy maps from
-- `Example 14.33.1`. Hence those maps extend uniquely to a simplicial object with the displayed
-- realization equations.
/-- Lemma 14.33.2 (1): if the degree-`0` degeneracy composed with the two degree-`0` face maps is
the identity and the two degree-`1` degeneracy composites agree, then the iterated endofunctor
data from `Example 14.33.1` is realized by a unique simplicial object of endofunctors of `C`. -/
theorem iteratedEndofunctor_exists_unique_simplicial_object
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆) :
    ∃! U : SimplicialObject (C ⥤ C),
      IteratedEndofunctorRealization d s U := sorry

/-- The canonical simplicial object realizing the iterated endofunctor data of
`Example 14.33.1`. -/
noncomputable def iteratedEndofunctorResolution
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆) :
    SimplicialObject (C ⥤ C) :=
  Classical.choose <|
    ExistsUnique.exists
      (iteratedEndofunctor_exists_unique_simplicial_object d s hσδ₀ hσδ₁ hσσ)

/-- The canonical iterated endofunctor resolution satisfies the realization equations. -/
theorem iteratedEndofunctorResolution_realization
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆) :
    IteratedEndofunctorRealization d s
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ) :=
  Classical.choose_spec <|
    ExistsUnique.exists
      (iteratedEndofunctor_exists_unique_simplicial_object d s hσδ₀ hσδ₁ hσσ)

/-- Any simplicial realization of the iterated endofunctor data is equal to the canonical one. -/
theorem iteratedEndofunctorResolution_eq
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ :
      s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ =
        s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U) :
    U = iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ :=
  ExistsUnique.unique
    (iteratedEndofunctor_exists_unique_simplicial_object d s hσδ₀ hσδ₁ hσσ)
    hU
    (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ)

/-- Lemma 14.33.2 (2): for any simplicial realization of the iterated endofunctor data from
`Example 14.33.1`, the map `d : Y ⟶ 𝟭 C` induces the canonical augmentation to the constant
simplicial object on the identity endofunctor. -/
def iteratedEndofunctorAugmentation
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U) :
    U ⟶ (const (C ⥤ C)).obj (𝟭 C) :=
  (augmentHomEquivZeroSimplex U (𝟭 C)).symm
    ⟨eqToHom (hU.obj_eq 0) ≫ d,
      iteratedEndofunctorAugmentation_zeroSimplex_face_condition d s hU⟩

-- Proof sketch: `iteratedEndofunctorAugmentation` is the canonical owner
-- `SimplicialObject.augment` applied to the degree-`0` map `eqToHom (hU.obj_eq 0) ≫ d`.
/-- The augmentation induced by `d` has the expected degree-`0` component. -/
@[simp]
theorem iteratedEndofunctorAugmentation_app_zero
    {U : SimplicialObject (C ⥤ C)}
    (hU : IteratedEndofunctorRealization d s U) :
    (iteratedEndofunctorAugmentation d s hU).app (op ⦋0⦌) =
      eqToHom (hU.obj_eq 0) ≫ d := by
  simpa [iteratedEndofunctorAugmentation] using
    augmentHomEquivZeroSimplex_symm_apply_zero U (𝟭 C)
      ⟨eqToHom (hU.obj_eq 0) ≫ d,
        iteratedEndofunctorAugmentation_zeroSimplex_face_condition d s hU⟩

end

end CategoryTheory
