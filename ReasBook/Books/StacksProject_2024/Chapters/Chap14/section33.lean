import Mathlib
import Mathlib.CategoryTheory.Monoidal.End

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_14_33_1 (from Chap14) -/
open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling:
- primary domain: simplicial endofunctor constructions from an endofunctor equipped with maps to
  the identity and to its self-composite;
- sampled owner declarations:
  `Nat.iterate`,
  `Functor.isoWhiskerRight`,
  `Functor.associator`,
  `Functor.leftUnitor`,
  `Functor.rightUnitor`;
- best owner abstraction: the source-facing recursive family `iteratedEndofunctor Y`; its bridge
  to the canonical iteration owner is `iteratedEndofunctor_eq_iterate`, while its comparison,
  face, and degeneracy maps use the canonical functor-coherence API for composition of
  endofunctors of `C`;
- layer triage:
  - `source-facing`: the family `iteratedEndofunctor Y` and the explicit face/degeneracy maps;
  - `core/canonical`: the functor coherence maps `Functor.associator`, `Functor.leftUnitor`,
    `Functor.rightUnitor`, together with whiskering and `Nat.iterate`;
  - `bridge/view`: `iteratedEndofunctor_eq_iterate` and the comparison isomorphism
    `iteratedEndofunctorCompIso`;
- primitive data: the endofunctor `Y` together with `d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y`;
- derived API: the comparison isomorphism and the face/degeneracy maps obtained by inserting `d`
  or `s` in the chosen factor.
-/

/-- Example 14.33.1: given an endofunctor `Y : C ⥤ C` with natural transformations
`d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y`, define `X n` to be the `(n + 1)`-fold composite of `Y`.
The companion declarations below provide the canonical comparison isomorphisms
`X (n + m + 1) ≅ X n ⋙ X m` and the face and degeneracy maps obtained by inserting `d` or `s`
in the chosen factor, counted from the left. -/
def iteratedEndofunctor (Y : C ⥤ C) : ℕ → C ⥤ C
  | 0 => Y
  | n + 1 => iteratedEndofunctor Y n ⋙ Y

scoped[IteratedEndofunctor] notation:80 Y:max "⦅" n:max "⦆" =>
  iteratedEndofunctor Y n

open scoped IteratedEndofunctor

/-- Postcomposition by `Y` commutes with the canonical iterate of postcomposition by `Y`. -/
private theorem iterate_postcompose_eq (Y F : C ⥤ C) (n : ℕ) :
    Nat.iterate (fun G : C ⥤ C ↦ G ⋙ Y) n (F ⋙ Y) =
      Nat.iterate (fun G : C ⥤ C ↦ G ⋙ Y) n F ⋙ Y := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih => simp [Nat.iterate, ih]

/-- The source-facing recursive `(n + 1)`-fold composite agrees with the canonical `n`-fold
iteration of postcomposition by `Y`. -/
theorem iteratedEndofunctor_eq_iterate (Y : C ⥤ C) (n : ℕ) :
    Y⦅n⦆ = Nat.iterate (fun F : C ⥤ C ↦ F ⋙ Y) n Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedEndofunctor, ih]
      symm
      simpa [Nat.iterate] using iterate_postcompose_eq Y Y n

/-- The canonical associator identifies the `(n + m + 1)`-fold iterate with the composite of the
`n`-th and `m`-th iterates, i.e. `Y⦅(n + m + 1)⦆ ≅ Y⦅n⦆ ⋙ Y⦅m⦆`. -/
def iteratedEndofunctorCompIso (Y : C ⥤ C) (n m : ℕ) :
    Y⦅(n + m + 1)⦆ ≅ (Y⦅n⦆) ⋙ Y⦅m⦆ :=
  match m with
  | 0 => Iso.refl _
  | m + 1 =>
      Functor.isoWhiskerRight (iteratedEndofunctorCompIso Y n m) Y ≪≫
        Functor.associator (Y⦅n⦆) (Y⦅m⦆) Y

/-- The face maps obtained by applying `d` in the chosen factor. Here
`d[Y, d]⦅n, j⦆` is the map `Y⦅(n + 1)⦆ ⟶ Y⦅n⦆` obtained by using `d` on the `j`-th copy of
`Y`, counted from the left. -/
def iteratedFaceMap (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (n : ℕ) (j : Fin (n + 2)) :
    Y⦅(n + 1)⦆ ⟶ Y⦅n⦆ :=
  match n with
  | 0 =>
      Fin.lastCases
        (Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom)
        (fun _ ↦ Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom)
        j
  | n + 1 =>
      Fin.lastCases
        (Functor.whiskerLeft (Y⦅(n + 1)⦆) d ≫ (Functor.rightUnitor (Y⦅(n + 1)⦆)).hom)
        (fun i ↦ Functor.whiskerRight (iteratedFaceMap Y d n i) Y)
        j

/-- The degeneracy maps obtained by applying `s` in the chosen factor. Here
`s[Y, s]⦅n, j⦆` is the map `Y⦅n⦆ ⟶ Y⦅(n + 1)⦆` obtained by using `s` on the `j`-th copy of
`Y`, counted from the left. -/
def iteratedDegeneracyMap (Y : C ⥤ C) (s : Y ⟶ Y ⋙ Y) (n : ℕ) (j : Fin (n + 1)) :
    Y⦅n⦆ ⟶ Y⦅(n + 1)⦆ :=
  match n with
  | 0 =>
      s
  | n + 1 =>
      Fin.lastCases
        (Functor.whiskerLeft (Y⦅n⦆) s ≫ (Functor.associator (Y⦅n⦆) Y Y).inv)
        (fun i ↦ Functor.whiskerRight (iteratedDegeneracyMap Y s n i) Y)
        j

scoped[IteratedEndofunctor] notation:80 "d[" Y ", " d "]⦅" n ", " j "⦆" =>
  iteratedFaceMap Y d n j
scoped[IteratedEndofunctor] notation:80 "s[" Y ", " s "]⦅" n ", " j "⦆" =>
  iteratedDegeneracyMap Y s n j

end CategoryTheory

/-! ### Lemma_14_33_2 (from Chap14) -/
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

/-! ### Example_14_33_3 (from Chap14) -/
open CategoryTheory
open Functor
open SimplicialObject
open SimplicialObject.Augmented

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/- Domain-style sampling for Example 14.33.3:
- primary domain: augmented simplicial objects and functorial whiskering in
  `CategoryTheory.SimplicialObject`;
- sampled owner API:
  `SimplicialObject.Augmented`,
  `SimplicialObject.Augmented.whiskeringObj`,
  `Functor.whiskeringLeft`,
  `Functor.whiskeringRight`;
- best owner abstraction: `SimplicialObject.Augmented`, transported by the single canonical owner
  `SimplicialObject.Augmented.whiskeringObj` along the composite functor
  `((whiskeringRight C C B).obj G) ⋙ ((whiskeringLeft A C B).obj F) :
    (C ⥤ C) ⥤ (A ⥤ B)`;
- primitive data: only the simplicial object `X` and the augmentation `ε`;
- derived API: the source-facing owner `prePostcomposeAugmented F G ε`; one-sided comparison maps
  are taken directly from the canonical `whiskeringObj.map` API.

Source/core/bridge triage:
- `source-facing`: the augmented simplicial object in `A ⥤ B` whose left side is `G ∘ X ∘ F` and
  whose augmentation point is `G ∘ F`;
- `core/canonical`: `SimplicialObject.Augmented.whiskeringObj`;
- `bridge/view`: the source-facing construction obtained by whiskering the given augmentation
  along the composite functor from endofunctors of `C` to functors `A ⥤ B`.
-/

/-- Example 14.33.3: if a simplicial object of endofunctors of `C` is augmented to the identity
functor of `C`, then composing on the left with `F : A ⥤ C` and on the right with `G : C ⥤ B`
produces an augmented simplicial object in the functor category `A ⥤ B`, whose underlying
simplicial object is `G ∘ X ∘ F` and whose augmentation points to `G ∘ F`. -/
abbrev prePostcomposeAugmented
    (F : A ⥤ C) (G : C ⥤ B)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    SimplicialObject.Augmented (A ⥤ B) :=
  (whiskeringObj (C ⥤ C) (A ⥤ B)
      (((whiskeringRight C C B).obj G) ⋙ ((whiskeringLeft A C B).obj F))).obj
    { left := X
      right := 𝟭 C
      hom := ε }

end CategoryTheory

/-! ### Lemma_14_33_4 (from Chap14) -/
open Opposite
open scoped Simplicial

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

namespace SimplicialObject

variable {C : Type u₁} [Category.{v₁} C]

/- Domain-style sampling for Lemma 14.33.4:
- primary domain: augmented simplicial objects and maps from constant simplicial objects,
  controlled by the terminal simplex `[0]`;
- sampled owner declarations:
  `SimplicialObject.Augmented`,
  `SimplicialObject.augment`,
  `SimplexCategory.isTerminalZero`;
- best owner abstraction: the split-augmentation statement belongs on the canonical owner
  `SimplicialObject.Augmented C`, while the map out of a constant simplicial object is derived from
  the terminal-simplex structure and should stay a thin bridge rather than a second packaged owner;
- primitive data vs. derived API:
  primitive data are only `f : Z ⟶ X _⦋0⦌`;
  the induced morphism `(const C).obj Z ⟶ X` and its section property against an
  augmentation are derived API.

Source/core/bridge triage:
- `source-facing`: the map from the constant simplicial object on `Z` into `X`, determined by the
  degree-`0` morphism `f`;
- `core/canonical`: the augmented simplicial-object owner `SimplicialObject.Augmented C`;
- `bridge/view`: extend `f` along the unique maps `Δ ⟶ [0]`, then specialize to sections of an
  augmentation.
-/

/-- The canonical morphism from the constant simplicial object on `Z` to `X` induced by a map
`Z ⟶ X₀`. -/
def fromZero (X : SimplicialObject C) {Z : C} (f : Z ⟶ X _⦋0⦌) :
    (const C).obj Z ⟶ X where
  app Δ := f ≫ X.map (SimplexCategory.isTerminalZero.from (unop Δ)).op
  naturality := by
    intro Δ₁ Δ₂ φ
    dsimp
    simp only [Category.id_comp]
    have h :
        (SimplexCategory.isTerminalZero.from (unop Δ₂)).op =
          (SimplexCategory.isTerminalZero.from (unop Δ₁)).op ≫ φ := by
      apply Quiver.Hom.unop_inj
      simp only [unop_comp, Quiver.Hom.unop_op]
      rw [SimplexCategory.eq_const_to_zero
        (SimplexCategory.isTerminalZero.from (unop Δ₂))]
      rw [SimplexCategory.eq_const_to_zero
        (φ.unop ≫ SimplexCategory.isTerminalZero.from (unop Δ₁))]
    rw [h, Functor.map_comp, Category.assoc]

-- Proof sketch: in simplicial degree `0`, the unique map `[0] ⟶ [0]` is the identity, so the
-- defining component formula for `fromZero` reduces to `f`.
/-- The degree-`0` component of `fromZero X f` is the original morphism `f`. -/
@[simp] theorem fromZero_app_zero (X : SimplicialObject C) {Z : C} (f : Z ⟶ X _⦋0⦌) :
    (fromZero X f).app (op ⦋0⦌) = f := by
  -- The unique endomorphism of `[0]` is the identity, so the defining formula collapses to `f`.
  simp [fromZero]

/-- Helper for Lemma 14.33.4: composing the degree-`n` component of `fromZero X.left f` with the
augmentation equals the degree-`0` section hypothesis. -/
theorem fromZero_app_comp_hom_app (X : SimplicialObject.Augmented C)
    (f : X.right ⟶ X.left _⦋0⦌)
    (hf : f ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right)
    (n : SimplexCategoryᵒᵖ) :
    (fromZero X.left f).app n ≫ X.hom.app n = 𝟙 X.right := by
  -- Naturality along the unique map `[0] ⟶ [n]` identifies the degree-`n` composite with the
  -- degree-`0` composite, and the latter is the given section equation.
  let α : op ⦋0⦌ ⟶ n := (SimplexCategory.isTerminalZero.from (unop n)).op
  have h_naturality :
      (fromZero X.left f).app n ≫ X.hom.app n = f ≫ X.hom.app (op ⦋0⦌) := by
    simpa [fromZero, α, Category.assoc] using
      congrArg (fun k => f ≫ k) (X.hom.naturality α)
  rw [h_naturality, hf]

-- Proof sketch: check the equality degreewise. In degree `n`, naturality of the augmentation
-- identifies the component with `f ≫ X.hom.app (op ⦋0⦌)`, and the hypothesis says this is the
-- identity.
/-- A section of the degree-`0` component of an augmentation yields a section of the whole
augmentation morphism. -/
theorem fromZero_comp_hom (X : SimplicialObject.Augmented C)
    (f : X.right ⟶ X.left _⦋0⦌)
    (hf : f ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right) :
    fromZero X.left f ≫ X.hom = 𝟙 _ := by
  -- Equality of natural transformations is checked degreewise, and each component is handled by
  -- the naturality computation above.
  ext n
  exact fromZero_app_comp_hom_app X f hf n

end SimplicialObject

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

-- Proof sketch: apply `SimplicialObject.fromZero_comp_hom` to the augmented simplicial
-- object from Example 14.33.3 after pre- and post-composition. The hypothesis says exactly that
-- the chosen degree-`0` map is a section of the degree-`0` augmentation component.
/-- Lemma 14.33.4: if the degree-`0` component of the pre/postcomposed augmentation admits a
section `h₀`, then the induced morphism from the constant simplicial object on `F ⋙ G` to the
pre/postcomposed simplicial object is a section of the whole augmentation. -/
theorem prePostcomposeAugmentation_fromZero_comp_eq_id
    {X : SimplicialObject (C ⥤ C)}
    (F : A ⥤ C) (G : C ⥤ B)
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (h₀ : F ⋙ G ⟶ (prePostcomposeAugmented F G ε).left _⦋0⦌)
    (hh₀ : h₀ ≫ (prePostcomposeAugmented F G ε).hom.app (op ⦋0⦌) = 𝟙 (F ⋙ G)) :
    (prePostcomposeAugmented F G ε).left.fromZero h₀ ≫ (prePostcomposeAugmented F G ε).hom =
      𝟙 _ := by
  simpa using SimplicialObject.fromZero_comp_hom (prePostcomposeAugmented F G ε) h₀ hh₀

end CategoryTheory

/-! ### Lemma_14_33_5 (from Chap14) -/
open CategoryTheory
open Functor
open CategoryTheory.SimplicialObject
open SimplicialObject.Augmented
open Opposite
open scoped IteratedEndofunctor Simplicial

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/- Domain-style sampling for Lemma 14.33.5:
- primary domain: iterated endofunctor resolutions, augmented simplicial objects in functor
  categories, functorial whiskering, and the zigzag homotopy relation on simplicial maps;
- sampled same-kind declarations:
  `IteratedEndofunctorRealization`,
  `iteratedEndofunctorAugmentation`,
  `Functor.whiskeringLeft`,
  `Functor.whiskeringRight`,
  `SimplicialObject.Augmented.whiskeringObj`,
  `prePostcomposeAugmented`,
  `CategoryTheory.SimplicialObject.Homotopic`,
  `CategoryTheory.SimplicialObject.Homotopic.of_homotopy`;
- best owner abstraction: for any simplicial realization `X` with
  `hX : IteratedEndofunctorRealization d s X`, the source-facing augmented owner is
  `prePostcomposeAugmented F G (iteratedEndofunctorAugmentation d s hX)`; the input morphisms
  `α` and `β` are morphisms between the canonical one-sided specializations
  `prePostcomposeAugmented (𝟭 C) G ε` and `prePostcomposeAugmented F (𝟭 C) ε`, and the induced
  simplicial maps are taken directly from
  `whiskeringObj.map ... |>.left`. The direct homotopy data are built from the realization
  equations in `hX` together with the explicit degeneracy maps and block decompositions
  `Y⦅n + 1⦆ ≅ Y⦅n - i⦆ ⋙ Y⦅i⦆`, while the numbered source-facing outcome lives in
  `CategoryTheory.SimplicialObject.Homotopic`;
- primitive data: `d`, `s`, the simplicial identities `hσδ₀`, `hσδ₁`, `hσσ`, and the augmented
  morphisms `α` and `β` for the canonical one-sided specializations of the augmentation
  `iteratedEndofunctorAugmentation d s hX`;
- derived API: the source-facing augmented owner `prePostcomposeAugmented F G ε`, the induced
  simplicial maps obtained by `whiskeringObj.map α |>.left` and
  `whiskeringObj.map β |>.left`, the resulting simplicial homotopy, and its image in the zigzag
  relation.

Source/core/bridge triage:
- `source-facing`: the induced simplicial maps on `G ∘ X ∘ F` and `G' ∘ X ∘ F'` for an arbitrary
  simplicial realization `X` of the iterated endofunctor data together with their zigzag
  homotopy relation;
- `core/canonical`: morphisms in `SimplicialObject.Augmented`, transported by
  `SimplicialObject.Augmented.whiskeringObj`, together with the source-facing owner
  `prePostcomposeAugmented F G (iteratedEndofunctorAugmentation d s hX)` and the chapter owner
  `CategoryTheory.SimplicialObject.Homotopic`;
- `bridge/view`: the one-sided specializations
  `prePostcomposeAugmented (𝟭 C) G ε` and `prePostcomposeAugmented F (𝟭 C) ε`, the induced
  simplicial maps obtained directly from `whiskeringObj.map ... |>.left`, and the passage from the
  explicit directed homotopy witness in `CategoryTheory.SimplicialObject.Homotopy` to the owner
  relation `SimplicialObject.Homotopic`.
-/

section Iterated

variable {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
local notation "X⦅" n:max "⦆" => Y⦅n⦆
local notation "d^⦅" n ", " j "⦆" => d[Y, d]⦅n, j⦆
local notation "s^⦅" n ", " j "⦆" => s[Y, s]⦅n, j⦆

variable
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)

private noncomputable def iteratedEndofunctorSplitIso (n : ℕ) (i : Fin (n + 1)) :
    X⦅(n + 1)⦆ ≅ X⦅(n - i.1)⦆ ⋙ X⦅i.1⦆ :=
  eqToIso (by rw [Nat.sub_add_cancel i.is_le]) ≪≫ iteratedEndofunctorCompIso Y (n - i.1) i.1

/-- Helper for Lemma 14.33.5: a nonterminal iterated face map is obtained by whiskering the
smaller face map on the right by `Y`. -/
@[simp] private theorem iterated_faceMap_castSucc
    (n : ℕ) (j : Fin (n + 2)) :
    d^⦅n + 1, j.castSucc⦆ = Functor.whiskerRight d^⦅n, j⦆ Y := by
  -- Unfold the recursive last-case definition at a nonterminal index.
  simp [iteratedFaceMap]

/-- Helper for Lemma 14.33.5: the last iterated face map is the right-unitor branch of the
recursive definition. -/
@[simp] private theorem iterated_faceMap_last
    (n : ℕ) :
    d^⦅n + 1, Fin.last (n + 2)⦆ =
      Functor.whiskerLeft X⦅(n + 1)⦆ d ≫ (Functor.rightUnitor X⦅(n + 1)⦆).hom := by
  -- Unfold the recursive last-case definition at the terminal index.
  simp [iteratedFaceMap]
  rfl

/-- Helper for Lemma 14.33.5: a nonterminal iterated degeneracy map is obtained by whiskering
the smaller degeneracy map on the right by `Y`. -/
@[simp] private theorem iterated_degeneracyMap_castSucc
    (n : ℕ) (j : Fin (n + 1)) :
    s^⦅n + 1, j.castSucc⦆ = Functor.whiskerRight s^⦅n, j⦆ Y := by
  -- Unfold the recursive last-case definition at a nonterminal index.
  simp [iteratedDegeneracyMap]

/-- Helper for Lemma 14.33.5: the last iterated degeneracy map is the associator branch of the
recursive definition. -/
@[simp] private theorem iterated_degeneracyMap_last
    (n : ℕ) :
    s^⦅n + 1, Fin.last (n + 1)⦆ =
      Functor.whiskerLeft X⦅n⦆ s ≫ (Functor.associator X⦅n⦆ Y Y).inv := by
  -- Unfold the recursive last-case definition at the terminal index.
  simp [iteratedDegeneracyMap]
  rfl

/-- Helper for Lemma 14.33.5: splitting off a zero-length right block has identity forward map. -/
@[simp] private theorem iteratedEndofunctorSplitIso_zero_hom
    (n : ℕ) :
    (iteratedEndofunctorSplitIso (Y := Y) n (0 : Fin (n + 1))).hom = 𝟙 X⦅(n + 1)⦆ := by
  -- The zero split is exactly the base case of `iteratedEndofunctorCompIso`.
  simp [iteratedEndofunctorSplitIso, iteratedEndofunctorCompIso]

/-- Helper for Lemma 14.33.5: splitting off a zero-length right block has identity inverse map. -/
@[simp] private theorem iteratedEndofunctorSplitIso_zero_inv
    (n : ℕ) :
    (iteratedEndofunctorSplitIso (Y := Y) n (0 : Fin (n + 1))).inv = 𝟙 X⦅(n + 1)⦆ := by
  -- The zero split is exactly the base case of `iteratedEndofunctorCompIso`.
  simp [iteratedEndofunctorSplitIso, iteratedEndofunctorCompIso]

-- Route correction: isolate the arithmetic of the split index before the categorical transport
-- step, so the remaining blocker is only the `eqToHom`/whiskering transport across the split iso.
/-- Helper for Lemma 14.33.5: increasing the split index by one lowers the left block degree by
one. -/
@[simp] private theorem split_left_degree_succ
    (n : ℕ) (i : Fin (n + 1)) :
    n + 1 - i.succ.1 = n - i.1 := by
  -- This is the arithmetic identity behind every recursive split-transport step.
  exact Nat.succ_sub_succ_eq_sub n i.1

/-- Helper for Lemma 14.33.5: casting a split index with `castSucc` does not change the left
block degree. -/
@[simp] private theorem split_left_degree_castSucc
    (n : ℕ) (i : Fin (n + 1)) :
    n - i.castSucc.1 = n - i.1 := by
  -- `castSucc` preserves the underlying natural number.
  rfl

/-- Helper for Lemma 14.33.5: the zero split leaves the entire degree in the left block. -/
@[simp] private theorem split_left_degree_zero
    (n : ℕ) :
    n - (0 : Fin (n + 1)).1 = n := by
  -- The zero split removes no terms from the left block.
  simp

/-- Helper for Lemma 14.33.5: the last split leaves no left block. -/
@[simp] private theorem split_left_degree_last
    (n : ℕ) :
    n - (Fin.last n).1 = 0 := by
  -- Splitting off the maximal right block exhausts the left block.
  simp

/-- Helper for Lemma 14.33.5: the recursive successor split has the expected source object after
viewing the final factor as a right whisker by `Y`. -/
private theorem split_succ_source_obj_eq
    (n : ℕ) (i : Fin (n + 1)) :
    X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y := by
  -- Normalize the source as one more iterate on the right block and solve the remaining index
  -- equality arithmetically.
  have h : n = n - i.1 + i.1 := by
    simpa using (Nat.sub_add_cancel i.is_le).symm
  simpa [iteratedEndofunctor, split_left_degree_succ] using
    congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h

/-- Helper for Lemma 14.33.5: the recursive successor split has the expected target object after
reassociating the right block with one extra copy of `Y`. -/
@[simp] private theorem split_succ_target_obj_eq
    (n : ℕ) (i : Fin (n + 1)) :
    X⦅(n + 1 - i.succ.1)⦆ ⋙ (X⦅i.1⦆ ⋙ Y) = X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆ := by
  -- This is definitionally the recursive clause `X⦅i + 1⦆ = X⦅i⦆ ⋙ Y`.
  rfl

/-- Helper for Lemma 14.33.5: the target-side successor split transport is the identity
natural transformation. -/
@[simp] private theorem split_succ_target_obj_eqToHom
    (n : ℕ) (i : Fin (n + 1)) :
    eqToHom (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)) = 𝟙 _ := by
  -- After substituting the definitional target equality, the cast is `eqToHom rfl`.
  ext Z
  cases split_succ_target_obj_eq (Y := Y) (n := n) (i := i)
  rfl

/-- Helper for Lemma 14.33.5: the inverse target-side successor split transport is the identity
natural transformation. -/
@[simp] private theorem split_succ_target_obj_eq_symm_eqToHom
    (n : ℕ) (i : Fin (n + 1)) :
    eqToHom (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)).symm = 𝟙 _ := by
  -- The symmetric cast is also `eqToHom rfl` after substituting the equality proof.
  ext Z
  cases split_succ_target_obj_eq (Y := Y) (n := n) (i := i)
  rfl

/-- Helper for Lemma 14.33.5: the objectwise successor target transport is the identity map. -/
@[simp] private theorem split_succ_target_obj_eq_obj_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C) :
    eqToHom
        (congrArg (fun F : C ⥤ C ↦ F.obj Z) (split_succ_target_obj_eq (Y := Y) (n := n) (i := i))) =
      𝟙 _ := by
  -- Passing to the `Z`-component reduces the target cast to a reflexive object equality.
  cases split_succ_target_obj_eq (Y := Y) (n := n) (i := i)
  rfl

/-- Helper for Lemma 14.33.5: the inverse objectwise successor target transport is the identity
map. -/
@[simp] private theorem split_succ_target_obj_eq_symm_obj_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C) :
    eqToHom
        (congrArg (fun F : C ⥤ C ↦ F.obj Z)
          (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)).symm) =
      𝟙 _ := by
  -- The symmetric componentwise cast collapses in the same way.
  cases split_succ_target_obj_eq (Y := Y) (n := n) (i := i)
  rfl

/-- Helper for Lemma 14.33.5: any objectwise successor target cast coming from the recursive split
is the identity map. -/
@[simp] private theorem split_succ_target_obj_any_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C)
    (p :
      (X⦅(n + 1 - i.succ.1)⦆ ⋙ (X⦅i.1⦆ ⋙ Y)).obj Z =
        (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z) :
    eqToHom p = 𝟙 _ := by
  -- All proofs of this definitional component equality induce the same identity map.
  have hp :
      p =
        ((by
          rfl :
            (X⦅(n + 1 - i.succ.1)⦆ ⋙ (X⦅i.1⦆ ⋙ Y)).obj Z =
              (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z)) := Subsingleton.elim _ _
  cases hp
  rfl

/-- Helper for Lemma 14.33.5: after applying the final `Y`, any successor target component cast
from the recursive split is still the identity map. -/
@[simp] private theorem split_succ_target_obj_after_Y_any_eqToHom
    (n : ℕ) (i : Fin (n + 1)) (Z : C)
    (p :
      Y.obj (X⦅i.1⦆.obj (X⦅(n + 1 - i.succ.1)⦆.obj Z)) =
        (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z) :
    eqToHom p = 𝟙 _ := by
  -- The recursive target equality remains definitional after evaluating the final `Y`.
  have hp :
      p =
        ((by
          rfl :
            Y.obj (X⦅i.1⦆.obj (X⦅(n + 1 - i.succ.1)⦆.obj Z)) =
              (X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆).obj Z)) := Subsingleton.elim _ _
  cases hp
  rfl

/-- Helper for Lemma 14.33.5: the leading source-side successor cast is the explicit block-split
transport. -/
@[simp] private theorem split_succ_source_obj_eqToHom
    (n : ℕ) (i : Fin (n + 1)) :
    eqToHom
        ((by
          have h : n = n - i.1 + i.1 := by
            simpa using (Nat.sub_add_cancel i.is_le).symm
          simpa [iteratedEndofunctor, split_left_degree_succ] using
            congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h) :
          X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y) =
      eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)) := by
  -- Both source casts encode the same arithmetic rewrite of the recursive successor split.
  simpa using congrArg eqToHom
    (Subsingleton.elim
      (((by
          have h : n = n - i.1 + i.1 := by
            simpa using (Nat.sub_add_cancel i.is_le).symm
          simpa [iteratedEndofunctor, split_left_degree_succ] using
            congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h) :
          X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y))
      (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)))

/-- Helper for Lemma 14.33.5: the inverse leading source-side successor cast is the explicit
block-split transport. -/
@[simp] private theorem split_succ_source_obj_eq_symm_eqToHom
    (n : ℕ) (i : Fin (n + 1)) :
    eqToHom
        (((by
          have h : n = n - i.1 + i.1 := by
            simpa using (Nat.sub_add_cancel i.is_le).symm
          simpa [iteratedEndofunctor, split_left_degree_succ] using
            congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h) :
          X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y).symm) =
      eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)).symm := by
  -- The symmetric source casts agree by the same object equality.
  simpa using congrArg (fun h ↦ eqToHom h.symm)
    (Subsingleton.elim
      (((by
          have h : n = n - i.1 + i.1 := by
            simpa using (Nat.sub_add_cancel i.is_le).symm
          simpa [iteratedEndofunctor, split_left_degree_succ] using
            congrArg (fun m : ℕ ↦ X⦅(m + 1)⦆ ⋙ Y) h) :
          X⦅(n + 2)⦆ = X⦅(n + 1 - i.succ.1 + i.1 + 1)⦆ ⋙ Y))
      (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)))

/-- Helper for Lemma 14.33.5: postcomposing with the component of a functor-object cast does not
change a morphism. -/
private theorem comp_eqToHom_congrArg_functor_obj
    {F G : C ⥤ C} (h : F = G) (Z : C) {X : C} (f : X ⟶ F.obj Z) :
    HEq (f ≫ eqToHom (congrArg (fun H : C ⥤ C ↦ H.obj Z) h)) f := by
  -- This is the componentwise form of `comp_eqToHom_heq` for functor-object equalities.
  exact comp_eqToHom_heq f (congrArg (fun H : C ⥤ C ↦ H.obj Z) h)

/-- Helper for Lemma 14.33.5: precomposing with the component of a functor-object cast does not
change a morphism. -/
private theorem eqToHom_congrArg_functor_obj_comp
    {F G : C ⥤ C} (h : F = G) (Z : C) {X : C} (g : G.obj Z ⟶ X) :
    HEq (eqToHom (congrArg (fun H : C ⥤ C ↦ H.obj Z) h) ≫ g) g := by
  -- This is the dual componentwise form of `eqToHom_comp_heq`.
  exact eqToHom_comp_heq g (congrArg (fun H : C ⥤ C ↦ H.obj Z) h)

/-- Helper for Lemma 14.33.5: the successor split isomorphism forward map is the recursive split
map, with the source and target transports made explicit by named casts. -/
private theorem iterated_split_iso_succ_hom_transport_with_named_casts
    (n : ℕ) (i : Fin (n + 1)) :
    (iteratedEndofunctorSplitIso (Y := Y) (n + 1) i.succ).hom =
      eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)) ≫
        Functor.whiskerRight
          (iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).hom Y ≫
          (Functor.associator X⦅(n + 1 - i.succ.1)⦆ X⦅i.1⦆ Y).hom ≫
            eqToHom (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)) :=
by
  -- Unfold one recursive layer of the split isomorphism and rewrite the source/target casts by
  -- the named transport lemmas. The remaining composite is definitionally the recursive forward
  -- branch of `iteratedEndofunctorCompIso`.
  rw [split_succ_source_obj_eqToHom, split_succ_target_obj_eqToHom]
  let f :
      X⦅(n + 2)⦆ ⟶ X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆ :=
    eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)) ≫
      Functor.whiskerRight
        (iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).hom Y ≫
      (Functor.associator X⦅(n + 1 - i.succ.1)⦆ X⦅i.1⦆ Y).hom
  -- After the source and target casts are named, the recursive branch is exactly `f`, and the
  -- only remaining normalization is the terminal composition with the identity morphism.
  simp [iteratedEndofunctorSplitIso, iteratedEndofunctorCompIso]
  simpa [f, iteratedEndofunctor] using (Category.comp_id f).symm

/-- Helper for Lemma 14.33.5: the successor split isomorphism inverse map is the recursive unsplit
map, with the source and target transports made explicit by named casts. -/
private theorem iterated_split_iso_succ_inv_transport_with_named_casts
    (n : ℕ) (i : Fin (n + 1)) :
    (iteratedEndofunctorSplitIso (Y := Y) (n + 1) i.succ).inv =
      eqToHom (split_succ_target_obj_eq (Y := Y) (n := n) (i := i)).symm ≫
        (Functor.associator X⦅(n + 1 - i.succ.1)⦆ X⦅i.1⦆ Y).inv ≫
          Functor.whiskerRight
            (iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).inv Y ≫
            eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)).symm :=
by
  -- The inverse recursion normalizes in the same way, now using the symmetric source and target
  -- casts.
  rw [split_succ_target_obj_eq_symm_eqToHom]
  simp [iteratedEndofunctorSplitIso, iteratedEndofunctorCompIso]
  let f :
      X⦅(n + 1 - i.succ.1)⦆ ⋙ X⦅i.succ.1⦆ ⟶ X⦅(n + 2)⦆ :=
    (Functor.associator X⦅(n + 1 - i.succ.1)⦆ X⦅i.1⦆ Y).inv ≫
      Functor.whiskerRight
        (iteratedEndofunctorCompIso Y (n + 1 - i.succ.1) i.1).inv Y ≫
        eqToHom (split_succ_source_obj_eq (Y := Y) (n := n) (i := i)).symm
  exact (Category.id_comp f).symm

-- Proof sketch: use the explicit degreewise homotopy operators
-- `σ_i ≫ (a_i ⋆ b_{n - i})`, where `σ_i` is the canonical degeneracy map in the iterated
-- endofunctor realization and the block decomposition `Y⦅n + 1⦆ ≅ Y⦅n - i⦆ ⋙ Y⦅i⦆` is given by
-- `iteratedEndofunctorSplitIso`. The simplicial identities reduce to the compatibility of `α`,
-- `β`, and the realization equations.
/-- Companion directed simplicial homotopy witnessing the zigzag relation of Lemma 14.33.5. -/
noncomputable def prePostcomposeAugmentedMap_homotopy
    {X : SimplicialObject (C ⥤ C)} (hX : IteratedEndofunctorRealization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α :
      prePostcomposeAugmented (𝟭 C) G (iteratedEndofunctorAugmentation d s hX) ⟶
        prePostcomposeAugmented (𝟭 C) G' (iteratedEndofunctorAugmentation d s hX))
    (β :
      prePostcomposeAugmented F (𝟭 C) (iteratedEndofunctorAugmentation d s hX) ⟶
        prePostcomposeAugmented F' (𝟭 C) (iteratedEndofunctorAugmentation d s hX)) :
    SimplicialObject.Homotopy
      (((whiskeringObj (A ⥤ C) (A ⥤ B) ((whiskeringRight A C B).obj G)).map β |>.left) ≫
        ((whiskeringObj (C ⥤ B) (A ⥤ B) ((whiskeringLeft A C B).obj F')).map α |>.left))
      (((whiskeringObj (C ⥤ B) (A ⥤ B) ((whiskeringLeft A C B).obj F)).map α |>.left) ≫
        ((whiskeringObj (A ⥤ C) (A ⥤ B) ((whiskeringRight A C B).obj G')).map β |>.left)) where
  h {n} i :=
    let j : Fin (n + 1) := ⟨n - i.1, lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self n)⟩
    let βn : F ⋙ X⦅(n - i.1)⦆ ⟶ F' ⋙ X⦅(n - i.1)⦆ :=
      eqToHom ((congrArg (fun Z : C ⥤ C ↦ F ⋙ Z)
        (hX.obj_eq (n - i.1))).symm) ≫
        β.left.app (Opposite.op (SimplexCategory.mk (n - i.1))) ≫
          eqToHom (congrArg (fun Z : C ⥤ C ↦ F' ⋙ Z)
            (hX.obj_eq (n - i.1)))
    let αi : X⦅i.1⦆ ⋙ G ⟶ X⦅i.1⦆ ⋙ G' :=
      eqToHom ((congrArg (fun Z : C ⥤ C ↦ Z ⋙ G)
        (hX.obj_eq i.1)).symm) ≫
        α.left.app (Opposite.op (SimplexCategory.mk i.1)) ≫
          eqToHom (congrArg (fun Z : C ⥤ C ↦ Z ⋙ G')
            (hX.obj_eq i.1))
    eqToHom (congrArg (fun Z : C ⥤ C ↦ (F ⋙ Z) ⋙ G)
      (hX.obj_eq n)) ≫
      whiskerRight (whiskerLeft F (s^⦅n, j⦆)) G ≫
      whiskerRight (whiskerLeft F (iteratedEndofunctorSplitIso n i).hom) G ≫
      whiskerRight (Functor.associator F X⦅(n - i.1)⦆ X⦅i.1⦆).inv G ≫
      (Functor.associator (F ⋙ X⦅(n - i.1)⦆) X⦅i.1⦆ G).hom ≫
      (βn ◫ αi) ≫
      (Functor.associator (F' ⋙ X⦅(n - i.1)⦆) X⦅i.1⦆ G').inv ≫
      whiskerRight (Functor.associator F' X⦅(n - i.1)⦆ X⦅i.1⦆).hom G' ≫
      whiskerRight (whiskerLeft F' (iteratedEndofunctorSplitIso n i).inv) G' ≫
        eqToHom ((congrArg (fun Z : C ⥤ C ↦ (F' ⋙ Z) ⋙ G')
          (hX.obj_eq (n + 1))).symm)
  h_zero_comp_δ_zero n := by
    -- TODO: after rewriting the zero split by `iteratedEndofunctorSplitIso_zero_hom`, the
    -- endpoint still needs a dedicated normalization lemma that turns the terminal
    -- `F'.whiskerLeft ((prePostcomposeAugmented _ _ _).left.δ 0)` factor into the whiskered
    -- augmentation map so that `SimplicialObject.Augmented.w₀` for `α` and `β` can fire.
    sorry
  h_last_comp_δ_last n := by
    -- TODO: rewrite the extremal split for `i = Fin.last n`, move `δ (Fin.last (n + 1))` to the
    -- left block, collapse the endpoint degeneracy/face pair, and identify the result with the
    -- `(a ⋆ b_n)` endpoint.
    sorry
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    -- TODO: use the right-block face split formula forced by `hij : i ≤ j.castSucc`, then apply
    -- `SimplicialObject.δ_naturality` for `β.left` on the transported left block.
    sorry
  h_succ_comp_δ_castSucc_succ j := by
    -- TODO: rewrite both sides through the split at the boundary index and compare them after the
    -- two standard simplicial identities `δ_comp_σ_self` and `δ_comp_σ_succ`.
    sorry
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    -- TODO: use the complementary left-block face split formula forced by `hji : j.castSucc < i`,
    -- then apply `SimplicialObject.δ_naturality` for `α.left` on the transported right block.
    sorry
  h_comp_σ_castSucc_of_le i j hij := by
    -- TODO: rewrite the degeneracy map into the left block using `hij : i ≤ j`, then use
    -- `SimplicialObject.σ_naturality` together with the split-degeneracy transport lemma.
    sorry
  h_comp_σ_succ_of_lt i j hji := by
    -- TODO: rewrite the degeneracy map into the right block using `hji : j ≤ i`, then use
    -- `SimplicialObject.σ_naturality` together with the complementary split-degeneracy lemma.
    sorry

/-- Lemma 14.33.5: if `X` realizes the iterated endofunctor formulas and `α` and `β` are
morphisms of the associated postcomposed and precomposed augmented simplicial objects, then the
two induced maps on `prePostcomposeAugmented` are homotopic in the zigzag sense. -/
theorem prePostcomposeAugmentedMap_homotopic
    {X : SimplicialObject (C ⥤ C)} (hX : IteratedEndofunctorRealization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α :
      prePostcomposeAugmented (𝟭 C) G (iteratedEndofunctorAugmentation d s hX) ⟶
        prePostcomposeAugmented (𝟭 C) G' (iteratedEndofunctorAugmentation d s hX))
    (β :
      prePostcomposeAugmented F (𝟭 C) (iteratedEndofunctorAugmentation d s hX) ⟶
        prePostcomposeAugmented F' (𝟭 C) (iteratedEndofunctorAugmentation d s hX)) :
    SimplicialObject.Homotopic
      (((whiskeringObj (A ⥤ C) (A ⥤ B) ((whiskeringRight A C B).obj G)).map β |>.left) ≫
        ((whiskeringObj (C ⥤ B) (A ⥤ B) ((whiskeringLeft A C B).obj F')).map α |>.left))
      (((whiskeringObj (C ⥤ B) (A ⥤ B) ((whiskeringLeft A C B).obj F)).map α |>.left) ≫
        ((whiskeringObj (A ⥤ C) (A ⥤ B) ((whiskeringRight A C B).obj G')).map β |>.left)) :=
  Homotopic.of_homotopy (prePostcomposeAugmentedMap_homotopy d s hX α β)

end Iterated

end CategoryTheory

/-! ### Lemma_14_33_6 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject.Augmented
open scoped IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IteratedEndofunctorResolutionWhiskerNotation

/- Source-facing notation for the two standard horizontal whiskerings of an endomorphism
`f : 𝟭 C ⟶ 𝟭 C` with a simplicial endofunctor object `X`. These are the simplicial maps whose
degreewise components are `f ⋆ 1_X` and `1_X ⋆ f`. -/
set_option quotPrecheck false in
scoped notation:81 f:81 " ⋆ₗ " X:82 =>
  Functor.whiskerLeft X ((whiskeringLeft C C C).map f)

set_option quotPrecheck false in
scoped notation:81 X:82 " ⋆ᵣ " f:81 =>
  Functor.whiskerLeft X ((whiskeringRight C C C).map f)

end IteratedEndofunctorResolutionWhiskerNotation

open scoped IteratedEndofunctorResolutionWhiskerNotation

/- Domain-style sampling for Lemma 14.33.6:
- primary domain: simplicial objects of endofunctors, augmented simplicial objects, whiskering of
  natural transformations by endofunctors, and the zigzag homotopy relation on simplicial maps;
- sampled same-kind declarations:
  `Functor.whiskeringLeft`,
  `Functor.whiskeringRight`,
  `Functor.id_hcomp`,
  `Functor.hcomp_id`,
  `prePostcomposeAugmented`,
  `SimplicialObject.Augmented.whiskeringObj`,
  `prePostcomposeAugmentedMap_homotopic`,
  `SimplicialObject.Augmented`;
- best owner abstraction: the primitive owner is the canonical whiskering action of the functors
  `whiskeringLeft C C C` and `whiskeringRight C C C` on the endofunorphism `f : 𝟭 C ⟶ 𝟭 C`; the
  source-facing simplicial maps are obtained by whiskering a simplicial object `X` by those owner
  maps, and for Lemma 14.33.6 the relevant `X` is the canonical iterated endofunctor resolution
  from `Lemma_14_33_2`, while the final homotopy statement is a specialization of the chapter-level
  theorem `prePostcomposeAugmentedMap_homotopic`;
- primitive data: the simplicial identities `hσδ₀`, `hσδ₁`, `hσσ` defining the canonical
  resolution, together with a natural endomorphism `f : 𝟭 C ⟶ 𝟭 C`;
- derived API: the source-facing simplicial endomorphisms
  `f ⋆ₗ X` and `X ⋆ᵣ f`, corresponding degreewise to `f ⋆ 1_X` and `1_X ⋆ f`, the canonical
  augmentation-compatibility squares for the iterated resolution, and the resulting homotopy
  statement.

Source/core/bridge triage:
- `source-facing`: the endomorphisms `f ⋆ 1_X` and `1_X ⋆ f` of the canonical simplicial
  endofunctor resolution arising from the iterated endofunctor construction;
- `core/canonical`: the functorial owner maps `(whiskeringLeft C C C).map f`,
  `(whiskeringRight C C C).map f`, whiskering by `X`, and the augmented pre/postcomposition owner
  API from `Lemma_14_33_5`;
- `bridge/view`: the notation-level source-facing whiskered maps `f ⋆ₗ X` and `X ⋆ᵣ f`, together
  with their augmentation-compatibility squares, which supply the augmented morphisms whose
  induced simplicial maps are obtained directly by `whiskeringObj.map ... |>.left`.
-/

private theorem prePostcomposeAugmented_id_id_hom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    :
    (prePostcomposeAugmented (𝟭 C) (𝟭 C) ε).hom = ε := by
  ext n
  simp [prePostcomposeAugmented]

private def leftStarAugmentedHom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    prePostcomposeAugmented (𝟭 C) (𝟭 C) ε ⟶
      prePostcomposeAugmented (𝟭 C) (𝟭 C) ε :=
  ((SimplicialObject.Augmented.whiskering (C ⥤ C) (C ⥤ C)).map
    ((whiskeringLeft C C C).map f)).app
      { left := X, right := 𝟭 C, hom := ε }

@[simp] private theorem leftStarAugmentedHom_left
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (leftStarAugmentedHom X ε f).left = f ⋆ₗ X := by
  simp [leftStarAugmentedHom]

@[simp] private theorem leftStarAugmentedHom_right
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (leftStarAugmentedHom X ε f).right = f := by
  ext Z
  simp [leftStarAugmentedHom]

private def rightStarAugmentedHom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    prePostcomposeAugmented (𝟭 C) (𝟭 C) ε ⟶
      prePostcomposeAugmented (𝟭 C) (𝟭 C) ε :=
  ((SimplicialObject.Augmented.whiskering (C ⥤ C) (C ⥤ C)).map
    ((whiskeringRight C C C).map f)).app
      { left := X, right := 𝟭 C, hom := ε }

@[simp] private theorem rightStarAugmentedHom_left
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (rightStarAugmentedHom X ε f).left = X ⋆ᵣ f := by
  simp [rightStarAugmentedHom]

@[simp] private theorem rightStarAugmentedHom_right
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (rightStarAugmentedHom X ε f).right = f := by
  ext Z
  simp [rightStarAugmentedHom]

section IteratedResolution

variable {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
local notation "X⦅" n:max "⦆" => Y⦅n⦆
local notation "d^⦅" n ", " j "⦆" => d[Y, d]⦅n, j⦆
local notation "s^⦅" n ", " j "⦆" => s[Y, s]⦅n, j⦆

-- Proof sketch: specialize the generic left-whiskering compatibility square to the canonical
-- iterated endofunctor resolution and its canonical augmentation.
/-- Lemma 14.33.6 (compatibility for `f ⋆ 1_X`): the left-whiskered endomorphism of the canonical
iterated endofunctor resolution is compatible with the augmentation via `f`. -/
theorem iterated_endofunctor_left_star_augmentation_compatible
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    CommSq
      (f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ)
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      ((SimplicialObject.const (C ⥤ C)).map f) := by
  let X := iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ
  let ε := iteratedEndofunctorAugmentation d s
    (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ)
  simpa [X, ε, prePostcomposeAugmented_id_id_hom] using
    CommSq.mk (leftStarAugmentedHom X ε f).w

-- Proof sketch: specialize the generic right-whiskering compatibility square to the canonical
-- iterated endofunctor resolution and its canonical augmentation.
/-- Lemma 14.33.6 (compatibility for `1_X ⋆ f`): the right-whiskered endomorphism of the canonical
iterated endofunctor resolution is compatible with the augmentation via `f`. -/
theorem iterated_endofunctor_right_star_augmentation_compatible
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    CommSq
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f)
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      ((SimplicialObject.const (C ⥤ C)).map f) := by
  let X := iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ
  let ε := iteratedEndofunctorAugmentation d s
    (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ)
  simpa [X, ε, prePostcomposeAugmented_id_id_hom] using
    CommSq.mk (rightStarAugmentedHom X ε f).w

-- Proof sketch: specialize `prePostcomposeAugmentedMap_homotopy` to the augmented simplicial
-- object coming from the canonical iterated endofunctor resolution, taking both source and
-- target functors to be `𝟭 C`. The two required augmented morphisms are the ones determined by
-- the public compatibility theorems above; after identifying the whiskering owners at `𝟭 C` with the
-- original simplicial endofunctor object, the two resulting simplicial maps are
-- `f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ` and
-- `iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f`.
/-- Lemma 14.33.6: for the simplicial endofunctor object arising from `Example 14.33.1` and
`Lemma 14.33.2`, the endomorphisms `f ⋆ 1_X` and `1_X ⋆ f` are homotopic in the zigzag sense. -/
theorem iterated_endofunctor_left_star_right_star_homotopic
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    SimplicialObject.Homotopic
      (f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ)
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f) :=
  sorry

end IteratedResolution

end CategoryTheory
