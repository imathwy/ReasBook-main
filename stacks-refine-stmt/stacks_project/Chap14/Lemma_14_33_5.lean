import Mathlib
import stacks_project.Chap14.Definition_14_26_1
import stacks_project.Chap14.Lemma_14_33_2
import stacks_project.Chap14.Example_14_33_3

-- Declarations for this item will be appended below by the statement pipeline.

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
