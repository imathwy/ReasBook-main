import Mathlib
import StacksProject_2024.Chap13.Definition_13_9_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ComplexShape HomologicalComplex HomotopyCategory

universe v u

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {A B C D : CochainComplex V ℤ}
variable {f : A ⟶ B} {a : A ⟶ C} {b : B ⟶ D} {g : C ⟶ D}

local notation "Q" => quotient V (up ℤ)

/- Domain-style sampling for Lemma 13.9.5:
- primary domain: homotopy-commutative squares of cochain-complex morphisms together with
  termwise split mono/epi hypotheses on one side of the square;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `HomotopyCategory.quotient`,
  `HomotopyCategory.homotopyOfEq`,
  `CategoryTheory.IsSplitMono`,
  `CategoryTheory.IsSplitEpi`;
- best owner abstraction: the source-facing compatibility datum is a homotopy
  `Homotopy (f ≫ b) (a ≫ g)` between the two composites; the canonical core/view of that datum is
  the square `CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g)` in the homotopy category,
  while the termwise splitting assumptions remain the direct componentwise owners from
  `Definition_13_9_4`;
- primitive data: the four maps `f`, `a`, `b`, `g`, together with the componentwise split
  structure on `f.f n` or `g.f n`, and the chosen homotopy witnessing up-to-homotopy
  commutativity;
- derived API: the quotient-square reformulation of “commutes up to homotopy” via
  `HomotopyCategory.homotopyOfEq`, and equality of quotient classes of a replacement map via
  `HomotopyCategory.eq_of_homotopy`.

Source/core/bridge triage:
- `source-facing`: the two strictification existence lemmas below, phrased as existence of a
  homotopic strictifying replacement with a chosen homotopy
  `Homotopy (f ≫ b) (a ≫ g)`;
- `core/canonical`: `CommSq` for square-shaped compatibility in the homotopy category and the
  per-component owners `IsSplitMono` / `IsSplitEpi`;
- `bridge/view`: the `CommSq` above, formed using the canonical quotient functor `Q`, as the
  homotopy-category reformulation of the source hypothesis, and
  equality of quotient classes via `eq_of_homotopy`.
-/

-- Proof sketch: choose degreewise retractions of the split monomorphism `f`, pick a homotopy
-- between `f ≫ b` and `a ≫ g`, and compose its components with those retractions to obtain a
-- correction term on `B`. Subtracting the associated null-homotopic map from `b` gives a map
-- homotopic to `b` whose composite with `f` is exactly `a ≫ g`.
/-- Helper for Lemma 13.9.5: the degree `-1` family on `B` obtained by pushing the chosen
homotopy across the split retractions of `f`. -/
private abbrev right_strictification_hom
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∀ i j, (ComplexShape.up ℤ).Rel j i → (B.X i ⟶ D.X j) :=
  fun i j _ ↦ @retraction V _ _ _ (f.f i) (hSplitMono i) ≫ hcomm.hom i j

/-- Helper for Lemma 13.9.5: the defect map coming from a homotopy is the canonical
null-homotopic map attached to its degree `-1` components. -/
private theorem homotopy_difference_eq_null_homotopic_map
    (hcomm : Homotopy (f ≫ b) (a ≫ g)) :
    f ≫ b - a ≫ g = Homotopy.nullHomotopicMap' (fun i j _ ↦ hcomm.hom i j) := by
  apply HomologicalComplex.hom_ext
  intro n
  -- Rewrite the null-homotopic map in degree `n` using the predecessor/successor terms.
  rw [Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)
    (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)]
  -- The remaining identity is exactly the defining homotopy relation, rearranged.
  change (f ≫ b).f n - (a ≫ g).f n =
    A.d n (n + 1) ≫ hcomm.hom (n + 1) n + hcomm.hom n (n - 1) ≫ D.d (n - 1) n
  have h := hcomm.comm n
  rw [dNext_eq hcomm.hom (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
    prevD_eq hcomm.hom (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at h
  simpa [sub_eq_iff_eq_add, add_assoc, add_left_comm, add_comm, Category.assoc] using h

/-- Helper for Lemma 13.9.5: the null-homotopic correction on `B` induced by the chosen
retractions of `f`. -/
private abbrev right_strictification_correction
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    B ⟶ D :=
  Homotopy.nullHomotopicMap' (right_strictification_hom (f := f) (a := a) (b := b) (g := g)
    hcomm hSplitMono)

/-- Helper for Lemma 13.9.5: precomposing the correction on `B` with `f` recovers exactly the
defect of commutativity of the original square. -/
private theorem right_strictification_correction_comp
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    f ≫ right_strictification_correction (f := f) (a := a) (b := b) (g := g) hcomm hSplitMono =
      f ≫ b - a ≫ g := by
  -- Push the null-homotopic map across `f`, then collapse the inserted retractions.
  rw [right_strictification_correction, Homotopy.comp_nullHomotopicMap']
  have hfamily :
      (fun i j hij ↦ f.f i ≫ right_strictification_hom (f := f) (a := a) (b := b) (g := g)
        hcomm hSplitMono i j hij) =
        fun i j hij ↦ hcomm.hom i j := by
    funext i
    funext j
    funext hij
    dsimp [right_strictification_hom]
    rw [← Category.assoc, IsSplitMono.id (f.f i), Category.id_comp]
  rw [hfamily]
  exact
    (homotopy_difference_eq_null_homotopic_map (f := f) (a := a) (b := b) (g := g) hcomm).symm

/-- Lemma 13.9.5 (1): if a square of morphisms of cochain complexes commutes up to homotopy and
the top map is termwise split monic, then the right map is homotopic to a morphism making the
square commute strictly. -/
@[stacks 014H]
theorem exists_homotopic_rightMap_of_termwiseSplitMono
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∃ (b' : B ⟶ D) (_ : Homotopy b b'), CommSq f a b' g := by
  let δ : B ⟶ D := right_strictification_correction (f := f) (a := a) (b := b) (g := g)
    hcomm hSplitMono
  let b' : B ⟶ D := b - δ
  have hδ : f ≫ δ = f ≫ b - a ≫ g := by
    simpa [δ] using
      right_strictification_correction_comp (f := f) (a := a) (b := b) (g := g)
        hcomm hSplitMono
  have hbb' : Homotopy b b' := by
    -- The correction is null-homotopic, so subtracting it does not change the homotopy class.
    simpa [b', δ, sub_eq_add_neg] using
      Homotopy.add (Homotopy.refl b)
        ((Homotopy.nullHomotopy'
          (right_strictification_hom (f := f) (a := a) (b := b) (g := g)
            hcomm hSplitMono)).symm.smul (-1 : ℤ))
  have hsq : CommSq f a b' g := by
    refine ⟨?_⟩
    -- Replace the correction term by the original commutativity defect and cancel algebraically.
    calc
      f ≫ b' = f ≫ b - f ≫ δ := by
        simp [b', δ, Preadditive.comp_sub]
      _ = f ≫ b - (f ≫ b - a ≫ g) := by rw [hδ]
      _ = a ≫ g := by abel
  exact ⟨b', hbb', hsq⟩

/-- Bridge/view form of Lemma 13.9.5 (1): if the square commutes in the homotopy category, then
the strictifying replacement may be chosen to represent the same morphism as `b` there. -/
theorem exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono
    (sq : CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∃ b' : B ⟶ D, (Q).map b = (Q).map b' ∧ CommSq f a b' g := by
  obtain ⟨b', hbb', hsq⟩ :=
    exists_homotopic_rightMap_of_termwiseSplitMono
      (homotopyOfEq _ _ (by simpa [Functor.map_comp] using sq.w)) hSplitMono
  exact ⟨b', eq_of_homotopy _ _ hbb', hsq⟩

-- Proof sketch: choose degreewise sections of the split epimorphism `g`, pick a homotopy
-- between `f ≫ b` and `a ≫ g`, and compose its components with those sections to obtain a
-- correction term on `A`. Adding the associated null-homotopic map to `a` gives a map homotopic
-- to `a` whose composite with `g` is exactly `f ≫ b`.
/-- Helper for Lemma 13.9.5: the degree `-1` family on `A` obtained by pushing the chosen
homotopy across the split sections of `g`. -/
private abbrev left_strictification_hom
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∀ i j, (ComplexShape.up ℤ).Rel j i → (A.X i ⟶ C.X j) :=
  fun i j _ ↦ hcomm.hom i j ≫ @section_ V _ _ _ (g.f j) (hSplitEpi j)

/-- Helper for Lemma 13.9.5: the null-homotopic correction on `A` induced by the chosen
sections of `g`. -/
private abbrev left_strictification_correction
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    A ⟶ C :=
  Homotopy.nullHomotopicMap' (left_strictification_hom (f := f) (a := a) (b := b) (g := g)
    hcomm hSplitEpi)

/-- Helper for Lemma 13.9.5: postcomposing the correction on `A` with `g` recovers exactly the
defect of commutativity of the original square. -/
private theorem left_strictification_correction_comp
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    left_strictification_correction (f := f) (a := a) (b := b) (g := g) hcomm hSplitEpi ≫ g =
      f ≫ b - a ≫ g := by
  -- Push the null-homotopic map across `g`, then collapse the inserted sections.
  rw [left_strictification_correction, Homotopy.nullHomotopicMap'_comp]
  have hfamily :
      (fun i j hij ↦ left_strictification_hom (f := f) (a := a) (b := b) (g := g)
        hcomm hSplitEpi i j hij ≫ g.f j) =
        fun i j hij ↦ hcomm.hom i j := by
    funext i
    funext j
    funext hij
    dsimp [left_strictification_hom]
    rw [Category.assoc, IsSplitEpi.id (g.f j), Category.comp_id]
  rw [hfamily]
  exact
    (homotopy_difference_eq_null_homotopic_map (f := f) (a := a) (b := b) (g := g) hcomm).symm

/-- Lemma 13.9.5 (2): if a square of morphisms of cochain complexes commutes up to homotopy and
the bottom map is termwise split epi, then the left map is homotopic to a morphism making the
square commute strictly. -/
@[stacks 014H]
theorem exists_homotopic_leftMap_of_termwiseSplitEpi
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∃ (a' : A ⟶ C) (_ : Homotopy a a'), CommSq f a' b g := by
  let δ : A ⟶ C := left_strictification_correction (f := f) (a := a) (b := b) (g := g)
    hcomm hSplitEpi
  let a' : A ⟶ C := a + δ
  have hδ : δ ≫ g = f ≫ b - a ≫ g := by
    simpa [δ] using
      left_strictification_correction_comp (f := f) (a := a) (b := b) (g := g)
        hcomm hSplitEpi
  have haa' : Homotopy a a' := by
    -- The correction is null-homotopic, so adding it preserves the homotopy class.
    simpa [a', δ] using
      Homotopy.add (Homotopy.refl a)
        (Homotopy.nullHomotopy'
          (left_strictification_hom (f := f) (a := a) (b := b) (g := g)
            hcomm hSplitEpi)).symm
  have hsq : CommSq f a' b g := by
    have hw : a' ≫ g = f ≫ b := by
      -- Replace the correction term by the original commutativity defect and cancel algebraically.
      calc
        a' ≫ g = a ≫ g + δ ≫ g := by
          simp [a', δ, Preadditive.add_comp]
        _ = a ≫ g + (f ≫ b - a ≫ g) := by rw [hδ]
        _ = f ≫ b := by abel
    exact ⟨hw.symm⟩
  exact ⟨a', haa', hsq⟩

/-- Bridge/view form of Lemma 13.9.5 (2): if the square commutes in the homotopy category, then
the strictifying replacement may be chosen to represent the same morphism as `a` there. -/
theorem exists_leftMap_eq_in_homotopyCategory_of_termwiseSplitEpi
    (sq : CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∃ a' : A ⟶ C, (Q).map a = (Q).map a' ∧ CommSq f a' b g := by
  obtain ⟨a', haa', hsq⟩ :=
    exists_homotopic_leftMap_of_termwiseSplitEpi
      (homotopyOfEq _ _ (by simpa [Functor.map_comp] using sq.w)) hSplitEpi
  exact ⟨a', eq_of_homotopy _ _ haa', hsq⟩

end CochainComplex
