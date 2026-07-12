import Mathlib
import StacksProject_2024.Chap14.Lemma_14_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : Y ⟶ X)
variable [∀ n : ℕ, HasWidePullback (Arrow.mk f).right
  (fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (fun _ ↦ (Arrow.mk f).hom)]

/- Domain-style sampling for Lemma 14.20.3:
- primary domain: augmented simplicial objects, the Čech nerve adjunction, and coskeleta in
  `CategoryTheory.SimplicialObject`;
- sampled owner declarations:
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.augment`,
  `SimplicialObject.cechNerveEquiv`,
  `SimplicialObject.augmentHomEquivZeroSimplex`;
- best owner abstraction: `SimplicialObject.IsCoskeletal` for the `1`-coskeletal statement, together
  with the chapter-level augmentation API from Lemma 14.20.2 for the source-facing
  degree-`0` description of morphisms into the Čech nerve;
- primitive data: the source-facing input is a simplicial morphism
  `V ⟶ (Arrow.mk f).cechNerve`; the compatible degree-`0` morphism `V₀ ⟶ Y` is derived from that
  owner abstraction;
- source/core/bridge triage:
  `source-facing`: the textbook degree-`0` compatibility description of maps into the Čech nerve;
  `core/canonical`: `SimplicialObject.IsCoskeletal`;
  `bridge/view`: the equivalence `cechNerveHomEquivZero` below, obtained from the local fixed-arrow
    universal property and the chapter augmentation equivalence from Lemma 14.20.2.

The local source-facing API should therefore expose the hom-set equivalence directly, rather than
splitting it into a raw function and a separate bijectivity theorem. -/

-- Proof sketch: for a simplicial morphism `g : V ⟶ (Arrow.mk f).cechNerve`, compose the
-- degree-`0` component `g.app (op ⦋0⦌)` with the unique projection from the degree-`0` wide
-- pullback to `Y`. Naturality with respect to the two face maps `δ₀, δ₁ : [0] ⟶ [1]` and the
-- defining pullback relation imply that the two composites to `X` coincide.
/-- The degree-`0` component of a morphism into the Čech nerve satisfies the equalizer relation
coming from the two degree-`1` face maps. -/
theorem cechNerve_degreeZero_condition
    (V : SimplicialObject C) (g : V ⟶ (Arrow.mk f).cechNerve) :
    V.δ 0 ≫ (g.app (op ⦋0⦌) ≫
      WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
      V.δ 1 ≫ (g.app (op ⦋0⦌) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f := by
  simpa [Category.assoc, WidePullback.π_arrow] using
    augmentation_zero_simplex_face_condition
      (g ≫ (Arrow.mk f).augmentedCechNerve.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse direction of `cechNerveHomEquivZero`, built from the augmentation owner together
with the fixed-arrow Čech nerve universal property. -/
private noncomputable def cechNerveHomFromZero
    (V : SimplicialObject C)
    (e : { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f }) :
    V ⟶ (Arrow.mk f).cechNerve where
  app n :=
    WidePullback.lift
      ((V.augment X (e.1 ≫ f) (zero_simplex_face_condition_all_maps (e.1 ≫ f) e.2)).hom.app n)
      (fun i ↦ V.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫ e.1)
      (fun i ↦ by
        simpa [Category.assoc] using
          zero_simplex_face_condition_all_maps (e.1 ≫ f) e.2 (unop n)
            (SimplexCategory.const ⦋0⦌ (unop n) i)
            (SimplexCategory.const ⦋0⦌ (unop n) 0))
  naturality := by
    intro n m α
    let _ : HasWidePullback X (fun _ : Fin ((unop m).len + 1) ↦ Y) (fun _ ↦ f) :=
      ‹∀ n : ℕ, HasWidePullback (Arrow.mk f).right
        (fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (fun _ ↦ (Arrow.mk f).hom)› (unop m).len
    apply WidePullback.hom_ext
    · intro i
      dsimp [CategoryTheory.Arrow.cechNerve]
      simp only [WidePullback.lift_π, Category.assoc]
      have hconst :
          α ≫ (SimplexCategory.const ⦋0⦌ (unop m) i).op =
            (SimplexCategory.const ⦋0⦌ (unop n) (α.unop.toOrderHom i)).op := by
        exact congrArg Quiver.Hom.op (SimplexCategory.const_comp ⦋0⦌ α.unop i)
      calc
        V.map α ≫ (V.map (SimplexCategory.const ⦋0⦌ (unop m) i).op ≫ e.1)
            = V.map (α ≫ (SimplexCategory.const ⦋0⦌ (unop m) i).op) ≫ e.1 := by
                rw [Functor.map_comp, Category.assoc]
        _ = V.map (SimplexCategory.const ⦋0⦌ (unop n) (α.unop.toOrderHom i)).op ≫ e.1 := by
              rw [hconst]
    · have hnat := NatTrans.naturality
          ((V.augment X (e.1 ≫ f) (zero_simplex_face_condition_all_maps (e.1 ≫ f) e.2)).hom) α
      simpa [SimplicialObject.augment] using hnat

@[simp]
private theorem cechNerveHomFromZero_app_zero_pi
    (V : SimplicialObject C)
    (e : { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f }) :
    (cechNerveHomFromZero f V e).app (op ⦋0⦌) ≫
      WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 = e.1 := by
  dsimp [cechNerveHomFromZero, SimplicialObject.augment]
  rw [WidePullback.lift_π]
  simp

private theorem augment_eq_comp_augmentedCechNerve_hom
    (V : SimplicialObject C) (g : V ⟶ (Arrow.mk f).cechNerve) :
    (V.augment X
        (g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f)
        (zero_simplex_face_condition_all_maps
          (g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f)
          (by
            simpa [Category.assoc] using cechNerve_degreeZero_condition f V g))).hom =
      g ≫ (Arrow.mk f).augmentedCechNerve.hom := by
  apply (augmentHomEquivZeroSimplex V X).injective
  apply Subtype.ext
  simp [WidePullback.π_arrow]

private theorem cechNerveHomFromZero_toFun
    (V : SimplicialObject C) (g : V ⟶ (Arrow.mk f).cechNerve) :
    cechNerveHomFromZero f V
        ⟨g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
          cechNerve_degreeZero_condition f V g⟩ =
      g := by
  let e : { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f } :=
    ⟨g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
      cechNerve_degreeZero_condition f V g⟩
  apply SimplicialObject.hom_ext
  intro n
  let _ : HasWidePullback X (fun _ : Fin ((unop n).len + 1) ↦ Y) (fun _ ↦ f) :=
    ‹∀ n : ℕ, HasWidePullback (Arrow.mk f).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (fun _ ↦ (Arrow.mk f).hom)› (unop n).len
  apply WidePullback.hom_ext
  · intro i
    have hnat :=
      g.naturality (SimplexCategory.const ⦋0⦌ (unop n) i).op
    dsimp [cechNerveHomFromZero]
    rw [WidePullback.lift_π]
    calc
      V.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫ e.1
          = g.app n ≫
              (Arrow.mk f).cechNerve.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫
                WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
              simpa [e, Category.assoc] using
                congrArg (fun k ↦ k ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) hnat
      _ = g.app n ≫ WidePullback.π (fun _ : Fin ((unop n).len + 1) ↦ (Arrow.mk f).hom) i := by
        have hπ :
            (Arrow.mk f).cechNerve.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫
              WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
            WidePullback.π (fun _ : Fin ((unop n).len + 1) ↦ (Arrow.mk f).hom) i := by
          dsimp [CategoryTheory.Arrow.cechNerve]
          rw [WidePullback.lift_π]
        simpa [Category.assoc] using congrArg (g.app n ≫ ·) hπ
  · dsimp [cechNerveHomFromZero]
    rw [WidePullback.lift_base]
    simpa [e] using
      congrArg (fun η ↦ η.app n) (augment_eq_comp_augmentedCechNerve_hom f V g)

/-- Morphisms from `V` to the Čech nerve of `f` are canonically equivalent to degree-`0`
morphisms `g₀ : V₀ ⟶ Y` whose composites with the two face maps `V₁ ⇉ V₀` agree after composing
with `f`. -/
noncomputable def cechNerveHomEquivZero
    (V : SimplicialObject C) :
    (V ⟶ (Arrow.mk f).cechNerve) ≃
      { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f } where
  toFun g :=
    ⟨g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
      cechNerve_degreeZero_condition f V g⟩
  invFun := cechNerveHomFromZero f V
  left_inv := by
    intro g
    exact cechNerveHomFromZero_toFun f V g
  right_inv := by
    intro e
    apply Subtype.ext
    exact cechNerveHomFromZero_app_zero_pi f V e

/-- The forward map of `cechNerveHomEquivZero` sends a simplicial morphism to its degree-`0`
component composed with the canonical projection from the `0`-simplices of the Čech nerve to `Y`.
-/
@[simp]
theorem cechNerveHomEquivZero_apply
    (V : SimplicialObject C) (g : V ⟶ (Arrow.mk f).cechNerve) :
    cechNerveHomEquivZero f V g =
      ⟨g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
        cechNerve_degreeZero_condition f V g⟩ := rfl

/-- The inverse map of `cechNerveHomEquivZero` recovers the prescribed degree-`0` morphism after
composing with the canonical projection from the `0`-simplices of the Čech nerve to `Y`. -/
@[simp]
theorem cechNerveHomEquivZero_symm_apply_zero_pi
    (V : SimplicialObject C)
    (e : { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f }) :
    ((cechNerveHomEquivZero f V).symm e).app (op ⦋0⦌) ≫
      WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 = e.1 := by
  exact cechNerveHomFromZero_app_zero_pi f V e

/-- Helper for Lemma 14.20.3: the degree-`0` object of the `1`-truncated simplex category. -/
private abbrev truncSimplexZero : SimplexCategory.Truncated 1 :=
  ⟨⦋0⦌, by decide⟩

/-- Helper for Lemma 14.20.3: the degree-`1` object of the `1`-truncated simplex category. -/
private abbrev truncSimplexOne : SimplexCategory.Truncated 1 :=
  ⟨⦋1⦌, by decide⟩

/-- Helper for Lemma 14.20.3: every object of `Δ≤1` is either `[0]` or `[1]`. -/
private theorem truncated_simplex_eq_zero_or_one (Δ : SimplexCategory.Truncated 1) :
    Δ = truncSimplexZero ∨ Δ = truncSimplexOne := by
  rcases Δ with ⟨⟨n⟩, hΔ⟩
  change n ≤ 1 at hΔ
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl <;> simp [truncSimplexZero, truncSimplexOne]

/-- Helper for Lemma 14.20.3: every object of `(Δ≤1)ᵒᵖ` is the opposite of `[0]` or `[1]`. -/
private theorem truncated_op_simplex_eq_zero_or_one
    (Δ : (SimplexCategory.Truncated 1)ᵒᵖ) :
    Δ = op truncSimplexZero ∨ Δ = op truncSimplexOne := by
  rcases truncated_simplex_eq_zero_or_one (unop Δ) with h | h
  · left
    exact congrArg op h
  · right
    exact congrArg op h

/-- Helper for Lemma 14.20.3: on a `1`-truncated simplicial object, compatibility with the two
face maps already forces compatibility with every map out of `[0]`. -/
private theorem truncated_zero_simplex_face_condition_all_maps
    (W : SimplicialObject.Truncated C 1) {Z : C}
    (ε₀ : W.obj (op truncSimplexZero) ⟶ Z)
    (hε₀ :
      W.map (SimplexCategory.Truncated.δ 1 (0 : Fin 2)).op ≫ ε₀ =
        W.map (SimplexCategory.Truncated.δ 1 (1 : Fin 2)).op ≫ ε₀)
    (Δ : SimplexCategory.Truncated 1) (g₁ g₂ : truncSimplexZero ⟶ Δ) :
    W.map g₁.op ≫ ε₀ = W.map g₂.op ≫ ε₀ := by
  -- Only `[0]` and `[1]` occur in `Δ≤1`, so the statement reduces to a finite case split.
  rcases truncated_simplex_eq_zero_or_one Δ with rfl | rfl
  · have hg₁ :
        g₁ = 𝟙 truncSimplexZero := by
      apply ObjectProperty.hom_ext _
      simpa [SimplexCategory.const_eq_id] using SimplexCategory.eq_const_to_zero g₁.hom
    have hg₂ :
        g₂ = 𝟙 truncSimplexZero := by
      apply ObjectProperty.hom_ext _
      simpa [SimplexCategory.const_eq_id] using SimplexCategory.eq_const_to_zero g₂.hom
    rw [hg₁, hg₂]
  · have hδ₀ :
        SimplexCategory.Truncated.δ 1 (0 : Fin 2) =
          SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
      decide
    have hδ₁ :
        SimplexCategory.Truncated.δ 1 (1 : Fin 2) =
          SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) := by
      decide
    obtain ⟨i₁, hg₁⟩ :
        ∃ i : Fin 2,
          g₁ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) := by
      refine ⟨g₁.hom.toOrderHom 0, ?_⟩
      apply ObjectProperty.hom_ext _
      simpa using SimplexCategory.eq_const_of_zero g₁.hom
    obtain ⟨i₂, hg₂⟩ :
        ∃ i : Fin 2,
          g₂ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) := by
      refine ⟨g₂.hom.toOrderHom 0, ?_⟩
      apply ObjectProperty.hom_ext _
      simpa using SimplexCategory.eq_const_of_zero g₂.hom
    fin_cases i₁ <;> fin_cases i₂
    · have hg₁' : g₁ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) := by
        simpa using hg₁
      have hg₂' : g₂ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) := by
        simpa using hg₂
      rw [hg₁', hg₂']
    · have hg₁' : g₁ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) := by
        simpa using hg₁
      have hg₂' : g₂ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
        simpa using hg₂
      rw [hg₁', hg₂', ← hδ₁, ← hδ₀]
      exact hε₀.symm
    · have hg₁' : g₁ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
        simpa using hg₁
      have hg₂' : g₂ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) := by
        simpa using hg₂
      rw [hg₁', hg₂', ← hδ₀, ← hδ₁]
      exact hε₀
    · have hg₁' : g₁ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
        simpa using hg₁
      have hg₂' : g₂ = SimplexCategory.Truncated.Hom.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
        simpa using hg₂
      rw [hg₁', hg₂']

/-- Helper for Lemma 14.20.3: the first truncated face map of the Čech nerve is the projection to
the second factor of the degree-`1` fiber product. -/
private theorem truncated_cechNerve_face_zero_projection :
    ((truncation 1).obj ((Arrow.mk f).cechNerve)).map
        (SimplexCategory.Truncated.δ 1 (0 : Fin 2)).op ≫
      WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
    WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1 := by
  -- Route correction: first rewrite the truncated face map through the inclusion `Δ≤1 ⥤ Δ`,
  -- then the Čech nerve face map is exactly the explicit constant-map projection from the source.
  change
      (Arrow.mk f).cechNerve.map
          (((SimplexCategory.Truncated.inclusion 1).op.map
              (SimplexCategory.Truncated.δ 1 (0 : Fin 2)).op)) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
      WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1
  change
      (Arrow.mk f).cechNerve.map
          (((SimplexCategory.Truncated.inclusion 1).map
              (SimplexCategory.Truncated.δ 1 (0 : Fin 2))).op) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
      WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1
  have hδ :
      (SimplexCategory.Truncated.inclusion 1).map
          (SimplexCategory.Truncated.δ 1 (0 : Fin 2)) =
        SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 := by
    decide
  rw [hδ]
  dsimp [CategoryTheory.Arrow.cechNerve]
  rw [WidePullback.lift_π]

/-- Helper for Lemma 14.20.3: the second truncated face map of the Čech nerve is the projection to
the first factor of the degree-`1` fiber product. -/
private theorem truncated_cechNerve_face_one_projection :
    ((truncation 1).obj ((Arrow.mk f).cechNerve)).map
        (SimplexCategory.Truncated.δ 1 (1 : Fin 2)).op ≫
      WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
    WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 := by
  -- As above, we first identify the truncated face map with the corresponding constant map in `Δ`.
  change
      (Arrow.mk f).cechNerve.map
          (((SimplexCategory.Truncated.inclusion 1).op.map
              (SimplexCategory.Truncated.δ 1 (1 : Fin 2)).op)) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
      WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0
  change
      (Arrow.mk f).cechNerve.map
          (((SimplexCategory.Truncated.inclusion 1).map
              (SimplexCategory.Truncated.δ 1 (1 : Fin 2))).op) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
      WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0
  have hδ :
      (SimplexCategory.Truncated.inclusion 1).map
          (SimplexCategory.Truncated.δ 1 (1 : Fin 2)) =
        SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 := by
    decide
  rw [hδ]
  dsimp [CategoryTheory.Arrow.cechNerve]
  rw [WidePullback.lift_π]

/-- Helper for Lemma 14.20.3: at degree `1`, postcomposing either Čech-nerve projection with `f`
is the same as the wide-pullback base map after any incoming morphism. -/
private theorem truncated_cechNerve_one_pi_arrow_assoc
    {A : C}
    (g : A ⟶ ((truncation 1).obj ((Arrow.mk f).cechNerve)).obj (op truncSimplexOne))
    (i : Fin 2) :
    g ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) i ≫ f =
      g ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
  -- Degree-`1` simplices of the Čech nerve are exactly the two-fold pullback, so the universal
  -- projection identity can be used after reassociation.
  simpa only [Category.assoc] using
    congrArg
      (fun t ↦ g ≫ t)
      (WidePullback.π_arrow (arrows := fun _ : Fin 2 ↦ (Arrow.mk f).hom) i)

/-- Helper for Lemma 14.20.3: a morphism into the `1`-truncation of the Čech nerve yields the
same degree-`0` compatibility condition as in the full simplicial object. -/
private theorem truncated_cechNerve_degree_zero_condition
    (W : SimplicialObject.Truncated C 1)
    (γ : W ⟶ (truncation 1).obj ((Arrow.mk f).cechNerve)) :
    W.map (SimplexCategory.Truncated.δ 1 (0 : Fin 2)).op ≫
        (γ.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
      W.map (SimplexCategory.Truncated.δ 1 (1 : Fin 2)).op ≫
        (γ.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f := by
  -- Naturality along the two face maps rewrites both source composites to the same degree-`1`
  -- morphism into `X`, namely the base map of the degree-`1` wide pullback.
  let δ₀ : truncSimplexZero ⟶ truncSimplexOne := SimplexCategory.Truncated.δ 1 (0 : Fin 2)
  let δ₁ : truncSimplexZero ⟶ truncSimplexOne := SimplexCategory.Truncated.δ 1 (1 : Fin 2)
  have hδ₀ :
      W.map δ₀.op ≫ (γ.app (op truncSimplexZero) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
        γ.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
    calc
      W.map δ₀.op ≫
          (γ.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
        (W.map δ₀.op ≫ γ.app (op truncSimplexZero)) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f := by
            simp [Category.assoc]
      _ =
        (γ.app (op truncSimplexOne) ≫
            ((truncation 1).obj ((Arrow.mk f).cechNerve)).map δ₀.op) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f := by
            rw [NatTrans.naturality γ δ₀.op]
      _ = γ.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
            calc
              (γ.app (op truncSimplexOne) ≫
                  ((truncation 1).obj ((Arrow.mk f).cechNerve)).map δ₀.op) ≫
                    WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f =
                γ.app (op truncSimplexOne) ≫
                  WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1 ≫ f := by
                    simpa [δ₀, Category.assoc] using
                      congrArg
                        (fun k ↦ γ.app (op truncSimplexOne) ≫ k ≫ f)
                        (truncated_cechNerve_face_zero_projection (f := f))
              _ = γ.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
                    -- The remaining step is exactly the reassociated wide-pullback projection
                    -- identity packaged in `truncated_cechNerve_one_pi_arrow_assoc`.
                    simpa using
                      truncated_cechNerve_one_pi_arrow_assoc (f := f)
                        (g := γ.app (op truncSimplexOne)) (i := (1 : Fin 2))
  have hδ₁ :
      W.map δ₁.op ≫ (γ.app (op truncSimplexZero) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
        γ.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
    calc
      W.map δ₁.op ≫
          (γ.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
        (W.map δ₁.op ≫ γ.app (op truncSimplexZero)) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f := by
            simp [Category.assoc]
      _ =
        (γ.app (op truncSimplexOne) ≫
            ((truncation 1).obj ((Arrow.mk f).cechNerve)).map δ₁.op) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f := by
            rw [NatTrans.naturality γ δ₁.op]
      _ = γ.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
            calc
              (γ.app (op truncSimplexOne) ≫
                  ((truncation 1).obj ((Arrow.mk f).cechNerve)).map δ₁.op) ≫
                    WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f =
                γ.app (op truncSimplexOne) ≫
                  WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 ≫ f := by
                    simpa [δ₁, Category.assoc] using
                      congrArg
                        (fun k ↦ γ.app (op truncSimplexOne) ≫ k ≫ f)
                        (truncated_cechNerve_face_one_projection (f := f))
              _ = γ.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
                    -- The second branch uses the same reassociated projection-to-base identity.
                    simpa using
                      truncated_cechNerve_one_pi_arrow_assoc (f := f)
                        (g := γ.app (op truncSimplexOne)) (i := (0 : Fin 2))
  exact hδ₀.trans hδ₁.symm

/-- Helper for Lemma 14.20.3: a morphism from the `1`-truncation of a simplicial object into the
truncated Čech nerve is determined by its degree-`0` projection to `Y`. -/
private theorem truncated_cechNerve_hom_ext
    (V : SimplicialObject C)
    {γ₁ γ₂ : (truncation 1).obj V ⟶ (truncation 1).obj ((Arrow.mk f).cechNerve)}
    (h₀ :
      γ₁.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
        γ₂.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) :
    γ₁ = γ₂ := by
  -- The source proof says the degree-`1` classifier is recovered from the degree-`0` one by the
  -- two face maps; once the two projections agree, every component in `Δ≤1` agrees.
  let δ₀ : truncSimplexZero ⟶ truncSimplexOne := SimplexCategory.Truncated.δ 1 (0 : Fin 2)
  let δ₁ : truncSimplexZero ⟶ truncSimplexOne := SimplexCategory.Truncated.δ 1 (1 : Fin 2)
  have hγ₁π₀ :
      ((truncation 1).obj V).map δ₁.op ≫
          (γ₁.app (op truncSimplexZero) ≫
            WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) =
        γ₁.app (op truncSimplexOne) ≫
          WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 := by
    calc
      ((truncation 1).obj V).map δ₁.op ≫
          (γ₁.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) =
        (((truncation 1).obj V).map δ₁.op ≫ γ₁.app (op truncSimplexZero)) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
            simp [Category.assoc]
      _ =
        (γ₁.app (op truncSimplexOne) ≫
            ((truncation 1).obj ((Arrow.mk f).cechNerve)).map δ₁.op) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
            rw [NatTrans.naturality γ₁ δ₁.op]
      _ = γ₁.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 := by
            simpa [δ₁, Category.assoc] using
              congrArg
                (fun k ↦ γ₁.app (op truncSimplexOne) ≫ k)
                (truncated_cechNerve_face_one_projection (f := f))
  have hγ₂π₀ :
      ((truncation 1).obj V).map δ₁.op ≫
          (γ₂.app (op truncSimplexZero) ≫
            WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) =
        γ₂.app (op truncSimplexOne) ≫
          WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 := by
    calc
      ((truncation 1).obj V).map δ₁.op ≫
          (γ₂.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) =
        (((truncation 1).obj V).map δ₁.op ≫ γ₂.app (op truncSimplexZero)) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
            simp [Category.assoc]
      _ =
        (γ₂.app (op truncSimplexOne) ≫
            ((truncation 1).obj ((Arrow.mk f).cechNerve)).map δ₁.op) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
            rw [NatTrans.naturality γ₂ δ₁.op]
      _ = γ₂.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 := by
            simpa [δ₁, Category.assoc] using
              congrArg
                (fun k ↦ γ₂.app (op truncSimplexOne) ≫ k)
                (truncated_cechNerve_face_one_projection (f := f))
  have hγ₁π₁ :
      ((truncation 1).obj V).map δ₀.op ≫
          (γ₁.app (op truncSimplexZero) ≫
            WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) =
        γ₁.app (op truncSimplexOne) ≫
          WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1 := by
    calc
      ((truncation 1).obj V).map δ₀.op ≫
          (γ₁.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) =
        (((truncation 1).obj V).map δ₀.op ≫ γ₁.app (op truncSimplexZero)) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
            simp [Category.assoc]
      _ =
        (γ₁.app (op truncSimplexOne) ≫
            ((truncation 1).obj ((Arrow.mk f).cechNerve)).map δ₀.op) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
            rw [NatTrans.naturality γ₁ δ₀.op]
      _ = γ₁.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1 := by
            simpa [δ₀, Category.assoc] using
              congrArg
                (fun k ↦ γ₁.app (op truncSimplexOne) ≫ k)
                (truncated_cechNerve_face_zero_projection (f := f))
  have hγ₂π₁ :
      ((truncation 1).obj V).map δ₀.op ≫
          (γ₂.app (op truncSimplexZero) ≫
            WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) =
        γ₂.app (op truncSimplexOne) ≫
          WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1 := by
    calc
      ((truncation 1).obj V).map δ₀.op ≫
          (γ₂.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) =
        (((truncation 1).obj V).map δ₀.op ≫ γ₂.app (op truncSimplexZero)) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
            simp [Category.assoc]
      _ =
        (γ₂.app (op truncSimplexOne) ≫
            ((truncation 1).obj ((Arrow.mk f).cechNerve)).map δ₀.op) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
            rw [NatTrans.naturality γ₂ δ₀.op]
      _ = γ₂.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1 := by
            simpa [δ₀, Category.assoc] using
              congrArg
                (fun k ↦ γ₂.app (op truncSimplexOne) ≫ k)
                (truncated_cechNerve_face_zero_projection (f := f))
  ext Δ
  rcases truncated_op_simplex_eq_zero_or_one Δ with rfl | rfl
  · -- On `[0]`, the target is the one-fold wide pullback, so the unique projection determines it.
    have hbase₁ :
        γ₁.app (op truncSimplexZero) ≫ WidePullback.base (fun _ : Fin 1 ↦ (Arrow.mk f).hom) =
          (γ₁.app (op truncSimplexZero) ≫
            WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f := by
      calc
        γ₁.app (op truncSimplexZero) ≫ WidePullback.base (fun _ : Fin 1 ↦ (Arrow.mk f).hom) =
          γ₁.app (op truncSimplexZero) ≫
            (WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f) := by
              exact congrArg
                (fun t ↦ γ₁.app (op truncSimplexZero) ≫ t)
                (WidePullback.π_arrow (arrows := fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0).symm
        _ = (γ₁.app (op truncSimplexZero) ≫
              WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f := by
              simp [Category.assoc]
    have hbase₂ :
        (γ₂.app (op truncSimplexZero) ≫
            WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
          γ₂.app (op truncSimplexZero) ≫ WidePullback.base (fun _ : Fin 1 ↦ (Arrow.mk f).hom) := by
      calc
        (γ₂.app (op truncSimplexZero) ≫
            WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
          γ₂.app (op truncSimplexZero) ≫
            (WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f) := by
              simp [Category.assoc]
        _ = γ₂.app (op truncSimplexZero) ≫ WidePullback.base (fun _ : Fin 1 ↦ (Arrow.mk f).hom) := by
              exact congrArg
                (fun t ↦ γ₂.app (op truncSimplexZero) ≫ t)
                (WidePullback.π_arrow (arrows := fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0)
    apply WidePullback.hom_ext
    · intro j
      fin_cases j
      simpa using h₀
    · have hmid :
          (γ₁.app (op truncSimplexZero) ≫
              WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
            (γ₂.app (op truncSimplexZero) ≫
              WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f) h₀
      exact Eq.trans hbase₁ (Eq.trans hmid hbase₂)
  · -- On `[1]`, the two projections are read off from the two truncated face maps.
    have hbase₁ :
        γ₁.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) =
          (γ₁.app (op truncSimplexOne) ≫
            WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0) ≫ f := by
      calc
        γ₁.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) =
          γ₁.app (op truncSimplexOne) ≫
            (WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 ≫ f) := by
              exact congrArg
                (fun t ↦ γ₁.app (op truncSimplexOne) ≫ t)
                (WidePullback.π_arrow (arrows := fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0).symm
        _ = (γ₁.app (op truncSimplexOne) ≫
              WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0) ≫ f := by
              simp [Category.assoc]
    have hbase₂ :
        (γ₂.app (op truncSimplexOne) ≫
            WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0) ≫ f =
          γ₂.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
      calc
        (γ₂.app (op truncSimplexOne) ≫
            WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0) ≫ f =
          γ₂.app (op truncSimplexOne) ≫
            (WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 ≫ f) := by
              simp [Category.assoc]
        _ = γ₂.app (op truncSimplexOne) ≫ WidePullback.base (fun _ : Fin 2 ↦ (Arrow.mk f).hom) := by
              exact congrArg
                (fun t ↦ γ₂.app (op truncSimplexOne) ≫ t)
                (WidePullback.π_arrow (arrows := fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0)
    apply WidePullback.hom_ext
    · intro j
      fin_cases j
      · calc
          γ₁.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 =
            ((truncation 1).obj V).map δ₁.op ≫
              (γ₁.app (op truncSimplexZero) ≫
                WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) := by
                  simpa [Category.assoc] using hγ₁π₀.symm
        _ =
            ((truncation 1).obj V).map δ₁.op ≫
              (γ₂.app (op truncSimplexZero) ≫
                WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) := by
                  rw [h₀]
        _ = γ₂.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 := by
              simpa [Category.assoc] using hγ₂π₀
      · calc
          γ₁.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1 =
            ((truncation 1).obj V).map δ₀.op ≫
              (γ₁.app (op truncSimplexZero) ≫
                WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) := by
                  simpa [Category.assoc] using hγ₁π₁.symm
        _ =
            ((truncation 1).obj V).map δ₀.op ≫
              (γ₂.app (op truncSimplexZero) ≫
                WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) := by
                  rw [h₀]
        _ = γ₂.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 1 := by
              simpa [Category.assoc] using hγ₂π₁
    · have hπ₀ :
          γ₁.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 =
            γ₂.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 := by
        calc
          γ₁.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 =
            ((truncation 1).obj V).map δ₁.op ≫
              (γ₁.app (op truncSimplexZero) ≫
                WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) := by
                  simpa [Category.assoc] using hγ₁π₀.symm
          _ =
            ((truncation 1).obj V).map δ₁.op ≫
              (γ₂.app (op truncSimplexZero) ≫
                WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) := by
                  rw [h₀]
          _ = γ₂.app (op truncSimplexOne) ≫ WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0 := by
                simpa [Category.assoc] using hγ₂π₀
      have hmid :
          (γ₁.app (op truncSimplexOne) ≫
              WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0) ≫ f =
            (γ₂.app (op truncSimplexOne) ≫
              WidePullback.π (fun _ : Fin 2 ↦ (Arrow.mk f).hom) 0) ≫ f := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f) hπ₀
      exact Eq.trans hbase₁ (Eq.trans hmid hbase₂)

-- Proof sketch: the source-facing classification `cechNerveHomEquivZero` identifies maps into the
-- Čech nerve with compatible degree-`0` data, and the truncated analogue gives the same
-- classification for morphisms into the restricted diagram along `(SimplexCategory.Truncated.inclusion 1).op`.
-- This provides the universal lifting and uniqueness required by the right Kan extension
-- definition of `1`-coskeletality.
/-- Lemma 14.20.3: the Čech nerve of `f : Y ⟶ X` is `1`-coskeletal. Equivalently, it is recovered
from its `1`-truncation by the canonical `1`-coskeleton functor, which is the library-facing form
of the textbook statement that maps into the Čech nerve are determined by compatible degree-`0`
data. -/
@[stacks 018I]
lemma cechNerve_isCoskeletal_one :
    (Arrow.mk f).cechNerve.IsCoskeletal 1 := by
  -- The source proof classifies truncated maps by a single compatible degree-`0` simplex; we
  -- package that datum into the existing full Čech classification and use it to prove terminality.
  rw [SimplicialObject.isCoskeletal_iff]
  constructor
  refine ⟨IsTerminal.ofUniqueHom ?_ ?_⟩
  · intro E
    let e : { g0 : E.left _⦋0⦌ ⟶ Y //
        SimplicialObject.δ E.left 0 ≫ g0 ≫ f = SimplicialObject.δ E.left 1 ≫ g0 ≫ f } :=
      ⟨E.hom.app (op truncSimplexZero) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
        truncated_cechNerve_degree_zero_condition f ((truncation 1).obj E.left) E.hom⟩
    let lift : E.left ⟶ (Arrow.mk f).cechNerve := (cechNerveHomEquivZero f E.left).symm e
    -- The factorization is checked in the truncated category, where the degree-`0` classifier
    -- determines a morphism uniquely.
    refine CostructuredArrow.homMk lift ?_
    change Functor.whiskerLeft (SimplexCategory.Truncated.inclusion 1).op lift ≫ 𝟙 _ = E.hom
    simpa using
      truncated_cechNerve_hom_ext (f := f) E.left
        (γ₁ := Functor.whiskerLeft (SimplexCategory.Truncated.inclusion 1).op lift)
        (γ₂ := E.hom)
        (by
          simpa [e, lift] using cechNerveHomEquivZero_symm_apply_zero_pi (f := f) E.left e)
  · intro E m
    let e : { g0 : E.left _⦋0⦌ ⟶ Y //
        SimplicialObject.δ E.left 0 ≫ g0 ≫ f = SimplicialObject.δ E.left 1 ≫ g0 ≫ f } :=
      ⟨E.hom.app (op truncSimplexZero) ≫
          WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
        truncated_cechNerve_degree_zero_condition f ((truncation 1).obj E.left) E.hom⟩
    let lift : E.left ⟶ (Arrow.mk f).cechNerve := (cechNerveHomEquivZero f E.left).symm e
    apply CostructuredArrow.hom_ext
    -- Uniqueness reduces to the injectivity of the full Čech classifier on the shared degree-`0`
    -- simplex extracted from the factorization equation.
    apply (cechNerveHomEquivZero f E.left).injective
    apply Subtype.ext
    have hm :
        Functor.whiskerLeft (SimplexCategory.Truncated.inclusion 1).op m.left = E.hom := by
      simpa using CostructuredArrow.w m
    have hm₀ :
        m.left.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
          E.hom.app (op truncSimplexZero) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
      simpa [Functor.comp_obj, truncSimplexZero] using
        congrArg
          (fun η ↦ η.app (op truncSimplexZero) ≫
            WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0)
          hm
    simpa [e, lift] using hm₀

end CategoryTheory
