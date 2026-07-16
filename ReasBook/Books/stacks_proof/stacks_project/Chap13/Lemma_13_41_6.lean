import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_41_3
import stacks_proof.stacks_project.Chap13.Lemma_13_41_4

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.41.6:
- primary domain: existence and uniqueness of finite Postnikov systems in a pretriangulated
  category under stagewise Hom-vanishing;
- inspected owner declarations:
  `PostnikovSystem`,
  `shifted_hom_vanishes_above_successor`,
  `morphism_extends_to_postnikovSystemMorphism`,
  `Pretriangulated.isIso₃_of_isIso₁₂`;
- best owner abstraction:
  `source-facing`: existence of `PostnikovSystem X` and isomorphism between two such systems;
  `core/canonical`: the extension owner `morphism_extends_to_postnikovSystemMorphism` and the
    stagewise distinguished-triangle two-out-of-three theorem
    `Pretriangulated.isIso₃_of_isIso₁₂`;
  `bridge/view`: the triangle-valued view `P.triangle i` of each Postnikov stage;
- primitive-vs-derived split:
  primitive data: the complex `X`, its complexness hypothesis, and the source-facing vanishing
  predicate `shifted_hom_vanishes_above_successor`;
  derived API: existence of an identity-over morphism of Postnikov systems and the resulting
    stagewise isomorphism statement. -/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]
variable {n : ℕ}

open PostnikovSystemMorphism

namespace PostnikovSystemMorphism

open scoped ZeroObject

/-- Helper for Lemma 13.41.6: at the rightmost stage, a morphism of Postnikov systems over the
identity of the underlying complex is an isomorphism because both comparison maps to `X_0` are
isomorphisms. -/
lemma yMap_last_isIso_of_identity
    {X : ComposableArrows D n} {P P' : PostnikovSystem X}
    (ψ : PostnikovSystemMorphism P P' (𝟙 X)) :
    IsIso (ψ.yMap (Fin.last n)) := by
  -- Compare the two rightmost maps to `X_0` and solve for `ψ.yMap` using the target isomorphism.
  have hfactor :
      ψ.yMap (Fin.last n) = P.toX (Fin.last n) ≫ inv (P'.toX (Fin.last n)) := by
    rw [← cancel_mono (P'.toX (Fin.last n))]
    simpa using (ψ.comm_toX_w (Fin.last n)).symm
  rw [hfactor]
  infer_instance

/-- Helper for Lemma 13.41.6: once the later auxiliary component is an isomorphism, the stage
triangle morphism forces the previous auxiliary component to be an isomorphism as well. -/
lemma yMap_castSucc_isIso_of_succ
    {X : ComposableArrows D n} {P P' : PostnikovSystem X}
    (ψ : PostnikovSystemMorphism P P' (𝟙 X)) (i : Fin n)
    [IsIso (ψ.yMap i.succ)] :
    IsIso (ψ.yMap i.castSucc) := by
  let φ : P.triangle i ⟶ P'.triangle i := ψ.triangleMorphism i
  -- The middle component is the identity on `X`, and the third component is the known later
  -- auxiliary isomorphism, so two-out-of-three applies on the distinguished stage triangles.
  have h₁ : IsIso φ.hom₁ :=
    Pretriangulated.isIso₁_of_isIso₂₃ φ
      (P.triangle_distinguished i) (P'.triangle_distinguished i)
      (by simpa [φ, PostnikovSystemMorphism.triangleMorphism] using
        (show IsIso (𝟙 (X.obj i.castSucc)) by infer_instance))
      (by simpa [φ, PostnikovSystemMorphism.triangleMorphism] using
        (show IsIso (ψ.yMap i.succ) by infer_instance))
  simpa [φ, PostnikovSystemMorphism.triangleMorphism] using h₁

-- Proof sketch: for the induced morphism between the stage triangles of `P` and `P'`, the middle
-- component is the identity on `X`, hence an isomorphism. Starting from the rightmost stage, where
-- `toX` is an isomorphism by definition, apply `Pretriangulated.isIso₃_of_isIso₁₂` inductively to
-- the stage triangle morphisms to show that each auxiliary component map `ψ.yMap i` is an
-- isomorphism.
/-- Under the vanishing hypothesis of Lemma 13.41.6 (2), any morphism of Postnikov systems over the
identity of `X` is stagewise an isomorphism on the auxiliary objects. This is the derived
stagewise-isomorphism API attached to the source-facing uniqueness statement. -/
@[stacks 0D83]
theorem yMap_isIso_of_extension_vanishing
    {X : ComposableArrows D n} {P P' : PostnikovSystem X}
    (ψ : PostnikovSystemMorphism P P' (𝟙 X))
    (h : shifted_hom_vanishes_above_successor X.intFamily X.intFamily)
    (i : Fin (n + 1)) : IsIso (ψ.yMap i) := by
  let _ := h
  -- Route correction: the stage-triangle propagation runs from right to left, so the correct
  -- two-out-of-three lemma is `isIso₁_of_isIso₂₃`.
  induction i using Fin.reverseInduction with
  | last =>
      exact yMap_last_isIso_of_identity ψ
  | cast i ih =>
      letI : IsIso (ψ.yMap i.succ) := ih
      exact yMap_castSucc_isIso_of_succ ψ i

end PostnikovSystemMorphism

/-- Helper for Lemma 13.41.6: the owner-level existence-vanishing hypothesis specializes to the
finite-row statement `Hom(X_a[a - b - 2], X_b) = 0` whenever `a + 2 < b`. -/
lemma existence_vanishing_apply
    {n : ℕ} {X : ComposableArrows D n}
    (h : shifted_hom_vanishes_above_successor
      X.intFamily (fun i ↦ X.intFamily (i - 1)))
    {a b : Fin (n + 1)} (hab : a.1 + 2 < b.1) :
    Subsingleton (ShiftedHom (X.obj a) (X.obj b) ((a.1 : ℤ) + 2 - b.1)) := by
  -- Translate the stronger textbook inequality to the shifted owner-level indexing.
  have hshift :
      ((((n - b.1 : ℕ) : ℤ) + 1) + 1 - ((n - a.1 : ℕ) : ℤ)) =
        ((a.1 : ℤ) + 2 - b.1) := by
    omega
  have hsub :
      Subsingleton
        (ShiftedHom
          (X.intFamily (((n - a.1 : ℕ) : ℤ)))
          ((fun i ↦ X.intFamily (i - 1)) (((n - b.1 : ℕ) : ℤ) + 1))
          (((((n - b.1 : ℕ) : ℤ) + 1) + 1 - ((n - a.1 : ℕ) : ℤ)))) :=
    h (show (((n - a.1 : ℕ) : ℤ) > (((n - b.1 : ℕ) : ℤ) + 1) + 1) by omega)
  simpa [ShiftedHom, hshift, X.intFamily_reverse a, X.intFamily_reverse b] using hsub

/-- Helper for Lemma 13.41.6: one reverse-induction step transfers fixed-source vanishing from the
row object `X'_i` and the later auxiliary object `Y_{i - 1}` to the current auxiliary object
`Y_i`. -/
lemma fixed_source_auxiliary_vanishing_step
    {m : ℕ} {X' : ComposableArrows D m} (P : PostnikovSystem X') (W : D) (i : Fin m)
    (hX :
      Subsingleton (ShiftedHom W (X'.obj i.castSucc) ((1 : ℤ) - i.castSucc.1)))
    (hSucc :
      Subsingleton (ShiftedHom W (P i.succ) ((1 : ℤ) - i.succ.1))) :
    Subsingleton (ShiftedHom W (P i.castSucc) ((1 : ℤ) - i.castSucc.1)) := by
  refine ⟨fun f g ↦ ?_⟩
  -- Proof comment: factor each map to `Y_i[(1 - i)]` through `Y_{i - 1}[-i]`, then kill the
  -- factor by the induction-stage vanishing on the later auxiliary object.
  have hkill :
      ∀ f : ShiftedHom W (P i.castSucc) ((1 : ℤ) - i.castSucc.1), f = 0 := by
    intro f
    have hk : ((1 : ℤ) - i.succ.1) + 1 = (1 : ℤ) - i.castSucc.1 := by
      change (1 - ((i.1 : ℤ) + 1)) + 1 = 1 - (i.1 : ℤ)
      ring
    -- Proof comment: the row-object vanishing makes the composite with `X'_i` zero, so the
    -- packaged exactness lemma factors `f` through the connecting morphism.
    have hfzero : f ≫ (P.toX i.castSucc)⟦((1 : ℤ) - i.castSucc.1)⟧' = 0 :=
      hX.elim _ _
    have f' : ShiftedHom W (P i.castSucc) (((1 : ℤ) - i.succ.1) + 1) := by
      simpa [hk] using f
    have hfzero' : f' ≫ (P.toX i.castSucc)⟦(((1 : ℤ) - i.succ.1) + 1)⟧' = 0 := by
      simpa [hk] using hfzero
    have hfactor' :
        ∃ g : ShiftedHom W (P i.succ) ((1 : ℤ) - i.succ.1),
          f' = ShiftedHom.comp g (P.connecting i)
            (shifted_hom_connecting_degree ((1 : ℤ) - i.succ.1)) := by
      exact P.stage_shiftedHom_exact₁_factor (i := i) (W := W)
        (k := (1 : ℤ) - i.succ.1) (f := f') hfzero'
    have hfactor :
        ∃ g : ShiftedHom W (P i.succ) ((1 : ℤ) - i.succ.1),
          f = ShiftedHom.comp g (P.connecting i)
            (shifted_hom_connecting_degree ((1 : ℤ) - i.succ.1)) := by
      simpa [hk] using hfactor'
    obtain ⟨g, hg⟩ := hfactor
    have hgzero : g = 0 := hSucc.elim _ _
    simpa [hgzero] using hg
  rw [hkill f, hkill g]

/-- Helper for Lemma 13.41.6: the source object `X_0` of the long row satisfies the required
two-step vanishing against the truncated tail row. -/
lemma head_source_tail_vanishing
    {m : ℕ} {X : ComposableArrows D (m + 3)}
    (h : ∀ {a b : Fin (m + 4)}, a.1 + 2 < b.1 →
      Subsingleton (ShiftedHom (X.obj a) (X.obj b) ((a.1 : ℤ) + 2 - b.1))) :
    ∀ {b : Fin (m + 3)}, 1 < b.1 →
      Subsingleton (ShiftedHom (X.obj 0) (X.δ₀.obj b) ((1 : ℤ) - b.1)) := by
  intro b hb
  -- Specialize the global vanishing hypothesis at `a = 0` and the successor index in the
  -- original row.
  have hshift : ((0 : ℤ) + 2 - b.succ.1) = ((1 : ℤ) - b.1) := by
    change 2 - ((b.1 : ℤ) + 1) = 1 - (b.1 : ℤ)
    ring
  simpa [ShiftedHom, hshift] using
    (h (a := 0) (b := b.succ) (by simpa [Fin.succ] using hb))

/-- Helper for Lemma 13.41.6: if maps from a fixed source object to the row objects vanish two
steps away, then the same vanishing holds for the auxiliary objects of any Postnikov system on the
row. -/
lemma fixed_source_auxiliary_vanishing
    {m : ℕ} {X' : ComposableArrows D m} (P : PostnikovSystem X') (W : D)
    (hW : ∀ {b : Fin (m + 1)}, 1 < b.1 →
      Subsingleton (ShiftedHom W (X'.obj b) ((1 : ℤ) - b.1))) :
    ∀ {b : Fin (m + 1)}, 1 < b.1 →
      Subsingleton (ShiftedHom W (P b) ((1 : ℤ) - b.1)) := by
  intro b
  induction b using Fin.reverseInduction with
  | last =>
      intro hb
      -- Proof comment: the rightmost auxiliary object is canonically isomorphic to the matching
      -- row object, so transport the known vanishing across `P.toX`.
      let e : P (Fin.last m) ≅ X'.obj (Fin.last m) := by
        simpa using asIso (P.toX (Fin.last m))
      exact subsingleton_shiftedHom_of_iso_target e _ <|
        hW (b := Fin.last m) hb
  | cast i ih =>
      intro hb
      -- Proof comment: one source-style reverse-induction step combines vanishing into the row
      -- object `X'_i` with the induction hypothesis for the later auxiliary object `Y_{i-1}`.
      exact fixed_source_auxiliary_vanishing_step P W i
        (hW (b := i.castSucc) hb)
        (ih (lt_trans hb (Nat.lt_succ_self _)))

/-- Helper for Lemma 13.41.6: in the inductive existence step, the first differential of `X`
lifts through the head triangle of a Postnikov system on the tail complex. -/
lemma head_map_lift_exists
    {m : ℕ} {X : ComposableArrows D (m + 3)} (P : PostnikovSystem X.δ₀) (hX : X.IsComplex)
    (h : ∀ {a b : Fin (m + 4)}, a.1 + 2 < b.1 →
      Subsingleton (ShiftedHom (X.obj a) (X.obj b) ((a.1 : ℤ) + 2 - b.1))) :
    ∃ f : X.obj 0 ⟶ P.head, f ≫ P.headToX = X.map' 0 1 := by
  let α : ShiftedHom (X.obj 0) (P 1) (0 : ℤ) :=
    ShiftedHom.mk₀ (0 : ℤ) rfl (X.map' 0 1 ≫ P.toNext 0)
  -- Proof comment: the obstruction map into `Y_1` vanishes after composing with `X_2`, because
  -- the original row is a complex and `P` recovers the tail differential.
  have hαX : α ≫ (P.toX 1)⟦(0 : ℤ)⟧' = 0 := by
    simpa [α, ShiftedHom.mk₀, Category.assoc, P.comp 0] using hX.zero 0
  -- Proof comment: exactness at the next stage factors the obstruction through `Y_2[-1]`.
  have hαdeg : ShiftedHom (X.obj 0) (P 1) (((-1 : ℤ)) + 1) := by
    simpa using α
  have hαX' : hαdeg ≫ (P.toX 1)⟦(((-1 : ℤ)) + 1)⟧' = 0 := by
    simpa using hαX
  obtain ⟨β, hβ⟩ :=
    P.stage_shiftedHom_exact₁_factor (i := (1 : Fin (m + 2))) (W := X.obj 0) (k := (-1 : ℤ))
      (f := hαdeg) hαX'
  have hβsub : Subsingleton (ShiftedHom (X.obj 0) (P 2) (-1 : ℤ)) := by
    simpa using
      (fixed_source_auxiliary_vanishing (P := P) (W := X.obj 0)
        (hW := head_source_tail_vanishing h) (b := (2 : Fin (m + 3))) (by decide))
  have hβzero : β = 0 := hβsub.elim _ _
  have hαzero : α = 0 := by
    simpa [hβzero] using hβ
  have hcomp_zero : X.map' 0 1 ≫ P.toNext 0 = 0 := by
    exact (ShiftedHom.homEquiv (0 : ℤ) rfl).injective <| by
      simpa [α] using hαzero
  -- Proof comment: once the obstruction into `Y_1` is zero, exactness of the head triangle lifts
  -- `X_0 ⟶ X_1` to a map into the head object.
  obtain ⟨f, hf⟩ := (P.triangle 0).coyoneda_exact₂ (P.triangle_distinguished 0) (X.map' 0 1)
    (by simpa using hcomp_zero)
  exact ⟨f, by simpa using hf⟩

/-- Helper for Lemma 13.41.6: the existence part can be proved directly from the finite-row
two-step vanishing condition by induction on the length of the row. -/
theorem postnikovSystem_exists_of_existence_vanishing_fin :
    ∀ {n : ℕ} (X : ComposableArrows D n), X.IsComplex →
      (∀ {a b : Fin (n + 1)}, a.1 + 2 < b.1 →
        Subsingleton (ShiftedHom (X.obj a) (X.obj b) ((a.1 : ℤ) + 2 - b.1))) →
      Nonempty (PostnikovSystem X)
  | 0, X, _hX, _h => by
      exact length_zero_postnikovSystem_exists X
  | 1, X, _hX, _h => by
      exact length_one_postnikovSystem_exists X
  | 2, X, hX, _h => by
      exact length_two_postnikovSystem_exists X hX
  | n + 3, X, hX, h => by
      -- Recurse on the tail complex, then kill the unique head obstruction by exactness.
      have hδ : X.δ₀.IsComplex := by
        refine ComposableArrows.IsComplex.mk ?_
        intro i hi
        simpa using hX.zero (i + 1)
      obtain ⟨P⟩ :=
        postnikovSystem_exists_of_existence_vanishing_fin X.δ₀ hδ (by
          intro a b hab
          have hshift : ((a.succ.1 : ℤ) + 2 - b.succ.1) = ((a.1 : ℤ) + 2 - b.1) := by
            change (((a.1 : ℤ) + 1) + 2 - ((b.1 : ℤ) + 1)) = (a.1 : ℤ) + 2 - b.1
            ring
          simpa [ShiftedHom, hshift] using (h (a := a.succ) (b := b.succ) (by omega)))
      obtain ⟨f, hf⟩ := head_map_lift_exists P hX h
      obtain ⟨Y, toX, connecting, hT⟩ := Pretriangulated.distinguished_cocone_triangle₁ f
      exact ⟨PostnikovSystem.mkSucc P Y toX f connecting hT hf⟩

-- Proof sketch: induct on the length `n`. The cases `n = 0, 1, 2` are Lemma 13.41.3. For the
-- inductive step, choose a Postnikov system on the tail complex, use the long exact Hom sequence
-- of the last distinguished triangle to reduce extension to a vanishing statement for
-- `Hom(X_n, Y_{n - 3}[-1])`, and then deduce that vanishing from the stated hypothesis exactly as
-- in Lemma 13.41.4 (1).
/-- Lemma 13.41.6 (1): if `X` is a finite complex and `Hom(X_i[i - j - 2], X_j) = 0` for
`i > j + 2`, then `X` admits a Postnikov system. This is expressed via the owner hypothesis
`shifted_hom_vanishes_above_successor X.intFamily (fun i ↦ X.intFamily (i - 1))`. -/
@[stacks 0D83]
theorem postnikovSystem_exists_of_existence_vanishing
    (X : ComposableArrows D n) (hX : X.IsComplex)
    (h : shifted_hom_vanishes_above_successor
      X.intFamily (fun i ↦ X.intFamily (i - 1))) :
    Nonempty (PostnikovSystem X) := by
  -- Convert the owner-level hypothesis to the finite-row form used by the induction.
  apply postnikovSystem_exists_of_existence_vanishing_fin X hX
  intro a b hab
  exact existence_vanishing_apply h hab

-- Proof sketch: Lemma 13.41.4 (2) applied to the identity morphism of `X` gives a morphism
-- `P ⟶ P'`. Applying `Pretriangulated.isIso₃_of_isIso₁₂` to the induced morphism between the
-- stage triangles of `P` and `P'`, and inducting from the rightmost stage where `toX` is an
-- isomorphism by definition, shows that every component map on the auxiliary objects is an
-- isomorphism.
/-- Lemma 13.41.6 (2): if `Hom(X_i[i - j - 1], X_j) = 0` for `i > j + 1`, then any two
Postnikov systems on `X` are isomorphic. The vanishing hypothesis is taken directly in the owner
form `shifted_hom_vanishes_above_successor X.intFamily X.intFamily`. -/
@[stacks 0D83]
theorem postnikovSystem_isomorphic_of_extension_vanishing
    {X : ComposableArrows D n} (P P' : PostnikovSystem X)
    (h : shifted_hom_vanishes_above_successor X.intFamily X.intFamily) :
    ∃ ψ : PostnikovSystemMorphism P P' (𝟙 X), ∀ i, IsIso (ψ.yMap i) := by
  rcases morphism_extends_to_postnikovSystemMorphism P P' (𝟙 X) h with ⟨ψ⟩
  exact ⟨ψ, yMap_isIso_of_extension_vanishing ψ h⟩

end

end CategoryTheory
