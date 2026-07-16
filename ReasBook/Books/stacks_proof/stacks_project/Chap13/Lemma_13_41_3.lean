import stacks_proof.stacks_project.Chap13.Definition_13_41_1
import stacks_proof.stacks_project.Chap13.Lemma_13_4_8
import stacks_proof.stacks_project.Chap13.Lemma_13_9_5
import stacks_proof.stacks_project.Chap13.Remark_13_9_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u v1 u1

namespace CategoryTheory

section

/-
Domain-style sampling for this item:
- primary domain: low-length Postnikov systems in a pretriangulated category;
- inspected canonical owner declarations:
  `PostnikovSystem`,
  `PostnikovSystemMorphism`,
  `CommSq`,
  `PostnikovSystem.mk₀`,
  `ComposableArrows.homMk₀` / `ComposableArrows.hom_ext₀`,
  `ComposableArrows.homMk₁` / `ComposableArrows.hom_ext₁`;
- best owner abstraction: the source-facing objects remain `PostnikovSystem X` and
  `PostnikovSystemMorphism P P' φ`, while the core/canonical low-length bookkeeping is handled by
  the existing `ComposableArrows` owners and the triangle API from `Definition_13_41_1`;
- primitive-vs-derived split:
  primitive data: a Postnikov system and a morphism of Postnikov systems;
  derived API: the length-`0` and length-`1` componentwise descriptions coming from the canonical
    `ComposableArrows` small-length API, the triangle view of a stage of a Postnikov system, and
    the induced complexness of the underlying `ComposableArrows` object.

Source/core/bridge triage:
- source-facing: the existence and uniqueness statements about `PostnikovSystem` and
  `PostnikovSystemMorphism`;
- core/canonical: `ComposableArrows` in lengths `0`, `1`, and `2`, together with the
  distinguished-triangle API;
- bridge/view: identifying the length-`1` case with extending an arrow to a distinguished triangle
  and the length-`0` case with the unique component map on the sole auxiliary object.
-/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

-- Semantic recall note: `lean_leansearch` was attempted for the low-length Postnikov-system API,
-- but the service returned HTTP 500, so the local file and source text remained the authority.
-- Proof sketch: a length-`0` complex is just one object, so the source-facing owner
-- `PostnikovSystem X` is given directly by the canonical base constructor `PostnikovSystem.mk₀`.
/-- Lemma 13.41.3 (1): for length `0`, Postnikov systems always exist. -/
@[stacks 0D81]
theorem length_zero_postnikovSystem_exists (X : ComposableArrows D 0) :
    Nonempty (PostnikovSystem X) :=
  ⟨PostnikovSystem.mk₀ (X.obj 0) (𝟙 (X.obj 0))⟩

-- Proof sketch: for `n = 0`, the only square to satisfy is the compatibility with
-- `Y₀ ⟶ X₀`, so the extension problem is governed by the unique component map in
-- `ComposableArrows D 0`.
/-- Lemma 13.41.3 (2): for length `0`, every morphism of complexes extends to a morphism of
Postnikov systems. -/
@[stacks 0D81]
theorem length_zero_morphism_extension_exists
    {X X' : ComposableArrows D 0} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Nonempty (PostnikovSystemMorphism P P' φ) := by
  let e : P' 0 ≅ X'.obj 0 := by
    simpa using asIso (P'.toX (Fin.last 0))
  let yMap : (i : Fin (0 + 1)) → P i ⟶ P' i := fun i ↦
    match i with
    | ⟨0, _⟩ => P.toX 0 ≫ φ.app 0 ≫ e.inv
  refine ⟨{
    yMap := yMap
    comm_toX := ?_
    comm_toNext := fun i ↦ Fin.elim0 i
    comm_connecting := fun i ↦ Fin.elim0 i
  }⟩
  intro i
  fin_cases i
  refine CommSq.mk ?_
  simp [yMap, e]

-- Proof sketch: for `n = 0`, a morphism of Postnikov systems is determined by its only component
-- on `Y₀`, and the compatibility with `Y₀ ⟶ X₀` forces that component uniquely.
/-- Lemma 13.41.3 (3): for length `0`, the extension of a morphism of complexes to Postnikov
systems is unique. -/
@[stacks 0D81]
theorem length_zero_morphism_extension_subsingleton
    {X X' : ComposableArrows D 0} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Subsingleton (PostnikovSystemMorphism P P' φ) := by
  let e : P' 0 ≅ X'.obj 0 := by
    simpa using asIso (P'.toX (Fin.last 0))
  refine ⟨?_⟩
  intro ψ ψ'
  have h0 : ψ.yMap 0 = ψ'.yMap 0 := by
    have hcomm : ψ.yMap 0 ≫ P'.toX 0 = ψ'.yMap 0 ≫ P'.toX 0 := by
      simpa using (ψ.comm_toX 0).w.symm.trans (ψ'.comm_toX 0).w
    have := congrArg (fun f ↦ f ≫ e.inv) hcomm
    simpa [Category.assoc, e] using this
  have hy : ψ.yMap = ψ'.yMap := by
    funext i
    fin_cases i
    exact h0
  cases ψ
  cases ψ'
  cases hy
  simp

-- Proof sketch: every arrow in a triangulated category extends to a distinguished triangle, and
-- that core triangle owner is exactly the data of a length-`1` Postnikov system.
/-- Lemma 13.41.3 (4): for length `1`, Postnikov systems always exist. -/
@[stacks 0D81]
theorem length_one_postnikovSystem_exists (X : ComposableArrows D 1) :
    Nonempty (PostnikovSystem X) := by
  -- Extend the unique differential of the row to a distinguished triangle.
  obtain ⟨Y, toX, connecting, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle₁ (X.map' 0 1)
  -- The rightmost auxiliary object is just `X.obj 1`, viewed through the base constructor.
  refine ⟨PostnikovSystem.mkSucc (PostnikovSystem.mk₀ (X.δ₀.obj 0) (𝟙 (X.δ₀.obj 0))) Y toX
    (X.map' 0 1) connecting hT ?_⟩
  simp [PostnikovSystem.mk₀]

-- Proof sketch: after choosing distinguished triangles for the two length-`1` Postnikov systems,
-- TR3 extends the given morphism of arrows to a morphism of triangles, hence to a morphism of
-- Postnikov systems.
/-- Lemma 13.41.3 (5): for length `1`, every morphism of complexes extends to a morphism of
Postnikov systems. -/
@[stacks 0D81]
theorem length_one_morphism_extension_exists
    {X X' : ComposableArrows D 1} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') : Nonempty (PostnikovSystemMorphism P P' φ) := by
  let e' : P' 1 ≅ X'.obj 1 := by
    simpa using asIso (P'.toX (Fin.last 1))
  let u1 : P 1 ⟶ P' 1 := P.toX 1 ≫ φ.app 1 ≫ e'.inv
  have hφ : X.map' 0 1 ≫ φ.app 1 = φ.app 0 ≫ X'.map' 0 1 := by
    exact ComposableArrows.naturality' φ 0 1
  -- Compare the known rightmost component against the maps `X₀ ⟶ Y₁`.
  have hnext : P.toNext 0 ≫ u1 = φ.app 0 ≫ P'.toNext 0 := by
    have hnext_toX :
        P.toNext 0 ≫ u1 ≫ e'.hom = φ.app 0 ≫ P'.toNext 0 ≫ e'.hom := by
      have hleft : P.toNext 0 ≫ u1 ≫ e'.hom = X.map' 0 1 ≫ φ.app 1 := by
        calc
          P.toNext 0 ≫ u1 ≫ e'.hom = P.toNext 0 ≫ P.toX 1 ≫ φ.app 1 := by
            simp [u1, Category.assoc]
          _ = X.map' 0 1 ≫ φ.app 1 := by
            simpa [Category.assoc] using congrArg (fun k ↦ k ≫ φ.app 1) (P.comp 0)
      have hright : φ.app 0 ≫ X'.map' 0 1 = φ.app 0 ≫ P'.toNext 0 ≫ e'.hom := by
        simpa [Category.assoc] using congrArg (fun k ↦ φ.app 0 ≫ k) (P'.comp 0).symm
      exact hleft.trans (hφ.trans hright)
    apply (cancel_mono e'.hom).1
    simpa [Category.assoc] using hnext_toX
  -- TR3 now fills in the missing map on the left auxiliary objects.
  obtain ⟨u0, hu0_toX, hu0_connecting⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism₁
      (P.triangle 0) (P'.triangle 0) (P.triangle_distinguished 0) (P'.triangle_distinguished 0)
      (φ.app 0) u1 hnext
  refine ⟨{
    yMap := fun i ↦
      match i with
      | ⟨0, _⟩ => u0
      | ⟨1, _⟩ => u1
    comm_toX := ?_
    comm_toNext := ?_
    comm_connecting := ?_
  }⟩
  · intro i
    fin_cases i
    · exact CommSq.mk hu0_toX
    · refine CommSq.mk ?_
      have hu1_toX_e : u1 ≫ e'.hom = P.toX 1 ≫ φ.app 1 := by
        simp [u1, Category.assoc]
      have hu1_toX : u1 ≫ P'.toX 1 = P.toX 1 ≫ φ.app 1 := by
        simpa using hu1_toX_e
      exact hu1_toX.symm
  · intro i
    fin_cases i
    exact CommSq.mk hnext
  · intro i
    fin_cases i
    exact CommSq.mk hu0_connecting

-- Proof sketch: choose a Postnikov system for the tail `X₁ ⟶ X₀`, factor `X₂ ⟶ X₁` through the
-- auxiliary object using the vanishing of the composite `X₂ ⟶ X₁ ⟶ X₀`, and complete that factor
-- to a distinguished triangle.
/-- Lemma 13.41.3 (6): for length `2`, Postnikov systems always exist. This is the first
non-formal existence step beyond the vacuous length-`0` and triangle length-`1` owner cases. -/
@[stacks 0D81]
theorem length_two_postnikovSystem_exists (X : ComposableArrows D 2) (hX : X.IsComplex) :
    Nonempty (PostnikovSystem X) := by
  -- First choose a Postnikov system on the tail row `X₁ ⟶ X₂`.
  obtain ⟨P⟩ := length_one_postnikovSystem_exists X.δ₀
  -- The complex relation kills the obstruction after composing with the rightmost comparison
  -- isomorphism of the tail Postnikov system.
  have hcomp : P.headToNext ≫ P.tail.toX 0 = X.map' 1 2 := by
    simpa using P.head_comp
  have hzero_toX : X.map' 0 1 ≫ P.headToNext ≫ P.tail.toX 0 = 0 := by
    calc
      X.map' 0 1 ≫ P.headToNext ≫ P.tail.toX 0 =
          X.map' 0 1 ≫ X.map' 1 2 := by
            simpa [Category.assoc] using congrArg (fun k ↦ X.map' 0 1 ≫ k) hcomp
      _ = 0 := hX.zero 0
  let e : P.tail.head ≅ X.obj 2 := by
    simpa using asIso (P.tail.toX (Fin.last 0))
  have hzero : X.map' 0 1 ≫ P.headToNext = 0 := by
    have hzero_toX' : X.map' 0 1 ≫ P.headToNext ≫ P.tail.toX 0 = 0 ≫ P.tail.toX 0 := by
      calc
        X.map' 0 1 ≫ P.headToNext ≫ P.tail.toX 0 = 0 := hzero_toX
        _ = 0 ≫ P.tail.toX 0 := by rw [Limits.zero_comp]
    exact (cancel_mono e.hom).1 <| by
      simpa [Category.assoc, e] using hzero_toX'
  -- Exactness of the first stage triangle of `P` lifts `X₀ ⟶ X₁` to the new auxiliary object.
  obtain ⟨f, hf⟩ := (P.triangle 0).coyoneda_exact₂ (P.triangle_distinguished 0) (X.map' 0 1)
    (by simpa using hzero)
  -- Complete that lift to a distinguished triangle and attach it as the new head step.
  obtain ⟨Y, toX, connecting, hT⟩ := Pretriangulated.distinguished_cocone_triangle₁ f
  refine ⟨PostnikovSystem.mkSucc P Y toX f connecting hT ?_⟩
  simpa using hf.symm

-- Proof comment: forgetting the new head stage of a padded row leaves exactly the original tail
-- row, so any Postnikov system on the padded row restricts to one on the tail.
/-- Helper: a Postnikov system on `X.precomp f` induces one on `X` by passing to
the tail. -/
theorem nonempty_postnikovSystem_of_precomp {n : ℕ} {X : ComposableArrows D n} {Y : D}
    (f : Y ⟶ X.left) :
    Nonempty (PostnikovSystem (X.precomp f)) → Nonempty (PostnikovSystem X) := by
  intro h
  rcases h with ⟨P⟩
  refine ⟨?_⟩
  simpa [ComposableArrows.precomp_δ₀] using P.tail

-- Proof comment: each left-padding step is a `precomp` by the zero map, and any hypothetical
-- Postnikov system on the larger row would restrict to one on the previous tail.
/-- Helper: if a length-`3` row has no Postnikov system, then iterated
left-padding by zero arrows preserves that nonexistence. -/
theorem leftPaddedNoPostnikov {X : ComposableArrows D 3}
    (hX : ¬ Nonempty (PostnikovSystem X)) (m : ℕ) :
    ∃ Y : ComposableArrows D (m + 3), ¬ Nonempty (PostnikovSystem Y) := by
  induction m with
  | zero =>
      exact ⟨X, by simpa using hX⟩
  | succ m hm =>
      rcases hm with ⟨Y, hY⟩
      refine ⟨Y.precomp (0 : (0 : D) ⟶ Y.left), ?_⟩
      exact fun hP ↦ hY (nonempty_postnikovSystem_of_precomp (0 : (0 : D) ⟶ Y.left) hP)

end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]

/-- Helper: precomposing a complex by the zero map preserves the complex
relation. -/
theorem precompZero_isComplex {n : ℕ} {X : ComposableArrows D n} (hX : X.IsComplex) :
    (X.precomp (0 : (0 : D) ⟶ X.left)).IsComplex := by
  refine ComposableArrows.IsComplex.mk ?_
  intro i hi
  cases i with
  | zero =>
      -- Proof comment: the new leftmost composite starts with the inserted zero morphism.
      change (0 : (0 : D) ⟶ X.left) ≫ X.map' 0 1 = 0
      exact zero_comp
  | succ i =>
      -- Proof comment: every later composite is inherited verbatim from the original row.
      simpa [ComposableArrows.precomp] using hX.zero i (by omega)

end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Helper: if a length-`3` complex has no Postnikov system, then iterated
left-padding by zero arrows preserves both complexness and nonexistence. -/
theorem leftPaddedNoPostnikovWithComplex {X : ComposableArrows D 3}
    (hXc : X.IsComplex) (hX : ¬ Nonempty (PostnikovSystem X)) (m : ℕ) :
    ∃ Y : ComposableArrows D (m + 3), Y.IsComplex ∧ ¬ Nonempty (PostnikovSystem Y) := by
  induction m with
  | zero =>
      exact ⟨X, hXc, hX⟩
  | succ m hm =>
      rcases hm with ⟨Y, hYc, hY⟩
      refine ⟨Y.precomp (0 : (0 : D) ⟶ Y.left), precompZero_isComplex hYc, ?_⟩
      exact fun hP ↦ hY (nonempty_postnikovSystem_of_precomp (0 : (0 : D) ⟶ Y.left) hP)

/-- Helper: a single length-`3` counterexample propagates to every larger
length by zero-padding on the left. -/
theorem lengthGtTwoPostnikovSystem_existence_not_universal_of_lengthThree
    {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]
    (h₃ : ∃ X : ComposableArrows D 3, X.IsComplex ∧ ¬ Nonempty (PostnikovSystem X))
    (n : ℕ) (hn : 2 < n) :
    ¬ ∀ (X : ComposableArrows D n) (_hX : X.IsComplex), Nonempty (PostnikovSystem X) := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 3 := by
    refine ⟨n - 3, ?_⟩
    omega
  rcases h₃ with ⟨X, hXc, hX⟩
  rcases leftPaddedNoPostnikovWithComplex hXc hX m with ⟨Y, hYc, hY⟩
  subst n
  exact hY (h Y hYc)

/-- Helper for Lemma 13.41.3: if every morphism of length-`2` complexes extended to a morphism
of Postnikov systems, then every length-`3` complex would admit a Postnikov system. -/
theorem lengthTwoUniversalExtension_implies_lengthThreeExistence
    (hExt : ∀ {X X' : ComposableArrows D 2} (P : PostnikovSystem X) (P' : PostnikovSystem X')
      (φ : X ⟶ X'), Nonempty (PostnikovSystemMorphism P P' φ))
    {X : ComposableArrows D 3} (hX : X.IsComplex) :
    Nonempty (PostnikovSystem X) := by
  -- Proof comment: first choose a Postnikov system on the tail row `X₁ ⟶ X₂ ⟶ X₃`.
  have hδ : X.δ₀.IsComplex := by
    refine ComposableArrows.IsComplex.mk ?_
    intro i hi
    simpa using hX.zero (i + 1)
  obtain ⟨P⟩ := length_two_postnikovSystem_exists X.δ₀ hδ
  let zeroBase : PostnikovSystem ((ComposableArrows.mk₁ (0 : (0 : D) ⟶ (0 : D))).δ₀) := by
    let hIso : IsIso (𝟙 (0 : D)) := by
      refine ⟨⟨𝟙 (0 : D), ?_, ?_⟩⟩ <;> simp
    refine
      { head := (0 : D)
        headToX := 𝟙 (0 : D)
        step := ?_ }
    exact @PostnikovSystem.Step.zero D _ _ _ _ _ _
      (X := ((ComposableArrows.mk₁ (0 : (0 : D) ⟶ (0 : D))).δ₀))
      (Y := (0 : D)) (toX := 𝟙 (0 : D)) hIso
  let zeroRow : ComposableArrows D 2 :=
    ComposableArrows.mk₂ (0 : X.obj 0 ⟶ (0 : D)) (0 : (0 : D) ⟶ (0 : D))
  let zeroTail : PostnikovSystem (ComposableArrows.mk₁ (0 : (0 : D) ⟶ (0 : D))) :=
    { head := (0 : D)
      headToX := (0 : (0 : D) ⟶ (0 : D))
      step := by
        exact PostnikovSystem.Step.succ
          (X := ComposableArrows.mk₁ (0 : (0 : D) ⟶ (0 : D)))
          (Y := (0 : D)) (toX := (0 : (0 : D) ⟶ (0 : D)))
          (Y' := (0 : D)) (toX' := (𝟙 (0 : D))) zeroBase.step
          (𝟙 (0 : D)) (0 : (0 : D) ⟶ (0 : D)⟦(1 : ℤ)⟧)
          (by simpa using (Pretriangulated.contractible_distinguished₁ (0 : D)))
          (by simp) }
  let zeroPostnikov : PostnikovSystem zeroRow :=
    { head := X.obj 0
      headToX := 𝟙 (X.obj 0)
      step := by
        exact PostnikovSystem.Step.succ
          (X := zeroRow) (Y := X.obj 0) (toX := 𝟙 (X.obj 0))
          (Y' := (0 : D)) (toX' := (0 : (0 : D) ⟶ (0 : D))) zeroTail.step
          (0 : X.obj 0 ⟶ (0 : D)) (0 : (0 : D) ⟶ (X.obj 0)⟦(1 : ℤ)⟧)
          (by simpa using (Pretriangulated.contractible_distinguished (X.obj 0)))
          (by simp [zeroRow]) }
  let zeroMap : zeroRow ⟶ X.δ₀ :=
    ComposableArrows.homMk₂ (X.map' 0 1) (0 : (0 : D) ⟶ X.obj 2) (0 : (0 : D) ⟶ X.obj 3)
      (by simpa [zeroRow] using (hX.zero 0).symm)
      (by
        have hleft : zeroRow.map' 1 2 ≫ (0 : (0 : D) ⟶ X.obj 3) = 0 := by
          dsimp [zeroRow, ComposableArrows.mk₂, ComposableArrows.precomp, ComposableArrows.Precomp.map]
          exact zero_comp
        have hright : (0 : (0 : D) ⟶ X.obj 3) = 0 ≫ X.δ₀.map' 1 2 := by
          have h : (0 : (0 : D) ⟶ X.obj 2) ≫ X.δ₀.map' 1 2 = 0 := by
            exact zero_comp
          exact h.symm
        simpa using hleft.trans hright)
  -- Proof comment: the universal extension hypothesis on the zero row produces the missing lift
  -- `X₀ ⟶ P.head` from the stage-`0` comparison square.
  obtain ⟨ψ⟩ := hExt zeroPostnikov P zeroMap
  have hLift : ψ.yMap 0 ≫ P.toX 0 = X.map' 0 1 := by
    simpa [zeroBase, zeroPostnikov, zeroTail, zeroMap, zeroRow, PostnikovSystem.toX] using
      (ψ.comm_toX_w 0).symm
  -- Proof comment: complete that lift to the new head triangle and attach it to the chosen tail
  -- Postnikov system on `X.δ₀`.
  obtain ⟨Y, toX, connecting, hT⟩ := Pretriangulated.distinguished_cocone_triangle₁ (ψ.yMap 0)
  refine ⟨PostnikovSystem.mkSucc P Y toX (ψ.yMap 0) connecting hT ?_⟩
  simpa using hLift

end

noncomputable section

/-- Helper: the concrete homotopy category
`K(AddCommGrpCat, ComplexShape.up ℤ)`. -/
local notation "K" => HomotopyCategory AddCommGrpCat (ComplexShape.up ℤ)

/-- Helper: the quotient functor from cochain complexes to the concrete
homotopy category `K(AddCommGrpCat, ComplexShape.up ℤ)`. -/
private noncomputable abbrev Qh :
    CochainComplex AddCommGrpCat ℤ ⥤ K :=
  HomotopyCategory.quotient AddCommGrpCat (ComplexShape.up ℤ)

/-- Helper: fix one degreewise splitting of the Stacks counterexample row in
each degree so that `trianglehOfDegreewiseSplit` can be used as the stage-`1` triangle. -/
private noncomputable abbrev counterexampleRowSplitting (n : ℤ) :
    (counterexampleRow.map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n)).Splitting :=
  Classical.choice (counterexample_row_termwise_split n)

/-- Helper: with the repo's cochain shift convention, `counterexampleA⟦1⟧`
is supported in degree `0`, so the previously planned `Hom((Qh.obj A)⟦1⟧, Qh.obj C)`-vanishing
route cannot apply in this file. -/
private theorem counterexampleAShiftedXZero :
    (counterexampleA⟦(1 : ℤ)⟧).X 0 = AddCommGrpCat.of (ZMod 4) := by
  -- Proof comment: unfolding the single-complex shift shows the shifted source sits in degree `0`.
  change counterexampleA.X 1 = AddCommGrpCat.of (ZMod 4)
  dsimp [counterexampleA]
  exact HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) 1
    (AddCommGrpCat.of (ZMod 4))

/-- Helper: the degreewise-split triangle attached to the counterexample row is
distinguished in the homotopy category. -/
private theorem counterexampleStageOneTriangleDistinguished :
    CochainComplex.trianglehOfDegreewiseSplit counterexampleRow counterexampleRowSplitting ∈
      distTriang K := by
  -- Proof comment: this is exactly the canonical distinguished triangle attached to a degreewise
  -- split short complex of cochain complexes.
  let T := CochainComplex.trianglehOfDegreewiseSplit counterexampleRow counterexampleRowSplitting
  exact (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2
    ⟨counterexampleRow, counterexampleRowSplitting, ⟨Iso.refl _⟩⟩

/-- Helper: the tail Postnikov system on
`Qh.map counterexampleG : Qh.obj counterexampleB ⟶ Qh.obj counterexampleC` whose unique stage
triangle is `trianglehOfDegreewiseSplit counterexampleRow counterexampleRowSplitting`. -/
private noncomputable def counterexampleTailPostnikovSystem :
    PostnikovSystem (ComposableArrows.mk₁ (Qh.map counterexampleG)) := by
  let e : Qh.obj counterexampleC ⟶ Qh.obj counterexampleC := (Iso.refl _).hom
  -- Proof comment: the stage-`1` triangle for the Stacks counterexample is exactly the canonical
  -- degreewise-split triangle, and the rightmost comparison map is the identity on `Qh.obj C`.
  refine PostnikovSystem.mkSucc (PostnikovSystem.mk₀ (Qh.obj counterexampleC) e)
    (Qh.obj counterexampleA) (Qh.map counterexampleF) (Qh.map counterexampleG)
    (CochainComplex.trianglehOfDegreewiseSplit counterexampleRow counterexampleRowSplitting).mor₃
    ?_ ?_
  · simpa using counterexampleStageOneTriangleDistinguished
  · simp [PostnikovSystem.mk₀, e]

/-- Helper: the chosen length-`2` Postnikov system on the explicit Remark
13.9.11 row in the homotopy category. -/
private noncomputable def counterexampleRowPostnikovSystem :
    PostnikovSystem (ComposableArrows.mk₂ (Qh.map counterexampleF) (Qh.map counterexampleG)) := by
  -- Proof comment: stage `0` is the contractible triangle `0 ⟶ Qh.obj A ⟶ Qh.obj A ⟶ 0[1]`,
  -- while stage `1` is the chosen tail Postnikov system above.
  refine PostnikovSystem.mkSucc counterexampleTailPostnikovSystem 0
    (0 : (0 : K) ⟶ Qh.obj counterexampleA) (𝟙 _) 0 ?_ ?_
  · simpa using (Pretriangulated.contractible_distinguished₁ (Qh.obj counterexampleA))
  · simp [counterexampleTailPostnikovSystem, PostnikovSystem.mk₀,
      PostnikovSystem.mkSucc]

/-- Helper: the explicit self-map of the counterexample row in the homotopy
category with components `Qh.map counterexampleAEnd`, `Qh.map (𝟙 counterexampleB)`, and
`Qh.map (𝟙 counterexampleC)`. -/
private noncomputable def counterexampleLengthTwoRowMap :
    ComposableArrows.mk₂ (Qh.map counterexampleF) (Qh.map counterexampleG) ⟶
      ComposableArrows.mk₂ (Qh.map counterexampleF) (Qh.map counterexampleG) := by
  -- Proof comment: the left square is the homotopy-category commutative square from
  -- Remark 13.9.11, and the right square already commutes strictly before passing to `K`.
  refine ComposableArrows.homMk₂ (Qh.map counterexampleAEnd) (Qh.map (𝟙 counterexampleB))
    (Qh.map (𝟙 counterexampleC)) ?_ ?_
  · simpa using counterexample_left_square_commSq.w
  · calc
      Qh.map counterexampleG ≫ Qh.map (𝟙 counterexampleC) = Qh.map counterexampleG := by
        simp
      _ = Qh.map (𝟙 counterexampleB) ≫ Qh.map counterexampleG := by
        simp

/-- Helper: the stage-`0` `toNext` map of the chosen counterexample Postnikov
system is the identity on `Qh.obj counterexampleA`. -/
private theorem counterexampleRowPostnikovSystem_toNext_zero :
    counterexampleRowPostnikovSystem.toNext 0 = 𝟙 (Qh.obj counterexampleA) := by
  rfl

/-- Helper: the rightmost comparison map of the chosen counterexample Postnikov
system is the identity on `Qh.obj counterexampleC`. -/
private theorem counterexampleRowPostnikovSystem_toX_two :
    counterexampleRowPostnikovSystem.toX 2 = 𝟙 (Qh.obj counterexampleC) := by
  -- Proof comment: unfold the recursive `toX` accessor twice until the tail hits the base
  -- `mk₀` stage, where the comparison map is literally the identity.
  change counterexampleTailPostnikovSystem.tail.headToX = 𝟙 (Qh.obj counterexampleC)
  rfl

/-- Helper: the zeroth component of `counterexampleLengthTwoRowMap` is
`Qh.map counterexampleAEnd`. -/
private theorem counterexampleLengthTwoRowMap_app_zero :
    counterexampleLengthTwoRowMap.app 0 = Qh.map counterexampleAEnd := by
  rfl

/-- Helper: the second component of `counterexampleLengthTwoRowMap` is
`Qh.map (𝟙 counterexampleC)`. -/
private theorem counterexampleLengthTwoRowMap_app_two :
    counterexampleLengthTwoRowMap.app 2 = Qh.map (𝟙 counterexampleC) := by
  rfl

/-- Helper: the middle component of `counterexampleLengthTwoRowMap` is the
identity class of `counterexampleB`. -/
private theorem counterexampleLengthTwoRowMap_app_one :
    counterexampleLengthTwoRowMap.app 1 = Qh.map (𝟙 counterexampleB) := by
  rfl

/-- Helper: the stage-`0` compatibility in a hypothetical Postnikov-system
morphism over `counterexampleLengthTwoRowMap` forces the map on the first auxiliary object to be
`Qh.map counterexampleAEnd`. -/
private theorem counterexampleStageOneLeftObjectMap
    (ψ : PostnikovSystemMorphism counterexampleRowPostnikovSystem counterexampleRowPostnikovSystem
      counterexampleLengthTwoRowMap) :
    ψ.yMap 1 = Qh.map counterexampleAEnd := by
  -- Proof comment: the stage-`0` `toNext` map is the identity, so the `comm_toNext` square reads
  -- exactly as the desired equality for the first auxiliary-object map.
  have h := ψ.comm_toNext_w 0
  rw [counterexampleRowPostnikovSystem_toNext_zero] at h
  have hsrc : ψ.yMap 1 = 𝟙 (Qh.obj counterexampleA) ≫ ψ.yMap 1 := by
    simpa [counterexampleRowPostnikovSystem, counterexampleTailPostnikovSystem] using
      (Category.id_comp (ψ.yMap 1)).symm
  have happ : counterexampleLengthTwoRowMap.app (Fin.castSucc 0) = Qh.map counterexampleAEnd := by
    rfl
  have hmid : 𝟙 (Qh.obj counterexampleA) ≫ ψ.yMap 1 =
      Qh.map counterexampleAEnd ≫ 𝟙 (Qh.obj counterexampleA) := by
    rw [happ] at h
    exact h
  have htgt : Qh.map counterexampleAEnd ≫ 𝟙 (Qh.obj counterexampleA) =
      Qh.map counterexampleAEnd := by
    simp
  exact hsrc.trans (hmid.trans htgt)

/-- Helper: the map on the rightmost auxiliary object in a hypothetical
Postnikov-system morphism over `counterexampleLengthTwoRowMap` is forced to be
`Qh.map (𝟙 counterexampleC)`. -/
private theorem counterexampleStageOneRightObjectMap
    (ψ : PostnikovSystemMorphism counterexampleRowPostnikovSystem counterexampleRowPostnikovSystem
      counterexampleLengthTwoRowMap) :
    ψ.yMap 2 = Qh.map (𝟙 counterexampleC) := by
  -- Proof comment: the rightmost comparison map is the identity, so the `comm_toX` square at
  -- index `2` isolates the final auxiliary-object map directly.
  have h := ψ.comm_toX_w 2
  rw [counterexampleRowPostnikovSystem_toX_two, counterexampleLengthTwoRowMap_app_two] at h
  have hsrc : ψ.yMap 2 = ψ.yMap 2 ≫ 𝟙 (Qh.obj counterexampleC) := by
    exact (Category.comp_id (ψ.yMap 2)).symm
  have hmid : ψ.yMap 2 ≫ 𝟙 (Qh.obj counterexampleC) =
      𝟙 (Qh.obj counterexampleC) ≫ 𝟙 (Qh.obj counterexampleC) := by
    simpa using h.symm
  have htgt : 𝟙 (Qh.obj counterexampleC) ≫ 𝟙 (Qh.obj counterexampleC) =
      Qh.map (𝟙 counterexampleC) := by
    simp
  exact hsrc.trans (hmid.trans htgt)

/-- Helper: any hypothetical Postnikov-system morphism over the explicit
counterexample row has its outer auxiliary-object maps forced by the stage-`0` and rightmost
comparison squares. -/
private theorem counterexampleStageBoundaryMapsOfPostnikovMorphism
    (ψ : PostnikovSystemMorphism counterexampleRowPostnikovSystem counterexampleRowPostnikovSystem
      counterexampleLengthTwoRowMap) :
    ψ.yMap 1 = Qh.map counterexampleAEnd ∧
      ψ.yMap 2 = Qh.map (𝟙 counterexampleC) := by
  constructor
  · -- Proof comment: the stage-`0` compatibility already pins down the first auxiliary-object map.
    exact counterexampleStageOneLeftObjectMap ψ
  · -- Proof comment: the rightmost comparison map is the identity, so the last auxiliary-object
    -- map is forced as well.
    exact counterexampleStageOneRightObjectMap ψ

/-- Helper: the source-level middle map forced by the outer components in
Remark 13.9.11 acts by the identity in degree `0`, by multiplication by `3` in degree `1`, and is
zero elsewhere. -/
private def counterexampleForcedMiddleMapComponent (n : ℤ) :
    counterexampleB.X n ⟶ counterexampleB.X n :=
  if h0 : n = 0 then by
    subst h0
    exact 𝟙 (AddCommGrpCat.of (ZMod 4))
  else if h1 : n = 1 then by
    subst h1
    exact (3 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4)))
  else
    0

/-- Helper: the forced middle map is the identity in degree `0`. -/
private theorem counterexampleForcedMiddleMapComponent_zero :
    counterexampleForcedMiddleMapComponent 0 = 𝟙 (AddCommGrpCat.of (ZMod 4)) := by
  simp [counterexampleForcedMiddleMapComponent]

/-- Helper: the forced middle map is multiplication by `3` in degree `1`. -/
private theorem counterexampleForcedMiddleMapComponent_one :
    counterexampleForcedMiddleMapComponent 1 = (3 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4))) := by
  simp [counterexampleForcedMiddleMapComponent]

/-- Helper: away from degrees `0` and `1`, the forced middle map vanishes. -/
private theorem counterexampleForcedMiddleMapComponent_eq_zero_of_ne_zero_of_ne_one
    (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    counterexampleForcedMiddleMapComponent n = 0 := by
  simp [counterexampleForcedMiddleMapComponent, h0, h1]

/-- Helper: the forced middle degree map commutes with the only nonzero
differential of the explicit middle complex. -/
private theorem counterexampleForcedMiddleMapComponent_comm
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    counterexampleForcedMiddleMapComponent i ≫ counterexampleB.d i j =
      counterexampleB.d i j ≫ counterexampleForcedMiddleMapComponent j := by
  by_cases hi : i = 0
  · subst hi
    have hj' : 1 = j := by simpa using hij
    have hj : j = 1 := by omega
    subst hj
    -- Proof comment: in the only nontrivial degree, both sides are the visible `ZMod 4`
    -- endomorphism `eps4`.
    rw [counterexampleForcedMiddleMapComponent_zero, counterexampleB_d_zero,
      counterexampleForcedMiddleMapComponent_one]
    calc
      (𝟙 (AddCommGrpCat.of (ZMod 4))) ≫ ((2 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4)))) =
          (2 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4))) := by simp
      _ =
          ((2 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4)))) ≫
            ((3 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4)))) := by
              rw [counterexample_three_smul_eq_double_plus_id, Preadditive.comp_add,
                zmod4_double_sq_zero]
              simp
  · have hd : counterexampleB.d i j = 0 := by
      have hji' : i + 1 = j := by simpa using hij
      have hji : j = i + 1 := by omega
      subst hji
      simpa using counterexampleB_d_eq_zero_of_ne_zero i hi
    -- Proof comment: outside degree `0`, the differential vanishes, so both composites are zero.
    rw [hd, comp_zero, zero_comp]

/-- Helper: the explicit forced middle endomorphism of `counterexampleB`. -/
private def counterexampleForcedMiddleMap : counterexampleB ⟶ counterexampleB :=
  HomologicalComplex.Hom.mk counterexampleForcedMiddleMapComponent
    (fun i j hij ↦ counterexampleForcedMiddleMapComponent_comm i j hij)

/-- Helper: the forced middle map is the identity in degree `0`. -/
private theorem counterexampleForcedMiddleMap_f_zero :
    counterexampleForcedMiddleMap.f 0 = 𝟙 (AddCommGrpCat.of (ZMod 4)) := by
  rfl

/-- Helper: the forced middle map is multiplication by `3` in degree `1`. -/
private theorem counterexampleForcedMiddleMap_f_one :
    counterexampleForcedMiddleMap.f 1 = (3 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4))) := by
  rfl

/-- Helper: the forced middle map vanishes away from degrees `0` and `1`. -/
private theorem counterexampleForcedMiddleMap_f_eq_zero_of_ne_zero_of_ne_one
    (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    counterexampleForcedMiddleMap.f n = 0 := by
  exact counterexampleForcedMiddleMapComponent_eq_zero_of_ne_zero_of_ne_one n h0 h1

/-- Helper: the explicit forced middle map gives a strict morphism of the
Stacks counterexample row with the prescribed outer components. -/
private def counterexampleForcedRowMorphism : counterexampleRow ⟶ counterexampleRow where
  τ₁ := counterexampleAEnd
  τ₂ := counterexampleForcedMiddleMap
  τ₃ := 𝟙 counterexampleC
  comm₁₂ := by
    -- Proof comment: maps out of the single complex `A` are determined in degree `1`.
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, counterexampleAEnd_f_one, counterexampleF_f_one,
      HomologicalComplex.comp_f, counterexampleF_f_one, counterexampleForcedMiddleMap_f_one]
    calc
      (3 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4))) ≫ 𝟙 (AddCommGrpCat.of (ZMod 4)) =
          (3 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4))) := by simp
      _ =
          𝟙 (AddCommGrpCat.of (ZMod 4)) ≫
            ((3 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4)))) := by simp
  comm₂₃ := by
    -- Proof comment: maps to the single complex `C` are determined in degree `0`.
    apply HomologicalComplex.to_single_hom_ext
    rw [HomologicalComplex.comp_f, counterexampleForcedMiddleMap_f_zero, counterexampleG_f_zero,
      HomologicalComplex.comp_f, counterexampleG_f_zero]
    calc
      𝟙 (AddCommGrpCat.of (ZMod 4)) ≫ 𝟙 (AddCommGrpCat.of (ZMod 4)) =
          𝟙 (AddCommGrpCat.of (ZMod 4)) := by simp
      _ = 𝟙 (AddCommGrpCat.of (ZMod 4)) := rfl

/-- Helper: the explicit forced row morphism has the prescribed outer
components. -/
private theorem counterexampleForcedRowMorphism_outer :
    counterexampleForcedRowMorphism.τ₁ = counterexampleAEnd ∧
      counterexampleForcedRowMorphism.τ₃ = 𝟙 counterexampleC := by
  constructor <;> rfl

/-- Helper: the left-square defect of the explicit Remark 13.9.11 row is the
precomposition operator used for the length-`3` obstruction. -/
private theorem counterexampleDefectPrecomp_comp_zero :
    ((Qh.map counterexampleAEnd) - 𝟙 (Qh.obj counterexampleA)) ≫ Qh.map counterexampleF = 0 := by
  have hleft :
      Qh.map counterexampleAEnd ≫ Qh.map counterexampleF =
        𝟙 (Qh.obj counterexampleA) ≫ Qh.map counterexampleF := by
    simpa [counterexampleRow] using counterexample_left_square_commSq.w.symm
  calc
    ((Qh.map counterexampleAEnd) - 𝟙 (Qh.obj counterexampleA)) ≫ Qh.map counterexampleF =
        Qh.map counterexampleAEnd ≫ Qh.map counterexampleF -
          𝟙 (Qh.obj counterexampleA) ≫ Qh.map counterexampleF := by
            rw [Preadditive.sub_comp]
    _ = 0 := by simp [hleft]

/-- Helper for Lemma 13.41.3: the explicit forced strict row morphism determines a morphism of
the stage-`1` distinguished triangle whose first two components are
`Qh.map counterexampleAEnd` and `Qh.map counterexampleForcedRowMorphism.τ₂`. -/
private theorem counterexampleForcedRowTriangleMorphism :
    ∃ χ : counterexampleTailPostnikovSystem.triangle 0 ⟶
        counterexampleTailPostnikovSystem.triangle 0,
      χ.hom₁ = Qh.map counterexampleAEnd ∧
        χ.hom₂ = Qh.map counterexampleForcedRowMorphism.τ₂ := by
  let T := counterexampleTailPostnikovSystem.triangle 0
  have hT : T ∈ distTriang K := counterexampleTailPostnikovSystem.triangle_distinguished 0
  have hcomm₁ :
      T.mor₁ ≫ Qh.map counterexampleForcedRowMorphism.τ₂ =
        Qh.map counterexampleAEnd ≫ T.mor₁ := by
    -- Proof comment: the first morphism of the stage triangle is `Qh.map counterexampleF`,
    -- so the forced strict row morphism gives the required commutative square after quotienting.
    simpa [T, Functor.map_comp] using congrArg (fun f ↦ Qh.map f)
      counterexampleForcedRowMorphism.comm₁₂.symm
  -- Proof comment: TR3 completes the left square to some endomorphism of the rightmost vertex.
  obtain ⟨c, hc₂, hc₃⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism
      T T hT hT (Qh.map counterexampleAEnd) (Qh.map counterexampleForcedRowMorphism.τ₂) hcomm₁
  refine ⟨Triangle.homMk _ _ (Qh.map counterexampleAEnd)
    (Qh.map counterexampleForcedRowMorphism.τ₂) c hcomm₁ hc₂ hc₃, rfl, rfl⟩

/-- Helper: the explicit length-`3` row obtained by precomposing the
counterexample length-`2` row with the left-square defect. -/
private noncomputable abbrev counterexampleDefectPrecompRow :
    ComposableArrows (HomotopyCategory AddCommGrpCat (ComplexShape.up ℤ)) 3 :=
  (ComposableArrows.mk₂ (Qh.map counterexampleF) (Qh.map counterexampleG)).precomp
    (((Qh.map counterexampleAEnd) - 𝟙 (Qh.obj counterexampleA)))

/-- Helper: the explicit defect-precomp length-`3` row is a complex. -/
private theorem counterexampleDefectPrecompRow_isComplex :
    counterexampleDefectPrecompRow.IsComplex := by
  refine ComposableArrows.IsComplex.mk ?_
  intro i hi
  cases i with
  | zero =>
      -- Proof comment: the new leftmost composite is exactly the defect operator composed with
      -- `F`.
      change ((Qh.map counterexampleAEnd) - 𝟙 (Qh.obj counterexampleA)) ≫
          Qh.map counterexampleF = 0
      exact counterexampleDefectPrecomp_comp_zero
  | succ i =>
      have hi0 : i = 0 := by omega
      subst hi0
      -- Proof comment: the tail of the defect-precomp row is the original short complex
      -- `counterexampleF ≫ counterexampleG = 0`, transported through the quotient functor.
      change Qh.map counterexampleF ≫ Qh.map counterexampleG = 0
      calc
        Qh.map counterexampleF ≫ Qh.map counterexampleG =
            Qh.map (counterexampleF ≫ counterexampleG) := by simp
        _ = 0 := by simpa [counterexampleF_comp_counterexampleG]

/-- Helper for Lemma 13.41.3: the tail triangle already admits the obvious homotopy-category
endomorphism with first two components `Qh.map counterexampleAEnd` and `Qh.map (𝟙 counterexampleB)`.
This route-correction check shows that the direct length-`2` obstruction cannot live only at the
tail-triangle level. -/
private theorem counterexampleTailTriangleAEndIdentityMiddleMorphism :
    ∃ χ : counterexampleTailPostnikovSystem.triangle 0 ⟶
        counterexampleTailPostnikovSystem.triangle 0,
      χ.hom₁ = Qh.map counterexampleAEnd ∧
        χ.hom₂ = Qh.map (𝟙 counterexampleB) := by
  let T := counterexampleTailPostnikovSystem.triangle 0
  have hT : T ∈ distTriang K := counterexampleTailPostnikovSystem.triangle_distinguished 0
  have hcomm₁ :
      T.mor₁ ≫ Qh.map (𝟙 counterexampleB) =
        Qh.map counterexampleAEnd ≫ T.mor₁ := by
    -- Proof comment: the left square from Remark 13.9.11 is already the first-square input for
    -- TR3 on the chosen stage-`1` triangle.
    simpa [T] using counterexample_left_square_commSq.w
  -- Proof comment: TR3 completes the visible first square to a full endomorphism of the tail
  -- triangle; the third component is irrelevant for the route-correction diagnostic.
  obtain ⟨c, hc₂, hc₃⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism
      T T hT hT (Qh.map counterexampleAEnd) (Qh.map (𝟙 counterexampleB)) hcomm₁
  refine ⟨Triangle.homMk _ _ (Qh.map counterexampleAEnd) (Qh.map (𝟙 counterexampleB)) c
    hcomm₁ hc₂ hc₃, rfl, rfl⟩

/-- Helper for Lemma 13.41.3: each degree of `counterexampleF` is split mono because the chosen
degreewise splitting of `counterexampleRow` splits the first map. -/
private theorem counterexampleF_termwiseSplitMono (n : ℤ) :
    IsSplitMono (counterexampleF.f n) := by
  -- Proof comment: reuse the degreewise splitting already fixed for the counterexample row.
  exact (counterexampleRowSplitting n).isSplitMono_f

/-- Helper for Lemma 13.41.3: each degree of `counterexampleG` is split epi because the chosen
degreewise splitting of `counterexampleRow` splits the second map. -/
private theorem counterexampleG_termwiseSplitEpi (n : ℤ) :
    IsSplitEpi (counterexampleG.f n) := by
  -- Proof comment: the same degreewise splitting also provides sections for the second map.
  exact (counterexampleRowSplitting n).isSplitEpi_g

/-- Helper for Lemma 13.41.3: the head-stage defect forces `Qh.map counterexampleAEnd` to act as
the identity on the stage-`0` transition map of `P.tail`. -/
private theorem headStageCounterexampleAEnd_on_tailToNext
    (P : PostnikovSystem counterexampleDefectPrecompRow) :
    Qh.map counterexampleAEnd ≫ P.tail.toNext 0 = P.tail.toNext 0 := by
  -- Proof comment: `P.comp 0` identifies the defect operator with the head-stage factorization,
  -- and the stage-`0` distinguished triangle of `P.tail` kills the extra term.
  have hzero :
      P.tail.toX 0 ≫ P.tail.toNext 0 = 0 := by
    simpa [PostnikovSystem.triangle] using
      Pretriangulated.comp_distTriang_mor_zero₁₂ (P.tail.triangle 0) (P.tail.triangle_distinguished 0)
  have hcomp :
      P.toNext 0 ≫ P.tail.toX 0 =
        (Qh.map counterexampleAEnd) - 𝟙 (Qh.obj counterexampleA) := by
    simpa [counterexampleDefectPrecompRow, ComposableArrows.precomp] using P.comp 0
  have hdefect :
      ((Qh.map counterexampleAEnd) - 𝟙 (Qh.obj counterexampleA)) ≫ P.tail.toNext 0 = 0 := by
    rw [← hcomp]
    calc
      (P.toNext 0 ≫ P.tail.toX 0) ≫ P.tail.toNext 0 =
          P.toNext 0 ≫ (P.tail.toX 0 ≫ P.tail.toNext 0) := by simp [Category.assoc]
      _ = P.toNext 0 ≫ 0 := by
        simpa [Category.assoc] using congrArg (fun k ↦ P.toNext 0 ≫ k) hzero
      _ = 0 := by simpa using (comp_zero : P.toNext 0 ≫ 0 = 0)
  -- Proof comment: rewrite the defect equation as a vanishing difference and cancel it.
  rw [Preadditive.sub_comp, Category.id_comp] at hdefect
  exact sub_eq_zero.mp hdefect

/-- Helper for Lemma 13.41.3: the stage-`1` transition of `P.tail` is the fixed tail map
`Qh.map counterexampleG` transported across the rightmost comparison isomorphism. -/
private theorem tailStageCounterexampleG_on_tailToXTwo
    (P : PostnikovSystem counterexampleDefectPrecompRow) :
    let e : P.tail 2 ≅ Qh.obj counterexampleC := by
      simpa using asIso (P.tail.toX (Fin.last 2))
    Qh.map counterexampleG ≫ e.inv = P.tail.toNext 1 := by
  -- Proof comment: `P.tail.comp 1` identifies the tail differential after postcomposing with the
  -- isomorphism `P.tail.toX 2`, so canceling that isomorphism normalizes the stage-`1` map.
  let e : P.tail 2 ≅ Qh.obj counterexampleC := by
    simpa using asIso (P.tail.toX (Fin.last 2))
  change Qh.map counterexampleG ≫ e.inv = P.tail.toNext 1
  apply (cancel_mono e.hom).1
  calc
    (Qh.map counterexampleG ≫ e.inv) ≫ e.hom = Qh.map counterexampleG := by
      calc
        (Qh.map counterexampleG ≫ e.inv) ≫ e.hom =
            Qh.map counterexampleG ≫ (e.inv ≫ e.hom) := by simp [Category.assoc]
        _ = Qh.map counterexampleG ≫ 𝟙 (Qh.obj counterexampleC) := by rw [e.inv_hom_id]
        _ = Qh.map counterexampleG := by simp
    _ = P.tail.toNext 1 ≫ e.hom := by
      simpa [counterexampleDefectPrecompRow, ComposableArrows.precomp, e] using (P.tail.comp 1).symm

/-- Helper for Lemma 13.41.3: after rotating the fixed tail triangle and the stage-`1` triangle
of a hypothetical Postnikov system on the defect-precomp row, both triangles lie over the common
arrow `Qh.map counterexampleG`. The resulting comparison isomorphism fixes the middle vertex and
identifies the right vertex via the canonical comparison `P.tail.toX 2`. -/
private theorem rotatedTailTriangleIsoOfDefectPrecompPostnikov
    (P : PostnikovSystem counterexampleDefectPrecompRow) :
    ∃ (e : P.tail 2 ≅ Qh.obj counterexampleC)
      (η : (counterexampleTailPostnikovSystem.triangle 0).rotate ≅ (P.tail.triangle 1).rotate),
      η.hom.hom₁ = 𝟙 (Qh.obj counterexampleB) ∧ η.hom.hom₂ = e.inv := by
  let T₁ := counterexampleTailPostnikovSystem.triangle 0
  let T₂ := P.tail.triangle 1
  let e : P.tail 2 ≅ Qh.obj counterexampleC := by
    simpa using asIso (P.tail.toX (Fin.last 2))
  -- Proof comment: rotate both distinguished triangles so that `Qh.map counterexampleG` is the
  -- common first morphism, then apply the canonical distinguished-triangle comparison.
  obtain ⟨η, hη₁, hη₂⟩ :=
    exists_iso_of_arrow_iso T₁.rotate T₂.rotate
      (rot_of_distTriang _ (counterexampleTailPostnikovSystem.triangle_distinguished 0))
      (rot_of_distTriang _ (P.tail.triangle_distinguished 1))
      (Arrow.isoMk (Iso.refl _) e.symm (by
        simpa [T₁, T₂, Category.id_comp] using (tailStageCounterexampleG_on_tailToXTwo P).symm))
  exact ⟨e, η, hη₁, hη₂⟩

/-- Helper for Lemma 13.41.3: undoing the rotated comparison gives a factorization of
`Qh.map counterexampleF` through the stage-`1` head object of `P.tail`. -/
private theorem headFactorMapOfDefectPrecompPostnikov
    (P : PostnikovSystem counterexampleDefectPrecompRow) :
    ∃ u : Qh.obj counterexampleA ⟶ P.tail 1,
      u ≫ P.tail.toX 1 = Qh.map counterexampleF := by
  obtain ⟨e, η, hη₁, _hη₂⟩ := rotatedTailTriangleIsoOfDefectPrecompPostnikov P
  let T₁ := counterexampleTailPostnikovSystem.triangle 0
  let T₂ := P.tail.triangle 1
  let ε : T₁ ≅ T₂ :=
    rotCompInvRot.app T₁ ≪≫
      ((Pretriangulated.invRotate K).mapIso η) ≪≫
      (rotCompInvRot.app T₂).symm
  refine ⟨ε.hom.hom₁, ?_⟩
  -- Proof comment: after undoing the rotation, the first square of the triangle isomorphism is
  -- exactly the desired source-facing factorization through `P.tail.toX 1`.
  have hcomm : ε.hom.hom₁ ≫ P.tail.toX 1 = counterexampleTailPostnikovSystem.toX 0 := by
    simpa [T₁, T₂, ε, hη₁] using ε.hom.comm₁.symm
  simpa [counterexampleTailPostnikovSystem, PostnikovSystem.toX, PostnikovSystem.mkSucc,
    PostnikovSystem.mk₀] using hcomm

/-- Helper for Lemma 13.41.3: the left square of the explicit Remark 13.9.11 counterexample can
be strictified on the source row without changing the middle map in the homotopy category. -/
private theorem identityClassLeftStrictificationOfCounterexample :
    ∃ τ₂ : counterexampleB ⟶ counterexampleB,
      Qh.map τ₂ = Qh.map (𝟙 counterexampleB) ∧
        counterexampleF ≫ τ₂ = counterexampleAEnd ≫ counterexampleF := by
  let sq : CommSq (Qh.map counterexampleF) (Qh.map counterexampleAEnd)
      (Qh.map (𝟙 counterexampleB)) (Qh.map counterexampleF) := by
    -- Proof comment: this is exactly the homotopy-category left square from Remark 13.9.11.
    simpa [counterexampleRow] using counterexample_left_square_commSq
  obtain ⟨τ₂, hQ, hsq⟩ :=
    CochainComplex.exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono
      (f := counterexampleF) (a := counterexampleAEnd) (b := 𝟙 counterexampleB)
      (g := counterexampleF) sq counterexampleF_termwiseSplitMono
  refine ⟨τ₂, hQ.symm, ?_⟩
  -- Proof comment: the strictifying replacement now commutes with `counterexampleF` on the nose.
  exact hsq.w

/-- Helper for Lemma 13.41.3: no endomorphism of `Qh.obj counterexampleA` can be fixed by
`Qh.map counterexampleAEnd` and still act trivially on the quotient class of
`counterexampleF`. -/
private theorem counterexampleAEndFixesNoPreservingEndomorphism
    (σ : Qh.obj counterexampleA ⟶ Qh.obj counterexampleA)
    (hfix : Qh.map counterexampleAEnd ≫ σ = σ)
    (hcomp : σ ≫ Qh.map counterexampleF = Qh.map counterexampleF) :
    False := by
  obtain ⟨s, hsσ⟩ := Qh.map_surjective σ
  have hfixQ : Qh.map (counterexampleAEnd ≫ s) = Qh.map s := by
    rw [Functor.map_comp, hsσ, hfix]
  have hcompQ : Qh.map (s ≫ counterexampleF) = Qh.map counterexampleF := by
    rw [Functor.map_comp, hsσ, hcomp]
  let Hfix : Homotopy (counterexampleAEnd ≫ s) s := HomotopyCategory.homotopyOfEq _ _ hfixQ
  have hfix1' : ((3 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4)))) ≫ s.f 1 = s.f 1 := by
    have hcomm := Hfix.comm 1
    rw [dNext_eq Hfix.hom (show (ComplexShape.up ℤ).Rel 1 2 by simp),
      prevD_eq Hfix.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp)] at hcomm
    have hd12 : counterexampleA.d 1 2 = 0 := by
      rfl
    have hd01 : counterexampleA.d 0 1 = 0 := by
      rfl
    rw [hd12, hd01, Limits.comp_zero, Limits.zero_comp, zero_add,
      HomologicalComplex.comp_f, counterexampleAEnd_f_one] at hcomm
    rw [zero_add] at hcomm
    exact hcomm
  have hfix1 : (3 : ℤ) • s.f 1 = s.f 1 := by
    simpa using hfix1'
  let H : Homotopy (s ≫ counterexampleF) counterexampleF := HomotopyCategory.homotopyOfEq _ _ hcompQ
  let h10 : AddCommGrpCat.of (ZMod 4) ⟶ AddCommGrpCat.of (ZMod 4) := by
    simpa [counterexampleA, counterexampleB] using H.hom 1 0
  have hcomp1 :
      s.f 1 = h10 ≫ ((2 : ℤ) • (𝟙 (AddCommGrpCat.of (ZMod 4)))) +
        𝟙 (AddCommGrpCat.of (ZMod 4)) := by
    have hcomm := H.comm 1
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel 1 2 by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp)] at hcomm
    have hd12 : counterexampleA.d 1 2 = 0 := by
      rfl
    rw [hd12, Limits.zero_comp, zero_add, HomologicalComplex.comp_f,
      counterexampleB_d_zero, counterexampleF_f_one] at hcomm
    simpa [h10] using hcomm
  have ha' :
      ((3 : ℤ) • s.f 1) (1 : ZMod 4) =
        (show AddCommGrpCat.of (ZMod 4) ⟶ AddCommGrpCat.of (ZMod 4) from s.f 1) (1 : ZMod 4) := by
    exact congrArg
      (fun f : AddCommGrpCat.of (ZMod 4) ⟶ AddCommGrpCat.of (ZMod 4) => f (1 : ZMod 4)) hfix1
  have ha :
      (3 : ℤ) • (s.f 1 (1 : ZMod 4)) = s.f 1 (1 : ZMod 4) := by
    simpa [Pi.smul_apply] using ha'
  have hb :
      ((show AddCommGrpCat.of (ZMod 4) ⟶ AddCommGrpCat.of (ZMod 4) from s.f 1) (1 : ZMod 4)) =
        (2 : ℤ) •
          ((show AddCommGrpCat.of (ZMod 4) ⟶ AddCommGrpCat.of (ZMod 4) from h10)
            (1 : ZMod 4)) +
          1 := by
    simpa using congrArg
      (fun f : AddCommGrpCat.of (ZMod 4) ⟶ AddCommGrpCat.of (ZMod 4) => f (1 : ZMod 4)) hcomp1
  have hbad : ∀ a b : ZMod 4, ¬ ((3 : ℤ) • a = a ∧ a = (2 : ℤ) • b + 1) := by
    decide
  exact hbad _ _ ⟨ha, hb⟩

/-- Helper for Lemma 13.41.3: any Postnikov system on the defect-precomp row would force the
forbidden strict replacement on the source counterexample row, hence cannot exist. -/
private theorem noPostnikovSystemOnCounterexampleDefectPrecompRow
    (P : PostnikovSystem counterexampleDefectPrecompRow) :
    False := by
  -- Route correction: the tail triangle already supports the obvious
  -- `(Qh.map counterexampleAEnd, Qh.map (𝟙 counterexampleB))` endomorphism, so the remaining
  -- blocker is the head-stage bridge from the hypothetical Postnikov system `P` back to a strict
  -- short-complex morphism on `counterexampleRow`.
  have htail₀ : P.tail.toNext 0 ≫ P.tail.toX 1 = Qh.map counterexampleF := by
    -- Proof comment: the first tail-stage comparison map already factors the fixed map
    -- `counterexampleF`.
    simpa [counterexampleDefectPrecompRow, ComposableArrows.precomp] using P.tail.comp 0
  have hhead : Qh.map counterexampleAEnd ≫ P.tail.toNext 0 = P.tail.toNext 0 := by
    -- Proof comment: the head-stage defect calculation is already isolated as a reusable lemma.
    exact headStageCounterexampleAEnd_on_tailToNext P
  obtain ⟨e, η, hη₁, _hη₂⟩ := rotatedTailTriangleIsoOfDefectPrecompPostnikov P
  let T₁ := counterexampleTailPostnikovSystem.triangle 0
  let T₂ := P.tail.triangle 1
  let ε : T₁ ≅ T₂ :=
    rotCompInvRot.app T₁ ≪≫
      ((Pretriangulated.invRotate K).mapIso η) ≪≫
      (rotCompInvRot.app T₂).symm
  let u : Qh.obj counterexampleA ⟶ P.tail 1 := ε.hom.hom₁
  let uInv : P.tail 1 ⟶ Qh.obj counterexampleA := ε.inv.hom₁
  have huF : u ≫ P.tail.toX 1 = Qh.map counterexampleF := by
    -- Proof comment: undoing the rotated comparison identifies the left vertex map with a
    -- factorization of `counterexampleF` through `P.tail.toX 1`.
    have hcomm : ε.hom.hom₁ ≫ P.tail.toX 1 = counterexampleTailPostnikovSystem.toX 0 := by
      simpa [T₁, T₂, ε, hη₁] using ε.hom.comm₁.symm
    simpa [u, counterexampleTailPostnikovSystem, PostnikovSystem.toX, PostnikovSystem.mkSucc,
      PostnikovSystem.mk₀] using hcomm
  let σ : Qh.obj counterexampleA ⟶ Qh.obj counterexampleA := P.tail.toNext 0 ≫ uInv
  have hfix : Qh.map counterexampleAEnd ≫ σ = σ := by
    -- Proof comment: transport the fixed-point identity on `P.tail.toNext 0` across `u`.
    simpa [σ, Category.assoc] using congrArg (fun k ↦ k ≫ uInv) hhead
  have hcomp : σ ≫ Qh.map counterexampleF = Qh.map counterexampleF := by
    -- Proof comment: both `u` and `P.tail.toNext 0` factor the same tail differential
    -- `counterexampleF`.
    dsimp [σ]
    have huInv : uInv ≫ u = 𝟙 _ := by
      change ε.inv.hom₁ ≫ ε.hom.hom₁ = 𝟙 _
      simpa using congrArg TriangleMorphism.hom₁ ε.inv_hom_id
    have huF' : uInv ≫ Qh.map counterexampleF = P.tail.toX 1 := by
      calc
        uInv ≫ Qh.map counterexampleF = uInv ≫ (u ≫ P.tail.toX 1) := by
          simpa [Category.assoc] using (congrArg (fun k ↦ uInv ≫ k) huF).symm
        _ = P.tail.toX 1 := by
          calc
            uInv ≫ (u ≫ P.tail.toX 1) = (uInv ≫ u) ≫ P.tail.toX 1 := by simp [Category.assoc]
            _ = 𝟙 _ ≫ P.tail.toX 1 := by rw [huInv]
            _ = P.tail.toX 1 := by simp
    have hstep : P.tail.toNext 0 ≫ uInv ≫ Qh.map counterexampleF = P.tail.toNext 0 ≫ P.tail.toX 1 := by
      simpa [Category.assoc] using congrArg (fun k ↦ P.tail.toNext 0 ≫ k) huF'
    simpa [Category.assoc] using hstep.trans htail₀
  exact counterexampleAEndFixesNoPreservingEndomorphism σ hfix hcomp

/-- Helper: a concrete length-`3` complex in a triangulated category with no
Postnikov system. -/
theorem counterexampleLengthThreeNoPostnikov :
    ∃ X : ComposableArrows.{0, 1} K 3,
      X.IsComplex ∧ ¬ Nonempty (PostnikovSystem X) := by
  -- Route correction: the obstruction is now pinned to the explicit defect-precomp row
  -- `counterexampleDefectPrecompRow`, whose complexness is already proved above.
  refine ⟨(counterexampleDefectPrecompRow : ComposableArrows.{0, 1} K 3),
    counterexampleDefectPrecompRow_isComplex, ?_⟩
  intro hP
  rcases hP with ⟨P⟩
  exact noPostnikovSystemOnCounterexampleDefectPrecompRow P

/-- Helper: a length-`3` counterexample forces the failure of universal length-`2` extension. -/
theorem counterexampleLengthTwoNoExtensionWitness :
    ¬ ∀ {D : Type 1} [Category.{0} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D] {X X' : ComposableArrows D 2}
        (P : PostnikovSystem X) (P' : PostnikovSystem X') (φ : X ⟶ X'),
          Nonempty (PostnikovSystemMorphism P P' φ) := by
  intro h
  have hK :
      ∀ {X X' : ComposableArrows K 2} (P : PostnikovSystem X) (P' : PostnikovSystem X')
        (φ : X ⟶ X'), Nonempty (PostnikovSystemMorphism P P' φ) := by
    intro X X' P P' φ
    exact @h K inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      X X' P P' φ
  rcases counterexampleLengthThreeNoPostnikov with ⟨X, hXc, hX⟩
  exact hX (lengthTwoUniversalExtension_implies_lengthThreeExistence (D := K) hK hXc)

-- Proof sketch: the textbook statement is a non-universality claim. One exhibits a triangulated
-- category, two length-`2` complexes with chosen Postnikov systems, and a morphism of complexes
-- for which no compatible morphism of Postnikov systems exists.
/-- Lemma 13.41.3 (7): for length `2`, it is not true in general that every morphism of complexes
extends to a morphism of Postnikov systems. -/
@[stacks 0D81]
theorem length_two_morphism_extension_not_universal :
    ¬ ∀ {D : Type 1} [Category.{0} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D] {X X' : ComposableArrows D 2}
        (P : PostnikovSystem X) (P' : PostnikovSystem X') (φ : X ⟶ X'),
          Nonempty (PostnikovSystemMorphism P P' φ) := by
  exact counterexampleLengthTwoNoExtensionWitness

-- Proof sketch: for each `n > 2`, one uses a standard counterexample showing that some
-- length-`n` complex in a triangulated category does not admit any Postnikov system.
/-- Lemma 13.41.3 (8): for every `n > 2`, it is not true in general that every length-`n`
complex in a triangulated category admits a Postnikov system. -/
@[stacks 0D81]
theorem length_gt_two_postnikovSystem_existence_not_universal (n : ℕ) (hn : 2 < n) :
    ¬ ∀ {D : Type 1} [Category.{0} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D] (X : ComposableArrows D n)
        (_hX : X.IsComplex), Nonempty (PostnikovSystem X) := by
  intro h
  -- Proof comment: once a single length-`3` counterexample in `K(AddCommGrpCat)` is available, the
  -- earlier padding lemma propagates it to every larger length.
  have hK :
      ∀ (X : ComposableArrows (HomotopyCategory AddCommGrpCat (ComplexShape.up ℤ)) n)
        (hX : X.IsComplex), Nonempty (PostnikovSystem X) := by
    intro X hX
    exact @h (HomotopyCategory AddCommGrpCat (ComplexShape.up ℤ))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance X hX
  exact
    lengthGtTwoPostnikovSystem_existence_not_universal_of_lengthThree
      counterexampleLengthThreeNoPostnikov n hn hK

end

end CategoryTheory
