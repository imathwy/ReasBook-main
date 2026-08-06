import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_1_8.Projection

-- Declarations for this item were appended by the statement pipeline.

universe u v w x

variable {E : Type u} {A : Type v} {B : Type w}
variable [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]

-- Semantic recall via `lean_leansearch`: abstract model-category fibrations are stable under base
-- change, and the pullback projection to the base is the canonical owner `pullbackSnd`.

/-- Helper for Lemma 7.1.5: the first coordinate of a pullback-valued map. -/
abbrev pullbackFirstCoordinate {X : Type*} [TopologicalSpace X] {p : C(E, B)} {g : C(A, B)}
    (f : C(X, Function.Pullback p g)) : C(X, E) :=
  ContinuousMap.fst.comp
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(Function.Pullback p g, E × A)).comp f)

/-- Helper for Lemma 7.1.5: evaluating `pullbackFirstCoordinate` recovers the first coordinate. -/
@[simp] theorem pullbackFirstCoordinate_apply {X : Type*} [TopologicalSpace X] {p : C(E, B)}
    {g : C(A, B)} (f : C(X, Function.Pullback p g)) (x : X) :
    pullbackFirstCoordinate f x = (f x).1.1 :=
  rfl

/-- Helper for Lemma 7.1.5: compatible maps into `E` and `A` assemble into a pullback-valued
continuous map. -/
theorem continuous_pullbackPair {X : Type*} [TopologicalSpace X] {p : C(E, B)} {g : C(A, B)}
    {u : C(X, E)} {v : C(X, A)} (h : ∀ x, p (u x) = g (v x)) :
    Continuous fun x ↦ (⟨(u x, v x), h x⟩ : Function.Pullback p g) := by
  -- The pair `(u, v)` is continuous into `E × A`, so we only need the subtype witness.
  exact Continuous.subtype_mk (u.continuous.prodMk v.continuous) _

/-- Helper for Lemma 7.1.5: the first coordinate of a pullback lift solves the projected lifting
problem for `p`. -/
theorem pullbackFirstCoordinateComp {X : Type*} [TopologicalSpace X] {p : C(E, B)} {g : C(A, B)}
    {f₀ : C(X, A)} {g₀ : C(X, Function.Pullback p g)}
    (hg₀ : (pullbackSnd p g).comp g₀ = f₀) :
    p.comp (pullbackFirstCoordinate g₀) = g.comp f₀ := by
  -- Project the pullback-valued map to the base and combine it with the pullback equation.
  ext x
  have hbase : pullbackSnd p g (g₀ x) = f₀ x := by
    simpa using ContinuousMap.congr_fun hg₀ x
  exact (g₀ x).2.trans (congrArg g hbase)

/-- Helper for Lemma 7.1.5: after projecting a pullback lifting problem to `E`, the fibration
structure on `p` lifts the induced base homotopy. -/
theorem existsFirstCoordinateHomotopyLift {X : Type x} [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{x, x} X] {p : C(E, B)}
    [hp : IsFibration.{u, w, x} p] {g : C(A, B)} {f₀ f₁ : C(X, A)} (H : f₀.Homotopy f₁)
    {g₀fst : C(X, E)} (hg₀fst : p.comp g₀fst = g.comp f₀) :
    ∃ g₁fst : C(X, E), ∃ Gfst : g₀fst.Homotopy g₁fst,
      p.comp Gfst.toContinuousMap = ((ContinuousMap.Homotopy.refl g).comp H).toContinuousMap := by
  -- Use the fibration lifting theorem directly on the projected square.
  simpa using
    (@IsFibration.exists_homotopyLift E B _ _ p hp X _ _ (g.comp f₀) (g.comp f₁)
      ((ContinuousMap.Homotopy.refl g).comp H) g₀fst hg₀fst)

/-- The projection from the pullback of a fibration is again a fibration. -/
instance pullbackSnd.instIsFibration {p : C(E, B)} [hp : IsFibration.{u, w, x} p]
    (g : C(A, B)) : IsFibration.{max u v, v, x} (pullbackSnd p g) where
  surjective := by
    -- Choose a point of `E` over `g a`, then pair it with `a` to land in the pullback.
    intro a
    have hpSurj : Function.Surjective p := hp.surjective
    rcases hpSurj (g a) with ⟨e, he⟩
    have hpull : p e = g a := by
      simpa using he
    exact ⟨⟨(e, a), hpull⟩, rfl⟩
  homotopyLift {X} _ _ {f₀} {f₁} H {g₀} hg₀ := by
    -- Route correction: lift only the first coordinate along `p`, then repackage the result.
    let g₀fst : C(X, E) := pullbackFirstCoordinate g₀
    have hg₀fst : p.comp g₀fst = g.comp f₀ := pullbackFirstCoordinateComp hg₀
    let Hg : (g.comp f₀).Homotopy (g.comp f₁) :=
      (ContinuousMap.Homotopy.refl g).comp H
    -- Apply the inherited covering homotopy property directly to avoid the universe-restricted
    -- convenience theorem.
    obtain ⟨g₁fst, Gfst, hGfst⟩ :=
      existsFirstCoordinateHomotopyLift (p := p) (g := g) (H := H) (g₀fst := g₀fst) hg₀fst
    have hg₁ : ∀ x, p (g₁fst x) = g (f₁ x) := by
      -- Evaluate the lifted first-coordinate homotopy at time `1`.
      intro x
      have hx : p (Gfst (1, x)) = Hg (1, x) := by
        simpa using ContinuousMap.congr_fun hGfst (1, x)
      simpa [Hg, Gfst.apply_one x, H.apply_one x] using hx
    have hGpullback : ∀ tx, p (Gfst tx) = g (H tx) := by
      -- Pointwise, the lifted homotopy in `E` projects to the given homotopy in `A`.
      intro tx
      have htx : p (Gfst tx) = Hg tx := by
        simpa using ContinuousMap.congr_fun hGfst tx
      simpa [Hg] using htx
    let g₁ : C(X, Function.Pullback p g) :=
      ⟨fun x ↦ ⟨(g₁fst x, f₁ x), hg₁ x⟩,
        continuous_pullbackPair (p := p) (g := g) (u := g₁fst) (v := f₁) hg₁⟩
    let G : g₀.Homotopy g₁ :=
      { toContinuousMap :=
        ⟨fun tx ↦ ⟨(Gfst tx, H tx), hGpullback tx⟩,
          continuous_pullbackPair (p := p) (g := g) (u := Gfst.toContinuousMap)
            (v := H.toContinuousMap) hGpullback⟩
        map_zero_left := by
          -- At time `0` we recover the given initial lift.
          intro x
          apply Subtype.ext
          apply Prod.ext
          · simp [g₀fst, Gfst.apply_zero x]
          · calc
              H (0, x) = f₀ x := H.apply_zero x
              _ = pullbackSnd p g (g₀ x) := (ContinuousMap.congr_fun hg₀ x).symm
              _ = (g₀ x).1.2 := rfl
        map_one_left := by
          -- At time `1` we arrive at the repackaged endpoint map.
          intro x
          apply Subtype.ext
          apply Prod.ext
          · simp [g₁, Gfst.apply_one x]
          · simp [g₁, H.apply_one x] }
    -- The second projection of the pullback-valued homotopy is exactly the base homotopy.
    refine ⟨g₁, G, ?_⟩
    ext tx
    rfl

/-- Lemma 7.1.5: pullbacks of fibrations are fibrations. If `p : C(E, B)` is a fibration and
`g : C(A, B)` is any continuous map, then the pullback projection `pullbackSnd p g` is a
fibration. -/
theorem pullbackSnd_isFibration {p : C(E, B)} (hp : IsFibration.{u, w, x} p) (g : C(A, B)) :
    IsFibration.{max u v, v, x} (pullbackSnd p g) := by
  -- Reuse the instance proved above with `hp` installed locally.
  let _ : IsFibration.{u, w, x} p := hp
  infer_instance
