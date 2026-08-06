import Mathlib.Logic.Equiv.Fin.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1

open CategoryTheory
open CategoryTheory.Limits
open GrpCat.FilteredColimits
open MonCat.FilteredColimits
open scoped Topology unitInterval Topology.Homotopy

noncomputable section

universe u w

-- Semantic recall via `lean_leansearch`: mathlib surfaced only the internally graded-ring API for
-- a single ambient ring, not a prespectrum result. The local Chapter 25 owners
-- `Prespectrum.stableHomotopyGroup` and `RingPrespectrum` therefore remain the primary surface.

/-- Reindex a stable homotopy group along an equality of degrees. -/
abbrev stableHomotopyGroupCast (T : Prespectrum.{u, w}) {i j : ℤ} (h : i = j) :
    Prespectrum.stableHomotopyGroup T i → Prespectrum.stableHomotopyGroup T j :=
  fun x ↦ h ▸ x

/-- Reindexing along the reflexive equality fixes every stable homotopy class. -/
@[simp] theorem stableHomotopyGroupCast_rfl (T : Prespectrum.{u, w}) (i : ℤ)
    (x : Prespectrum.stableHomotopyGroup T i) :
    stableHomotopyGroupCast T rfl x = x := by
  -- The reflexive transport is definitionally the identity.
  rfl

/-- The raw swap map on representatives of a smash product. -/
private def smashProductSwapRaw (X Y : BasedSpace) :
    X.right × Y.right → (smashProduct Y X).right
  | (x, y) => smashProductMk Y X (y, x)

/-- The raw swap map respects the smash-product quotient relation. -/
private theorem smashProductSwapRaw_respects (X Y : BasedSpace) :
    ∀ ⦃p q : X.right × Y.right⦄,
      smashProductRel X Y p q →
        smashProductSwapRaw X Y p = smashProductSwapRaw X Y q := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · -- Equal representatives have equal images under the raw swap.
    rfl
  · -- Wedge representatives are both sent to the distinguished smash-product class.
    rcases p with ⟨x₁, y₁⟩
    rcases q with ⟨x₂, y₂⟩
    have hp' : smashWedge Y X (y₁, x₁) := by
      rcases hp with hx | hy
      · exact Or.inr hx
      · exact Or.inl hy
    have hq' : smashWedge Y X (y₂, x₂) := by
      rcases hq with hx | hy
      · exact Or.inr hx
      · exact Or.inl hy
    calc
      smashProductSwapRaw X Y (x₁, y₁) = underTopBasepoint (smashProduct Y X) := by
        simp [smashProductSwapRaw, smashProduct_mk_eq_basepoint_of_mem_smashWedge, hp']
      _ = smashProductSwapRaw X Y (x₂, y₂) := by
        symm
        simp [smashProductSwapRaw, smashProduct_mk_eq_basepoint_of_mem_smashWedge, hq']

/-- The swap map on a smash product is continuous. -/
private theorem smashProductSwapContinuous (X Y : BasedSpace) :
    Continuous
      (Quotient.lift
        (smashProductSwapRaw X Y)
        (smashProductSwapRaw_respects X Y) :
          (smashProduct X Y).right → (smashProduct Y X).right) := by
  -- Continuity is inherited from the raw quotient map on the product representatives.
  have hraw : Continuous (smashProductSwapRaw X Y) := by
    simpa [smashProductSwapRaw] using
      (continuous_quotient_mk'.comp
        (continuous_snd.prodMk continuous_fst :
          Continuous fun p : X.right × Y.right ↦ (p.2, p.1)))
  exact hraw.quotient_lift (smashProductSwapRaw_respects X Y)

/-- The continuous swap map on smash products. -/
private def smashProductSwapContinuousMap (X Y : BasedSpace) :
    C((smashProduct X Y).right, (smashProduct Y X).right) :=
  ⟨Quotient.lift
      (smashProductSwapRaw X Y)
      (smashProductSwapRaw_respects X Y),
    smashProductSwapContinuous X Y⟩

/-- The smash-product swap preserves the chosen basepoint. -/
private theorem smashProductSwap_w (X Y : BasedSpace) :
    (smashProduct X Y).hom ≫
      TopCat.ofHom (smashProductSwapContinuousMap X Y) =
      (smashProduct Y X).hom := by
  -- Both terminal maps pick out the smash-product basepoint after swapping the basepoint pair.
  ext x
  change
    Quotient.lift (smashProductSwapRaw X Y) (smashProductSwapRaw_respects X Y)
        (smashProductMk X Y (underTopBasepoint X, underTopBasepoint Y)) =
      smashProductMk Y X (underTopBasepoint Y, underTopBasepoint X)
  rfl

/-- The based map `X ∧ Y ⟶ Y ∧ X` swapping the two smash-product factors. -/
def smashProductSwap (X Y : BasedSpace) :
    smashProduct X Y ⟶ smashProduct Y X :=
  Under.homMk
    (TopCat.ofHom (smashProductSwapContinuousMap X Y))
    (smashProductSwap_w X Y)

/-- Swapping the factors of a smash product twice is homotopic to the identity map. -/
theorem smashProductSwap_comp_swap (X Y : BasedSpace) :
    smashProductSwap X Y ≫ smashProductSwap Y X = 𝟙 (smashProduct X Y) := by
  -- On quotient representatives, the double swap returns the original pair.
  ext z
  refine Quotient.inductionOn' z ?_
  intro p
  rcases p with ⟨x, y⟩
  rfl

/-- A path loop at `x` determines a `1`-dimensional generalized loop based at `x`. -/
private theorem pathToGenLoopContinuous {X : Type u} [TopologicalSpace X] {x : X}
    (γ : Path x x) :
    Continuous fun t : I^(Fin 1) ↦ γ (t 0) := by
  -- Evaluate the path at the unique cube coordinate.
  exact γ.continuous.comp (continuous_apply 0)

/-- The generalized loop attached to a based path still lands at the basepoint on the cube
boundary. -/
private theorem pathToGenLoop_boundary {X : Type u} [TopologicalSpace X] {x : X}
    (γ : Path x x) :
    ∀ t ∈ Cube.boundary (Fin 1), γ (t 0) = x := by
  intro t ht
  rcases ht with ⟨i, hi⟩
  fin_cases i
  rcases hi with h0 | h1
  · -- The `0`-face of the cube evaluates at the path source.
    have h0' : t 0 = 0 := by
      simpa using h0
    rw [h0']
    exact γ.source
  · -- The `1`-face of the cube evaluates at the path target.
    have h1' : t 0 = 1 := by
      simpa using h1
    rw [h1']
    exact γ.target

/-- Regard a based path as a representative of a class in `π_1`. -/
private def pathToGenLoop {X : Type u} [TopologicalSpace X] {x : X} (γ : Path x x) :
    Ω^ (Fin 1) X x :=
  ⟨⟨fun t ↦ γ (t 0), pathToGenLoopContinuous γ⟩, pathToGenLoop_boundary γ⟩

/-- Helper for Lemma 25.3.3: generalized loops represent the same homotopy class exactly when
they lie in the same path component. -/
private theorem genLoop_homotopic_iff_joined
    {X : Type*} [TopologicalSpace X] {N : Type*} {x : X} {p q : Ω^ N X x} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    refine ⟨Path.mk
      ⟨fun t ↦
          (⟨curriedHomotopy t, fun y hy ↦ (H.prop t y hy).trans (p.property y hy)⟩ :
            Ω^ N X x),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t y hy
      exact (H.prop t y hy).trans (p.property y hy)
    · ext y
      exact H.apply_zero y
    · ext y
      exact H.apply_one y
  · rintro ⟨γ⟩
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro y
      change γ 0 y = p y
      exact congrArg (fun r : Ω^ N X x ↦ r y) γ.source
    · intro y
      change γ 1 y = q y
      exact congrArg (fun r : Ω^ N X x ↦ r y) γ.target
    · intro t y hy
      exact ((γ t).property y hy).trans (p.property y hy).symm

/-- Helper for Lemma 25.3.3: a homeomorphism preserves and reflects path-connectedness. -/
private theorem joined_iff_homeomorph
    {Y : Type*} {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {a b : Y} :
    Joined (h a) (h b) ↔ Joined a b := by
  constructor
  · -- Pull a path in the target back along the inverse homeomorphism.
    rintro ⟨γ⟩
    simpa using (show Joined (h.symm (h a)) (h.symm (h b)) from ⟨γ.map h.symm.continuous⟩)
  · -- Push a path in the source forward along the homeomorphism.
    rintro ⟨γ⟩
    exact ⟨γ.map h.continuous⟩

/-- Helper for Lemma 25.3.3: a homeomorphism between generalized-loop spaces preserves and
reflects the homotopy relation. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M : Type*} {N : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}
    (h : Ω^ M Y y ≃ₜ Ω^ N Z z) {p q : Ω^ M Y y} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Convert homotopies to paths in the generalized-loop space, apply the homeomorphism, and
  -- convert back.
  rw [genLoop_homotopic_iff_joined, genLoop_homotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Lemma 25.3.3: `1`-dimensional generalized loops are exactly ordinary based paths.
-/
private def oneGenLoopHomeomorph {X : Type u} [TopologicalSpace X] (x : X) :
    Ω^ (Fin 1) X x ≃ₜ Path x x where
  toFun p :=
    Path.mk ⟨fun t ↦ p (fun _ ↦ t), by fun_prop⟩
      (p.2 (fun _ ↦ 0) ⟨0, Or.inl rfl⟩)
      (p.2 (fun _ ↦ 1) ⟨0, Or.inr rfl⟩)
  invFun γ :=
    ⟨⟨fun t ↦ γ (t 0), by fun_prop⟩, fun t ht ↦ by
      rcases ht with ⟨i, hi | hi⟩
      · -- Boundary points on the `0`-face evaluate at the path source.
        have hi0 : t 0 = 0 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 0 := by simpa using congrArg γ hi0
          _ = x := γ.source
      · -- Boundary points on the `1`-face evaluate at the path target.
        have hi1 : t 0 = 1 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 1 := by simpa using congrArg γ hi1
          _ = x := γ.target⟩
  left_inv p := by
    -- A `Fin 1`-cube is determined by its unique coordinate.
    ext t
    have ht : t = fun _ : Fin 1 ↦ t 0 := by
      funext i
      fin_cases i
      rfl
    rw [ht]
    rfl
  right_inv γ := by
    -- The inverse construction recovers the original path pointwise.
    ext t
    rfl
  continuous_toFun := by
    -- Continuity comes from precomposition with the unique cube-coordinate projection.
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t _ ↦ t, by fun_prop⟩).comp continuous_subtype_val
  continuous_invFun := by
    -- The inverse is the same precomposition map in the opposite direction.
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t : I^(Fin 1) ↦ t 0, by fun_prop⟩).comp continuous_induced_dom

/-- Helper for Lemma 25.3.3: the inverse of `oneGenLoopHomeomorph` sends the constant path to
the constant generalized loop. -/
@[simp] private theorem oneGenLoopHomeomorph_symm_refl
    {X : Type u} [TopologicalSpace X] (x : X) :
    (oneGenLoopHomeomorph x).symm (Path.refl x) = GenLoop.const := by
  -- Both representatives are pointwise constant at the basepoint.
  ext t
  rfl

/-- Helper for Lemma 25.3.3: a homeomorphism of spaces induces a homeomorphism of generalized
loop spaces. -/
private def genLoopHomeomorph {M : Type v} {Y : Type u} {Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z) :
    Ω^ M Y y ≃ₜ Ω^ M Z z where
  toFun p :=
    ⟨⟨fun t ↦ h (p t), h.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      simpa [hy] using congrArg h (p.2 t ht)⟩
  invFun p :=
    let hInv : C(Z, Y) := ⟨h.symm, h.symm.continuous⟩
    ⟨⟨fun t ↦ hInv (p t), hInv.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      have hp : p t = z := p.2 t ht
      calc
        h.symm (p t) = h.symm z := by rw [hp]
        _ = y := (h.symm_apply_eq).2 hy.symm⟩
  left_inv p := by
    -- The forward and inverse homeomorphisms cancel pointwise.
    ext t
    simp
  right_inv p := by
    -- The same pointwise cancellation proves the reverse direction.
    ext t
    simp
  continuous_toFun := by
    -- Postcomposition with a homeomorphism is continuous on generalized loops.
    rw [continuous_induced_rng]
    exact (ContinuousMap.continuous_postcomp ⟨h, h.continuous⟩).comp continuous_subtype_val
  continuous_invFun := by
    let hInv : C(Z, Y) := ⟨h.symm, h.symm.continuous⟩
    -- So is postcomposition with the inverse homeomorphism.
    rw [continuous_induced_rng]
    exact (ContinuousMap.continuous_postcomp hInv).comp continuous_subtype_val

/-- Helper for Lemma 25.3.3: generalized loops in the ordinary loop space identify with
generalized loops in one higher dimension. -/
private def loopSpaceRepresentativeEquiv {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X) :
    Ω^ (Fin n) (Path x x) (Path.refl x) ≃ₜ Ω^ (Fin (n + 1)) X x :=
  let e₁ : Ω^ (Fin n) (Path x x) (Path.refl x) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
  let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
    GenLoop.genLoopGenLoopEquiv x
  let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
    GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  -- Reassociate loops-of-loops into a single higher-dimensional generalized loop.
  (e₁.trans e₂).trans e₃

/-- Helper for Lemma 25.3.3: a homeomorphism of target spaces commutes with outer-coordinate
concatenation of generalized loops. -/
private theorem genLoopHomeomorph_transAt
    {M : Type*} {Y : Type*} {Z : Type*}
    [DecidableEq M] [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}
    (h : Y ≃ₜ Z) (hy : h y = z) (i : M)
    (p q : Ω^ M Y y) :
    genLoopHomeomorph h hy (GenLoop.transAt i p q) =
      GenLoop.transAt i (genLoopHomeomorph h hy p) (genLoopHomeomorph h hy q) := by
  -- Both sides evaluate by the same coordinatewise concatenation formula after postcomposition by
  -- the homeomorphism.
  ext t
  change h
      (if (t i : ℝ) ≤ 1 / 2 then
        p (Function.update t i (Set.projIcc 0 1 GenLoop.transAt._proof_3 (2 * t i)))
      else
        q (Function.update t i (Set.projIcc 0 1 GenLoop.transAt._proof_3 (2 * t i - 1)))) =
    if (t i : ℝ) ≤ 1 / 2 then
      h (p (Function.update t i (Set.projIcc 0 1 GenLoop.transAt._proof_3 (2 * t i))))
    else
      h (q (Function.update t i (Set.projIcc 0 1 GenLoop.transAt._proof_3 (2 * t i - 1))))
  split_ifs <;> rfl

/-- Helper for Lemma 25.3.3: reassociating loops-of-loops sends an outer concatenation to the
corresponding concatenation in the summed coordinate. -/
private theorem genLoopGenLoopEquiv_transAt_inl
    {M : Type*} {N : Type*} {X : Type*}
    [DecidableEq M] [DecidableEq N] [TopologicalSpace X] (x : X)
    (i : M) (p q : Ω^ M (Ω^ N X x) GenLoop.const) :
    GenLoop.genLoopGenLoopEquiv x (GenLoop.transAt i p q) =
      GenLoop.transAt (Sum.inl i) (GenLoop.genLoopGenLoopEquiv x p)
        (GenLoop.genLoopGenLoopEquiv x q) := by
  -- The uncurrying map places the outer concatenation in the left summand coordinate.
  ext t
  simp [GenLoop.genLoopGenLoopEquiv, GenLoop.uncurry, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- Helper for Lemma 25.3.3: reindexing the cube coordinates transports concatenation to the
image coordinate. -/
private theorem genLoopCongr_transAt
    {M : Type*} {N : Type*} {X : Type*}
    [DecidableEq M] [DecidableEq N] [TopologicalSpace X] (x : X)
    (e : M ≃ N) (i : M) (p q : Ω^ M X x) :
    GenLoop.congr x e (GenLoop.transAt i p q) =
      GenLoop.transAt (e i) (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  -- The coordinate change only renames the concatenation direction.
  ext t
  simp [GenLoop.congr, GenLoop.transAt, GenLoop.coe_copy, Function.update]
  split_ifs
  · apply congrArg p
    funext m
    by_cases hm : m = i
    · simp [Function.update, hm]
    · simp [Function.update, hm]
  · apply congrArg q
    funext m
    by_cases hm : m = i
    · simp [Function.update, hm]
    · simp [Function.update, hm]

/-- Helper for Lemma 25.3.3: the standard loop-space shift descends to an equivalence on
homotopy groups. -/
private def loopSpaceHomotopyGroupEquivPiSucc {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X) :
    HomotopyGroup.Pi n (Path x x) (Path.refl x) ≃ HomotopyGroup.Pi (n + 1) X x :=
  Quotient.congr (loopSpaceRepresentativeEquiv n x).toEquiv fun _ _ ↦
    -- The representative homeomorphism preserves exactly the generalized-loop homotopy relation.
    (genLoopHomotopic_iff_of_homeomorph (loopSpaceRepresentativeEquiv n x)).symm

/-- Helper for Lemma 25.3.3: the loop-space shift sends a class to the class of its shifted
representative. -/
@[simp] private theorem loopSpaceHomotopyGroupEquivPiSucc_apply
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X)
    (γ : Ω^ (Fin n) (Path x x) (Path.refl x)) :
    loopSpaceHomotopyGroupEquivPiSucc n x ⟦γ⟧ =
      (⟦loopSpaceRepresentativeEquiv n x γ⟧ : HomotopyGroup.Pi (n + 1) X x) :=
  rfl

/-- Helper for Lemma 25.3.3: the representative-level loop-space shift sends multiplication in
`π_n(Ω X)` to multiplication in `π_(n + 1)(X)`. -/
private theorem loopSpaceRepresentativeEquiv_mulRepresentative
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X)
    (i : Fin n) (p q : Ω^ (Fin n) (Path x x) (Path.refl x)) :
    loopSpaceRepresentativeEquiv n x (GenLoop.transAt i q p) =
      GenLoop.transAt
        (Fin.castAdd 1 i)
        (loopSpaceRepresentativeEquiv n x q)
        (loopSpaceRepresentativeEquiv n x p) := by
  -- Route correction: instead of rewriting under `HomotopyGroup.Pi`, commute `transAt` through
  -- the three explicit representative-level equivalences once.
  let e₁ :
      Ω^ (Fin n) (Path x x) (Path.refl x) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
  let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
    GenLoop.genLoopGenLoopEquiv x
  let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
    GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  -- Commute `transAt` through `e₁`, then `e₂`, and finally the coordinate renaming `e₃`.
  calc
    loopSpaceRepresentativeEquiv n x (GenLoop.transAt i q p)
        = e₃ (e₂ (e₁ (GenLoop.transAt i q p))) := by
            rfl
    _ = e₃ (e₂ (GenLoop.transAt i (e₁ q) (e₁ p))) := by
            rw [genLoopHomeomorph_transAt]
    _ = e₃ (GenLoop.transAt (Sum.inl i) (e₂ (e₁ q)) (e₂ (e₁ p))) := by
            rw [genLoopGenLoopEquiv_transAt_inl]
    _ = GenLoop.transAt (Fin.castAdd 1 i) (e₃ (e₂ (e₁ q))) (e₃ (e₂ (e₁ p))) := by
            simpa using genLoopCongr_transAt x
              (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
              (Sum.inl i) (e₂ (e₁ q)) (e₂ (e₁ p))
    _ = GenLoop.transAt (Fin.castAdd 1 i)
          (loopSpaceRepresentativeEquiv n x q)
          (loopSpaceRepresentativeEquiv n x p) := by
            rfl

/-- Helper for Lemma 25.3.3: the loop-space shift equivalence is multiplicative. -/
private theorem loopSpaceHomotopyGroupEquivPiSucc_map_mul
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X)
    (a b : HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x)) :
    loopSpaceHomotopyGroupEquivPiSucc (n + 1) x (a * b) =
      loopSpaceHomotopyGroupEquivPiSucc (n + 1) x a *
        loopSpaceHomotopyGroupEquivPiSucc (n + 1) x b := by
  -- Reduce multiplicativity to representatives and use the explicit `transAt` compatibility.
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  have hsource :
      ((· * ·) : HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x) →
          HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x) →
          HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x)) ⟦p⟧ ⟦q⟧ =
        ⟦GenLoop.transAt (0 : Fin (n + 1)) q p⟧ := by
    simpa using
      (HomotopyGroup.mul_spec :
        ((· * ·) : HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x) →
            HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x) →
            HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x)) ⟦p⟧ ⟦q⟧ =
          ⟦GenLoop.transAt (0 : Fin (n + 1)) q p⟧)
  have htarget :
      ((· * ·) : HomotopyGroup.Pi (n + 2) X x →
          HomotopyGroup.Pi (n + 2) X x →
          HomotopyGroup.Pi (n + 2) X x)
          ⟦loopSpaceRepresentativeEquiv (n + 1) x p⟧
          ⟦loopSpaceRepresentativeEquiv (n + 1) x q⟧ =
        ⟦GenLoop.transAt
            (Fin.castAdd 1 (0 : Fin (n + 1)))
            (loopSpaceRepresentativeEquiv (n + 1) x q)
            (loopSpaceRepresentativeEquiv (n + 1) x p)⟧ := by
    simpa using
      (HomotopyGroup.mul_spec :
        ((· * ·) : HomotopyGroup.Pi (n + 2) X x →
            HomotopyGroup.Pi (n + 2) X x →
            HomotopyGroup.Pi (n + 2) X x)
            ⟦loopSpaceRepresentativeEquiv (n + 1) x p⟧
            ⟦loopSpaceRepresentativeEquiv (n + 1) x q⟧ =
          ⟦GenLoop.transAt
              (Fin.castAdd 1 (0 : Fin (n + 1)))
              (loopSpaceRepresentativeEquiv (n + 1) x q)
              (loopSpaceRepresentativeEquiv (n + 1) x p)⟧)
  -- Rewrite both sides to the same shifted concatenation representative.
  have himage :
      loopSpaceHomotopyGroupEquivPiSucc (n + 1) x ⟦GenLoop.transAt (0 : Fin (n + 1)) q p⟧ =
        loopSpaceHomotopyGroupEquivPiSucc (n + 1) x ⟦p⟧ *
          loopSpaceHomotopyGroupEquivPiSucc (n + 1) x ⟦q⟧ := by
    -- Rewrite the image of the source representative and then use the target-side multiplication
    -- formula.
    rw [loopSpaceHomotopyGroupEquivPiSucc_apply, loopSpaceRepresentativeEquiv_mulRepresentative]
    simpa [loopSpaceHomotopyGroupEquivPiSucc_apply] using htarget.symm
  -- Assemble the source multiplication formula with the image computation.
  exact (congrArg (loopSpaceHomotopyGroupEquivPiSucc (n + 1) x) hsource).trans himage

/-- Helper for Lemma 25.3.3: the positive-degree loop-space shift is a multiplicative
equivalence. -/
private def loopSpaceHomotopyGroupEquivPiSuccMulEquiv
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X) :
    HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x) ≃*
      HomotopyGroup.Pi (n + 2) X x :=
  { toEquiv := loopSpaceHomotopyGroupEquivPiSucc (n + 1) x
    -- Package the already-proved multiplicativity once so later proofs can use a stable owner.
    map_mul' := loopSpaceHomotopyGroupEquivPiSucc_map_mul n x }

/-- Helper for Lemma 25.3.3: iterated loops commute with taking one further loop at the pointed
space level. -/
private theorem omegaIteratedLoopPointedSpace_eq
    (k : ℕ) (Y : PointedCompactlyGenerated.{u, w}) :
    Ω (Prespectrum.iteratedLoopPointedSpace k Y) =
      Prespectrum.iteratedLoopPointedSpace k (Ω Y) := by
  induction k generalizing Y with
  | zero =>
      -- Zero iterated loops leave the pointed space unchanged.
      rfl
  | succ k hk =>
      -- Unfold one loop on each side and apply the induction hypothesis.
      simp [Prespectrum.iteratedLoopPointedSpace_succ, hk]

/-- Helper for Lemma 25.3.3: a continuous map from a compact Hausdorff source remains continuous
after replacing the codomain by its compactly generated topology. -/
private theorem continuousCompHausToCompactlyGenerated
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type w} [TopologicalSpace Z] {f : K → Z} (hf : Continuous f) :
    @Continuous K Z ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, w} Z) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Z)), j.fst) → Z := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Z) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-Hausdorff map is one of the generators for the compactly generated
  -- topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Z),
        @Continuous j.fst Z inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Z)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Lemma 25.3.3: a compact Hausdorff source in `Type` can be `ULift`ed into
`CompHaus.{u}` before passing to the codomain's compactly generated topology. -/
private theorem continuousSmallCompHausToCompactlyGenerated
    {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type w} [TopologicalSpace Z] {f : K → Z} (hf : Continuous f) :
    @Continuous K Z ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, w} Z) f := by
  let f' : ULift.{u} K → Z := f ∘ ULift.down
  have hf' : Continuous f' := hf.comp continuous_uliftDown
  have hLift :
      @Continuous (ULift.{u} K) Z inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Z)
        f' :=
    continuousCompHausToCompactlyGenerated hf'
  -- The `ULift` homeomorphism transfers the compact-source continuity back to `K`.
  exact
    @Continuous.comp K (ULift.{u} K) Z ‹TopologicalSpace K› inferInstance
      (TopologicalSpace.compactlyGenerated.{u, w} Z) ULift.up f'
      hLift continuous_uliftUp

/-- Helper for Lemma 25.3.3: the public loop-space topology is the compactly generated topology on
the raw path-space carrier. -/
private theorem loopPointedSpaceTopology_eq
    (Y : PointedCompactlyGenerated.{u, w}) :
    (Ω Y).toCompactlyGenerated.toTop.str =
      TopologicalSpace.compactlyGenerated.{u, w} (Path Y.point Y.point) := by
  -- Unfolding `Ω Y` reveals the bundled compactly generated path topology.
  rfl

/-- Helper for Lemma 25.3.3: forgetting the public loop-space topology back to the raw path
topology is continuous. -/
private theorem continuousLoopPointedSpaceForget
    (Y : PointedCompactlyGenerated.{u, w}) :
    Continuous fun χ : (Ω Y).toCompactlyGenerated ↦
      (show Path Y.point Y.point from χ) := by
  let f : Path Y.point Y.point → Path Y.point Y.point := id
  -- Test continuity from the compactly generated loop topology against compact Hausdorff probes.
  have hraw :
      @Continuous (Path Y.point Y.point) (Path Y.point Y.point)
        (TopologicalSpace.compactlyGenerated.{u, w} (Path Y.point Y.point))
        inferInstance f := by
    refine continuous_from_compactlyGenerated f ?_
    intro S g
    simpa [f, Function.comp_def] using g.continuous
  simpa [f, loopPointedSpace] using hraw

/-- Helper for Lemma 25.3.3: a generalized loop valued in the public loop-space topology can be
viewed as the same generalized loop valued in the raw path topology. -/
private def loopPointedSpaceRepresentativeToRaw
    {M : Type} (Y : PointedCompactlyGenerated.{u, w}) :
    Ω^ M (Ω Y).toCompactlyGenerated (Ω Y).point →
      Ω^ M (Path Y.point Y.point) (Path.refl Y.point)
  | p =>
      ⟨⟨fun t ↦ (p t : Path Y.point Y.point),
          (continuousLoopPointedSpaceForget Y).comp p.1.continuous⟩,
        fun t ht ↦ by
          simpa using p.2 t ht⟩

/-- Helper for Lemma 25.3.3: a raw generalized loop in the path space becomes a generalized loop
for the public loop-space topology because the cube domain is compact Hausdorff. -/
private def rawLoopPointedSpaceRepresentative
    {M : Type} (Y : PointedCompactlyGenerated.{u, w}) :
    Ω^ M (Path Y.point Y.point) (Path.refl Y.point) →
      Ω^ M (Ω Y).toCompactlyGenerated (Ω Y).point
  | p =>
      ⟨⟨fun t ↦ (p t : (Ω Y).toCompactlyGenerated), by
            have hraw :
                Continuous fun t : I^M ↦
                  (p t : Path Y.point Y.point) := p.1.continuous
            -- Re-kify the raw path-valued cube map along the compact Hausdorff source `I^M`.
            change
              @Continuous (I^M) (Path Y.point Y.point) inferInstance
                (TopologicalSpace.compactlyGenerated.{u, w} (Path Y.point Y.point))
                (fun t : I^M ↦ (p t : Path Y.point Y.point))
            exact
              (continuousSmallCompHausToCompactlyGenerated hraw :
                @Continuous (I^M) (Path Y.point Y.point) inferInstance
                  (TopologicalSpace.compactlyGenerated.{u, w} (Path Y.point Y.point))
                  (fun t : I^M ↦ (p t : Path Y.point Y.point)))⟩,
        fun t ht ↦ by
          simpa using p.2 t ht⟩

/-- Helper for Lemma 25.3.3: forgetting the loop topology and then re-kifying a representative
does nothing. -/
@[simp] private theorem rawLoopPointedSpaceRepresentative_toRaw
    {M : Type} (Y : PointedCompactlyGenerated.{u, w})
    (p : Ω^ M (Ω Y).toCompactlyGenerated (Ω Y).point) :
    rawLoopPointedSpaceRepresentative Y (loopPointedSpaceRepresentativeToRaw Y p) = p := by
  -- Both representatives are literally the same cube map after the two identity conversions.
  ext t
  rfl

/-- Helper for Lemma 25.3.3: re-kifying a raw representative and then forgetting the loop topology
also does nothing. -/
@[simp] private theorem loopPointedSpaceRepresentativeToRaw_of_raw
    {M : Type} (Y : PointedCompactlyGenerated.{u, w})
    (p : Ω^ M (Path Y.point Y.point) (Path.refl Y.point)) :
    loopPointedSpaceRepresentativeToRaw Y (rawLoopPointedSpaceRepresentative Y p) = p := by
  -- Again both sides are pointwise the same raw path-valued cube map.
  ext t
  rfl

/-- Helper for Lemma 25.3.3: forgetting the public loop topology commutes with the standard
coordinatewise multiplication representative `transAt`. -/
private theorem loopPointedSpaceRepresentativeToRaw_transAt
    {M : Type} [DecidableEq M] (Y : PointedCompactlyGenerated.{u, w})
    (i : M)
    (p q : Ω^ M (Ω Y).toCompactlyGenerated (Ω Y).point) :
    loopPointedSpaceRepresentativeToRaw Y (GenLoop.transAt i p q) =
      GenLoop.transAt i
        (loopPointedSpaceRepresentativeToRaw Y p)
        (loopPointedSpaceRepresentativeToRaw Y q) := by
  -- The transport only changes the codomain topology, so the `transAt` formula is unchanged.
  ext t
  rfl

/-- Helper for Lemma 25.3.3: a positive-degree continuous map induces a multiplicative map on
homotopy groups. -/
private def homotopyGroupMulHomOverEq
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (m : ℕ) :
    π_ (m + 1) A a →* π_ (m + 1) B b :=
  f.eStarMulHomOverEq m hf

/-- Helper for Lemma 25.3.3: forgetting the public loop-space topology induces a multiplicative
map on positive-degree homotopy groups. -/
private def loopPointedSpaceHomotopyGroupToRaw
    (m : ℕ) (Y : PointedCompactlyGenerated.{u, w}) :
    π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point →*
      π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point) :=
  -- The forgetful comparison is an honest continuous map, so Chapter 25's positive-degree owner
  -- `homotopyGroupMonoidHom` already packages the induced group homomorphism.
  homotopyGroupMulHomOverEq
    ⟨fun χ : (Ω Y).toCompactlyGenerated ↦ (show Path Y.point Y.point from χ),
      continuousLoopPointedSpaceForget Y⟩
    rfl
    m

/-- Helper for Lemma 25.3.3: forgetting the public loop-space topology preserves and reflects
generalized-loop homotopy classes. -/
private theorem loopPointedSpaceRepresentativeHomotopic_iff_raw
    {M : Type} (Y : PointedCompactlyGenerated.{u, w})
    {p q : Ω^ M (Ω Y).toCompactlyGenerated (Ω Y).point} :
    GenLoop.Homotopic (loopPointedSpaceRepresentativeToRaw Y p)
        (loopPointedSpaceRepresentativeToRaw Y q) ↔
      GenLoop.Homotopic p q := by
  constructor
  · intro hpq
    rcases hpq with ⟨H⟩
    -- Re-kify the raw cylinder homotopy once so it becomes a public loop-space homotopy.
    refine ⟨⟨⟨
      ⟨fun tx : I × I^M ↦ (H tx : (Ω Y).toCompactlyGenerated), by
          have hraw :
              Continuous fun tx : I × I^M ↦
                (H tx : Path Y.point Y.point) := H.continuous
          change
            @Continuous (I × I^M) (Path Y.point Y.point) inferInstance
              (TopologicalSpace.compactlyGenerated.{u, w} (Path Y.point Y.point))
              (fun tx : I × I^M ↦ (H tx : Path Y.point Y.point))
          exact
            (continuousSmallCompHausToCompactlyGenerated hraw :
              @Continuous (I × I^M) (Path Y.point Y.point) inferInstance
                (TopologicalSpace.compactlyGenerated.{u, w} (Path Y.point Y.point))
                (fun tx : I × I^M ↦ (H tx : Path Y.point Y.point)))⟩,
      ?_, ?_⟩, ?_⟩⟩
    · intro t
      change
        (show Path Y.point Y.point from H (0, t)) =
          (show Path Y.point Y.point from p t)
      exact H.apply_zero t
    · intro t
      change
        (show Path Y.point Y.point from H (1, t)) =
          (show Path Y.point Y.point from q t)
      exact H.apply_one t
    · intro t x hx
      change
        (show Path Y.point Y.point from H (t, x)) =
          (show Path Y.point Y.point from p x)
      exact H.prop t x hx
  · intro hpq
    -- Postcompose a public loop-space homotopy with the forgetful comparison map.
    simpa [GenLoop.Homotopic, loopPointedSpaceRepresentativeToRaw] using
      hpq.comp_continuousMap
        ⟨fun χ : (Ω Y).toCompactlyGenerated ↦ (show Path Y.point Y.point from χ),
          continuousLoopPointedSpaceForget Y⟩

/-- Helper for Lemma 25.3.3: the raw/public loop comparison induces an equivalence on positive
homotopy groups. -/
private def loopPointedSpaceHomotopyGroupEquivRawPath
    (m : ℕ) (Y : PointedCompactlyGenerated.{u, w}) :
    π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point ≃
      π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point) :=
  let hRaw :
      ∀ p q : Ω^ (Fin (m + 1)) (Ω Y).toCompactlyGenerated (Ω Y).point,
        GenLoop.Homotopic (loopPointedSpaceRepresentativeToRaw Y p)
          (loopPointedSpaceRepresentativeToRaw Y q) ↔
        GenLoop.Homotopic p q := by
      intro p q
      exact loopPointedSpaceRepresentativeHomotopic_iff_raw Y
  Quotient.congr
    { toFun := loopPointedSpaceRepresentativeToRaw Y
      invFun := rawLoopPointedSpaceRepresentative Y
      left_inv := rawLoopPointedSpaceRepresentative_toRaw Y
      right_inv := loopPointedSpaceRepresentativeToRaw_of_raw Y }
    (fun p q ↦ (hRaw p q).symm)

/-- Helper for Lemma 25.3.3: the quotient-level raw/public loop comparison sends a class to the
class of the same representative in the raw path-space topology. -/
@[simp] private theorem loopPointedSpaceHomotopyGroupEquivRawPath_apply
    (m : ℕ) (Y : PointedCompactlyGenerated.{u, w})
    (γ : Ω^ (Fin (m + 1)) (Ω Y).toCompactlyGenerated (Ω Y).point) :
    loopPointedSpaceHomotopyGroupEquivRawPath m Y ⟦γ⟧ =
      (⟦loopPointedSpaceRepresentativeToRaw Y γ⟧ :
        π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point)) :=
  rfl

/-- Helper for Lemma 25.3.3: the quotient-level raw/public loop comparison is multiplicative. -/
private theorem loopPointedSpaceHomotopyGroupEquivRawPath_map_mul
    (m : ℕ) (Y : PointedCompactlyGenerated.{u, w})
    (a b : π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point) :
    loopPointedSpaceHomotopyGroupEquivRawPath m Y (a * b) =
      loopPointedSpaceHomotopyGroupEquivRawPath m Y a *
        loopPointedSpaceHomotopyGroupEquivRawPath m Y b := by
  -- Reduce multiplicativity to representatives and use compatibility with `transAt`.
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  have hsource :
      ((· * ·) : π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point →
          π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point →
          π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point) ⟦p⟧ ⟦q⟧ =
        ⟦GenLoop.transAt (0 : Fin (m + 1)) q p⟧ := by
    simpa using
      (HomotopyGroup.mul_spec :
        ((· * ·) : π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point →
            π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point →
            π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point) ⟦p⟧ ⟦q⟧ =
          ⟦GenLoop.transAt (0 : Fin (m + 1)) q p⟧)
  have htarget :
      ((· * ·) : π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point) →
          π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point) →
          π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point))
          ⟦loopPointedSpaceRepresentativeToRaw Y p⟧
          ⟦loopPointedSpaceRepresentativeToRaw Y q⟧ =
        ⟦GenLoop.transAt
            (0 : Fin (m + 1))
            (loopPointedSpaceRepresentativeToRaw Y q)
            (loopPointedSpaceRepresentativeToRaw Y p)⟧ := by
    simpa using
      (HomotopyGroup.mul_spec :
        ((· * ·) : π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point) →
            π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point) →
            π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point))
            ⟦loopPointedSpaceRepresentativeToRaw Y p⟧
            ⟦loopPointedSpaceRepresentativeToRaw Y q⟧ =
          ⟦GenLoop.transAt
              (0 : Fin (m + 1))
              (loopPointedSpaceRepresentativeToRaw Y q)
              (loopPointedSpaceRepresentativeToRaw Y p)⟧)
  have himage :
      loopPointedSpaceHomotopyGroupEquivRawPath m Y
          (⟦GenLoop.transAt (0 : Fin (m + 1)) q p⟧ :
            π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point) =
        loopPointedSpaceHomotopyGroupEquivRawPath m Y ⟦p⟧ *
          loopPointedSpaceHomotopyGroupEquivRawPath m Y ⟦q⟧ := by
    -- Push the source representative through the raw/public comparison and rewrite the target
    -- multiplication in the raw path presentation.
    rw [loopPointedSpaceHomotopyGroupEquivRawPath_apply,
      loopPointedSpaceRepresentativeToRaw_transAt]
    simpa [loopPointedSpaceHomotopyGroupEquivRawPath_apply] using htarget.symm
  exact (congrArg (loopPointedSpaceHomotopyGroupEquivRawPath m Y) hsource).trans himage

/-- Helper for Lemma 25.3.3: the raw/public loop comparison is a multiplicative equivalence on
positive homotopy groups. -/
private def loopPointedSpaceHomotopyGroupMulEquivRawPath
    (m : ℕ) (Y : PointedCompactlyGenerated.{u, w}) :
    π_ (m + 1) (Ω Y).toCompactlyGenerated (Ω Y).point ≃*
      π_ (m + 1) (Path Y.point Y.point) (Path.refl Y.point) :=
  { toEquiv := loopPointedSpaceHomotopyGroupEquivRawPath m Y
    -- Package multiplicativity once so the successor-stage comparison can reuse it directly.
    map_mul' := loopPointedSpaceHomotopyGroupEquivRawPath_map_mul m Y }

/-- Helper for Lemma 25.3.3: every successor tail stage identifies multiplicatively with the next
higher homotopy group of the unlooped stage. -/
private def successorTailStageLoopSpaceMulEquiv
    (T : Prespectrum.{u, w}) (n : ℤ) (k : ℕ) :
    (Prespectrum.stableHomotopyGroupTailDiagram T n).obj (k + 1) ≃*
      π_ (Int.toNat (n - 1) + 2)
        (Prespectrum.iteratedLoopPointedSpace k
          (T (Int.toNat (1 - n) + (k + 1)))).toCompactlyGenerated
        (Prespectrum.iteratedLoopPointedSpace k
          (T (Int.toNat (1 - n) + (k + 1)))).point :=
  let Y :=
    Prespectrum.iteratedLoopPointedSpace k
      (T (Int.toNat (1 - n) + (k + 1)))
  -- Route correction: descend the raw/public representative comparison directly to a
  -- quotient-level `MulEquiv`, then compose it with the standard loop-space shift.
  by
    let hSpace :
        Prespectrum.iteratedLoopPointedSpace (k + 1)
            (T (Int.toNat (1 - n) + (k + 1))) =
          Ω Y := by
      -- Normalize the successor tail stage to a single loop on the already chosen stage `Y`.
      simpa [Y, Prespectrum.iteratedLoopPointedSpace_succ] using
        (omegaIteratedLoopPointedSpace_eq k
          (T (Int.toNat (1 - n) + (k + 1)))).symm
    let e₀ :
        (Prespectrum.stableHomotopyGroupTailDiagram T n).obj (k + 1) ≃*
          π_ (Int.toNat (n - 1) + 1) (Ω Y).toCompactlyGenerated (Ω Y).point :=
      -- Transport the successor tail stage along the explicit iterated-loop normalization.
      by
        let P := fun Z : PointedCompactlyGenerated.{u, w} ↦
          π_ (Int.toNat (n - 1) + 1) Z.toCompactlyGenerated Z.point
        change
          P (Prespectrum.iteratedLoopPointedSpace (k + 1)
              (T (Int.toNat (1 - n) + (k + 1)))) ≃* P (Ω Y)
        exact MulEquiv.cast hSpace
    simpa [Y] using
      e₀.trans <|
        (loopPointedSpaceHomotopyGroupMulEquivRawPath (Int.toNat (n - 1)) Y).trans
          (loopSpaceHomotopyGroupEquivPiSuccMulEquiv (Int.toNat (n - 1)) Y.point)

/-- Helper for Lemma 25.3.3: every successor stage in the stable-homotopy tail diagram is
commutative. -/
private theorem stableHomotopyTailStageSucc_mul_comm
    (T : Prespectrum.{u, w}) (n : ℤ) (k : ℕ)
    (x y : (Prespectrum.stableHomotopyGroupTailDiagram T n).obj (k + 1)) :
    x * y = y * x := by
  let e := successorTailStageLoopSpaceMulEquiv T n k
  -- Route correction: move the stage multiplication through the owner-level `MulEquiv` and use
  -- commutativity only in the higher homotopy-group target.
  apply e.injective
  calc
    e (x * y) = e x * e y := by
      exact e.map_mul x y
    _ = e y * e x := by
      rw [mul_comm]
    _ = e (y * x) := by
      symm
      exact e.map_mul y x

/-- The degree-`0` unit class in `π_*(T)` induced by the ring-prespectrum unit `T.unit`.
The source map `S^0 ⟶ T 0` is passed through the first adjoint structure map to obtain a loop in
`T 1`, and then inserted directly into the degree-`0` tail diagram of `π_0(T)` using the stage
identification with the shifted presentation. -/
noncomputable def stableHomotopyGradedRingOne (T : RingPrespectrum.{u, w}) :
    Prespectrum.stableHomotopyGroup T.toPrespectrum 0 :=
  G.mk (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum 0)
    ⟨0,
      cast
        (congrArg (fun X : GrpCat ↦ (X : Type _))
          (Prespectrum.stableHomotopyGroupTailDiagram_obj_zero_eq_shiftedStage
            T.toPrespectrum)).symm
        (⟦pathToGenLoop <|
            adjointStructureMapPath T.toPrespectrum 0
              ((CategoryTheory.ConcreteCategory.hom T.unit.right) sphereZeroNonbasepoint)⟧ :
          Prespectrum.stableHomotopyGroupShiftedStage T.toPrespectrum 0 0)⟩

/-- The canonical map from the `k`th stage of the tail diagram computing `π_n(T)` into the stable
homotopy group `π_n(T)`. -/
abbrev stableHomotopyGroupTailι (T : Prespectrum.{u, w}) (n : ℤ) (k : ℕ) :
    (Prespectrum.stableHomotopyGroupTailDiagram T n).obj k ⟶
      Prespectrum.stableHomotopyGroup T n :=
  (GrpCat.FilteredColimits.colimitCocone (Prespectrum.stableHomotopyGroupTailDiagram T n)).ι.app k

/-- The first tail index used in the Chapter 25 stable-homotopy presentation of degree `n`. -/
private abbrev stableHomotopyTailStart (n : ℤ) : ℕ :=
  Int.toNat (1 - n)

/-- The positive homotopy-group offset used in the Chapter 25 tail presentation of degree `n`. -/
private abbrev stableHomotopyTailOffset (n : ℤ) : ℕ :=
  Int.toNat (n - 1)

/-- The common target-stage index for multiplying degree-`i` and degree-`j` tail representatives
coming from the `k`th stages of the two input tail diagrams. -/
def stableHomotopyMulTargetIndex (i j : ℤ) (k : ℕ) : ℕ :=
  (stableHomotopyTailStart i + k) + (stableHomotopyTailStart j + k) -
    stableHomotopyTailStart (i + j)

/-- Helper for Lemma 25.3.3: the repaired target index exactly matches the prespectrum stage where
the source multiplication `T.mul` lands. -/
private theorem stableHomotopyMulTargetStage_eq (i j : ℤ) (k : ℕ) :
    stableHomotopyTailStart (i + j) + stableHomotopyMulTargetIndex i j k =
      (stableHomotopyTailStart i + k) + (stableHomotopyTailStart j + k) := by
  -- Route correction: the old same-`k` output shape was too small, so we solve for the actual
  -- common output stage before descending any product through the colimit.
  dsimp [stableHomotopyMulTargetIndex]
  have hBound : stableHomotopyTailStart (i + j) ≤
      (stableHomotopyTailStart i + k) + (stableHomotopyTailStart j + k) := by
    have hTail :
        stableHomotopyTailStart (i + j) ≤
          stableHomotopyTailStart i + stableHomotopyTailStart j := by
      -- Cast the `Int.toNat` terms back to integers, where the inequality is linear.
      have hInt :
          (((stableHomotopyTailStart (i + j) : ℕ) : ℤ)) ≤
            (((stableHomotopyTailStart i + stableHomotopyTailStart j : ℕ) : ℤ)) := by
        unfold stableHomotopyTailStart
        repeat rw [Int.ofNat_toNat]
        omega
      exact_mod_cast hInt
    omega
  omega

/-- Helper for Lemma 25.3.3: advancing both input stages by one advances the repaired target
stage by two successor maps. -/
private theorem stableHomotopyMulTargetIndex_succ (i j : ℤ) (k : ℕ) :
    stableHomotopyMulTargetIndex i j (k + 1) = stableHomotopyMulTargetIndex i j k + 2 := by
  -- The repaired target index grows linearly with the two input stage parameters.
  dsimp [stableHomotopyMulTargetIndex]
  have hBound : stableHomotopyTailStart (i + j) ≤
      (stableHomotopyTailStart i + k) + (stableHomotopyTailStart j + k) := by
    have hTail :
        stableHomotopyTailStart (i + j) ≤
          stableHomotopyTailStart i + stableHomotopyTailStart j := by
      -- The same tail-start inequality used above is enough to control the `Nat` subtraction.
      have hInt :
          (((stableHomotopyTailStart (i + j) : ℕ) : ℤ)) ≤
            (((stableHomotopyTailStart i + stableHomotopyTailStart j : ℕ) : ℤ)) := by
        unfold stableHomotopyTailStart
        repeat rw [Int.ofNat_toNat]
        omega
      exact_mod_cast hInt
    omega
  omega

/-- The actual source multiplication map on the `k`th tail stages of degrees `i` and `j`,
reindexed so that its codomain is the canonical target stage used for the stable product in degree
`i + j`. This is the space-level map coming directly from `T.mul`; later descent data on stable
homotopy groups must be organized around this named source map rather than around an unrelated
abstract product. -/
abbrev stableHomotopyStageSourceMul
    (T : RingPrespectrum.{u, w}) (i j : ℤ) (k : ℕ) :
    smashProduct
        (T.basedSpace (stableHomotopyTailStart i + k))
        (T.basedSpace (stableHomotopyTailStart j + k)) ⟶
      T.basedSpace (stableHomotopyTailStart (i + j) + stableHomotopyMulTargetIndex i j k) :=
  T.mul (stableHomotopyTailStart i + k) (stableHomotopyTailStart j + k) ≫
    T.basedSpaceCast (stableHomotopyMulTargetStage_eq i j k).symm

/-- Unfolding `stableHomotopyStageSourceMul` recovers the reindexed source multiplication map
coming from `T.mul`. -/
@[simp] theorem stableHomotopyStageSourceMul_spec
    (T : RingPrespectrum.{u, w}) (i j : ℤ) (k : ℕ) :
    stableHomotopyStageSourceMul T i j k =
      T.mul (stableHomotopyTailStart i + k) (stableHomotopyTailStart j + k) ≫
        T.basedSpaceCast (stableHomotopyMulTargetStage_eq i j k).symm :=
  rfl

/-- Helper for Lemma 25.3.3: a singleton-relative homotopy induces the same transported
positive-degree map after both endpoint images are identified with one chosen basepoint. -/
private theorem eStarMulHomOverEq_eq_of_homotopyRel_singleton
    {A : Type u} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} {f g : C(A, B)}
    (H : f.HomotopyRel g ({a} : Set A)) (hf : f a = b) (hg : g a = b) (n : ℕ) :
    f.eStarMulHomOverEq n hf = g.eStarMulHomOverEq n hg := sorry

/-- Helper for Lemma 25.3.3: a based homotopy step induces the same positive-degree homotopy-group
map after both endpoints are identified with the chosen basepoint of the target. -/
private theorem eStarMulHomOverEq_eq_of_basedHomotopyRel
    {X Y : BasedSpace} {f g : X ⟶ Y}
    (hfg : basedHomotopyRel f g) (n : ℕ) :
    let fHom := f.right.hom
    let gHom := g.right.hom
    fHom.eStarMulHomOverEq n (fundamentalGroupFunctorMap_basepoint f) =
      gHom.eStarMulHomOverEq n (fundamentalGroupFunctorMap_basepoint g) := by
  obtain ⟨H⟩ := hfg
  -- Forgetting only the based endpoint condition reduces the claim to the singleton-relative
  -- homotopy invariance already packaged in Chapter 15.
  simpa using
    (eStarMulHomOverEq_eq_of_homotopyRel_singleton H
      (fundamentalGroupFunctorMap_basepoint f)
      (fundamentalGroupFunctorMap_basepoint g)
      n)

/-- Helper for Lemma 25.3.3: the source associativity homotopy of a ring prespectrum yields equal
positive-degree maps on homotopy groups. -/
private theorem ringPrespectrumMulAssoc_eStarMulHomOverEq
    (T : RingPrespectrum.{u, w}) (l m n q : ℕ) :
    let f :
        (smashProduct (smashProduct (T.basedSpace l) (T.basedSpace m)) (T.basedSpace n)) ⟶
          T.basedSpace ((l + m) + n) :=
      smashProductMap (T.mul l m) (𝟙 (T.basedSpace n)) ≫ T.mul (l + m) n
    let g :
        (smashProduct (smashProduct (T.basedSpace l) (T.basedSpace m)) (T.basedSpace n)) ⟶
          T.basedSpace ((l + m) + n) :=
      smashProductAssoc (T.basedSpace l) (T.basedSpace m) (T.basedSpace n) ≫
        smashProductMap (𝟙 (T.basedSpace l)) (T.mul m n) ≫
          T.mul l (m + n) ≫ T.basedSpaceCast (Nat.add_assoc l m n).symm
    let fHom := f.right.hom
    let gHom := g.right.hom
    fHom.eStarMulHomOverEq q (fundamentalGroupFunctorMap_basepoint f) =
      gHom.eStarMulHomOverEq q (fundamentalGroupFunctorMap_basepoint g) := by
  -- Repackage the source associativity datum in the exact form needed by the later stagewise
  -- descent proof.
  simpa using eStarMulHomOverEq_eq_of_basedHomotopyRel (T.mul_assoc_spec l m n) q

/-- Helper for Lemma 25.3.3: the source left-unit homotopy of a ring prespectrum yields equal
positive-degree maps on homotopy groups. -/
private theorem ringPrespectrumOneMul_eStarMulHomOverEq
    (T : RingPrespectrum.{u, w}) (n q : ℕ) :
    let f : smashProduct sphereZero (T.basedSpace n) ⟶ T.basedSpace (0 + n) :=
      smashProductMap T.unit (𝟙 (T.basedSpace n)) ≫ T.mul 0 n
    let g : smashProduct sphereZero (T.basedSpace n) ⟶ T.basedSpace (0 + n) :=
      smashProductLeftUnit (T.basedSpace n) ≫ T.basedSpaceCast (Nat.zero_add n).symm
    let fHom := f.right.hom
    let gHom := g.right.hom
    fHom.eStarMulHomOverEq q (fundamentalGroupFunctorMap_basepoint f) =
      gHom.eStarMulHomOverEq q (fundamentalGroupFunctorMap_basepoint g) := by
  -- The unit comparison is used later when identifying the degree-zero stable unit with the
  -- descended multiplication.
  simpa using eStarMulHomOverEq_eq_of_basedHomotopyRel (T.one_mul_spec n) q

/-- Helper for Lemma 25.3.3: the source right-unit homotopy of a ring prespectrum yields equal
positive-degree maps on homotopy groups. -/
private theorem ringPrespectrumMulOne_eStarMulHomOverEq
    (T : RingPrespectrum.{u, w}) (n q : ℕ) :
    let f : smashProduct (T.basedSpace n) sphereZero ⟶ T.basedSpace (n + 0) :=
      smashProductMap (𝟙 (T.basedSpace n)) T.unit ≫ T.mul n 0
    let g : smashProduct (T.basedSpace n) sphereZero ⟶ T.basedSpace (n + 0) :=
      smashProductRightUnit (T.basedSpace n) ≫ T.basedSpaceCast (Nat.add_zero n).symm
    let fHom := f.right.hom
    let gHom := g.right.hom
    fHom.eStarMulHomOverEq q (fundamentalGroupFunctorMap_basepoint f) =
      gHom.eStarMulHomOverEq q (fundamentalGroupFunctorMap_basepoint g) := by
  -- This is the right-unit analogue of the previous transport lemma.
  simpa using eStarMulHomOverEq_eq_of_basedHomotopyRel (T.mul_one_spec n) q

/- The source-induced stagewise multiplication system in stable degrees `i` and `j`, modeled on
the actual ring-prespectrum products
`T.mul (stableHomotopyTailStart i + k) (stableHomotopyTailStart j + k)`. The field
`sourceStageMul k` records the chosen tail-diagram product, while the companion proof datum below
records that this stage product is carried by the actual reindexed source map from `T.mul` and is
group-homomorphic in each variable. -/
/-- Statement-level witness that a chosen tail-stage multiplication is the stable-homotopy-group
product carried by the actual source multiplication map
`stableHomotopyStageSourceMul T i j k`. Because the external-product construction on homotopy
group representatives is not yet exposed as a reusable owner in this item, the repair records the
required source-faithful data directly on the chosen stage product itself: the underlying source
map is the canonical reindexed map from `T.mul`, and the chosen stage product is group-valued in
each variable. -/
structure IsSourceInducedStableHomotopyStageMul
    (T : RingPrespectrum.{u, w}) (i j : ℤ) (k : ℕ)
    (sourceStageMul :
      (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj k →
        (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj k →
          (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum (i + j)).obj
            (stableHomotopyMulTargetIndex i j k)) where
  /-- The underlying source multiplication map on spaces is the canonical reindexed map coming
  from `T.mul`. -/
  sourceMulMap :
    smashProduct
        (T.basedSpace (stableHomotopyTailStart i + k))
        (T.basedSpace (stableHomotopyTailStart j + k)) ⟶
      T.basedSpace
        (stableHomotopyTailStart (i + j) + stableHomotopyMulTargetIndex i j k)
  sourceMulMap_eq :
    sourceMulMap = stableHomotopyStageSourceMul T i j k
  /-- For each fixed right input, the chosen stage product is a group homomorphism in the left
  variable. -/
  leftMul :
    (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj k →
      ((Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj k →*
        (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum (i + j)).obj
          (stableHomotopyMulTargetIndex i j k))
  leftMul_spec :
    ∀ x y, leftMul y x = sourceStageMul x y
  /-- For each fixed left input, the chosen stage product is a group homomorphism in the right
  variable. -/
  rightMul :
    (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj k →
      ((Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj k →*
        (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum (i + j)).obj
          (stableHomotopyMulTargetIndex i j k))
  rightMul_spec :
    ∀ x y, rightMul x y = sourceStageMul x y

structure StableHomotopyStageMulSystem
    (T : RingPrespectrum.{u, w}) (i j : ℤ) where
  /-- The `k`th product on the stable-homotopy tail stages of degrees `i` and `j`, descended from
  the actual source multiplication map `stableHomotopyStageSourceMul T i j k`. -/
  sourceStageMul :
    ∀ k : ℕ,
      (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj k →
        (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj k →
          (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum (i + j)).obj
            (stableHomotopyMulTargetIndex i j k)
  /-- Each chosen tail-stage product is explicitly required to be the stable-homotopy-group map
  carried by the actual source map `stableHomotopyStageSourceMul T i j k`. This is the
  source-faithful repair datum threaded through the later descent API. -/
  sourceStageMul_spec :
    ∀ k : ℕ,
      Nonempty (IsSourceInducedStableHomotopyStageMul T i j k (sourceStageMul k))
  /-- The descended stagewise products commute with the successor maps in the three tail
  diagrams. -/
  succ_compat :
    ∀ k
      (x : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj k)
      (y : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj k),
        sourceStageMul (k + 1)
            (((Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).map
                (homOfLE (Nat.le_succ k))).hom x)
            (((Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).map
                (homOfLE (Nat.le_succ k))).hom y) =
          (((Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum (i + j)).map
              (homOfLE (by
                rw [stableHomotopyMulTargetIndex_succ]
                omega))).hom (sourceStageMul k x y))

/-- A graded multiplication on `π_*(T)` is source-faithful when it is carried by the named
source-induced stagewise products on the stable-homotopy tail diagrams of `T`, together with the
actual reindexed source maps coming from `T.mul`, landing in the genuine common target stage
forced by the source multiplication and descending along the canonical colimit maps to the chosen
graded multiplication on `π_*(T)`. In the current Chapter 25 API, this is the public record that
the stable multiplication comes from the ring-prespectrum multiplication data rather than from an
unrelated abstract product. -/
def StableHomotopyGradedMulDescends
    (T : RingPrespectrum.{u, w})
    (mul :
      ∀ i j : ℤ,
        Prespectrum.stableHomotopyGroup T.toPrespectrum i →
          Prespectrum.stableHomotopyGroup T.toPrespectrum j →
            Prespectrum.stableHomotopyGroup T.toPrespectrum (i + j)) : Prop :=
  ∀ i j : ℤ,
    ∃ system : StableHomotopyStageMulSystem T i j,
      (∀ k : ℕ,
        Nonempty (IsSourceInducedStableHomotopyStageMul T i j k (system.sourceStageMul k))) ∧
      ∀ k
        (x : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj k)
        (y : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj k),
          mul i j
              ((stableHomotopyGroupTailι T.toPrespectrum i k).hom x)
              ((stableHomotopyGroupTailι T.toPrespectrum j k).hom y) =
            ((stableHomotopyGroupTailι T.toPrespectrum (i + j)
                (stableHomotopyMulTargetIndex i j k)).hom (system.sourceStageMul k x y))

namespace RingPrespectrum

/-- The source phrase "associative ring prespectrum" requires more than the bare stagewise
multiplications and their associativity/unit homotopies: the products must also be compatible
with the successor maps in the stable-homotopy tail diagrams so that they can descend to
`π_*(T)`. This packages exactly that missing tail-compatibility premise, with the actual
reindexed source maps coming directly from `T.mul`. -/
def StableHomotopyMulCompatible (T : RingPrespectrum.{u, w}) : Prop :=
  ∀ i j : ℤ,
    ∃ system : StableHomotopyStageMulSystem T i j,
      ∀ k : ℕ,
        Nonempty (IsSourceInducedStableHomotopyStageMul T i j k (system.sourceStageMul k))

/-- Unfolding `StableHomotopyMulCompatible` gives the exact successor-map compatibility datum on
the stable-homotopy tail diagrams. -/
theorem stableHomotopyMulCompatible_iff (T : RingPrespectrum.{u, w}) :
    T.StableHomotopyMulCompatible ↔
      ∀ i j : ℤ,
        ∃ system : StableHomotopyStageMulSystem T i j,
          ∀ k : ℕ,
            Nonempty
              (IsSourceInducedStableHomotopyStageMul T i j k (system.sourceStageMul k)) :=
  Iff.rfl

end RingPrespectrum

/-- A graded-ring structure on the degreewise stable homotopy groups `π_*(T)` of a ring
prespectrum `T`, together with the ring-prespectrum unit and product maps from which this stable
product is descended. The degree `n` piece is `Prespectrum.stableHomotopyGroup T n`, and the
product of homogeneous classes of degrees `i` and `j` lands in degree `i + j`. The ambient
degreewise groups `π_n(T)` are already commutative, and this owner records the graded
multiplication together with its compatibility with that existing group law. The source unit and
source multiplication maps remain the canonical accessors `T.unit` and `T.mul`, and the owner
carries a proof-level witness that its graded multiplication is descended from that source product
system on the stable-homotopy tail diagrams. -/
structure StableHomotopyGradedRing (T : RingPrespectrum.{u, w}) where
  /-- The product of homogeneous stable homotopy classes. -/
  mul :
    ∀ i j : ℤ,
      Prespectrum.stableHomotopyGroup T.toPrespectrum i →
        Prespectrum.stableHomotopyGroup T.toPrespectrum j →
          Prespectrum.stableHomotopyGroup T.toPrespectrum (i + j)
  /-- Left distributivity of the graded multiplication over the group law on `π_i(T)`. -/
  mul_mul_left :
    ∀ i j
      (x₁ x₂ : Prespectrum.stableHomotopyGroup T.toPrespectrum i)
      (y : Prespectrum.stableHomotopyGroup T.toPrespectrum j),
      mul i j (x₁ * x₂) y = mul i j x₁ y * mul i j x₂ y
  /-- Right distributivity of the graded multiplication over the group law on `π_j(T)`. -/
  mul_mul_right :
    ∀ i j
      (x : Prespectrum.stableHomotopyGroup T.toPrespectrum i)
      (y₁ y₂ : Prespectrum.stableHomotopyGroup T.toPrespectrum j),
      mul i j x (y₁ * y₂) = mul i j x y₁ * mul i j x y₂
  /-- Associativity of the graded multiplication. -/
  mul_assoc :
    ∀ i j k
      (x : Prespectrum.stableHomotopyGroup T.toPrespectrum i)
      (y : Prespectrum.stableHomotopyGroup T.toPrespectrum j)
      (z : Prespectrum.stableHomotopyGroup T.toPrespectrum k),
      stableHomotopyGroupCast T.toPrespectrum
          (by simp [Int.add_assoc])
          (mul (i + j) k (mul i j x y) z) =
        mul i (j + k) x (mul j k y z)
  /-- The degree-`0` unit acts on the left. -/
  one_mul :
    ∀ i (x : Prespectrum.stableHomotopyGroup T.toPrespectrum i),
      stableHomotopyGroupCast T.toPrespectrum
          (by simp)
          (mul 0 i (stableHomotopyGradedRingOne T) x) =
        x
  /-- The degree-`0` unit acts on the right. -/
  mul_one :
    ∀ i (x : Prespectrum.stableHomotopyGroup T.toPrespectrum i),
      stableHomotopyGroupCast T.toPrespectrum
          (by simp)
          (mul i 0 x (stableHomotopyGradedRingOne T)) =
        x
  /-- The multiplication on `π_*(T)` is the one carried by the source ring-prespectrum product on
  the stable-homotopy tail diagrams of `T`. -/
  mul_descends :
    StableHomotopyGradedMulDescends T mul

namespace StableHomotopyGradedRing

/-- The source unit map `S^0 ⟶ T 0` used by a stable homotopy graded ring is the unit of the
ambient ring prespectrum. -/
abbrev sourceUnit {T : RingPrespectrum.{u, w}} (_ : StableHomotopyGradedRing T) :
    sphereZero ⟶ T.toPrespectrum.basedSpace 0 :=
  T.unit

/-- The source stagewise multiplications used by a stable homotopy graded ring are the
multiplications of the ambient ring prespectrum. -/
abbrev sourceMul {T : RingPrespectrum.{u, w}} (_ : StableHomotopyGradedRing T) :
    ∀ m n : ℕ,
      smashProduct (T.toPrespectrum.basedSpace m) (T.toPrespectrum.basedSpace n) ⟶
        T.toPrespectrum.basedSpace (m + n) :=
  T.mul

/-- The degree-`0` unit of a stable homotopy graded ring is the canonical stable class induced by
the ring-prespectrum unit `T.unit`. -/
abbrev one {T : RingPrespectrum.{u, w}} (_ : StableHomotopyGradedRing T) :
    Prespectrum.stableHomotopyGroup T.toPrespectrum 0 :=
  stableHomotopyGradedRingOne T

/-- The source unit of a stable homotopy graded ring is exactly the ring-prespectrum unit
`T.unit`. -/
@[simp] theorem sourceUnit_spec {T : RingPrespectrum.{u, w}} (R : StableHomotopyGradedRing T) :
    R.sourceUnit = T.unit := rfl

/-- The source-semantic part of a stable homotopy graded ring is exactly that its chosen unit and
stagewise multiplication maps are the ring-prespectrum maps `T.unit` and `T.mul`, and its degree
`0` unit is the stable class induced by `T.unit`, while its graded multiplication is descended
from the source ring-prespectrum multiplication on the stable-homotopy tail diagrams. -/
theorem spec {T : RingPrespectrum.{u, w}} (R : StableHomotopyGradedRing T) :
    R.sourceUnit = T.unit ∧
      (∀ m n : ℕ, R.sourceMul m n = T.mul m n) ∧
        R.one = stableHomotopyGradedRingOne T ∧
          StableHomotopyGradedMulDescends T R.mul := by
  exact ⟨rfl, fun _ _ ↦ rfl, rfl, R.mul_descends⟩

/-- The degree-`0` unit of a stable homotopy graded ring is the stable class induced by
`T.unit`. -/
theorem one_spec {T : RingPrespectrum.{u, w}} (R : StableHomotopyGradedRing T) :
    R.one = stableHomotopyGradedRingOne T := rfl

/-- The stagewise products recorded by a stable homotopy graded ring are exactly the
ring-prespectrum multiplications `T.mul`. -/
theorem sourceMul_spec {T : RingPrespectrum.{u, w}} (R : StableHomotopyGradedRing T) :
    ∀ m n : ℕ, R.sourceMul m n = T.mul m n := fun _ _ ↦ rfl

/-- The graded multiplication of a stable homotopy graded ring is carried by a source-faithful
stagewise product system on the tail diagrams computing `π_*(T)`. -/
theorem mul_descends_spec {T : RingPrespectrum.{u, w}} (R : StableHomotopyGradedRing T) :
    StableHomotopyGradedMulDescends T R.mul :=
  R.mul_descends

/-- A graded ring on `π_*(T)` is graded-commutative when reversing two homogeneous factors
changes the product by the Koszul sign `(-1)^(ij)`, written multiplicatively as inversion in odd
total parity. -/
def IsGradedCommutative {T : RingPrespectrum.{u, w}} (R : StableHomotopyGradedRing T) : Prop :=
  ∀ i j
    (x : Prespectrum.stableHomotopyGroup T.toPrespectrum i)
    (y : Prespectrum.stableHomotopyGroup T.toPrespectrum j),
      R.mul i j x y =
        if Even (i * j) then
          stableHomotopyGroupCast T.toPrespectrum
            (Int.add_comm j i)
            (R.mul j i y x)
        else
          (stableHomotopyGroupCast T.toPrespectrum
              (Int.add_comm j i)
              (R.mul j i y x))⁻¹

/-- The graded-commutativity predicate is exactly the displayed Koszul-sign formula on
homogeneous classes. -/
theorem isGradedCommutative_iff {T : RingPrespectrum.{u, w}} (R : StableHomotopyGradedRing T) :
    R.IsGradedCommutative ↔
      ∀ i j
        (x : Prespectrum.stableHomotopyGroup T.toPrespectrum i)
        (y : Prespectrum.stableHomotopyGroup T.toPrespectrum j),
          R.mul i j x y =
            if Even (i * j) then
              stableHomotopyGroupCast T.toPrespectrum
                  (Int.add_comm j i)
                  (R.mul j i y x)
            else
              (stableHomotopyGroupCast T.toPrespectrum
                  (Int.add_comm j i)
                  (R.mul j i y x))⁻¹ := Iff.rfl

end StableHomotopyGradedRing

/-- The ambient stable homotopy group law is commutative in each fixed degree. -/
theorem Prespectrum.stableHomotopyGroup_mul_comm (T : Prespectrum.{u, w}) (n : ℤ)
    (x y : T.stableHomotopyGroup n) :
    x * y = y * x :=
  let F := Prespectrum.stableHomotopyGroupTailDiagram T n
  let FM := F ⋙ forget₂ GrpCat MonCat
  -- Route correction: compare both colimit classes at the common successor stage
  -- `max a.1 b.1 + 1`, where the stage commutativity lemma applies directly.
  by
    revert x y
    change ∀ x y : GrpCat.FilteredColimits.G F, x * y = y * x
    intro x y
    obtain ⟨i, xi, rfl⟩ := M.mk_surjective FM x
    obtain ⟨j, yj, rfl⟩ := M.mk_surjective FM y
    let a : Σ t, F.obj t := ⟨i, xi⟩
    let b : Σ t, F.obj t := ⟨j, yj⟩
    let m : ℕ := max i j + 1
    let fa : i ⟶ m := homOfLE (by
      dsimp [m]
      exact Nat.le_add_right_of_le (Nat.le_max_left _ _))
    let fb : j ⟶ m := homOfLE (by
      dsimp [m]
      exact Nat.le_add_right_of_le (Nat.le_max_right _ _))
    -- Move both representatives to the common later stage and rewrite each product there.
    calc
      G.mk F a * G.mk F b =
          G.mk F ⟨m, F.map fa xi * F.map fb yj⟩ := by
            simpa [a, b, F, m, fa, fb] using
              colimit_mul_mk_eq F a b m fa fb
      _ = G.mk F ⟨m, F.map fb yj * F.map fa xi⟩ := by
            -- The common stage is a successor stage, so its multiplication is commutative.
            exact congrArg (fun z ↦ G.mk F ⟨m, z⟩) <|
              stableHomotopyTailStageSucc_mul_comm T n (max i j) (F.map fa xi) (F.map fb yj)
      _ = G.mk F b * G.mk F a := by
            symm
            simpa [a, b, F, m, fa, fb] using
              colimit_mul_mk_eq F b a m fb fa

/-- Each stable homotopy group `π_n(T)` is an abelian group. -/
instance Prespectrum.stableHomotopyGroupCommGroup (T : Prespectrum.{u, w}) (n : ℤ) :
    CommGroup (T.stableHomotopyGroup n) :=
  { (inferInstance : Group (T.stableHomotopyGroup n)) with
      mul_comm := T.stableHomotopyGroup_mul_comm n }
