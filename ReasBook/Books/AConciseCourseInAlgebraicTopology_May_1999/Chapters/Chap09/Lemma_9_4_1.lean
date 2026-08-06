import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Subpath
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Proposition_1_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped unitInterval Topology Topology.Homotopy

variable {X : Type u} [TopologicalSpace X] [ContractibleSpace X]

-- Semantic recall: `ContractibleSpace.hequiv_unit`, `HomotopyGroup`, and `HomotopyGroup.Pi`
-- are the relevant mathlib APIs here.

/-- Helper for Lemma 9.4.1: contractibility makes `π_ 0 X x` trivial because `X` is path
connected, so `ZerothHomotopy X` is subsingleton. -/
private theorem pi0SubsingletonOfContractible (x : X) :
    Subsingleton (π_ 0 X x) := by
  -- First collapse the path-component quotient using path connectedness of a contractible space.
  let _ : Subsingleton (ZerothHomotopy X) := by
    refine ⟨fun a b ↦ ?_⟩
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    exact Quotient.sound (PathConnectedSpace.joined x y)
  -- Then pull subsingletonity back across the canonical `π₀`/`ZerothHomotopy` equivalence.
  refine ⟨fun a b ↦ ?_⟩
  apply (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X).injective
  exact Subsingleton.elim _ _

/-- Helper for Lemma 9.4.1: contractibility makes `π_ 1 X x` trivial because contractible spaces
are simply connected, hence their fundamental groups are subsingleton. -/
private theorem pi1SubsingletonOfContractible (x : X) :
    Subsingleton (π_ 1 X x) := by
  -- Convert the `π₁` statement to the fundamental group, where simple connectedness applies.
  let _ : Subsingleton (FundamentalGroup X x) := by
    change Subsingleton (Path.Homotopic.Quotient x x)
    infer_instance
  refine ⟨fun a b ↦ ?_⟩
  apply (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x).injective
  exact Subsingleton.elim _ _

/-- Helper for Lemma 9.4.1: postcomposition with a continuous map preserves the boundary condition
for generalized loops. -/
private theorem genLoopMap_boundary {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {n : ℕ} {y : Y} (γ : Ω^ (Fin n) Y y) :
    ∀ t ∈ Cube.boundary (Fin n), f.comp γ.1 t = f y := by
  -- Evaluate the boundary condition for `γ` and postcompose by `f`.
  intro t ht
  simpa using congrArg f (γ.2 t ht)

/-- Helper for Lemma 9.4.1: postcomposition sends generalized loops to generalized loops. -/
private def genLoopMap {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {n : ℕ} {y : Y} :
    Ω^ (Fin n) Y y → Ω^ (Fin n) Z (f y) :=
  fun γ ↦ ⟨f.comp γ.1, genLoopMap_boundary f γ⟩

/-- Helper for Lemma 9.4.1: postcomposition with a continuous map preserves the boundary condition
for generalized loops indexed by an arbitrary finite cube. -/
private theorem genLoopMapContinuous_boundary {N : Type*} {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {y : Y} (γ : Ω^ N Y y) :
    ∀ t ∈ Cube.boundary N, f.comp γ.1 t = f y := by
  -- The boundary values of `γ` are already pinned to `y`, so postcomposition preserves them.
  intro t ht
  simpa using congrArg f (γ.2 t ht)

/-- Helper for Lemma 9.4.1: the underlying postcomposition map on generalized-loop spaces is
continuous. -/
private theorem continuous_genLoopMapContinuous {N : Type*} {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {y : Y} :
    Continuous fun γ : Ω^ N Y y ↦ (f.comp γ.1 : C(I^N, Z)) := by
  -- This is the standard continuity of postcomposition in the compact-open function space.
  exact (ContinuousMap.continuous_postcomp f).comp continuous_subtype_val

/-- Helper for Lemma 9.4.1: postcomposition defines a bundled continuous map on generalized-loop
spaces for arbitrary index types. -/
private def genLoopMapContinuous {N : Type*} {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {y : Y} :
    C(Ω^ N Y y, Ω^ N Z (f y)) :=
  ⟨fun γ ↦ ⟨f.comp γ.1, genLoopMapContinuous_boundary f γ⟩,
    Continuous.subtype_mk (continuous_genLoopMapContinuous f)
      (fun γ ↦ genLoopMapContinuous_boundary f γ)⟩

/-- Helper for Lemma 9.4.1: postcomposition respects homotopy relative to the boundary. -/
private theorem genLoopMap_respects {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {n : ℕ} {y : Y} {γ δ : Ω^ (Fin n) Y y} (h : GenLoop.Homotopic γ δ) :
    GenLoop.Homotopic (genLoopMap f γ) (genLoopMap f δ) := by
  -- Relative homotopies remain relative after postcomposition.
  change (genLoopMap f γ).1.HomotopicRel (genLoopMap f δ).1 (Cube.boundary (Fin n))
  simpa [genLoopMap, GenLoop.Homotopic] using
    ContinuousMap.HomotopicRel.comp_continuousMap h f

/-- Helper for Lemma 9.4.1: a continuous map induces a map on homotopy groups by
postcomposition on representatives. -/
private def homotopyGroupMap {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) (y : Y) :
    π_ n Y y → π_ n Z (f y) :=
  Quotient.map (genLoopMap f) fun _ _ h ↦ genLoopMap_respects f h

/-- Helper for Lemma 9.4.1: postcomposition by a composite agrees with successive
postcomposition on generalized loops. -/
private theorem genLoopMap_comp {Y : Type u} {Z : Type v} {W : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    (f : C(Y, Z)) (g : C(Z, W)) {n : ℕ} {y : Y} (γ : Ω^ (Fin n) Y y) :
    genLoopMap g (genLoopMap f γ) = genLoopMap (g.comp f) γ := by
  -- Both representatives are the same pointwise composite.
  ext t
  rfl

/-- Helper for Lemma 9.4.1: the induced map on homotopy groups sends the identity map to the
identity function. -/
private theorem homotopyGroupMap_id {Y : Type u} [TopologicalSpace Y] (n : ℕ) (y : Y) :
    homotopyGroupMap (ContinuousMap.id Y) n y = id := by
  -- Check the quotient map on representatives, where postcomposition by the identity is
  -- definitionally trivial.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Lemma 9.4.1: the induced map on homotopy groups respects composition. -/
private theorem homotopyGroupMap_comp {Y : Type u} {Z : Type v} {W : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    (f : C(Y, Z)) (g : C(Z, W)) (n : ℕ) (y : Y) :
    homotopyGroupMap (g.comp f) n y =
      (homotopyGroupMap g n (f y)) ∘ homotopyGroupMap f n y := by
  -- Reduce to representatives, where the composite is literally `g ∘ f`.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Lemma 9.4.1: every generalized loop into `Unit` is the constant one. -/
private theorem genLoop_eq_const_unit (n : ℕ) (u : Unit) (γ : Ω^ (Fin n) Unit u) :
    γ = GenLoop.const := by
  -- `Unit` is subsingleton, so the entire generalized-loop space is subsingleton as well.
  exact Subsingleton.elim _ _

/-- Helper for Lemma 9.4.1: all homotopy groups of `Unit` are subsingleton. -/
private theorem unitHomotopyGroupSubsingleton (n : ℕ) (u : Unit) :
    Subsingleton (π_ n Unit u) := by
  -- Quotient by homotopy preserves the one-point behavior of the representative space.
  refine ⟨fun a b ↦ Quotient.inductionOn₂ a b ?_⟩
  intro γ δ
  apply Quotient.sound
  simpa [genLoop_eq_const_unit n u γ, genLoop_eq_const_unit n u δ] using
    (GenLoop.Homotopic.refl (GenLoop.const : Ω^ (Fin n) Unit u))

/-- Helper for Lemma 9.4.1: a continuous map with a left homotopy inverse induces an injective
map on fundamental groups after transporting back along the endpoint track of the left homotopy.
-/
private theorem fundamentalGroupMap_injective_of_leftHomotopy
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(Z, Y)) (H : (g.comp f).Homotopy (ContinuousMap.id Y)) (y : Y) :
    Function.Injective (FundamentalGroup.map f y) := by
  -- Transport the composite `(g ∘ f)_*` back to the original basepoint via the endpoint track of
  -- the left homotopy, then use the homotopy-commutative square on `π₁`.
  let p : Path (g (f y)) y := H.evalAt y
  let transportBack : FundamentalGroup Z (f y) →* FundamentalGroup Y y :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom.comp
      (FundamentalGroup.map g (f y))
  have hbase :
      transportBack.comp (FundamentalGroup.map f y) =
        FundamentalGroup.map (ContinuousMap.id Y) y := by
    calc
      transportBack.comp (FundamentalGroup.map f y)
          =
            (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom.comp
              ((FundamentalGroup.map g (f y)).comp (FundamentalGroup.map f y)) := by
            rfl
      _ =
            (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom.comp
              (FundamentalGroup.map (g.comp f) y) := by
            rw [fundamental_group_map_comp f g y]
      _ = FundamentalGroup.map (ContinuousMap.id Y) y := by
            simpa [p] using
              fundamental_group_map_homotopy_commutes
                (g.comp f) (ContinuousMap.id Y) H y
  have hsection :
      transportBack.comp (FundamentalGroup.map f y) = MonoidHom.id _ := by
    exact hbase.trans (by simpa using fundamental_group_map_id y)
  intro a b hab
  -- Apply the transport-back section to move the equality back to the source group.
  calc
    a = (MonoidHom.id _) a := by
      rfl
    _ = (transportBack.comp (FundamentalGroup.map f y)) a := by
      rw [hsection]
    _ = transportBack (FundamentalGroup.map f y a) := rfl
    _ = transportBack (FundamentalGroup.map f y b) := by
      simpa [transportBack] using congrArg transportBack hab
    _ = (transportBack.comp (FundamentalGroup.map f y)) b := rfl
    _ = (MonoidHom.id _) b := by
      rw [hsection]
    _ = b := by
      rfl

/-- Helper for Lemma 9.4.1: a homotopy equivalence induces an injective map on fundamental groups
by specializing the left-homotopy criterion to its chosen left inverse. -/
private theorem fundamentalGroupMap_injective_of_homotopyEquiv
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv Y Z) (y : Y) :
    Function.Injective (FundamentalGroup.map e.toFun y) := by
  -- Reuse the left-homotopy injectivity theorem with the chosen left inverse of `e`.
  classical
  exact
    fundamentalGroupMap_injective_of_leftHomotopy
      e.toFun e.invFun (Classical.choice e.left_inv) y

/-- Helper for Lemma 9.4.1: a continuous map induces the evident map on ordinary loop spaces. -/
private def loopSpaceMapContinuous
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y : Y) :
    C(Ω Y y, Ω Z (f y)) :=
  ⟨fun γ ↦ γ.map f.continuous, by
    rw [continuous_induced_rng]
    change Continuous fun γ : Ω Y y ↦ (f.comp γ.toContinuousMap : C(I, Z))
    exact (ContinuousMap.continuous_postcomp f).comp continuous_induced_dom⟩

/-- Helper for Lemma 9.4.1: conjugating a loop by a path changes the loop-space basepoint. -/
private noncomputable def loopSpaceBaseChangeMap
    {Y : Type u} [TopologicalSpace Y] {y₀ y₁ : Y} (p : Path y₀ y₁) :
    C(Ω Y y₀, Ω Y y₁) :=
  ⟨fun γ ↦ p.symm.trans (γ.trans p), by
    -- Continuity comes from the continuity of path concatenation in each variable.
    have hRight : Continuous fun γ : Ω Y y₀ ↦ γ.trans p :=
      by
        simpa using
          (Continuous.path_trans
            (f := fun γ : Path y₀ y₀ ↦ γ)
            (g := fun _ : Path y₀ y₀ ↦ p) continuous_id continuous_const)
    simpa using
      (Continuous.path_trans
        (f := fun _ : Path y₀ y₀ ↦ p.symm)
        (g := fun γ : Path y₀ y₀ ↦ γ.trans p) continuous_const hRight)⟩

/-- Helper for Lemma 9.4.1: the one-cube generalized-loop model is homeomorphic to the ordinary
loop space. -/
private def oneGenLoopHomeomorph
    {Y : Type u} [TopologicalSpace Y] (y : Y) :
    Ω^ (Fin 1) Y y ≃ₜ Ω Y y where
  toFun p :=
    Path.mk ⟨fun t ↦ p (fun _ ↦ t), by fun_prop⟩
      (p.2 (fun _ ↦ 0) ⟨0, Or.inl rfl⟩)
      (p.2 (fun _ ↦ 1) ⟨0, Or.inr rfl⟩)
  invFun γ :=
    ⟨⟨fun t ↦ γ (t 0), by fun_prop⟩, fun t ht ↦ by
      rcases ht with ⟨i, hi | hi⟩
      · have hi0 : t 0 = 0 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = y
        calc
          γ (t 0) = γ 0 := by simpa using congrArg γ hi0
          _ = y := γ.source
      · have hi1 : t 0 = 1 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = y
        calc
          γ (t 0) = γ 1 := by simpa using congrArg γ hi1
          _ = y := γ.target⟩
  left_inv p := by
    -- Collapse `Fin 1`-indexed cubes to the unique coordinate.
    ext t
    have ht : t = fun _ : Fin 1 ↦ t 0 := by
      funext i
      fin_cases i
      rfl
    rw [ht]
    rfl
  right_inv γ := by
    -- The inverse just evaluates the one available coordinate.
    ext t
    rfl
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t _ ↦ t, by fun_prop⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t : I^(Fin 1) ↦ t 0, by fun_prop⟩).comp continuous_induced_dom

/-- Helper for Lemma 9.4.1: the inverse of `oneGenLoopHomeomorph` sends the constant loop to the
constant generalized loop. -/
@[simp] private theorem oneGenLoopHomeomorph_symm_refl
    {Y : Type u} [TopologicalSpace Y] (y : Y) :
    (oneGenLoopHomeomorph y).symm (Path.refl y) = GenLoop.const := by
  -- Both representatives are pointwise constant at the basepoint.
  ext t
  rfl

/-- Helper for Lemma 9.4.1: a homeomorphism transports generalized loops and preserves the chosen
basepoint. -/
private def genLoopHomeomorph
    {M : Type v} {Y : Type u} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z) :
    Ω^ M Y y ≃ₜ Ω^ M Z z where
  toFun p :=
    ⟨⟨fun t ↦ h (p t), h.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      simpa [hy] using congrArg h (p.2 t ht)⟩
  invFun p :=
    ⟨⟨fun t ↦ h.symm (p t), (h.symm.continuous).comp p.1.continuous⟩, fun t ht ↦ by
      have hp : p t = z := p.2 t ht
      calc
        h.symm (p t) = h.symm z := by rw [hp]
        _ = y := (h.symm_apply_eq).2 hy.symm⟩
  left_inv p := by
    -- The homeomorphism and its inverse cancel pointwise.
    ext t
    simp
  right_inv p := by
    -- The inverse direction is pointwise cancellation as well.
    ext t
    simp
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact (ContinuousMap.continuous_postcomp ⟨h, h.continuous⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_postcomp ⟨h.symm, h.symm.continuous⟩).comp
        continuous_subtype_val

/-- Helper for Lemma 9.4.1: generalized-loop homotopies are exactly paths in the generalized-loop
space. -/
private theorem genLoopHomotopic_iff_joined
    {N : Type*} {Y : Type*} [TopologicalSpace Y] {y : Y} {p q : Ω^ N Y y} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    -- Curry the relative homotopy into a path through the generalized-loop space.
    refine ⟨Path.mk
      ⟨fun t ↦
          (⟨curriedHomotopy t, fun a ha ↦ (H.prop t a ha).trans (p.property a ha)⟩ :
            Ω^ N Y y),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t a ha
      exact (H.prop t a ha).trans (p.property a ha)
    · ext a
      exact H.apply_zero a
    · ext a
      exact H.apply_one a
  · rintro ⟨γ⟩
    -- Uncurry a path of generalized loops into a homotopy relative to the boundary.
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro a
      change γ 0 a = p a
      exact congrArg (fun r : Ω^ N Y y ↦ r a) γ.source
    · intro a
      change γ 1 a = q a
      exact congrArg (fun r : Ω^ N Y y ↦ r a) γ.target
    · intro t a ha
      exact ((γ t).property a ha).trans (p.property a ha).symm

/-- Helper for Lemma 9.4.1: a homeomorphism preserves and reflects the path relation `Joined`. -/
private theorem joined_iff_homeomorph
    {Y : Type*} {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {a b : Y} :
    Joined (h a) (h b) ↔ Joined a b := by
  constructor
  · rintro ⟨γ⟩
    -- Pull the path back along the inverse homeomorphism.
    simpa using (show Joined (h.symm (h a)) (h.symm (h b)) from ⟨γ.map h.symm.continuous⟩)
  · rintro ⟨γ⟩
    -- Push the path forward along the homeomorphism.
    exact ⟨γ.map h.continuous⟩

/-- Helper for Lemma 9.4.1: a homeomorphism between generalized-loop spaces preserves and
reflects generalized-loop homotopy. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M : Type*} {N : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}
    (h : Ω^ M Y y ≃ₜ Ω^ N Z z) {p q : Ω^ M Y y} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Translate homotopies to paths, use the homeomorphism, then translate back.
  rw [genLoopHomotopic_iff_joined, genLoopHomotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Lemma 9.4.1: the representative-level loop-space shift is built by reassociating
generalized loops and then reindexing the cube. -/
private def loopSpaceRepresentativeEquiv
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (y : Y) :
    Ω^ (Fin n) (Ω Y y) (Path.refl y) ≃ Ω^ (Fin (n + 1)) Y y :=
  let e₁ :
      Ω^ (Fin n) (Ω Y y) (Path.refl y) ≃ₜ
        Ω^ (Fin n) (Ω^ (Fin 1) Y y) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph y).symm (oneGenLoopHomeomorph_symm_refl y)
  let e₂ :
      Ω^ (Fin n) (Ω^ (Fin 1) Y y) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) Y y :=
    GenLoop.genLoopGenLoopEquiv y
  let e₃ : Ω^ (Fin n ⊕ Fin 1) Y y ≃ₜ Ω^ (Fin (n + 1)) Y y :=
    GenLoop.congr y (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  (e₁.trans e₂).trans e₃

/-- Helper for Lemma 9.4.1: the loop-space shift preserves and reflects generalized-loop
homotopy. -/
private theorem loopSpaceRepresentativeEquiv_homotopic_iff
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (y : Y)
    {p q : Ω^ (Fin n) (Ω Y y) (Path.refl y)} :
    GenLoop.Homotopic (loopSpaceRepresentativeEquiv n y p) (loopSpaceRepresentativeEquiv n y q) ↔
      GenLoop.Homotopic p q := by
  let e :
      Ω^ (Fin n) (Ω Y y) (Path.refl y) ≃ₜ Ω^ (Fin (n + 1)) Y y :=
    let e₁ :
        Ω^ (Fin n) (Ω Y y) (Path.refl y) ≃ₜ
          Ω^ (Fin n) (Ω^ (Fin 1) Y y) GenLoop.const :=
      genLoopHomeomorph (oneGenLoopHomeomorph y).symm (oneGenLoopHomeomorph_symm_refl y)
    let e₂ :
        Ω^ (Fin n) (Ω^ (Fin 1) Y y) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) Y y :=
      GenLoop.genLoopGenLoopEquiv y
    let e₃ : Ω^ (Fin n ⊕ Fin 1) Y y ≃ₜ Ω^ (Fin (n + 1)) Y y :=
      GenLoop.congr y (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
    (e₁.trans e₂).trans e₃
  -- Descend the quotient comparison through the composite homeomorphism.
  change GenLoop.Homotopic (e p) (e q) ↔ GenLoop.Homotopic p q
  exact genLoopHomotopic_iff_of_homeomorph e

/-- Helper for Lemma 9.4.1: the canonical shift identifies `π_ n(Ω Y y)` with
`π_(n + 1) Y y`. -/
private def loopSpaceHomotopyGroupEquivPiSucc
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (y : Y) :
    π_ n (Ω Y y) (Path.refl y) ≃ π_ (n + 1) Y y :=
  -- Descend the representative-level equivalence to the quotient.
  Quotient.congr (loopSpaceRepresentativeEquiv n y) fun _ _ ↦
    (loopSpaceRepresentativeEquiv_homotopic_iff n y).symm

/-- Helper for Lemma 9.4.1: the representative-level loop-space shift commutes with
postcomposition. -/
private theorem loopSpaceRepresentativeEquiv_genLoopMap_eq
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) {y : Y}
    (γ : Ω^ (Fin n) (Ω Y y) (Path.refl y)) :
    loopSpaceRepresentativeEquiv n (f y) (genLoopMap (loopSpaceMapContinuous f y) γ) =
      genLoopMap f (loopSpaceRepresentativeEquiv n y γ) := by
  -- Every component of the shift equivalence is defined pointwise, so it commutes with
  -- postcomposition by `f`.
  ext t
  rfl

/-- Helper for Lemma 9.4.1: under the loop-space shift, the induced map on higher homotopy groups
is the induced map on the loop space one degree lower. -/
private theorem homotopyGroupMap_piSucc_eq_loopSpaceMap
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) (y : Y) :
    loopSpaceHomotopyGroupEquivPiSucc n (f y) ∘
        homotopyGroupMap (loopSpaceMapContinuous f y) n (Path.refl y) =
      homotopyGroupMap f (n + 1) y ∘
        loopSpaceHomotopyGroupEquivPiSucc n y := by
  -- Reduce the quotient statement to the representative-level compatibility theorem.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  change
    Quotient.mk' (loopSpaceRepresentativeEquiv n (f y)
      (genLoopMap (loopSpaceMapContinuous f y) γ)) =
      Quotient.mk' (genLoopMap f (loopSpaceRepresentativeEquiv n y γ))
  exact congrArg Quotient.mk' (loopSpaceRepresentativeEquiv_genLoopMap_eq f n γ)

/-- Helper for Lemma 9.4.1: the canonical `π₁`/fundamental-group bridge commutes with the induced
map on representatives. -/
private theorem genLoopEquivOfUnique_genLoopMap_eq_pathMap
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {y : Y} (γ : Ω^ (Fin 1) Y y) :
    genLoopEquivOfUnique (X := Z) (x := f y) (Fin 1) (genLoopMap f γ) =
      (genLoopEquivOfUnique (X := Y) (x := y) (Fin 1) γ).map f.continuous := by
  -- Both paths evaluate the unique cube-coordinate and then postcompose by `f`.
  ext t
  rfl

/-- Helper for Lemma 9.4.1: under the canonical `π₁`/fundamental-group identification, the local
`homotopyGroupMap` agrees with `FundamentalGroup.map`. -/
private theorem homotopyGroupMap_one_eq_fundamentalGroupMap
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y : Y) :
    (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Z (f y) ≃ FundamentalGroup Z (f y)) ∘
        homotopyGroupMap f 1 y =
      (FundamentalGroup.map f y) ∘
        (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Y y ≃ FundamentalGroup Y y) := by
  -- Reduce to representatives, where both constructions are literally postcomposition by `f`.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  change
    Path.Homotopic.Quotient.mk
        (genLoopEquivOfUnique (X := Z) (x := f y) (Fin 1) (genLoopMap f γ)) =
      Path.Homotopic.Quotient.mk
        ((genLoopEquivOfUnique (X := Y) (x := y) (Fin 1) γ).map f.continuous)
  exact congrArg Path.Homotopic.Quotient.mk
    (genLoopEquivOfUnique_genLoopMap_eq_pathMap f γ)

/-- Helper for Lemma 9.4.1: a continuous map with a left homotopy inverse induces an injective map
on `π₁` by comparison with the fundamental group. -/
private theorem homotopyGroupMap_injective_of_leftHomotopy_one
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(Z, Y)) (H : (g.comp f).Homotopy (ContinuousMap.id Y)) (y : Y) :
    Function.Injective (homotopyGroupMap f 1 y) := by
  intro a b hab
  -- Transport the equality across the `π₁`/fundamental-group comparison on the target.
  apply
    (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Y y ≃ FundamentalGroup Y y).injective
  apply fundamentalGroupMap_injective_of_leftHomotopy f g H y
  have hNat := homotopyGroupMap_one_eq_fundamentalGroupMap f y
  -- Rewrite both sides of the target equality using the naturality of `π₁`.
  calc
    FundamentalGroup.map f y
        ((HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Y y ≃ FundamentalGroup Y y) a)
      = (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Z (f y) ≃ FundamentalGroup Z (f y))
          (homotopyGroupMap f 1 y a) := by
            exact (congrArg (fun g ↦ g a) hNat).symm
    _ = (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Z (f y) ≃ FundamentalGroup Z (f y))
          (homotopyGroupMap f 1 y b) := by
            exact congrArg
              (HomotopyGroup.pi1EquivFundamentalGroup :
                π_ 1 Z (f y) ≃ FundamentalGroup Z (f y)) hab
    _ = FundamentalGroup.map f y
          ((HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Y y ≃ FundamentalGroup Y y) b) := by
            exact congrArg (fun g ↦ g b) hNat

/-- Helper for Lemma 9.4.1: a homotopy equivalence already gives injectivity on `π₁` by
specializing the left-homotopy theorem to its chosen left inverse. -/
private theorem homotopyGroupMap_injective_of_homotopyEquiv_one
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv Y Z) (y : Y) :
    Function.Injective (homotopyGroupMap e.toFun 1 y) := by
  -- Reuse the left-homotopy `π₁` criterion with the chosen left inverse of `e`.
  classical
  exact
    homotopyGroupMap_injective_of_leftHomotopy_one
      e.toFun e.invFun (Classical.choice e.left_inv) y

/-- Helper for Lemma 9.4.1: converting a postcomposed generalized loop into the loop-space owner
agrees with first converting to the loop-space owner and then applying the induced loop-space map.
-/
private theorem toLoop_genLoopMap_eq_pathMap
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (k : ℕ) {y : Y} (γ : Ω^ (Fin (k + 2)) Y y) :
    GenLoop.toLoop (0 : Fin (k + 2)) (genLoopMap f γ) =
      (GenLoop.toLoop (0 : Fin (k + 2)) γ).map
        (genLoopMapContinuous (N := {j : Fin (k + 2) // j ≠ (0 : Fin (k + 2))}) f).continuous := by
  -- Both paths evaluate by inserting the distinguished coordinate and then postcomposing by `f`.
  ext t tn
  rfl

/-- Helper for Lemma 9.4.1: after rewriting `π_(k+2)` as a fundamental group of the loop-space
owner, the map induced by `f` is the corresponding fundamental-group map on that owner. -/
private theorem homotopyGroupMap_eq_fundamentalGroupMap_via_loopOwner
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (k : ℕ) (y : Y) :
    (homotopyGroupEquivFundamentalGroup (X := Z) (x := f y) (i := (0 : Fin (k + 2)))) ∘
        homotopyGroupMap f (k + 2) y =
      (FundamentalGroup.map
          (genLoopMapContinuous (N := {j : Fin (k + 2) // j ≠ (0 : Fin (k + 2))}) f)
          GenLoop.const) ∘
        (homotopyGroupEquivFundamentalGroup (X := Y) (x := y) (i := (0 : Fin (k + 2)))) := by
  -- Reduce the quotient-level claim to the representative-level compatibility of `toLoop`.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  -- After unfolding the quotient-based constructions, both sides are path classes in the
  -- loop-space owner.
  change
    Path.Homotopic.Quotient.mk (GenLoop.toLoop (0 : Fin (k + 2)) (genLoopMap f γ)) =
      Path.Homotopic.Quotient.mk
        ((GenLoop.toLoop (0 : Fin (k + 2)) γ).map
          (genLoopMapContinuous (N := {j : Fin (k + 2) // j ≠ (0 : Fin (k + 2))}) f).continuous)
  exact congrArg Path.Homotopic.Quotient.mk (toLoop_genLoopMap_eq_pathMap f k γ)

/-- Helper for Lemma 9.4.1: a left homotopy inverse on spaces induces a left homotopy section on
ordinary loop spaces after correcting the basepoint by the endpoint track. -/
private theorem loopSpaceMapContinuous_leftSection
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(Z, Y)) (H : (g.comp f).Homotopy (ContinuousMap.id Y)) (y : Y) :
    ∃ s : C(Ω Z (f y), Ω Y y),
      ContinuousMap.Homotopic (s.comp (loopSpaceMapContinuous f y)) (ContinuousMap.id _) :=
    by
  -- Route correction: the higher-degree induction only needs a one-sided loop-space section, so
  -- we avoid constructing a full loop-space homotopy equivalence.
  let p : Path (g (f y)) y := H.evalAt y
  let s : C(Ω Z (f y), Ω Y y) :=
    (loopSpaceBaseChangeMap p).comp (loopSpaceMapContinuous g (f y))
  refine ⟨s, ?_⟩
  have hTransport :
      ContinuousMap.Homotopic (s.comp (loopSpaceMapContinuous f y))
        (loopSpaceBaseChangeMap (Path.refl y)) := by
    let tail : (q : Ω Y y × I) → Path (p q.2) y := fun q ↦
      (p.subpath q.2 1).cast rfl p.target.symm
    let mid : (q : Ω Y y × I) → Ω Y (p q.2) := fun q ↦
      Path.mk
        ⟨fun u ↦ H (q.2, q.1 u),
          H.continuous_toFun.comp (continuous_const.prodMk q.1.continuous)⟩
        (by
          change H (q.2, q.1 0) = H (q.2, y)
          simpa using congrArg (fun z ↦ H (q.2, z)) q.1.source)
        (by
          change H (q.2, q.1 1) = H (q.2, y)
          simpa using congrArg (fun z ↦ H (q.2, z)) q.1.target)
    have hTail : Continuous ↿tail := by
      -- The tail of `p` varies continuously in the start parameter.
      simpa [tail] using
        p.subpath_continuous_family.comp
          ((continuous_snd.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have hMid : Continuous ↿mid := by
      -- The middle loop is obtained by evaluating the ambient homotopy along `γ`.
      change Continuous fun q : ((Ω Y y × I) × I) ↦ H (q.1.2, q.1.1 q.2)
      exact H.continuous_toFun.comp <|
        (continuous_snd.comp continuous_fst).prodMk <|
          continuous_eval.comp <|
            (continuous_fst.comp continuous_fst).prodMk continuous_snd
    have hRight :
        Continuous ↿fun q : Ω Y y × I ↦ (mid q).trans (tail q) := by
      -- First append the moving tail to the intermediate loop.
      exact Path.trans_continuous_family mid hMid tail hTail
    have hAll :
        Continuous ↿fun q : Ω Y y × I ↦ (tail q).symm.trans ((mid q).trans (tail q)) := by
      -- Then conjugate by the inverse tail to move the basepoint back to `y`.
      exact
        Path.trans_continuous_family
          (fun q ↦ (tail q).symm) (Path.symm_continuous_family tail hTail)
          (fun q ↦ (mid q).trans (tail q)) hRight
    let F : C(Ω Y y × I, Ω Y y) :=
      ⟨fun q ↦ (tail q).symm.trans ((mid q).trans (tail q)),
        Path.continuous_uncurry_iff.mp hAll⟩
    refine ⟨ContinuousMap.Homotopy.ofProdSwap F ?_ ?_⟩
    · intro γ
      -- At time `0`, the family is exactly the section followed by `f_*`.
      have hp0 : p 0 = g (f y) := by
        simpa [p] using p.source
      have hTailZero :
          tail (γ, 0) = p.cast hp0 rfl := by
        ext t
        change p.subpath 0 1 t = p t
        rw [Path.subpath_zero_one]
        rfl
      have hMidZero :
          mid (γ, 0) =
            (((loopSpaceMapContinuous g (f y)).comp
              (loopSpaceMapContinuous f y)) γ).cast hp0 hp0 := by
        ext t
        change H (0, γ t) = g (f (γ t))
        simpa using H.apply_zero (γ t)
      change (tail (γ, 0)).symm.trans ((mid (γ, 0)).trans (tail (γ, 0))) =
        (s.comp (loopSpaceMapContinuous f y)) γ
      rw [hTailZero, hMidZero]
      ext u
      rfl
    · intro γ
      -- At time `1`, only the reflexive basepoint correction remains.
      have hp1 : p 1 = y := by
        simpa [p] using p.target
      have hTailOne :
          tail (γ, 1) = (Path.refl y).cast hp1 rfl := by
        ext t
        change p.subpath 1 1 t = y
        rw [Path.subpath_self]
        simpa [hp1]
      have hMidOne :
          mid (γ, 1) = γ.cast hp1 hp1 := by
        ext t
        change H (1, γ t) = γ t
        simpa using H.apply_one (γ t)
      change (tail (γ, 1)).symm.trans ((mid (γ, 1)).trans (tail (γ, 1))) =
        (loopSpaceBaseChangeMap (Path.refl y)) γ
      rw [hTailOne, hMidOne]
      ext u
      rfl
  let rightUnit : C(Ω Y y, Ω Y y) :=
    ⟨fun γ ↦ γ.trans (Path.refl y), by
      simpa using
        (Continuous.path_trans
          (f := fun γ : Ω Y y ↦ γ)
          (g := fun _ : Ω Y y ↦ Path.refl y) continuous_id continuous_const)⟩
  have hLeftUnit :
      ContinuousMap.Homotopic (loopSpaceBaseChangeMap (Path.refl y)) rightUnit := by
    let F : C(Ω Y y × I, Ω Y y) :=
      ⟨fun q ↦ Path.delayReflLeft q.2 (q.1.trans (Path.refl y)), by
        have hLoop : Continuous fun q : Ω Y y × I ↦ q.1.trans (Path.refl y) := by
          simpa using
            (Continuous.path_trans
              (f := fun q : Ω Y y × I ↦ q.1)
              (g := fun _ : Ω Y y × I ↦ Path.refl y) continuous_fst continuous_const)
        exact Path.continuous_delayReflLeft.comp (continuous_snd.prodMk hLoop)⟩
    refine ⟨ContinuousMap.Homotopy.ofProdSwap F ?_ ?_⟩
    · intro γ
      -- At time `0`, this is the left-unit part of the reflexive basepoint correction.
      simpa [F, loopSpaceBaseChangeMap] using Path.delayReflLeft_zero (γ.trans (Path.refl y))
    · intro γ
      -- At time `1`, only the right-unit correction remains.
      simpa [F, rightUnit] using Path.delayReflLeft_one (γ.trans (Path.refl y))
  have hRightUnit :
      ContinuousMap.Homotopic rightUnit (ContinuousMap.id _) := by
    let F : C(Ω Y y × I, Ω Y y) :=
      ⟨fun q ↦ Path.delayReflRight q.2 q.1, by
        exact Path.continuous_delayReflRight.comp (continuous_snd.prodMk continuous_fst)⟩
    refine ⟨ContinuousMap.Homotopy.ofProdSwap F ?_ ?_⟩
    · intro γ
      -- At time `0`, this is the right-unit path.
      simpa [F, rightUnit] using Path.delayReflRight_zero γ
    · intro γ
      -- At time `1`, the right-unit homotopy reaches the original loop.
      simpa [F] using Path.delayReflRight_one γ
  -- Compose the transport homotopy with the canonical reflexive basepoint cleanup.
  exact
    ContinuousMap.Homotopic.trans hTransport
      (ContinuousMap.Homotopic.trans hLeftUnit hRightUnit)

/-- Helper for Lemma 9.4.1: higher-degree maps with a left homotopy inverse are injective,
proved by induction after shifting to ordinary loop spaces. -/
private theorem homotopyGroupMap_injective_of_leftHomotopy_succ_succ
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(Z, Y)) (H : (g.comp f).Homotopy (ContinuousMap.id Y))
    (k : ℕ) (y : Y) :
    Function.Injective (homotopyGroupMap f (k + 2) y) := by
  induction k generalizing Y Z y f g with
  | zero =>
      -- Shift `π₂` to `π₁` of the ordinary loop space and use the degree-`1` left-section
      -- criterion there.
      let eY := loopSpaceHomotopyGroupEquivPiSucc 1 y
      let eZ := loopSpaceHomotopyGroupEquivPiSucc 1 (f y)
      have hNat := homotopyGroupMap_piSucc_eq_loopSpaceMap f 1 y
      obtain ⟨sLoop, hLoopHomotopic⟩ := loopSpaceMapContinuous_leftSection f g H y
      let hLoop :
          (sLoop.comp (loopSpaceMapContinuous f y)).Homotopy (ContinuousMap.id _) :=
        Classical.choice hLoopHomotopic
      have hLoop :
          Function.Injective
            (homotopyGroupMap (loopSpaceMapContinuous f y) 1 (Path.refl y)) := by
        -- The induced loop-space map already has a left homotopy section.
        exact
          homotopyGroupMap_injective_of_leftHomotopy_one
            (loopSpaceMapContinuous f y) sLoop hLoop (Path.refl y)
      intro a b hab
      apply eY.symm.injective
      apply hLoop
      apply eZ.injective
      calc
        loopSpaceHomotopyGroupEquivPiSucc 1 (f y)
            (homotopyGroupMap (loopSpaceMapContinuous f y) 1 (Path.refl y) (eY.symm a))
          = homotopyGroupMap f 2 y (eY (eY.symm a)) := by
              exact congrArg (fun g ↦ g (eY.symm a)) hNat
        _ = homotopyGroupMap f 2 y a := by
              simp [eY]
        _ = homotopyGroupMap f 2 y b := hab
        _ = homotopyGroupMap f 2 y (eY (eY.symm b)) := by
              simp [eY]
        _ = loopSpaceHomotopyGroupEquivPiSucc 1 (f y)
              (homotopyGroupMap (loopSpaceMapContinuous f y) 1 (Path.refl y)
                (eY.symm b)) := by
              exact (congrArg (fun g ↦ g (eY.symm b)) hNat).symm
  | succ k ih =>
      -- Shift once and invoke the induction hypothesis on the induced loop-space map with its
      -- one-sided section.
      let eY := loopSpaceHomotopyGroupEquivPiSucc (k + 2) y
      let eZ := loopSpaceHomotopyGroupEquivPiSucc (k + 2) (f y)
      have hNat := homotopyGroupMap_piSucc_eq_loopSpaceMap f (k + 2) y
      obtain ⟨sLoop, hLoopHomotopic⟩ := loopSpaceMapContinuous_leftSection f g H y
      let hLoop :
          (sLoop.comp (loopSpaceMapContinuous f y)).Homotopy (ContinuousMap.id _) :=
        Classical.choice hLoopHomotopic
      have hLoop :
          Function.Injective
            (homotopyGroupMap (loopSpaceMapContinuous f y) (k + 2) (Path.refl y)) := by
        -- The inductive step is exactly the same statement one loop lower.
        exact ih (loopSpaceMapContinuous f y) sLoop hLoop (Path.refl y)
      intro a b hab
      apply eY.symm.injective
      apply hLoop
      apply eZ.injective
      calc
        loopSpaceHomotopyGroupEquivPiSucc (k + 2) (f y)
            (homotopyGroupMap (loopSpaceMapContinuous f y) (k + 2) (Path.refl y)
              (eY.symm a))
          = homotopyGroupMap f (k + 3) y (eY (eY.symm a)) := by
              exact congrArg (fun g ↦ g (eY.symm a)) hNat
        _ = homotopyGroupMap f (k + 3) y a := by
              simp [eY]
        _ = homotopyGroupMap f (k + 3) y b := hab
        _ = homotopyGroupMap f (k + 3) y (eY (eY.symm b)) := by
              simp [eY]
        _ = loopSpaceHomotopyGroupEquivPiSucc (k + 2) (f y)
              (homotopyGroupMap (loopSpaceMapContinuous f y) (k + 2) (Path.refl y)
                (eY.symm b)) := by
              exact (congrArg (fun g ↦ g (eY.symm b)) hNat).symm

/-- Helper for Lemma 9.4.1: higher-degree maps induced by homotopy equivalences are injective by
specializing the one-sided criterion to the chosen left inverse. -/
private theorem homotopyGroupMap_injective_of_homotopyEquiv_succ_succ
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv Y Z) (k : ℕ) (y : Y) :
    Function.Injective (homotopyGroupMap e.toFun (k + 2) y) := by
  -- Reuse the one-sided higher-degree injectivity theorem with the chosen left inverse of `e`.
  classical
  exact
    homotopyGroupMap_injective_of_leftHomotopy_succ_succ
      e.toFun e.invFun (Classical.choice e.left_inv) k y

instance homotopyGroupSubsingletonOfContractible (n : ℕ) (x : X) :
    Subsingleton (π_ n X x) := by
  cases n with
  | zero =>
      -- The zeroth homotopy group is the path-component quotient.
      exact pi0SubsingletonOfContractible x
  | succ m =>
      cases m with
      | zero =>
          -- The first homotopy group is the fundamental group, which is trivial here.
          exact pi1SubsingletonOfContractible x
      | succ k =>
          -- Map into the contractible target `Unit`, where every homotopy group is already
          -- subsingleton.
          obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
          let hUnit : Subsingleton (π_ (k + 2) Unit (e x)) :=
            unitHomotopyGroupSubsingleton (k + 2) (e x)
          let hInj : Function.Injective (homotopyGroupMap e.toFun (k + 2) x) :=
            homotopyGroupMap_injective_of_homotopyEquiv_succ_succ e k x
          -- Injectivity transports the triviality of the target homotopy group back to the source.
          refine ⟨fun a b ↦ hInj ?_⟩
          exact Subsingleton.elim _ _

/-- Lemma 9.4.1: if `X` is contractible, then `π_ n X x` is trivial for every `n : ℕ` and every
basepoint `x : X`. -/
theorem homotopyGroup_subsingleton_of_contractible (n : ℕ) (x : X) :
    Subsingleton (π_ n X x) :=
  inferInstance
