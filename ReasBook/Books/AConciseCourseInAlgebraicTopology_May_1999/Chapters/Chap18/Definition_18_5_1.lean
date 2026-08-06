import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_5_2

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]
  [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]

-- Semantic recall via `lean_leansearch`, local search, and repo precedent: mathlib still does not
-- expose a named `π₁`-action on higher homotopy groups, while Chapter 9 already provides the
-- Section 9.5 basepoint-change equivalence on the explicit sphere-evaluation fiber model
-- `ZerothHomotopy (sphereBasepointFiber q x)` for `π_q(X, x)`.

/-- The Section 9.5 `π₁(X, x)`-action on the source-facing sphere-fiber owner of `π_q(X, x)`. -/
noncomputable def piOneSphereFiberAction (x : X) (q : ℕ) :
    FundamentalGroup X x →* Equiv.Perm (ZerothHomotopy (sphereBasepointFiber q x)) where
  toFun γ := sphereBasepointFiberZerothEquivOfPathClass q γ.toPath
  map_one' := sorry
  map_mul' := sorry

/-- Applying `piOneSphereFiberAction x q` amounts to applying the Chapter 9 transported map on
path components induced by the loop class `γ : π₁(X, x)`. -/
theorem piOneSphereFiberAction_apply (x : X) (q : ℕ) (γ : FundamentalGroup X x)
    (η : ZerothHomotopy (sphereBasepointFiber q x)) :
    piOneSphereFiberAction x q γ η = sphereBasepointFiberZerothMap q γ.toPath η :=
  sphereBasepointFiberZerothEquivOfPathClass_apply q γ.toPath η

/-- The identity element of `π₁(X, x)` acts trivially on the path-component owner of the chosen
sphere-map fiber. -/
theorem piOneSphereFiberAction_one_apply (x : X) (q : ℕ)
    (η : ZerothHomotopy (sphereBasepointFiber q x)) :
    piOneSphereFiberAction x q 1 η = η := sorry

/-- Definition 18.5.1 (1): a connected space `X` is `n`-simple when `π₁(X, x)` is abelian and the
Section 9.5 action `piOneSphereFiberAction x q` on the source-facing sphere-fiber owner of
`π_q(X, x)` is trivial for every `1 ≤ q ≤ n`. -/
class NSimpleSpace (n : ℕ) (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] : Prop extends ConnectedSpace X where
  /-- The fundamental group at every basepoint is abelian. -/
  pi1_abelian : ∀ x : X, ∀ a b : FundamentalGroup X x, a * b = b * a
  /-- The Section 9.5 `π₁`-action on each `π_q(X, x)` with `1 ≤ q ≤ n` is trivial, expressed on
  the source-facing owner `ZerothHomotopy (sphereBasepointFiber q x)`. -/
  action_trivial :
    ∀ x : X, ∀ q : ℕ, 1 ≤ q → q ≤ n →
      ∀ γ : FundamentalGroup X x, ∀ η : ZerothHomotopy (sphereBasepointFiber q x),
        piOneSphereFiberAction x q γ η = η

/-- `NSimpleSpace n X` is a proposition. -/
instance instSubsingletonNSimpleSpace (n : ℕ) (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] :
    Subsingleton (NSimpleSpace n X) :=
  inferInstance

/-- `NSimpleSpace n X` is exactly connectedness, abelian `π₁`, and triviality of the Section 9.5
`π₁`-action on `π_q(X, x)` for all `1 ≤ q ≤ n`, expressed on the source-facing sphere-fiber owner
of `π_q(X, x)`. -/
theorem nSimpleSpace_iff (n : ℕ) (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] :
    NSimpleSpace n X ↔
      ConnectedSpace X ∧
        (∀ x : X, ∀ a b : FundamentalGroup X x, a * b = b * a) ∧
        (∀ x : X, ∀ q : ℕ, 1 ≤ q → q ≤ n →
          ∀ γ : FundamentalGroup X x, ∀ η : ZerothHomotopy (sphereBasepointFiber q x),
            piOneSphereFiberAction x q γ η = η) := by
  constructor
  · intro h
    exact ⟨h.toConnectedSpace, h.pi1_abelian, h.action_trivial⟩
  · rintro ⟨h_connected, h_pi1_abelian, h_action_trivial⟩
    exact
      { toConnectedSpace := h_connected
        pi1_abelian := h_pi1_abelian
        action_trivial := h_action_trivial }

/-- Definition 18.5.1 (2): a connected space `X` is simple when it is `n`-simple for every `n`. -/
class SimpleSpace (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] : Prop where
  /-- Every simple space is `n`-simple in each degree `n`. -/
  nSimple : ∀ n : ℕ, NSimpleSpace n X

/-- A simple space is `n`-simple in every degree. -/
instance instNSimpleSpaceOfSimpleSpace (n : ℕ) (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] [SimpleSpace X] :
    NSimpleSpace n X :=
  SimpleSpace.nSimple n

/-- A simple space is connected because it is `0`-simple. -/
instance instConnectedSpaceOfSimpleSpace (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] [SimpleSpace X] :
    ConnectedSpace X :=
  (inferInstance : NSimpleSpace 0 X).toConnectedSpace

/-- `SimpleSpace X` is exactly the requirement that `X` be `n`-simple for every `n`. -/
theorem simpleSpace_iff (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X] :
    SimpleSpace X ↔ ∀ n : ℕ, NSimpleSpace n X := by
  constructor
  · intro h n
    exact h.nSimple n
  · intro h
    exact ⟨h⟩
