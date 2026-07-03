

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_40 (from Chap01/Sec01_05) -/
noncomputable section

open Set

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [TopologicalManifoldWithBoundary n M]

/-- A coordinate ball in Lee's boundary model is the source of a chart whose target is an open
metric ball centered away from the boundary hyperplane. In dimension `0`, this is the ordinary
coordinate-ball condition in `ℝ^0`. -/
def IsBoundaryModelCoordinateBall (n : ℕ) (s : Set M) : Prop :=
  match n with
  | 0 =>
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 0)),
        e.source = s ∧
          ∃ c : EuclideanSpace ℝ (Fin 0), ∃ r : ℝ, 0 < r ∧ e.target = Metric.ball c r
  | m + 1 =>
      let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
      show Prop from
        ∃ e : OpenPartialHomeomorph M { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 },
          e.source = s ∧
            ∃ c : { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 }, ∃ r : ℝ,
              0 < r ∧ r < c.1 0 ∧ e.target = Metric.ball c r

/-- A coordinate half-ball in Lee's boundary model is the source of a chart whose target is an open
metric ball centered on the boundary hyperplane. In dimension `0` there are no half-balls. -/
def IsBoundaryModelCoordinateHalfBall (n : ℕ) (s : Set M) : Prop :=
  match n with
  | 0 => False
  | m + 1 =>
      let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
      show Prop from
        ∃ e : OpenPartialHomeomorph M { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 },
          e.source = s ∧
            ∃ c : { x : EuclideanSpace ℝ (Fin (m + 1)) // 0 ≤ x 0 }, ∃ r : ℝ,
              0 < r ∧ c.1 0 = 0 ∧ e.target = Metric.ball c r

/-- A precompact boundary-model coordinate ball is a coordinate ball with compact closure. -/
def IsPrecompactBoundaryModelCoordinateBall (n : ℕ) (s : Set M) : Prop :=
  IsBoundaryModelCoordinateBall n s ∧ IsCompact (closure s)

/-- A precompact boundary-model coordinate half-ball is a coordinate half-ball with compact
closure. -/
def IsPrecompactBoundaryModelCoordinateHalfBall (n : ℕ) (s : Set M) : Prop :=
  IsBoundaryModelCoordinateHalfBall n s ∧ IsCompact (closure s)

/-- A basis all of whose members are precompact boundary-model coordinate balls or half-balls. -/
class IsPrecompactBoundaryModelCoordinateBallHalfBallBasis
    (n : ℕ) (b : Set (Set M)) : Prop where
  isTopologicalBasis : TopologicalSpace.IsTopologicalBasis b
  mem_isPrecompactBoundaryModelCoordinateBall_or_halfBall :
    ∀ s ∈ b,
      IsPrecompactBoundaryModelCoordinateBall n s ∨
        IsPrecompactBoundaryModelCoordinateHalfBall n s

-- Proof sketch: refine the countable atlas by choosing, inside each chart target, a countable
-- family of rational balls centered either in the interior or on the boundary hyperplane and with
-- compact closure inside the chart domain, then pull them back to `M`.
/-- Proposition 1.40 (1): a topological manifold with boundary admits a countable basis consisting
of precompact coordinate balls and precompact coordinate half-balls. -/
theorem exists_countable_precompact_coordinate_ball_half_ball_basis :
    ∃ b : Set (Set M),
      b.Countable ∧ IsPrecompactBoundaryModelCoordinateBallHalfBallBasis n b := sorry

-- Proof sketch: the model spaces `ℝ^0` and `H^n` are locally compact, and local compactness
-- transfers from the model space to any charted space.
/-- Proposition 1.40 (2): a topological manifold with boundary is locally compact. -/
theorem topologicalManifoldWithBoundary_locallyCompactSpace : LocallyCompactSpace M := sorry

-- Proof sketch: combine local compactness from the previous clause with second countability and
-- Hausdorff separation, then apply the standard paracompactness theorem for such spaces.
/-- Proposition 1.40 (3): a topological manifold with boundary is paracompact. -/
theorem topologicalManifoldWithBoundary_paracompactSpace : ParacompactSpace M := sorry

-- Proof sketch: every point has a chart into `ℝ^0` or a Euclidean half-space, and these model
-- spaces are locally path-connected; the property transfers across local homeomorphisms.
/-- Proposition 1.40 (4): a topological manifold with boundary is locally path-connected. -/
instance topologicalManifoldWithBoundaryLocPathConnectedSpace : LocPathConnectedSpace M := sorry

/-- Convenience theorem restating the local path-connectedness instance. -/
theorem topologicalManifoldWithBoundary_locPathConnectedSpace : LocPathConnectedSpace M :=
  inferInstance

/-- The connected component through `x`, regarded as an open subset of the ambient manifold. -/
def connectedComponentOpens (x : M) : TopologicalSpace.Opens M :=
  ⟨connectedComponent x, isOpen_connectedComponent⟩

-- Proof sketch: local path-connectedness makes connected components open, hence the quotient by
-- connected components is discrete; second countability then forces this quotient to be countable.
/-- Proposition 1.40 (5): a topological manifold with boundary has countably many connected
components. -/
theorem topologicalManifoldWithBoundary_countable_connectedComponents :
    Countable (ConnectedComponents M) := sorry

-- Proof sketch: in a locally path-connected space, connected components are open because locally
-- path-connected spaces are locally connected.
/-- Proposition 1.40 (6): every connected component of a topological manifold with boundary is an
open subset of the manifold. -/
theorem connectedComponent_isOpen (x : M) : IsOpen (connectedComponent x) := sorry

-- Proof sketch: by definition, the connected component of `x` is the maximal connected subset
-- containing `x`, so its subtype is connected.
/-- Proposition 1.40 (7): each connected component, viewed as a subtype, is connected. -/
theorem connectedComponent_connectedSpace (x : M) :
    ConnectedSpace (connectedComponentOpens x) := sorry

-- Proof sketch: once a connected component is viewed as an open subset, it inherits the ambient
-- charts, Hausdorff property, and second-countable topology, hence the same manifold-with-boundary
-- structure.
/-- Proposition 1.40 (8): each connected component, viewed as an open subset, is a connected
topological manifold with boundary. -/
instance connectedComponent_topologicalManifoldWithBoundary (x : M) :
    TopologicalManifoldWithBoundary n (connectedComponentOpens x) := sorry

-- Proof sketch: a second-countable locally path-connected manifold admits a countable loop space
-- model up to homotopy, so the quotient defining the fundamental group at a basepoint is
-- countable.
/-- Proposition 1.40 (9): the fundamental group at any basepoint of a topological manifold with
boundary is countable. -/
theorem countable_fundamentalGroup (x : M) : Countable (FundamentalGroup M x) := sorry
