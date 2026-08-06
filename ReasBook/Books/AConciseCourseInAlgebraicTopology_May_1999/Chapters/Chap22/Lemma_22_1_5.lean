import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Lemma_22_1_5.Comparison

universe u v w

open scoped RestrictedProduct unitInterval Topology Topology.Homotopy

variable {ι : Type v}

/-- Lemma 22.1.5::statement_repair::4

Homotopy groups of a weak product are the direct sum of the homotopy groups of its factors. -/
noncomputable abbrev weakProductHomotopyGroup_mulEquiv_directSum
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    [WeakProductHasFiniteStageCompactFactorization X] :
    π_ (n : ℕ) (weakProduct X).toCompactlyGenerated (weakProductPoint X) ≃*
      weakProductHomotopyGroupDirectSum n X :=
  -- Compose the transport comparison with the direct-sum comparison from the frozen prerequisite.
  (weakProductHomotopyGroupTransportMulEquiv n X).trans
    (weakProductDirectLimitHomotopyGroup_mulEquiv_directSum n X)

/-- `weakProductHomotopyGroup_mulEquiv_directSum` is the source-facing weak-product equivalence
obtained by transporting the auxiliary direct-limit equivalence supplied by
`Lemma_22_1_5.Comparison`. -/
theorem weakProductHomotopyGroup_mulEquiv_directSum_def
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    [WeakProductHasFiniteStageCompactFactorization X] :
    weakProductHomotopyGroup_mulEquiv_directSum n X =
      (weakProductHomotopyGroupTransportMulEquiv n X).trans
        (weakProductDirectLimitHomotopyGroup_mulEquiv_directSum n X) :=
  -- The companion theorem only exposes the chosen normal form of the abbrev.
  rfl

/-- Evaluating `weakProductHomotopyGroup_mulEquiv_directSum` first transports a weak-product
homotopy class to the auxiliary direct-limit model and then applies the direct-sum equivalence. -/
@[simp] theorem weakProductHomotopyGroup_mulEquiv_directSum_apply
    (n : ℕ+) (X : ι → PointedCompactlyGenerated.{u, w})
    [WeakProductHasFiniteStageCompactFactorization X]
    (f : π_ (n : ℕ) (weakProduct X).toCompactlyGenerated (weakProductPoint X)) :
    weakProductHomotopyGroup_mulEquiv_directSum n X f =
      weakProductDirectLimitHomotopyGroup_mulEquiv_directSum n X
        (weakProductHomotopyGroupTransportMulEquiv n X f) :=
  -- Applying the composite equivalence is definitionally transport followed by the direct-sum map.
  rfl
