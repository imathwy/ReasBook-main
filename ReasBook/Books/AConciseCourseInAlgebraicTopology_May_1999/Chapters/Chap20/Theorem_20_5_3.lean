import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_5_2

open CategoryTheory
open scoped Manifold Topology

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {π : Type u} [AddCommGroup π]
variable (Hcoh : PairCohomologyTheory π)
variable {n : ℕ}
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ V H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ V = n)] [UnivLE.{u, v}]

/-- The automation-facing compact-support Poincare duality isomorphism for the global map from
Construction 20.5.2. The parameter `localCap` packages the local maps
`D_K(-) = - ∩ [M]_K`, and `fundamentalClass` supplies the compatible family of compact
fundamental classes used to assemble the global morphism. -/
instance compactlySupportedPoincareDualityMap_isIso
    (o : ROrientedManifold R I n M) (p : ℕ)
    (localCap : CompactlySupportedLocalCapWithFundamentalClass Hcoh R M n p)
    (fundamentalClass : CompactFundamentalClassFamily o) :
    IsIso (compactlySupportedPoincareDualityMap Hcoh R o p localCap fundamentalClass) := by
  sorry

/-- Theorem 20.5.3. For an `R`-oriented manifold `M`, the compact-support duality map
`H_c^p(M; π) ⟶ H_(n - p)(M; R)` assembled in Construction 20.5.2 from the local
cap-with-fundamental-class maps is an isomorphism. -/
theorem compactlySupportedPoincareDuality
    (o : ROrientedManifold R I n M) (p : ℕ)
    (localCap : CompactlySupportedLocalCapWithFundamentalClass Hcoh R M n p)
    (fundamentalClass : CompactFundamentalClassFamily o) :
    IsIso (compactlySupportedPoincareDualityMap Hcoh R o p localCap fundamentalClass) := by
  infer_instance

end
