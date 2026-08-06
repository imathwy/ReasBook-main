import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_3_3

open CategoryTheory
open scoped BigOperators Manifold Topology

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced no verified Wu-class owner in the current
-- environment, so this file packages the source-facing Wu-class family directly through the
-- chapter-local Steenrod-square and tangential Stiefel-Whitney owners.

section

variable (H2 : ModTwoCohomologyTheory)
variable {suspension : TopCat ⥤ TopCat}
variable {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
variable (Sq : SteenrodSquareFamily H2 suspension suspensionIso)

/-- A Wu-class family on `M` for the chosen ambient mod-`2` cohomology theory `H2`: one class
`v_i ∈ H^i(M; ZMod 2)` in each degree `i`. -/
abbrev WuClassFamily (H2 : ModTwoCohomologyTheory) (M : Type) [TopologicalSpace M] :=
  ∀ i : ℕ, modTwoCohomologyGroup H2 i (TopCat.of M)

/-- The degree-`k` component of the total Steenrod-square expression `Sq(v)` on `M`. -/
def wuFormulaExpansion
    (M : Type) [TopologicalSpace M]
    (v : WuClassFamily H2 M) (k : ℕ) :
    modTwoCohomologyGroup H2 k (TopCat.of M) :=
  ∑ i : Fin (k + 1),
    cast
      (by
        simpa using
          congrArg
            (fun m ↦ ((modTwoCohomologyGroup H2 m (TopCat.of M)) : Type))
            (Nat.sub_add_cancel (Nat.le_of_lt_succ i.2)))
      (Sq.sq i (k - i) (TopCat.of M) (v (k - i)))

/-- Unfolding `wuFormulaExpansion H2 Sq M v k` recovers the finite degreewise Wu-formula sum. -/
theorem wuFormulaExpansion_def
    (M : Type) [TopologicalSpace M]
    (v : WuClassFamily H2 M) (k : ℕ) :
    wuFormulaExpansion H2 Sq M v k =
      ∑ i : Fin (k + 1),
        cast
          (by
            simpa using
              congrArg
                (fun m ↦ ((modTwoCohomologyGroup H2 m (TopCat.of M)) : Type))
                (Nat.sub_add_cancel (Nat.le_of_lt_succ i.2)))
          (Sq.sq i (k - i) (TopCat.of M) (v (k - i))) := sorry

variable (n : ℕ)
variable (M : Type) [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) ⊤ M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
variable [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]

/-- A family `v_i ∈ H^i(M; ZMod 2)` is a Wu-class family for the tangent Stiefel-Whitney classes
of the smooth `n`-manifold `M` when each `w_k(M)` is recovered by the degree-`k`
Steenrod-square expansion of `v`. -/
def IsWuClassFamily
    (w : StiefelWhitneyClassFamily H2) (v : WuClassFamily H2 M) : Prop :=
  ∀ k : ℕ,
    tangentialStiefelWhitneyClass n M H2 w k =
      wuFormulaExpansion H2 Sq M v k

/-- Unfolding `IsWuClassFamily H2 Sq n M w v` recovers the degreewise Wu formula for each
tangential Stiefel-Whitney class of `M`. -/
theorem isWuClassFamily_iff
    {w : StiefelWhitneyClassFamily H2} {v : WuClassFamily H2 M} :
    IsWuClassFamily H2 Sq n M w v ↔
      ∀ k : ℕ,
        tangentialStiefelWhitneyClass n M H2 w k =
          wuFormulaExpansion H2 Sq M v k :=
  Iff.rfl

/-- A Wu-class family on `M` satisfies the Wu formula in each degree. -/
theorem isWuClassFamily_apply
    {w : StiefelWhitneyClassFamily H2} {v : WuClassFamily H2 M}
    (h_wu : IsWuClassFamily H2 Sq n M w v) (k : ℕ) :
    tangentialStiefelWhitneyClass n M H2 w k =
      wuFormulaExpansion H2 Sq M v k :=
  h_wu k

/-- Theorem 23.3.4. For a smooth closed `n`-manifold `M`, any Stiefel-Whitney theory `w` on the
chosen ambient mod-`2` cohomology theory has a family of Wu classes whose Steenrod-square
expansion recovers the tangential Stiefel-Whitney classes of `M`. Here "closed" is recorded by
`[T2Space M]` and `[CompactSpace M]`, while the smooth boundaryless structure is encoded by the
`(𝓡 n)`-manifold hypotheses. -/
theorem exists_wuClassFamily_for_tangentStiefelWhitneyClasses
    [T2Space M] [CompactSpace M]
    (normalizationData : StiefelWhitneyNormalization H2)
    (w : StiefelWhitneyClassFamily H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w) :
    ∃ v : WuClassFamily H2 M,
      IsWuClassFamily H2 Sq n M w v := sorry

end
