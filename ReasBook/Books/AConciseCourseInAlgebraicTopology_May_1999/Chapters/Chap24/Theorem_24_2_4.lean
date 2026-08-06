import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Lemma_24_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_2_2

open scoped ComplexKTheory TensorProduct

noncomputable section

universe u w

-- Semantic recall via `lean_leansearch` surfaced `AddEquiv.ofBijective` as the canonical way to
-- pass from a bijective additive map to an additive equivalence. This file keeps the explicit
-- Chapter 24 reduced Bott multiplication map for the canonical reduced Hopf class on `S²` and the
-- auxiliary `S²` product-model comparison as companion API, while the labeled theorem presents
-- Bott periodicity directly as an additive equivalence on reduced `K`-theory.

/-- The reduced suspension of a compact pointed compactly generated space is compact. -/
instance reducedSuspensionCompactSpace
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated] :
    CompactSpace (reducedSuspension X).toCompactlyGenerated := sorry

/-- The reduced Bott multiplication map `K̃(X) → K̃(X × S²)` obtained from a chosen Bott
external-product map on unreduced `K`-theory by multiplying a reduced class on `X` with the
canonical reduced Hopf class `sphereTwoReducedHopfLineClass x₂` on `S²`, then projecting to the
reduced summand at the basepoint `(X.point, x₂)`. -/
def reducedBottProductMap
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w})
    (bottTensorProductMap :
      K(X.toCompactlyGenerated) ⊗[ℤ] K(SphereTwo) →+
        K(X.toCompactlyGenerated × SphereTwo)) :
    K̃(X.toCompactlyGenerated, X.point) →+
      K̃(X.toCompactlyGenerated × SphereTwo, (X.point, x₂)) where
  toFun := fun ξ ↦
    (complexKTheoryToReducedProdInt (X.toCompactlyGenerated × SphereTwo) (X.point, x₂)
      (bottTensorProductMap (ξ.1 ⊗ₜ[ℤ] (sphereTwoReducedHopfLineClass x₂).1))).1
  map_zero' := sorry
  map_add' := sorry

/-- On an input `ξ ∈ K̃(X)`, `reducedBottProductMap X x₂ bottTensorProductMap` is the reduced part
at `(X.point, x₂)` of the chosen Bott external product of `ξ` with the canonical reduced Hopf
class on `S²`. -/
theorem reducedBottProductMap_apply
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w})
    (bottTensorProductMap :
      K(X.toCompactlyGenerated) ⊗[ℤ] K(SphereTwo) →+
        K(X.toCompactlyGenerated × SphereTwo))
    (ξ : K̃(X.toCompactlyGenerated, X.point)) :
    reducedBottProductMap X x₂ bottTensorProductMap ξ =
      (complexKTheoryToReducedProdInt (X.toCompactlyGenerated × SphereTwo) (X.point, x₂)
        (bottTensorProductMap (ξ.1 ⊗ₜ[ℤ] (sphereTwoReducedHopfLineClass x₂).1))).1 := rfl

/-- Given a chosen comparison `K̃(X × S²) ≃+ K̃(Σ²X)`, the reduced Bott map to the double reduced
suspension is the composition of that comparison with `reducedBottProductMap X x₂` formed from the
chosen Bott external-product map and the canonical reduced Hopf class on `S²`. -/
def reducedBottDoubleSuspensionMap
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w})
    (bottTensorProductMap :
      K(X.toCompactlyGenerated) ⊗[ℤ] K(SphereTwo) →+
        K(X.toCompactlyGenerated × SphereTwo))
    (comparison :
      K̃(X.toCompactlyGenerated × SphereTwo, (X.point, x₂)) ≃+
        K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point)) :
    K̃(X.toCompactlyGenerated, X.point) →+
      K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point) where
  toFun := fun ξ ↦ comparison (reducedBottProductMap X x₂ bottTensorProductMap ξ)
  map_zero' := sorry
  map_add' := sorry

/-- On an input `ξ ∈ K̃(X)`, `reducedBottDoubleSuspensionMap X x₂ bottTensorProductMap comparison`
is the chosen comparison applied to the reduced Bott product class
`reducedBottProductMap X x₂ bottTensorProductMap ξ`. -/
theorem reducedBottDoubleSuspensionMap_apply
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w})
    (bottTensorProductMap :
      K(X.toCompactlyGenerated) ⊗[ℤ] K(SphereTwo) →+
        K(X.toCompactlyGenerated × SphereTwo))
    (comparison :
      K̃(X.toCompactlyGenerated × SphereTwo, (X.point, x₂)) ≃+
        K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point))
    (ξ : K̃(X.toCompactlyGenerated, X.point)) :
    reducedBottDoubleSuspensionMap X x₂ bottTensorProductMap comparison ξ =
      comparison (reducedBottProductMap X x₂ bottTensorProductMap ξ) := rfl

/-- If the explicit reduced Bott double-suspension map built from the canonical reduced Hopf
class is bijective, it determines the additive equivalence `K̃(X) ≃+ K̃(Σ²X)` realized by that
map. -/
def reducedBottDoubleSuspensionAddEquiv
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w})
    (bottTensorProductMap :
      K(X.toCompactlyGenerated) ⊗[ℤ] K(SphereTwo) →+
        K(X.toCompactlyGenerated × SphereTwo))
    (comparison :
      K̃(X.toCompactlyGenerated × SphereTwo, (X.point, x₂)) ≃+
        K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point))
    (hcomparison :
      Function.Bijective
        (reducedBottDoubleSuspensionMap X x₂ bottTensorProductMap comparison)) :
    K̃(X.toCompactlyGenerated, X.point) ≃+
      K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point) :=
  AddEquiv.ofBijective
    (reducedBottDoubleSuspensionMap X x₂ bottTensorProductMap comparison)
    hcomparison

/-- The additive equivalence `reducedBottDoubleSuspensionAddEquiv` has underlying homomorphism
equal to the explicit reduced Bott double-suspension map. -/
theorem reducedBottDoubleSuspensionAddEquiv_spec
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w})
    (bottTensorProductMap :
      K(X.toCompactlyGenerated) ⊗[ℤ] K(SphereTwo) →+
        K(X.toCompactlyGenerated × SphereTwo))
    (comparison :
      K̃(X.toCompactlyGenerated × SphereTwo, (X.point, x₂)) ≃+
        K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point))
    (hcomparison :
      Function.Bijective
        (reducedBottDoubleSuspensionMap X x₂ bottTensorProductMap comparison)) :
    (reducedBottDoubleSuspensionAddEquiv
        X x₂ bottTensorProductMap comparison hcomparison).toAddMonoidHom =
      reducedBottDoubleSuspensionMap X x₂ bottTensorProductMap comparison := rfl

/-- Companion API for Theorem 24.2.4: reduced Bott periodicity supplies a Bott external-product
map on `K(X)` together with a comparison `K̃(X × S²) ≃+ K̃(Σ²X)` for which the explicit reduced
Bott double-suspension map is bijective. -/
theorem reducedBottPeriodicity_doubleSuspension_exists_data
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w})
    :
    ∃ bottTensorProductMap :
        K(X.toCompactlyGenerated) ⊗[ℤ] K(SphereTwo) →+
          K(X.toCompactlyGenerated × SphereTwo),
      IsBottTensorProductMap X.toCompactlyGenerated bottTensorProductMap ∧
      ∃ comparison :
          K̃(X.toCompactlyGenerated × SphereTwo, (X.point, x₂)) ≃+
            K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point),
        Function.Bijective
          (reducedBottDoubleSuspensionMap X x₂ bottTensorProductMap comparison) := by
  sorry

/-- Theorem 24.2.4: for the canonical reduced Bott class
`sphereTwoReducedHopfLineClass x₂ ∈ K̃(S², x₂)` and a based compact space `X`, reduced Bott
periodicity yields an additive equivalence `K̃(X) ≃+ K̃(Σ²X)`, together with explicit Bott
external-product and `S²` product-model comparison data realizing its underlying homomorphism as
the reduced Bott double-suspension map; the separate companion theorem
`reducedBottPeriodicity_doubleSuspension_exists_data` records the corresponding bijectivity
statement for that explicit map. -/
theorem reducedBottPeriodicity_doubleSuspension
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w}) :
    ∃ bottEquiv :
        K̃(X.toCompactlyGenerated, X.point) ≃+
          K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point),
      ∃ bottTensorProductMap :
        K(X.toCompactlyGenerated) ⊗[ℤ] K(SphereTwo) →+
          K(X.toCompactlyGenerated × SphereTwo),
      IsBottTensorProductMap X.toCompactlyGenerated bottTensorProductMap ∧
      ∃ comparison :
          K̃(X.toCompactlyGenerated × SphereTwo, (X.point, x₂)) ≃+
            K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point),
        bottEquiv.toAddMonoidHom =
            reducedBottDoubleSuspensionMap X x₂ bottTensorProductMap comparison := by
  rcases reducedBottPeriodicity_doubleSuspension_exists_data X x₂ with
    ⟨bottTensorProductMap, hBott, comparison, hcomparison⟩
  refine ⟨reducedBottDoubleSuspensionAddEquiv X x₂ bottTensorProductMap comparison hcomparison,
    bottTensorProductMap, hBott, comparison, ?_⟩
  exact reducedBottDoubleSuspensionAddEquiv_spec
    X x₂ bottTensorProductMap comparison hcomparison

/-- Theorem 24.2.4 still implies the existential `Nonempty` form of reduced Bott periodicity. -/
theorem reducedBottPeriodicity_doubleSuspension_nonempty
    (X : PointedCompactlyGenerated.{u, w}) [CompactSpace X.toCompactlyGenerated]
    (x₂ : SphereTwo.{w}) :
    Nonempty
      (K̃(X.toCompactlyGenerated, X.point) ≃+
        K̃((Σ (Σ X)).toCompactlyGenerated, (Σ (Σ X)).point)) := by
  rcases reducedBottPeriodicity_doubleSuspension X x₂ with ⟨bottEquiv, -, -, -, -⟩
  exact ⟨bottEquiv⟩
