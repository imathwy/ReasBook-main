import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_3_3.GradedRing

open CategoryTheory
open CategoryTheory.Limits
open GrpCat.FilteredColimits
open MonCat.FilteredColimits
open scoped Topology unitInterval Topology.Homotopy

noncomputable section

universe u w

/-- The source phrase "associative ring prespectrum" is modeled in this file by a ring
prespectrum together with the missing compatibility premise saying that the space-level products
`toRingPrespectrum.mul m n` fit the successor maps in the stable-homotopy tail diagrams. This is
the extra source-faithful hypothesis needed before the induced multiplication on `π_*(T)` can
descend from the prespectrum level. -/
structure AssociativeRingPrespectrum where
  toRingPrespectrum : RingPrespectrum.{u, w}
  stableHomotopyMulCompatible :
    toRingPrespectrum.StableHomotopyMulCompatible

namespace AssociativeRingPrespectrum

/-- The underlying prespectrum of an associative ring prespectrum. -/
abbrev toPrespectrum (T : AssociativeRingPrespectrum.{u, w}) : Prespectrum.{u} :=
  T.toRingPrespectrum.toPrespectrum

/-- The stable-homotopy tail-diagram compatibility premise carried by an associative ring
prespectrum is exactly the Chapter 25 source-faithful missing hypothesis on the space-level
multiplication maps `T.mul`. -/
theorem stableHomotopyMulCompatible_spec (T : AssociativeRingPrespectrum.{u, w}) :
    T.toRingPrespectrum.StableHomotopyMulCompatible :=
  T.stableHomotopyMulCompatible

end AssociativeRingPrespectrum

/-- Helper for Lemma 25.3.3: choose one compatible stagewise multiplication system in degrees
`i` and `j` from the source compatibility hypothesis. -/
private noncomputable def chosenStageMulSystem
    (T : RingPrespectrum.{u, w}) (hcompat : T.StableHomotopyMulCompatible) (i j : ℤ) :
    StableHomotopyStageMulSystem T i j :=
  Classical.choose (hcompat i j)

/-- Helper for Lemma 25.3.3: the chosen stagewise multiplication system still comes with the
source-induced witness at every stage. -/
private theorem chosenStageMulSystem_spec
    (T : RingPrespectrum.{u, w}) (hcompat : T.StableHomotopyMulCompatible) (i j : ℤ) (k : ℕ) :
    Nonempty
      (IsSourceInducedStableHomotopyStageMul T i j k
        ((chosenStageMulSystem T hcompat i j).sourceStageMul k)) :=
  Classical.choose_spec (hcompat i j) k

/-- Helper for Lemma 25.3.3: fix the source-induced witness attached to the chosen stagewise
product at stage `k`. -/
private noncomputable def chosenStageMulStageWitness
    (T : RingPrespectrum.{u, w}) (hcompat : T.StableHomotopyMulCompatible) (i j : ℤ) (k : ℕ) :
    IsSourceInducedStableHomotopyStageMul T i j k
      ((chosenStageMulSystem T hcompat i j).sourceStageMul k) :=
  Classical.choice (chosenStageMulSystem_spec T hcompat i j k)

/-- Helper for Lemma 25.3.3: the chosen stagewise product is multiplicative in its left input. -/
private theorem chosenStageMul_mul_left
    (T : RingPrespectrum.{u, w}) (hcompat : T.StableHomotopyMulCompatible) (i j : ℤ) (k : ℕ)
    (x₁ x₂ : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj k)
    (y : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj k) :
    (chosenStageMulSystem T hcompat i j).sourceStageMul k (x₁ * x₂) y =
      (chosenStageMulSystem T hcompat i j).sourceStageMul k x₁ y *
        (chosenStageMulSystem T hcompat i j).sourceStageMul k x₂ y := by
  let witness := chosenStageMulStageWitness T hcompat i j k
  -- Use the chosen left multiplication homomorphism instead of unfolding the stage product.
  calc
    (chosenStageMulSystem T hcompat i j).sourceStageMul k (x₁ * x₂) y =
        witness.leftMul y (x₁ * x₂) := by
          symm
          exact witness.leftMul_spec (x₁ * x₂) y
    _ = witness.leftMul y x₁ * witness.leftMul y x₂ := by
          exact (witness.leftMul y).map_mul x₁ x₂
    _ =
        (chosenStageMulSystem T hcompat i j).sourceStageMul k x₁ y *
          (chosenStageMulSystem T hcompat i j).sourceStageMul k x₂ y := by
          rw [witness.leftMul_spec, witness.leftMul_spec]

/-- Helper for Lemma 25.3.3: the chosen stagewise product is multiplicative in its right input.
-/
private theorem chosenStageMul_mul_right
    (T : RingPrespectrum.{u, w}) (hcompat : T.StableHomotopyMulCompatible) (i j : ℤ) (k : ℕ)
    (x : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj k)
    (y₁ y₂ : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj k) :
    (chosenStageMulSystem T hcompat i j).sourceStageMul k x (y₁ * y₂) =
      (chosenStageMulSystem T hcompat i j).sourceStageMul k x y₁ *
        (chosenStageMulSystem T hcompat i j).sourceStageMul k x y₂ := by
  let witness := chosenStageMulStageWitness T hcompat i j k
  -- The right multiplication homomorphism gives the stagewise bilinearity in the second factor.
  calc
    (chosenStageMulSystem T hcompat i j).sourceStageMul k x (y₁ * y₂) =
        witness.rightMul x (y₁ * y₂) := by
          symm
          exact witness.rightMul_spec x (y₁ * y₂)
    _ = witness.rightMul x y₁ * witness.rightMul x y₂ := by
          exact (witness.rightMul x).map_mul y₁ y₂
    _ =
        (chosenStageMulSystem T hcompat i j).sourceStageMul k x y₁ *
          (chosenStageMulSystem T hcompat i j).sourceStageMul k x y₂ := by
          rw [witness.rightMul_spec, witness.rightMul_spec]

/-- Helper for Lemma 25.3.3: advancing the common tail stage by one advances the target stage by
two successor steps. -/
private theorem stableHomotopyMulTargetIndex_succ_local
    (i j : ℤ) (k : ℕ) :
    stableHomotopyMulTargetIndex i j (k + 1) = stableHomotopyMulTargetIndex i j k + 2 := by
  -- TODO: normalize the `Nat` subtraction in `stableHomotopyMulTargetIndex` to a fixed base
  -- stage and finish with the same tail-start inequality used in `GradedRing.lean`.
  sorry

/-- Helper for Lemma 25.3.3: the repaired target-stage index grows monotonically with the common
tail stage. -/
private theorem stableHomotopyMulTargetIndex_mono
    (i j : ℤ) {a b : ℕ} (hab : a ≤ b) :
    stableHomotopyMulTargetIndex i j a ≤ stableHomotopyMulTargetIndex i j b := by
  -- TODO: iterate `stableHomotopyMulTargetIndex_succ_local` along `Nat.exists_eq_add_of_le hab`
  -- to obtain the forward output-stage map used by the colimit descent.
  sorry

/-- Helper for Lemma 25.3.3: the chosen stagewise product commutes with arbitrary forward maps in
the stable-homotopy tail diagrams. -/
private theorem chosenStageMulSystem_map_homOfLE
    (T : RingPrespectrum.{u, w}) (hcompat : T.StableHomotopyMulCompatible) (i j : ℤ)
    {a b : ℕ} (hab : a ≤ b)
    (x : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).obj a)
    (y : (Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).obj a) :
    let system := chosenStageMulSystem T hcompat i j
    system.sourceStageMul b
        (((Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum i).map
            (homOfLE hab)).hom x)
        (((Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum j).map
            (homOfLE hab)).hom y) =
      (((Prespectrum.stableHomotopyGroupTailDiagram T.toPrespectrum (i + j)).map
          (homOfLE (stableHomotopyMulTargetIndex_mono i j hab))).hom
        (system.sourceStageMul a x y)) := by
  -- TODO: induct on the gap `b - a`, use `system.succ_compat` for the successor step, and
  -- identify the long tail maps by `Functor.map_comp`/`CategoryTheory.homOfLE_comp`.
  sorry

/-- Helper for Lemma 25.3.3: a ring prespectrum whose source multiplication is compatible with the
stable-homotopy tail diagrams induces a graded ring structure on `π_*(T)`. -/
private theorem stableHomotopyGradedRingOfCompatible
    (T : RingPrespectrum.{u, w}) (hcompat : T.StableHomotopyMulCompatible) :
    Nonempty (StableHomotopyGradedRing T) := by
  -- Route correction: the imported support file exposes the stagewise source-faithful product
  -- systems and their bilinearity witnesses, but not a public two-variable filtered-colimit
  -- descent constructor. The proof has been reduced to that single descent step.
  -- TODO: first prove `chosenStageMulSystem_map_homOfLE`, then define the quotient-level product
  -- on `π_*(T)` by choosing common-stage representatives and rewriting it with one common-stage
  -- normalization lemma. After that, `mul_descends` and bilinearity are routine; the remaining
  -- blocker is the missing source-induced associativity/unit transport from `T.mul`.
  sorry

/-- Helper for Lemma 25.3.3: if the source multiplication is compatible with the stable-homotopy
tail diagrams and commutative up to `smashProductSwap`, then the induced graded ring on `π_*(T)`
is graded-commutative. -/
private theorem stableHomotopyGradedRingIsGradedCommutativeOfStagewiseComm
    (T : RingPrespectrum.{u, w}) (hcompat : T.StableHomotopyMulCompatible)
    (hcomm :
      ∀ m n : ℕ,
        basedHomotopyRel
          (smashProductSwap
              (T.toPrespectrum.basedSpace m)
              (T.toPrespectrum.basedSpace n) ≫
            T.mul n m ≫
              Prespectrum.basedSpaceCast
                T.toPrespectrum
                (Nat.add_comm n m))
          (T.mul m n)) :
    ∃ R : StableHomotopyGradedRing T, R.IsGradedCommutative := by
  obtain ⟨R⟩ := stableHomotopyGradedRingOfCompatible T hcompat
  refine ⟨R, ?_⟩
  -- Route correction: once the filtered-colimit product is constructed, the remaining proof is a
  -- representative-level comparison between the source swap homotopies and the Koszul sign rule.
  -- TODO: rewrite both products by the future common-stage descent formula, compare the source
  -- representatives using `hcomm`, and use `Prespectrum.stableHomotopyGroup_mul_comm` only in the
  -- odd-parity branch after both sides live in the same target degree.
  sorry

/-- Lemma 25.3.3::statement_repair::1

Lemma 25.3.3. If `T` is an associative ring prespectrum, then `π_*(T)`
carries an induced graded-ring structure. Here `AssociativeRingPrespectrum` is the source-facing
owner for an associative ring prespectrum, and the graded family `π_*(T)` is formalized as
`n ↦ Prespectrum.stableHomotopyGroup T.toPrespectrum n`. The main statement is recorded by the
existence theorem `existsStableHomotopyGradedRing`, while the commutative clause of the source is
recorded by `stableHomotopyGradedRing_isGradedCommutative`. -/
theorem existsStableHomotopyGradedRing
    (T : AssociativeRingPrespectrum.{u, w}) :
    Nonempty (StableHomotopyGradedRing T.toRingPrespectrum) := by
  -- Reduce the public existence statement to the source-faithful compatibility-to-graded-ring
  -- construction on the underlying ring prespectrum.
  exact
    stableHomotopyGradedRingOfCompatible
      T.toRingPrespectrum
      T.stableHomotopyMulCompatible_spec

/-- Lemma 25.3.3 (2). If the multiplication of a ring prespectrum `T` is commutative up to the
smash-product
symmetry `smashProductSwap`, then the induced graded ring on `π_*(T)` is graded-commutative. The
displayed commutativity hypothesis is the source-faithful condition on the space-level products
`T.toRingPrespectrum.mul m n : T m ∧ T n ⟶ T (m + n)`. -/
theorem stableHomotopyGradedRing_isGradedCommutative
    (T : AssociativeRingPrespectrum.{u, w})
    (hcomm :
      ∀ m n : ℕ,
        basedHomotopyRel
          (smashProductSwap
              (T.toPrespectrum.basedSpace m)
              (T.toPrespectrum.basedSpace n) ≫
            T.toRingPrespectrum.mul n m ≫
              Prespectrum.basedSpaceCast
                T.toPrespectrum
                (Nat.add_comm n m))
          (T.toRingPrespectrum.mul m n)) :
    ∃ R : StableHomotopyGradedRing T.toRingPrespectrum, R.IsGradedCommutative := by
  -- Reduce the commutative clause to the support-level comparison between the source commutativity
  -- homotopies and the graded-commutative Koszul sign rule on `π_*(T)`.
  exact
    stableHomotopyGradedRingIsGradedCommutativeOfStagewiseComm
      T.toRingPrespectrum
      T.stableHomotopyMulCompatible_spec
      hcomm
