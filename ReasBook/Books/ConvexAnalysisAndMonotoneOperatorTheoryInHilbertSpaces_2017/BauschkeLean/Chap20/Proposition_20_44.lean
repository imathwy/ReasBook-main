import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Definition_20_42

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

/-
Source/core/bridge triage:
- `source-facing`: Proposition 20.44 records the textbook properties of the partial inverse.
- `core/canonical`: the owner abstractions are `partialInverse`, `partialInverseTransform`,
  `SetValuedOperator.graph`, `SetValuedOperator.IsMonotone`, and `Maximal IsMonotone`.
- `bridge/view`: the proposition transports graph membership, monotonicity, and maximality across
  the involutive graph transform `partialInverseTransform`.
-/

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 20.44: projecting onto `(Vᗮ)ᗮ` agrees with projecting onto `V`. -/
lemma doubleOrthogonalStarProjection_eq
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    (Vᗮᗮ).starProjection = V.starProjection := by
  -- Identify the double-orthogonal projection by reusing the `V ⊕ Vᗮ` decomposition of `x`.
  ext x
  refine (Vᗮᗮ).eq_starProjection_of_mem_orthogonal ?_ ?_
  · exact V.le_orthogonal_orthogonal (V.starProjection_apply_mem x)
  · exact (Vᗮ).le_orthogonal_orthogonal (V.sub_starProjection_mem_orthogonal x)

/-- Helper for Proposition 20.44: applying Spingarn's transform to a graph point of `A` produces
a graph point of `A₍V₎`, and conversely. -/
lemma partialInverseTransform_mem_graph_partialInverse_iff
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] (x u : H) :
    partialInverseTransform V (x, u) ∈ gra (A₍V₎) ↔ (x, u) ∈ gra A := by
  -- Apply the graph characterization to the transformed pair and collapse the involution.
  rw [SetValuedOperator.mem_graph_partialInverse_iff]
  exact Iff.of_eq <|
    congrArg (fun p ↦ p ∈ gra A)
      (SetValuedOperator.partialInverseTransform_involutive (V := V) (x, u))

-- Proof sketch: unfold the partial inverse on `V` and on `Vᗮ`, rewrite graph membership through
-- the same transformed pair, and swap the graph coordinates to identify the result with the
-- inverse graph.
/-- Clause (i) of Proposition 20.44: the partial inverse with respect to `V` is the inverse of
the partial inverse with respect to `Vᗮ`. -/
theorem partialInverse_eq_inverse_partialInverse_orthogonal
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A₍V₎ = A₍Vᗮ₎⁻¹ := by
  -- Rewrite both operator values to the same graph condition and normalize `(Vᗮ)ᗮ`.
  funext x
  ext y
  rw [SetValuedOperator.mem_partialInverse_iff, SetValuedOperator.mem_inverse_iff,
    SetValuedOperator.mem_partialInverse_iff, doubleOrthogonalStarProjection_eq (V := V)]
  simp [add_comm]

-- Proof sketch: rewrite `gra ((A⁻¹)₍Vᗮ₎)` from the definition of the partial inverse and use
-- `SetValuedOperator.mem_inverse_iff` to exchange the graph coordinates of `A`.
/-- Clause (i) of Proposition 20.44: the partial inverse with respect to `V` is also the
partial inverse of the inverse operator with respect to `Vᗮ`. -/
theorem partialInverse_eq_partialInverse_inverse_orthogonal
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A₍V₎ = (A⁻¹)₍Vᗮ₎ := by
  -- Rewrite the right-hand side through the inverse operator and normalize `(Vᗮ)ᗮ`.
  funext x
  ext y
  rw [SetValuedOperator.mem_partialInverse_iff, SetValuedOperator.mem_partialInverse_iff,
    SetValuedOperator.mem_inverse_iff, doubleOrthogonalStarProjection_eq (V := V)]
  simp [add_comm]

/- Clause (ii) of Proposition 20.44: Spingarn's transform is an involution; this is exactly
the owner theorem `partialInverseTransform_involutive` from Definition 20.42. -/
recall partialInverseTransform_involutive

/- Clause (ii) of Proposition 20.44: the graph-image formula for the partial inverse is
exactly the owner theorem `graph_partialInverse_eq` from Definition 20.42. -/
recall graph_partialInverse_eq

-- Proof sketch: use the previous graph-image formula for `A₍V₎` and the
-- involutivity of `partialInverseTransform V` to apply the same transform once more and recover
-- `A.graph`.
/-- Clause (ii) of Proposition 20.44: applying Spingarn's transform to the graph of the partial
inverse recovers the original graph. -/
theorem graph_eq_image_partialInverseTransform_partialInverse
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A.graph = partialInverseTransform V '' (A₍V₎).graph := by
  -- Use the involution to move graph points back and forth across the transform.
  ext p
  constructor
  · intro hp
    refine ⟨partialInverseTransform V p, ?_, ?_⟩
    · exact (partialInverseTransform_mem_graph_partialInverse_iff
        (A := A) (V := V) p.1 p.2).2 hp
    · simpa using (SetValuedOperator.partialInverseTransform_involutive (V := V) p)
  · rintro ⟨q, hq, rfl⟩
    exact (SetValuedOperator.mem_graph_partialInverse_iff
      (A := A) (V := V) q.1 q.2).1 hq

/-- Helper for Proposition 20.44: after expanding the transformed pairing, the mixed `V`/`Vᗮ`
terms vanish by orthogonality. -/
lemma inner_partialInverseTransform_expand_eq
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] (dx du : H) :
    ⟪V.starProjection dx + Vᗮ.starProjection du,
      V.starProjection du + Vᗮ.starProjection dx⟫_ℝ
      = ⟪V.starProjection dx, V.starProjection du⟫_ℝ
        + ⟪Vᗮ.starProjection du, Vᗮ.starProjection dx⟫_ℝ := by
  let a := V.starProjection dx
  let b := Vᗮ.starProjection du
  let c := V.starProjection du
  let d := Vᗮ.starProjection dx
  have hcross₁ :
      ⟪a, d⟫_ℝ = 0 := by
    -- The `V`-component is orthogonal to the `Vᗮ`-component.
    dsimp [a, d]
    exact Submodule.inner_right_of_mem_orthogonal
      (V.starProjection_apply_mem dx) (Vᗮ.starProjection_apply_mem dx)
  have hcross₂ :
      ⟪b, c⟫_ℝ = 0 := by
    -- The mixed term with `du` vanishes for the same orthogonality reason.
    dsimp [b, c]
    exact Submodule.inner_left_of_mem_orthogonal
      (V.starProjection_apply_mem du) (Vᗮ.starProjection_apply_mem du)
  change ⟪a + b, c + d⟫_ℝ = ⟪a, c⟫_ℝ + ⟪b, d⟫_ℝ
  rw [inner_add_left, inner_add_right, inner_add_right]
  rw [hcross₁, hcross₂]
  simp

/-- Helper for Proposition 20.44: the core pairing identity for the `V`/`Vᗮ` decomposition of a
difference pair `(dx, du)`. -/
lemma inner_partialInverseTransform_core_eq
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] (dx du : H) :
    ⟪V.starProjection dx + Vᗮ.starProjection du,
      V.starProjection du + Vᗮ.starProjection dx⟫_ℝ = ⟪dx, du⟫_ℝ := by
  have hprojV :
      ⟪V.starProjection dx, V.starProjection du⟫_ℝ = ⟪dx, V.starProjection du⟫_ℝ := by
    -- Move the `V`-projection from the first argument onto the second one.
    rw [Submodule.inner_starProjection_left_eq_right (K := V)]
    rw [Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem du)]
  have hprojOrth :
      ⟪Vᗮ.starProjection du, Vᗮ.starProjection dx⟫_ℝ = ⟪dx, Vᗮ.starProjection du⟫_ℝ := by
    -- After commuting the orthogonal-complement term, the same self-adjointness identity applies.
    rw [real_inner_comm, Submodule.inner_starProjection_left_eq_right (K := Vᗮ)]
    rw [Submodule.starProjection_eq_self_iff.mpr (Vᗮ.starProjection_apply_mem du)]
  calc
    ⟪V.starProjection dx + Vᗮ.starProjection du,
      V.starProjection du + Vᗮ.starProjection dx⟫_ℝ
        = ⟪V.starProjection dx, V.starProjection du⟫_ℝ
          + ⟪Vᗮ.starProjection du, Vᗮ.starProjection dx⟫_ℝ := by
            exact inner_partialInverseTransform_expand_eq (V := V) dx du
    _ = ⟪dx, V.starProjection du⟫_ℝ + ⟪dx, Vᗮ.starProjection du⟫_ℝ := by
            rw [hprojV, hprojOrth]
    _ = ⟪dx, V.starProjection du + Vᗮ.starProjection du⟫_ℝ := by
            rw [inner_add_right]
    _ = ⟪dx, du⟫_ℝ := by
            rw [V.starProjection_add_starProjection_orthogonal]

/-- Helper for Proposition 20.44: Spingarn's transform sends pair differences to differences of
transformed pairs. -/
lemma partialInverseTransform_sub_eq
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] (p q : H × H) :
    partialInverseTransform V (p - q) =
      partialInverseTransform V p - partialInverseTransform V q := by
  rcases p with ⟨x₁, u₁⟩
  rcases q with ⟨x₂, u₂⟩
  ext
  · -- Normalize the first coordinate using the linearity of both orthogonal projections.
    simp [SetValuedOperator.partialInverseTransform, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
  · -- Normalize the second coordinate in the same pairwise form.
    simp [SetValuedOperator.partialInverseTransform, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]

-- Proof sketch: after normalizing the two transformed coordinate differences to
-- `P_V (x₁ - x₂) + P_{Vᗮ} (u₁ - u₂)` and `P_V (u₁ - u₂) + P_{Vᗮ} (x₁ - x₂)`, apply the core
-- pairing helper above.
/-- Clause (iii) of Proposition 20.44: Spingarn's transform preserves the monotonicity pairing
between differences of graph points. -/
theorem inner_partialInverseTransform_sub_eq
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] (x₁ u₁ x₂ u₂ : H) :
    ⟪(partialInverseTransform V (x₁, u₁)).1 - (partialInverseTransform V (x₂, u₂)).1,
      (partialInverseTransform V (x₁, u₁)).2 - (partialInverseTransform V (x₂, u₂)).2⟫_ℝ =
      ⟪x₁ - x₂, u₁ - u₂⟫_ℝ := by
  -- Route correction: rewrite the whole pair difference once, then reuse the verified core pairing
  -- identity instead of re-normalizing the two coordinates separately.
  calc
    ⟪(partialInverseTransform V (x₁, u₁)).1 - (partialInverseTransform V (x₂, u₂)).1,
      (partialInverseTransform V (x₁, u₁)).2 - (partialInverseTransform V (x₂, u₂)).2⟫_ℝ
        = ⟪(partialInverseTransform V ((x₁, u₁) - (x₂, u₂))).1,
            (partialInverseTransform V ((x₁, u₁) - (x₂, u₂))).2⟫_ℝ := by
            rw [partialInverseTransform_sub_eq]
            rfl
    _ = ⟪x₁ - x₂, u₁ - u₂⟫_ℝ := by
            simpa [partialInverseTransform_fst, partialInverseTransform_snd, Prod.fst_sub,
              Prod.snd_sub] using
              (inner_partialInverseTransform_core_eq (V := V) (dx := x₁ - x₂) (du := u₁ - u₂))

-- Proof sketch: translate graph points of `A` to graph points of `A₍V₎` via the
-- graph-image formula, then apply the pairing-preservation identity from the previous clause in
-- both directions.
/-- Clause (iv) of Proposition 20.44: the partial inverse is monotone exactly when the original
operator is monotone. -/
theorem partialInverse_isMonotone_iff
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A₍V₎.IsMonotone ↔ A.IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff, SetValuedOperator.isMonotone_iff]
  constructor
  · intro hAV x u y v hxu hyv
    -- Transport the two original graph points into `gra (A₍V₎)` through Spingarn's transform.
    have hxu_graph : (x, u) ∈ gra A := by
      rw [SetValuedOperator.mem_graph]
      exact hxu
    have hyv_graph : (y, v) ∈ gra A := by
      rw [SetValuedOperator.mem_graph]
      exact hyv
    have hxuAV_graph : partialInverseTransform V (x, u) ∈ gra (A₍V₎) := by
      exact (partialInverseTransform_mem_graph_partialInverse_iff
        (A := A) (V := V) x u).2 hxu_graph
    have hyvAV_graph : partialInverseTransform V (y, v) ∈ gra (A₍V₎) := by
      exact (partialInverseTransform_mem_graph_partialInverse_iff
        (A := A) (V := V) y v).2 hyv_graph
    have hxuAV :
        (partialInverseTransform V (x, u)).2 ∈ A₍V₎ ((partialInverseTransform V (x, u)).1) := by
      rw [← SetValuedOperator.mem_graph]
      exact hxuAV_graph
    have hyvAV :
        (partialInverseTransform V (y, v)).2 ∈ A₍V₎ ((partialInverseTransform V (y, v)).1) := by
      rw [← SetValuedOperator.mem_graph]
      exact hyvAV_graph
    -- Apply monotonicity to the transformed graph points and rewrite the pairing back.
    have htrans :
        0 ≤ ⟪(partialInverseTransform V (x, u)).1 - (partialInverseTransform V (y, v)).1,
          (partialInverseTransform V (x, u)).2 - (partialInverseTransform V (y, v)).2⟫_ℝ :=
      hAV hxuAV hyvAV
    rw [← inner_partialInverseTransform_sub_eq (V := V) x u y v]
    exact htrans
  · intro hA x u y v hxu hyv
    -- Move the partial-inverse graph points back to `gra A`.
    have hxu_graph : (x, u) ∈ gra (A₍V₎) := by
      rw [SetValuedOperator.mem_graph]
      exact hxu
    have hyv_graph : (y, v) ∈ gra (A₍V₎) := by
      rw [SetValuedOperator.mem_graph]
      exact hyv
    have hxuA_graph : partialInverseTransform V (x, u) ∈ gra A := by
      exact (SetValuedOperator.mem_graph_partialInverse_iff
        (A := A) (V := V) x u).1 hxu_graph
    have hyvA_graph : partialInverseTransform V (y, v) ∈ gra A := by
      exact (SetValuedOperator.mem_graph_partialInverse_iff
        (A := A) (V := V) y v).1 hyv_graph
    have hxuA :
        (partialInverseTransform V (x, u)).2 ∈ A ((partialInverseTransform V (x, u)).1) := by
      rw [← SetValuedOperator.mem_graph]
      exact hxuA_graph
    have hyvA :
        (partialInverseTransform V (y, v)).2 ∈ A ((partialInverseTransform V (y, v)).1) := by
      rw [← SetValuedOperator.mem_graph]
      exact hyvA_graph
    -- Monotonicity on `A` becomes monotonicity on `A₍V₎` after the same pairing rewrite.
    have htrans :
        0 ≤ ⟪(partialInverseTransform V (x, u)).1 - (partialInverseTransform V (y, v)).1,
          (partialInverseTransform V (x, u)).2 - (partialInverseTransform V (y, v)).2⟫_ℝ :=
      hA hxuA hyvA
    rw [← inner_partialInverseTransform_sub_eq (V := V) x u y v]
    exact htrans

-- Proof sketch: combine the involutive graph transform with the characterization of maximal
-- monotonicity as maximality among monotone graph extensions, so graph inclusion is transported
-- back and forth by the involution.
/-- Helper for Proposition 20.44: inclusion is preserved and reflected by taking the partial
inverse on both sides. -/
lemma partialInverse_le_partialInverse_iff
    (A B : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A₍V₎ ≤ B₍V₎ ↔ A ≤ B := by
  constructor
  · intro hAB x u hu
    -- Move the original graph point into the partial inverse, use the inclusion there, and move
    -- back through the involutive graph transform.
    have huA_graph : (x, u) ∈ gra A := by
      rw [SetValuedOperator.mem_graph]
      exact hu
    have huApartial_graph : partialInverseTransform V (x, u) ∈ gra (A₍V₎) := by
      exact (partialInverseTransform_mem_graph_partialInverse_iff
        (A := A) (V := V) x u).2 huA_graph
    have huApartial :
        (partialInverseTransform V (x, u)).2 ∈
          A₍V₎ ((partialInverseTransform V (x, u)).1) := by
      rw [← SetValuedOperator.mem_graph]
      exact huApartial_graph
    have huBpartial :
        (partialInverseTransform V (x, u)).2 ∈
          B₍V₎ ((partialInverseTransform V (x, u)).1) := hAB _ huApartial
    have huBpartial_graph : partialInverseTransform V (x, u) ∈ gra (B₍V₎) := by
      rw [SetValuedOperator.mem_graph]
      exact huBpartial
    have huB_graph : (x, u) ∈ gra B := by
      exact (partialInverseTransform_mem_graph_partialInverse_iff
        (A := B) (V := V) x u).1 huBpartial_graph
    rw [SetValuedOperator.mem_graph] at huB_graph
    exact huB_graph
  · intro hAB x u hu
    -- Rewrite a graph point of `A₍V₎` as a transformed graph point of `A`, apply the inclusion,
    -- and then rewrite back to a graph point of `B₍V₎`.
    have huApartial_graph : (x, u) ∈ gra (A₍V₎) := by
      rw [SetValuedOperator.mem_graph]
      exact hu
    have huA_graph : partialInverseTransform V (x, u) ∈ gra A := by
      exact (SetValuedOperator.mem_graph_partialInverse_iff
        (A := A) (V := V) x u).1 huApartial_graph
    have huA :
        (partialInverseTransform V (x, u)).2 ∈
          B ((partialInverseTransform V (x, u)).1) := by
      -- The transformed pair is now a graph point of `B`.
      exact hAB _ <| by
        rw [← SetValuedOperator.mem_graph]
        exact huA_graph
    have huB_graph : partialInverseTransform V (x, u) ∈ gra B := by
      rw [← SetValuedOperator.mem_graph]
      exact huA
    have huBpartial_graph : (x, u) ∈ gra (B₍V₎) := by
      exact (SetValuedOperator.mem_graph_partialInverse_iff
        (A := B) (V := V) x u).2 huB_graph
    rw [SetValuedOperator.mem_graph] at huBpartial_graph
    exact huBpartial_graph

/-- Helper for Proposition 20.44: inclusion from a partial inverse into another operator is
equivalent to inclusion from the original operator into the other partial inverse. -/
lemma partialInverse_le_iff
    (A B : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A₍V₎ ≤ B ↔ A ≤ B₍V₎ := by
  constructor
  · intro hAB x u hu
    -- Transport the original graph point into `gra (A₍V₎)`, apply the assumed inclusion, and
    -- rewrite the resulting transformed graph point into `gra (B₍V₎)`.
    have huA_graph : (x, u) ∈ gra A := by
      rw [SetValuedOperator.mem_graph]
      exact hu
    have huApartial_graph : partialInverseTransform V (x, u) ∈ gra (A₍V₎) := by
      exact (partialInverseTransform_mem_graph_partialInverse_iff
        (A := A) (V := V) x u).2 huA_graph
    have huApartial :
        (partialInverseTransform V (x, u)).2 ∈
          A₍V₎ ((partialInverseTransform V (x, u)).1) := by
      rw [← SetValuedOperator.mem_graph]
      exact huApartial_graph
    have huB :
        (partialInverseTransform V (x, u)).2 ∈
          B ((partialInverseTransform V (x, u)).1) := hAB _ huApartial
    have huB_graph : partialInverseTransform V (x, u) ∈ gra B := by
      rw [← SetValuedOperator.mem_graph]
      exact huB
    have huBpartial_graph : (x, u) ∈ gra (B₍V₎) := by
      exact (SetValuedOperator.mem_graph_partialInverse_iff
        (A := B) (V := V) x u).2 huB_graph
    rw [SetValuedOperator.mem_graph] at huBpartial_graph
    exact huBpartial_graph
  · intro hAB x u hu
    -- Move the partial-inverse graph point back to `gra A`, use the inclusion into `B₍V₎`, and
    -- then undo the transform to recover a graph point of `B`.
    have huApartial_graph : (x, u) ∈ gra (A₍V₎) := by
      rw [SetValuedOperator.mem_graph]
      exact hu
    have huA_graph : partialInverseTransform V (x, u) ∈ gra A := by
      exact (SetValuedOperator.mem_graph_partialInverse_iff
        (A := A) (V := V) x u).1 huApartial_graph
    have huA :
        (partialInverseTransform V (x, u)).2 ∈
          A ((partialInverseTransform V (x, u)).1) := by
      rw [← SetValuedOperator.mem_graph]
      exact huA_graph
    have huBpartial :
        (partialInverseTransform V (x, u)).2 ∈
          B₍V₎ ((partialInverseTransform V (x, u)).1) := hAB _ huA
    have huBpartial_graph : partialInverseTransform V (x, u) ∈ gra (B₍V₎) := by
      rw [SetValuedOperator.mem_graph]
      exact huBpartial
    have huB_graph : (x, u) ∈ gra B := by
      exact (partialInverseTransform_mem_graph_partialInverse_iff
        (A := B) (V := V) x u).1 huBpartial_graph
    rw [SetValuedOperator.mem_graph] at huB_graph
    exact huB_graph

/-- Proposition 20.44 (8): clause (v). The partial inverse is maximally monotone exactly when the
original operator is maximally monotone. -/
theorem partialInverse_isMaximallyMonotone_iff
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    Maximal IsMonotone A₍V₎ ↔ Maximal IsMonotone A := by
  constructor
  · intro hAV
    constructor
    · -- Reuse the monotonicity transport already established in clause (iv).
      exact (partialInverse_isMonotone_iff (A := A) (V := V)).1 hAV.1
    · intro B hB hAB x u huB
      -- Route correction: apply maximality after transporting the extension relation once, rather
      -- than rebuilding transformed graph points locally for this direction.
      have hBpartial : B₍V₎.IsMonotone :=
        (partialInverse_isMonotone_iff (A := B) (V := V)).2 hB
      have hABpartial : A₍V₎ ≤ B₍V₎ :=
        (partialInverse_le_partialInverse_iff (A := A) (B := B) (V := V)).2 hAB
      have hBApartial : B₍V₎ ≤ A₍V₎ := hAV.2 hBpartial hABpartial
      have hBA : B ≤ A :=
        (partialInverse_le_partialInverse_iff (A := B) (B := A) (V := V)).1 hBApartial
      exact hBA x huB
  · intro hA
    constructor
    · exact (partialInverse_isMonotone_iff (A := A) (V := V)).2 hA.1
    · intro B hB hAB x u huB
      -- Transport this extension across the partial inverse once, apply maximality of `A`, and
      -- then transport the conclusion back.
      have hBpartial : B₍V₎.IsMonotone :=
        (partialInverse_isMonotone_iff (A := B) (V := V)).2 hB
      have hABpartial : A ≤ B₍V₎ :=
        (partialInverse_le_iff (A := A) (B := B) (V := V)).1 hAB
      have hBpartialA : B₍V₎ ≤ A := hA.2 hBpartial hABpartial
      have hBApartial : B ≤ A₍V₎ :=
        (partialInverse_le_iff (A := B) (B := A) (V := V)).1 hBpartialA
      exact hBApartial x huB

-- Proof sketch: unfold `SetValuedOperator.zeros`, rewrite `0 ∈ A₍V₎ x` as `(x, 0) ∈ (A₍V₎).graph`,
-- use the graph-image description, and compute `partialInverseTransform V (x, 0)`.
/-- Clause (vi) of Proposition 20.44: a point is a zero of the partial inverse exactly when its
`V`- and `Vᗮ`-projections form a graph point of the original operator. -/
theorem mem_zeros_partialInverse_iff_projection_mem_graph
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] (x : H) :
    x ∈ A₍V₎.zeros ↔ (V.starProjection x, Vᗮ.starProjection x) ∈ A.graph := by
  -- Unfold zeros and evaluate the defining relation of the partial inverse at `0`.
  rw [SetValuedOperator.mem_zeros_iff, SetValuedOperator.mem_partialInverse_iff,
    SetValuedOperator.mem_graph]
  simp

end SetValuedOperator
