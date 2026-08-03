import Mathlib
import BauschkeLean.Chap01.Text_1_0_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: `partialInverse A V`, with notation `A₍V₎`, is the textbook partial inverse.
- `core/canonical`: the reusable owner abstraction is the graph `gra A` of a set-valued operator.
- `bridge/view`: `partialInverseTransform V` is the involutive graph transform transporting
  `gra A` to `gra A₍V₎`.
- primitive data: the operator `A` and the orthogonal-projection API on `V`.
- derived API: pointwise membership, graph membership, involutivity, and graph-image lemmas. -/

/-- The Spingarn graph transform associated with a subspace `V`, obtained by exchanging the
`V`- and `Vᗮ`-components of a pair `(x, u)`. -/
def partialInverseTransform (V : Submodule ℝ H) [V.HasOrthogonalProjection] : H × H → H × H :=
  fun xu ↦
    (V.starProjection xu.1 + Vᗮ.starProjection xu.2,
      V.starProjection xu.2 + Vᗮ.starProjection xu.1)

/-- The first coordinate of Spingarn's transform keeps the `V`-component of `x` and the
`Vᗮ`-component of `u`. -/
@[simp] theorem partialInverseTransform_fst (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (x u : H) :
    (partialInverseTransform V (x, u)).1 = V.starProjection x + Vᗮ.starProjection u :=
  rfl

/-- The second coordinate of Spingarn's transform keeps the `V`-component of `u` and the
`Vᗮ`-component of `x`. -/
@[simp] theorem partialInverseTransform_snd (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (x u : H) :
    (partialInverseTransform V (x, u)).2 = V.starProjection u + Vᗮ.starProjection x :=
  rfl

/-- The partial inverse from Definition 20.42 for a set-valued operator `A` and a closed linear
subspace `V`, represented in the projection API by the primitive assumption
`[V.HasOrthogonalProjection]`, is the operator whose graph is obtained from `gra A` by
Spingarn's graph transform. The source-facing Lean notation for the textbook partial inverse `A_V`
is `A₍V₎`. -/
def partialInverse (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    SetValuedOperator H H :=
  fun x ↦ { y | partialInverseTransform V (x, y) ∈ gra A }

/- Lean cannot parse an arbitrary term as a literal subscript, so we use the parenthesized
subscript-style surface `A₍V₎` as the direct notation for the textbook partial inverse `A_V`. -/
scoped notation:max A:max "₍" V:max "₎" => SetValuedOperator.partialInverse A V

open scoped SetValuedOperator

-- Proof sketch: unfold `SetValuedOperator.partialInverse`, `partialInverseTransform`, and
-- `SetValuedOperator.graph`; evaluating the operator at `x` returns exactly the swapped
-- projection relation in `A`.
/-- Applying the partial inverse at `x` returns the set of `y` satisfying the swapped projection
relation in `A`. -/
@[simp] theorem partialInverse_apply (A : SetValuedOperator H H) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (x : H) :
    A₍V₎ x =
      { y |
          V.starProjection y + Vᗮ.starProjection x ∈
            A (V.starProjection x + Vᗮ.starProjection y) } :=
  rfl

-- Proof sketch: membership in the partial inverse is definitionally the graph-membership
-- condition for the transformed pair `partialInverseTransform V (x, y)`.
/-- Membership in the partial inverse is equivalent to the defining swapped projection relation in
`A`. -/
@[simp] theorem mem_partialInverse_iff (A : SetValuedOperator H H) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (x y : H) :
    y ∈ A₍V₎ x ↔
      V.starProjection y + Vᗮ.starProjection x ∈
        A (V.starProjection x + Vᗮ.starProjection y) :=
  Iff.rfl

-- Proof sketch: unfold `SetValuedOperator.graph`, `SetValuedOperator.partialInverse`, and
-- `partialInverseTransform`; graph membership for `A₍V₎` is exactly graph
-- membership for the transformed pair in `A`.
/- A pair `(x, y)` lies in the graph of `A₍V₎` exactly when its Spingarn transform
lies in the graph of `A`. -/
@[simp] theorem mem_graph_partialInverse_iff (A : SetValuedOperator H H) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (x y : H) :
    (x, y) ∈ gra (A₍V₎) ↔ partialInverseTransform V (x, y) ∈ gra A :=
  Iff.rfl

-- Proof sketch: apply the projection identities `P_V + P_{Vᗮ} = Id` and `P_V P_{Vᗮ} = 0` in
-- both coordinates to compute `L (L (x, u)) = (x, u)`.
/-- Helper for Definition 20.42: applying Spingarn's graph transform twice recovers the original
pair. -/
theorem partialInverseTransform_apply_apply
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] (xu : H × H) :
    partialInverseTransform V (partialInverseTransform V xu) = xu := by
  rcases xu with ⟨x, u⟩
  have project_project (z : H) : V.starProjection (V.starProjection z) = V.starProjection z := by
    simpa [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun
        (Submodule.starProjection_comp_starProjection_of_le (U := V) (V := V) le_rfl) z
  have project_orthogonal (z : H) : V.starProjection (Vᗮ.starProjection z) = 0 := by
    simpa [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun
        ((Submodule.isOrtho_orthogonal_right V).starProjection_comp_starProjection
          (U := V) (V := Vᗮ)) z
  have orthogonal_project (z : H) : Vᗮ.starProjection (V.starProjection z) = 0 := by
    simpa [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun
        ((Submodule.isOrtho_orthogonal_left V).starProjection_comp_starProjection
          (U := Vᗮ) (V := V)) z
  have orthogonal_orthogonal (z : H) :
      Vᗮ.starProjection (Vᗮ.starProjection z) = Vᗮ.starProjection z := by
    simpa [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun
        (Submodule.starProjection_comp_starProjection_of_le (U := Vᗮ) (V := Vᗮ) le_rfl) z
  -- Compute each coordinate of the double transform and collapse the projection terms.
  ext <;>
    simp [partialInverseTransform, ContinuousLinearMap.map_add, project_project,
      orthogonal_project, add_comm]

/-- Spingarn's graph transform is an involution. -/
theorem partialInverseTransform_involutive
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    Function.Involutive (partialInverseTransform V) := by
  -- Reduce involutivity to the pairwise double-transform computation.
  intro xu
  simpa using partialInverseTransform_apply_apply (V := V) xu

-- Proof sketch: unfold `SetValuedOperator.partialInverse` and `SetValuedOperator.graph`; graph
-- membership in the partial inverse is transported by `partialInverseTransform V`, and the
-- involutivity of that transform turns the preimage description into an image description.
/-- Definition 20.42: the graph of the partial inverse is the image of `gra A` under Spingarn's
graph transform. -/
theorem graph_partialInverse_eq (A : SetValuedOperator H H) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] :
    gra (A₍V₎) = partialInverseTransform V '' gra A := by
  ext xu
  rcases xu with ⟨x, y⟩
  constructor
  · intro hxy
    -- Use the transformed pair as the image witness coming from `gra A`.
    refine ⟨partialInverseTransform V (x, y), ?_, ?_⟩
    · simpa using (mem_graph_partialInverse_iff (A := A) (V := V) x y).mp hxy
    · simpa using partialInverseTransform_apply_apply (V := V) (x, y)
  · rintro ⟨uv, huv, huv_eq⟩
    rcases uv with ⟨u, v⟩
    -- Transport graph membership back across the involution.
    cases huv_eq
    have huv' : partialInverseTransform V (partialInverseTransform V (u, v)) ∈ gra A := by
      simpa [partialInverseTransform_apply_apply (V := V) (u, v)] using huv
    exact
      (mem_graph_partialInverse_iff
        (A := A) (V := V)
        (partialInverseTransform V (u, v)).1
        (partialInverseTransform V (u, v)).2).2 huv'

end

end SetValuedOperator
