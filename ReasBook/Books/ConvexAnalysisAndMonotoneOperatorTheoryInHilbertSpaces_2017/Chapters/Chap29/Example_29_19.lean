import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import BauschkeLean.Chap21.Example_21_3

open ContinuousLinearMap
open LinearMap
open WithLp
open scoped ContinuousLinearMap InnerProduct InnerProductSpace

noncomputable section

universe u v w

section

variable {𝕜 : Type w} [RCLike 𝕜]
variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Example 29.19 gives explicit projection formulas for the graph of a bounded
  operator and its orthogonal complement.
- `core/canonical`: the graph owner is `LinearMap.graph`, applied here to `L.toLinearMap`.
- `bridge/view`: `hilbertGraph L` is the thin transport of that owner into the Hilbert carrier
  `WithLp 2 (H × K)` via `WithLp.linearEquiv`, and `hilbertGraph_eq_ker` identifies this
  transported graph with the kernel of `sndL 2 𝕜 H K - L ∘L fstL 2 𝕜 H K`. The source pairs
  `(x, y)` are inserted into the Hilbert carrier by `toLp 2`. -/

section

variable (L : H →L[𝕜] K)

/-- The graph of `L`, viewed in the Hilbert direct sum `WithLp 2 (H × K)`. -/
abbrev hilbertGraph : Submodule 𝕜 (WithLp 2 (H × K)) :=
  (graph L.toLinearMap).map (WithLp.linearEquiv 2 𝕜 (H × K)).symm.toLinearMap

omit [CompleteSpace H] [CompleteSpace K] in
/-- The transported graph `hilbertGraph L` is the kernel of the canonical graph map
`sndL 2 𝕜 H K - L ∘L fstL 2 𝕜 H K`. -/
theorem hilbertGraph_eq_ker :
    hilbertGraph L = (sndL 2 𝕜 H K - L ∘L fstL 2 𝕜 H K).ker := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change w.2 = L w.1 at hw
    change w.2 - L w.1 = 0
    simp [hw]
  · intro hz
    refine ⟨ofLp z, ?_, ?_⟩
    · change z.snd = L z.fst
      change z.snd - L z.fst = 0 at hz
      exact sub_eq_zero.mp hz
    · simp [WithLp.linearEquiv_symm_apply]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 29.19: membership in `hilbertGraph L` is exactly the graph equation
`(ofLp z).snd = L (ofLp z).fst`. -/
@[simp] lemma mem_hilbertGraph_iff {z : WithLp 2 (H × K)} :
    z ∈ hilbertGraph L ↔ (ofLp z).snd = L (ofLp z).fst := by
  rw [hilbertGraph_eq_ker L]
  simp [sub_eq_zero]

/-- Helper for Example 29.19: `1 + L ∘L L†` cancels its inverse on vectors of `K`. -/
lemma one_add_comp_adjoint_inverse_apply (z : K) :
    (1 + (L ∘L L†)) ((1 + (L ∘L L†)).inverse z) = z := by
  have hUnit : IsUnit (1 + (L ∘L L†) : K →L[𝕜] K) := one_add_comp_adjoint_isUnit L
  simpa [← ringInverse_eq_inverse, one_def] using
    congrArg (fun A : K →L[𝕜] K ↦ A z)
      (Ring.mul_inverse_cancel (1 + (L ∘L L†) : K →L[𝕜] K) hUnit)

/-- Helper for Example 29.19: `(1 + L† ∘L L)⁻¹` cancels `1 + L† ∘L L` on vectors of `H`. -/
lemma inverse_one_add_adjoint_comp_apply (z : H) :
    (1 + (L† ∘L L)).inverse ((1 + (L† ∘L L)) z) = z := by
  have hUnit : IsUnit (1 + (L† ∘L L) : H →L[𝕜] H) := one_add_adjoint_comp_isUnit L
  simpa [← ringInverse_eq_inverse, one_def] using
    congrArg (fun A : H →L[𝕜] H ↦ A z)
      (Ring.inverse_mul_cancel (1 + (L† ∘L L) : H →L[𝕜] H) hUnit)

/-- Helper for Example 29.19: the residual vector `(L† u, -u)` is orthogonal to `hilbertGraph L`.
-/
lemma projectionResidual_mem_orthogonal_hilbertGraph (u : K) :
    toLp 2 ((L†) u, -u) ∈ (hilbertGraph L)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro z hz
  rw [mem_hilbertGraph_iff (L := L)] at hz
  -- Expand the product inner product and use the graph relation on the second coordinate.
  calc
    ⟪toLp 2 ((L†) u, -u), z⟫_𝕜
        = ⟪(L†) u, (ofLp z).fst⟫_𝕜 + ⟪-u, (ofLp z).snd⟫_𝕜 := by
            simp [WithLp.prod_inner_apply]
    _ = ⟪u, L ((ofLp z).fst)⟫_𝕜 - ⟪u, (ofLp z).snd⟫_𝕜 := by
          rw [ContinuousLinearMap.adjoint_inner_left]
          simpa [sub_eq_add_neg]
    _ = 0 := by
          rw [hz]
          simp

/-- Helper for Example 29.19: subtraction of `toLp` points is computed coordinatewise. -/
lemma toLp_sub_apply (a b : H × K) :
    toLp 2 a - toLp 2 b = toLp 2 (a - b) := by
  rw [sub_eq_add_neg, ← toLp_neg, ← toLp_add]
  simp [sub_eq_add_neg]

/-- Helper for Example 29.19: the clause-(i) projection candidate lies in `hilbertGraph L`. -/
lemma projectionCandidate_mem_hilbertGraph (x : H) (y : K) :
    toLp 2
      (x - (L†) ((1 + (L ∘L L†)).inverse (L x - y)),
        y + (1 + (L ∘L L†)).inverse (L x - y)) ∈ hilbertGraph L := by
  let u : K := (1 + (L ∘L L†)).inverse (L x - y)
  have hu : (1 + (L ∘L L†)) u = L x - y := by
    simpa [u] using one_add_comp_adjoint_inverse_apply (L := L) (L x - y)
  have hcoord : y + u = L (x - (L†) u) := by
    have hu' : u + (L ∘L L†) u = L x - y := by
      simpa [one_def, ContinuousLinearMap.comp_apply] using hu
    have hLx : L x = y + (u + (L ∘L L†) u) := by
      calc
        L x = y + (L x - y) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = y + (u + (L ∘L L†) u) := by rw [← hu']
    -- Rewrite the graph equation using the inverse-cancellation identity for `u`.
    calc
      y + u = L x - (L ∘L L†) u := by
        rw [hLx]
        simp [sub_eq_add_neg, add_assoc, add_comm]
      _ = L (x - (L†) u) := by
        simp [ContinuousLinearMap.comp_apply]
  rw [mem_hilbertGraph_iff]
  simpa [u] using hcoord

/-- Helper for Example 29.19: the first coordinate in clause (i) equals the inverse form from
clause (ii). -/
lemma sub_adjoint_inverse_comp_adjoint_eq_inverse_adjoint_comp (x : H) (y : K) :
    x - (L†) ((1 + (L ∘L L†)).inverse (L x - y)) =
      (1 + (L† ∘L L)).inverse (x + (L†) y) := by
  let u : K := (1 + (L ∘L L†)).inverse (L x - y)
  let v : H := x - (L†) u
  let A : H →L[𝕜] H := 1 + (L† ∘L L)
  have hgraph : y + u = L v := by
    have hmem := projectionCandidate_mem_hilbertGraph (L := L) x y
    rw [mem_hilbertGraph_iff (L := L)] at hmem
    simpa [u, v] using hmem
  have hAv : A v = x + (L†) y := by
    -- Push the graph equation through `L†` to identify the inverse-image point.
    calc
      A v = v + (L†) (L v) := by
        simp [A, one_def, ContinuousLinearMap.comp_apply]
      _ = (x - (L†) u) + (L†) (y + u) := by
        rw [hgraph]
      _ = x + (L†) y := by
        simp [v, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Apply the inverse of `1 + L† ∘L L` to the established image identity.
  calc
    x - (L†) u = v := by rfl
    _ = A.inverse (A v) := by
          symm
          exact inverse_one_add_adjoint_comp_apply (L := L) v
    _ = A.inverse (x + (L†) y) := by rw [hAv]
    _ = (1 + (L† ∘L L)).inverse (x + (L†) y) := by rfl

/-- The transported graph of a bounded operator in a Hilbert direct sum is orthogonally
complemented. -/
instance hilbertGraph_hasOrthogonalProjection :
    (hilbertGraph L).HasOrthogonalProjection := by
  rw [hilbertGraph_eq_ker L]
  infer_instance

/-- Example 29.19 (1): clause (i). The orthogonal projection onto the graph of `L` is
`(x, y) ↦ (x - L† ((1 + L ∘L L†)⁻¹ (L x - y)), y + (1 + L ∘L L†)⁻¹ (L x - y))`. -/
theorem starProjection_graph_eq_sub_adjoint_inverse_one_add_comp_adjoint (x : H) (y : K) :
    Submodule.starProjection (hilbertGraph L) (toLp 2 (x, y)) =
      toLp 2
        (x - (L†) ((1 + (L ∘L L†)).inverse (L x - y)),
          y + (1 + (L ∘L L†)).inverse (L x - y)) := by
  let u : K := (1 + (L ∘L L†)).inverse (L x - y)
  have hmem : toLp 2 (x - (L†) u, y + u) ∈ hilbertGraph L := by
    simpa [u] using projectionCandidate_mem_hilbertGraph (L := L) x y
  have horth : toLp 2 (x, y) - toLp 2 (x - (L†) u, y + u) ∈ (hilbertGraph L)ᗮ := by
    -- The residual is the canonical orthogonal correction `(L† u, -u)`.
    rw [toLp_sub_apply]
    simpa [sub_eq_add_neg, add_assoc, add_comm] using
      projectionResidual_mem_orthogonal_hilbertGraph (L := L) u
  -- Characterize the projector by membership in the graph and orthogonality of the residual.
  calc
    Submodule.starProjection (hilbertGraph L) (toLp 2 (x, y))
        = toLp 2 (x - (L†) u, y + u) := by
            exact (hilbertGraph L).eq_starProjection_of_mem_orthogonal hmem horth
    _ = toLp 2
          (x - (L†) ((1 + (L ∘L L†)).inverse (L x - y)),
            y + (1 + (L ∘L L†)).inverse (L x - y)) := by
          simp [u]

/-- Example 29.19 (2): clause (ii). The orthogonal projection onto the graph of `L` is also
`(x, y) ↦ ((1 + L† ∘L L)⁻¹ (x + L† y), L ((1 + L† ∘L L)⁻¹ (x + L† y)))`. -/
theorem starProjection_graph_eq_inverse_one_add_adjoint_comp (x : H) (y : K) :
    Submodule.starProjection (hilbertGraph L) (toLp 2 (x, y)) =
      toLp 2
        ((1 + (L† ∘L L)).inverse (x + (L†) y),
          L ((1 + (L† ∘L L)).inverse (x + (L†) y))) := by
  have hproj :=
    starProjection_graph_eq_sub_adjoint_inverse_one_add_comp_adjoint (L := L) x y
  have hfst :=
    sub_adjoint_inverse_comp_adjoint_eq_inverse_adjoint_comp (L := L) x y
  have hsnd :
      y + (1 + (L ∘L L†)).inverse (L x - y) =
        L ((1 + (L† ∘L L)).inverse (x + (L†) y)) := by
    have hmem :
        toLp 2
          (x - (L†) ((1 + (L ∘L L†)).inverse (L x - y)),
            y + (1 + (L ∘L L†)).inverse (L x - y)) ∈ hilbertGraph L := by
      rw [← hproj]
      exact Submodule.starProjection_apply_mem (hilbertGraph L) (toLp 2 (x, y))
    rw [mem_hilbertGraph_iff (L := L)] at hmem
    -- The projection point already lies in the graph, so its second coordinate is `L` of the first.
    calc
      y + (1 + (L ∘L L†)).inverse (L x - y)
          = L (x - (L†) ((1 + (L ∘L L†)).inverse (L x - y))) := hmem
      _ = L ((1 + (L† ∘L L)).inverse (x + (L†) y)) := by rw [hfst]
  calc
    Submodule.starProjection (hilbertGraph L) (toLp 2 (x, y))
        =
          toLp 2
            (x - (L†) ((1 + (L ∘L L†)).inverse (L x - y)),
              y + (1 + (L ∘L L†)).inverse (L x - y)) := hproj
    _ =
        toLp 2
          ((1 + (L† ∘L L)).inverse (x + (L†) y),
            L ((1 + (L† ∘L L)).inverse (x + (L†) y))) := by
          rw [hfst, hsnd]

/-- Example 29.19 (3): clause (iii). The orthogonal projection onto the orthogonal complement of
the graph of `L` is `(x, y) ↦ (L† ((1 + L ∘L L†)⁻¹ (L x - y)),
-((1 + L ∘L L†)⁻¹ (L x - y)))`. -/
theorem starProjection_orthogonal_graph_eq_adjoint_inverse_one_add_comp_adjoint
    (x : H) (y : K) :
    Submodule.starProjection (hilbertGraph L)ᗮ (toLp 2 (x, y)) =
      toLp 2
        ((L†) ((1 + (L ∘L L†)).inverse (L x - y)),
          -((1 + (L ∘L L†)).inverse (L x - y))) := by
  -- Route correction: prove the orthogonal complement formula from `P_{Vᗮ} = Id - P_V`.
  calc
    Submodule.starProjection (hilbertGraph L)ᗮ (toLp 2 (x, y))
        = toLp 2 (x, y) - Submodule.starProjection (hilbertGraph L) (toLp 2 (x, y)) := by
            simpa using (hilbertGraph L).starProjection_orthogonal_val (toLp 2 (x, y))
    _ =
        toLp 2
          ((L†) ((1 + (L ∘L L†)).inverse (L x - y)),
            -((1 + (L ∘L L†)).inverse (L x - y))) := by
          rw [starProjection_graph_eq_sub_adjoint_inverse_one_add_comp_adjoint (L := L) x y]
          rw [toLp_sub_apply]
          simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Example 29.19 (4): clause (iv). The orthogonal projection onto the orthogonal complement of
the graph of `L` is also `(x, y) ↦ (x - (1 + L† ∘L L)⁻¹ (x + L† y), y - L ((1 + L† ∘L L)⁻¹
(x + L† y)))`. -/
theorem starProjection_orthogonal_graph_eq_sub_inverse_one_add_adjoint_comp (x : H) (y : K) :
    Submodule.starProjection (hilbertGraph L)ᗮ (toLp 2 (x, y)) =
      toLp 2
        (x - (1 + (L† ∘L L)).inverse (x + (L†) y),
          y - L ((1 + (L† ∘L L)).inverse (x + (L†) y))) := by
  -- Use clause (ii) inside `P_{Vᗮ} = Id - P_V` to obtain the second explicit formula.
  calc
    Submodule.starProjection (hilbertGraph L)ᗮ (toLp 2 (x, y))
        = toLp 2 (x, y) - Submodule.starProjection (hilbertGraph L) (toLp 2 (x, y)) := by
            simpa using (hilbertGraph L).starProjection_orthogonal_val (toLp 2 (x, y))
    _ =
        toLp 2
          (x - (1 + (L† ∘L L)).inverse (x + (L†) y),
            y - L ((1 + (L† ∘L L)).inverse (x + (L†) y))) := by
          rw [starProjection_graph_eq_inverse_one_add_adjoint_comp (L := L) x y]
          rw [toLp_sub_apply]
          simp [sub_eq_add_neg, add_assoc, add_comm]

end

end
