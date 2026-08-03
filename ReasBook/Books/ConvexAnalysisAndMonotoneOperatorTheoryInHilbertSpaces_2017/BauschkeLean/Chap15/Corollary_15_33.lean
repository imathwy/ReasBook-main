import Mathlib
import BauschkeLean.Chap07.Example_7_15
import BauschkeLean.Chap15.Corollary_15_31

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProductSpace Pointwise

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
private theorem submodule_image_eq_map (L : H →L[ℝ] K) (C : Submodule ℝ H) :
    L '' (C : Set H) = ((C.map L.toLinearMap : Submodule ℝ K) : Set K) := by
  ext y
  simp

omit [CompleteSpace H] in
private theorem submodule_set_add_eq_sup (C D : Submodule ℝ H) :
    (C : Set H) + (D : Set H) = ((C ⊔ D : Submodule ℝ H) : Set H) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact Submodule.mem_sup.mpr ⟨u, hu, v, hv, rfl⟩
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩

omit [CompleteSpace H] in
private theorem submodule_set_sub_eq_sup (C D : Submodule ℝ H) :
    (C : Set H) - (D : Set H) = ((C ⊔ D : Submodule ℝ H) : Set H) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    simpa [sub_eq_add_neg] using
      ((Submodule.mem_sup.mpr ⟨u, hu, -v, by simpa using D.neg_mem hv, rfl⟩) :
        u + -v ∈ (C ⊔ D : Submodule ℝ H))
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, -v, by simpa using D.neg_mem hv, by abel_nf⟩

/-- Helper for Corollary 15.33: the polar cone of a submodule is its orthogonal complement. -/
private theorem submodulePolarCone_eq_orthogonal (C : Submodule ℝ H) :
    Set.polarCone (C : Set H) = (Cᗮ : Set H) := by
  simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule C).2

/-- Helper for Corollary 15.33: closed submodules agree with their double orthogonals. -/
private theorem orthogonalOrthogonal_eq_self_of_isClosed
    (C : Submodule ℝ H) (hC_closed : IsClosed (C : Set H)) :
    Cᗮᗮ = C := by
  calc
    Cᗮᗮ = C.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure C
    _ = C := hC_closed.submodule_topologicalClosure_eq

-- Route correction: split the closedness equivalence into directional lemmas so each call to
-- Corollary 15.31 is consumed after one fixed normalization pass.
/-- Helper for Corollary 15.33: closedness of `L(C) + D` implies closedness of
`Cᗮ + L.adjoint(Dᗮ)`. -/
private theorem isClosedOrthogonalSupAdjointMapOrthogonal_of_isClosedMapSup
    (C : Submodule ℝ H) (D : Submodule ℝ K) (L : H →L[ℝ] K)
    (hC_closed : IsClosed (C : Set H)) (hD_closed : IsClosed (D : Set K))
    (hsum : IsClosed (((C.map L.toLinearMap) ⊔ D : Submodule ℝ K) : Set K)) :
    IsClosed (((Cᗮ) ⊔ (Dᗮ).map L.adjoint.toLinearMap : Submodule ℝ H) : Set H) := by
  have hsubspace :
      (D : Set K) - L '' (C : Set H) =
        (Submodule.span ℝ ((D : Set K) - L '' (C : Set H)) : Set K) := by
    -- Normalize the source difference set to the corresponding submodule supremum.
    rw [submodule_image_eq_map L C, submodule_set_sub_eq_sup D (C.map L.toLinearMap)]
    simp
  have hsub_closed : IsClosed ((D : Set K) - L '' (C : Set H)) := by
    -- The hypothesis on `L(C) ⊔ D` is exactly the closedness of the difference set.
    rw [submodule_image_eq_map L C, submodule_set_sub_eq_sup D (C.map L.toLinearMap)]
    simpa [sup_comm] using hsum
  have hpolar_closed :=
    Set.isClosed_add_adjoint_image_polarCone_of_closed_subspace_sub_image
      (C : Set H) (D : Set K) L
      ⟨0, C.zero_mem⟩
      hC_closed C.convex (Set.submodule_isCone C)
      ⟨0, D.zero_mem⟩
      hD_closed D.convex (Set.submodule_isCone D)
      hsubspace
      hsub_closed
  -- Rewrite the polar-cone sum to the orthogonal-complement supremum surface.
  rw [submodulePolarCone_eq_orthogonal C, submodulePolarCone_eq_orthogonal D,
    submodule_image_eq_map L.adjoint Dᗮ,
    submodule_set_add_eq_sup Cᗮ ((Dᗮ).map L.adjoint.toLinearMap)] at hpolar_closed
  simpa [sup_comm] using hpolar_closed

/-- Helper for Corollary 15.33: closedness of `Cᗮ + L.adjoint(Dᗮ)` implies closedness of
`L(C) + D`. -/
private theorem isClosedMapSup_of_isClosedOrthogonalSupAdjointMapOrthogonal
    (C : Submodule ℝ H) (D : Submodule ℝ K) (L : H →L[ℝ] K)
    (hC_closed : IsClosed (C : Set H)) (hD_closed : IsClosed (D : Set K))
    (hsum : IsClosed (((Cᗮ) ⊔ (Dᗮ).map L.adjoint.toLinearMap : Submodule ℝ H) : Set H)) :
    IsClosed (((C.map L.toLinearMap) ⊔ D : Submodule ℝ K) : Set K) := by
  have hsubspace :
      (Cᗮ : Set H) - L.adjoint '' (Dᗮ : Set K) =
        (Submodule.span ℝ ((Cᗮ : Set H) - L.adjoint '' (Dᗮ : Set K)) : Set H) := by
    -- Normalize the orthogonal-side difference set to the corresponding submodule supremum.
    rw [submodule_image_eq_map L.adjoint Dᗮ,
      submodule_set_sub_eq_sup Cᗮ ((Dᗮ).map L.adjoint.toLinearMap)]
    simp
  have hsub_closed : IsClosed ((Cᗮ : Set H) - L.adjoint '' (Dᗮ : Set K)) := by
    -- The orthogonal-side hypothesis again matches the difference-set surface.
    rw [submodule_image_eq_map L.adjoint Dᗮ,
      submodule_set_sub_eq_sup Cᗮ ((Dᗮ).map L.adjoint.toLinearMap)]
    simpa [sup_comm] using hsum
  have hpolar_closed :=
    Set.isClosed_add_adjoint_image_polarCone_of_closed_subspace_sub_image
      (Dᗮ : Set K) (Cᗮ : Set H) L.adjoint
      ⟨0, (Dᗮ).zero_mem⟩
      D.isClosed_orthogonal Dᗮ.convex (Set.submodule_isCone Dᗮ)
      ⟨0, (Cᗮ).zero_mem⟩
      C.isClosed_orthogonal Cᗮ.convex (Set.submodule_isCone Cᗮ)
      hsubspace
      hsub_closed
  -- Collapse the double orthogonals and return to the original map-sum surface.
  rw [submodulePolarCone_eq_orthogonal Dᗮ, submodulePolarCone_eq_orthogonal Cᗮ,
    orthogonalOrthogonal_eq_self_of_isClosed D hD_closed,
    orthogonalOrthogonal_eq_self_of_isClosed C hC_closed,
    ContinuousLinearMap.adjoint_adjoint, submodule_image_eq_map L C,
    submodule_set_add_eq_sup D (C.map L.toLinearMap)] at hpolar_closed
  simpa [sup_comm] using hpolar_closed

-- Proof sketch: identify `D - L '' C` and `Cᗮ - L.adjoint '' Dᗮ` with the corresponding subspace
-- sums, apply Corollary 15.31(4) in each direction, and rewrite the resulting polar cones of
-- subspaces as orthogonal complements.
/-- Corollary 15.33: for closed linear subspaces `C` and `D`, the subspace sum corresponding to
`L(C) + D` is closed if and only if the orthogonal-complement sum `Cᗮ + L^*(Dᗮ)` is closed. -/
theorem isClosed_map_sup_iff_isClosed_orthogonal_sup_adjoint_map_orthogonal
    (C : Submodule ℝ H) (D : Submodule ℝ K) (L : H →L[ℝ] K)
    (hC_closed : IsClosed (C : Set H)) (hD_closed : IsClosed (D : Set K)) :
    IsClosed (((C.map L.toLinearMap) ⊔ D : Submodule ℝ K) : Set K) ↔
      IsClosed (((Cᗮ) ⊔ (Dᗮ).map L.adjoint.toLinearMap : Submodule ℝ H) : Set H) := by
  constructor
  · intro hsum
    exact
      isClosedOrthogonalSupAdjointMapOrthogonal_of_isClosedMapSup
        C D L hC_closed hD_closed hsum
  · intro hsum
    exact
      isClosedMapSup_of_isClosedOrthogonalSupAdjointMapOrthogonal
        C D L hC_closed hD_closed hsum
