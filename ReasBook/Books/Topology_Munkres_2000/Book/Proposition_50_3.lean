module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/-- Helper for Proposition 50.3: a nonempty interior of an affine subspace gives a nonempty
interior of its direction. -/
private lemma directionInteriorNonempty {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : AffineSubspace ℝ V) (hP : (interior (P : Set V)).Nonempty) :
    (interior (P.direction : Set V)).Nonempty := by
  -- Choose an interior point to identify the direction with the translate through that point.
  obtain ⟨x, hx⟩ := hP
  have hxP : x ∈ P := interior_subset hx
  rw [P.coe_direction_eq_vsub_set_right hxP]
  simp only [vsub_eq_sub]
  -- Translation is a homeomorphism, so it carries the given interior onto the translated one.
  have himage : ((Homeomorph.subRight x) '' interior (P : Set V)).Nonempty :=
    Set.image_nonempty.mpr ⟨x, hx⟩
  rw [(Homeomorph.subRight x).image_interior] at himage
  simpa only [Homeomorph.subRight_apply] using himage

/-- Proposition 50.3. An affine subspace of `ℝ^N` whose direction has dimension less than `N`
has empty interior. -/
theorem affineSubspace_interior_eq_empty_of_finrank_lt {N : ℕ}
    (P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin N)))
    (hdim : Module.finrank ℝ P.direction < N) :
    interior (P : Set (EuclideanSpace ℝ (Fin N))) = ∅ := by
  -- The dimension bound says that the direction is a proper submodule of the ambient space.
  have hfinrank :
      Module.finrank ℝ P.direction < Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  have hdirection : P.direction < ⊤ :=
    Submodule.lt_top_of_finrank_lt_finrank hfinrank
  -- An interior point would give the direction nonempty interior and hence force it to be `⊤`.
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hdirectionInterior :
      (interior (P.direction : Set (EuclideanSpace ℝ (Fin N)))).Nonempty :=
    directionInteriorNonempty P ⟨x, hx⟩
  have htop : P.direction = ⊤ :=
    Submodule.eq_top_of_nonempty_interior' P.direction hdirectionInterior
  exact hdirection.ne htop
