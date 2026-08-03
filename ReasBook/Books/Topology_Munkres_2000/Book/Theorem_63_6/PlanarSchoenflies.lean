module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Topology_Munkres_2000.Book.Definition_25_1.ComponentIn
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.RCLike.Real

public section

open Set

/-- Helper for Theorem 63.6: the exterior of the Euclidean closed unit ball is connected
in every real normed space of dimension greater than one. -/
private lemma isConnected_compl_closedUnitBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) :
    IsConnected (Metric.closedBall (0 : E) 1)ᶜ := by
  -- Polar coordinates realize the exterior as positive radial scalings of the unit sphere.
  let radialDomain : Set (Metric.sphere (0 : E) 1 × ℝ) :=
    Set.univ ×ˢ Set.Ioi 1
  let radialMap : Metric.sphere (0 : E) 1 × ℝ → E :=
    fun p ↦ p.2 • (p.1 : E)
  have hdomain : IsConnected radialDomain := by
    letI : ConnectedSpace (Metric.sphere (0 : E) 1) :=
      Subtype.connectedSpace (isConnected_sphere hrank 0 zero_le_one)
    change IsConnected
      ((Set.univ : Set (Metric.sphere (0 : E) 1)) ×ˢ Set.Ioi (1 : ℝ))
    exact isConnected_univ.prod
      (isConnected_Ioi (a := (1 : ℝ)))
  have hcontinuous : ContinuousOn radialMap radialDomain := by
    have : Continuous radialMap :=
      continuous_snd.smul (continuous_subtype_val.comp continuous_fst)
    exact this.continuousOn
  have himage : radialMap '' radialDomain = (Metric.closedBall (0 : E) 1)ᶜ := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨u, r⟩, ⟨_, hr⟩, rfl⟩
      change 1 < r at hr
      rw [Set.mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hr)]
      have huNorm : ‖(u : E)‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using u.property
      rw [huNorm, mul_one]
      exact hr
    · intro x hx
      have hxNorm : 1 < ‖x‖ := by
        simpa only [Set.mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right] using hx
      have hxNe : x ≠ 0 := by
        exact norm_pos_iff.mp (zero_lt_one.trans hxNorm)
      let u : Metric.sphere (0 : E) 1 :=
        ⟨‖x‖⁻¹ • x, by
          rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hxNe)]⟩
      refine ⟨(u, ‖x‖), ⟨Set.mem_univ _, hxNorm⟩, ?_⟩
      change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hxNe), one_smul]
  -- Connectedness now follows from the continuous image description.
  rw [← himage]
  exact hdomain.image radialMap hcontinuous

/-- Helper for Theorem 63.6: a planar Jordan curve filling records the closed disk
and the two connected sides of its frontier. -/
structure PlanarJordanFilling (D : Set (EuclideanSpace ℝ (Fin 2))) where
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  diskHomeomorph : carrier ≃ₜ B²
  interior_nonempty : (interior carrier).Nonempty
  interior_connected : IsConnected (interior carrier)
  exterior_connected : IsConnected carrierᶜ
  frontier_eq : frontier carrier = D
  closure_interior_eq : closure (interior carrier) = carrier

/-- Helper for Theorem 63.6: the Euclidean closed unit disk has nonempty interior. -/
private lemma closedUnitDisk_interior_nonempty :
    (interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)).Nonempty := by
  -- The interior is the nonempty open unit disk.
  rw [interior_closedBall 0 one_ne_zero]
  exact Metric.nonempty_ball.mpr one_pos

/-- Helper for Theorem 63.6: the Euclidean closed unit disk has connected interior. -/
private lemma closedUnitDisk_interior_connected :
    IsConnected (interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
  -- Convexity gives connectedness of the open unit disk.
  rw [interior_closedBall 0 one_ne_zero]
  exact Metric.isConnected_ball one_pos

/-- Helper for Theorem 63.6: the exterior of the Euclidean closed unit disk is connected. -/
private lemma closedUnitDisk_exterior_connected :
    IsConnected (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ := by
  -- Apply the polar-coordinate lemma using the plane's two-dimensional rank.
  apply isConnected_compl_closedUnitBall
  rw [← Module.finrank_eq_rank]
  norm_num

/-- Helper for Theorem 63.6: the frontier of the Euclidean closed unit disk is the unit circle. -/
private lemma closedUnitDisk_frontier_eq :
    frontier (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) =
      Metric.sphere 0 1 := by
  -- The frontier of a positive-radius closed ball is its metric sphere.
  exact frontier_closedBall 0 one_ne_zero

/-- Helper for Theorem 63.6: the closed unit disk is the closure of its interior. -/
private lemma closedUnitDisk_closure_interior_eq :
    closure (interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) =
      Metric.closedBall 0 1 := by
  -- Closing the open unit disk recovers the closed unit disk.
  rw [interior_closedBall 0 one_ne_zero]
  exact closure_ball 0 one_ne_zero

/-- Helper for Theorem 63.6: the Euclidean closed unit disk is the standard planar
Jordan filling of its unit-circle frontier. -/
noncomputable def standardPlanarJordanFilling :
    PlanarJordanFilling
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  { carrier := Metric.closedBall 0 1
    diskHomeomorph := Homeomorph.refl B²
    interior_nonempty := closedUnitDisk_interior_nonempty
    interior_connected := closedUnitDisk_interior_connected
    exterior_connected := closedUnitDisk_exterior_connected
    frontier_eq := closedUnitDisk_frontier_eq
    closure_interior_eq := closedUnitDisk_closure_interior_eq }

/-- Helper for Theorem 63.6: the inverse image of the standard disk has nonempty interior. -/
private lemma ambientDisk_interior_nonempty
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2)) :
    (interior (h.symm '' standardPlanarJordanFilling.carrier)).Nonempty := by
  -- Homeomorphisms carry the nonempty standard interior onto the new interior.
  rw [← h.symm.image_interior]
  exact standardPlanarJordanFilling.interior_nonempty.image h.symm

/-- Helper for Theorem 63.6: the inverse image of the standard disk has connected interior. -/
private lemma ambientDisk_interior_connected
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2)) :
    IsConnected (interior (h.symm '' standardPlanarJordanFilling.carrier)) := by
  -- Connectedness of the standard interior is preserved by the ambient homeomorphism.
  rw [← h.symm.image_interior]
  exact standardPlanarJordanFilling.interior_connected.image h.symm
    h.symm.continuous.continuousOn

/-- Helper for Theorem 63.6: the inverse image of the standard disk has connected exterior. -/
private lemma ambientDisk_exterior_connected
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2)) :
    IsConnected (h.symm '' standardPlanarJordanFilling.carrier)ᶜ := by
  -- The transported exterior is the image of the connected standard exterior.
  rw [← h.symm.image_compl]
  exact standardPlanarJordanFilling.exterior_connected.image h.symm
    h.symm.continuous.continuousOn

/-- Helper for Theorem 63.6: ambient straightening identifies the transported disk frontier. -/
private lemma ambientDisk_frontier_eq
    (D : Set (EuclideanSpace ℝ (Fin 2)))
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hD : h '' D = Metric.sphere 0 1) :
    frontier (h.symm '' standardPlanarJordanFilling.carrier) = D := by
  -- Transport the standard frontier and then invert the straightening equation.
  calc
    frontier (h.symm '' standardPlanarJordanFilling.carrier) =
        h.symm '' frontier standardPlanarJordanFilling.carrier :=
      (h.symm.image_frontier standardPlanarJordanFilling.carrier).symm
    _ = h.symm '' Metric.sphere 0 1 :=
      congrArg (fun S ↦ h.symm '' S) standardPlanarJordanFilling.frontier_eq
    _ = D := by
      rw [← hD, h.symm.image_eq_preimage_symm]
      exact h.preimage_image D

/-- Helper for Theorem 63.6: the transported disk is the closure of its interior. -/
private lemma ambientDisk_closure_interior_eq
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2)) :
    closure (interior (h.symm '' standardPlanarJordanFilling.carrier)) =
      h.symm '' standardPlanarJordanFilling.carrier := by
  -- Closure and interior both commute with the ambient homeomorphism.
  rw [← h.symm.image_interior, ← h.symm.image_closure,
    standardPlanarJordanFilling.closure_interior_eq]

/-- Helper for Theorem 63.6: an ambient plane homeomorphism carrying a curve to the
unit circle transports the standard disk filling back to that curve. -/
noncomputable def planarJordanFillingOfAmbientHomeomorph
    (D : Set (EuclideanSpace ℝ (Fin 2)))
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hD : h '' D = Metric.sphere 0 1) : PlanarJordanFilling D :=
  { carrier := h.symm '' standardPlanarJordanFilling.carrier
    diskHomeomorph :=
      (Homeomorph.image h.symm standardPlanarJordanFilling.carrier).symm.trans
        standardPlanarJordanFilling.diskHomeomorph
    interior_nonempty := ambientDisk_interior_nonempty h
    interior_connected := ambientDisk_interior_connected h
    exterior_connected := ambientDisk_exterior_connected h
    frontier_eq := ambientDisk_frontier_eq D h hD
    closure_interior_eq := ambientDisk_closure_interior_eq h }

namespace PlanarJordanFilling

/-- Helper for Theorem 63.6: the carrier of a planar Jordan filling is compact. -/
lemma isCompact_carrier {D : Set (EuclideanSpace ℝ (Fin 2))}
    (F : PlanarJordanFilling D) : IsCompact F.carrier := by
  -- Transfer compactness from the closed unit disk through the chosen homeomorphism.
  letI : CompactSpace F.carrier := F.diskHomeomorph.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- Helper for Theorem 63.6: the carrier of a planar Jordan filling is closed. -/
lemma isClosed_carrier {D : Set (EuclideanSpace ℝ (Fin 2))}
    (F : PlanarJordanFilling D) : IsClosed F.carrier := by
  -- Compact subsets of the Euclidean plane are closed.
  exact F.isCompact_carrier.isClosed

/-- Helper for Theorem 63.6: the carrier of a planar Jordan filling is bounded. -/
lemma carrier_bounded {D : Set (EuclideanSpace ℝ (Fin 2))}
    (F : PlanarJordanFilling D) : Bornology.IsBounded F.carrier := by
  -- Compactness supplies the metric boundedness needed to distinguish the two sides.
  exact F.isCompact_carrier.isBounded

/-- Helper for Theorem 63.6: a subset of an unbounded normed space with bounded
complement is itself unbounded. -/
private lemma not_bounded_of_compl_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {S : Set E} (hSc : Bornology.IsBounded Sᶜ) : ¬ Bornology.IsBounded S := by
  -- If both sides were bounded, their union would make the whole space bounded.
  intro hS
  have huniv : Bornology.IsBounded (Set.univ : Set E) := by
    rw [← union_compl_self S]
    exact hS.union hSc
  exact NormedSpace.unbounded_univ ℝ E huniv

/-- Helper for Theorem 63.6: the exterior side of a planar Jordan filling is unbounded. -/
lemma exterior_unbounded {D : Set (EuclideanSpace ℝ (Fin 2))}
    (F : PlanarJordanFilling D) : ¬ Bornology.IsBounded F.carrierᶜ := by
  -- The complement of the exterior is the bounded filled carrier.
  apply not_bounded_of_compl_bounded
  simpa only [compl_compl] using F.carrier_bounded

/-- Helper for Theorem 63.6: the complement of the frontier is the union of the
interior and exterior sides of a planar Jordan filling. -/
lemma compl_eq_interior_union_exterior {D : Set (EuclideanSpace ℝ (Fin 2))}
    (F : PlanarJordanFilling D) : Dᶜ = interior F.carrier ∪ F.carrierᶜ := by
  -- Rewrite the curve as the frontier, then use closedness to normalize the exterior interior.
  calc
    Dᶜ = (frontier F.carrier)ᶜ := congrArg (fun S : Set (EuclideanSpace ℝ (Fin 2)) ↦ Sᶜ)
      F.frontier_eq |>.symm
    _ = interior F.carrier ∪ interior F.carrierᶜ := compl_frontier_eq_union_interior
    _ = interior F.carrier ∪ F.carrierᶜ := by
      rw [F.isClosed_carrier.isOpen_compl.interior_eq]

/-- Helper for Theorem 63.6: the filling interior and exterior are exactly the
two connected components of the curve complement. -/
lemma interiorExterior_components {D : Set (EuclideanSpace ℝ (Fin 2))}
    (F : PlanarJordanFilling D) :
    IsConnectedComponentIn Dᶜ (interior F.carrier) ∧
      IsConnectedComponentIn Dᶜ F.carrierᶜ := by
  -- The normalized frontier-complement equation puts each connected side inside `Dᶜ`.
  have hdecomp := F.compl_eq_interior_union_exterior
  have hinteriorSubset : interior F.carrier ⊆ Dᶜ := by
    rw [hdecomp]
    exact subset_union_left
  have hexteriorSubset : F.carrierᶜ ⊆ Dᶜ := by
    rw [hdecomp]
    exact subset_union_right
  have hsidesDisjoint : Disjoint (interior F.carrier) F.carrierᶜ := by
    rw [Set.disjoint_left]
    exact fun _ hxInterior hxExterior ↦ hxExterior (interior_subset hxInterior)
  constructor
  · obtain ⟨x, hxInterior⟩ := F.interior_nonempty
    have hinteriorEq : interior F.carrier = connectedComponentIn Dᶜ x := by
      apply Set.Subset.antisymm
      · exact F.interior_connected.isPreconnected.subset_connectedComponentIn
          hxInterior hinteriorSubset
      · -- A connected component meeting the interior cannot lie in the disjoint exterior.
        obtain hsubsetInterior | hsubsetExterior :=
          IsPreconnected.subset_or_subset isOpen_interior
            F.isClosed_carrier.isOpen_compl hsidesDisjoint
            (by simpa only [← hdecomp] using connectedComponentIn_subset Dᶜ x)
            isPreconnected_connectedComponentIn
        · exact hsubsetInterior
        · exact False.elim
            (hsidesDisjoint.le_bot
              ⟨hxInterior, hsubsetExterior (mem_connectedComponentIn (hinteriorSubset hxInterior))⟩)
    rw [hinteriorEq]
    exact IsConnectedComponentIn.of_mem (hinteriorSubset hxInterior)
  · obtain ⟨x, hxExterior⟩ := F.exterior_connected.nonempty
    have hexteriorEq : F.carrierᶜ = connectedComponentIn Dᶜ x := by
      apply Set.Subset.antisymm
      · exact F.exterior_connected.isPreconnected.subset_connectedComponentIn
          hxExterior hexteriorSubset
      · -- A connected component meeting the exterior cannot lie in the disjoint interior.
        obtain hsubsetInterior | hsubsetExterior :=
          IsPreconnected.subset_or_subset isOpen_interior
            F.isClosed_carrier.isOpen_compl hsidesDisjoint
            (by simpa only [← hdecomp] using connectedComponentIn_subset Dᶜ x)
            isPreconnected_connectedComponentIn
        · exact False.elim
            (hsidesDisjoint.le_bot
              ⟨hsubsetInterior (mem_connectedComponentIn (hexteriorSubset hxExterior)), hxExterior⟩)
        · exact hsubsetExterior
    rw [hexteriorEq]
    exact IsConnectedComponentIn.of_mem (hexteriorSubset hxExterior)

/-- Helper for Theorem 63.6: every bounded complementary component of a planar
Jordan filling is its interior side. -/
lemma boundedComponent_eq_interior {D W : Set (EuclideanSpace ℝ (Fin 2))}
    (F : PlanarJordanFilling D) (hW : IsConnectedComponentIn Dᶜ W)
    (hWbounded : Bornology.IsBounded W) : W = interior F.carrier := by
  -- Connectedness places `W` wholly on one side of the frontier decomposition.
  have hdecomp := F.compl_eq_interior_union_exterior
  have hsidesDisjoint : Disjoint (interior F.carrier) F.carrierᶜ := by
    rw [Set.disjoint_left]
    exact fun _ hxInterior hxExterior ↦ hxExterior (interior_subset hxInterior)
  obtain hWinterior | hWexterior :=
    IsPreconnected.subset_or_subset isOpen_interior
      F.isClosed_carrier.isOpen_compl hsidesDisjoint
      (by simpa only [← hdecomp] using hW.subset)
      hW.isConnected.isPreconnected
  · -- A shared point identifies `W` with the canonical interior component.
    obtain ⟨w, hwW⟩ := hW.nonempty
    have hwInterior := hWinterior hwW
    calc
      W = connectedComponentIn Dᶜ w := hW.eq_connectedComponentIn hwW
      _ = interior F.carrier :=
        (F.interiorExterior_components.1.eq_connectedComponentIn hwInterior).symm
  · -- Equality with the exterior would contradict boundedness.
    obtain ⟨w, hwW⟩ := hW.nonempty
    have hwExterior := hWexterior hwW
    have hW_eq_exterior : W = F.carrierᶜ := by
      calc
        W = connectedComponentIn Dᶜ w := hW.eq_connectedComponentIn hwW
        _ = F.carrierᶜ :=
          (F.interiorExterior_components.2.eq_connectedComponentIn hwExterior).symm
    exact False.elim (F.exterior_unbounded (hW_eq_exterior ▸ hWbounded))

end PlanarJordanFilling

/-- Helper for Theorem 63.6: every planar simple closed curve admits a Jordan
disk filling with the specified interior and exterior behavior. -/
theorem simpleClosedCurve_hasPlanarJordanFilling
    (D : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve D] :
    Nonempty (PlanarJordanFilling D) := by
  -- TODO: formalize the disk-filling form of the planar Schoenflies theorem cited by Munkres.
  sorry

/-- Helper for Theorem 63.6: a bounded complementary component supplied by a
planar Jordan filling has closed-disk closure. -/
lemma PlanarJordanFilling.componentClosure_homeomorph_closedUnitDisk
    {D W : Set (EuclideanSpace ℝ (Fin 2))} (F : PlanarJordanFilling D)
    (hW : IsConnectedComponentIn Dᶜ W) (hWbounded : Bornology.IsBounded W) :
    Nonempty (closure W ≃ₜ B²) := by
  -- First identify the selected bounded component with the filling interior.
  have hWinterior : W = interior F.carrier :=
    F.boundedComponent_eq_interior hW hWbounded
  have hclosure : closure W = F.carrier := by
    calc
      closure W = closure (interior F.carrier) := congrArg closure hWinterior
      _ = F.carrier := F.closure_interior_eq
  -- Transport along the closure equality before applying the disk model.
  exact ⟨(Homeomorph.setCongr hclosure).trans F.diskHomeomorph⟩

/-- Helper for Theorem 63.6: the closure of a bounded complementary component
of a planar simple closed curve is homeomorphic to the closed unit disk. -/
theorem boundedJordanComponentClosure_homeomorph_closedUnitDisk
    (D W : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve D]
    (hW : IsConnectedComponentIn Dᶜ W) (hWbounded : Bornology.IsBounded W) :
    Nonempty (closure W ≃ₜ B²) := by
  -- Choose the curve-indexed filling supplied by planar Schoenflies.
  obtain ⟨F⟩ := simpleClosedCurve_hasPlanarJordanFilling D
  -- The filling-level adapter performs the component identification and transport.
  exact F.componentClosure_homeomorph_closedUnitDisk hW hWbounded
