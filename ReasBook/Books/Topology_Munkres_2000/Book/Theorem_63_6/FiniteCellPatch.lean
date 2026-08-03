module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Piecewise

public section

open Set
open scoped Topology

universe u

namespace Schoenflies

/-- Helper for Theorem 63.6: a finite closed-cell patch records compatible
forward and inverse maps on a closed finite union. -/
structure FiniteClosedCellPatch (X : Type u) [TopologicalSpace X] (n : ℕ) where
  cell : Fin n → Set X
  support : Set X
  support_eq_iUnion : support = ⋃ i, cell i
  cell_isClosed : ∀ i, IsClosed (cell i)
  forward : X → X
  inverse : X → X
  forward_continuousOn : ContinuousOn forward support
  inverse_continuousOn : ContinuousOn inverse support
  forward_cell : ∀ i, MapsTo forward (cell i) (cell i)
  inverse_cell : ∀ i, MapsTo inverse (cell i) (cell i)
  leftInvOn : Set.LeftInvOn inverse forward support
  rightInvOn : Set.RightInvOn inverse forward support
  forward_frontier : Set.EqOn forward id (frontier support)
  inverse_frontier : Set.EqOn inverse id (frontier support)

namespace FiniteClosedCellPatch

variable {X : Type u} [TopologicalSpace X] {n : ℕ}

/-- Helper for Theorem 63.6: select an index of a finite cell containing a
point of the union. -/
noncomputable def selectedCellIndex (cell : Fin n → Set X)
    (x : (⋃ i, cell i : Set X)) : Fin n :=
  Classical.choose (Set.mem_iUnion.mp x.property)

omit [TopologicalSpace X] in
/-- Helper for Theorem 63.6: the selected cell really contains the union
point. -/
theorem selectedCellIndex_mem (cell : Fin n → Set X)
    (x : (⋃ i, cell i : Set X)) : x.1 ∈ cell (selectedCellIndex cell x) := by
  -- Read the membership proof attached to the classical selected index.
  exact Classical.choose_spec (Set.mem_iUnion.mp x.property)

/-- Helper for Theorem 63.6: glue the forward maps of compatible local cell
homeomorphisms, using the identity away from their union. -/
noncomputable def gluedForward (cell : Fin n → Set X)
    (e : ∀ i, cell i ≃ₜ cell i) : X → X :=
  fun x ↦ @dite X (x ∈ ⋃ i, cell i) (Classical.propDecidable _)
    (fun hx ↦
      (e (selectedCellIndex cell ⟨x, hx⟩)
        ⟨x, selectedCellIndex_mem cell ⟨x, hx⟩⟩ : X))
    (fun _ ↦ x)

/-- Helper for Theorem 63.6: glue the inverse maps of compatible local cell
homeomorphisms, using the identity away from their union. -/
noncomputable def gluedInverse (cell : Fin n → Set X)
    (e : ∀ i, cell i ≃ₜ cell i) : X → X :=
  fun x ↦ @dite X (x ∈ ⋃ i, cell i) (Classical.propDecidable _)
    (fun hx ↦
      ((e (selectedCellIndex cell ⟨x, hx⟩)).symm
        ⟨x, selectedCellIndex_mem cell ⟨x, hx⟩⟩ : X))
    (fun _ ↦ x)

/-- Helper for Theorem 63.6: compatibility on overlaps identifies the glued
forward map with any local forward map containing the point. -/
theorem gluedForward_eq_local (cell : Fin n → Set X)
    (e : ∀ i, cell i ≃ₜ cell i)
    (hcompat : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
      (e i ⟨x, hxi⟩ : X) = (e j ⟨x, hxj⟩ : X))
    (i : Fin n) {x : X} (hx : x ∈ cell i) :
    gluedForward cell e x = (e i ⟨x, hx⟩ : X) := by
  -- Select the union branch, then compare the selected cell with `i` on their overlap.
  classical
  unfold gluedForward
  rw [dif_pos (Set.mem_iUnion_of_mem i hx)]
  exact hcompat (selectedCellIndex cell ⟨x, Set.mem_iUnion_of_mem i hx⟩) i x
    (selectedCellIndex_mem cell ⟨x, Set.mem_iUnion_of_mem i hx⟩) hx

/-- Helper for Theorem 63.6: inverse compatibility identifies the glued
inverse map with any local inverse map containing the point. -/
theorem gluedInverse_eq_local (cell : Fin n → Set X)
    (e : ∀ i, cell i ≃ₜ cell i)
    (hcompat : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
      ((e i).symm ⟨x, hxi⟩ : X) = ((e j).symm ⟨x, hxj⟩ : X))
    (i : Fin n) {x : X} (hx : x ∈ cell i) :
    gluedInverse cell e x = ((e i).symm ⟨x, hx⟩ : X) := by
  -- Select the union branch and use inverse agreement on the chosen overlap.
  classical
  unfold gluedInverse
  rw [dif_pos (Set.mem_iUnion_of_mem i hx)]
  exact hcompat (selectedCellIndex cell ⟨x, Set.mem_iUnion_of_mem i hx⟩) i x
    (selectedCellIndex_mem cell ⟨x, Set.mem_iUnion_of_mem i hx⟩) hx

/-- Helper for Theorem 63.6: explicit compatible local self-homeomorphisms glue
to a finite closed-cell patch while retaining its construction specifications. -/
theorem ofLocalEquivsWithSpecs (cell : Fin n → Set X)
    (hclosed : ∀ i, IsClosed (cell i))
    (e : ∀ i, cell i ≃ₜ cell i)
    (hforwardCompat : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
      (e i ⟨x, hxi⟩ : X) = (e j ⟨x, hxj⟩ : X))
    (hinverseCompat : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
      ((e i).symm ⟨x, hxi⟩ : X) = ((e j).symm ⟨x, hxj⟩ : X))
    (hfrontier : ∀ i x (hxi : x ∈ cell i) (_ : x ∈ frontier (⋃ i, cell i)),
      (e i ⟨x, hxi⟩ : X) = x) :
    ∃ P : FiniteClosedCellPatch X n,
      P.cell = cell ∧
        P.support = ⋃ i, cell i ∧
        P.forward = gluedForward cell e ∧
        P.inverse = gluedInverse cell e := by
  let forward := gluedForward cell e
  let inverse := gluedInverse cell e
  have hforwardCell (i : Fin n) : MapsTo forward (cell i) (cell i) := by
    -- On a cell the glued map is its local homeomorphism, hence remains in that cell.
    intro x hx
    dsimp only [forward]
    rw [gluedForward_eq_local cell e hforwardCompat i hx]
    exact (e i ⟨x, hx⟩).property
  have hinverseCell (i : Fin n) : MapsTo inverse (cell i) (cell i) := by
    -- The inverse computation rule gives the analogous cell preservation.
    intro x hx
    dsimp only [inverse]
    rw [gluedInverse_eq_local cell e hinverseCompat i hx]
    exact ((e i).symm ⟨x, hx⟩).property
  have hforwardContinuousCell (i : Fin n) : ContinuousOn forward (cell i) := by
    -- Restrict to one cell, where compatibility reduces the glued map to `e i`.
    rw [continuousOn_iff_continuous_restrict]
    exact (continuous_subtype_val.comp (e i).continuous).congr fun x ↦
      (gluedForward_eq_local cell e hforwardCompat i x.property).symm
  have hinverseContinuousCell (i : Fin n) : ContinuousOn inverse (cell i) := by
    -- The restriction of the glued inverse is the continuous inverse of `e i`.
    rw [continuousOn_iff_continuous_restrict]
    exact (continuous_subtype_val.comp (e i).continuous_symm).congr fun x ↦
      (gluedInverse_eq_local cell e hinverseCompat i x.property).symm
  have hforwardContinuous : ContinuousOn forward (⋃ i, cell i) := by
    -- A finite closed cover glues the cellwise continuity statements.
    exact (locallyFinite_of_finite cell).continuousOn_iUnion hclosed hforwardContinuousCell
  have hinverseContinuous : ContinuousOn inverse (⋃ i, cell i) := by
    -- Apply the same finite-cover continuity theorem to the inverse.
    exact (locallyFinite_of_finite cell).continuousOn_iUnion hclosed hinverseContinuousCell
  have hleftInv : Set.LeftInvOn inverse forward (⋃ i, cell i) := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hforwardEq := gluedForward_eq_local cell e hforwardCompat i hxi
    have hforwardMem : forward x ∈ cell i := hforwardCell i hxi
    calc
      inverse (forward x) = ((e i).symm ⟨forward x, hforwardMem⟩ : X) :=
        gluedInverse_eq_local cell e hinverseCompat i hforwardMem
      _ = ((e i).symm (e i ⟨x, hxi⟩) : X) := by
        congr 2
        exact Subtype.ext hforwardEq
      _ = x := congrArg Subtype.val ((e i).symm_apply_apply ⟨x, hxi⟩)
  have hrightInv : Set.RightInvOn inverse forward (⋃ i, cell i) := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hinverseEq := gluedInverse_eq_local cell e hinverseCompat i hxi
    have hinverseMem : inverse x ∈ cell i := hinverseCell i hxi
    calc
      forward (inverse x) = (e i ⟨inverse x, hinverseMem⟩ : X) :=
        gluedForward_eq_local cell e hforwardCompat i hinverseMem
      _ = (e i ((e i).symm ⟨x, hxi⟩) : X) := by
        congr 2
        exact Subtype.ext hinverseEq
      _ = x := congrArg Subtype.val ((e i).apply_symm_apply ⟨x, hxi⟩)
  have hforwardFrontier : Set.EqOn forward id (frontier (⋃ i, cell i)) := by
    intro x hx
    have hxUnion : x ∈ ⋃ i, cell i :=
      (isClosed_iUnion_of_finite hclosed).frontier_subset hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxUnion
    exact (gluedForward_eq_local cell e hforwardCompat i hxi).trans
      (hfrontier i x hxi hx)
  have hinverseFrontier : Set.EqOn inverse id (frontier (⋃ i, cell i)) := by
    intro x hx
    have hxUnion : x ∈ ⋃ i, cell i :=
      (isClosed_iUnion_of_finite hclosed).frontier_subset hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxUnion
    have hfixSubtype : e i ⟨x, hxi⟩ = ⟨x, hxi⟩ :=
      Subtype.ext (hfrontier i x hxi hx)
    calc
      inverse x = ((e i).symm ⟨x, hxi⟩ : X) :=
        gluedInverse_eq_local cell e hinverseCompat i hxi
      _ = ((e i).symm (e i ⟨x, hxi⟩) : X) := by rw [hfixSubtype]
      _ = x := congrArg Subtype.val ((e i).symm_apply_apply ⟨x, hxi⟩)
  -- Assemble the stable patch interface from the cellwise gluing facts.
  refine ⟨{
    cell := cell
    support := ⋃ i, cell i
    support_eq_iUnion := rfl
    cell_isClosed := hclosed
    forward := forward
    inverse := inverse
    forward_continuousOn := hforwardContinuous
    inverse_continuousOn := hinverseContinuous
    forward_cell := hforwardCell
    inverse_cell := hinverseCell
    leftInvOn := hleftInv
    rightInvOn := hrightInv
    forward_frontier := hforwardFrontier
    inverse_frontier := hinverseFrontier
  }, rfl, rfl, rfl, rfl⟩

/-- Helper for Theorem 63.6: explicit compatible local self-homeomorphisms of
finitely many closed cells glue to a finite closed-cell patch. -/
theorem ofLocalEquivs (cell : Fin n → Set X)
    (hclosed : ∀ i, IsClosed (cell i))
    (e : ∀ i, cell i ≃ₜ cell i)
    (hforwardCompat : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
      (e i ⟨x, hxi⟩ : X) = (e j ⟨x, hxj⟩ : X))
    (hinverseCompat : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
      ((e i).symm ⟨x, hxi⟩ : X) = ((e j).symm ⟨x, hxj⟩ : X))
    (hfrontier : ∀ i x (hxi : x ∈ cell i) (_ : x ∈ frontier (⋃ i, cell i)),
      (e i ⟨x, hxi⟩ : X) = x) :
    Nonempty (FiniteClosedCellPatch X n) := by
  -- Forget only the construction equations when callers need the patch itself.
  obtain ⟨P, _, _, _, _⟩ := ofLocalEquivsWithSpecs cell hclosed e
    hforwardCompat hinverseCompat hfrontier
  exact Nonempty.intro P

/-- Helper for Theorem 63.6: the support of a finite closed-cell patch is closed. -/
theorem support_isClosed (P : FiniteClosedCellPatch X n) : IsClosed P.support := by
  -- Rewrite the named support as the finite union of its closed cells.
  rw [P.support_eq_iUnion]
  exact isClosed_iUnion_of_finite P.cell_isClosed

/-- Helper for Theorem 63.6: the patch forward map preserves its support. -/
theorem forward_mapsTo_support (P : FiniteClosedCellPatch X n) :
    MapsTo P.forward P.support P.support := by
  -- Choose a cell containing the point and use preservation of that same cell.
  rw [P.support_eq_iUnion, mapsTo_iUnion]
  intro i x hx
  exact Set.mem_iUnion_of_mem i (P.forward_cell i hx)

/-- Helper for Theorem 63.6: the patch inverse map preserves its support. -/
theorem inverse_mapsTo_support (P : FiniteClosedCellPatch X n) :
    MapsTo P.inverse P.support P.support := by
  -- The inverse uses the identical finite-cell preservation argument.
  rw [P.support_eq_iUnion, mapsTo_iUnion]
  intro i x hx
  exact Set.mem_iUnion_of_mem i (P.inverse_cell i hx)

/-- Helper for Theorem 63.6: extend the patch forward map by the identity off
its support. -/
noncomputable def extendedForward (P : FiniteClosedCellPatch X n) : X → X :=
  @Set.piecewise X (fun _ ↦ X) P.support P.forward id
    (fun _ ↦ Classical.propDecidable _)

/-- Helper for Theorem 63.6: extend the patch inverse map by the identity off
its support. -/
noncomputable def extendedInverse (P : FiniteClosedCellPatch X n) : X → X :=
  @Set.piecewise X (fun _ ↦ X) P.support P.inverse id
    (fun _ ↦ Classical.propDecidable _)

/-- Helper for Theorem 63.6: the extended forward map agrees with the patch on
the support. -/
theorem extendedForward_eq (P : FiniteClosedCellPatch X n) :
    Set.EqOn P.extendedForward P.forward P.support := by
  -- Select the support branch of the piecewise definition.
  classical
  intro x hx
  unfold extendedForward
  exact P.support.piecewise_eq_of_mem P.forward id hx

/-- Helper for Theorem 63.6: the extended inverse map agrees with the patch on
the support. -/
theorem extendedInverse_eq (P : FiniteClosedCellPatch X n) :
    Set.EqOn P.extendedInverse P.inverse P.support := by
  -- Select the support branch of the piecewise definition.
  classical
  intro x hx
  unfold extendedInverse
  exact P.support.piecewise_eq_of_mem P.inverse id hx

/-- Helper for Theorem 63.6: the extended forward map is the identity off the
support. -/
theorem extendedForward_eq_id (P : FiniteClosedCellPatch X n) :
    Set.EqOn P.extendedForward id P.supportᶜ := by
  -- Select the exterior branch of the piecewise definition.
  classical
  intro x hx
  unfold extendedForward
  exact P.support.piecewise_eq_of_notMem P.forward id hx

/-- Helper for Theorem 63.6: the extended inverse map is the identity off the
support. -/
theorem extendedInverse_eq_id (P : FiniteClosedCellPatch X n) :
    Set.EqOn P.extendedInverse id P.supportᶜ := by
  -- Select the exterior branch of the piecewise definition.
  classical
  intro x hx
  unfold extendedInverse
  exact P.support.piecewise_eq_of_notMem P.inverse id hx

/-- Helper for Theorem 63.6: the identity extension of the forward patch map
is continuous. -/
theorem continuous_extendedForward (P : FiniteClosedCellPatch X n) :
    Continuous P.extendedForward := by
  -- Frontier fixation glues the continuous support map to the exterior identity.
  classical
  unfold extendedForward
  apply continuous_piecewise P.forward_frontier
  · simpa only [P.support_isClosed.closure_eq] using P.forward_continuousOn
  · exact continuous_id.continuousOn

/-- Helper for Theorem 63.6: the identity extension of the inverse patch map
is continuous. -/
theorem continuous_extendedInverse (P : FiniteClosedCellPatch X n) :
    Continuous P.extendedInverse := by
  -- Apply the same frontier gluing argument to the inverse map.
  classical
  unfold extendedInverse
  apply continuous_piecewise P.inverse_frontier
  · simpa only [P.support_isClosed.closure_eq] using P.inverse_continuousOn
  · exact continuous_id.continuousOn

/-- Helper for Theorem 63.6: the extended inverse is a left inverse of the
extended forward map. -/
theorem extended_leftInverse (P : FiniteClosedCellPatch X n) :
    Function.LeftInverse P.extendedInverse P.extendedForward := by
  intro x
  by_cases hx : x ∈ P.support
  · -- Inside the support, preservation keeps the second evaluation inside.
    rw [P.extendedForward_eq hx,
      P.extendedInverse_eq (P.forward_mapsTo_support hx)]
    exact P.leftInvOn hx
  · -- Outside the support, both extensions are the identity.
    rw [P.extendedForward_eq_id hx]
    simpa only [id_eq] using P.extendedInverse_eq_id hx

/-- Helper for Theorem 63.6: the extended inverse is a right inverse of the
extended forward map. -/
theorem extended_rightInverse (P : FiniteClosedCellPatch X n) :
    Function.RightInverse P.extendedInverse P.extendedForward := by
  intro x
  by_cases hx : x ∈ P.support
  · -- Inside the support, inverse preservation exposes the patch inverse law.
    rw [P.extendedInverse_eq hx,
      P.extendedForward_eq (P.inverse_mapsTo_support hx)]
    exact P.rightInvOn hx
  · -- Outside the support, both extensions again reduce to the identity.
    rw [P.extendedInverse_eq_id hx]
    simpa only [id_eq] using P.extendedForward_eq_id hx

/-- Helper for Theorem 63.6: the mutually inverse identity extensions form an
ambient equivalence. -/
noncomputable def supportedEquiv (P : FiniteClosedCellPatch X n) : X ≃ X :=
  Equiv.mk P.extendedForward P.extendedInverse P.extended_leftInverse P.extended_rightInverse

/-- Helper for Theorem 63.6: the finite patch extends to an ambient
homeomorphism supported on its closed union. -/
noncomputable def supportedHomeomorph (P : FiniteClosedCellPatch X n) : X ≃ₜ X :=
  Homeomorph.mk P.supportedEquiv P.continuous_extendedForward P.continuous_extendedInverse

/-- Helper for Theorem 63.6: the supported homeomorphism has the prescribed
forward and inverse behavior on and off the support. -/
theorem existsSupportedHomeomorph (P : FiniteClosedCellPatch X n) :
    ∃ k : X ≃ₜ X,
      Set.EqOn k P.forward P.support ∧
        Set.EqOn k.symm P.inverse P.support ∧
        Set.EqOn k id P.supportᶜ ∧
        Set.EqOn k.symm id P.supportᶜ := by
  -- Package the four computation rules for the explicit identity extension.
  refine ⟨P.supportedHomeomorph, ?_, ?_, ?_, ?_⟩
  · exact P.extendedForward_eq
  · exact P.extendedInverse_eq
  · exact P.extendedForward_eq_id
  · exact P.extendedInverse_eq_id

variable [PseudoMetricSpace X]

/-- Helper for Theorem 63.6: cell diameter bounds control both displacements
of the supported ambient homeomorphism. -/
theorem existsSupportedHomeomorphWithDisplacement
    (P : FiniteClosedCellPatch X n) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hbounded : ∀ i, Bornology.IsBounded (P.cell i))
    (hdiam : ∀ i, Metric.diam (P.cell i) ≤ ε) :
    ∃ k : X ≃ₜ X,
      Set.EqOn k P.forward P.support ∧
        Set.EqOn k.symm P.inverse P.support ∧
        Set.EqOn k id P.supportᶜ ∧
        Set.EqOn k.symm id P.supportᶜ ∧
        (∀ x, dist (k x) x ≤ ε) ∧
        ∀ x, dist (k.symm x) x ≤ ε := by
  obtain ⟨k, hkForward, hkInverse, hkOutside, hkInverseOutside⟩ :=
    P.existsSupportedHomeomorph
  refine ⟨k, hkForward, hkInverse, hkOutside, hkInverseOutside, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ P.support
    · -- A containing cell bounds the forward displacement by its diameter.
      have hxSupport := hx
      rw [P.support_eq_iUnion] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      calc
        dist (k x) x = dist (P.forward x) x :=
          congrArg (fun y ↦ dist y x) (hkForward hxSupport)
        _ ≤ Metric.diam (P.cell i) :=
          Metric.dist_le_diam_of_mem (hbounded i) (P.forward_cell i hxi) hxi
        _ ≤ ε := hdiam i
    · -- Off the support the displacement vanishes.
      rw [hkOutside hx, id_eq, dist_self]
      exact hε
  · intro x
    by_cases hx : x ∈ P.support
    · -- The inverse preserves the chosen cell and obeys the same diameter bound.
      have hxSupport := hx
      rw [P.support_eq_iUnion] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      calc
        dist (k.symm x) x = dist (P.inverse x) x :=
          congrArg (fun y ↦ dist y x) (hkInverse hxSupport)
        _ ≤ Metric.diam (P.cell i) :=
          Metric.dist_le_diam_of_mem (hbounded i) (P.inverse_cell i hxi) hxi
        _ ≤ ε := hdiam i
    · -- The inverse extension is also the identity off the support.
      rw [hkInverseOutside hx, id_eq, dist_self]
      exact hε

end FiniteClosedCellPatch

/-- Helper for Theorem 63.6: composing a finite supported correction after an
ambient homeomorphism has displacement controlled in target cells and their
old inverse images. -/
theorem refineAmbientHomeomorphInFiniteCells
    {X : Type u} [PseudoMetricSpace X] {n : ℕ}
    (h : X ≃ₜ X) (P : FiniteClosedCellPatch X n) (ε : ℝ)
    (hε : 0 ≤ ε)
    (htargetBounded : ∀ i, Bornology.IsBounded (P.cell i))
    (htargetDiam : ∀ i, Metric.diam (P.cell i) ≤ ε)
    (hsourceBounded : ∀ i, Bornology.IsBounded (h.symm '' P.cell i))
    (hsourceDiam : ∀ i, Metric.diam (h.symm '' P.cell i) ≤ ε) :
    ∃ h' : X ≃ₜ X,
      (∀ x, h x ∈ P.support → h' x = P.forward (h x)) ∧
        (∀ x, h x ∉ P.support → h' x = h x) ∧
        (∀ x, dist (h' x) (h x) ≤ ε) ∧
        ∀ y, dist (h'.symm y) (h.symm y) ≤ ε := by
  obtain ⟨k, hkForward, hkInverse, hkOutside, hkInverseOutside⟩ :=
    P.existsSupportedHomeomorph
  let h' := h.trans k
  refine ⟨h', ?_, ?_, ?_, ?_⟩
  · -- On the pulled-back support, composition applies the patch forward map.
    intro x hx
    exact hkForward hx
  · -- Away from the pulled-back support, the correction is the identity.
    intro x hx
    exact hkOutside hx
  · intro x
    by_cases hx : h x ∈ P.support
    · -- Choose the target cell containing `h x` and apply its mesh bound.
      have hxSupport := hx
      rw [P.support_eq_iUnion] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      simp only [h', Homeomorph.trans_apply]
      calc
        dist (k (h x)) (h x) = dist (P.forward (h x)) (h x) :=
          congrArg (fun y ↦ dist y (h x)) (hkForward hxSupport)
        _ ≤ Metric.diam (P.cell i) :=
          Metric.dist_le_diam_of_mem (htargetBounded i) (P.forward_cell i hxi) hxi
        _ ≤ ε := htargetDiam i
    · -- Outside the support the correction contributes no forward displacement.
      simp only [h', Homeomorph.trans_apply]
      rw [hkOutside hx, id_eq, dist_self]
      exact hε
  · intro y
    by_cases hy : y ∈ P.support
    · -- Both old inverse images lie in the inverse image of one target cell.
      have hySupport := hy
      rw [P.support_eq_iUnion] at hy
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
      have hkyi : k.symm y ∈ P.cell i := by
        rw [hkInverse hySupport]
        exact P.inverse_cell i hyi
      calc
        dist (h'.symm y) (h.symm y) = dist (h.symm (k.symm y)) (h.symm y) := rfl
        _ ≤ Metric.diam (h.symm '' P.cell i) :=
          Metric.dist_le_diam_of_mem (hsourceBounded i)
            (Set.mem_image_of_mem h.symm hkyi) (Set.mem_image_of_mem h.symm hyi)
        _ ≤ ε := hsourceDiam i
    · -- The inverse correction is the identity outside the support.
      simp only [h', Homeomorph.symm_trans_apply]
      rw [hkInverseOutside hy, id_eq, dist_self]
      exact hε

end Schoenflies
