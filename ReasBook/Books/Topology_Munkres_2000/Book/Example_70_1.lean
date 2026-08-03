module

public import Topology_Munkres_2000.Book.Corollary_70_3
public import Topology_Munkres_2000.Book.Definition_64_2.ThetaSpace
public import Topology_Munkres_2000.Book.Exercise_58_1
public import Topology_Munkres_2000.Book.Exercise_51_3.Contractible
public import Topology_Munkres_2000.Book.Lemma_69_1
public import Topology_Munkres_2000.Book.Theorem_18_3.Pasting
public import Topology_Munkres_2000.Book.Theorem_58_3
public import Topology_Munkres_2000.Book.Theorem_58_7
public import Topology_Munkres_2000.Book.Theorem_63_6.CrosscutSplit

public section

universe u

namespace Set.IsDeformationRetract

/-- Helper for Example 70.1: a deformation retract transports along a homeomorphism. -/
lemma imageHomeomorph
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {A : Set Y}
    (hA : Set.IsDeformationRetract A) (e : Y ≃ₜ Z) :
    Set.IsDeformationRetract (e '' A) := by
  -- Conjugate both the endpoint retraction and its relative homotopy by `e`.
  rw [Set.isDeformationRetract_iff] at hA ⊢
  obtain ⟨rA, ⟨H⟩⟩ := hA
  have himage (z : Z) : e (rA.apply (e.symm z)) ∈ e '' A := by
    exact ⟨rA.apply (e.symm z), (rA.apply (e.symm z)).2, rfl⟩
  have hrContinuous :
      Continuous (fun z : Z ↦
        (⟨e (rA.apply (e.symm z)), himage z⟩ : (e '' A))) := by
    apply Continuous.subtype_mk
    exact e.continuous.comp
      (continuous_subtype_val.comp
        (rA.toContinuousMap.continuous.comp e.symm.continuous))
  have hrLeftInverse :
      Function.LeftInverse
        (fun z : Z ↦ (⟨e (rA.apply (e.symm z)), himage z⟩ : (e '' A)))
        Subtype.val := by
    intro z
    rcases z.2 with ⟨a, ha, haz⟩
    apply Subtype.ext
    change e (rA.apply (e.symm (z : Z))) = (z : Z)
    rw [← haz, e.symm_apply_apply]
    exact congrArg e (congrArg Subtype.val (rA.leftInverse ⟨a, ha⟩))
  let r : Set.Retraction (e '' A) :=
    ⟨⟨fun z ↦ (⟨e (rA.apply (e.symm z)), himage z⟩ : (e '' A)), hrContinuous⟩,
      hrLeftInverse⟩
  have K : ContinuousMap.HomotopyRel (ContinuousMap.id Z) r.toAmbient (e '' A) := by
    refine ⟨?_, ?_⟩
    · refine ⟨⟨fun p ↦ e (H (p.1, e.symm p.2)), ?_⟩, ?_, ?_⟩
      · exact e.continuous.comp
          (H.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
      · intro z
        calc
          e (H (0, e.symm z)) = e (e.symm z) := congrArg e (H.apply_zero (e.symm z))
          _ = z := e.apply_symm_apply z
      · intro z
        apply congrArg e
        exact H.apply_one (e.symm z)
    · intro s z hz
      rcases hz with ⟨a, ha, haz⟩
      change e (H (s, e.symm z)) = z
      rw [← haz, e.symm_apply_apply]
      exact congrArg e (H.eq_fst s ha)
  exact ⟨r, ⟨K⟩⟩

/-- Helper for Example 70.1: a deformation retraction on one member of a closed cover,
relative to its overlap with the other member, extends by the identity. -/
lemma ofClosedCover
    {Y : Type*} [TopologicalSpace Y] {C D : Set Y}
    (hCD : Set.IsDeformationRetract (Subtype.val ⁻¹' C : Set D))
    (hC : IsClosed C) (hD : IsClosed D) (hcover : C ∪ D = Set.univ) :
    Set.IsDeformationRetract C := by
  -- Paste the endpoint map to the identity on `C`.
  rw [Set.isDeformationRetract_iff] at hCD
  obtain ⟨rD, ⟨HDrel⟩⟩ := hCD
  let HD : Set.DeformationRetraction (Subtype.val ⁻¹' C : Set D) := ⟨rD, HDrel⟩
  let leftEndpoint : C(C, Y) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hRightEndpointContinuous :
      Continuous (fun d : D ↦ ((HD.toRetraction.apply d : D) : Y)) := by
    exact continuous_subtype_val.comp
      (continuous_subtype_val.comp HD.toRetraction.toContinuousMap.continuous)
  let rightEndpoint : C(D, Y) :=
    ⟨fun d ↦ (HD.toRetraction.apply d : D),
      hRightEndpointContinuous⟩
  have hEndpointAgree (x : (C ∩ D : Set Y)) :
      leftEndpoint ⟨x, x.2.1⟩ = rightEndpoint ⟨x, x.2.2⟩ := by
    change (x : Y) = ((HD.toRetraction.apply ⟨x, x.2.2⟩ : D) : Y)
    exact (congrArg (fun z : D ↦ (z : Y))
      (congrArg Subtype.val (HD.toRetraction.leftInverse ⟨⟨x, x.2.2⟩, x.2.1⟩))).symm
  let endpoint : C(Y, Y) :=
    ContinuousMap.pasteClosed hC hD hcover leftEndpoint rightEndpoint hEndpointAgree
  have hEndpointMem (y : Y) : endpoint y ∈ C := by
    have hycover : y ∈ C ∪ D := by
      rw [hcover]
      exact Set.mem_univ y
    rcases hycover with hyC | hyD
    · rw [ContinuousMap.pasteClosed_apply_left hC hD hcover leftEndpoint rightEndpoint
          hEndpointAgree ⟨y, hyC⟩]
      exact hyC
    · rw [ContinuousMap.pasteClosed_apply_right hC hD hcover leftEndpoint rightEndpoint
          hEndpointAgree ⟨y, hyD⟩]
      exact (HD.toRetraction.apply ⟨y, hyD⟩).2
  have hrLeftInverse :
      Function.LeftInverse (fun y : Y ↦ (⟨endpoint y, hEndpointMem y⟩ : C))
        Subtype.val := by
    intro c
    apply Subtype.ext
    exact ContinuousMap.pasteClosed_apply_left hC hD hcover leftEndpoint rightEndpoint
      hEndpointAgree c
  let r : Set.Retraction C :=
    ⟨⟨fun y ↦ ⟨endpoint y, hEndpointMem y⟩,
      endpoint.continuous.subtype_mk hEndpointMem⟩, hrLeftInverse⟩
  -- Paste the original homotopy on `D` to the stationary homotopy on `C`.
  let cylinderC : Set (unitInterval × Y) := Prod.snd ⁻¹' C
  let cylinderD : Set (unitInterval × Y) := Prod.snd ⁻¹' D
  have hCylinderC : IsClosed cylinderC := hC.preimage continuous_snd
  have hCylinderD : IsClosed cylinderD := hD.preimage continuous_snd
  have hCylinderCover : cylinderC ∪ cylinderD = Set.univ := by
    ext p
    simpa only [cylinderC, cylinderD, Set.mem_union, Set.mem_preimage, Set.mem_univ,
      iff_true] using (Set.ext_iff.mp hcover p.2).mpr (Set.mem_univ p.2)
  let leftHomotopy : C(cylinderC, Y) :=
    ⟨fun p ↦ p.1.2, continuous_snd.comp continuous_subtype_val⟩
  have hCylinderDMem (p : cylinderD) : p.1.2 ∈ D := p.2
  have hRightHomotopyContinuous :
      Continuous (fun p : cylinderD ↦
        ((HD.toHomotopyRel (p.1.1, ⟨p.1.2, hCylinderDMem p⟩) : D) : Y)) := by
    exact continuous_subtype_val.comp
      (HD.toHomotopyRel.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk hCylinderDMem)))
  let rightHomotopy : C(cylinderD, Y) :=
    ⟨fun p ↦ (HD.toHomotopyRel (p.1.1, ⟨p.1.2, hCylinderDMem p⟩) : D),
      hRightHomotopyContinuous⟩
  have hHomotopyAgree (p : (cylinderC ∩ cylinderD : Set (unitInterval × Y))) :
      leftHomotopy ⟨p, p.2.1⟩ = rightHomotopy ⟨p, p.2.2⟩ := by
    change p.1.2 = (HD.toHomotopyRel (p.1.1, ⟨p.1.2, p.2.2⟩) : D)
    exact (congrArg (fun z : D ↦ (z : Y))
      (HD.toHomotopyRel.eq_fst p.1.1 (x := ⟨p.1.2, p.2.2⟩) p.2.1)).symm
  let homotopyMap : C(unitInterval × Y, Y) :=
    ContinuousMap.pasteClosed hCylinderC hCylinderD hCylinderCover
      leftHomotopy rightHomotopy hHomotopyAgree
  have hHomotopyZero (y : Y) : homotopyMap (0, y) = y := by
    have hycover : y ∈ C ∪ D := by
      rw [hcover]
      exact Set.mem_univ y
    rcases hycover with hyC | hyD
    · calc
        homotopyMap (0, y) = leftHomotopy ⟨(0, y), hyC⟩ := by
          simpa only [homotopyMap] using
            ContinuousMap.pasteClosed_apply_left hCylinderC hCylinderD hCylinderCover
              leftHomotopy rightHomotopy hHomotopyAgree ⟨(0, y), hyC⟩
        _ = y := rfl
    · calc
        homotopyMap (0, y) = rightHomotopy ⟨(0, y), hyD⟩ := by
          simpa only [homotopyMap] using
            ContinuousMap.pasteClosed_apply_right hCylinderC hCylinderD hCylinderCover
              leftHomotopy rightHomotopy hHomotopyAgree ⟨(0, y), hyD⟩
        _ = y := congrArg (fun z : D ↦ (z : Y))
          (HD.toHomotopyRel.apply_zero ⟨y, hyD⟩)
  have hHomotopyOne (y : Y) : homotopyMap (1, y) = endpoint y := by
    have hycover : y ∈ C ∪ D := by
      rw [hcover]
      exact Set.mem_univ y
    rcases hycover with hyC | hyD
    · calc
        homotopyMap (1, y) = leftHomotopy ⟨(1, y), hyC⟩ := by
          simpa only [homotopyMap] using
            ContinuousMap.pasteClosed_apply_left hCylinderC hCylinderD hCylinderCover
              leftHomotopy rightHomotopy hHomotopyAgree ⟨(1, y), hyC⟩
        _ = y := rfl
        _ = endpoint y := (ContinuousMap.pasteClosed_apply_left hC hD hcover
          leftEndpoint rightEndpoint hEndpointAgree ⟨y, hyC⟩).symm
    · calc
        homotopyMap (1, y) = rightHomotopy ⟨(1, y), hyD⟩ := by
          simpa only [homotopyMap] using
            ContinuousMap.pasteClosed_apply_right hCylinderC hCylinderD hCylinderCover
              leftHomotopy rightHomotopy hHomotopyAgree ⟨(1, y), hyD⟩
        _ = rightEndpoint ⟨y, hyD⟩ := congrArg (fun z : D ↦ (z : Y))
          (HD.toHomotopyRel.apply_one ⟨y, hyD⟩)
        _ = endpoint y := (ContinuousMap.pasteClosed_apply_right hC hD hcover
          leftEndpoint rightEndpoint hEndpointAgree ⟨y, hyD⟩).symm
  have hHomotopyFixed (s : unitInterval) (y : Y) (hyC : y ∈ C) :
      homotopyMap (s, y) = y := by
    calc
      homotopyMap (s, y) = leftHomotopy ⟨(s, y), hyC⟩ := by
        simpa only [homotopyMap] using
          ContinuousMap.pasteClosed_apply_left hCylinderC hCylinderD hCylinderCover
            leftHomotopy rightHomotopy hHomotopyAgree ⟨(s, y), hyC⟩
      _ = y := rfl
  have K : ContinuousMap.HomotopyRel (ContinuousMap.id Y) r.toAmbient C := by
    refine ⟨⟨homotopyMap, hHomotopyZero, ?_⟩, hHomotopyFixed⟩
    intro y
    exact hHomotopyOne y
  rw [Set.isDeformationRetract_iff]
  exact ⟨r, ⟨K⟩⟩

end Set.IsDeformationRetract

/-- Helper for Example 70.1: removing an interior point from `unitInterval` deformation
retracts the remaining two components onto their endpoints. -/
private lemma puncturedUnitInterval_endpoints_isDeformationRetract
    (t : unitInterval) :
    Set.IsDeformationRetract
      (Subtype.val ⁻¹' ({0, 1} : Set unitInterval) : Set ({t}ᶜ : Set unitInterval)) := by
  -- Split the punctured interval into its two closed order components.
  let Y : Set unitInterval := {t}ᶜ
  let A : Set Y := Subtype.val ⁻¹' ({0, 1} : Set unitInterval)
  let L : Set Y := {x | (x : unitInterval) ≤ t}
  let R : Set Y := {x | t ≤ (x : unitInterval)}
  have hL : IsClosed L := by
    exact isClosed_Iic.preimage continuous_subtype_val
  have hR : IsClosed R := by
    exact isClosed_Ici.preimage continuous_subtype_val
  have hcover : L ∪ R = Set.univ := by
    ext x
    simp only [L, R, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total (x : unitInterval) t
  let cylinderL : Set (unitInterval × Y) := Prod.snd ⁻¹' L
  let cylinderR : Set (unitInterval × Y) := Prod.snd ⁻¹' R
  have hCylinderL : IsClosed cylinderL := hL.preimage continuous_snd
  have hCylinderR : IsClosed cylinderR := hR.preimage continuous_snd
  have hCylinderCover : cylinderL ∪ cylinderR = Set.univ := by
    ext p
    simpa only [cylinderL, cylinderR, Set.mem_union, Set.mem_preimage, Set.mem_univ,
      iff_true] using (Set.ext_iff.mp hcover p.2).mpr (Set.mem_univ p.2)
  -- Convex combinations on either side stay strictly on that side of the puncture.
  have hleftMem (p : cylinderL) :
      Set.Icc.convexComb (p.1.2 : unitInterval) 0 p.1.1 ∈ Y := by
    have hxne : p.1.2 ≠ t := by
      simpa only [Y, Set.mem_compl_iff, Set.mem_singleton_iff] using p.1.2.2
    have hxt : (p.1.2 : unitInterval) < t := lt_of_le_of_ne p.2 hxne
    have hzeroLe : (0 : unitInterval) ≤ p.1.2 := by
      change (0 : ℝ) ≤ ((p.1.2 : unitInterval) : ℝ)
      exact (p.1.2 : unitInterval).2.1
    have hconvexLe :
        Set.Icc.convexComb (p.1.2 : unitInterval) 0 p.1.1 ≤ p.1.2 := by
      rw [← Set.Icc.convexComb_symm]
      exact Set.Icc.convexComb_le hzeroLe _
    have hvalue : Set.Icc.convexComb (p.1.2 : unitInterval) 0 p.1.1 < t :=
      lt_of_le_of_lt hconvexLe hxt
    simpa only [Y, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq,
      Subtype.ext_iff] using hvalue.ne
  have hrightMem (p : cylinderR) :
      Set.Icc.convexComb (p.1.2 : unitInterval) 1 p.1.1 ∈ Y := by
    have hxne : p.1.2 ≠ t := by
      simpa only [Y, Set.mem_compl_iff, Set.mem_singleton_iff] using p.1.2.2
    have htx : t < (p.1.2 : unitInterval) := lt_of_le_of_ne p.2 hxne.symm
    have hxOne : p.1.2 ≤ (1 : unitInterval) := by
      change (((p.1.2 : unitInterval) : ℝ) ≤ 1)
      exact (p.1.2 : unitInterval).2.2
    have hxLeConvex :
        p.1.2 ≤ Set.Icc.convexComb (p.1.2 : unitInterval) 1 p.1.1 := by
      exact Set.Icc.le_convexComb hxOne _
    have hvalue : t < Set.Icc.convexComb (p.1.2 : unitInterval) 1 p.1.1 :=
      lt_of_lt_of_le htx hxLeConvex
    simpa only [Y, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq,
      Subtype.ext_iff] using hvalue.ne'
  have hleftContinuous :
      Continuous (fun p : cylinderL ↦
        (⟨Set.Icc.convexComb p.1.2 0 p.1.1, hleftMem p⟩ : Y)) := by
    apply Continuous.subtype_mk
    exact Set.Icc.continuous_convexComb_prod.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).prodMk
        (continuous_const.prodMk (continuous_fst.comp continuous_subtype_val)))
  have hrightContinuous :
      Continuous (fun p : cylinderR ↦
        (⟨Set.Icc.convexComb p.1.2 1 p.1.1, hrightMem p⟩ : Y)) := by
    apply Continuous.subtype_mk
    exact Set.Icc.continuous_convexComb_prod.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).prodMk
        (continuous_const.prodMk (continuous_fst.comp continuous_subtype_val)))
  let leftHomotopy : C(cylinderL, Y) :=
    ⟨fun p ↦ ⟨Set.Icc.convexComb p.1.2 0 p.1.1, hleftMem p⟩, hleftContinuous⟩
  let rightHomotopy : C(cylinderR, Y) :=
    ⟨fun p ↦ ⟨Set.Icc.convexComb p.1.2 1 p.1.1, hrightMem p⟩, hrightContinuous⟩
  have hHomotopyAgree
      (p : (cylinderL ∩ cylinderR : Set (unitInterval × Y))) :
      leftHomotopy ⟨p, p.2.1⟩ = rightHomotopy ⟨p, p.2.2⟩ := by
    have hxt : p.1.2 = t := le_antisymm p.2.1 p.2.2
    exact False.elim (p.1.2.2 (Set.mem_singleton_iff.mpr hxt))
  let homotopyMap : C(unitInterval × Y, Y) :=
    ContinuousMap.pasteClosed hCylinderL hCylinderR hCylinderCover
      leftHomotopy rightHomotopy hHomotopyAgree
  have hzero (y : Y) : homotopyMap (0, y) = y := by
    rcases le_total (y : unitInterval) t with hyL | hyR
    · have hpaste : homotopyMap (0, y) = leftHomotopy ⟨(0, y), hyL⟩ := by
        simpa only [homotopyMap] using
          ContinuousMap.pasteClosed_apply_left hCylinderL hCylinderR hCylinderCover
            leftHomotopy rightHomotopy hHomotopyAgree ⟨(0, y), hyL⟩
      rw [hpaste]
      apply Subtype.ext
      dsimp only [leftHomotopy]
      exact Set.Icc.convexComb_zero (y : unitInterval) 0
    · have hpaste : homotopyMap (0, y) = rightHomotopy ⟨(0, y), hyR⟩ := by
        simpa only [homotopyMap] using
          ContinuousMap.pasteClosed_apply_right hCylinderL hCylinderR hCylinderCover
            leftHomotopy rightHomotopy hHomotopyAgree ⟨(0, y), hyR⟩
      rw [hpaste]
      apply Subtype.ext
      dsimp only [rightHomotopy]
      exact Set.Icc.convexComb_zero (y : unitInterval) 1
  have honeMem (y : Y) : homotopyMap (1, y) ∈ A := by
    rcases le_total (y : unitInterval) t with hyL | hyR
    · have hpaste : homotopyMap (1, y) = leftHomotopy ⟨(1, y), hyL⟩ := by
        simpa only [homotopyMap] using
          ContinuousMap.pasteClosed_apply_left hCylinderL hCylinderR hCylinderCover
            leftHomotopy rightHomotopy hHomotopyAgree ⟨(1, y), hyL⟩
      rw [hpaste]
      apply Set.mem_insert_iff.mpr
      left
      dsimp only [leftHomotopy]
      exact Set.Icc.convexComb_one (y : unitInterval) 0
    · have hpaste : homotopyMap (1, y) = rightHomotopy ⟨(1, y), hyR⟩ := by
        simpa only [homotopyMap] using
          ContinuousMap.pasteClosed_apply_right hCylinderL hCylinderR hCylinderCover
            leftHomotopy rightHomotopy hHomotopyAgree ⟨(1, y), hyR⟩
      rw [hpaste]
      apply Set.mem_insert_iff.mpr
      right
      apply Set.mem_singleton_iff.mpr
      dsimp only [rightHomotopy]
      exact Set.Icc.convexComb_one (y : unitInterval) 1
  have hfixed (s : unitInterval) (y : Y) (hy : y ∈ A) : homotopyMap (s, y) = y := by
    rcases Set.mem_insert_iff.mp hy with hyzero | hyone
    · have hyL : y ∈ L := by
        have hzeroLe : (0 : unitInterval) ≤ t := by
          change (0 : ℝ) ≤ (t : ℝ)
          exact t.2.1
        simpa only [L, Set.mem_setOf_eq, hyzero] using hzeroLe
      have hpaste : homotopyMap (s, y) = leftHomotopy ⟨(s, y), hyL⟩ := by
        simpa only [homotopyMap] using
          ContinuousMap.pasteClosed_apply_left hCylinderL hCylinderR hCylinderCover
            leftHomotopy rightHomotopy hHomotopyAgree ⟨(s, y), hyL⟩
      rw [hpaste]
      apply Subtype.ext
      change Set.Icc.convexComb (y : unitInterval) 0 s = (y : unitInterval)
      rw [hyzero, Set.Icc.convexComb_eq]
    · have hyone' : (y : unitInterval) = 1 := Set.mem_singleton_iff.mp hyone
      have hyR : y ∈ R := by
        have honeGe : t ≤ (1 : unitInterval) := by
          change (t : ℝ) ≤ 1
          exact t.2.2
        simpa only [R, Set.mem_setOf_eq, hyone'] using honeGe
      have hpaste : homotopyMap (s, y) = rightHomotopy ⟨(s, y), hyR⟩ := by
        simpa only [homotopyMap] using
          ContinuousMap.pasteClosed_apply_right hCylinderL hCylinderR hCylinderCover
            leftHomotopy rightHomotopy hHomotopyAgree ⟨(s, y), hyR⟩
      rw [hpaste]
      apply Subtype.ext
      change Set.Icc.convexComb (y : unitInterval) 1 s = (y : unitInterval)
      rw [hyone', Set.Icc.convexComb_eq]
  have hrContinuous :
      Continuous (fun y : Y ↦ (⟨homotopyMap (1, y), honeMem y⟩ : A)) := by
    apply Continuous.subtype_mk
    exact homotopyMap.continuous.comp (continuous_const.prodMk continuous_id)
  have hrLeftInverse :
      Function.LeftInverse (fun y : Y ↦ (⟨homotopyMap (1, y), honeMem y⟩ : A))
        Subtype.val := by
    intro a
    apply Subtype.ext
    exact hfixed 1 a a.2
  let r : Set.Retraction A :=
    ⟨⟨fun y ↦ ⟨homotopyMap (1, y), honeMem y⟩, hrContinuous⟩, hrLeftInverse⟩
  have H : ContinuousMap.HomotopyRel (ContinuousMap.id Y) r.toAmbient A := by
    refine ⟨⟨homotopyMap, hzero, ?_⟩, ?_⟩
    · intro y
      rfl
    · exact hfixed
  have hResult : Set.IsDeformationRetract A := by
    rw [Set.isDeformationRetract_iff]
    exact ⟨r, ⟨H⟩⟩
  simpa only [A, Y] using hResult

/-- Helper for Example 70.1: path-connectedness passes from the source to the target of a
homotopy equivalence. -/
private lemma pathConnectedSpace_target_of_homotopyEquiv
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [PathConnectedSpace Y]
    (e : ContinuousMap.HomotopyEquiv Y Z) : PathConnectedSpace Z := by
  -- Join target points through inverse images, using the inverse homotopy at both ends.
  classical
  obtain ⟨H⟩ := e.right_inv
  refine ⟨⟨e (Classical.choice (inferInstance : Nonempty Y))⟩, ?_⟩
  intro z₀ z₁
  let middle := (PathConnectedSpace.somePath (e.symm z₀) (e.symm z₁)).map e.continuous
  exact ⟨(H.evalAt z₀).symm |>.trans middle |>.trans (H.evalAt z₁)⟩

/-- Helper for Example 70.1: a space deforming onto a circle is path connected. -/
private lemma pathConnectedSpaceOfCircleDeformationRetract
    {Y : Type*} [TopologicalSpace Y] (A : Set Y)
    (hA : Set.IsDeformationRetract A) (e : A ≃ₜ Circle) : PathConnectedSpace Y := by
  -- First transport circle path-connectedness to the retract, then across the deformation.
  let hPathA : PathConnectedSpace A :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  obtain ⟨hEquiv⟩ := hA.nonempty_homotopyEquiv
  exact @pathConnectedSpace_target_of_homotopyEquiv A Y _ _ hPathA hEquiv

/-- Helper for Example 70.1: a space deforming onto an interval is simply connected. -/
private lemma simplyConnectedSpaceOfIntervalDeformationRetract
    {Y : Type*} [TopologicalSpace Y] (A : Set Y)
    (hA : Set.IsDeformationRetract A) (e : A ≃ₜ unitInterval) :
    SimplyConnectedSpace Y := by
  -- Contractibility passes first to the interval core and then to the ambient space.
  let hContractibleA : ContractibleSpace A := e.contractibleSpace
  obtain ⟨hEquiv⟩ := hA.nonempty_homotopyEquiv
  let hContractibleY : ContractibleSpace Y :=
    @ContinuousMap.HomotopyEquiv.contractibleSpace Y A _ _ hContractibleA hEquiv.symm
  exact @SimplyConnectedSpace.ofContractible Y _ hContractibleY

/-- Helper for Example 70.1: a deformation retract homeomorphic to `Circle` gives a
one-generator free basis of the ambient fundamental group. -/
private lemma freeBasisOfCircleDeformationRetract
    {Y : Type u} [TopologicalSpace Y] (A : Set Y)
    (hA : Set.IsDeformationRetract A) (e : A ≃ₜ Circle) (a : A) :
    Nonempty (FreeGroupBasis PUnit (FundamentalGroup Y (a : Y))) := by
  -- Give the retract integer coordinates and turn its homotopy equivalence into coordinates.
  rw [Set.isDeformationRetract_iff] at hA
  obtain ⟨r, ⟨H⟩⟩ := hA
  let deformation : Set.DeformationRetraction A := ⟨r, H⟩
  let hEquiv : ContinuousMap.HomotopyEquiv A Y :=
    Set.DeformationRetraction.toHomotopyEquiv deformation
  have hinclusionPoint : hEquiv a = (a : Y) := by
    exact Set.DeformationRetraction.toHomotopyEquiv_apply deformation a
  let inclusion : FundamentalGroup A a ≃* FundamentalGroup Y (a : Y) :=
    MulEquiv.ofBijective (FundamentalGroup.mapOfEq hEquiv.toFun hinclusionPoint)
      (hEquiv.fundamentalGroupMapOfEq_bijective a (a : Y) hinclusionPoint)
  let circleCoordinates : FundamentalGroup A a ≃* Multiplicative ℤ :=
    (e.fundamentalGroupMulEquiv a).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e a) 1).trans
        Circle.fundamentalGroupEquivInt)
  let repr : FundamentalGroup Y (a : Y) ≃* FreeGroup PUnit :=
    inclusion.symm.trans
      (circleCoordinates.trans (FreeGroup.mulEquivIntOfUnique (α := PUnit)).symm)
  exact ⟨FreeGroupBasis.ofRepr repr⟩

namespace FreeGroupBasis

/-- Helper for Example 70.1: the binary free product of groups with chosen free bases has
the sum of their basis types as a free basis. -/
lemma nonempty_coprod
    {ι κ G H : Type u} [Group G] [Group H]
    (bG : FreeGroupBasis ι G) (bH : FreeGroupBasis κ H) :
    Nonempty (FreeGroupBasis (ι ⊕ κ) (Monoid.Coprod G H)) := by
  -- Verify the universal extension property by lifting independently out of both factors.
  let generators : ι ⊕ κ → Monoid.Coprod G H :=
    Sum.elim (fun i ↦ Monoid.Coprod.inl (bG i))
      (fun k ↦ Monoid.Coprod.inr (bH k))
  have hUniversal :
      ∀ {K : Type u} [Group K] (y : ι ⊕ κ → K),
        ∃! f : Monoid.Coprod G H →* K, ∀ i, f (generators i) = y i := by
    intro K _ y
    let leftMap : G →* K := bG.lift (fun i ↦ y (Sum.inl i))
    let rightMap : H →* K := bH.lift (fun k ↦ y (Sum.inr k))
    let extension : Monoid.Coprod G H →* K := Monoid.Coprod.lift leftMap rightMap
    refine ⟨extension, ?_, ?_⟩
    · rintro (i | k)
      · exact congr_fun (bG.lift.symm_apply_apply (fun j ↦ y (Sum.inl j))) i
      · exact congr_fun (bH.lift.symm_apply_apply (fun j ↦ y (Sum.inr j))) k
    · intro f hf
      apply Monoid.Coprod.hom_ext
      · apply bG.ext_hom
        intro i
        calc
          (f.comp Monoid.Coprod.inl) (bG i) = y (Sum.inl i) := by
            simpa only [MonoidHom.comp_apply, generators, Sum.elim_inl] using
              hf (Sum.inl i)
          _ = leftMap (bG i) :=
            (congr_fun (bG.lift.symm_apply_apply (fun j ↦ y (Sum.inl j))) i).symm
          _ = (extension.comp Monoid.Coprod.inl) (bG i) := by rfl
      · apply bH.ext_hom
        intro k
        calc
          (f.comp Monoid.Coprod.inr) (bH k) = y (Sum.inr k) := by
            simpa only [MonoidHom.comp_apply, generators, Sum.elim_inr] using
              hf (Sum.inr k)
          _ = rightMap (bH k) :=
            (congr_fun (bH.lift.symm_apply_apply (fun j ↦ y (Sum.inr j))) k).symm
          _ = (extension.comp Monoid.Coprod.inr) (bH k) := by rfl
  have hBasisWithValues :
      ∃ basis : FreeGroupBasis (ι ⊕ κ) (Monoid.Coprod G H),
        ∀ i, basis i = generators i :=
    (existsFreeGroupBasis_iff_uniqueExtension generators).2 hUniversal
  obtain ⟨basis, _⟩ := hBasisWithValues
  exact ⟨basis⟩

end FreeGroupBasis

namespace Topology.ThetaPresentation

/-- Helper for Example 70.1: an interior point of one theta edge does not lie on a
different edge. -/
private lemma interiorPoint_not_mem_otherEdge
    {X : Type u} [TopologicalSpace X] (P : Topology.ThetaPresentation X)
    (i j : Fin 3) (hij : i ≠ j) (t : unitInterval) (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    P.arc i t ∉ P.edge j := by
  -- Pairwise edge intersection forces any shared point to be a common endpoint.
  intro hOther
  have hSelf : P.arc i t ∈ P.edge i := by
    rw [P.edge_eq_range]
    exact ⟨t, rfl⟩
  have hEndpoint : P.arc i t ∈ ({P.initial, P.terminal} : Set X) := by
    rw [← P.edge_inter_edge i j hij]
    exact ⟨hSelf, hOther⟩
  rcases Set.mem_insert_iff.mp hEndpoint with hInitial | hTerminal
  · apply ht₀
    apply (P.isEmbedding i).injective
    rw [P.map_zero]
    exact hInitial
  · apply ht₁
    apply (P.isEmbedding i).injective
    rw [P.map_one]
    exact Set.mem_singleton_iff.mp hTerminal

/-- Helper for Example 70.1: a punctured theta edge, viewed inside any ambient subspace
containing the rest of that edge, deformation retracts onto its two endpoints. -/
private lemma puncturedEdgePiece_deformationRetractsEndpoints
    {X : Type u} [TopologicalSpace X] (P : Topology.ThetaPresentation X)
    (i : Fin 3) (t : unitInterval) (ht₀ : t ≠ 0) (ht₁ : t ≠ 1)
    (Y : Set X)
    (hEdgeSubset : ∀ {x : X}, x ∈ P.edge i → x ≠ P.arc i t → x ∈ Y)
    (hPuncture : P.arc i t ∉ Y) :
    let D : Set Y := Subtype.val ⁻¹' P.edge i
    let E : Set D := Subtype.val ⁻¹'
      (Subtype.val ⁻¹' ({P.initial, P.terminal} : Set X) : Set Y)
    Set.IsDeformationRetract E := by
  -- Use the edge embedding as coordinates on the punctured edge piece.
  dsimp only
  let T : Set unitInterval := {t}ᶜ
  let D : Set Y := Subtype.val ⁻¹' P.edge i
  let E : Set D := Subtype.val ⁻¹'
    (Subtype.val ⁻¹' ({P.initial, P.terminal} : Set X) : Set Y)
  have hArcNe (z : T) : P.arc i z ≠ P.arc i t := by
    intro h
    apply z.2
    exact Set.mem_singleton_iff.mpr ((P.isEmbedding i).injective h)
  have hForwardY (z : T) : P.arc i z ∈ Y := by
    apply hEdgeSubset
    · rw [P.edge_eq_range]
      exact ⟨z, rfl⟩
    · exact hArcNe z
  have hForwardEdge (z : T) :
      P.arc i z ∈ P.edge i := by
    rw [P.edge_eq_range]
    exact ⟨z, rfl⟩
  let edgeHomeomorph : unitInterval ≃ₜ Set.range (P.arc i) :=
    (P.isEmbedding i).toHomeomorph
  have hRange (d : D) : (d : X) ∈ Set.range (P.arc i) := by
    rw [← P.edge_eq_range]
    exact d.2
  let rangePoint (d : D) : Set.range (P.arc i) := ⟨(d : X), hRange d⟩
  let coordinate (d : D) : unitInterval := edgeHomeomorph.symm (rangePoint d)
  have hCoordinateSpec (d : D) : P.arc i (coordinate d) = (d : X) := by
    change ((edgeHomeomorph (coordinate d) : Set.range (P.arc i)) : X) = (d : X)
    exact congrArg Subtype.val (edgeHomeomorph.apply_symm_apply (rangePoint d))
  have hCoordinateNe (d : D) : coordinate d ≠ t := by
    intro h
    apply hPuncture
    have hpoint : P.arc i t = (d : X) := by
      rw [← hCoordinateSpec d, h]
    rw [hpoint]
    exact d.1.2
  let forward (z : T) : D :=
    ⟨⟨P.arc i z, hForwardY z⟩, hForwardEdge z⟩
  let inverse (d : D) : T := ⟨coordinate d, hCoordinateNe d⟩
  have hForwardContinuous : Continuous forward := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (P.arc i).continuous.comp continuous_subtype_val
  have hRangePointContinuous : Continuous rangePoint := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  have hInverseContinuous : Continuous inverse := by
    apply Continuous.subtype_mk
    exact edgeHomeomorph.symm.continuous.comp hRangePointContinuous
  have hLeftInverse : Function.LeftInverse inverse forward := by
    intro z
    apply Subtype.ext
    apply (P.isEmbedding i).injective
    exact hCoordinateSpec (forward z)
  have hRightInverse : Function.RightInverse inverse forward := by
    intro d
    apply Subtype.ext
    apply Subtype.ext
    exact hCoordinateSpec d
  let edgeCoordinates : T ≃ₜ D :=
    ⟨⟨forward, inverse, hLeftInverse, hRightInverse⟩,
      hForwardContinuous, hInverseContinuous⟩
  have hInterval := puncturedUnitInterval_endpoints_isDeformationRetract t
  have hTransported :=
    Set.IsDeformationRetract.imageHomeomorph hInterval edgeCoordinates
  have hImage :
      edgeCoordinates ''
          (Subtype.val ⁻¹' ({0, 1} : Set unitInterval) : Set T) = E := by
    ext d
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases Set.mem_insert_iff.mp hz with hz₀ | hz₁
      · left
        rw [← P.map_zero i]
        exact congrArg (P.arc i) hz₀
      · right
        rw [← P.map_one i]
        exact congrArg (P.arc i) (Set.mem_singleton_iff.mp hz₁)
    · intro hd
      rcases Set.mem_insert_iff.mp hd with hd₀ | hd₁
      · have hzeroT : (0 : unitInterval) ∈ T := by
          simpa only [T, Set.mem_compl_iff, Set.mem_singleton_iff] using ht₀.symm
        let z : T := ⟨0, hzeroT⟩
        have hzEndpoint : z ∈
            (Subtype.val ⁻¹' ({0, 1} : Set unitInterval) : Set T) := by
          exact Set.mem_insert_iff.mpr (Or.inl rfl)
        refine ⟨z, hzEndpoint, ?_⟩
        change forward z = d
        apply Subtype.ext
        apply Subtype.ext
        change P.arc i (z : unitInterval) = (d : X)
        rw [show (z : unitInterval) = 0 from rfl]
        rw [P.map_zero]
        exact hd₀.symm
      · have honeT : (1 : unitInterval) ∈ T := by
          simpa only [T, Set.mem_compl_iff, Set.mem_singleton_iff] using ht₁.symm
        let z : T := ⟨1, honeT⟩
        have hzEndpoint : z ∈
            (Subtype.val ⁻¹' ({0, 1} : Set unitInterval) : Set T) := by
          exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
        refine ⟨z, hzEndpoint, ?_⟩
        change forward z = d
        apply Subtype.ext
        apply Subtype.ext
        change P.arc i (z : unitInterval) = (d : X)
        rw [show (z : unitInterval) = 1 from rfl]
        rw [P.map_one]
        exact (Set.mem_singleton_iff.mp hd₁).symm
  have hResult : Set.IsDeformationRetract E := hImage ▸ hTransported
  simpa only [E, D] using hResult

/-- Helper for Example 70.1: deleting an interior point of one theta edge deformation
retracts the complement onto the circle formed by the other two edges. -/
private lemma puncturedEdgeDeformationRetractsCircleCore
    {X : Type u} [TopologicalSpace X] [T2Space X] (P : Topology.ThetaPresentation X)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : unitInterval) (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    let U : Set X := {P.arc i t}ᶜ
    let A : Set U := Subtype.val ⁻¹' (P.edge j ∪ P.edge k)
    Set.IsDeformationRetract A ∧ Nonempty (A ≃ₜ Circle) := by
  dsimp only
  constructor
  · -- Cover the punctured theta space by the retained circle and the punctured edge.
    let U : Set X := {P.arc i t}ᶜ
    let C : Set U := Subtype.val ⁻¹' (P.edge j ∪ P.edge k)
    let D : Set U := Subtype.val ⁻¹' P.edge i
    have hEdgeClosed (r : Fin 3) : IsClosed (P.edge r) := by
      rw [P.edge_eq_range]
      exact (isCompact_range (P.arc r).continuous).isClosed
    have hC : IsClosed C := by
      exact ((hEdgeClosed j).union (hEdgeClosed k)).preimage continuous_subtype_val
    have hD : IsClosed D := by
      exact (hEdgeClosed i).preimage continuous_subtype_val
    have hcover : C ∪ D = Set.univ := by
      ext x
      simp only [C, D, Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
      have hxAll : (x : X) ∈ ⋃ r : Fin 3, P.edge r := by
        rw [P.iUnion_edge]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.mp hxAll with ⟨r, hr⟩
      have hrCases : r = i ∨ r = j ∨ r = k := by omega
      rcases hrCases with rfl | rfl | rfl
      · exact Or.inr hr
      · exact Or.inl (Or.inl hr)
      · exact Or.inl (Or.inr hr)
    have hEdgeSubset :
        ∀ {x : X}, x ∈ P.edge i → x ≠ P.arc i t → x ∈ U := by
      intro x _ hx
      simpa only [U, Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hPuncture : P.arc i t ∉ U := by
      intro h
      exact h rfl
    have hEndpoints :=
      P.puncturedEdgePiece_deformationRetractsEndpoints
        i t ht₀ ht₁ U hEdgeSubset hPuncture
    have hOverlap :
        (Subtype.val ⁻¹' C : Set D) =
          (Subtype.val ⁻¹'
            (Subtype.val ⁻¹' ({P.initial, P.terminal} : Set X) : Set U) : Set D) := by
      ext d
      constructor
      · intro hd
        rcases hd with hdj | hdk
        · rw [← P.edge_inter_edge i j hij]
          exact ⟨d.2, hdj⟩
        · rw [← P.edge_inter_edge i k hik]
          exact ⟨d.2, hdk⟩
      · intro hd
        left
        have hdi : (d : X) ∈ P.edge i := d.2
        have hinter : (d : X) ∈ P.edge i ∩ P.edge j := by
          rwa [P.edge_inter_edge i j hij]
        exact hinter.2
    have hCD : Set.IsDeformationRetract (Subtype.val ⁻¹' C : Set D) := by
      rw [hOverlap]
      exact hEndpoints
    have hResult : Set.IsDeformationRetract C :=
      Set.IsDeformationRetract.ofClosedCover hCD hC hD hcover
    simpa only [C, U] using hResult
  · -- First identify the retained core inside the punctured subtype with its ambient copy.
    have hCoreSubset : P.edge j ∪ P.edge k ⊆ ({P.arc i t}ᶜ : Set X) := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hxp
      rcases hx with hxj | hxk
      · exact P.interiorPoint_not_mem_otherEdge i j hij t ht₀ ht₁ (hxp ▸ hxj)
      · exact P.interiorPoint_not_mem_otherEdge i k hik t ht₀ ht₁ (hxp ▸ hxk)
    have hCoreRange :
        P.edge j ∪ P.edge k ⊆
          Set.range (Subtype.val : ({P.arc i t}ᶜ : Set X) → X) := by
      intro x hx
      exact ⟨⟨x, hCoreSubset hx⟩, rfl⟩
    let nestedToCore :=
      Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hCoreRange
    -- The two retained parameterized edges form a circle by the embedded-path theorem.
    let alpha : Path P.initial P.terminal :=
      ⟨P.arc j, P.map_zero j, P.map_one j⟩
    let betaForward : Path P.initial P.terminal :=
      ⟨P.arc k, P.map_zero k, P.map_one k⟩
    have hAlpha : Topology.IsEmbedding alpha := P.isEmbedding j
    have hBeta : Topology.IsEmbedding betaForward.symm :=
      (P.isEmbedding k).comp unitInterval.symmHomeomorph.isEmbedding
    have hAlphaRange : Set.range alpha = P.edge j := by
      rw [P.edge_eq_range]
      apply congrArg Set.range
      funext x
      rfl
    have hBetaRange : Set.range betaForward = P.edge k := by
      rw [P.edge_eq_range]
      apply congrArg Set.range
      funext x
      rfl
    have hInter :
        Set.range alpha ∩ Set.range betaForward.symm = {P.initial, P.terminal} := by
      rw [Path.symm_range, hAlphaRange, hBetaRange]
      exact P.edge_inter_edge j k hjk
    obtain ⟨coreCircle⟩ :=
      embeddedPathsUnion_homeomorphicCircle alpha betaForward.symm hAlpha hBeta hInter
    have hCoreEq :
        Set.range alpha ∪ Set.range betaForward.symm = P.edge j ∪ P.edge k := by
      rw [Path.symm_range, hAlphaRange, hBetaRange]
    let coreToPathUnion :
        ↥(P.edge j ∪ P.edge k) ≃ₜ ↥(Set.range alpha ∪ Set.range betaForward.symm) :=
      Homeomorph.setCongr hCoreEq.symm
    exact ⟨nestedToCore.trans (coreToPathUnion.trans coreCircle)⟩

/-- Helper for Example 70.1: deleting interior points of two theta edges deformation
retracts the complement onto the remaining interval edge. -/
private lemma twoPunctureComplementDeformationRetractsIntervalCore
    {X : Type u} [TopologicalSpace X] [T2Space X] (P : Topology.ThetaPresentation X)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t : unitInterval) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    let W : Set X := {P.arc i s}ᶜ ∩ {P.arc j t}ᶜ
    let A : Set W := Subtype.val ⁻¹' P.edge k
    Set.IsDeformationRetract A ∧ Nonempty (A ≃ₜ unitInterval) := by
  dsimp only
  constructor
  · -- First collapse the `j`-edge while fixing the union of the `k`- and `i`-edges.
    let W : Set X := {P.arc i s}ᶜ ∩ {P.arc j t}ᶜ
    let K : Set W := Subtype.val ⁻¹' P.edge k
    let I : Set W := Subtype.val ⁻¹' P.edge i
    let J : Set W := Subtype.val ⁻¹' P.edge j
    let A : Set W := K ∪ I
    have hEdgeClosed (r : Fin 3) : IsClosed (P.edge r) := by
      rw [P.edge_eq_range]
      exact (isCompact_range (P.arc r).continuous).isClosed
    have hK : IsClosed K := (hEdgeClosed k).preimage continuous_subtype_val
    have hI : IsClosed I := (hEdgeClosed i).preimage continuous_subtype_val
    have hJ : IsClosed J := (hEdgeClosed j).preimage continuous_subtype_val
    have hA : IsClosed A := hK.union hI
    have hcover : A ∪ J = Set.univ := by
      ext x
      simp only [A, K, I, J, Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
      have hxAll : (x : X) ∈ ⋃ r : Fin 3, P.edge r := by
        rw [P.iUnion_edge]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.mp hxAll with ⟨r, hr⟩
      have hrCases : r = i ∨ r = j ∨ r = k := by omega
      rcases hrCases with rfl | rfl | rfl
      · exact Or.inl (Or.inr hr)
      · exact Or.inr hr
      · exact Or.inl (Or.inl hr)
    have hEdgeSubsetI :
        ∀ {x : X}, x ∈ P.edge i → x ≠ P.arc i s → x ∈ W := by
      intro x hxi hxpuncture
      constructor
      · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxpuncture
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hxj
        exact P.interiorPoint_not_mem_otherEdge j i hij.symm t ht₀ ht₁ (hxj ▸ hxi)
    have hEdgeSubsetJ :
        ∀ {x : X}, x ∈ P.edge j → x ≠ P.arc j t → x ∈ W := by
      intro x hxj hxpuncture
      constructor
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hxi
        exact P.interiorPoint_not_mem_otherEdge i j hij s hs₀ hs₁ (hxi ▸ hxj)
      · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxpuncture
    have hPunctureI : P.arc i s ∉ W := by
      intro h
      exact h.1 rfl
    have hPunctureJ : P.arc j t ∉ W := by
      intro h
      exact h.2 rfl
    have hIEndpoints :=
      P.puncturedEdgePiece_deformationRetractsEndpoints
        i s hs₀ hs₁ W hEdgeSubsetI hPunctureI
    have hJEndpoints :=
      P.puncturedEdgePiece_deformationRetractsEndpoints
        j t ht₀ ht₁ W hEdgeSubsetJ hPunctureJ
    have hJOverlap :
        (Subtype.val ⁻¹' A : Set J) =
          (Subtype.val ⁻¹'
            (Subtype.val ⁻¹' ({P.initial, P.terminal} : Set X) : Set W) : Set J) := by
      ext d
      constructor
      · intro hd
        rcases hd with hdk | hdi
        · rw [← P.edge_inter_edge j k hjk]
          exact ⟨d.2, hdk⟩
        · rw [← P.edge_inter_edge j i hij.symm]
          exact ⟨d.2, hdi⟩
      · intro hd
        left
        have hinter : (d : X) ∈ P.edge j ∩ P.edge k := by
          rwa [P.edge_inter_edge j k hjk]
        exact hinter.2
    have hAJ : Set.IsDeformationRetract (Subtype.val ⁻¹' A : Set J) := by
      rw [hJOverlap]
      exact hJEndpoints
    have hStageOne : Set.IsDeformationRetract A :=
      Set.IsDeformationRetract.ofClosedCover hAJ hA hJ hcover
    -- Within the first retract, transport the `i`-edge contraction to its nested copy.
    let K' : Set A := Subtype.val ⁻¹' K
    let I' : Set A := Subtype.val ⁻¹' I
    have hK' : IsClosed K' := hK.preimage continuous_subtype_val
    have hI' : IsClosed I' := hI.preimage continuous_subtype_val
    have hcover' : K' ∪ I' = Set.univ := by
      ext x
      rcases x.2 with hxK | hxI
      · exact iff_of_true (Or.inl hxK) (Set.mem_univ x)
      · exact iff_of_true (Or.inr hxI) (Set.mem_univ x)
    have hIRange : I ⊆ Set.range (Subtype.val : A → W) := by
      intro x hxI
      exact ⟨⟨x, Or.inr hxI⟩, rfl⟩
    let nestedI : I' ≃ₜ I :=
      Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hIRange
    let edgeIntoStage : I ≃ₜ I' := nestedI.symm
    have hNestedCoe (d : I) : ((edgeIntoStage d : A) : W) = (d : W) := by
      exact congrArg Subtype.val (nestedI.apply_symm_apply d)
    have hITransported :=
      Set.IsDeformationRetract.imageHomeomorph hIEndpoints edgeIntoStage
    have hIImage :
        edgeIntoStage ''
            (Subtype.val ⁻¹'
              (Subtype.val ⁻¹' ({P.initial, P.terminal} : Set X) : Set W) : Set I) =
          (Subtype.val ⁻¹' K' : Set I') := by
      ext d
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxEndpoint : (x : X) ∈ ({P.initial, P.terminal} : Set X) := hx
        have hinter : (x : X) ∈ P.edge i ∩ P.edge k := by
          rwa [P.edge_inter_edge i k hik]
        simpa only [K', K, Set.mem_preimage, hNestedCoe] using hinter.2
      · intro hdK
        let x : I := nestedI d
        have hxCoe : (x : W) = ((d : A) : W) := by
          exact Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe
            Topology.IsEmbedding.subtypeVal hIRange d
        have hxEndpoint : (x : X) ∈ ({P.initial, P.terminal} : Set X) := by
          rw [← P.edge_inter_edge i k hik]
          constructor
          · exact x.2
          · simpa only [K', K, Set.mem_preimage, ← hxCoe] using hdK
        refine ⟨x, hxEndpoint, ?_⟩
        exact nestedI.symm_apply_apply d
    have hKI : Set.IsDeformationRetract (Subtype.val ⁻¹' K' : Set I') := by
      rw [← hIImage]
      exact hITransported
    have hStageTwo : Set.IsDeformationRetract K' :=
      Set.IsDeformationRetract.ofClosedCover hKI hK' hI' hcover'
    have hKSubsetA : K ⊆ A := fun _ hx ↦ Or.inl hx
    have hResult : Set.IsDeformationRetract K :=
      Set.IsDeformationRetract.trans hStageOne hKSubsetA hStageTwo
    simpa only [K, W] using hResult
  · -- The remaining edge avoids both punctures and hence embeds into their complement.
    have hCoreSubset :
        P.edge k ⊆ ({P.arc i s}ᶜ ∩ {P.arc j t}ᶜ : Set X) := by
      intro x hx
      constructor
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hxp
        exact P.interiorPoint_not_mem_otherEdge i k hik s hs₀ hs₁ (hxp ▸ hx)
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hxp
        exact P.interiorPoint_not_mem_otherEdge j k hjk t ht₀ ht₁ (hxp ▸ hx)
    have hCoreRange :
        P.edge k ⊆ Set.range
          (Subtype.val : ({P.arc i s}ᶜ ∩ {P.arc j t}ᶜ : Set X) → X) := by
      intro x hx
      exact ⟨⟨x, hCoreSubset hx⟩, rfl⟩
    let nestedToCore :=
      Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hCoreRange
    -- The edge embedding supplies canonical interval coordinates on the core.
    let edgeToInterval : ↥(P.edge k) ≃ₜ unitInterval :=
      (Homeomorph.setCongr (P.edge_eq_range k)).trans (P.isEmbedding k).toHomeomorph.symm
    exact ⟨nestedToCore.trans edgeToInterval⟩

end Topology.ThetaPresentation

/-- Example 70.1. The fundamental group of a theta space admits a free basis on two
generators. -/
theorem fundamentalGroup_freeBasis_of_thetaSpace
    {X : Type u} [TopologicalSpace X] [Topology.IsThetaSpace X] (x₀ : X) :
    Nonempty (FreeGroupBasis (Fin 2) (FundamentalGroup X x₀)) := by
  -- Choose two interior punctures and form the source proof's two-set cover.
  classical
  obtain ⟨P⟩ := Topology.IsThetaSpace.presentation (X := X)
  have hmidpoint : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  let m : unitInterval := ⟨1 / 2, hmidpoint⟩
  have hm₀ : m ≠ 0 := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num [m] at hval
  have hm₁ : m ≠ 1 := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num [m] at hval
  let a : X := P.arc 0 m
  let b : X := P.arc 1 m
  let U : Set X := {a}ᶜ
  let V : Set X := {b}ᶜ
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have ha_ne_b : a ≠ b := by
    intro hab
    have haEdgeZero : a ∈ P.edge 0 := by
      rw [P.edge_eq_range]
      exact ⟨m, rfl⟩
    have haEdgeOne : a ∈ P.edge 1 := by
      rw [P.edge_eq_range]
      exact ⟨m, hab.symm⟩
    have haEndpoint : a ∈ ({P.initial, P.terminal} : Set X) := by
      rw [← P.edge_inter_edge 0 1 h01]
      exact ⟨haEdgeZero, haEdgeOne⟩
    rcases Set.mem_insert_iff.mp haEndpoint with haInitial | haTerminal
    · apply hm₀
      apply (P.isEmbedding 0).injective
      rw [P.map_zero]
      simpa only [a] using haInitial
    · have haTerminal' := Set.mem_singleton_iff.mp haTerminal
      apply hm₁
      apply (P.isEmbedding 0).injective
      rw [P.map_one]
      simpa only [a] using haTerminal'
  have hUOpen : IsOpen U := by
    exact isClosed_singleton.isOpen_compl
  have hVOpen : IsOpen V := by
    exact isClosed_singleton.isOpen_compl
  have hcover : U ∪ V = Set.univ := by
    ext x
    simp only [U, V, Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    by_cases hxa : x = a
    · right
      intro hxb
      exact ha_ne_b (hxa.symm.trans hxb)
    · exact Or.inl hxa
  have hinitial_ne_a : P.initial ≠ a := by
    intro h
    apply hm₀
    apply (P.isEmbedding 0).injective
    rw [P.map_zero]
    simpa only [a] using h.symm
  have hinitial_ne_b : P.initial ≠ b := by
    intro h
    apply hm₀
    apply (P.isEmbedding 1).injective
    rw [P.map_zero]
    simpa only [b] using h.symm
  have hinitial : P.initial ∈ U ∩ V := by
    exact ⟨hinitial_ne_a, hinitial_ne_b⟩
  -- Invoke the geometric interfaces before transporting their homotopy consequences.
  have hCircleU :=
    P.puncturedEdgeDeformationRetractsCircleCore 0 1 2 h01 h02 h12 m hm₀ hm₁
  have hCircleV :=
    P.puncturedEdgeDeformationRetractsCircleCore 1 0 2 h01.symm h12 h02 m hm₀ hm₁
  have hInterval :=
    P.twoPunctureComplementDeformationRetractsIntervalCore
      0 1 2 h01 h02 h12 m m hm₀ hm₁ hm₀ hm₁
  have hCircleU' :
      Set.IsDeformationRetract
          (Subtype.val ⁻¹' (P.edge 1 ∪ P.edge 2) : Set U) ∧
        Nonempty
          ((Subtype.val ⁻¹' (P.edge 1 ∪ P.edge 2) : Set U) ≃ₜ Circle) := by
    simpa only [U, a] using hCircleU
  have hCircleV' :
      Set.IsDeformationRetract
          (Subtype.val ⁻¹' (P.edge 0 ∪ P.edge 2) : Set V) ∧
        Nonempty
          ((Subtype.val ⁻¹' (P.edge 0 ∪ P.edge 2) : Set V) ≃ₜ Circle) := by
    simpa only [V, b] using hCircleV
  have hInterval' :
      Set.IsDeformationRetract
          (Subtype.val ⁻¹' P.edge 2 : Set ↥(U ∩ V)) ∧
        Nonempty
          ((Subtype.val ⁻¹' P.edge 2 : Set ↥(U ∩ V)) ≃ₜ unitInterval) := by
    simpa only [U, V, a, b] using hInterval
  obtain ⟨eCircleU⟩ := hCircleU'.2
  obtain ⟨eCircleV⟩ := hCircleV'.2
  obtain ⟨eInterval⟩ := hInterval'.2
  -- Local instance justification (geometric transport): these instances depend on the
  -- chosen punctures and on the supplied deformation-retraction witnesses.
  letI : PathConnectedSpace U :=
    pathConnectedSpaceOfCircleDeformationRetract _ hCircleU'.1 eCircleU
  letI : PathConnectedSpace V :=
    pathConnectedSpaceOfCircleDeformationRetract _ hCircleV'.1 eCircleV
  letI : SimplyConnectedSpace (U ∩ V : Set X) :=
    simplyConnectedSpaceOfIntervalDeformationRetract _ hInterval'.1 eInterval
  -- Choose the common endpoint in both circle cores and construct their rank-one bases.
  have hinitialEdgeZero : P.initial ∈ P.edge 0 := by
    rw [P.edge_eq_range]
    exact ⟨0, P.map_zero 0⟩
  have hinitialEdgeOne : P.initial ∈ P.edge 1 := by
    rw [P.edge_eq_range]
    exact ⟨0, P.map_zero 1⟩
  have hinitialCoreU :
      (⟨P.initial, hinitial.1⟩ : U) ∈
        (Subtype.val ⁻¹' (P.edge 1 ∪ P.edge 2) : Set U) :=
    Set.mem_union_left _ hinitialEdgeOne
  have hinitialCoreV :
      (⟨P.initial, hinitial.2⟩ : V) ∈
        (Subtype.val ⁻¹' (P.edge 0 ∪ P.edge 2) : Set V) :=
    Set.mem_union_left _ hinitialEdgeZero
  let corePointU : (Subtype.val ⁻¹' (P.edge 1 ∪ P.edge 2) : Set U) :=
    ⟨⟨P.initial, hinitial.1⟩, hinitialCoreU⟩
  let corePointV : (Subtype.val ⁻¹' (P.edge 0 ∪ P.edge 2) : Set V) :=
    ⟨⟨P.initial, hinitial.2⟩, hinitialCoreV⟩
  have hBasisU :
      Nonempty (FreeGroupBasis PUnit
        (FundamentalGroup U ⟨P.initial, hinitial.1⟩)) := by
    simpa only [corePointU] using
      freeBasisOfCircleDeformationRetract _ hCircleU'.1 eCircleU corePointU
  have hBasisV :
      Nonempty (FreeGroupBasis PUnit
        (FundamentalGroup V ⟨P.initial, hinitial.2⟩)) := by
    simpa only [corePointV] using
      freeBasisOfCircleDeformationRetract _ hCircleV'.1 eCircleV corePointV
  obtain ⟨basisU⟩ := hBasisU
  obtain ⟨basisV⟩ := hBasisV
  obtain ⟨coproductBasis⟩ := FreeGroupBasis.nonempty_coprod basisU basisV
  obtain ⟨vanKampenEquiv, _⟩ :=
    exists_vanKampenMulEquiv U V P.initial hinitial hUOpen hVOpen hcover
  let indexEquiv : (PUnit ⊕ PUnit) ≃ Fin 2 :=
    (finTwoEquiv.trans Equiv.boolEquivPUnitSumPUnit).symm
  let basisAtInitial : FreeGroupBasis (Fin 2) (FundamentalGroup X P.initial) :=
    (coproductBasis.map vanKampenEquiv).reindex indexEquiv
  -- The path-connected cover supplies the final basepoint change to `x₀`.
  have hUPath : IsPathConnected U := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hVPath : IsPathConnected V := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hXPath : IsPathConnected (Set.univ : Set X) := by
    rw [← hcover]
    exact hUPath.union hVPath ⟨P.initial, hinitial⟩
  -- Local instance justification (cover transport): this instance is derived from the
  -- chosen path-connected cover and is needed only for canonical basepoint change.
  letI : PathConnectedSpace X := pathConnectedSpace_iff_univ.mpr hXPath
  exact ⟨basisAtInitial.map
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected P.initial x₀)⟩

/-- The fundamental group of a theta space is free. -/
instance fundamentalGroup_isFree_of_thetaSpace
    {X : Type u} [TopologicalSpace X] [Topology.IsThetaSpace X] (x₀ : X) :
    IsFreeGroup (FundamentalGroup X x₀) where
  nonempty_basis :=
    ⟨ULift.{u} (Fin 2),
      (fundamentalGroup_freeBasis_of_thetaSpace x₀).map
        (fun basis ↦ basis.reindex Equiv.ulift.symm)⟩

end
