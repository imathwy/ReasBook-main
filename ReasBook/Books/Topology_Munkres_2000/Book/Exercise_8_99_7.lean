module

public import Mathlib.Topology.Separation.CompletelyRegular
public import Topology_Munkres_2000.Book.Definition_8_99_1

public section

universe u

/-- Exercise 8.99.7: A locally `m`-Euclidean space is Hausdorff if and only if it is
completely regular in Munkres's sense. -/
theorem hausdorff_iff_completelyRegular {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] : T2Space X ↔ T35Space X := by
  -- The chart model canonically supplies local compactness, but mathlib exposes the transfer
  -- as a theorem rather than an instance.
  -- Local instance justification (proof-local temporary data): installs that derived structure.
  letI : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) X
  constructor
  · intro hT2
    letI : T2Space X := hT2
    have hCompletelyRegular : CompletelyRegularSpace X :=
      CompletelyRegularSpace.mk fun x K hK hxK ↦ by
      -- A compactly supported bump at `x` vanishes on `K`; subtracting it from one
      -- gives the required complete-regularity separator.
        obtain ⟨f, hfx, _hfCompact, hfSupport, _hfRange⟩ :=
          exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton
            hK.isOpen_compl (Set.singleton_subset_iff.mpr hxK)
        refine ⟨fun y ↦ unitInterval.symm ⟨f y, _hfRange y⟩,
          unitInterval.continuous_symm.comp (Continuous.subtype_mk f.continuous _hfRange), ?_, ?_⟩
        · have hfxOne : (⟨f x, _hfRange x⟩ : unitInterval) = 1 := Subtype.ext (hfx rfl)
          simp [hfxOne]
        · intro y hy
          have hyNotSupport : y ∉ Function.support f := fun hySupport ↦
            (hfSupport (subset_tsupport f hySupport)) hy
          have hfy : f y = 0 := not_ne_iff.mp hyNotSupport
          have hfyZero : (⟨f y, _hfRange y⟩ : unitInterval) = 0 := Subtype.ext hfy
          simp [hfyZero]
    letI : CompletelyRegularSpace X := hCompletelyRegular
    exact @T35Space.mk X _ inferInstance hCompletelyRegular
  · intro hT35
    letI : T35Space X := hT35
    infer_instance
