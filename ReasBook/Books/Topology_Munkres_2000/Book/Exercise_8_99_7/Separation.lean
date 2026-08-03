module

public import Mathlib.Topology.Separation.CompletelyRegular

public section

universe u

namespace LocallyCompactSpace

/-- In a locally compact space, Hausdorffness is equivalent to complete regularity together
with the `T₀` separation axiom. -/
theorem t2Space_iff_t35Space {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] :
    T2Space X ↔ T35Space X := by
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

end LocallyCompactSpace
