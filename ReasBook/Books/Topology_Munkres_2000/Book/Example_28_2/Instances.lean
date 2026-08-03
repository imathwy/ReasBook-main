module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Topology_Munkres_2000.Book.Theorem_10_3
public import Mathlib.Topology.Order.Compact

public section

open Ordinal

namespace OpenOmegaOne

/-- Helper for Example 28.2: every point of `OpenOmegaOne` has a strictly larger point. -/
lemma exists_gt (a : OpenOmegaOne) : ∃ b : OpenOmegaOne, a < b := by
  -- The ordinal successor of `a` remains below the first uncountable ordinal.
  have hsucc : Order.succ (a : Ordinal) < ω₁ :=
    Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) a.property
  -- Package that successor as another countable ordinal.
  have hlt : (a : Ordinal) < Order.succ (a : Ordinal) := Order.lt_succ (a : Ordinal)
  refine ⟨⟨Order.succ (a : Ordinal), hsucc⟩, ?_⟩
  exact hlt

/-- Helper for Example 28.2: every closed initial interval of `OpenOmegaOne` is compact. -/
lemma isCompact_Iic (b : OpenOmegaOne) : IsCompact (Set.Iic b) := by
  -- Transport compactness to the ambient ordinal space through the subtype embedding.
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  -- The ambient image is exactly the compact ordinal interval from `0` to `b`.
  have himage : ((fun x : OpenOmegaOne ↦ (x : Ordinal)) '' Set.Iic b) =
      Set.Icc 0 (b : Ordinal) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨bot_le, ha⟩
    · intro hx
      have hlt : x < ω₁ := lt_of_le_of_lt hx.2 b.property
      refine ⟨⟨x, hlt⟩, hx.2, rfl⟩
  rw [himage]
  exact isCompact_Icc

/-- Helper for Example 28.2: every countably infinite subset of `OpenOmegaOne` has an
accumulation point. -/
lemma accPt_of_countable_infinite_bounded {B : Set OpenOmegaOne} (hBcountable : B.Countable)
    (hBinfinite : B.Infinite) : ∃ x, AccPt x (Filter.principal B) := by
  -- Countability supplies an upper bound, so `B` lies in a compact initial interval.
  obtain ⟨b, hb⟩ := bddAbove_of_countable B hBcountable
  have hBsub : B ⊆ Set.Iic b := hb
  -- Countable compactness of that interval gives an accumulation point of `B`.
  obtain ⟨x, _, hx⟩ :=
    (isCompact_Iic b).isCountablyCompact.exists_accPt_of_infinite hBsub hBinfinite
  exact ⟨x, hx⟩

/-- The open first-uncountable ordinal is not compact. -/
instance instNoncompactSpace : NoncompactSpace OpenOmegaOne := by
  -- A compact space would make the identity attain a greatest value.
  rw [← not_compactSpace_iff]
  intro hcompact
  letI : CompactSpace OpenOmegaOne := hcompact
  obtain ⟨a, _, ha⟩ :=
    isCompact_univ.exists_isMaxOn
      (Set.univ_nonempty : (Set.univ : Set OpenOmegaOne).Nonempty)
      continuous_id.continuousOn
  -- The successor helper contradicts that alleged greatest point.
  obtain ⟨b, hab⟩ := exists_gt a
  exact (not_le_of_gt hab) (ha (Set.mem_univ b))

/-- The open first-uncountable ordinal is limit point compact. -/
instance instLimitPointCompactSpace : LimitPointCompactSpace OpenOmegaOne := by
  refine ⟨fun A hA ↦ ?_⟩
  -- Choose a countably infinite subset, following the source proof.
  obtain ⟨B, hBA, hBcountable, hBinfinite⟩ := hA.exists_subset_countable_infinite
  obtain ⟨x, hx⟩ := accPt_of_countable_infinite_bounded hBcountable hBinfinite
  -- An accumulation point of `B` is also one of its superset `A`.
  exact ⟨x, hx.mono (Filter.principal_mono.mpr hBA)⟩

end OpenOmegaOne

end
