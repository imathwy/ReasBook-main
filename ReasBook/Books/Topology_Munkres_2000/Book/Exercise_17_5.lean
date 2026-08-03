module

public import Topology_Munkres_2000.Book.Definition_14_3.OrderBasis

public section

open Set

universe u

variable {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]

/-- The inclusion part of Exercise 17.5: in the order topology, the closure of an
open interval `Ioo a b` is contained in the corresponding closed interval `Icc a b`. -/
theorem closure_Ioo_subset_Icc (a b : X) : closure (Ioo a b) ⊆ Icc a b := by
  -- Enclose the interval in the closed set `Icc a b`, then use minimality of closure.
  exact closure_minimal Ioo_subset_Icc_self isClosed_Icc

/-- Helper for Exercise 17.5: the left endpoint lies in `closure (Ioo a b)` exactly
when interval points occur below every point strictly above it. -/
lemma leftEndpoint_mem_closure_Ioo_iff (a b : X) (hab : a < b) :
    a ∈ closure (Ioo a b) ↔ ∀ c, a < c → (Ioo a b ∩ Iio c).Nonempty := by
  constructor
  · intro ha c hac
    -- Test closure membership against the basic left ray neighborhood `Iio c`.
    obtain ⟨x, hxc, hxab⟩ :=
      mem_closure_iff_nhds.mp ha (Iio c) (Iio_mem_nhds hac)
    exact ⟨x, hxab, hxc⟩
  · intro hdense
    rw [mem_closure_iff_nhds]
    intro s hs
    -- Refine the arbitrary neighborhood to a half-open interval on the right of `a`.
    obtain ⟨c, hac, hcs⟩ := exists_Ico_subset_of_mem_nhds hs ⟨b, hab⟩
    obtain ⟨x, hxab, hxc⟩ := hdense c hac
    exact ⟨x, hcs ⟨hxab.1.le, hxc⟩, hxab⟩

/-- Helper for Exercise 17.5: the right endpoint lies in `closure (Ioo a b)` exactly
when interval points occur above every point strictly below it. -/
lemma rightEndpoint_mem_closure_Ioo_iff (a b : X) (hab : a < b) :
    b ∈ closure (Ioo a b) ↔ ∀ c, c < b → (Ioo a b ∩ Ioi c).Nonempty := by
  constructor
  · intro hb c hcb
    -- Test closure membership against the basic right ray neighborhood `Ioi c`.
    obtain ⟨x, hxc, hxab⟩ :=
      mem_closure_iff_nhds.mp hb (Ioi c) (Ioi_mem_nhds hcb)
    exact ⟨x, hxab, hxc⟩
  · intro hdense
    rw [mem_closure_iff_nhds]
    intro s hs
    -- Refine the arbitrary neighborhood to a half-open interval on the left of `b`.
    obtain ⟨c, hcb, hcs⟩ := exists_Ioc_subset_of_mem_nhds hs ⟨a, hab⟩
    obtain ⟨x, hxab, hxc⟩ := hdense c hcb
    exact ⟨x, hcs ⟨hxc, hxab.2.le⟩, hxab⟩

/-- Exercise 17.5: For `a < b`, the closure of `Ioo a b` equals `Icc a b`
exactly when points of `Ioo a b` occur arbitrarily close to `a` from the right and
to `b` from the left. -/
theorem closure_Ioo_eq_Icc_iff_dense_at_endpoints (a b : X) (hab : a < b) :
    closure (Ioo a b) = Icc a b ↔
      (∀ c, a < c → (Ioo a b ∩ Iio c).Nonempty) ∧
        ∀ c, c < b → (Ioo a b ∩ Ioi c).Nonempty := by
  constructor
  · intro hclosure
    -- Equality puts both endpoints in the closure, so the endpoint interfaces apply.
    have ha : a ∈ closure (Ioo a b) := by
      rw [hclosure]
      exact left_mem_Icc.2 hab.le
    have hb : b ∈ closure (Ioo a b) := by
      rw [hclosure]
      exact right_mem_Icc.2 hab.le
    exact ⟨(leftEndpoint_mem_closure_Ioo_iff a b hab).mp ha,
      (rightEndpoint_mem_closure_Ioo_iff a b hab).mp hb⟩
  · intro hdense
    apply Subset.antisymm (closure_Ioo_subset_Icc a b)
    -- The open interval is already in its closure, so only the two endpoints remain.
    rw [← sdiff_subset_closure_iff, Icc_sdiff_Ioo_same hab.le]
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨(leftEndpoint_mem_closure_Ioo_iff a b hab).mpr hdense.1,
      (rightEndpoint_mem_closure_Ioo_iff a b hab).mpr hdense.2⟩
