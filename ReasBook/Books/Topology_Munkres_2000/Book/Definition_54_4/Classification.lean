module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

universe u

/-- A group is infinite cyclic exactly when it is isomorphic to the additive
group of integers. -/
theorem isCyclic_infinite_iff_nonempty_equiv_int {G : Type u} [Group G] :
    (IsCyclic G ∧ Infinite G) ↔ Nonempty (G ≃* Multiplicative ℤ) := by
  constructor
  · rintro ⟨h_cyclic, h_infinite⟩
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp h_cyclic
    refine ⟨(MulEquiv.ofBijective (zpowersHom G g) ?_).symm⟩
    refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, MonoidHom.range_eq_top.mp hg⟩
    simp [zpowersHom_ker_eq, ← infinite_zpowers, hg,
      Set.infinite_univ_iff.mpr h_infinite]
  · rintro ⟨e⟩
    exact ⟨e.isCyclic.mpr inferInstance, Infinite.of_injective e.symm e.symm.injective⟩

/-- A group is cyclic of order `k` exactly when it is isomorphic to the
additive group of integers modulo `k`. For `k = 0`, this is the infinite cyclic
case. -/
theorem isCyclic_card_eq_iff_nonempty_equiv_zmod {G : Type u} [Group G] {k : ℕ} :
    (IsCyclic G ∧ Nat.card G = k) ↔ Nonempty (G ≃* Multiplicative (ZMod k)) := by
  constructor
  · rintro ⟨h_cyclic, h_card⟩
    exact ⟨(zmodCyclicMulEquiv h_cyclic).symm.trans <| h_card ▸ MulEquiv.refl _⟩
  · rintro ⟨e⟩
    exact ⟨e.isCyclic.mpr inferInstance, by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]⟩

end
