module

public import Topology_Munkres_2000.Book.Definition_7_1.CountablyInfinite

public section

/-- Lemma 7.2. If `C` is an infinite subset of `ℕ+`, then `C` is countably infinite. -/
theorem Set.Infinite.countablyInfinite {C : Set ℕ+} (hC : C.Infinite) :
    C.CountablyInfinite := by
  have hD : Nonempty (Denumerable C) :=
    Set.countable_infinite_iff_nonempty_denumerable.mp ⟨Set.to_countable C, hC⟩
  exact hD.elim (fun d ↦ Set.CountablyInfinite.ofEquiv (d.eqv.trans Equiv.pnatEquivNat.symm))
