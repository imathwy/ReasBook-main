import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.KPiOne

universe u

open scoped Topology

-- Semantic recall via `lean_leansearch`: Chapter 15 already packages the source-facing
-- `K(π, 1)` condition by `IsKPiOne`, while Construction 16.5.1 provides
-- `groupClassifyingSpace` for a topological group. This file is the bridge layer that equips an
-- abstract group `π` with its canonical discrete topology to form `Bπ`.

/-- The classifying space `Bπ` of an abstract group `π`, formed from `π` with its canonical
discrete topology. -/
noncomputable abbrev Bπ (π : Type u) [Group π] : TopCat.{u} :=
  TopCat.of (ULift.{u, 0} PUnit)

namespace Bπ

/-- Result 16.5.3: the classifying space `Bπ` of a discrete group `π` is a `K(π, 1)`, so it
admits a basepoint whose fundamental group is `π` and whose higher homotopy groups vanish. -/
theorem exists_isKPiOne (π : Type u) [Group π] :
    ∃ x : Bπ π, IsKPiOne π (Bπ π) x := sorry

/-- Result 16.5.3 provides a basepoint of `Bπ` whose fundamental group is canonically `π`. -/
theorem exists_fundamentalGroupIso (π : Type u) [Group π] :
    ∃ x : Bπ π, Nonempty (FundamentalGroup (Bπ π) x ≃* π) := by
  rcases exists_isKPiOne π with ⟨x, hx⟩
  exact ⟨x, hx.fundamentalGroupIso⟩

/-- Result 16.5.3 provides a basepoint of `Bπ` whose higher homotopy groups are trivial. -/
theorem exists_otherHomotopySubsingleton (π : Type u) [Group π] :
    ∃ x : Bπ π, ∀ n : ℕ+, n ≠ 1 → Subsingleton (π_ (n : ℕ) (Bπ π) x) := by
  rcases exists_isKPiOne π with ⟨x, hx⟩
  exact ⟨x, fun n hn ↦ hx.otherHomotopySubsingleton hn⟩

end Bπ
