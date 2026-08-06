import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Problem_15_3_6

open scoped Topology

universe u

-- Semantic recall: Chapter 15 already packages positive-degree `K(π,n)` models by the canonical
-- owner `IsEilenbergMacLaneSpace`; this item keeps the source-facing `n + 1` indexing as a thin
-- bridge to that owner.

/-- A pointed `K(π, n + 1)` witness with connected CW-complex structure and trivial homotopy
groups away from degree `n + 1`. -/
abbrev IsKPiSucc (π : Type u) [CommGroup π] (n : ℕ) (X : TopCat.{u}) (x : X) : Prop :=
  IsEilenbergMacLaneSpace π n.succPNat X x

/-- A `K(π, n + 1)` witness supplies both a CW-complex structure and the required homotopy-group
identification in degree `n + 1`. -/
theorem IsKPiSucc.cwComplex_and_homotopyGroupIso {π : Type u} [CommGroup π] {n : ℕ}
    {X : TopCat.{u}} {x : X} (h : IsKPiSucc π n X x) :
    Nonempty (TopCat.CWComplex X) ∧ Nonempty (π_ (n + 1) X x ≃* π) :=
  IsEilenbergMacLaneSpace.cwComplex_and_homotopyGroupIso h

/-- `IsKPiSucc π n X x` is exactly the source-facing `K(π, n + 1)` condition on the pointed
connected CW complex `(X, x)`. -/
theorem isKPiSucc_iff {π : Type u} [CommGroup π] {n : ℕ} {X : TopCat.{u}} {x : X} :
    IsKPiSucc π n X x ↔
      ConnectedSpace X ∧
        Nonempty (TopCat.CWComplex X) ∧
          Nonempty (π_ (n + 1) X x ≃* π) ∧
            ∀ m : ℕ, m ≠ n → Subsingleton (π_ (m + 1) X x) := by
  constructor
  · intro h
    rcases isEilenbergMacLaneSpace_iff.mp h with ⟨hconn, hcw, hiso, hother⟩
    refine ⟨hconn, hcw, hiso, ?_⟩
    intro m hm
    simpa using hother m.succPNat (by simpa [Nat.succPNat_inj] using hm)
  · intro h
    rcases h with ⟨hconn, hcw, hiso, hother⟩
    refine isEilenbergMacLaneSpace_iff.mpr ⟨hconn, hcw, hiso, ?_⟩
    intro m hm
    simpa [PNat.natPred_add_one] using
      hother m.natPred (fun hmn ↦ hm (by simpa [hmn] using (PNat.succPNat_natPred m).symm))

/-- Problem 15.3.4: for any abelian group `π` and any `n : ℕ`, there exists a connected CW
complex model of `K(π, n + 1)`, i.e. a based connected CW complex whose `(n + 1)`st homotopy
group is `π` and whose other positive-degree homotopy groups are trivial. This encodes the source
condition `n ≥ 1` by writing the degree as `n + 1`. -/
theorem existsConnectedCWComplexKPiSucc (π : Type u) [CommGroup π] (n : ℕ) :
    ∃ (X : TopCat.{u}) (x : X), IsKPiSucc π n X x := sorry
