import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.HomotopyGroup

open scoped Topology

universe u v

noncomputable section

-- Semantic recall: `lean_leansearch` identifies `HomotopyGroup.Pi` as the canonical owner for
-- based homotopy groups, and `HomotopyGroup.pi1EquivFundamentalGroup` supplies the source-facing
-- bridge to `FundamentalGroup`. Later Chapter 15 files generalize this degree-`1` owner to
-- `K(π,n)` spaces, so this support file keeps the source-facing `K(π, 1)` API lightweight and
-- reusable.

/-- A pointed `K(π, 1)` witness with connected CW-complex structure and trivial higher homotopy
groups. -/
class IsKPiOne (π : Type v) [Group π] (X : TopCat.{u}) (x : X) : Prop extends ConnectedSpace X
    where
  cwComplex : Nonempty (TopCat.CWComplex X)
  pi1Iso : Nonempty (π_ 1 X x ≃* π)
  higherHomotopySubsingleton : ∀ n : ℕ, 1 < n → Subsingleton (π_ n X x)

/-- A `K(π, 1)` witness identifies the source-facing fundamental group with `π`. -/
theorem IsKPiOne.fundamentalGroupIso {π : Type v} [Group π] {X : TopCat.{u}} {x : X}
    (h : IsKPiOne π X x) : Nonempty (FundamentalGroup X x ≃* π) := by
  -- Convert the based first homotopy group identification into the standard fundamental group.
  rcases h.pi1Iso with ⟨e⟩
  exact ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup x).symm.trans e⟩

/-- A `K(π, 1)` witness supplies both a CW-complex structure and the required fundamental-group
identification. -/
theorem IsKPiOne.cwComplex_and_fundamentalGroupIso {π : Type v} [Group π] {X : TopCat.{u}}
    {x : X} (h : IsKPiOne π X x) :
    Nonempty (TopCat.CWComplex X) ∧ Nonempty (FundamentalGroup X x ≃* π) :=
  ⟨h.cwComplex, h.fundamentalGroupIso⟩

/-- The higher-homotopy triviality in a `K(π, 1)` witness can be used with positive-degree
indices directly. -/
theorem IsKPiOne.otherHomotopySubsingleton {π : Type v} [Group π] {X : TopCat.{u}} {x : X}
    (h : IsKPiOne π X x) {n : ℕ+} (hn : n ≠ 1) : Subsingleton (π_ (n : ℕ) X x) := by
  -- Translate the positive-degree index inequality into the `1 < n` shape stored in the witness.
  have hn' : (n : ℕ) ≠ 1 := by
    intro hEq
    apply hn
    apply PNat.coe_injective
    simpa using hEq
  exact h.higherHomotopySubsingleton n <|
    lt_of_le_of_ne (Nat.succ_le_of_lt n.2) (by simpa [eq_comm] using hn')

/-- `IsKPiOne π X x` is exactly the source-facing `K(π, 1)` condition on the pointed connected CW
complex `(X, x)`. -/
theorem isKPiOne_iff {π : Type v} [Group π] {X : TopCat.{u}} {x : X} :
    IsKPiOne π X x ↔
      ConnectedSpace X ∧
        Nonempty (TopCat.CWComplex X) ∧
          Nonempty (FundamentalGroup X x ≃* π) ∧
            ∀ n : ℕ, 1 < n → Subsingleton (π_ n X x) := by
  constructor
  · intro h
    -- Unpack the witness into the explicit source-facing conjunction.
    exact ⟨h.toConnectedSpace, h.cwComplex, h.fundamentalGroupIso, h.higherHomotopySubsingleton⟩
  · rintro ⟨hConnected, hCW, hpi1, hHigher⟩
    -- Repackage the conjunction using the canonical `π₁`/fundamental-group bridge.
    rcases hpi1 with ⟨e⟩
    exact
      { toConnectedSpace := hConnected
        cwComplex := hCW
        pi1Iso := ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup x).trans e⟩
        higherHomotopySubsingleton := hHigher }

/-- Helper for Problem 15.3.1: a pointed `K(π, 1)` witness immediately yields the existential
statement over a space and its basepoint. -/
theorem existsConnectedCWComplexKPiOneOfWitness {π : Type u} [Group π] {X : TopCat.{u}} {x : X}
    (h : IsKPiOne π X x) :
    ∃ (Y : TopCat.{u}) (y : Y), IsKPiOne π Y y := by
  -- Repackage the already chosen pointed witness into the source-facing existential statement.
  exact ⟨X, x, h⟩

end
