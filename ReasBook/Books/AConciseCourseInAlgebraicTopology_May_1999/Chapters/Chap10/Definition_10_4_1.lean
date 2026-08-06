import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.HomotopyGroup

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

-- Semantic recall: `lean_leansearch` found `HomotopyGroup.Pi` as the canonical owner for based
-- homotopy groups, and mathlib already packages the degree-`1` case as
-- `SimplyConnectedSpace`. No built-in general `n`-connected-space owner was found in mathlib, so
-- this file keeps the source-facing owner and adds thin bridges in degrees `0` and `1`.

/-- Definition 10.4.1: a space `X` is `n`-connected when every based homotopy group `π_ q X x`
with `q ≤ n` is trivial, equivalently when `π_ q(X, x) = 0` for all `0 ≤ q ≤ n` and all
basepoints `x : X`. -/
class NConnectedSpace (n : ℕ) (X : Type u) [TopologicalSpace X] : Prop where
  subsingleton_pi (q : ℕ) (hq : q ≤ n) (x : X) : Subsingleton (π_ q X x)

namespace NConnectedSpace

variable {m n q : ℕ} {X : Type u} [TopologicalSpace X]

/-- Lower connectivity follows formally from higher connectivity. -/
theorem of_le [hX : NConnectedSpace n X] (hqn : q ≤ n) : NConnectedSpace q X where
  subsingleton_pi r hr x := hX.subsingleton_pi r (Nat.le_trans hr hqn) x

/-- The defining condition of `NConnectedSpace q X` gives a canonical `Subsingleton` instance for
the `q`th homotopy group. -/
instance subsingletonPi [hX : NConnectedSpace q X] (x : X) :
    Subsingleton (π_ q X x) :=
  hX.subsingleton_pi q le_rfl x

/-- `NConnectedSpace n X` is equivalent to the vanishing of all based homotopy groups `π_ q X x`
for `q ≤ n` and all basepoints `x : X`. -/
theorem nConnectedSpace_iff :
    NConnectedSpace n X ↔ ∀ (q : ℕ) (_hq : q ≤ n) (x : X), Subsingleton (π_ q X x) := by
  constructor
  · intro hX q hq x
    -- Unpack the single field of the connectivity structure.
    exact hX.subsingleton_pi q hq x
  · intro hX
    -- Repack the pointwise vanishing data into the source-facing owner.
    exact ⟨hX⟩

/-- Helper for Definition 10.4.1: path connectedness forces `π_ 0 X x` to be subsingleton. -/
lemma pi0SubsingletonOfPathConnected [PathConnectedSpace X] (x : X) :
    Subsingleton (π_ 0 X x) := by
  -- Convert path connectedness into subsingleton zeroth homotopy.
  have hZeroth : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy (X := X)).mp inferInstance |>.2
  -- Transport that triviality across the canonical `π₀` equivalence.
  refine ⟨fun a b => ?_⟩
  apply (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective
  exact @Subsingleton.elim _ hZeroth _ _

/-- A path-connected space is `0`-connected. -/
theorem of_pathConnectedSpace [PathConnectedSpace X] : NConnectedSpace 0 X where
  subsingleton_pi q hq x := by
    -- The inequality `q ≤ 0` forces the degree to be exactly `0`.
    have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
    -- Reduce to the canonical degree-`0` bridge.
    simpa [hq0] using pi0SubsingletonOfPathConnected (X := X) x

/-- For nonempty spaces, `0`-connectedness is equivalent to path connectedness. -/
theorem zero_iff_pathConnectedSpace [Nonempty X] :
    NConnectedSpace 0 X ↔ PathConnectedSpace X := by
  constructor
  · intro hX
    rcases ‹Nonempty X› with ⟨x⟩
    -- Route correction: prove path connectedness through `ZerothHomotopy`, not by building paths
    -- directly from the `π₀` statement.
    have hPi0 : Subsingleton (π_ 0 X x) := hX.subsingleton_pi 0 le_rfl x
    have hZeroth : Subsingleton (ZerothHomotopy X) := by
      -- Move the `π₀` triviality to the canonical zeroth homotopy quotient.
      refine ⟨fun a b => ?_⟩
      apply (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm.injective
      exact @Subsingleton.elim _ hPi0 _ _
    -- The quotient is nonempty because the space is.
    exact
      (pathConnectedSpace_iff_zerothHomotopy (X := X)).mpr
        ⟨⟨⟦x⟧⟩, hZeroth⟩
  · intro hX
    -- The reverse implication is exactly the degree-`0` bridge.
    exact of_pathConnectedSpace (X := X)

/-- On a nonempty `0`-connected space, path connectedness is available through typeclass search. -/
instance pathConnectedSpace [Nonempty X] [NConnectedSpace 0 X] :
    PathConnectedSpace X := by
  -- Reuse the degree-`0` characterization as an instance bridge.
  exact (zero_iff_pathConnectedSpace (X := X)).mp inferInstance

/-- Helper for Definition 10.4.1: simple connectedness forces `π_ 1 X x` to be subsingleton. -/
lemma pi1SubsingletonOfSimplyConnected [SimplyConnectedSpace X] (x : X) :
    Subsingleton (π_ 1 X x) := by
  -- The fundamental group is already trivial in a simply connected space.
  have hFund : Subsingleton (FundamentalGroup X x) := by
    change Subsingleton (Path.Homotopic.Quotient x x)
    infer_instance
  -- Transport that triviality across the canonical `π₁` equivalence.
  refine ⟨fun a b => ?_⟩
  apply (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).injective
  exact @Subsingleton.elim _ hFund _ _

/-- Helper for Definition 10.4.1: a subsingleton `π_ 1 X x` makes every loop at `x`
null-homotopic. -/
lemma loopNullhomotopicOfSubsingletonPi1 (x : X) [Subsingleton (π_ 1 X x)] (γ : Path x x) :
    Path.Homotopic γ (Path.refl x) := by
  -- First transport the `π₁` triviality to the fundamental group.
  have hFund : Subsingleton (FundamentalGroup X x) := by
    refine ⟨fun a b => ?_⟩
    apply (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).symm.injective
    exact Subsingleton.elim _ _
  have hLoops : Subsingleton (Path.Homotopic.Quotient x x) := by
    simpa [FundamentalGroup] using hFund
  -- Equality of loop classes is exactly null-homotopy.
  exact Quotient.eq.mp (@Subsingleton.elim _ hLoops ⟦γ⟧ ⟦Path.refl x⟧)

/-- A simply connected space is `1`-connected. -/
theorem of_simplyConnectedSpace [SimplyConnectedSpace X] : NConnectedSpace 1 X where
  subsingleton_pi q hq x := by
    cases q with
    | zero =>
        -- The degree-`0` part comes from path connectedness, available by instance search.
        simpa using pi0SubsingletonOfPathConnected (X := X) x
    | succ q =>
        -- The inequality `q.succ ≤ 1` forces the remaining case to be degree `1`.
        have hq0 : q = 0 := Nat.eq_zero_of_le_zero (Nat.succ_le_succ_iff.mp hq)
        cases hq0
        simpa using pi1SubsingletonOfSimplyConnected (X := X) x

/-- For nonempty spaces, `1`-connectedness is equivalent to being simply connected. -/
theorem one_iff_simplyConnectedSpace [Nonempty X] :
    NConnectedSpace 1 X ↔ SimplyConnectedSpace X := by
  constructor
  · intro hX
    have h0 : NConnectedSpace 0 X := of_le (X := X) (n := 1) (q := 0) (by simp)
    have hPath : PathConnectedSpace X := (zero_iff_pathConnectedSpace (X := X)).mp h0
    -- Route correction: use the loop-null-homotopy characterization of simple connectedness.
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨hPath, ?_⟩
    intro x γ
    have hPi1 : Subsingleton (π_ 1 X x) := hX.subsingleton_pi 1 le_rfl x
    let _ : Subsingleton (π_ 1 X x) := hPi1
    -- Every loop class agrees with the constant loop class when `π₁` is trivial.
    simpa using loopNullhomotopicOfSubsingletonPi1 (X := X) x γ
  · intro hX
    -- The reverse implication is the degree-`1` bridge.
    exact of_simplyConnectedSpace (X := X)

/-- On a nonempty `1`-connected space, `SimplyConnectedSpace` is available through typeclass
search. -/
instance simplyConnectedSpace [Nonempty X] [NConnectedSpace 1 X] :
    SimplyConnectedSpace X := by
  -- Reuse the degree-`1` characterization as an instance bridge.
  exact (one_iff_simplyConnectedSpace (X := X)).mp inferInstance

end NConnectedSpace
