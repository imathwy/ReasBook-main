import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_5_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_3_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Theorem_1_5_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContinuousMap
open scoped FundamentalGroup

/-- A canonical path from `z : S¹` back to the basepoint `1`. -/
def circlePathToOne (z : Circle) : Path z (1 : Circle) :=
  (((Path.segment (0 : ℝ) (Complex.arg (z : ℂ))).map Circle.exp.continuous).cast
    Circle.exp_zero.symm (Circle.exp_arg z).symm).symm

/-- Every point of `S¹` is joined to the basepoint `1` by `circlePathToOne`. -/
theorem circleJoinedToOne (z : Circle) : Joined z (1 : Circle) :=
  ⟨circlePathToOne z⟩

/-- Definition 1.7.1: the degree of a self-map `f : S¹ → S¹` is the integer by which the induced
map on `π₁(S¹)` sends the chosen generator `standardLoopClass 1` after transporting the basepoint
from `f 1` back to `1`. -/
def circleDegree (f : C(Circle, Circle)) : ℤ :=
  circleFundamentalGroupLiftIndex <|
    γ[circlePathToOne (f 1)]
      (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1))

/-- The standard notation for the degree of a self-map of the circle. -/
scoped[CircleDegree] notation "deg(" f ")" => circleDegree f

open scoped CircleDegree

/-- Helper for Definition 1.7.1: the fundamental group `π₁(S¹, 1)` is commutative because
Theorem 1.5.11 identifies it with `ℤ`. -/
instance circleFundamentalGroup_commutative :
    Std.Commutative ((· * ·) :
      FundamentalGroup Circle (1 : Circle) →
        FundamentalGroup Circle (1 : Circle) →
          FundamentalGroup Circle (1 : Circle)) := by
  let e := circleFundamentalGroupMulEquivInt
  -- Transport commutativity from `Multiplicative ℤ` across the canonical equivalence.
  refine ⟨fun g h ↦ ?_⟩
  rcases e.surjective g with ⟨a, rfl⟩
  rcases e.surjective h with ⟨b, rfl⟩
  simpa using congrArg e (mul_comm a b)

/-- Helper for Definition 1.7.1: transporting loops from `f 1` to `1` identifies
`π₁(S¹, f 1)` with the already commutative group `π₁(S¹, 1)`. -/
instance circleFundamentalGroup_commutative_at (z : Circle) :
    Std.Commutative ((· * ·) :
      FundamentalGroup Circle z →
        FundamentalGroup Circle z →
          FundamentalGroup Circle z) := by
  let c : FundamentalGroup Circle z ≃* FundamentalGroup Circle (1 : Circle) :=
    γ[circlePathToOne z]
  -- Transfer commutativity across the basepoint-change equivalence.
  refine ⟨fun g h ↦ c.injective ?_⟩
  calc
    c (g * h) = c g * c h := by
      exact map_mul c g h
    _ = c h * c g := by
      exact Std.Commutative.comm (c g) (c h)
    _ = c (h * g) := by
      rw [map_mul]

/-- Helper for Definition 1.7.1: transporting `f_*(ι)` from `f 1` to `1` is independent of the
chosen path because `π₁(S¹, 1)` is commutative. -/
private lemma circle_transport_standard_generator_eq_of_paths
    (f : C(Circle, Circle)) (a b : Path (f 1) 1) :
    γ[a] (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1)) =
      γ[b] (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1)) := by
  -- First identify the two basepoint-change equivalences, then evaluate them on `f_*(ι)`.
  have hγ : γ[a] = γ[b] :=
    fundamentalGroupMulEquivOfPath_eq_of_abelian a b
  exact congrArg (fun e ↦ e (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1))) hγ

/-- Helper for Definition 1.7.1: the preferred path used in `deg(f)` transports `f_*(ι)` to the
standard loop class indexed by that degree. -/
private lemma circleDegree_spec_somePath (f : C(Circle, Circle)) :
    γ[circlePathToOne (f 1)]
        (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1)) =
      standardLoopClass (deg(f)) := by
  -- Compare lift indices: the left-hand side is definitionally the integer `deg(f)`.
  apply circleFundamentalGroupLiftIndex_injective
  rw [circleFundamentalGroupLiftIndex_standardLoop]
  simp [circleDegree]

/-- Changing the basepoint of `f_* (ι)` along any path from `f 1` back to `1` yields the standard
loop class of winding number `deg(f)`. -/
-- Proof sketch: compare the chosen path `circlePathToOne (f 1)` used in
-- `circleDegree f` with the arbitrary path `a` via path-independence of basepoint change on the
-- abelian group
-- `π₁(S¹)`, and then use the identification of `π₁(S¹, 1)` with `ℤ` from Theorem 1.5.11 to
-- recognize the resulting loop class as the `deg(f)`-fold generator.
theorem circleDegree_spec (f : C(Circle, Circle)) (a : Path (f 1) 1) :
    γ[a] (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1)) =
      standardLoopClass (deg(f)) := by
  -- Route correction: use path-independence of basepoint change first, then unfold `deg(f)` only
  -- at the chosen comparison path.
  calc
    γ[a] (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1)) =
        γ[circlePathToOne (f 1)]
          (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1)) := by
            -- Replace the arbitrary path by the canonical one used in the definition of `deg(f)`.
            exact circle_transport_standard_generator_eq_of_paths f a (circlePathToOne (f 1))
    _ = standardLoopClass (deg(f)) := by
      -- The chosen-path transport is exactly the loop class whose lift index defines `deg(f)`.
      exact circleDegree_spec_somePath f
