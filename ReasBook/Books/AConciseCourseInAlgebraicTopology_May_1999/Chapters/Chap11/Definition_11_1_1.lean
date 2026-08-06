import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.SpacePair

open Function
open scoped Topology Topology.Homotopy unitInterval

universe u

-- Semantic recall via `lean_leansearch`: no current mathlib owner for relative homotopy groups of
-- maps of pairs surfaced. Chapter 9/13 precedent in this repo uses `homotopyGroupMap` for induced
-- maps, `relativeHomotopyGroup` for pair-relative groups, and `SpacePair.Hom` for maps of pairs.

namespace SpacePair

/-- The constant point of the modeled homotopy fiber of `P.subspace ↪ P.space` at `c`. -/
def relativeHomotopyBasepoint (P : SpacePair.{u}) (c : P.subspace) :
    inclusionHomotopyFiber P.subspace c :=
  ⟨(c, ContinuousMap.const I c.1), by simp⟩

/-- The relative homotopy group of a pair `P` based at `c ∈ P.subspace`, modeled by the homotopy
fiber of the inclusion `P.subspace ↪ P.space`. -/
abbrev relativeHomotopyGroup (n : ℕ+) (P : SpacePair.{u}) (c : P.subspace) :=
  π_ ((n : ℕ) - 1) (inclusionHomotopyFiber P.subspace c) (relativeHomotopyBasepoint P c)

/-- `SpacePair.relativeHomotopyGroup` is the shifted homotopy group of the modeled homotopy fiber
of the distinguished subspace inclusion. -/
theorem relativeHomotopyGroup_def (n : ℕ+) (P : SpacePair.{u}) (c : P.subspace) :
    relativeHomotopyGroup n P c =
      π_ ((n : ℕ) - 1) (inclusionHomotopyFiber P.subspace c) (relativeHomotopyBasepoint P c) :=
  sorry

/-- Relative homotopy groups in degrees `n + 2` carry the canonical group structure induced by
the shifted homotopy group of the modeled homotopy fiber. -/
noncomputable instance relativeHomotopyGroupGroup (P : SpacePair.{u}) (c : P.subspace) (n : ℕ) :
    Group (relativeHomotopyGroup (n + 1).succPNat P c) := by
  simpa [relativeHomotopyGroup, Nat.add_assoc] using
    (inferInstance :
      Group (HomotopyGroup.Pi (n + 1) (inclusionHomotopyFiber P.subspace c)
        (relativeHomotopyBasepoint P c)))

namespace Hom

/-- A map of pairs induces a continuous map on the distinguished subspaces. -/
def mapSubspace {P Q : SpacePair.{u}} (f : P ⟶ Q) : C(P.subspace, Q.subspace) where
  toFun c := ⟨f.hom c.1, f.map_subspace' c.2⟩
  continuous_toFun :=
    ((map_continuous f.hom.hom).comp continuous_subtype_val).subtype_mk
      fun c ↦ f.map_subspace' c.2

/-- Evaluating `f.mapSubspace` gives the induced point of the target distinguished subspace. -/
@[simp] theorem mapSubspace_apply {P Q : SpacePair.{u}} (f : P ⟶ Q) (c : P.subspace) :
    f.mapSubspace c = ⟨f.hom c.1, f.map_subspace' c.2⟩ :=
  rfl

/-- Evaluating `f.mapSubspace` and then forgetting the subtype agrees with applying the ambient
map `f.hom`. -/
theorem mapSubspace_val {P Q : SpacePair.{u}} (f : P ⟶ Q) (c : P.subspace) :
    (f.mapSubspace c : Q.space) = f.hom c.1 :=
  rfl

/-- A map of pairs induces a continuous map on the modeled homotopy fibers of the distinguished
subspace inclusions. -/
def relativePathSpaceMap {P Q : SpacePair.{u}} (f : P ⟶ Q) (c : P.subspace) :
    C(inclusionHomotopyFiber P.subspace c,
      inclusionHomotopyFiber Q.subspace (f.mapSubspace c)) where
  toFun z :=
    let fcont : C(P.space, Q.space) := CategoryTheory.ConcreteCategory.hom f.hom
    ⟨((f.mapSubspace z.1.1), fcont.comp z.1.2), by
      constructor
      · simpa [fcont, ContinuousMap.comp_apply] using congrArg f.hom z.2.1
      · simpa [fcont, ContinuousMap.comp_apply] using congrArg f.hom z.2.2⟩
  continuous_toFun := by
    let fcont : C(P.space, Q.space) := CategoryTheory.ConcreteCategory.hom f.hom
    exact Continuous.subtype_mk
      (Continuous.prodMk
        (Continuous.subtype_mk (by continuity) (fun z : inclusionHomotopyFiber P.subspace c ↦
          f.map_subspace' z.1.1.2))
        ((ContinuousMap.continuous_postcomp fcont).comp
          (continuous_snd.comp continuous_subtype_val)))
      (fun z ↦ by
        constructor
        · simpa [fcont, ContinuousMap.comp_apply] using congrArg f.hom z.2.1
        · simpa [fcont, ContinuousMap.comp_apply] using congrArg f.hom z.2.2)

/-- The induced map on modeled homotopy fibers sends the constant relative path at `c` to the
constant relative path at `f(c)`. -/
@[simp] theorem relativePathSpaceMap_basepoint {P Q : SpacePair.{u}} (f : P ⟶ Q)
    (c : P.subspace) :
    f.relativePathSpaceMap c (relativeHomotopyBasepoint P c) =
      relativeHomotopyBasepoint Q (f.mapSubspace c) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  ext t
  rfl

/-- The map on modeled relative homotopy groups induced by a map of pairs. -/
def relativeHomotopyGroupMap {P Q : SpacePair.{u}} (f : P ⟶ Q) (n : ℕ+) (c : P.subspace) :
    SpacePair.relativeHomotopyGroup n P c →
      SpacePair.relativeHomotopyGroup n Q (f.mapSubspace c) :=
  cast
    (by
      simpa [SpacePair.relativeHomotopyGroup] using
        congrArg
          (fun b ↦ SpacePair.relativeHomotopyGroup n P c →
            π_ ((n : ℕ) - 1) (inclusionHomotopyFiber Q.subspace (f.mapSubspace c)) b)
          (relativePathSpaceMap_basepoint f c))
    (homotopyGroupMap (f.relativePathSpaceMap c) ((n : ℕ) - 1) (relativeHomotopyBasepoint P c))

/-- Definition 11.1.1. A map of pairs `f : (A, C) ⟶ (X, B)` is an `n`-equivalence when it
satisfies the source's component condition and induces isomorphisms on relative homotopy groups
in every positive degree below `n`, together with surjections in degree `n`. The component
condition is expressed on ambient path components: any point of `P.space` whose image under `f`
is joined to `Q.subspace` is itself joined to `P.subspace`. -/
@[mk_iff isNEquivalence_iff]
class IsNEquivalence {P Q : SpacePair.{u}} (n : ℕ) (f : P ⟶ Q) : Prop where
  /-- The ambient component condition: if `f x` is joined to some point of the target
  distinguished subspace, then `x` is joined to some point of the source distinguished subspace.
  Equivalently, `(f_*)⁻¹ Im(π₀ Q.subspace → π₀ Q.space) = Im(π₀ P.subspace → π₀ P.space)`. -/
  componentCondition :
    ∀ x : P.space, (∃ b : Q.subspace, Joined (f.hom x) b.1) → ∃ a : P.subspace, Joined x a.1
  /-- The induced map on each relative homotopy group in positive degree strictly below `n` is
  bijective. -/
  relativeBijectiveBelow :
    ∀ c : P.subspace, ∀ ⦃q : ℕ+⦄, (q : ℕ) < n → Bijective (f.relativeHomotopyGroupMap q c)
  /-- The induced map on each relative homotopy group in degree `n` is surjective. -/
  relativeSurjectiveInDegree :
    ∀ c : P.subspace, ∀ ⦃q : ℕ+⦄, (q : ℕ) = n → Surjective (f.relativeHomotopyGroupMap q c)

/-- The identity map of a pair is an `n`-equivalence of pairs. -/
instance isNEquivalenceId (P : SpacePair.{u}) (n : ℕ) :
    IsNEquivalence n (SpacePair.id P) := sorry

/-- An `n`-equivalence of pairs induces bijections on relative homotopy groups in every positive
degree strictly below `n`. -/
theorem IsNEquivalence.relativeBijective {P Q : SpacePair.{u}} {n : ℕ} {f : P ⟶ Q}
    (h : IsNEquivalence n f) (c : P.subspace) {q : ℕ+} (hq : (q : ℕ) < n) :
    Bijective (f.relativeHomotopyGroupMap q c) :=
  sorry

/-- An `n`-equivalence of pairs induces injective maps on relative homotopy groups in every
positive degree strictly below `n`. -/
theorem IsNEquivalence.relativeInjective {P Q : SpacePair.{u}} {n : ℕ} {f : P ⟶ Q}
    (h : IsNEquivalence n f) (c : P.subspace) {q : ℕ+} (hq : (q : ℕ) < n) :
    Injective (f.relativeHomotopyGroupMap q c) :=
  (h.relativeBijective c hq).1

/-- An `n`-equivalence of pairs induces surjective maps on relative homotopy groups in every
positive degree strictly below `n`. -/
theorem IsNEquivalence.relativeSurjectiveOfLt {P Q : SpacePair.{u}} {n : ℕ} {f : P ⟶ Q}
    (h : IsNEquivalence n f) (c : P.subspace) {q : ℕ+} (hq : (q : ℕ) < n) :
    Surjective (f.relativeHomotopyGroupMap q c) :=
  (h.relativeBijective c hq).2

end Hom
end SpacePair
