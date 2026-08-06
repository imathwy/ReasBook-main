import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Theorem_11_2_3

noncomputable section

open scoped Topology Topology.Homotopy

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for `π_ n`.
-- Chapter 9 already exports the induced-map surface `ContinuousMap.eStar` on homotopy groups.
-- This file packages the current repository's sphere self-map owners so the degree predicate can
-- be stated on a reusable API instead of raw projection chains.

/-- The chosen based self-map owner on `S^n := suspensionSphere n`. -/
abbrev SphereBasedSelfMap (n : ℕ+) :=
  suspensionSphere (n : ℕ) ⟶ suspensionSphere (n : ℕ)

/-- The chosen ordinary continuous self-map owner on `S^n := suspensionSphere n`. -/
abbrev SphereSelfMap (n : ℕ+) :=
  C((suspensionSphere (n : ℕ)).toCompactlyGenerated,
    (suspensionSphere (n : ℕ)).toCompactlyGenerated)

namespace SphereBasedSelfMap

/-- The underlying continuous self-map of a based self-map of `S^n`. -/
abbrev toContinuousMap {n : ℕ+} (f : SphereBasedSelfMap n) : SphereSelfMap n :=
  (PointedCompactlyGenerated.Hom.hom f).hom.hom

@[simp] theorem toContinuousMap_eq {n : ℕ+} (f : SphereBasedSelfMap n) :
    f.toContinuousMap = (PointedCompactlyGenerated.Hom.hom f).hom.hom :=
  rfl

/-- The endomorphism of `π_ n(S^n)` induced by a based self-map of `S^n`. -/
def homotopyGroupMap (n : ℕ+) (f : SphereBasedSelfMap n) :
    π_ (n : ℕ) (suspensionSphere (n : ℕ)).toCompactlyGenerated
        (suspensionSphere (n : ℕ)).point →
      π_ (n : ℕ) (suspensionSphere (n : ℕ)).toCompactlyGenerated
        (suspensionSphere (n : ℕ)).point :=
  fun a ↦
    (PointedCompactlyGenerated.Hom.map_point f) ▸
      f.toContinuousMap.eStar (n : ℕ) (suspensionSphere (n : ℕ)).point a

@[simp] theorem homotopyGroupMap_apply
    (n : ℕ+) (f : SphereBasedSelfMap n)
    (a : π_ (n : ℕ) (suspensionSphere (n : ℕ)).toCompactlyGenerated
      (suspensionSphere (n : ℕ)).point) :
    homotopyGroupMap n f a =
      (PointedCompactlyGenerated.Hom.map_point f) ▸
        f.toContinuousMap.eStar (n : ℕ) (suspensionSphere (n : ℕ)).point a :=
  rfl

/-- A based self-map of the chosen sphere model `S^n := suspensionSphere n` has degree `d` when
some identification `π_ n(S^n) ≃* Multiplicative ℤ` carries the canonical based specialization
of the induced map `ContinuousMap.eStar` on `π_ n(S^n)` to `x ↦ x ^ d`. -/
def HasDegree (n : ℕ+) (f : SphereBasedSelfMap n) (d : ℤ) : Prop :=
  ∃ e :
      π_ (n : ℕ) (suspensionSphere (n : ℕ)).toCompactlyGenerated
        (suspensionSphere (n : ℕ)).point ≃* Multiplicative ℤ,
    ∀ a :
      π_ (n : ℕ) (suspensionSphere (n : ℕ)).toCompactlyGenerated
        (suspensionSphere (n : ℕ)).point,
      e (homotopyGroupMap n f a) = e a ^ d

end SphereBasedSelfMap

namespace SphereSelfMap

/-- Definition 13.2.2. A continuous self-map `S^n → S^n`, represented on the chosen sphere owner
`S^n := suspensionSphere n`, has degree `d` when it is homotopic to a based self-map whose
induced endomorphism of `π_ n(S^n)` becomes `x ↦ x ^ d` under some identification
`π_ n(S^n) ≃* Multiplicative ℤ`. -/
def HasDegree (n : ℕ+) (f : SphereSelfMap n) (d : ℤ) : Prop :=
  ∃ f' : SphereBasedSelfMap n,
    ContinuousMap.Homotopic f'.toContinuousMap f ∧
      SphereBasedSelfMap.HasDegree n f' d

/-- `SphereSelfMap.HasDegree n f d` means that `f` admits a homotopic based representative of
degree `d`. -/
theorem hasDegree_iff (n : ℕ+) (f : SphereSelfMap n) (d : ℤ) :
    HasDegree n f d ↔
      ∃ f' : SphereBasedSelfMap n,
        ContinuousMap.Homotopic f'.toContinuousMap f ∧
          SphereBasedSelfMap.HasDegree n f' d :=
  Iff.rfl

/-- A based self-map gives an ordinary self-map of `S^n` with the same degree. -/
theorem hasDegree_of_based
    (n : ℕ+) (f : SphereBasedSelfMap n) (d : ℤ)
    (hf : SphereBasedSelfMap.HasDegree n f d) :
    HasDegree n f.toContinuousMap d := by
  exact ⟨f, ContinuousMap.Homotopic.refl f.toContinuousMap, hf⟩

/-- Every continuous self-map of the canonical sphere owner has a unique degree. -/
theorem existsUnique_hasDegree (n : ℕ+) (f : SphereSelfMap n) :
    ∃! d : ℤ, HasDegree n f d := sorry

end SphereSelfMap
