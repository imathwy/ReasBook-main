module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient

public section

open scoped Pointwise

universe u

namespace Subgroup

variable {G : Type u} [Group G]

/-- Two subgroups are conjugate when the second lies in the conjugation orbit of the first. -/
def IsConj (H K : Subgroup G) : Prop :=
  K ∈ MulAction.orbit (ConjAct G) H

/-- Subgroup conjugacy means that a group element carries the first subgroup to the second by
inner automorphism. -/
theorem isConj_iff_exists {H K : Subgroup G} :
    H.IsConj K ↔ ∃ g : G, MulAut.conj g • H = K :=
  Iff.rfl

/-- Every subgroup is conjugate to itself. -/
@[refl]
theorem isConj_refl (H : Subgroup G) : H.IsConj H :=
  (MulAction.orbitRel (ConjAct G) (Subgroup G)).refl H

/-- Subgroup conjugacy is symmetric. -/
@[symm]
theorem isConj_symm {H K : Subgroup G} (h : H.IsConj K) : K.IsConj H :=
  (MulAction.orbitRel (ConjAct G) (Subgroup G)).symm h

/-- Subgroup conjugacy is transitive. -/
@[trans]
theorem isConj_trans {H K L : Subgroup G} (hHK : H.IsConj K) (hKL : K.IsConj L) :
    H.IsConj L :=
  (MulAction.orbitRel (ConjAct G) (Subgroup G)).trans hKL hHK

/-- The conjugacy class of a subgroup is its orbit under inner automorphisms. -/
def conjugacyClass (H : Subgroup G) : Set (Subgroup G) :=
  MulAction.orbit (ConjAct G) H

/-- Membership in a subgroup conjugacy class is subgroup conjugacy. -/
theorem mem_conjugacyClass {H K : Subgroup G} :
    K ∈ H.conjugacyClass ↔ H.IsConj K :=
  Iff.rfl

/-- The type of conjugacy classes of subgroups of a group. -/
abbrev ConjClasses (G : Type u) [Group G] :=
  MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G)

/-- The conjugacy class represented by a subgroup. -/
@[expose]
def mkConjClass (H : Subgroup G) : ConjClasses G :=
  Quotient.mk'' H

/-- Two subgroups represent the same conjugacy class exactly when they are conjugate. -/
theorem mkConjClass_eq_iff {H K : Subgroup G} :
    mkConjClass H = mkConjClass K ↔ H.IsConj K := by
  change (Quotient.mk'' H : MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G)) =
      Quotient.mk'' K ↔ K ∈ MulAction.orbit (ConjAct G) H
  rw [Quotient.eq'']
  exact MulAction.mem_orbit_symm

end Subgroup
