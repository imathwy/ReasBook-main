module

public import Topology_Munkres_2000.Book.Theorem_79_2
public import Topology_Munkres_2000.Book.Lemma_79_3

public section

universe u v

open scoped Pointwise

namespace Subgroup

/-- Helper for Exercise 79.3: a subgroup is normal exactly when every subgroup conjugate to it
is equal to it. -/
private lemma normal_iff_forall_isConj_eq {G : Type*} [Group G] (H : Subgroup G) :
    H.Normal ↔ ∀ K : Subgroup G, K.IsConj H → K = H := by
  constructor
  · intro hnormal K hK
    -- Reverse the conjugacy witness so that normality applies to a conjugate of `H`.
    obtain ⟨g, hg⟩ := isConj_iff_exists.mp (Subgroup.isConj_symm hK)
    exact hg.symm.trans (hnormal.conjAct g)
  · intro hfixed
    -- Every inner automorphism produces a subgroup conjugate to `H`.
    apply Normal.of_conjugate_fixed
    intro g
    apply hfixed
    apply Subgroup.isConj_symm
    apply isConj_iff_exists.mpr
    use g

end Subgroup

namespace CoveringMap.Equiv

/-- Helper for Exercise 79.3: two equivalences into the same covering that agree at one point
are equal when their common source is preconnected. -/
private lemma eq_of_apply_eq
    {E : Type u} {E' : Type v} {B : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PreconnectedSpace E] {p : E → B} {p' : E' → B} (hp' : IsCoveringMap p')
    (h k : CoveringMap.Equiv p p') (e : E)
    (he : h.toHomeomorph e = k.toHomeomorph e) : h = k := by
  apply CoveringMap.Equiv.ext
  apply Homeomorph.ext
  -- Uniqueness of lifts upgrades agreement at `e` to pointwise agreement.
  exact congrFun (hp'.eq_of_comp_eq h.toHomeomorph.continuous k.toHomeomorph.continuous
    (h.commutes.symm.trans k.commutes) e he)

end CoveringMap.Equiv

namespace IsCoveringMap

/-- Helper for Exercise 79.3: a pointed equivalence of connected coverings identifies their
fundamental-group ranges. -/
private lemma fundamentalGroupMapRange_eq_of_equiv
    {E : Type u} {E' : Type v} {B : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace E']
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace E']
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    {e₀ : E} {e₀' : E'} {b₀ : B} (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀)
    (h : CoveringMap.Equiv p p') (hh : h.toHomeomorph e₀ = e₀') :
    hp.fundamentalGroupMapRange he₀ = hp'.fundamentalGroupMapRange he₀' := by
  apply (existsUnique_equiv_iff_fundamentalGroupMapRange_eq
    p p' hp hp' e₀ e₀' b₀ he₀ he₀').mp
  refine ExistsUnique.intro h hh ?_
  intro k hk
  -- Pointed lift uniqueness supplies the uniqueness required by Theorem 79.2.
  exact CoveringMap.Equiv.eq_of_apply_eq hp' k h e₀ (hk.trans hh.symm)

/-- Helper for Exercise 79.3: if one fundamental-group range of a connected covering is normal,
then the ranges based at all other points of the same fiber equal it. -/
private lemma fundamentalGroupMapRange_eq_of_normal
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] {p : E → B} (hp : IsCoveringMap p)
    {e₀ e : E} {b₀ : B} (he₀ : p e₀ = b₀) (he : p e = b₀)
    (hnormal : (hp.fundamentalGroupMapRange he₀).Normal) :
    hp.fundamentalGroupMapRange he = hp.fundamentalGroupMapRange he₀ := by
  -- A path in `E` makes the two ranges conjugate; normality collapses that conjugacy class.
  apply (Subgroup.normal_iff_forall_isConj_eq
    (hp.fundamentalGroupMapRange he₀)).mp hnormal
  exact hp.fundamentalGroupMapRange_isConj_of_path he₀ he
    (PathConnectedSpace.somePath e₀ e)

/-- Exercise 79.3: the image of the fundamental group of a connected covering is normal
exactly when covering self-equivalences act transitively on the fiber over the basepoint. -/
theorem fundamentalGroupMapRange_normal_iff_equiv_transitive
    {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B]
    (p : E → B) (hp : IsCoveringMap p) (hp_surjective : Function.Surjective p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    (hp.fundamentalGroupMapRange he₀).Normal ↔
      ∀ e₁ e₂ : p ⁻¹' {b₀},
        ∃ h : CoveringMap.Equiv p p, h.toHomeomorph e₁ = e₂ := by
  constructor
  · intro hnormal e₁ e₂
    have he₁ : p e₁ = b₀ := Set.mem_singleton_iff.mp e₁.property
    have he₂ : p e₂ = b₀ := Set.mem_singleton_iff.mp e₂.property
    -- Normality identifies both pointed ranges with the range at `e₀`.
    have hrange : hp.fundamentalGroupMapRange he₁ = hp.fundamentalGroupMapRange he₂ :=
      (hp.fundamentalGroupMapRange_eq_of_normal he₀ he₁ hnormal).trans
      (hp.fundamentalGroupMapRange_eq_of_normal he₀ he₂ hnormal).symm
    -- The pointed classification theorem now supplies the required self-equivalence.
    obtain ⟨h, hh, _⟩ := (existsUnique_equiv_iff_fundamentalGroupMapRange_eq
      p p hp hp e₁ e₂ b₀ he₁ he₂).mpr hrange
    exact ⟨h, hh⟩
  · intro htransitive
    apply (Subgroup.normal_iff_forall_isConj_eq
      (hp.fundamentalGroupMapRange he₀)).mpr
    intro H hH
    -- Lemma 79.3 realizes the arbitrary conjugate `H` at a point of the fiber.
    obtain ⟨e, he, hrange⟩ :=
      hp.exists_fiberPoint_fundamentalGroupMapRange_eq_of_isConj e₀ he₀ H hH
    let e₀InFiber : p ⁻¹' {b₀} := ⟨e₀, he₀⟩
    let eInFiber : p ⁻¹' {b₀} := ⟨e, he⟩
    obtain ⟨h, hh⟩ := htransitive e₀InFiber eInFiber
    have hh' : h.toHomeomorph e₀ = e := hh
    -- The pointed equivalence identifies the realized range with the original one.
    have hequiv := hp.fundamentalGroupMapRange_eq_of_equiv hp he₀ he h hh'
    exact hrange.symm.trans hequiv.symm

end IsCoveringMap
