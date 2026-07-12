import StacksProject_2024.Chap34.Definition_34_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `CategoryTheory.Pretopology.mk` as the general
-- identity/base-change/transitivity closure pattern; Chapter 34 uses `PhCovering` as the
-- source-facing owner for ph covering families.

/-- Lemma 34.8.8 (1): if `T' ⟶ T` is an isomorphism, then the singleton family
`{T' ⟶ T}` is a ph covering of `T`. -/
@[stacks 0DBI]
theorem phCovering_singleton_of_isIso {T T' : Scheme.{u}} (f : T' ⟶ T) [IsIso f] :
    PhCovering (fun _ : PUnit ↦ T') (fun _ : PUnit ↦ f) := sorry

/-- Lemma 34.8.8 (2): if `{T_i ⟶ T}` is a ph covering and each `{T_{ij} ⟶ T_i}`
is a ph covering, then the composite family `{T_{ij} ⟶ T}` is a ph covering. -/
@[stacks 0DBI]
theorem phCovering_sigma_comp
    {ι : Type u} {T : Scheme.{u}} (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ T)
    [PhCovering X π] (J : ι → Type u) (Y : ∀ i, J i → Scheme.{u})
    (ρ : ∀ i, ∀ j : J i, Y i j ⟶ X i)
    (hY : ∀ i, PhCovering (Y i) (ρ i)) :
    PhCovering (fun p : Sigma J ↦ Y p.1 p.2)
      (fun p : Sigma J ↦ ρ p.1 p.2 ≫ π p.1) := sorry

/-- Lemma 34.8.8 (3): if `{T_i ⟶ T}` is a ph covering and `T' ⟶ T` is any morphism,
then the base-change family `{T_i ×_T T' ⟶ T'}` is a ph covering. -/
@[stacks 0DBI]
theorem phCovering_pullback
    {ι : Type u} {T T' : Scheme.{u}} (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ T)
    [PhCovering X π] (f : T' ⟶ T) :
    PhCovering (fun i : ι ↦ pullback (π i) f)
      (fun i : ι ↦ pullback.snd (π i) f) := sorry

end AlgebraicGeometry
