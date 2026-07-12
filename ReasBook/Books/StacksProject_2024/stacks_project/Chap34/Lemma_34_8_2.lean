import StacksProject_2024.Chap34.Definition_34_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic layer:
-- `source-facing`: base change preserves standard ph coverings;
-- `core/canonical`: the Chapter 34 owner `StandardPhCovering`;
-- `bridge/view`: the theorem exposes the pulled-back affine family comparison explicitly.

/-- Lemma 34.8.2: the base change of a standard ph covering along a morphism of affine schemes is
again a standard ph covering. Starting from `Φ : StandardPhCovering T`, the family
`Φ_j ×_T T' ⟶ T'` is presented by the proper surjective morphism
`Φ.source ×_T T' ⟶ T'` together with a finite affine open cover of `Φ.source ×_T T'`. -/
@[stacks 0DBE]
theorem StandardPhCovering.pullback_family {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (Φ : StandardPhCovering T) (g : T' ⟶ T) :
    let W : Scheme.{u} := pullback Φ.toBase g
    let q : W ⟶ T' := pullback.snd Φ.toBase g
    let U' : Fin Φ.m → Scheme.{u} := fun j ↦ pullback (Φ.map j) g
    let p' : (j : Fin Φ.m) → U' j ⟶ T' := fun j ↦ pullback.snd (Φ.map j) g
    (∀ j, IsAffine (U' j)) ∧
      IsProper q ∧
        Surjective q ∧
          ∃ 𝒱 : Fin Φ.m → W.affineOpens,
            (⨆ j, ((𝒱 j : W.Opens)) = ⊤) ∧
              ∀ j, ∃ e : U' j ≅ ((𝒱 j : W.Opens)).toScheme,
                p' j = e.hom ≫ ((𝒱 j : W.Opens)).ι ≫ q := sorry

end AlgebraicGeometry
