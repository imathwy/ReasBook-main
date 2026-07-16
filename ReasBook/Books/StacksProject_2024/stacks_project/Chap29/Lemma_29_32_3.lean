import StacksProject_2024.stacks_project.Chap17.Lemma_17_28_6

open AlgebraicGeometry
open TopCat.Sheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)

-- Semantic recall: the Chapter 17 owner
-- `TopCat.Sheaf.inverseImage_relativeDifferentialsIso` already gives the restriction isomorphism
-- for relative differentials along an open inclusion. The source-facing scheme statement here is
-- its direct specialization to the open immersion `U.toScheme ⟶ X` and the restricted morphism
-- `U.toScheme ⟶ V.toScheme`.

/-- Lemma 29.32.3: for a morphism of schemes `f : X ⟶ S` and opens `U ⊆ X`, `V ⊆ S` with
`f(U) ⊆ V`, the restriction of `\Omega_{X/S}` to `U` is canonically identified with
`\Omega_{U/V}` for the restricted morphism `U.toScheme ⟶ V.toScheme`. This is the scheme-level
specialization of the Chapter 17 restriction isomorphism for relative differentials along an open
immersion. -/
@[stacks 01US]
noncomputable abbrev restrictRelativeDifferentialsIso :
    ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj Ω[f.toShHom]) ≅
      Ω[(X.homOfLE hU ≫ f ∣_ V).toShHom] :=
  (inverseImage_relativeDifferentialsIso U.inclusion' f.toRingCatSheafHom :
    ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj Ω[f.toShHom]) ≅
      Ω[(X.homOfLE hU ≫ f ∣_ V).toShHom])

/-- Companion: the canonical restriction comparison morphism carries each universal relative
differential to the corresponding restricted universal differential. -/
theorem restrictRelativeDifferentialsIso_characterizing :
    inverseImage_relativeDifferentialsComparisonProperty
      U.inclusion'
      f.toRingCatSheafHom
      (restrictRelativeDifferentialsIso (f := f) U V hU).hom := sorry

/-- Companion: the restriction of `\Omega_{X/S}` to `U` is isomorphic to `\Omega_{U/V}`. -/
theorem restrictRelativeDifferentials_isIsomorphic :
    IsIsomorphic
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj Ω[f.toShHom])
      Ω[(X.homOfLE hU ≫ f ∣_ V).toShHom] := sorry

/-- Companion: there is a unique comparison morphism from the restriction of `\Omega_{X/S}` to
`\Omega_{U/V}` sending each universal relative differential `d(t)` to the corresponding
restricted universal differential. -/
theorem existsUnique_restrictRelativeDifferentialsComparison :
    ∃! τ :
        ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj Ω[f.toShHom]) ⟶
          Ω[(X.homOfLE hU ≫ f ∣_ V).toShHom],
      inverseImage_relativeDifferentialsComparisonProperty
        U.inclusion'
        f.toRingCatSheafHom
        τ := sorry

/-- Companion: any two comparison morphisms satisfying the universal relative-differential
compatibility property are equal. -/
theorem restrictRelativeDifferentialsComparison_unique
    (τ :
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj Ω[f.toShHom]) ⟶
        Ω[(X.homOfLE hU ≫ f ∣_ V).toShHom])
    (τ' :
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj Ω[f.toShHom]) ⟶
        Ω[(X.homOfLE hU ≫ f ∣_ V).toShHom])
    (hτ :
      inverseImage_relativeDifferentialsComparisonProperty
        U.inclusion'
        f.toRingCatSheafHom
        τ)
    (hτ' :
      inverseImage_relativeDifferentialsComparisonProperty
        U.inclusion'
        f.toRingCatSheafHom
        τ') :
    τ = τ' := sorry

end AlgebraicGeometry
