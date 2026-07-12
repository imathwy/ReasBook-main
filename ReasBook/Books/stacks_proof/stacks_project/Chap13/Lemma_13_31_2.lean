import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory DerivedCategory ComplexShape HomotopyCategory

universe w v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "Qis" => quasiIso 𝒜 (up ℤ)

-- Domain-style sampling:
-- * primary domain: K-injective cochain complexes and the localization
--   `K(𝒜) ⥤ D(𝒜)` at quasi-isomorphisms.
-- * inspected owner declarations:
--   `CochainComplex.IsKInjective`,
--   `CochainComplex.isKInjective_iff_rightOrthogonal`,
--   `CochainComplex.IsKInjective.rightOrthogonal`,
--   `CochainComplex.IsKInjective.Qh_map_bijective`,
--   `DerivedCategory.isIso_Qh_map_iff`.
-- * layer: `source-facing`; Lemma 13.31.2 is genuinely a three-way equivalence, so the main entry
--   should remain a local `List.TFAE`, but the owner abstraction must stay `I.IsKInjective`.
-- * core/canonical owner abstraction: `I.IsKInjective`.
-- * primitive data: only the cochain complex `I`.
-- * derived API: bijectivity of precomposition by quasi-isomorphisms into `I`, and bijectivity of
--   the canonical localization map `Qh.map` on morphisms with target `I`.
-- * abstraction check: there is no coordinate bookkeeping here; the correct ambient owner is the
--   homotopy/derived-category localization API, not a local wrapper around Hom-sets.

-- Proof sketch: clause `(2)` is exactly the `Qis.isLocal` formulation of the acyclic
-- right-orthogonality criterion `isKInjective_iff_rightOrthogonal`, while clause `(3)` is the
-- canonical owner theorem `IsKInjective.Qh_map_bijective`; conversely, bijectivity of `Qh.map`
-- transports the derived-category bijection induced by any quasi-isomorphism back to the
-- homotopy category.
/-- A cochain complex is K-injective exactly when precomposition by every quasi-isomorphism in the
homotopy category induces a bijection on morphisms into it. -/
theorem isKInjective_iff_precomp_bijective_of_quasiIso (I : CochainComplex 𝒜 ℤ) :
    I.IsKInjective ↔
      ∀ ⦃M N : KHom⦄ (f : M ⟶ N), Qis f →
        Function.Bijective
          (fun g : N ⟶ (quotient 𝒜 (up ℤ)).obj I ↦ f ≫ g) := by
  simpa only [MorphismProperty.isLocal_iff,
    HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W 𝒜] using
    (show I.IsKInjective ↔
        (HomotopyCategory.subcategoryAcyclic 𝒜).trW.isLocal
          ((quotient 𝒜 (up ℤ)).obj I) by
      rw [CochainComplex.isKInjective_iff_rightOrthogonal,
        ← ObjectProperty.isLocal_trW (HomotopyCategory.subcategoryAcyclic 𝒜)])

/-- Lemma 13.31.2: for a complex `I^•` in an abelian category, the following are equivalent:
`I^•` is K-injective; precomposition with any quasi-isomorphism in the homotopy category induces a
bijection on morphisms into `I^•`; and for every complex, the canonical map from morphisms in the
homotopy category to morphisms in the derived category with target `I^•` is bijective. -/
@[stacks 070I]
theorem isKInjective_tfae [HasDerivedCategory.{w} 𝒜] (I : CochainComplex 𝒜 ℤ) :
    List.TFAE
      [ I.IsKInjective
      , ∀ ⦃M N : KHom⦄ (f : M ⟶ N), Qis f →
          Function.Bijective
            (fun g : N ⟶ (quotient 𝒜 (up ℤ)).obj I ↦ f ≫ g)
      , ∀ N : KHom,
          Function.Bijective
            (Qh.map : (N ⟶ (quotient 𝒜 (up ℤ)).obj I) → _)
      ] := by
  tfae_have 1 ↔ 2 := isKInjective_iff_precomp_bijective_of_quasiIso I
  tfae_have 1 ↔ 3 := by
    let J : KHom := (quotient 𝒜 (up ℤ)).obj I
    constructor
    · intro hI N
      let _ : I.IsKInjective := hI
      simpa [J] using IsKInjective.Qh_map_bijective N I
    · intro hI
      refine (isKInjective_iff_precomp_bijective_of_quasiIso I).2 ?_
      intro M N f hf
      have hM :
          Function.Bijective
            (Qh.map : (M ⟶ J) → (Qh.obj M ⟶ Qh.obj J)) := by
        simpa [J] using hI M
      have hN :
          Function.Bijective
            (Qh.map : (N ⟶ J) → (Qh.obj N ⟶ Qh.obj J)) := by
        simpa [J] using hI N
      have : IsIso (Qh.map f) := (isIso_Qh_map_iff f).2 hf
      have hpre :
          Function.Bijective
            (fun g : Qh.obj N ⟶ Qh.obj J ↦ Qh.map f ≫ g) := by
        refine ⟨?_, ?_⟩
        · intro g₁ g₂ h
          exact (cancel_epi (Qh.map f)).1 h
        · intro g
          exact ⟨inv (Qh.map f) ≫ g, by simp⟩
      have hcomp :
          ((Qh.map :
              (M ⟶ J) →
                (Qh.obj M ⟶ Qh.obj J)) ∘
            fun g : N ⟶ J ↦ f ≫ g) =
          (fun g : Qh.obj N ⟶ Qh.obj J ↦ Qh.map f ≫ g) ∘
            (Qh.map :
              (N ⟶ J) →
                (Qh.obj N ⟶ Qh.obj J)) := by
        funext g
        simp [Functor.map_comp]
      have hcompBij :
          Function.Bijective
            (((Qh.map :
                (M ⟶ J) →
                  (Qh.obj M ⟶ Qh.obj J)) ∘
              fun g : N ⟶ J ↦ f ≫ g)) := by
        rw [hcomp]
        exact hpre.comp hN
      exact (Function.Bijective.of_comp_iff' hM _).mp hcompBij
  tfae_finish

end

end CochainComplex
