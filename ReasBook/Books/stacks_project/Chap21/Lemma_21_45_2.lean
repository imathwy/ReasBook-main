import Mathlib

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable (Mod : Type w) [Category.{v} Mod] [Abelian Mod]
variable (ModLoc : C → Type w)
variable [∀ U : C, Category.{v} (ModLoc U)]
variable [∀ U : C, Abelian (ModLoc U)]

/- The parameter `strictlyPerfect U` stands for the strict-perfectness predicate on complexes of
`\mathcal O_U`-modules. -/
variable (strictlyPerfect : ∀ U : C, CochainComplex (ModLoc U) ℤ → Prop)

/- The parameter `localizedRestrictionDerived U` stands for the derived restriction functor
`D(\mathcal O) → D(\mathcal O_U)`. -/
variable (localizedRestrictionDerived :
  ∀ U : C, DerivedCategory Mod ⥤ DerivedCategory (ModLoc U))

/- The parameter `complexIsMPseudoCoherent` stands for the complex-level `m`-pseudo-coherence
predicate from Definition `21.45.1`. -/
variable (complexIsMPseudoCoherent : CochainComplex Mod ℤ → ℤ → Prop)

/- The parameter `derivedIsMPseudoCoherent` stands for the derived-category `m`-pseudo-coherence
predicate from Definition `21.45.1`. -/
variable (derivedIsMPseudoCoherent : DerivedCategory Mod → ℤ → Prop)

/- The parameter `localizedDerivedIsMPseudoCoherent U` stands for `m`-pseudo-coherence on the
localized ringed site over `U`. -/
variable (localizedDerivedIsMPseudoCoherent :
  ∀ U : C, DerivedCategory (ModLoc U) → ℤ → Prop)

section

variable {J : GrothendieckTopology C}
variable {Mod : Type w} [Category.{v} Mod] [Abelian Mod]
variable {ModLoc : C → Type w}
variable [∀ U : C, Category.{v} (ModLoc U)]
variable [∀ U : C, Abelian (ModLoc U)]
variable {strictlyPerfect : ∀ U : C, CochainComplex (ModLoc U) ℤ → Prop}
variable {localizedRestrictionDerived :
  ∀ U : C, DerivedCategory Mod ⥤ DerivedCategory (ModLoc U)}

/-- A localized derived object over `U` admits a strict-perfect approximation in degree `m` when
it is represented by a strictly perfect complex whose comparison morphism induces cohomology
isomorphisms above `m` and an epimorphism in degree `m`. -/
abbrev HasStrictlyPerfectApproximationInDegree
    (U : C) (K : DerivedCategory Mod) (m : ℤ) : Prop :=
  ∃ E' : CochainComplex (ModLoc U) ℤ,
    strictlyPerfect U E' ∧
      ∃ α :
        ((DerivedCategory.Q :
            CochainComplex (ModLoc U) ℤ ⥤
              DerivedCategory (ModLoc U)).obj E') ⟶
          (localizedRestrictionDerived U).obj K,
        (∀ j : ℤ, m < j →
          IsIso ((DerivedCategory.homologyFunctor (ModLoc U) j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor (ModLoc U) m).map α)

end

/- Local shorthand for the strict-perfect approximation predicate used in Lemma `21.45.2`. -/
local notation "LocalApproximationInDegree" =>
  @HasStrictlyPerfectApproximationInDegree
    C Mod _ _ ModLoc _ _ strictlyPerfect localizedRestrictionDerived

-- Proof sketch: choose a complex representing `K`. By Lemma `21.44.8`, after refining the given
-- cover of the final object `X`, each local derived morphism from a strictly perfect complex is
-- represented by an actual chain map to the localized representative complex. Since `X` is final,
-- covers of `X` restrict to covers of every object of `C`, and the resulting local chain maps are
-- exactly the data required in Definition `21.45.1`.
/-- Lemma 21.45.2 (1): if a derived `\mathcal O`-module admits on a cover of a final object local
strictly perfect approximations with cohomology isomorphisms above `m` and an epimorphism in
degree `m`, then it is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_exists_cover_on_finalObject
    (K : DerivedCategory Mod) (m : ℤ) (X : C) (_hX : Limits.IsTerminal X)
    (hcover :
      ∃ T : J.Cover X, ∀ I : T.Arrow,
        LocalApproximationInDegree I.Y K m) :
    derivedIsMPseudoCoherent K m := sorry

-- Proof sketch: unfold `derivedIsMPseudoCoherent K m` to obtain some representing complex `E`.
-- Transport the chosen representation `F ≅ K` to an isomorphism `Q.obj F ≅ Q.obj E`. Refining
-- the local covers and applying Lemma `21.44.8` transfers the strictly perfect local
-- approximations from `E` to `F`, which is exactly the condition `complexIsMPseudoCoherent F m`.
/-- Lemma 21.45.2 (2): if `K` is `m`-pseudo-coherent, then every complex representing `K` is
`m`-pseudo-coherent as a complex of `\mathcal O`-modules. -/
theorem cochainComplex_isMPseudoCoherent_of_represents_isMPseudoCoherent
    (K : DerivedCategory Mod) (F : CochainComplex Mod ℤ) (m : ℤ)
    (e : ((DerivedCategory.Q : CochainComplex Mod ℤ ⥤ DerivedCategory Mod).obj F) ≅ K)
    (hK : derivedIsMPseudoCoherent K m) :
    complexIsMPseudoCoherent F m := sorry

-- Proof sketch: apply the local hypothesis to the terminal object `U` occurring in the definition
-- of complex-level `m`-pseudo-coherence. For each member of the chosen cover of `U`, unfold the
-- assumption that the restriction of `K` is `m`-pseudo-coherent and compose the corresponding
-- covers using the site-composition axiom from Definition `7.6.2`; this gives the local strictly
-- perfect approximations required for `K` itself.
/-- Lemma 21.45.2 (3): if every object of the site admits a covering on which the localized
restriction of `K` is `m`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_locally_isMPseudoCoherent
    (K : DerivedCategory Mod) (m : ℤ)
    (hlocal :
      ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
        localizedDerivedIsMPseudoCoherent I.Y
          ((localizedRestrictionDerived I.Y).obj K) m) :
    derivedIsMPseudoCoherent K m := sorry

end

end SheafOfModules.RingedSite
