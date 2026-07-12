import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.subscheme`,
`Scheme.IdealSheafData.ideal`, `Scheme.IdealSheafData.support`, and
`Scheme.Modules.pushforward` as the canonical owners. Local Chapter 29 support files use
`moduleSupport` for scheme-module support, so this item is stated on the closed subscheme
`I : X.IdealSheafData` whose affine-open ideals are the annihilators of affine sections. -/

/-- Lemma 29.5.4 (1): for a finite type quasi-coherent `\mathcal O_X`-module `ℱ`,
there is a smallest closed subscheme through which `ℱ` is the pushforward of a
quasi-coherent module. In the `IdealSheafData` owner, this closed subscheme is characterized
on every affine open by the annihilator of the corresponding section module. -/
@[stacks 05JU]
theorem exists_minimal_closedSubscheme_pushforward_iso :
    ∃ I : X.IdealSheafData,
      (∀ U : X.affineOpens,
        I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1))) ∧
      ∀ J : X.IdealSheafData,
        (∃ 𝒢 : J.subscheme.Modules,
          ∃ _ : 𝒢.IsQuasicoherent,
            Nonempty ((Scheme.Modules.pushforward J.subschemeι).obj 𝒢 ≅ ℱ)) ↔ J ≤ I := sorry

/-- Lemma 29.5.4 (2): the closed subscheme from Lemma 29.5.4 (1), characterized affine-locally
by annihilator ideals, has underlying closed subset equal to the support of `ℱ`. -/
@[stacks 05JU]
theorem moduleSupport_eq_support_of_affineOpen_ideal_eq_annihilator
    (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens,
      I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1))) :
    moduleSupport ℱ = (I.support : Set X) := sorry

/-- Lemma 29.5.4 (3): on the closed subscheme from Lemma 29.5.4 (1), there is a finite type
quasi-coherent module whose pushforward is `ℱ`, and its support is all of that closed
subscheme. -/
@[stacks 05JU]
theorem exists_finiteType_module_on_annihilator_closedSubscheme
    (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens,
      I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1))) :
    ∃ 𝒢 : I.subscheme.Modules,
      ∃ _ : 𝒢.IsQuasicoherent,
        ∃ _ : 𝒢.IsFiniteType,
          (∃ _e : (Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ,
            moduleSupport 𝒢 = Set.univ) := sorry

/-- Lemma 29.5.4 (4): the quasi-coherent module on the closed subscheme from Lemma 29.5.4 (1)
whose pushforward is `ℱ` is unique up to a unique isomorphism compatible with the chosen
pushforward identifications. -/
@[stacks 05JU]
theorem existsUnique_iso_of_pushforward_iso_annihilator_closedSubscheme
    (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens,
      I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1)))
    (𝒢 𝒢' : I.subscheme.Modules) [𝒢.IsQuasicoherent] [𝒢'.IsQuasicoherent]
    (e : (Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ)
    (e' : (Scheme.Modules.pushforward I.subschemeι).obj 𝒢' ≅ ℱ) :
    ∃! α : 𝒢 ≅ 𝒢',
      ((Scheme.Modules.pushforward I.subschemeι).mapIso α).trans e' = e := sorry

end AlgebraicGeometry.Scheme.Modules
