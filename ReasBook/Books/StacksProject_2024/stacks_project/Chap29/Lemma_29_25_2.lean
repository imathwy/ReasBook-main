import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the scheme-morphism flatness owner
-- `AlgebraicGeometry.Flat` and its affine-open API `AlgebraicGeometry.flat_iff`. For the module
-- side, Chapter 29 already exposes the scheme-level owner `flatOver`; this file records the
-- affine-open and local-cover criteria as source-facing bridges around that owner.

/-- The `\mathcal O_X`-module `ℱ`, viewed by restriction of scalars as an
`f^{-1}\mathcal O_S`-module. -/
abbrev relativeModuleOver
    (ℱ : X.Modules) (f : X ⟶ S) :=
  SheafOfModules.relativeModule ℱ f.toShHom

/-- Sectionwise flatness of `ℱ` on the affine open pair `U ⊆ f^{-1}(V)`. -/
abbrev flatOnAffineOpenPair
    (ℱ : X.Modules) (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) : Prop :=
  let _ : Module Γ(S, V) Γ(ℱ, U) := Module.compHom (Γ(ℱ, U)) (f.appLE V U e).hom
  Module.Flat Γ(S, V) Γ(ℱ, U)

/-- Affine-open sectionwise flatness of `ℱ` over `S`. -/
abbrev affineOpenSectionsFlatOver
    (ℱ : X.Modules) (f : X ⟶ S) : Prop :=
  ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
    ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
      flatOnAffineOpenPair ℱ f U V e

/-- Data of an open cover criterion for flatness of `ℱ` over `S`. -/
structure FlatOpenCover
    (ℱ : X.Modules) (f : X ⟶ S) where
  J : Type v
  V : J → S.Opens
  iSup_eq_top : (⨆ j, V j) = ⊤
  I : J → Type w
  U : ∀ j, I j → X.Opens
  iSup_eq_preimage : ∀ j, (⨆ i, U j i) = f ⁻¹ᵁ V j
  flat_restrict :
    ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, flatOver (ℱ.restrict (U j i).ι) (f.resLE (V j) (U j i) e)

/-- Data of an affine-open cover criterion for flatness of `ℱ` over `S`. -/
structure FlatAffineOpenCover
    (ℱ : X.Modules) (f : X ⟶ S) where
  J : Type v
  V : J → S.Opens
  iSup_eq_top : (⨆ j, V j) = ⊤
  affine_V : ∀ j, IsAffineOpen (V j)
  I : J → Type w
  U : ∀ j, I j → X.Opens
  iSup_eq_preimage : ∀ j, (⨆ i, U j i) = f ⁻¹ᵁ V j
  affine_U : ∀ j i, IsAffineOpen (U j i)
  appLE_flat :
    ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, flatOnAffineOpenPair ℱ f (U j i) (V j) e

/-- Lemma 29.25.2 (1): for a quasi-coherent `\mathcal O_X`-module `ℱ`, flatness over `S`
is equivalent to affine-open sectionwise flatness over the corresponding rings of functions. -/
@[stacks 01U4]
theorem flatOver_iff_affineOpenSectionsFlatOver
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S) :
    flatOver ℱ f ↔ affineOpenSectionsFlatOver ℱ f := sorry

/-- Lemma 29.25.2 (2): for a quasi-coherent `\mathcal O_X`-module `ℱ`, flatness over `S`
is equivalent to the existence of an open cover of `S` and open covers of the local preimages on
which the restrictions of `ℱ` are flat over the corresponding restricted base schemes. -/
@[stacks 01U4]
theorem flatOver_iff_hasFlatOpenCover
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S) :
    flatOver ℱ f ↔ Nonempty (FlatOpenCover ℱ f) := sorry

/-- Lemma 29.25.2 (3): for a quasi-coherent `\mathcal O_X`-module `ℱ`, flatness over `S`
is equivalent to the existence of affine open covers on which all section modules are flat over
the corresponding affine base rings. -/
@[stacks 01U4]
theorem flatOver_iff_hasFlatAffineOpenCover
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : X ⟶ S) :
    flatOver ℱ f ↔ Nonempty (FlatAffineOpenCover ℱ f) := sorry

/-- Lemma 29.25.2 (4): if `ℱ` is flat over `S`, then its restriction to any open `U ⊆ X`
mapping into an open `V ⊆ S` remains flat over `V`. -/
@[stacks 01U4]
theorem flatOver_resLE_of_flatOver
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] {f : X ⟶ S}
    (hflat : flatOver ℱ f)
    {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    flatOver (ℱ.restrict U.ι) (f.resLE V U e) := sorry

end AlgebraicGeometry.Scheme.Modules
