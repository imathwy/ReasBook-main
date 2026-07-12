import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced mathlib's canonical closed-subscheme owner
`Scheme.IdealSheafData.subscheme` and only the ordinary scheme-theoretic zero-locus API. The
source-facing zero scheme of a section of an invertible sheaf is therefore kept on the local
Chapter 31 owner `zeroIdealSheaf`, but the defining ideal is presented through the equivalent
affine-local annihilator-of-cokernel description of the restricted section map
`Γ(U, 𝒪_X) → Γ(U, \mathcal L)` on affine opens. For invertible `\mathcal L`, this is the same
ideal sheaf as the image of `\mathcal L^{-1} → \mathcal O_X` from Stacks 31.14.8 while avoiding
the noncanonical tensor-unit comparison data. -/

variable {X : Scheme.{u}}

local notation "ModX" => X.Modules

local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

private noncomputable abbrev zeroIdealSheafIdeal
    [MonoidalCategory ModX]
    (ℒ : ModX) (s : ℒ.sections) (U : X.affineOpens) :
    Ideal (Γ(X, U.1)) :=
  let φ :=
    (((ℒ.over U.1).unitHomEquiv.symm
        (SheafOfModules.pushforwardSections (𝟙 (X.ringCatSheaf.over U.1)) s)).val.app
      (op (Over.mk (𝟙 U.1)))).hom
  letI : Module (Γ(X, U.1)) (Γ(ℒ, U.1) ⧸ φ.range) := Submodule.Quotient.module φ.range
  Module.annihilator (Γ(X, U.1))
    (Γ(ℒ, U.1) ⧸ φ.range)

/-- The ideal sheaf on `X` whose affine-open ideals are the image ideals of the section-induced
map from `\mathcal L^{-1}` to `\mathcal O_X`; equivalently, on each affine open `U`, it is the
annihilator of the cokernel of the restricted section map
`Γ(U, \mathcal O_X) \to Γ(U, \mathcal L)`. -/
noncomputable def zeroIdealSheaf
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (zeroIdealSheafIdeal ℒ s)

/-- Definition 31.14.8: for a scheme `X`, an invertible sheaf `\mathcal L`, and a global
section `s \in \Gamma(X, \mathcal L)`, the zero scheme `Z(s)` is the closed subscheme defined by
the ideal sheaf which is, equivalently, the image ideal of the induced morphism
`\mathcal L^{-1} \to \mathcal O_X` or the affine-local annihilator of the cokernel of the
restricted section map. -/
@[stacks 02OQ]
noncomputable def zeroScheme
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) :
    Scheme :=
  (zeroIdealSheaf ℒ s).subscheme

/-- The canonical closed immersion `Z(s) ⟶ X` of the zero scheme of a section `s`. This keeps
the source-facing zero-scheme owner as the main entry while exposing the immersion needed by the
downstream factorization and Cartier-divisor API. -/
noncomputable abbrev zeroSchemeι
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) :
    zeroScheme ℒ s ⟶ X :=
  (zeroIdealSheaf ℒ s).subschemeι

end AlgebraicGeometry.Scheme
