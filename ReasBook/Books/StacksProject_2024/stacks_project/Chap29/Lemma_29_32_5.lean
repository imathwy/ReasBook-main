import Mathlib
import StacksProject_2024.Chap17.Definition_17_28_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {R A : CommRingCat.{u}}

-- Semantic recall / analogue check:
-- `lean_leansearch` recalled the affine Kähler-differential owners
-- `CommRingCat.KaehlerDifferential` and `CommRingCat.KaehlerDifferential.d`, while local Chapter
-- 29 precedent in `Lemma_29_32_4` fixes the top-sections comparison through `Scheme.ΓSpecIso`.
-- Since `Lemma_29_32_3` already supplies the restriction bridge to arbitrary affine opens, the
-- source-facing core statement here is the affine `Spec(A) ⟶ Spec(R)` comparison.

/-- Lemma 29.32.5: for a ring map `φ : R ⟶ A`, corresponding to the affine morphism
`Spec(A) ⟶ Spec(R)`, there is a unique `A`-linear isomorphism
`Γ(\operatorname{Spec}(A), \Omega_{\operatorname{Spec}(A)/\operatorname{Spec}(R)}) ≅ \Omega_{A/R}`
compatible with the global relative differential and the universal Kähler differential. Via
Lemma 29.32.3, this is the affine-open comparison for an arbitrary morphism of schemes. -/
@[stacks 01UT]
theorem existsUnique_affineGlobalSectionsLinearEquiv_kaehlerDifferential
    (φ : R ⟶ A) :
    let M := Γ(Ω[(Spec.map φ).toShHom], ⊤)
    letI : Algebra R A := φ.hom.toAlgebra
    letI : Module A M := Module.compHom M (Scheme.ΓSpecIso A).inv.hom
    letI : Module R M := Module.compHom M φ.hom
    letI : IsScalarTower R A M := IsScalarTower.of_compHom R A M
    letI : SMulCommClass A R M := inferInstance
    letI : SMulCommClass R A M := inferInstance
    ∃! eΩ : M ≃ₗ[A] CommRingCat.KaehlerDifferential φ,
      ∀ a : A,
        eΩ (((d[(Spec.map φ).toShHom]).app (op ⊤)).d ((Scheme.ΓSpecIso A).inv.hom a)) =
          CommRingCat.KaehlerDifferential.d a := sorry

end

end AlgebraicGeometry
