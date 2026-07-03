import Mathlib
import StacksProject_2024.Chap13.Definition_13_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: short exact sequences of bounded-below cochain complexes and compatible
  bounded-below injective resolutions;
- sampled owner declarations:
  `CategoryTheory.ShortComplex.Hom`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CochainComplex.PlusWithTermsIn.ι`,
  `CochainComplex.plus`,
  `CochainComplex.InjectivePlus`,
  `CochainComplex.InjectiveResolution`;
- best owner abstraction: the resolving row should be owned by
  `ShortComplex (InjectivePlus 𝒜)`, its comparison with the given short exact sequence by a
  single `ShortComplex.Hom`, and short exactness by `ShortComplex.ShortExact`;
- primitive data here: the short exact resolving row in `InjectivePlus 𝒜`, the morphism from `S`
  to its underlying short complex, and the quasi-isomorphism witnesses on the three vertical
  components;
- derived API here: the source-facing existence theorems below, with any columnwise
  `InjectiveResolution` view recovered directly from the canonical row and comparison morphism.

Source/core/bridge triage:
- `source-facing`: the injective-resolution diagram data above a bounded-below short exact
  sequence, together with its existence theorems;
- `core/canonical`: `ShortComplex (InjectivePlus 𝒜)`, `ShortComplex.Hom`,
  `ShortComplex.ShortExact`, `CochainComplex.InjectiveResolution`, and the generic
  extension-closure interface `ObjectProperty.prop_X₂_of_shortExact`;
- `bridge/view`: the `strictlyGE_zero` existence specializations below.
-/

local notation "injPlusι" => PlusWithTermsIn.ι (isInjective 𝒜)

section

variable [EnoughInjectives 𝒜]

-- Proof sketch: choose an injective resolution of the left complex, push out the short exact
-- sequence along it to reduce to the termwise split case, resolve the right complex, lift the
-- connecting morphism to the chosen injective resolutions by Lemma 13.18.6, and use the resulting
-- upper-triangular differential on the direct-sum complex to build the middle injective
-- resolution and the lower short exact row.
/-- Lemma 13.18.9: if `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` is a short exact sequence of cochain complexes
whose outer terms are bounded below, then it extends to a commutative diagram whose vertical maps
are injective resolutions and whose lower row is again a short exact sequence of complexes. The
middle term is bounded below because bounded-below cochain complexes are closed under extensions.
-/
theorem exists_injectiveResolutionDiagram_of_shortExact
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃) :
    ∃ row : ShortComplex (InjectivePlus 𝒜), ∃ hom : S ⟶ row.map injPlusι,
      (row.map injPlusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧ QuasiIso hom.τ₂ ∧ QuasiIso hom.τ₃ := sorry

-- Proof sketch: run the construction of `exists_injectiveResolutionDiagram_of_shortExact` starting
-- from the prescribed injective resolution of the left complex, then perform the pushout
-- reduction and the lifted-connecting-morphism construction relative to that fixed choice.
/-- Given a chosen injective resolution of the left complex, the diagram can be built with that
resolution as its left column, provided the outer terms of the short exact row are bounded below.
The middle term is then bounded below by short exactness. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃)
    (I : InjectiveResolution S.X₁) :
    ∃ (J K : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧ QuasiIso φ.τ₃ := sorry

-- Proof sketch: choose the left and right injective resolutions using Lemma 13.18.3 with lower
-- bound `0`, so their targets are zero in negative degrees, and then carry out the same
-- upper-triangular construction of the middle resolution; the direct-sum model is also zero in
-- negative degrees.
/-- If the outer terms of the original short exact sequence are zero in negative degrees, then the
middle term is also zero in negative degrees, and the injective-resolution diagram can be chosen
so that all three lower resolving complexes are zero in negative degrees as well. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_strictlyGE_zero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : S.X₁.IsStrictlyGE 0) (hC : S.X₃.IsStrictlyGE 0) :
    ∃ row : ShortComplex (InjectivePlus 𝒜), ∃ hom : S ⟶ row.map injPlusι,
      (row.map injPlusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧
        QuasiIso hom.τ₂ ∧
        QuasiIso hom.τ₃ ∧
        (row.X₁ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
        (row.X₂ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
        (row.X₃ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 := sorry

-- Proof sketch: combine the prescribed-left-resolution construction with the bounded-below choice
-- from the previous theorem, using the given lower bound on the chosen left resolution to keep
-- the whole lower row zero in negative degrees.
/-- If the outer terms of the original sequence are zero in negative degrees and the chosen left
injective resolution is also zero in negative degrees, then the middle term is automatically zero
in negative degrees, and the diagram can be built with that prescribed left comparison map and
with the remaining resolving complexes zero in negative degrees. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution_strictlyGE_zero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (hI : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE 0)
    (hA : S.X₁.IsStrictlyGE 0) (hC : S.X₃.IsStrictlyGE 0) :
    ∃ (J K : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧
          QuasiIso φ.τ₃ ∧
          (J : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
          (K : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 := sorry

end

end CochainComplex
