import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v w

section

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical owner `LocallyQuasiFinite`, the affine-open
  characterization `locallyQuasiFinite_iff`, and
  `LocallyQuasiFinite.quasiFinite_appLE`.
- Local Chapter 29 precedent in `Lemma_29_15_2.lean`, `Lemma_29_21_2.lean`,
  `Lemma_29_25_3.lean`, and `Lemma_29_34_2.lean` uses this owner-and-cover shape for the
  corresponding local properties.
- The Stacks tag evidence is consistent: item tag `01TK` and source URL
  `https://stacks.math.columbia.edu/tag/01TK`.
-/

/-- Data of an open-cover criterion for local quasi-finiteness of a morphism of schemes. -/
@[stacks 01TK]
structure LocallyQuasiFiniteOpenCover
    (f : X ⟶ S) where
  J : Type v
  V : J → S.Opens
  iSup_eq_top : (⨆ j, V j) = ⊤
  I : J → Type w
  U : ∀ j, I j → X.Opens
  iSup_eq_preimage : ∀ j, (⨆ i, U j i) = f ⁻¹ᵁ V j
  locallyQuasiFinite_resLE :
    ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, LocallyQuasiFinite (f.resLE (V j) (U j i) e)

/-- Data of an affine-open-cover criterion for local quasi-finiteness of a morphism of schemes. -/
@[stacks 01TK]
structure LocallyQuasiFiniteAffineOpenCover
    (f : X ⟶ S) where
  J : Type v
  V : J → S.Opens
  iSup_eq_top : (⨆ j, V j) = ⊤
  affine_V : ∀ j, IsAffineOpen (V j)
  I : J → Type w
  U : ∀ j, I j → X.Opens
  iSup_eq_preimage : ∀ j, (⨆ i, U j i) = f ⁻¹ᵁ V j
  affine_U : ∀ j i, IsAffineOpen (U j i)
  appLE_quasiFinite :
    ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j,
      (CommRingCat.Hom.hom (f.appLE (V j) (U j i) e)).QuasiFinite

/-- Lemma 29.20.11 (1): a morphism of schemes is locally quasi-finite if and only if for every
pair of affine opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`, the induced ring map
`\Gamma(V, \mathcal O_S) → \Gamma(U, \mathcal O_X)` is quasi-finite. -/
@[stacks 01TK]
theorem locallyQuasiFinite_iff_affineOpen_appLE_quasiFinite
    (f : X ⟶ S) :
    LocallyQuasiFinite f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).QuasiFinite := sorry

/-- Lemma 29.20.11 (2): a morphism of schemes is locally quasi-finite if and only if there is an
open cover of the base and open covers of the corresponding inverse images such that every
restricted morphism is locally quasi-finite. -/
@[stacks 01TK]
theorem locallyQuasiFinite_iff_hasLocallyQuasiFiniteOpenCover
    (f : X ⟶ S) :
    LocallyQuasiFinite f ↔ Nonempty (LocallyQuasiFiniteOpenCover f) := sorry

/-- Lemma 29.20.11 (3): a morphism of schemes is locally quasi-finite if and only if there are
affine open covers `V_j` of `S` and `U_i` of each `f^{-1}(V_j)` such that all induced ring maps on
sections are quasi-finite. -/
@[stacks 01TK]
theorem locallyQuasiFinite_iff_hasLocallyQuasiFiniteAffineOpenCover
    (f : X ⟶ S) :
    LocallyQuasiFinite f ↔ Nonempty (LocallyQuasiFiniteAffineOpenCover f) := sorry

/-- Lemma 29.20.11 (4): if `f : X ⟶ S` is locally quasi-finite, then for any open subschemes
`U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, the restricted morphism `U ⟶ V` is locally quasi-finite. -/
@[stacks 01TK]
theorem locallyQuasiFinite_resLE_of_locallyQuasiFinite
    {f : X ⟶ S} (hloc : LocallyQuasiFinite f) {U : X.Opens} {V : S.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    LocallyQuasiFinite (f.resLE V U e) := sorry

end Scheme.Hom

end
