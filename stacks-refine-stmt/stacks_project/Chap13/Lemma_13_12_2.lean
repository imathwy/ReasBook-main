import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Pretriangulated
open DerivedCategory
open HomologicalComplex.HomologySequence

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.12.2:
- primary domain: distinguished triangles in the derived category attached to short exact
  sequences of cochain complexes, together with morphisms induced by maps of short exact
  sequences;
- sampled owner declarations in this domain:
  `DerivedCategory.triangleOfSES`,
  `DerivedCategory.triangleOfSES.map`,
  `HomologicalComplex.HomologySequence.quasiIso_τ₃`,
  `Pretriangulated.Triangle.isIso_of_isIsos`,
  `DerivedCategory.Q`'s instance sending a quasi-isomorphism to an isomorphism;
- best owner abstraction: the core owner is the canonical triangle morphism
  `DerivedCategory.triangleOfSES.map`; its being an isomorphism is derived API from the three
  component morphisms and the ambient triangle-category lemma `Triangle.isIso_of_isIsos`;
- source/core/bridge triage:
  `source-facing`: the induced morphism between the two distinguished triangles attached to the
    short exact sequences;
  `core/canonical`: `triangleOfSES.map` together with `Triangle.isIso_of_isIsos` and the
    localization functor `DerivedCategory.Q`;
  `bridge/view`: none beyond the canonical passage from quasi-isomorphisms of cochain complexes to
    isomorphisms after applying `Q`.

Primitive data are only the short exact sequences, the morphism `φ`, and the quasi-isomorphism
assumptions on `φ.τ₁` and `φ.τ₂`. The third quasi-isomorphism is already derived by the canonical
owner lemma `HomologicalComplex.HomologySequence.quasiIso_τ₃`, and the fact that the induced
triangle morphism is an isomorphism is derived from those owner-level data, so no auxiliary
wrapper or second triangle-level API should be introduced here.
-/

-- Proof sketch: derive `QuasiIso φ.τ₃` from `hτ₁` and `hτ₂` using
-- `HomologicalComplex.HomologySequence.quasiIso_τ₃`. The three components of
-- `triangleOfSES.map hS hT φ` are then `Q.map φ.τ₁`, `Q.map φ.τ₂`, and `Q.map φ.τ₃`, so
-- `Triangle.isIso_of_isIsos` applies directly to the canonical triangle morphism.
/- Companion recall: for a morphism of short exact sequences of cochain complexes, if the first
two vertical maps are quasi-isomorphisms, then the third vertical map is the canonical owner
consequence `quasiIso_τ₃`. -/
recall quasiIso_τ₃

/-- Lemma 13.12.2: a morphism between short exact sequences of cochain complexes whose first two
vertical maps are quasi-isomorphisms induces an isomorphism between the associated distinguished
triangles in the derived category; the third vertical map is automatically a quasi-isomorphism. -/
theorem triangleOfSES_map_isIso_of_quasiIso
    {S T : ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (hτ₁ : QuasiIso φ.τ₁) (hτ₂ : QuasiIso φ.τ₂) :
    IsIso (triangleOfSES.map hS hT φ) := by
  letI : QuasiIso φ.τ₁ := hτ₁
  letI : QuasiIso φ.τ₂ := hτ₂
  letI : QuasiIso φ.τ₃ := quasiIso_τ₃ φ hS hT hτ₁ hτ₂
  refine Triangle.isIso_of_isIsos (triangleOfSES.map hS hT φ) ?_ ?_ ?_
  all_goals
    simpa [triangleOfSES.map] using (inferInstance : IsIso _)

end CategoryTheory
