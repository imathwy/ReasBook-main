import Mathlib
import StacksProject_2024.Chap29.Definition_29_45_1
import StacksProject_2024.Chap29.Definition_29_47_3
import StacksProject_2024.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed the normalization owner
-- `Scheme.Hom.normalization`/`Scheme.normalizationTo`, while local and semantic search found no
-- existing seminormalization owner for schemes in this project snapshot. The source-facing
-- fallback is therefore the relative universal-property owner below.

namespace Scheme.Hom

/-- A seminormalization of `X` in `Y` along `f : Y ⟶ X` is a factorization
`Y ⟶ X' ⟶ X` in which `X' ⟶ X` is a universal homeomorphism inducing isomorphisms on residue
fields, `X'` is seminormal, and the factorization is initial among such factorizations. -/
@[stacks 0H3Q]
structure RelativeSeminormalization {X Y : Scheme.{u}} (f : Y ⟶ X) where
  /-- The underlying scheme `X^{Y /sn}`. -/
  obj : Scheme.{u}
  /-- The seminormalization morphism `X^{Y /sn} ⟶ X`. -/
  toScheme : obj ⟶ X
  /-- The canonical factorization map `Y ⟶ X^{Y /sn}`. -/
  lift : Y ⟶ obj
  /-- The factorization `f = lift ≫ toScheme`. -/
  fac : lift ≫ toScheme = f
  /-- The relative seminormalization morphism is a universal homeomorphism. -/
  isUniversalHomeomorphism_toScheme : UniversalHomeomorphism toScheme
  /-- The underlying scheme of a relative seminormalization is seminormal. -/
  seminormal_obj : Scheme.Seminormal obj
  /-- The relative seminormalization morphism induces residue-field isomorphisms. -/
  residueFieldMap_isIso : ∀ x : obj, IsIso (Scheme.Hom.residueFieldMap toScheme x)
  /-- The relative seminormalization is initial among seminormal universal-homeomorphism
  factorizations of `f` that induce residue-field isomorphisms. -/
  desc :
    ∀ {Z : Scheme.{u}} (g : Y ⟶ Z) (π : Z ⟶ X),
      UniversalHomeomorphism π →
      Scheme.Seminormal Z →
      (∀ z : Z, IsIso (Scheme.Hom.residueFieldMap π z)) →
      g ≫ π = f →
      ∃! h : obj ⟶ Z, lift ≫ h = g ∧ h ≫ π = toScheme

end Scheme.Hom

namespace Scheme.Hom.RelativeSeminormalization

/-- A relative seminormalization carries a universal-homeomorphism structure on its map to the
base scheme. -/
@[stacks 0H3Q]
instance instUniversalHomeomorphismToScheme
    {X Y : Scheme.{u}} {f : Y ⟶ X} (S : Scheme.Hom.RelativeSeminormalization f) :
    UniversalHomeomorphism S.toScheme :=
  S.isUniversalHomeomorphism_toScheme

/-- The underlying scheme of a relative seminormalization is seminormal. -/
@[stacks 0H3Q]
instance instSeminormalObj
    {X Y : Scheme.{u}} {f : Y ⟶ X} (S : Scheme.Hom.RelativeSeminormalization f) :
    Scheme.Seminormal S.obj :=
  S.seminormal_obj

/-- The defining factorization of a relative seminormalization recovers the original morphism. -/
@[stacks 0H3Q]
theorem comp_toScheme
    {X Y : Scheme.{u}} {f : Y ⟶ X} (S : Scheme.Hom.RelativeSeminormalization f) :
    S.lift ≫ S.toScheme = f := sorry

/-- Lemma 29.55.7: if every quasi-compact open of `X` has finitely many irreducible components,
then the seminormalization of `X` in its normalization `X^ν` satisfies the universal property of
the seminormalization of `X`. Equivalently, in the source notation,
`X^{sn} = X^{X^ν /sn}`. -/
@[stacks 0H3Q]
theorem isSeminormalizationOfNormalization
    (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    (S : Scheme.Hom.RelativeSeminormalization (Scheme.normalizationTo X)) :
    ∀ {Z : Scheme.{u}} (π : Z ⟶ X),
      UniversalHomeomorphism π →
      Scheme.Seminormal Z →
      (∀ z : Z, IsIso (Scheme.Hom.residueFieldMap π z)) →
      ∃! h : S.obj ⟶ Z, h ≫ π = S.toScheme := sorry

end Scheme.Hom.RelativeSeminormalization

end AlgebraicGeometry
