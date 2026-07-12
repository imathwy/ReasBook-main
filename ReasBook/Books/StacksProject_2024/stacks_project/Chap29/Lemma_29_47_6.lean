import Mathlib
import StacksProject_2024.Chap29.Definition_29_45_1
import StacksProject_2024.Chap29.Definition_29_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical `ObjectProperty.FullSubcategory`
-- and `IsTerminal`/`HasTerminal` APIs for source-facing final-object statements. Local Chapter 29
-- precedent supplies `UniversalHomeomorphism`, `SeminormalRing`, and
-- `AbsolutelyWeaklyNormalRing`. The Stacks tag evidence is consistent: item tag `0EUR` agrees
-- with the source URL ending in `/tag/0EUR`.

/-- The object property on `CommAlgCat A` selecting `A`-algebras whose affine spectrum map to
`Spec A` is a universal homeomorphism. -/
@[stacks 0EUR]
abbrev absoluteWeakNormalizationAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B : CommAlgCat.{u} A ↦
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- Membership in the absolute-weak-normalization algebra property is exactly the source-facing
universal-homeomorphism condition on affine spectra. -/
theorem absoluteWeakNormalizationAlgebraProperty_iff
    (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    absoluteWeakNormalizationAlgebraProperty A B ↔
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))) := sorry

/-- The category of `A`-algebras inducing universal homeomorphisms on spectra. -/
@[stacks 0EUR]
abbrev AbsoluteWeakNormalizationAlgebras (A : Type u) [CommRing A] : Type (u + 1) :=
  (absoluteWeakNormalizationAlgebraProperty A).FullSubcategory

/-- An object of the absolute-weak-normalization algebra category has the defining
universal-homeomorphism property. -/
theorem AbsoluteWeakNormalizationAlgebras.property
    (A : Type u) [CommRing A] (B : AbsoluteWeakNormalizationAlgebras A) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A (B.1 : Type u)))) := sorry

/-- The object property on `CommAlgCat A` selecting `A`-algebras whose affine spectrum map to
`Spec A` is a universal homeomorphism and induces isomorphisms on all residue fields. -/
@[stacks 0EUR]
abbrev seminormalizationAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B : CommAlgCat.{u} A ↦
    let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    UniversalHomeomorphism f ∧ ∀ x : Spec (CommRingCat.of B), IsIso (f.residueFieldMap x)

/-- Membership in the seminormalization algebra property is exactly the conjunction of universal
homeomorphism and residue-field isomorphism conditions on affine spectra. -/
theorem seminormalizationAlgebraProperty_iff
    (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    seminormalizationAlgebraProperty A B ↔
      (let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
        Spec.map (CommRingCat.ofHom (algebraMap A B))
      UniversalHomeomorphism f ∧ ∀ x : Spec (CommRingCat.of B), IsIso (f.residueFieldMap x)) := sorry

/-- The category of `A`-algebras inducing residue-field isomorphisms and universal
homeomorphisms on spectra. -/
@[stacks 0EUR]
abbrev SeminormalizationAlgebras (A : Type u) [CommRing A] : Type (u + 1) :=
  (seminormalizationAlgebraProperty A).FullSubcategory

/-- An object of the seminormalization algebra category has the defining universal
homeomorphism and residue-field isomorphism properties. -/
theorem SeminormalizationAlgebras.property
    (A : Type u) [CommRing A] (B : SeminormalizationAlgebras A) :
    (let f : Spec (CommRingCat.of (B.1 : Type u)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (B.1 : Type u)))
    UniversalHomeomorphism f ∧
      ∀ x : Spec (CommRingCat.of (B.1 : Type u)), IsIso (f.residueFieldMap x)) := sorry

/-- Lemma 29.47.6 (1): the category of ring maps `A → B` inducing a universal homeomorphism on
spectra has a final object, denoted in the source by `A → A^{awn}`. -/
@[stacks 0EUR, instance]
instance instHasTerminalAbsoluteWeakNormalizationAlgebras
    (A : Type u) [CommRing A] :
    HasTerminal (AbsoluteWeakNormalizationAlgebras A) := sorry

/-- Lemma 29.47.6 (2): for an `A`-algebra in the universal-homeomorphism category, the induced
map to the final object `A^{awn}` is an isomorphism exactly when the algebra is absolutely weakly
normal. -/
@[stacks 0EUR]
theorem isIso_to_absoluteWeakNormalization_iff_absolutelyWeaklyNormalRing
    (A : Type u) [CommRing A] (B : AbsoluteWeakNormalizationAlgebras A) :
    IsIso (terminal.from B : B ⟶ ⊤_ (AbsoluteWeakNormalizationAlgebras A)) ↔
      AbsolutelyWeaklyNormalRing (B.1 : Type u) := sorry

/-- Lemma 29.47.6 (3): the category of ring maps `A → B` inducing isomorphisms on residue fields
and a universal homeomorphism on spectra has a final object, denoted in the source by
`A → A^{sn}`. -/
@[stacks 0EUR, instance]
instance instHasTerminalSeminormalizationAlgebras
    (A : Type u) [CommRing A] :
    HasTerminal (SeminormalizationAlgebras A) := sorry

/-- Lemma 29.47.6 (4): for an `A`-algebra in the residue-field-isomorphism and
universal-homeomorphism category, the induced map to the final object `A^{sn}` is an isomorphism
exactly when the algebra is seminormal. -/
@[stacks 0EUR]
theorem isIso_to_seminormalization_iff_seminormalRing
    (A : Type u) [CommRing A] (B : SeminormalizationAlgebras A) :
    IsIso (terminal.from B : B ⟶ ⊤_ (SeminormalizationAlgebras A)) ↔
      SeminormalRing (B.1 : Type u) := sorry

/-- Lemma 29.47.6 (5): every ring map `φ : A → A'` induces a unique compatible map
`φ^{awn} : A^{awn} → (A')^{awn}` between the final objects of the absolute-weak-normalization
categories. -/
@[stacks 0EUR]
theorem existsUnique_absoluteWeakNormalizationMap
    {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃! φawn : ((⊤_ (AbsoluteWeakNormalizationAlgebras A)).1 : Type u) →+*
        ((⊤_ (AbsoluteWeakNormalizationAlgebras A')).1 : Type u),
      φawn.comp (algebraMap A ((⊤_ (AbsoluteWeakNormalizationAlgebras A)).1 : Type u)) =
        (algebraMap A' ((⊤_ (AbsoluteWeakNormalizationAlgebras A')).1 : Type u)).comp φ := sorry

/-- Lemma 29.47.6 (6): every ring map `φ : A → A'` induces a unique compatible map
`φ^{sn} : A^{sn} → (A')^{sn}` between the final objects of the seminormalization categories. -/
@[stacks 0EUR]
theorem existsUnique_seminormalizationMap
    {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃! φsn : ((⊤_ (SeminormalizationAlgebras A)).1 : Type u) →+*
        ((⊤_ (SeminormalizationAlgebras A')).1 : Type u),
      φsn.comp (algebraMap A ((⊤_ (SeminormalizationAlgebras A)).1 : Type u)) =
        (algebraMap A' ((⊤_ (SeminormalizationAlgebras A')).1 : Type u)).comp φ := sorry

end AlgebraicGeometry
