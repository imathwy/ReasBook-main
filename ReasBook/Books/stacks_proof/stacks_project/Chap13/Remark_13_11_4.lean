import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Localization
open ComplexShape HomotopyCategory
open CochainComplex

universe w v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Remark 13.11.4:
- primary domain: quasi-isomorphism localizations of cochain complexes and the computation of
  derived-category morphisms by K-injective targets;
- sampled owner declarations:
  `Localization.HasSmallLocalizedHom`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `Localization.hasSmallLocalizedHom_iff_target`,
  `DerivedCategory.quotientCompQhIso`;
- best owner abstraction:
  `source-facing`: smallness of morphism types in the localization at quasi-isomorphisms once the
    target admits a quasi-isomorphism to a K-injective complex;
  `core/canonical`: `HasSmallLocalizedHom` together with the canonical K-injective bijection
    `IsKInjective.Qh_map_bijective`;
  `bridge/view`: target transport along a quasi-isomorphism via
    `Localization.hasSmallLocalizedHom_iff_target`.
- primitive data: a source complex `K`, a target complex `L`, and a quasi-isomorphism from `L` to
  some K-injective replacement `I`;
- derived API: the smallness statement in the localization, obtained by transporting smallness of
  homotopy-category Hom-types through the canonical localization comparison maps.

The owner theorem here is therefore `HasSmallLocalizedHom`; the K-injective case is the core
computation statement, the explicit quasi-isomorphism-to-K-injective theorem is the primitive
bridge/view layer, and the source-facing remark is the existential corollary obtained from that
bridge.
-/

local notation "Qis" => HomologicalComplex.quasiIso 𝒜 (up ℤ)

-- Proof sketch: Lemma 13.31.2 identifies morphisms into a K-injective complex in the
-- quasi-isomorphism localization with morphisms in the homotopy category, and the latter form a
-- `w`-small type whenever the ambient category is `w`-locally small.
/-- A K-injective target computes morphisms in the quasi-isomorphism localization by morphisms in
the homotopy category, so the resulting localized Hom-type is small. -/
theorem hasSmallLocalizedHom_of_isKInjective
    [LocallySmall.{w} 𝒜] (K I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    HasSmallLocalizedHom.{w} Qis K I := by
  let Kq := quotient 𝒜 (up ℤ)
  rw [hasSmallLocalizedHom_iff Qis DerivedCategory.Q]
  have hKHom :
      Small.{w} ((Kq.obj K) ⟶ (Kq.obj I)) := by
    let _ : LocallySmall.{w} (CochainComplex 𝒜 ℤ) := by infer_instance
    exact small_of_surjective Kq.map_surjective
  have hQh :
      Small.{w}
        (DerivedCategory.Qh.obj (Kq.obj K) ⟶ DerivedCategory.Qh.obj (Kq.obj I)) :=
    (small_congr
      (Equiv.ofBijective DerivedCategory.Qh.map
        (IsKInjective.Qh_map_bijective (Kq.obj K) I))).1 hKHom
  exact (small_congr
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso 𝒜).app K)
      ((DerivedCategory.quotientCompQhIso 𝒜).app I))).2 hQh

-- Proof sketch: use the given quasi-isomorphism from `L` to a K-injective complex `I`, apply
-- `hasSmallLocalizedHom_of_isKInjective` to `I`, and transport smallness back along that
-- comparison quasi-isomorphism.
/-- If `L^•` admits a quasi-isomorphism to a K-injective complex `I^•`, then morphisms
`K^• ⟶ L^•` in the localization at quasi-isomorphisms form a small type. -/
theorem hasSmallLocalizedHom_of_quasiIso_to_isKInjective
    [LocallySmall.{w} 𝒜] (K : CochainComplex 𝒜 ℤ) {L I : CochainComplex 𝒜 ℤ}
    [I.IsKInjective] (f : L ⟶ I) (hf : QuasiIso f) :
    HasSmallLocalizedHom.{w} Qis K L := by
  exact (hasSmallLocalizedHom_iff_target Qis K f hf).2
    (hasSmallLocalizedHom_of_isKInjective K I)

-- Proof sketch: unpack the existential K-injective replacement and apply the explicit
-- quasi-isomorphism-to-K-injective bridge theorem above.
/-- Remark 13.11.4: if `L^•` is quasi-isomorphic to a K-injective complex, then morphisms
`K^• ⟶ L^•` in the localization at quasi-isomorphisms form a small type; equivalently,
`Hom_{D(\mathcal A)}(K^•, L^•)` is a set. -/
@[stacks 09PA]
theorem hasSmallLocalizedHom_of_hasKInjectiveReplacement
    [LocallySmall.{w} 𝒜] (K L : CochainComplex 𝒜 ℤ)
    (hL : ∃ (I : CochainComplex 𝒜 ℤ) (_ : I.IsKInjective) (f : L ⟶ I), QuasiIso f) :
    HasSmallLocalizedHom.{w} Qis K L := by
  obtain ⟨I, hI, f, hf⟩ := hL
  let _ : I.IsKInjective := hI
  exact hasSmallLocalizedHom_of_quasiIso_to_isKInjective K f hf

end
