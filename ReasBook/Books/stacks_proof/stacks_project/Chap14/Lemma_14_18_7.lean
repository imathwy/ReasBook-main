import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite AlgebraicTopology
open Abelian.DoldKan
open scoped Simplicial

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} (f : U ⟶ V)

/- Domain-style sampling for Lemma 14.18.7:
- primary domain: simplicial objects in an abelian category and the Dold-Kan normalized Moore
  complex functor
- sampled owner API:
  `N`,
  `equivalence`,
  `HomologicalComplex.mono_of_mono_f`,
  `HomologicalComplex.epi_of_epi_f`,
  `HomologicalComplex.Hom.isIso_of_components`
- best owner abstraction: the canonical functor `N : SimplicialObject A ⥤
  ChainComplex A ℕ`
- primitive data: the simplicial morphism `f` and the degree maps of `(N.map f)`
- derived API: global mono/epi/isIso detection for chain maps and objectwise detection for
  simplicial morphisms
- source/core/bridge triage: these lemmas are `source-facing` transfer statements; the owner
  `Abelian.DoldKan.N` is `core/canonical`; the Dold-Kan equivalence and the componentwise
  detection lemmas in `ChainComplex` and functor categories form the `bridge/view` layer used in
  the proofs.
-/

-- Proof sketch: componentwise monomorphisms make `N.map f` a monomorphism of chain complexes via
-- `HomologicalComplex.mono_of_mono_f`. The faithful Dold-Kan functor `N` reflects monos, so `f`
-- is mono; evaluate objectwise in the simplicial functor category.
/-- If the degree maps of the normalized Moore complex morphism `N(f)` are monomorphisms, then the
underlying simplicial morphism `f` is a monomorphism. -/
theorem mono_of_normalizedMooreComplex_degreewise_mono
    (h :
      ∀ i : ℕ, Mono ((N.map f).f i)) :
    Mono f := by
  let F : SimplicialObject A ⥤ ChainComplex A ℕ := N
  haveI : Functor.Faithful F := by
    simpa [F, equivalence_functor] using
      (inferInstance : Functor.Faithful ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor))
  exact F.mono_of_mono_map <| by
    simpa [F] using (HomologicalComplex.mono_of_mono_f (N.map f) h)

/-- Lemma 14.18.7 (1): if the degree maps of the normalized Moore complex morphism `N(f)` are
monomorphisms, then every simplicial degree map `f_i` is a monomorphism. -/
@[stacks 017W]
theorem degreewise_mono_of_normalizedMooreComplex_degreewise_mono
    (h :
      ∀ i : ℕ, Mono ((N.map f).f i)) :
    ∀ i : ℕ, Mono (f.app (op ⦋i⦌)) := by
  let _ : Mono f := mono_of_normalizedMooreComplex_degreewise_mono f h
  exact fun _ ↦ inferInstance

-- Proof sketch: componentwise epimorphisms make `N.map f` an epimorphism of chain complexes via
-- `HomologicalComplex.epi_of_epi_f`. The faithful Dold-Kan functor `N` reflects epis, so `f` is
-- epi; evaluate objectwise in the simplicial functor category.
/-- If the degree maps of the normalized Moore complex morphism `N(f)` are epimorphisms, then the
underlying simplicial morphism `f` is an epimorphism. -/
theorem epi_of_normalizedMooreComplex_degreewise_epi
    (h :
      ∀ i : ℕ, Epi ((N.map f).f i)) :
    Epi f := by
  let F : SimplicialObject A ⥤ ChainComplex A ℕ := N
  haveI : Functor.Faithful F := by
    simpa [F, equivalence_functor] using
      (inferInstance : Functor.Faithful ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor))
  exact F.epi_of_epi_map <| by
    simpa [F] using (HomologicalComplex.epi_of_epi_f (N.map f) h)

/-- If the degree maps of the normalized Moore complex morphism `N(f)` are epimorphisms, then
every simplicial degree map `f_i` is an epimorphism. -/
theorem degreewise_epi_of_normalizedMooreComplex_degreewise_epi
    (h :
      ∀ i : ℕ, Epi ((N.map f).f i)) :
    ∀ i : ℕ, Epi (f.app (op ⦋i⦌)) := by
  let _ : Epi f := epi_of_normalizedMooreComplex_degreewise_epi f h
  exact fun _ ↦ inferInstance

-- Proof sketch: componentwise isomorphisms make `N.map f` an isomorphism of chain complexes via
-- `HomologicalComplex.Hom.isIso_of_components`. The Dold-Kan functor `N` reflects isomorphisms,
-- so `f` is an isomorphism; evaluate objectwise in the simplicial functor category.
/-- If the degree maps of the normalized Moore complex morphism `N(f)` are isomorphisms, then the
underlying simplicial morphism `f` is an isomorphism. -/
theorem isIso_of_normalizedMooreComplex_degreewise_isIso
    (h :
      ∀ i : ℕ, IsIso ((N.map f).f i)) :
    IsIso f := by
  let F : SimplicialObject A ⥤ ChainComplex A ℕ := N
  haveI : F.ReflectsIsomorphisms := by
    simpa [F, equivalence_functor] using
      (inferInstance :
        ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).ReflectsIsomorphisms)
  let _ : ∀ i : ℕ, IsIso ((N.map f).f i) := h
  have hF : IsIso (F.map f) := by
    simpa [F] using (HomologicalComplex.Hom.isIso_of_components (N.map f))
  exact isIso_of_reflects_iso f F

/-- If the degree maps of the normalized Moore complex morphism `N(f)` are isomorphisms, then
every simplicial degree map `f_i` is an isomorphism. -/
theorem degreewise_isIso_of_normalizedMooreComplex_degreewise_isIso
    (h :
      ∀ i : ℕ, IsIso ((N.map f).f i)) :
    ∀ i : ℕ, IsIso (f.app (op ⦋i⦌)) := by
  let _ : IsIso f := isIso_of_normalizedMooreComplex_degreewise_isIso f h
  exact fun _ ↦ inferInstance

end CategoryTheory
