import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_137_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Algebra.TensorProduct
open scoped TensorProduct

universe u v w uJ vJ

namespace Algebra

/- 
Domain-style sampling for Lemma 10.143.3:
- primary domain: étale `R`-algebras and their locality, base-change, filtered-colimit, and
  finite-product behavior in commutative algebra;
- sampled owner declarations:
  `Algebra.Etale`,
  `RingHom.Etale.ofLocalizationSpanTarget`,
  `Algebra.Etale.baseChange`,
  `Algebra.Etale.exists_subalgebra_fg`,
  `smooth_is_baseChange_of_stage_of_isColimit`;
- best owner abstraction: `Algebra.Etale` is the algebra-level owner, while
  `RingHom.Etale.ofLocalizationSpanTarget` is the canonical locality owner for target-local
  descent;
- primitive data: an `R`-algebra `S` together with the owner predicate `Etale R S`;
- derived API: locality on principal-open covers, étale loci, syntomicity, flatness, field
  criteria, filtered-colimit descent, localization descent, and finite-product criteria.

Source/core/bridge triage:
- `source-facing`: the textbook clauses (4) through (11), which are bridge statements about how
  étaleness behaves under standard constructions;
- `core/canonical`: `Algebra.Etale` / `RingHom.Etale`;
- `bridge/view`: algebra-level finite-cover formulations, `etaleLocus`, filtered-colimit descent,
  and the syntomic / flat / field criteria consequences.
-/

/- Lemma 10.143.3 (1): for any commutative ring `R` and any element `f : R`, the localization map
`R → R[1 / f]` is étale. This is exactly the canonical theorem
`Algebra.Etale.of_isLocalizationAway`. -/
recall Algebra.Etale.of_isLocalizationAway

/- Companion recall, clause (2): compositions of étale ring maps are étale. This is exactly the
canonical theorem `Algebra.Etale.comp`. -/
recall Algebra.Etale.comp

/- Companion recall, clause (3): base change preserves étale ring maps. This is exactly the
canonical tensor-product base-change instance `Algebra.Etale.baseChange`. -/
recall Algebra.Etale.baseChange

/- Clause (4): étaleness is local on the target for principal-open covers. This is exactly the
canonical owner-level locality theorem `RingHom.Etale.ofLocalizationSpanTarget`. -/
recall RingHom.Etale.ofLocalizationSpanTarget

section Locus

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [FinitePresentation R S] [Module.Flat R R']

-- Proof sketch: identify étaleness with smoothness plus vanishing of `Ω` and `H¹(L)`. Smooth loci
-- pull back correctly under flat base change by the smooth analogue, and flat base change detects
-- the vanishing of finitely presented modules by support-theoretic base-change on prime spectra.
-- Intersecting the two resulting pullback descriptions gives the claimed equality of étale loci.
/-- Clause (5): after a flat base change `R → R'`, the étale locus of `R' ⊗[R] S` is the inverse
image of the étale locus of `S`. -/
theorem etaleLocus_baseChange_of_flat :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹' etaleLocus R S =
      etaleLocus R' (R' ⊗[R] S) := sorry

end Locus

section Syntomic

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: an étale algebra is smooth, hence syntomic by the already established smooth case.
/-- Clause (6): an étale ring map is syntomic. -/
theorem etale_syntomic [Etale R S] :
    (algebraMap R S).Syntomic := by
  exact smooth_syntomic

-- Proof sketch: combine the previous clause with the flatness built into the definition of a
-- syntomic ring map, or equivalently use that étale implies smooth and smooth algebras are flat.
/-- Clause (6): an étale ring map is flat. -/
theorem etale_flat [Etale R S] : Module.Flat R S := by
  infer_instance

end Syntomic

section FieldCriterion

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] [EssFiniteType k S]

-- Proof sketch: over a field, the canonical finiteness input for the field criterion is
-- essential finite type. Then `Algebra.FormallyEtale.iff_formallyUnramified_of_field` identifies
-- formal étaleness with formal unramifiedness, and the latter is exactly the vanishing of
-- `Ω[S⁄k]`. To rebuild `Etale k S` from this owner-level criterion, use
-- `FormallyUnramified.finite_of_free` to get `Module.Finite k S`, hence `FiniteType k S`, and then
-- `FinitePresentation k S` because fields are noetherian.
/-- Clause (7): for an essentially finite type algebra over a field, étaleness is equivalent to
the vanishing of the module of Kähler differentials. -/
theorem etale_iff_subsingleton_kaehlerDifferential_of_field :
    Etale k S ↔ Subsingleton Ω[S⁄k] := by
  constructor
  · intro _; infer_instance
  · intro _
    letI : FormallyUnramified k S := ⟨inferInstance⟩
    letI : FormallyEtale k S :=
      FormallyEtale.iff_formallyUnramified_of_field.2 inferInstance
    letI : Module.Finite k S := FormallyUnramified.finite_of_free k S
    exact ⟨inferInstance, FinitePresentation.of_finiteType.mp inferInstance⟩

end FieldCriterion

/- Companion recall, clause (8): every étale algebra descends to an étale model over a finitely
generated `ℤ`-subalgebra of the base. This is exactly
`Algebra.Etale.exists_subalgebra_fg`. -/
recall Algebra.Etale.exists_subalgebra_fg

section FilteredColimit

variable {J : Type vJ} [Category.{uJ} J] [IsFiltered J]

-- Proof sketch: apply the finite-type `ℤ`-model from clause (8) to the étale algebra over the
-- colimit ring. Because the descended algebra is finitely presented over a finitely generated
-- subalgebra of the colimit, Lemma `10.127.3` factors the structure map through some stage. Base
-- changing that stagewise étale model back to the colimit recovers the original algebra.
/-- Clause (9): an étale algebra over a filtered colimit of rings is obtained by base change from
an étale algebra over some stage of the diagram. -/
theorem etale_is_baseChange_of_stage_of_isColimit
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c)
    (B : Type w) [CommRing B] [Algebra c.pt B] [Etale c.pt B] :
    ∃ (j : J) (B_j : Type w) (_ : CommRing B_j) (_ : Algebra (F.obj j) B_j),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Etale (F.obj j) B_j ∧ Nonempty (B ≃ₐ[c.pt] c.pt ⊗[F.obj j] B_j) := sorry

end FilteredColimit

section LocalizationDescent

variable {A : Type u} [CommRing A]

-- Proof sketch: write the localization `Aₛ` as a filtered colimit of principal localizations of
-- `A`. Clause (9) descends the étale `Aₛ`-algebra to one of those principal stages, clause (1)
-- makes that stage étale over `A`, and clause (2) composes the two étale maps. The descended
-- algebra then base changes back to the original one over `Aₛ`.
/-- Clause (10): an étale algebra over a localization of `A` descends to an étale algebra over
`A`; in canonical tensor-product form, the localized algebra is obtained from the descended one by
base change along `A → Aₛ`. -/
theorem exists_etale_model_over_base_of_localization
    (M : Submonoid A) {Aₛ : Type v} [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization M Aₛ]
    (B' : Type w) [CommRing B'] [Algebra Aₛ B'] [Etale Aₛ B'] :
    ∃ (B : Type w) (_ : CommRing B) (_ : Algebra A B) (_ : Etale A B),
      Nonempty (B' ≃ₐ[Aₛ] Aₛ ⊗[A] B) := sorry

end LocalizationDescent

section Products

variable {R : Type u} {S' : Type v} {S'' : Type w}
variable [CommRing R] [CommRing S'] [CommRing S''] [Algebra R S'] [Algebra R S'']

-- Proof sketch: for the forward implication, restrict an étale structure on `S' × S''` to each
-- factor via the projection idempotents; formal étaleness splits by `Algebra.FormallyEtale.pi_iff`
-- and finite presentation descends to each factor. Conversely, if both factors are étale, then
-- their product is formally étale by the finite-product criterion and finitely presented by the
-- corresponding finite-presentation product statement.
/-- Clause (11): a binary product of `R`-algebras is étale over `R` if and only if each factor is
étale over `R`. -/
theorem etale_prod_iff :
    Etale R (S' × S'') ↔ Etale R S' ∧ Etale R S'' := sorry

end Products

end Algebra
