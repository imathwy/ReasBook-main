import Mathlib
import Mathlib.RingTheory.Etale.Field
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_143_1 (from Chap10) -/
universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.143.1 (1): the textbook notion that `R → S` is étale is the canonical typeclass
`Algebra.Etale R S`, i.e. finite presentation together with vanishing of `Ω[S⁄R]` and
`H1Cotangent R S`. -/
recall Algebra.Etale

/- Definition 10.143.1 (2): the textbook notion that `R → S` is étale at the prime `q` is the
canonical local notion `Algebra.IsEtaleAt R q.asIdeal`. -/
recall Algebra.IsEtaleAt

-- Proof sketch: if `S_q` is formally étale over `R`, apply
-- `Algebra.exists_etale_of_isEtaleAt` to obtain an element `g ∉ q` with `S_g` étale. Conversely,
-- if such a `g` exists, then the basic open `D(g)` lies in the étale locus by
-- `Algebra.basicOpen_subset_etaleLocus_iff_etale`, and since `q ∈ D(g)` this implies
-- `Algebra.IsEtaleAt R q.asIdeal`.
/-- Local étaleness at a prime is equivalent to the existence of an étale basic-open neighborhood
of that prime. -/
theorem isEtaleAt_iff_exists_etale_away [FinitePresentation R S] (q : PrimeSpectrum S) :
    IsEtaleAt R q.asIdeal ↔ ∃ g : S, g ∉ q.asIdeal ∧ Etale R (Localization.Away g) := by
  constructor
  · intro hq
    letI : IsEtaleAt R q.asIdeal := hq
    exact exists_etale_of_isEtaleAt q.asIdeal
  · rintro ⟨g, hg, hEtale⟩
    rw [← mem_etaleLocus_iff]
    have hsubset : ↑(PrimeSpectrum.basicOpen g) ⊆ etaleLocus R S :=
      basicOpen_subset_etaleLocus_iff_etale.2 hEtale
    exact hsubset <| (PrimeSpectrum.mem_basicOpen g q).2 hg

end Algebra

/-! ### Lemma_10_143_2 (from Chap10) -/
universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-
Domain-style sampling for Lemma 10.143.2:
- primary domain: commutative-algebraic smoothness and étaleness for `R`-algebras;
- sampled owner declarations:
  `Algebra.Etale`,
  `Algebra.IsStandardSmoothOfRelativeDimension`,
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`,
  `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero`;
- best owner abstraction: the algebra-level equivalence
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`;
- primitive data: the owner predicates `Etale R S` and `IsStandardSmoothOfRelativeDimension 0 R S`;
- derived API: the forward and backward implications, plus the ring-hom bridge theorem.

Layer triage:
- `source-facing`: the Stacks lemma asserting that étale implies standard smooth of relative
  dimension `0`;
- `core/canonical`: the upstream equivalence
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`;
- `bridge/view`: the ring-hom reformulation
  `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero`.

This item adds no new mathematical content beyond the existing owner equivalence, and nothing
downstream depends on a local theorem name, so the canonical refinement is a direct recall rather
than a parallel wrapper for one implication.
-/

/- Lemma 10.143.2: an `R`-algebra is étale if and only if it is standard smooth of relative
dimension `0`; the stated implication is the forward direction of this canonical owner theorem. -/
recall Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

end Algebra

/-! ### Lemma_10_143_3 (from Chap10) -/
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

/-! ### Lemma_10_143_4 (from Chap10) -/
/- Lemma 10.143.4: for a field `k`, a `k`-algebra `S` is étale over `k` if and only if `S` is
isomorphic as a `k`-algebra to a finite product of finite separable field extensions of `k`. This
is exactly the canonical theorem `Algebra.Etale.iff_exists_algEquiv_prod`. -/
recall Algebra.Etale.iff_exists_algEquiv_prod

/-! ### Lemma_10_143_5 (from Chap10) -/
universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: local étale / unramified behavior of prime ideals and residue fields in
  commutative algebra;
- sampled owner declarations:
  `Algebra.IsEtaleAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `Algebra.FormallyUnramified.map_maximalIdeal`,
  `Localization.AtPrime.map_eq_maximalIdeal`;
- best owner abstraction: the core owner is local formal étaleness
  `Algebra.IsEtaleAt R q`, but the source-facing notion used in these two consequences is the
  existence of an étale basic-open neighborhood of `q`;
- source/core/bridge triage:
  - `source-facing`: an explicit witness `g ∉ q` with `R → S_g` étale;
  - `core/canonical`: `Algebra.IsEtaleAt`, `Algebra.IsUnramifiedAt`, and the local-ring owner
    API for maximal ideals and residue fields;
  - `bridge/view`: transporting the global étale neighborhood to the local ring `S_q`.
- primitive vs. derived:
  - primitive data: the prime `q` and an étale neighborhood `S_g` of `q`;
  - derived API: the equality `(q ∩ R) S_q = 𝔪_{S_q}` and finiteness/separability of
    `κ(q) / κ(q ∩ R)`.

The raw owner `Algebra.IsEtaleAt R q` is too weak by itself for the residue-field finiteness
conclusion, so this file should keep the source-facing neighborhood hypothesis rather than expose a
stronger conclusion from a weaker owner.
-/

-- Proof sketch: choose an étale basic-open neighborhood `S_g` of `q`. Étale implies unramified
-- on that neighborhood, so after localizing further at the prime over `q` the local criterion
-- `Algebra.isUnramifiedAt_iff_map_eq` gives `(q ∩ R) S_q = 𝔪_{S_q}`.
/-- Lemma 10.143.5 (1): if some neighborhood `R → S_g` with `g ∉ q` is étale, then the extended
ideal `(q ∩ R) S_q` is the maximal ideal of the local ring `S_q`. Equivalently,
`(q ∩ R) S_q = q S_q`. -/
theorem map_eq_maximalIdeal_of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (hEt : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) := sorry

-- Proof sketch: choose an étale neighborhood `S_g` of `q`, localize it at the prime over `q`,
-- and apply the local unramified field criterion there. The residue-field extension is unchanged
-- by inverting `g ∉ q`, so `κ(q) / κ(q ∩ R)` is finite and separable.
/-- Lemma 10.143.5 (2): if some neighborhood `R → S_g` with `g ∉ q` is étale, then the
residue-field extension `κ(q) / κ(q ∩ R)` is finite and separable. -/
theorem residueField_finite_and_separable_of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (hEt : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    Module.Finite (q.under R).ResidueField q.ResidueField ∧
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := sorry

end

/-! ### Lemma_10_143_6 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Etale R S]

-- Proof sketch: the owner abstraction for the conclusion is `Algebra.QuasiFinite R S`. Mathlib
-- already provides the canonical instance
-- `[Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] : Algebra.QuasiFinite R S`, and
-- an étale algebra supplies these hypotheses automatically.
/-- Lemma 10.143.6: an étale ring map `R → S` is quasi-finite. -/
theorem etale_ringHom_quasiFinite : (algebraMap R S).QuasiFinite := by
  rw [RingHom.quasiFinite_algebraMap]
  infer_instance

end

/-! ### Lemma_10_143_7 (from Chap10) -/
universe u v

open IsLocalRing

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [FinitePresentation R S]

/- Domain-style sampling:
- primary domain: local étaleness criteria for finitely presented ring maps;
- sampled owner declarations:
  `Algebra.IsEtaleAt`,
  `Algebra.IsUnramifiedAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `[Algebra.IsUnramifiedAt R q] → Module.Finite p.ResidueField q.ResidueField`,
  `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`,
  `Algebra.IsSmoothAt.of_formallySmooth_fiber`;
- best owner abstraction: `Algebra.IsEtaleAt R q` is the canonical local owner.

Source/core/bridge triage:
- `source-facing`: the Stacks local criterion for étaleness at `q`;
- `core/canonical`: the owner predicates `IsEtaleAt`, `IsUnramifiedAt`, and `IsSmoothAt`;
- `bridge/view`: the local flatness hypothesis together with the maximal-ideal equality and the
  separable residue-field extension.

Primitive data vs. derived API:
- primitive data: local flatness of `R_p → S_q`, the equality `pS_q = 𝔪_{S_q}`, and separability
  of `κ(q) / κ(p)`;
- derived API: local unramifiedness, finiteness of `κ(q) / κ(p)`, local smoothness, and hence
  local étaleness.

This file should keep the bridge theorem rather than collapse to the sampled owner theorem
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`, because that owner theorem assumes global
flatness `Module.Flat R S`, while the source statement only assumes flatness of the localized map
`R_p → S_q`.
-/
-- Proof sketch: use `Algebra.isUnramifiedAt_iff_map_eq` to deduce that `R → S` is unramified at
-- `q` from the equality `pS_q = 𝔪_{S_q}` and the separability of `κ(q) / κ(p)`. The flat-local
-- and finite-presentation hypotheses then give smoothness at `q` by the smooth-fiber criterion;
-- once unramifiedness is known, mathlib's local unramified API supplies the finiteness of
-- `κ(q) / κ(p)`, so the fiber identifies with a finite separable field extension. Combine
-- smoothness and unramifiedness to conclude étaleness at `q`.
/-- Lemma 10.143.7: let `q` be a prime of `S` lying over a prime `p` of `R`. If `R → S` is of
finite presentation, the localized map `R_p → S_q` is flat, `p S_q` is the maximal ideal of the
local ring `S_q`, and the residue field extension `κ(q) / κ(p)` is separable, then `R → S` is
étale at `q`; the finiteness of `κ(q) / κ(p)` is automatic from these hypotheses. -/
theorem isEtaleAt_of_flat_localRingHom_of_map_eq_maximalIdeal_of_separableResidueField
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hflat : (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).Flat)
    (hmax : p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q))
    [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    IsEtaleAt R q := sorry

end

end Algebra

/-! ### Lemma_10_143_8 (from Chap10) -/
universe u v w

namespace Algebra

section

variable {R : Type u} {S' : Type v} {S : Type w}
variable [CommRing R] [CommRing S'] [CommRing S]
variable [Algebra R S'] [Algebra R S] [Algebra S' S] [IsScalarTower R S' S]
variable [Etale R S'] [Etale R S]

/- Domain-style sampling:
- primary domain: étale morphisms of commutative rings, especially target-local descent from the
  owner predicates `Etale` and `IsEtaleAt`;
- sampled owner declarations:
  `Algebra.Etale`,
  `RingHom.Etale.ofLocalizationSpanTarget`,
  `map_eq_maximalIdeal_of_exists_etale_away`,
  `isEtaleAt_of_flat_localRingHom_of_map_eq_maximalIdeal_of_separableResidueField`;
- best owner abstraction: the global owner remains `Etale S' S`, while the local bridge owner is
  `IsEtaleAt S' q` at each prime `q : Ideal S`;
- primitive data: the two étale structures over the common base `R` and the compatible
  `S'`-algebra structure on `S`;
- derived API: residue-field separability, local maximal-ideal identification, local flatness of
  `S'_q' → S_q`, and the final target-local reconstruction of `Etale S' S`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that two étale algebras over a common base induce an
  étale map between them;
- `core/canonical`: `Algebra.Etale`, `Algebra.IsEtaleAt`, and `RingHom.Etale`;
- `bridge/view`: the local primewise flatness and residue-field criteria supplied by
  `10.143.5`, `10.143.7`, and `10.128.9`.
-/

-- Proof sketch: étaleness is local on the target, so it suffices to prove `S' → S` is étale at
-- every prime of `S`. For a prime `q ⊂ S` lying over `q' ⊂ S'` and `p ⊂ R`, the chapter-local
-- owners from Lemmas `10.143.5` and `10.143.7` provide the needed maximal-ideal and
-- residue-field criteria, while the global owner remains `Algebra.Etale S' S` rather than a new
-- wrapper around local data.
/-- Lemma 10.143.8: if `R → S` and `R → S'` are étale and `S` is equipped with a compatible
`S'`-algebra structure over `R`, then the induced map `S' → S` is étale. -/
theorem etale_of_etale_over_common_base :
    Etale S' S := by
  sorry

end

end Algebra

/-! ### Lemma_10_143_9 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.Flat R S] [Algebra.FinitePresentation R S]

/-
Domain triage:
- primary domain: surjective flat finitely presented algebra maps and their canonical presentation
  as localizations away from an idempotent;
- sampled owner declarations:
  `Ideal.Pure`,
  `Ideal.isIdempotentElem_of_pure`,
  `Ideal.isIdempotentElem_iff_of_fg`,
  `IsLocalization.away_of_isIdempotentElem`,
  `Ideal.quotientKerAlgEquivOfSurjective`;
- best owner abstraction: the kernel ideal of `algebraMap R S`, viewed through the canonical owner
  pipeline "flat quotient => pure ideal => finitely generated idempotent ideal => away
  localization";
- primitive data: the `R`-algebra `S`, the flatness and finite-presentation owner instances, and
  the surjectivity of `algebraMap R S`;
- derived API: the idempotent element cutting out the kernel and the resulting
  `IsLocalization.Away e S`.

This lemma is `source-facing`: it keeps the textbook existence statement, but the proof should
reuse the canonical owner declarations directly rather than introducing any local kernel/idempotent
wrapper.
-/
-- Proof sketch: let `I = RingHom.ker (algebraMap R S)`. Surjectivity identifies `S` with the
-- quotient `R ⧸ I`, so flatness makes `I` a pure ideal. Hence `I` is idempotent, and finite
-- presentation makes it finitely generated. Apply the canonical finitely-generated idempotent-ideal
-- criterion to write `I = (1 - e)` for an idempotent `1 - e`, then use
-- `IsLocalization.away_of_isIdempotentElem` to identify `S` with the localization of `R` away from
-- `e`.
/-- Lemma 10.143.9: if `S` is a surjective, flat, finitely presented `R`-algebra, then there
exists an idempotent `e ∈ R` such that `S` is the localization of `R` away from `e`. -/
theorem exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation
    (hsurj : Function.Surjective (algebraMap R S)) :
    ∃ e : R, IsIdempotentElem e ∧ IsLocalization.Away e S := by
  let I : Ideal R := RingHom.ker (algebraMap R S)
  have hfg : I.FG := by
    simpa [I] using
      Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId R S) hsurj
  have hI : IsIdempotentElem I := by
    let f : R →ₐ[R] S := Algebra.ofId R S
    have hf : Function.Surjective f := by
      simpa [f] using hsurj
    let e : (R ⧸ I) ≃ₐ[R] S := by
      simpa [I, f] using (Ideal.quotientKerAlgEquivOfSurjective hf :
        (R ⧸ RingHom.ker f) ≃ₐ[R] S)
    letI : I.Pure := by
      change Module.Flat R (R ⧸ I)
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    exact Ideal.isIdempotentElem_of_pure I
  obtain ⟨e, he, hker⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hI
  refine ⟨1 - e, he.one_sub, ?_⟩
  exact IsLocalization.away_of_isIdempotentElem he.one_sub (hker.trans (by simp)) hsurj

end

/-! ### Lemma_10_143_10 (from Chap10) -/
universe u v

namespace Algebra

section

variable {R : Type u} {Sbar : Type v} [CommRing R] (I : Ideal R)
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar] [Etale (R ⧸ I) Sbar]

/- Domain-style sampling:
* primary domain: étale commutative algebras over quotient rings and their lifting to the base
  ring;
* sampled declarations:
  `Algebra.Etale`,
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`,
  `exists_standardSmooth_lift_cover_of_quotient_smooth`,
  `exists_etale_lift_to_quotient_of_smooth`;
* best owner abstraction: the primitive owner data are the ambient étale structures on the
  quotient algebra `Sbar` and on the lifted algebra `S`; the reduction isomorphism is derived
  comparison data and should be exposed on the canonical quotient-identification surface
  `Nonempty ((S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I] Sbar)`.

Source/core/bridge triage:
* `source-facing`: the existence of an étale `R`-algebra lifting the given étale
  `(R ⧸ I)`-algebra;
* `core/canonical`: the owner predicate `Algebra.Etale` together with the quotient algebra
  `S ⧸ Ideal.map (algebraMap R S) I`;
* `bridge/view`: the quotient comparison equivalence identifying that reduction with `Sbar`.

Primitive-vs-derived split:
* primitive data: only the lifted algebra `S` with its `R`-algebra and étale structures;
* derived API: the comparison equivalence between its reduction modulo `I` and `Sbar`.

This item is not a pure recall: it adds genuine source-facing existence content. The refinement is
therefore to keep the theorem and remove only the non-canonical `AlgHom`-plus-bijectivity
packaging of the comparison isomorphism.
-/

-- Proof sketch: by Lemma 10.143.2, present the étale `(R ⧸ I)`-algebra `Sbar` as standard smooth
-- of relative dimension `0`, with as many generators as relations and invertible Jacobian
-- determinant. Lift the defining polynomials to `R`, adjoin an inverse to the lifted determinant,
-- and use the standard étale criterion to obtain an étale `R`-algebra `S`. Reducing modulo `I`
-- recovers the original presentation, giving the required quotient algebra equivalence.
/-- Lemma 10.143.10: every étale algebra over the quotient ring `R ⧸ I` lifts to an étale
`R`-algebra whose reduction modulo `I` is isomorphic to the given quotient algebra. -/
theorem exists_etale_lift_of_quotient :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : Etale R S),
      Nonempty ((S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I] Sbar) := sorry

end

end Algebra

/-! ### Lemma_10_143_11 (from Chap10) -/
universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-
Domain-style sampling:
- primary domain: infinitesimal lifting of étale ring maps across square-zero extension squares;
- sampled owner API:
  `RingHom.Etale`,
  `RingHom.etale_iff_formallyUnramified_and_smooth`,
  `RingHom.FormallyUnramified.of_comp`,
  `RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero`;
- best owner abstraction: this is a source-facing lifting theorem, but its canonical owner
  predicate is `RingHom.Etale`;
- source-facing: the square-zero lifting criterion for étaleness in a commutative square of
  surjective ring maps;
- core/canonical: `RingHom.Etale`, together with its derived owner consequences
  `FormallyUnramified`, `Smooth`, `Flat`, and `FinitePresentation`;
- bridge/view: the commutative square `qB.comp g = f.comp qA` and the kernel comparison
  `ker qB = (ker qA).map g`.

Primitive-vs-derived split:
- primitive data: the four ring maps, the commutative square, surjectivity, and the square-zero
  / kernel-identification hypotheses;
- derived API: the formal unramifiedness / smoothness / flatness consequences extracted from the
  owner predicate `Etale`.

This item adds genuine source-facing content, so the public theorem should stay a theorem about
`g.Etale`; the refinement is to keep the owner predicate explicit and avoid parallel local wrappers
around its derived formal properties.
-/

-- Proof sketch: keep `RingHom.Etale` as the owner abstraction. The quotient map `f` contributes
-- the derived formally unramified, smooth, flat, and finite-presentation data. The formal
-- unramified part ascends through the commutative square via composition with the surjective map
-- `qB`, while the smooth part is obtained by lifting the quotient étale algebra across the
-- square-zero extension and identifying the lift with `Bprime` using
-- `ker qB = (ker qA).map g`. This recovers `g.Etale`.
/-- Lemma 10.143.11: in a commutative square of surjective ring maps
`Aprime ⟶ Bprime` over `A ⟶ B`, if `A → B` is étale, the kernel of `Aprime → A` is square-zero,
and the kernel of `Bprime → B` is the image ideal `(ker qA).map g`, then
`Aprime → Bprime` is étale. -/
theorem etale_of_surjective_of_ker_eq_map_of_square_zero
    (hcomm : qB.comp g = f.comp qA)
    (hEtale : f.Etale)
    (hSurjA : Function.Surjective qA)
    (hSurjB : Function.Surjective qB)
    (hSq : (ker qA) ^ 2 = ⊥)
    (hker : ker qB = (ker qA).map g) :
    g.Etale := sorry

end

end RingHom

/-! ### Example_10_143_12 (from Chap10) -/
section

open Polynomial

variable (n m : ℕ)

/- Example 10.143.12: the textbook generic factorization map
`ℤ[a₁, …, a_{n+m}] → ℤ[b₁, …, bₙ, c₁, …, cₘ]`, localized away from the Sylvester determinant
or equivalently the resultant of the two generic monic factors, is exactly the canonical owner
`Polynomial.UniversalCoprimeFactorizationRing`. Its étaleness is the upstream instance below. The
source positivity hypotheses `n, m ≥ 1` are redundant for this canonical statement and are
therefore omitted from the public surface. -/
#check (inferInstance :
  Algebra.Etale (MvPolynomial (Fin (n + m)) ℤ)
    (UniversalCoprimeFactorizationRing n m rfl (MonicDegreeEq.freeMonic ℤ (n + m))))

end

/-! ### Lemma_10_143_13 (from Chap10) -/
/- Lemma 10.143.13: if a monic polynomial `f ∈ R[X]` has a factorization
`f mod 𝔭 = ḡ * h̄` in the residue field `κ(𝔭)[X]` with `ḡ` and `h̄` coprime, then after passing
to an étale `R`-algebra there is a prime lying over `𝔭` with the same residue field and a lift of
this factorization to coprime factors upstairs. This is exactly the canonical theorem
`Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`, where
`Function.Bijective` on the residue-field map encodes `κ(𝔭) = κ(𝔭')` and `IsCoprime` encodes that
the lifted factors generate the unit ideal. -/
recall Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime
