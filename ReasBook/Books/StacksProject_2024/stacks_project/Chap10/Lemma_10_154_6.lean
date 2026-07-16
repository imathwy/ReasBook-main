import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open RingHom

section

variable {R : Type u} {A : Type u} {S : Type u}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [HenselianLocalRing S]

/-
Domain-style sampling:
- primary domain: henselian local rings, residue-field maps at primes, and ind-étale
  `R`-algebras;
- sampled owner declarations in the local chapter/domain:
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`,
  `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  `HenselianLocalRing`;
- best owner abstraction: the ind-étale presentation should use the chapter owner
  `RingHom.IsFilteredColimitOfEtale`, while the present theorem remains the source-facing
  henselian lifting statement built on top of that owner and the residue-field API;
- primitive data vs. derived API:
  the primitive inputs are the `R`-algebra map `R → A`, its ind-étale presentation, the prime
  `q`, and the compatible residue-field map `τ`;
  the derived API is the unique `R`-algebra map `A → S` with prescribed maximal-ideal fiber and
  residue-field action.

Source/core/bridge triage:
- `source-facing`: the present ind-étale lifting theorem;
- `core/canonical`: `HenselianLocalRing S`, `RingHom.IsFilteredColimitOfEtale`, and
  `Ideal.ResidueField.map`;
- `bridge/view`: the compatibility condition on `τ` and the resulting unique `R`-algebra point
  of `A` valued in `S`.
-/

-- Proof sketch: write `A` as a filtered colimit of étale `R`-algebras using `hA`. For each étale
-- stage, restrict `q` and `τ`, then apply Lemma `10.153.11` to obtain a unique compatible map from
-- that stage to `S`. The uniqueness clause makes these stage maps compatible, so they glue along
-- the colimit to a unique `R`-algebra map `A → S` with the prescribed inverse image of
-- `maximalIdeal S` and induced residue-field map.
/-- Lemma 10.154.6: let `R → S` be a ring map with `S` henselian local. If `A` is a filtered
colimit of étale `R`-algebras, `q` is a prime of `A` whose contraction is the contraction of
`maximalIdeal S`, and `τ : κ(q) → S / maximalIdeal S` is compatible with the induced map from the
common residue field `κ(q ∩ R)`, then there exists a unique `R`-algebra map `f : A → S` whose
inverse image of `maximalIdeal S` is `q` and which induces `τ` on residue fields. -/
lemma existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap
    (hA : (algebraMap R A).IsFilteredColimitOfEtale) (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := sorry

end
