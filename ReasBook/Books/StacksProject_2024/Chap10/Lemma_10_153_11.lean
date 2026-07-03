import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open IsLocalRing

section

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [HenselianLocalRing S] [Algebra.Etale R A]

/- Domain-style sampling:
- primary domain: henselian local rings, étale neighborhoods, and residue-field controlled lifts
  of points to henselian local targets;
- sampled owner declarations in the surrounding chapter/domain:
  `HenselianLocalRing`,
  `etale_retraction_unique_property`,
  `RingHom.IsFilteredColimitOfEtale`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- best owner abstraction:
  the core owner is the henselian étale-retraction criterion
  `etale_retraction_unique_property`, while the present file is `source-facing`, recording the
  textbook étale-algebra specialization before the later ind-étale generalization of
  Lemma `10.154.6`;
- primitive data vs. derived API:
  the primitive source-facing inputs are the étale `R`-algebra `A`, the chosen prime `q`, and the
  compatible residue-field map `τ`;
  the derived API is the unique `R`-algebra map `A → S` inducing that residue-field map.

Source/core/bridge triage:
- `source-facing`: the present étale lifting theorem;
- `core/canonical`: `HenselianLocalRing S` together with `etale_retraction_unique_property S`;
- `bridge/view`: the passage from the chosen prime and residue-field map on `A` to the unique
  `R`-algebra point of `A` valued in the henselian local ring `S`.
-/

-- Proof sketch: base change the étale `R`-algebra `A` along `R → S` to obtain the étale
-- `S`-algebra `A ⊗[R] S`. The prime `q` together with the chosen residue-field map `τ` determines
-- a prime of `A ⊗[R] S` over `maximalIdeal S` whose residue field is the same as that of `S`.
-- Apply the unique étale-neighborhood retraction characterization of henselian local rings from
-- Lemma `10.153.3` to get a unique `S`-algebra retraction `A ⊗[R] S → S`, then compose it with
-- the canonical map `A → A ⊗[R] S`.
/-- Lemma 10.153.11: let `R → S` be a ring map with `S` henselian local. If `R → A` is étale,
`q` is a prime of `A` whose contraction is the contraction of `maximalIdeal S`, and
`τ : κ(q) → S / maximalIdeal S` is compatible with the induced map from the common residue field
`κ(q ∩ R)`, then there exists a unique `R`-algebra map `f : A → S` whose inverse image of
`maximalIdeal S` is `q` and which induces `τ` on residue fields. -/
lemma existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := sorry

end
