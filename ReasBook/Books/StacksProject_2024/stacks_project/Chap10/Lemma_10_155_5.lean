import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open IsLocalRing

section

variable {R : Type u} (S : Type v) {Sh : Type v} {A : Type w}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [CommRing Sh] [Algebra S Sh] [Algebra R Sh] [IsScalarTower R S Sh]
variable [IsHenselizationOf S Sh]
variable [CommRing A] [Algebra R A] [Algebra.Etale R A]

/- Domain-style sampling:
- primary domain: henselian local targets, henselization owners, and étale lifting of local
  points controlled by residue fields;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `Ideal.ResidueField.map`,
  `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  `IsHenselizationOf.residueFieldEquiv`;
- best owner abstraction: `Lemma_10_153_11` is the core lifting owner, while the present lemma is
  a `source-facing` specialization in which the target henselian local ring is a henselization of
  `S`, and the source-side residue-field input should be the primitive canonical map
  `κ(maximalIdeal R) → κ(q)` together with its bijectivity, not a separately chosen ring
  equivalence;
- primitive data: the étale `R`-algebra `A`, the prime `q`, the contraction condition
  `q.under R = maximalIdeal R`, and bijectivity of the canonical residue-field map
  `κ(maximalIdeal R) → κ(q)`;
- derived API: the unique `R`-algebra map `A → Sh`, with the inverse-image condition on
  `maximalIdeal Sh`, and the companion `κ`-based reformulation obtained by upgrading the bijective
  canonical map to a ring equivalence.

Source/core/bridge triage:
- `source-facing`: the present source-specialized henselization lifting statement;
- `core/canonical`: `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`;
- `bridge/view`: the chosen ring equivalence version of the residue-field hypothesis, which is
  derived from bijectivity of the canonical map and retained only as a thin companion surface.
-/
-- Proof sketch: apply `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap` with
-- target `Sh`. Since `Sh` is henselian local, it suffices to supply the residue-field map
-- required by Lemma `10.153.11`. The source hypothesis gives that the canonical map
-- `κ(maximalIdeal R) → κ(q)` is bijective, so it can be inverted to identify `κ(q)` with the
-- common source residue field and compared with the canonical residue-field map into `Sh`.
/-- Lemma 10.155.5: if `R → S` is a local map of local rings, `Sh` is a henselization of `S`,
`R → A` is étale, and `q` is a prime of `A` over `maximalIdeal R` such that the canonical map
`κ(maximalIdeal R) → κ(q)` is bijective, then there is a unique `R`-algebra map `A → Sh` whose
inverse image of `maximalIdeal Sh` is `q`. -/
lemma existsUnique_algHom_to_henselization_of_etale_of_residueFieldMap_bijective
    (q : Ideal A) [q.IsPrime] (hq : q.under R = maximalIdeal R)
    (hκ : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm)) :
    ∃! f : A →ₐ[R] Sh,
      q = Ideal.comap (f : A →+* Sh) (maximalIdeal Sh) := by
  sorry

/-- Thin bridge/view companion: a chosen ring equivalence identifying `κ(maximalIdeal R)` with
`κ(q)` through the canonical map also suffices. -/
lemma existsUnique_algHom_to_henselization_of_etale_of_residueFieldEquiv
    (q : Ideal A) [q.IsPrime] (hq : q.under R = maximalIdeal R)
    (κ : (maximalIdeal R).ResidueField ≃+* q.ResidueField)
    (hκ : κ.toRingHom = Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm) :
    ∃! f : A →ₐ[R] Sh,
      q = Ideal.comap (f : A →+* Sh) (maximalIdeal Sh) := by
  let hbij :
      Function.Bijective (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm) := by
    rw [← hκ]
    exact κ.bijective
  simpa using
    existsUnique_algHom_to_henselization_of_etale_of_residueFieldMap_bijective S q hq hbij

end
