import Mathlib
import stacks_project.Chap10.Lemma_10_150_4
import stacks_project.Chap10.Lemma_10_150_6
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap10.Remark_10_155_4
import stacks_project.Chap10.Lemma_10_97_7
import stacks_project.Chap15.Lemma_15_105_14

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingHom

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh]

local notation "mR" => maximalIdeal R
local notation "mRh" => maximalIdeal Rh
local notation "mRsh" => maximalIdeal Rsh

/-
Domain-style sampling:
- primary domain: local henselization and strict henselization maps of local rings, together with
  their maximal-ideal and Artinian-quotient behavior;
- sampled owner declarations of the same kind:
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `IsHenselizationOf.map_maximalIdeal`,
  `IsStrictHenselizationOf.map_maximalIdeal`,
  `RingHom.formallyEtale_quotientMap_pow_bijective`,
  `strictHenselization_over_henselization_isStrictHenselizationOf`;
- best owner abstraction: the primitive source data is carried by `IsHenselizationOf` and
  `IsStrictHenselizationOf`; weakly étale and formally étale consequences, faithful flatness,
  maximal-ideal extension, and quotient comparison are derived API from those owners;
- primitive data: locality of the structural map, filtered-colimit-of-etale presentation,
  maximal-ideal image, and for henselizations the residue-field bijectivity;
- derived API: faithful flatness of the structural maps and the induced comparison on quotients by
  powers of the maximal ideal.

Layer triage:
- `source-facing`: parts (4), (6), and (7) of Lemma 15.45.1;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`,
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `RingHom.formallyEtale_quotientMap_pow_bijective`;
- `bridge/view`: parts (1), (2), (3), and (5) as direct owner specializations, together with
  `strictHenselization_over_henselization_isStrictHenselizationOf`.
-/

section Henselization

variable [IsHenselizationOf R Rh]

/-- Lemma 15.45.1 (1): the canonical map from a local ring to its henselization is faithfully
flat. -/
theorem henselizationMap_faithfullyFlat :
    (algebraMap R Rh).FaithfullyFlat := by
  let _ : Algebra.IsWeaklyEtale R Rh :=
    isWeaklyEtale_of_isFilteredColimitOfEtale
      IsHenselizationOf.isFilteredColimitOfEtale
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

section StrictHenselization

variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh]
variable [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.1 (2): the canonical map from a local ring to its strict henselization is
faithfully flat. -/
theorem strictHenselizationMap_faithfullyFlat :
    (algebraMap R Rsh).FaithfullyFlat := by
  let _ : Algebra.IsWeaklyEtale R Rsh :=
    isWeaklyEtale_of_isFilteredColimitOfEtale
      IsStrictHenselizationOf.isFilteredColimitOfEtale
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end StrictHenselization

section StrictOverHenselization
variable [Algebra Rh Rsh] [IsScalarTower R Rh Rsh]

-- Proof sketch: this is one of the defining properties of `IsHenselizationOf`.
/- Lemma 15.45.1 (3): the maximal ideal of a henselization is the extension of the maximal ideal
of the base local ring. -/
recall IsHenselizationOf.map_maximalIdeal

-- Proof sketch:
-- `strictHenselization_over_henselization_isStrictHenselizationOf` upgrades `R → Rsh` to a strict
-- henselization, so both sides identify with `maximalIdeal Rsh` via the owner theorem
-- `IsStrictHenselizationOf.map_maximalIdeal`.
/-- Lemma 15.45.1 (4): if `Rh` is a henselization of `R` and `Rsh` is a strict henselization of
`Rh`, then the image of the maximal ideal of `R` in `Rsh` is the image of the maximal ideal of
`Rh`. -/
theorem strictHenselizationOverHenselization_map_baseMaximalIdeal :
    Ideal.map (algebraMap R Rsh) mR = Ideal.map (algebraMap Rh Rsh) mRh := by
  calc
    Ideal.map (algebraMap R Rsh) mR =
        Ideal.map (algebraMap Rh Rsh) (Ideal.map (algebraMap R Rh) mR) := by
      simpa [Ideal.map_map, IsScalarTower.algebraMap_eq R Rh Rsh]
    _ = Ideal.map (algebraMap Rh Rsh) mRh := by
      rw [IsHenselizationOf.map_maximalIdeal]

variable [IsStrictHenselizationOf Rh Rsh]

-- Proof sketch: this is one of the defining properties of `IsStrictHenselizationOf` applied to
-- the henselian local ring `Rh`.
/- Lemma 15.45.1 (5): the maximal ideal of a strict henselization over `Rh` is the extension of
the maximal ideal of `Rh`. -/
recall IsStrictHenselizationOf.map_maximalIdeal

end StrictOverHenselization

-- Proof sketch: `RingHom.formallyEtale_of_isFilteredColimitOfEtale` makes the henselization map
-- `R → Rh` formally étale, and the induced map on closed fibers `R → Rh / maximalIdeal Rh` is
-- surjective because the residue-field map of a henselization is bijective. Apply the owner
-- theorem `RingHom.formallyEtale_quotientMap_pow_bijective` with `J = maximalIdeal Rh`.
/-- Lemma 15.45.1 (6): for every `n`, the canonical map
`R / maximalIdeal R ^ n → Rh / maximalIdeal Rh ^ n` is bijective. -/
theorem henselizationQuotientPowMap_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap (mRh ^ n) (algebraMap R Rh)
        (pow_maximalIdeal_le_comap_pow_maximalIdeal (algebraMap R Rh) n)) := sorry

end Henselization

section StrictHenselizationQuotients

-- For part `(7)`, use the canonical quotient owner
-- `Ideal.Quotient.algebraQuotientOfLEComap` as local instance data rather than a named local
-- wrapper.
local instance [IsStrictHenselizationOf R Rsh] (n : ℕ) :
    Algebra (R ⧸ mR ^ n) (Rsh ⧸ mRsh ^ n) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (pow_maximalIdeal_le_comap_pow_maximalIdeal (algebraMap R Rsh) n)

/-- Lemma 15.45.1 (7): there is a single family of elements of `Rˢʰ` whose classes modulo
`maximalIdeal Rˢʰ ^ n` form a basis of `Rˢʰ / maximalIdeal Rˢʰ ^ n` over
`R / maximalIdeal R ^ n` for every `n`. -/
theorem strictHenselization_exists_basis_lift_family [IsStrictHenselizationOf R Rsh] :
    ∃ (ι : Type u) (x : ι → Rsh), ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ mR ^ n) (Rsh ⧸ mRsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i) := sorry

end StrictHenselizationQuotients

end
