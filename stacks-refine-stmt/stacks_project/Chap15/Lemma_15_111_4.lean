import Mathlib
import stacks_project.Chap10.Definition_10_32_1
import stacks_project.Chap15.Lemma_15_111_2
import stacks_project.Chap15.Lemma_15_111_3

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial PrimeSpectrum
open RingHom
open scoped Pointwise

universe u v

/- Domain-style sampling for Lemma 15.111.4:
- primary domain: invariant-theoretic quotient maps for fixed subrings under finite group actions
- sampled owner declarations:
  `FixedPoints.subring`,
  `fixedPointsQuotientToQuotientFixedPoints`,
  `Ideal.map`,
  `Ideal.quotientMap`
- best owner abstraction: the canonical owner map
  `fixedPointsQuotientToQuotientFixedPoints I hI : R^G / (I ∩ R^G) → (R / I)^G`; this file is the
  source-facing specialization to the extended ideal `JR` of an ideal `J ⊆ R^G`
- primitive data: `J : Ideal RFix` and its extension ideal `Ideal.map fixedSubringSubtype J : Ideal R`
- derived API: the canonical fixed quotient subring `FixedPoints.subring (R ⧸ JR) G`, the
  source-facing map `(R^G)/J → (R/JR)^G`, and the polynomial/integrality consequences of that map

Layer triage:
- `source-facing`: the specialized map `(R^G)/J → (R/JR)^G` and its consequences
- `core/canonical`: `fixedPointsQuotientToQuotientFixedPoints`
- `bridge/view`: factoring the owner map through the canonical quotient map
  `(R^G)/J → R^G / (JR ∩ R^G)`

The file should keep the source-facing quotient map, but its concrete data should be expressed in
terms of the owner abstraction and the canonical extension ideal `JR`, rather than by repeating the
raw `Ideal.map` / `Ideal.comap` expressions declaration-by-declaration.
-/

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

-- Proof sketch: if `x ∈ JR`, write `x` as a finite sum of products of fixed elements from `J`
-- with arbitrary coefficients; applying `g` fixes the coefficients from `J`, so `g • x` remains
-- in `JR`.
/-- The extended ideal `JR` is stable under each element of `G`. -/
private theorem smul_fixedSubringIdeal_map
    (J : Ideal RFix) (g : G) :
    g • Ideal.map (FixedPoints.subring R G).subtype J =
      Ideal.map (FixedPoints.subring R G).subtype J := sorry

/-- The extension `JR` of an ideal `J ⊆ R^G` along the fixed-subring inclusion `R^G ↪ R`. -/
abbrev fixedSubringIdealExtension (J : Ideal RFix) : Ideal R :=
  Ideal.map (FixedPoints.subring R G).subtype J

instance fixedSubringIdealMapQuotientMulSemiringAction (J : Ideal RFix) :
    MulSemiringAction G (R ⧸ fixedSubringIdealExtension J) :=
  quotientMulSemiringAction (fixedSubringIdealExtension J)
    (smul_fixedSubringIdeal_map J)

/-- The fixed subring `(R / JR)^G` of the quotient by the extension of `J ⊆ R^G`. -/
abbrev fixedSubringFixedQuotient (J : Ideal RFix) :=
  let JR : Ideal R := fixedSubringIdealExtension J
  letI := fixedSubringIdealMapQuotientMulSemiringAction J
  FixedPoints.subring (R ⧸ JR) G

/-- The canonical map `(R^G)/J → (R / JR)^G`. -/
def fixedSubringQuotientToFixedQuotient (J : Ideal RFix) :
    RFix ⧸ J →+* fixedSubringFixedQuotient J :=
  let JR : Ideal R := fixedSubringIdealExtension J
  letI := fixedSubringIdealMapQuotientMulSemiringAction J
  (fixedPointsQuotientToQuotientFixedPoints JR (smul_fixedSubringIdeal_map J)).comp
    (Ideal.quotientMap _ (RingHom.id _) Ideal.le_comap_map)

end

section FixedIdealExtensionQuotient

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]
variable [Finite G] (J : Ideal (FixedPoints.subring R G))

local notation "RFix" => FixedPoints.subring R G

local notation "JR" => fixedSubringIdealExtension J
local instance : MulSemiringAction G (R ⧸ JR) :=
  fixedSubringIdealMapQuotientMulSemiringAction J
local notation "QuotFix" => fixedSubringFixedQuotient J

-- Proof sketch: apply Lemma `15.111.1` to the equivariant quotient map `R → R/JR`, using the
-- induced fixed quotient subring as codomain. The orbit polynomial obtained there descends to a
-- monic polynomial over `(R^G)/J`.
/-- Lemma 15.111.4: for every fixed class `b ∈ (R/JR)^G`, there is a monic polynomial over
`(R^G)/J` whose image in `(R/JR)^G[T]` is `(X - C b)^|G|`. -/
theorem exists_monic_polynomial_over_fixedSubringQuotient_map_eq_X_sub_C_pow
    (b : QuotFix) :
    ∃ P : Polynomial (RFix ⧸ J),
      P.Monic ∧
        P.map (fixedSubringQuotientToFixedQuotient J) = (X - C b) ^ Nat.card G := sorry

-- Proof sketch: lift a kernel element to an invariant element of `JR`; then Lemma `15.111.3`
-- shows that every nonleading coefficient of its orbit polynomial dies modulo `J`, so the orbit
-- polynomial becomes `X^|G|`.
/-- A kernel element of `(R^G)/J → (R/JR)^G` satisfies `(X - C a)^|G| = X^|G|`. -/
theorem kernelElement_X_sub_pow_eq_X_pow
    (a : RingHom.ker (fixedSubringQuotientToFixedQuotient J)) :
    (X - C a.1) ^ Nat.card G = X ^ Nat.card G := sorry

-- Proof sketch: the kernel identity above makes the kernel locally nilpotent, which is the
-- remaining source-facing input for the Chapter 10 shift-power criterion.
/-- The kernel of `(R^G)/J → (R/JR)^G` is locally nilpotent. -/
theorem fixedSubringQuotientToFixedQuotient_ker_isLocallyNilpotent
    :
    (RingHom.ker (fixedSubringQuotientToFixedQuotient J)).IsLocallyNilpotent := sorry

-- Proof sketch: combine the monic-polynomial statement and the locally nilpotent-kernel theorem
-- above with the canonical Chapter 10 criterion for shift-power generated maps.
/-- The canonical map `(R^G)/J → (R/JR)^G` is integral. -/
theorem fixedSubringQuotientToFixedQuotient_isIntegral
    :
    (fixedSubringQuotientToFixedQuotient J).IsIntegral := sorry

-- Proof sketch: the same Chapter 10 criterion identifies the induced map on spectra as a
-- homeomorphism.
/-- The induced map `Spec((R/JR)^G) → Spec((R^G)/J)` is a homeomorphism. -/
theorem fixedSubringQuotientToFixedQuotient_isHomeomorph_comap
    :
    IsHomeomorph (PrimeSpectrum.comap (fixedSubringQuotientToFixedQuotient J)) := sorry

-- Proof sketch: the residue-field clause is another consequence of the same shift-power
-- generation criterion applied to `(R^G)/J → (R/JR)^G`.
/-- The canonical map `(R^G)/J → (R/JR)^G` induces purely inseparable residue-field extensions. -/
theorem fixedSubringQuotientToFixedQuotient_hasPurelyInseparableResidueFieldExtensions
    :
    (fixedSubringQuotientToFixedQuotient J).HasPurelyInseparableResidueFieldExtensions := sorry

end FixedIdealExtensionQuotient
