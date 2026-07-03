import Mathlib
import Mathlib.RingTheory.Invariant.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_111_1 (from Chap15) -/
universe u v w

open Polynomial

/- Domain-style sampling for Lemma 15.111.1:
- primary domain: invariant theory for fixed subrings under finite group actions
- sampled owner declarations:
  `RingHom.codRestrict`,
  `MulSemiringAction.charpoly_eq`,
  `Algebra.IsInvariant.charpoly_mem_lifts`,
  `Polynomial.lifts_and_natDegree_eq_and_monic`
- best owner abstraction: the orbit polynomial owner `MulSemiringAction.charpoly` together with the
  canonical lift-to-subring theorem `Algebra.IsInvariant.charpoly_mem_lifts`; the induced map on
  fixed subrings is a small bridge built from `RingHom.codRestrict`
- primitive data: an equivariant ring homomorphism `φ : A →+*[G] B`, its surjectivity, and a fixed
  element `b : B^G`
- derived API: the monic polynomial over `A^G` mapping to `(X - C b) ^ |G|`

Layer triage:
- `source-facing`: the existence of the monic polynomial over the fixed subring
- `core/canonical`: `MulSemiringAction.charpoly` and `Algebra.IsInvariant.charpoly_mem_lifts`
- `bridge/view`: the induced ring homomorphism on fixed subrings

The theorem should stay source-facing, while its proof reuses the invariant-ring owner API instead
of rebuilding the coefficient-lift argument entrywise.
-/

section

variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]
variable [MulSemiringAction G A] [MulSemiringAction G B]

local notation "AFix" => FixedPoints.subring A G
local notation "BFix" => FixedPoints.subring B G

namespace FixedPoints

/-- A ring is invariant over its own fixed subring. -/
instance subring_isInvariant : Algebra.IsInvariant (FixedPoints.subring A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

end FixedPoints

namespace MulSemiringActionHom

/-- The ring homomorphism induced on fixed subrings by an equivariant ring homomorphism. -/
def fixedPoints (φ : A →+*[G] B) : AFix →+* BFix :=
  RingHom.codRestrict
    ((φ : A →+* B).comp (FixedPoints.subring A G).subtype)
    BFix fun a g ↦ by
    simpa [MulSemiringActionHom.map_smul] using congrArg φ (a.2 g)

/-- Composing the induced map on fixed subrings with the subtype recovers the underlying ring
homomorphism restricted to the fixed subring. -/
@[simp] theorem subtype_comp_fixedPoints (φ : A →+*[G] B) :
    (FixedPoints.subring B G).subtype.comp φ.fixedPoints =
      (φ : A →+* B).comp (FixedPoints.subring A G).subtype :=
  rfl

end MulSemiringActionHom

variable [Finite G]

-- Proof sketch: choose `a : A` with `φ a = b`, form the orbit product
-- `∏ g : G, (X - C ⟨g • a, ...⟩)`, and use equivariance to see that its coefficients lie in
-- `A^G`; after applying the induced map on fixed subrings, this becomes `(X - C b) ^ |G|`.
/-- Lemma 15.111.1: for a surjective equivariant ring homomorphism and a fixed element `b` of `B`,
there is a monic polynomial over the fixed subring of `A` mapping to `(X - C b) ^ |G|` over the
fixed subring of `B`. -/
theorem exists_monic_polynomial_over_fixedPoints_map_eq_X_sub_C_pow
    (φ : A →+*[G] B) (hφ : Function.Surjective φ) (b : BFix) :
    ∃ P : Polynomial AFix,
      P.Monic ∧
        P.map φ.fixedPoints = (X - C b) ^ Nat.card G := by
  classical
  cases nonempty_fintype G
  obtain ⟨a, ha⟩ := hφ b
  have hchar_lifts :
      MulSemiringAction.charpoly G a ∈ Polynomial.lifts (FixedPoints.subring A G).subtype := by
    simpa using Algebra.IsInvariant.charpoly_mem_lifts AFix A G a
  obtain ⟨P, hPmap, -, hPmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hchar_lifts
      (MulSemiringAction.monic_charpoly G a)
  refine ⟨P, hPmonic, ?_⟩
  have hb : ∀ g : G, g • (b : B) = b := b.2
  exact (Polynomial.map_injective (FixedPoints.subring B G).subtype Subtype.val_injective) <|
    calc
      Polynomial.map (FixedPoints.subring B G).subtype (P.map φ.fixedPoints) =
          Polynomial.map ((FixedPoints.subring B G).subtype.comp φ.fixedPoints) P := by
            rw [Polynomial.map_map]
      _ = Polynomial.map ((φ : A →+* B).comp (FixedPoints.subring A G).subtype) P := by
            rw [MulSemiringActionHom.subtype_comp_fixedPoints]
      _ = Polynomial.map (φ : A →+* B) (MulSemiringAction.charpoly G a) := by
            rw [← hPmap, Polynomial.map_map]
      _ = (X - C (b : B)) ^ Fintype.card G := by
            rw [MulSemiringAction.charpoly_eq, Polynomial.map_prod]
            calc
              ∏ g : G, Polynomial.map (φ : A →+* B) (X - C (g • a)) =
                  ∏ g : G, (X - C (g • (b : B))) := by
                    refine Finset.prod_congr rfl ?_
                    intro g _
                    simp [ha]
              _ = ∏ _ : G, (X - C (b : B)) := by
                    refine Finset.prod_congr rfl ?_
                    intro g _
                    rw [hb g]
              _ = (X - C (b : B)) ^ Fintype.card G := by
                    simp
      _ = Polynomial.map (FixedPoints.subring B G).subtype ((X - C b) ^ Nat.card G) := by
            simp [Nat.card_eq_fintype_card]

end

/-! ### Lemma_15_111_2 (from Chap15) -/
open PrimeSpectrum
open Ideal.Quotient (lift eq_zero_iff_mem)
open scoped Pointwise

universe u v w

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

/- Domain-style sampling for Lemma 15.111.2:
- primary domain: invariant-theoretic quotient maps for fixed subrings under finite group actions
- sampled owner declarations:
  `FixedPoints.subring`,
  `MulSemiringActionHom.fixedPoints`,
  `MulSemiringActionHom.subtype_comp_fixedPoints`,
  `Ideal.Quotient.lift`
- best owner abstraction: the source-facing map
  `R^G / (I ∩ R^G) → (R / I)^G` should be built from the equivariant quotient morphism
  `R →+*[G] R ⧸ I` via the upstream owner `MulSemiringActionHom.fixedPoints`, then factored through
  the quotient of `R^G`
- primitive data: the invariant ideal `I` together with the induced quotient action on `R ⧸ I`
- derived API: the fixed subring `(R ⧸ I)^G`, the induced map on fixed subrings, and its quotient
  factor

Layer triage:
- `source-facing`: the quotient map `fixedPointsQuotientToQuotientFixedPoints`
- `core/canonical`: `FixedPoints.subring` and `MulSemiringActionHom.fixedPoints`
- `bridge/view`: the induced quotient action on `R ⧸ I` and the quotient lift on `R^G`

The local quotient action remains primitive here, but the induced map on fixed subrings should
reuse the owner declaration from `Lemma_15_111_1` rather than duplicating it.
-/

/-- An invariant ideal is stable under the ring endomorphism attached to each group element. -/
private theorem le_comap_of_smul_eq (I : Ideal R) (hI : ∀ g : G, g • I = I) (g : G) :
    I ≤ Ideal.comap (MulSemiringAction.toRingHom G R g) I :=
  Ideal.map_le_iff_le_comap.mp <| le_of_eq <| by
    simpa [Ideal.pointwise_smul_def] using hI g

private def quotientSmulRingHom (I : Ideal R) (hI : ∀ g : G, g • I = I) (g : G) :
    R ⧸ I →+* R ⧸ I :=
  Ideal.quotientMap I (MulSemiringAction.toRingHom G R g) (le_comap_of_smul_eq I hI g)

@[simp] private theorem quotientSmulRingHom_mk
    (I : Ideal R) (hI : ∀ g : G, g • I = I) (g : G) (x : R) :
    quotientSmulRingHom I hI g (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (g • x) := by
  simp [quotientSmulRingHom]

/-- The quotient ring inherits the given group action whenever the ideal is stable under that
action. -/
instance quotientMulSemiringAction (I : Ideal R)
    (hI : ∀ g : G, g • I = I) :
    MulSemiringAction G (R ⧸ I) where
  smul g := quotientSmulRingHom I hI g
  one_smul := by
    rintro ⟨x⟩
    change quotientSmulRingHom I hI 1 (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I x
    rw [quotientSmulRingHom_mk]
    simp
  mul_smul := by
    intro g₁ g₂
    rintro ⟨x⟩
    change quotientSmulRingHom I hI (g₁ * g₂) (Ideal.Quotient.mk I x) =
        quotientSmulRingHom I hI g₁ (quotientSmulRingHom I hI g₂ (Ideal.Quotient.mk I x))
    rw [quotientSmulRingHom_mk, quotientSmulRingHom_mk, quotientSmulRingHom_mk]
    simp [mul_smul]
  smul_zero := by
    intro g
    change quotientSmulRingHom I hI g (Ideal.Quotient.mk I 0) = Ideal.Quotient.mk I 0
    rw [quotientSmulRingHom_mk]
    simp
  smul_add := by
    intro g x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    change quotientSmulRingHom I hI g (Ideal.Quotient.mk I (a + b)) =
        quotientSmulRingHom I hI g (Ideal.Quotient.mk I a) +
          quotientSmulRingHom I hI g (Ideal.Quotient.mk I b)
    rw [quotientSmulRingHom_mk, quotientSmulRingHom_mk, quotientSmulRingHom_mk]
    simp [smul_add]
  smul_one := by
    intro g
    change quotientSmulRingHom I hI g (Ideal.Quotient.mk I 1) = Ideal.Quotient.mk I 1
    rw [quotientSmulRingHom_mk]
    simp
  smul_mul := by
    intro g x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    change quotientSmulRingHom I hI g (Ideal.Quotient.mk I (a * b)) =
        quotientSmulRingHom I hI g (Ideal.Quotient.mk I a) *
          quotientSmulRingHom I hI g (Ideal.Quotient.mk I b)
    rw [quotientSmulRingHom_mk, quotientSmulRingHom_mk, quotientSmulRingHom_mk]
    simp [smul_mul']

section Quotient

variable (I : Ideal R)
variable (hI : ∀ g : G, g • I = I)

private def quotientMkMulSemiringActionHom :
    letI := quotientMulSemiringAction I hI
    R →+*[G] R ⧸ I :=
  letI := quotientMulSemiringAction I hI
  { toRingHom := Ideal.Quotient.mk I
    map_smul' := fun g x ↦ quotientSmulRingHom_mk I hI g x }

/-- The canonical map from the quotient of the fixed subring to the fixed subring of the quotient
ring. -/
def fixedPointsQuotientToQuotientFixedPoints :
    letI := quotientMulSemiringAction I hI
    RFix ⧸ Ideal.comap (FixedPoints.subring R G).subtype I →+* FixedPoints.subring (R ⧸ I) G :=
  letI := quotientMulSemiringAction I hI
  lift (Ideal.comap (FixedPoints.subring R G).subtype I)
    ((quotientMkMulSemiringActionHom I hI).fixedPoints) fun x hx ↦ by
      apply Subtype.ext
      change Ideal.Quotient.mk I (x : R) = 0
      exact eq_zero_iff_mem.mpr hx

-- Proof sketch: this is the defining property of the quotient lift, so evaluating at the class of
-- a fixed element recovers the fixed-point image of that element in the quotient ring.
/-- The canonical map `R^G / (I ∩ R^G) → (R / I)^G` sends the class of a fixed element to its
class in the quotient ring after forgetting the fixed-point structure. -/
@[simp]
theorem fixedPointsQuotientToQuotientFixedPoints_mk
    (x : RFix) :
    ((fixedPointsQuotientToQuotientFixedPoints I hI
        (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I) x)) : R ⧸ I) =
      Ideal.Quotient.mk I x := by
  rfl

end Quotient

section Finite

variable [Finite G]

-- Proof sketch: use Lemma `15.111.1` for the surjective equivariant quotient map
-- `R → R ⧸ I` to obtain the shift-power polynomial condition for the induced map
-- `R^G / (I ∩ R^G) → (R / I)^G`; applying Lemma `10.46.11` gives integrality, a
-- homeomorphism on spectra, and purely inseparable residue-field extensions.
/-- Lemma 15.111.2: if a finite group `G` acts on `R` and `I` is stable under the action, then the
canonical map `R^G / (I ∩ R^G) → (R / I)^G` is integral, induces a homeomorphism on spectra, and
induces purely inseparable residue-field extensions. -/
theorem fixedPointsQuotient_isIntegral_and_isHomeomorph_comap
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    (fixedPointsQuotientToQuotientFixedPoints I hI).IsIntegral ∧
      IsHomeomorph (comap (fixedPointsQuotientToQuotientFixedPoints I hI)) ∧
      (fixedPointsQuotientToQuotientFixedPoints I hI).HasPurelyInseparableResidueFieldExtensions :=
  sorry

/-- The canonical map `R^G / (I ∩ R^G) → (R / I)^G` is integral. -/
theorem fixedPointsQuotient_isIntegral
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    (fixedPointsQuotientToQuotientFixedPoints I hI).IsIntegral := by
  rcases fixedPointsQuotient_isIntegral_and_isHomeomorph_comap I hI with ⟨hint, -, -⟩
  exact hint

/-- The induced map `Spec((R / I)^G) → Spec(R^G / (I ∩ R^G))` is a homeomorphism. -/
theorem fixedPointsQuotient_isHomeomorph_comap
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    IsHomeomorph (comap (fixedPointsQuotientToQuotientFixedPoints I hI)) := by
  rcases fixedPointsQuotient_isIntegral_and_isHomeomorph_comap I hI with ⟨-, hhomeo, -⟩
  exact hhomeo

-- Proof sketch: the same application of Lemma `10.46.11` to the induced fixed-points quotient map
-- also yields purely inseparable residue-field extensions.
/-- The canonical map `R^G / (I ∩ R^G) → (R / I)^G` induces purely inseparable extensions on
residue fields. -/
theorem fixedPointsQuotient_hasPurelyInseparableResidueFieldExtensions
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    (fixedPointsQuotientToQuotientFixedPoints I hI).HasPurelyInseparableResidueFieldExtensions := by
  rcases fixedPointsQuotient_isIntegral_and_isHomeomorph_comap I hI with ⟨_, _, hresidue⟩
  exact hresidue

end Finite

end

/-! ### Lemma_15_111_3 (from Chap15) -/
universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R] [Fintype G]

local notation "RFix" => FixedPoints.subring R G

/-- Lemma 15.111.3: if `x` lies in the extension of an ideal `J` of the fixed subring `R^G`, then
every nonleading coefficient of `∏ σ : G, (T - σ(x))` belongs to `J`. -/
-- Proof sketch: induct on an expression of `x` as a finite sum of elements of the extended ideal
-- `JR`. Replacing `x` by `y - f b` changes the orbit polynomial by a sum of terms divisible by
-- powers of `f ∈ J`, and the symmetric coefficient expressions remain fixed by the action, hence
-- define elements of the fixed subring lying in `J`.
theorem coeff_charpoly_mem_fixed_ideal_of_mem_ideal_map
    (J : Ideal RFix) {x : R}
    (hx : x ∈ Ideal.map (FixedPoints.subring R G).subtype J)
    (i : Fin (Fintype.card G)) :
    ⟨(MulSemiringAction.charpoly G x).coeff i,
      fun g ↦ MulSemiringAction.smul_coeff_charpoly x i g⟩ ∈ J := sorry

end

/-! ### Lemma_15_111_4 (from Chap15) -/
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

/-! ### Remark_15_111_5 (from Chap15) -/
universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

/- Domain-style sampling for Remark 15.111.5:
- primary domain: invariant-theoretic fixed-point quotients for finite group actions when `|G|` is
  invertible
- sampled owner declarations:
  `fixedSubringQuotientToFixedQuotient`,
  `fixedSubringFixedQuotient`,
  `RingEquiv.ofBijective`,
  `Nat.card`
- best owner abstraction: the source-facing owner is still the canonical map
  `fixedSubringQuotientToFixedQuotient J` from `Lemma_15_111_4`; once bijectivity is proved, the
  canonical derived API is the induced ring equivalence
- primitive data: the ideal `J : Ideal RFix` and the invertibility hypothesis on `|G|`
- derived API: bijectivity of the canonical map and the resulting ring equivalence

Layer triage:
- `source-facing`: bijectivity of the canonical map `(R^G)/J → (R / JR)^G`
- `core/canonical`: `fixedSubringQuotientToFixedQuotient` from `Lemma_15_111_4`
- `bridge/view`: `RingEquiv.ofBijective` packaging that canonical map as an isomorphism

The public finiteness assumption should be `[Finite G]`; the proof may introduce a local
`Fintype` instance, but the theorem statement only depends on `Nat.card G`.
-/

-- Proof sketch: use the averaging operator `|G|⁻¹ ∑ g∈G g` on `R / JR`. When `|G|` is invertible
-- in `R`, averaging projects onto the fixed subring and gives an inverse to the canonical map
-- from `(R^G)/J`.
/-- Remark 15.111.5: if `|G|` is a unit in `R`, then the canonical map
`(R^G)/J → (R / JR)^G` is bijective, hence an isomorphism. -/
theorem fixedSubringQuotientToFixedQuotient_bijective_of_isUnit_card
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    Function.Bijective (fixedSubringQuotientToFixedQuotient J) := by
  letI := Fintype.ofFinite G
  letI := h_card.invertible
  sorry

/-- Remark 15.111.5, canonical isomorphism form: if `|G|` is a unit in `R`, then the canonical map
`(R^G)/J → (R / JR)^G` is an isomorphism of rings. -/
noncomputable def fixedSubringQuotientToFixedQuotientEquivOfIsUnit_card
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    RFix ⧸ J ≃+* fixedSubringFixedQuotient J :=
  RingEquiv.ofBijective (fixedSubringQuotientToFixedQuotient J)
    (fixedSubringQuotientToFixedQuotient_bijective_of_isUnit_card J h_card)

end

/-! ### Lemma_15_111_6 (from Chap15) -/
open Polynomial
open scoped TensorProduct

universe u v w

/- Domain-style sampling for Lemma 15.111.6:
- primary domain: invariant theory for finite group actions on a tensor-product base change
- sampled owner declarations:
  `FixedPoints.subring`,
  `FixedPoints.subalgebra`,
  `MulSemiringAction.compHom`,
  `Algebra.TensorProduct.map`
- best owner abstraction: the fixed-object owners `FixedPoints.subring` / `FixedPoints.subalgebra`,
  with the induced tensor action treated only as the bridge obtained from
  `Algebra.TensorProduct.map` and `MulSemiringAction.compHom`
- primitive data: a `G`-action on `R`, an `R^G`-algebra `A`, and the canonical base-change ring
  `A ⊗[R^G] R`
- derived API: the induced right-factor `G`-action on `A ⊗[R^G] R`, its fixed subalgebra, and the
  orbit-polynomial consequences for invariant elements

Layer triage:
- `source-facing`: the two orbit-polynomial statements for invariant elements and kernel elements
- `core/canonical`: `FixedPoints.subring`, `FixedPoints.subalgebra`, `MulSemiringAction.compHom`,
  and `Algebra.TensorProduct.map`
- `bridge/view`: the induced action on `A ⊗[R^G] R`, acting trivially on `A` and through the given
  `G`-action on `R`

The source-facing theorems should stay here, but the bridge layer should reuse the canonical tensor
and fixed-point owners instead of carrying a longer hand-rolled action API than needed.
-/

section

variable {R : Type u} {G : Type v}
variable [CommRing R] [Group G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

-- Proof sketch: if `r ∈ R^G`, then every `g : G` fixes `r`; therefore `g • (r * x) = r * (g • x)`
-- for all `x : R`, so the action is `R^G`-linear.
/-- Fixed scalars from `R^G` commute with the given `G`-action on `R`. -/
instance fixedPointsSubring_smulCommClass :
    SMulCommClass G RFix R := sorry

end

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R

private noncomputable abbrev tensorBaseChangeRightAlgHom (g : G) :
    BaseChange →ₐ[RFix] BaseChange :=
  Algebra.TensorProduct.map (AlgHom.id RFix A) (MulSemiringAction.toAlgHom RFix R g)

private noncomputable def tensorBaseChangeRightAction :
    G →* (BaseChange →+* BaseChange) where
  toFun g := (tensorBaseChangeRightAlgHom g).toRingHom
  map_one' := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext a
      simp [tensorBaseChangeRightAlgHom]
    · ext r
      simp [tensorBaseChangeRightAlgHom]
  map_mul' g h := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext a
      simp [tensorBaseChangeRightAlgHom]
    · ext r
      simp [tensorBaseChangeRightAlgHom, mul_smul]

/-- The induced `G`-action on `A ⊗[R^G] R`, acting on the right tensor factor and trivially on
`A`. -/
noncomputable instance tensorBaseChangeRightMulSemiringAction :
    MulSemiringAction G BaseChange :=
  MulSemiringAction.compHom BaseChange
    (tensorBaseChangeRightAction : G →* (BaseChange →+* BaseChange))

@[simp]
theorem tensorBaseChangeRight_smul_tmul (g : G) (a : A) (r : R) :
    g • ((a ⊗ₜ[RFix] r : BaseChange)) = a ⊗ₜ[RFix] (g • r) := by
  change
    ((tensorBaseChangeRightAction : G →* (BaseChange →+* BaseChange)) g) (a ⊗ₜ[RFix] r) =
    a ⊗ₜ[RFix] (g • r)
  rfl

instance tensorBaseChangeRight_smulCommClass :
    SMulCommClass G RFix BaseChange where
  smul_comm g x z := by
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro a r
      simp [TensorProduct.smul_tmul']
    · intro z w hz hw
      simp [hz, hw]

end

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R
local notation "BaseChangeFixed" => FixedPoints.subalgebra RFix BaseChange G

-- Proof sketch: choose a polynomial algebra `E` over `R^G` mapping surjectively to `A`, lift `b`
-- to an invariant element of `E ⊗[R^G] R`, apply Lemma `15.111.4` to that polynomial algebra,
-- and descend the resulting monic polynomial to `A`.
/-- Lemma 15.111.6 (1): if `b : A ⊗[R^G] R` is fixed by the induced right `G`-action, then there
exists a monic polynomial over `A` whose image in `(A ⊗[R^G] R)[T]` is `(X - C b)^|G|`. -/
theorem exists_monic_polynomial_over_baseChange_eq_X_sub_C_pow_of_fixed
    (b : BaseChangeFixed) :
    ∃ P : Polynomial A,
      P.Monic ∧
        P.map (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) =
          (X - C (b : BaseChange)) ^ Nat.card G := sorry

-- Proof sketch: apply the first clause to the image of `a` in `A ⊗[R^G] R`; because `a` lies in
-- the kernel of `A → A ⊗[R^G] R`, its image is zero, so the translated polynomial identity
-- reduces to `(X - C a)^|G| = X^|G|` in `A[T]`.
/-- Lemma 15.111.6 (2): if `a` maps to zero under the canonical base-change map
`A → A ⊗[R^G] R`, then `(X - C a)^|G| = X^|G|` in `A[T]`. -/
theorem kernelElement_X_sub_pow_eq_X_pow_of_baseChange
    (a : RingHom.ker (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)) :
    ((X - C a.1) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := sorry

end

/-! ### Lemma_15_111_7 (from Chap15) -/
open PrimeSpectrum RingHom
open scoped TensorProduct

universe u v w

/- Domain-style sampling for Lemma 15.111.7:
- primary domain: invariant theory for the canonical fixed-points map on the base-changed tensor
  product `A ⊗[R^G] R`
- sampled owner declarations:
  `FixedPoints.subalgebra`,
  `Algebra.TensorProduct.includeLeft`,
  `RingHom.ShiftPowerPolynomialImageGenerating`,
  `RingHom.isIntegral_of_shiftPowerPolynomialImageGenerating`
- best owner abstraction: the source-facing owner is the canonical map
  `A → (A ⊗[R^G] R)^G`; the Chapter 10 owner abstraction governing its spectral consequences is the
  shift-power generation predicate `RingHom.ShiftPowerPolynomialImageGenerating`
- primitive data: the fixed subalgebra `FixedPoints.subalgebra RFix (A ⊗[RFix] R) G` and the
  canonical map into it induced by `Algebra.TensorProduct.includeLeft`
- derived API: the flat isomorphism, the shift-power bridge theorem, integrality, purely
  inseparable residue-field extensions, and the homeomorphism on spectra

Layer triage:
- `source-facing`: the canonical fixed-points map and the four source statements of Lemma 15.111.7
- `core/canonical`: `FixedPoints.subalgebra`, `Algebra.TensorProduct.includeLeft`, and the Chapter
  10 owner predicate `RingHom.ShiftPowerPolynomialImageGenerating`
- `bridge/view`: the proof that the canonical fixed-points map satisfies the shift-power
  generation hypothesis, allowing the Chapter 10 owner theorems to supply the spectral
  consequences directly

The file should keep the source-facing fixed-points map, but its spectral consequences should be
derived through the Chapter 10 owner abstraction rather than via parallel local wrappers.
-/

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R
local notation "BaseChangeFixed" => FixedPoints.subalgebra RFix BaseChange G

-- Proof sketch: the induced endomorphism on `A ⊗[R^G] R` acts trivially on the left tensor factor,
-- so it fixes every element coming from `A` through `includeLeft`.
/-- The canonical map `A → A ⊗[R^G] R` lands in the fixed part of the base-changed tensor
product. -/
theorem tensorBaseChange_includeLeft_mem_fixedPoints (a : A) :
    (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) a ∈ BaseChangeFixed := sorry

/-- The canonical `RFix`-algebra map `A → (A ⊗[R^G] R)^G`. -/
noncomputable def tensorBaseChangeFixedPointsMap :
    A →ₐ[RFix] BaseChangeFixed :=
  (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange).codRestrict BaseChangeFixed
    tensorBaseChange_includeLeft_mem_fixedPoints

end

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R
local notation "BaseChangeFixed" => FixedPoints.subalgebra RFix BaseChange G
local notation "f" =>
  ((tensorBaseChangeFixedPointsMap : A →ₐ[RFix] BaseChangeFixed) : A →+* BaseChangeFixed)

-- Proof sketch: tensor the equalizer sequence
-- `0 → R^G → R → ∏_{g ∈ G} R` with the flat `R^G`-algebra `A`; exactness identifies the equalizer
-- with the fixed elements of `A ⊗[R^G] R`, so the canonical map from `A` is an isomorphism.
/-- The canonical map `A → (A ⊗[R^G] R)^G` is bijective when `R^G → A` is flat. -/
private theorem tensorBaseChangeFixedPointsMap_bijective_of_flat_aux [Module.Flat RFix A] :
    Function.Bijective (tensorBaseChangeFixedPointsMap : A →ₐ[RFix] BaseChangeFixed) := sorry

/-- Lemma 15.111.7 (1): if `R^G → A` is flat, then the canonical map
`A → (A ⊗[R^G] R)^G` is an isomorphism of `R^G`-algebras. -/
noncomputable def tensorBaseChangeFixedPointsEquivOfFlat [Module.Flat RFix A] :
    A ≃ₐ[RFix] BaseChangeFixed :=
  AlgEquiv.ofBijective tensorBaseChangeFixedPointsMap
    tensorBaseChangeFixedPointsMap_bijective_of_flat_aux

/-- The canonical isomorphism of Lemma 15.111.7 (1) acts by the canonical map
`A → (A ⊗[R^G] R)^G`. -/
@[simp] theorem tensorBaseChangeFixedPointsEquivOfFlat_apply [Module.Flat RFix A] (a : A) :
    (tensorBaseChangeFixedPointsEquivOfFlat : A ≃ₐ[RFix] BaseChangeFixed) a =
      tensorBaseChangeFixedPointsMap a := rfl

/-- The canonical map `A → (A ⊗[R^G] R)^G` is bijective when `R^G → A` is flat. -/
theorem tensorBaseChangeFixedPointsMap_bijective_of_flat [Module.Flat RFix A] :
    Function.Bijective (tensorBaseChangeFixedPointsMap : A →ₐ[RFix] BaseChangeFixed) :=
  tensorBaseChangeFixedPointsEquivOfFlat.bijective

-- Proof sketch: every element of `BaseChangeFixed` is fixed by definition, so Lemma `15.111.6`
-- supplies the required polynomial identity with exponent `|G|`; since this holds for every
-- element of the codomain, the Chapter 10 shift-power generation owner predicate follows
-- directly.
/-- The canonical map `A → (A ⊗[R^G] R)^G` satisfies the shift-power generation hypothesis from
Lemma `10.46.11`. -/
theorem tensorBaseChangeFixedPointsMap_shiftPowerPolynomialImageGenerating :
    (f).ShiftPowerPolynomialImageGenerating := sorry

-- Proof sketch: apply Lemma `15.111.6 (2)` to any kernel element of
-- `A → (A ⊗[R^G] R)^G`; the resulting identity `(X - C a)^|G| = X^|G|` forces `a^|G| = 0`, so
-- every kernel element is nilpotent.
theorem tensorBaseChangeFixedPointsMap_ker_isLocallyNilpotent :
    (ker f).IsLocallyNilpotent := sorry

-- Proof sketch: for an invariant element of `A ⊗[R^G] R`, Lemma `15.111.6` supplies a monic
-- polynomial over `A` annihilating it, so every element of `(A ⊗[R^G] R)^G` is integral over `A`.
/-- Lemma 15.111.7 (2): the canonical map `A → (A ⊗[R^G] R)^G` is integral. -/
theorem tensorBaseChangeFixedPointsMap_isIntegral :
    (f).IsIntegral := by
  exact isIntegral_of_shiftPowerPolynomialImageGenerating f
    tensorBaseChangeFixedPointsMap_shiftPowerPolynomialImageGenerating

-- Proof sketch: the same orbit-polynomial argument gives the shift-power generation hypothesis,
-- and the positive-power bridge from Lemma `10.46.11`; together with local nilpotence of the
-- kernel, the canonical owner theorem `PrimeSpectrum.isHomeomorph_comap` applies directly.
/-- Lemma 15.111.7 (3): the induced map
`Spec((A ⊗[R^G] R)^G) → Spec(A)` is a homeomorphism. -/
theorem tensorBaseChangeFixedPointsMap_isHomeomorph_comap :
    IsHomeomorph (comap f) := by
  exact isHomeomorph_comap f
    (exists_pow_mem_range_of_shiftPowerPolynomialImageGenerating f
      tensorBaseChangeFixedPointsMap_shiftPowerPolynomialImageGenerating)
    tensorBaseChangeFixedPointsMap_ker_isLocallyNilpotent

-- Proof sketch: this is the residue-field clause of the Chapter 10 owner theorem applied to the
-- shift-power bridge above.
/-- Lemma 15.111.7 (4): the canonical map `A → (A ⊗[R^G] R)^G` induces purely inseparable
extensions on residue fields. -/
theorem tensorBaseChangeFixedPointsMap_hasPurelyInseparableResidueFieldExtensions :
    (f).HasPurelyInseparableResidueFieldExtensions := by
  exact hasPurelyInseparableResidueFieldExtensions_of_shiftPowerPolynomialImageGenerating f
    tensorBaseChangeFixedPointsMap_shiftPowerPolynomialImageGenerating

end

/-! ### Lemma_15_111_8 (from Chap15) -/
universe u v

open scoped Pointwise

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

attribute [local instance] fixedPointsSubring_smulCommClass

/- Domain-style sampling for Lemma 15.111.8:
- primary domain: invariant-theoretic transitivity on prime ideals above a fixed prime of the
  fixed subring
- sampled owner declarations:
  `fixedPointsSubring_smulCommClass`,
  `FixedPoints.subring_isInvariant`,
  `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `Ideal.LiesOver`,
  `Algebra.IsInvariant.orbit_eq_primesOver`
- best owner abstraction: `Algebra.IsInvariant.exists_smul_of_under_eq`
- primitive data: the fixed-subring extension `RFix ↪ R` and primes `q`, `q'` lying over
  `p : Ideal RFix`
- derived API: transitivity of the `G`-action on primes of `R` above `p`

Layer triage:
- `source-facing`: the fixed-subring prime-transitivity statement
- `core/canonical`: `Algebra.IsInvariant.exists_smul_of_under_eq`
- `bridge/view`: the imported fixed-subring action bridge `fixedPointsSubring_smulCommClass`
  together with the imported owner instance `FixedPoints.subring_isInvariant`

The public theorem stays source-facing, while the proof is reduced to a direct specialization of
the canonical invariant-theory owner theorem. The `SMulCommClass` bridge is already owned upstream
by `Lemma_15_111_6`, and the `IsInvariant` bridge is already owned upstream by `Lemma_15_111_1`,
so this file should reuse both owner declarations directly rather than rebuilding either locally.
-/

/-- Lemma 15.111.8: if two prime ideals of `R` lie over the same prime ideal of the fixed subring
`R^G`, then one is obtained from the other by the action of an element of `G`. -/
-- Proof sketch: specialize `Algebra.IsInvariant.exists_smul_of_under_eq` to the inclusion
-- `FixedPoints.subring R G ↪ R`. The hypotheses that `q` and `q'` both lie over `p` identify
-- their pullbacks to the fixed subring, and the general transitivity theorem then produces
-- `σ : G` with `σ • q = q'`.
theorem exists_smul_eq_of_liesOver_fixedPoints
    (p : Ideal RFix) (q q' : Ideal R)
    [q.IsPrime] [q'.IsPrime] [q.LiesOver p] [q'.LiesOver p] :
    ∃ σ : G, σ • q = q' := by
  simpa [eq_comm] using Algebra.IsInvariant.exists_smul_of_under_eq RFix R G q q'
    ((q.over_def p).symm.trans (q'.over_def p))

end

/-! ### Lemma_15_111_9 (from Chap15) -/
open scoped Pointwise

universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

/- Domain-style sampling for Lemma 15.111.9:
- primary domain: invariant-theoretic actions of decomposition/stabilizer groups on quotient and
  residue fields
- sampled owner declarations:
  `Algebra.IsInvariant`,
  `Ideal.Quotient.normal`,
  `Ideal.Quotient.stabilizerHom`,
  `IsFractionRing.stabilizerHom`,
  `IsFractionRing.stabilizerHom_surjective`
- best owner abstractions: the quotient-level normality theorem `Ideal.Quotient.normal` for clause
  `(1)`, and the stabilizer owner `IsFractionRing.stabilizerHom` with its canonical surjectivity
  theorem `IsFractionRing.stabilizerHom_surjective` for clause `(2)`
- primitive data: the invariant fixed-subring extension `RFix ⊆ R` together with primes
  `p ⊆ RFix`, `q ⊆ R` and the lying-over hypothesis `q.LiesOver p`
- derived API: normality of the residue-field extension and surjectivity of the decomposition-group
  action on `Aut(κ(q) / κ(p))`

Layer triage:
- `source-facing`: the textbook residue-field statement for the decomposition group over `p` and
  `q`
- `core/canonical`: `Ideal.Quotient.normal`, `IsFractionRing.stabilizerHom`, and
  `IsFractionRing.stabilizerHom_surjective`
- `bridge/view`: the fixed-subring/residue-field instances in this file realizing the source
  situation as an instance of the canonical owner theorem

The surjectivity clause is derived API from the owner theorem, so it should be expressed by direct
canonical reuse rather than by a parallel local wrapper theorem.
-/

attribute [local instance] fixedPointsSubring_smulCommClass

variable (p : Ideal (FixedPoints.subring R G)) [p.IsPrime]
variable (q : Ideal R) [q.IsPrime] [q.LiesOver p]

local notation "κp" => p.ResidueField
local notation "κq" => q.ResidueField

private noncomputable instance fixedPointsResidueFieldAlgebra :
    Algebra (RFix ⧸ p) κq :=
  ((Ideal.ResidueField.map p q (algebraMap RFix R) (Ideal.over_def q p)).comp
    (algebraMap (RFix ⧸ p) κp)).toAlgebra

-- Proof sketch: both ring homomorphisms are induced by the same inclusion `R^G ↪ R`; compare them
-- on quotient classes represented by elements of `R^G`.
private theorem fixedPointsResidueField_comp_quotient :
    algebraMap (RFix ⧸ p) κq =
      (algebraMap (R ⧸ q) κq).comp (algebraMap (RFix ⧸ p) (R ⧸ q)) := sorry

private noncomputable instance fixedPointsResidueFieldTower :
    IsScalarTower (RFix ⧸ p) κp κq :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable instance fixedPointsQuotientResidueFieldTower :
    IsScalarTower (RFix ⧸ p) (R ⧸ q) κq :=
  IsScalarTower.of_algebraMap_eq' (fixedPointsResidueField_comp_quotient p q)

-- Proof sketch: the invariant extension `R^G ⊆ R` is integral, so the induced residue field
-- extension is algebraic; normality follows from the orbit polynomial over `R^G` whose roots are
-- the conjugates `σ(a)` and whose reduction mod `q` splits in `κ(q)`.
/-- Lemma 15.111.9 (1): if `q` is a prime of `R` lying over a prime `p` of the fixed subring
`R^G`, then the residue field extension `κ(q) / κ(p)` is algebraic and normal. -/
theorem residueField_normal_of_liesOver_fixedPoints :
    Normal κp κq := sorry

-- Proof sketch: the stabilizer of `q` acts on `R / q` over `(R^G) / p`, hence on
-- `Frac(R / q) = κ(q)` over `Frac((R^G) / p) = κ(p)`. The invariant-theory surjectivity theorem for
-- stabilizers then gives every automorphism of `κ(q) / κ(p)`.
/- Lemma 15.111.9 (2): the decomposition group
`D = {σ ∈ G | σ(q) = q}` surjects onto `Aut(κ(q) / κ(p))`. In this fixed-subring setting, this is
exactly the canonical invariant-theory owner theorem
`IsFractionRing.stabilizerHom_surjective`, specialized to `A = R^G`, `B = R`, `P = p`, and
`Q = q`. -/
#check (IsFractionRing.stabilizerHom_surjective G p q κp κq :
  Function.Surjective (IsFractionRing.stabilizerHom G p q κp κq))

end

/-! ### Lemma_15_111_10 (from Chap15) -/
open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [IsGalois K L]

local notation "B" => integralClosure A L

/- Domain-style sampling for Lemma 15.111.10:
- primary domain: Galois actions on the integral closure of an integrally closed domain and the
  induced decomposition-group action on residue fields
- sampled owner declarations:
  `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `Algebra.isInvariant_of_isGalois`,
  `IsFractionRing.stabilizerHom`,
  `FixedPoints.toAlgAut_surjective`
- best owner abstraction: the invariant-extension owner
  `Algebra.IsInvariant A (integralClosure A L) Gal(L/K)` together with the residue-field owner
  `IsFractionRing.stabilizerHom`
- primitive data: `B = integralClosure A L`, a prime `p : Ideal A`, and primes of `B` lying over
  `p`
- derived API: transitivity on primes above `p`, normality of the residue-field extension, and the
  decomposition-group action on `Aut(κ(q) / κ(p))`

Layer triage:
- `source-facing`: the three textbook clauses for `B = integralClosure A L`
- `core/canonical`: `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `IsFractionRing.stabilizerHom`, and the profinite/fixed-field surjectivity owner behind the
  induced residue-field action
- `bridge/view`: the quotient-to-residue-field algebra and scalar-tower instances identifying the
  integral-closure situation with those owner theorems

The decomposition-group homomorphism itself is an exact owner specialization, so the refined file
should reuse that directly rather than keep a parallel local definition. Clauses `(1)` and `(3)`
remain source-facing theorems because the finite-group owner theorems in mathlib live under
stronger assumptions than the current statement header.
-/

/-- The Galois group `Gal(L / K)` acts on `B = integralClosure A L`. -/
private local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass Gal(L/K) A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B Gal(L/K) := sorry

attribute [local instance] integralClosure_isInvariant

variable (p : Ideal A) [p.IsPrime]
variable (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver p]

local notation "κp" => p.ResidueField
local notation "κq" => q.ResidueField

-- The canonical map `(A ⧸ p) → κ(q)` agrees with the composite `(A ⧸ p) → B ⧸ q → κ(q)`.
-- Proof sketch: both maps are induced by the same ring map `A → integralClosure A L`; compare them
-- on quotient classes represented by elements of `A`.
private theorem integralClosureResidueFieldMap_comp_quotient :
    (Ideal.ResidueField.map p q (algebraMap A B) (Ideal.over_def q p)).comp
        (algebraMap (A ⧸ p) κp) =
      (algebraMap (B ⧸ q) κq).comp (algebraMap (A ⧸ p) (B ⧸ q)) := sorry

/-- The residue field `κ(q)` is an `(A ⧸ p)`-algebra via the composite
`(A ⧸ p) → κ(p) → κ(q)`. -/
private noncomputable instance integralClosureQuotientResidueFieldAlgebra :
    Algebra (A ⧸ p) κq :=
  ((Ideal.ResidueField.map p q (algebraMap A B) (Ideal.over_def q p)).comp
    (algebraMap (A ⧸ p) κp)).toAlgebra

/-- The canonical maps `(A ⧸ p) → κ(p) → κ(q)` form a scalar tower. -/
private noncomputable instance integralClosureResidueField_isScalarTower :
    IsScalarTower (A ⧸ p) κp κq :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical maps `(A ⧸ p) → (integralClosure A L) ⧸ q → κ(q)` form a scalar tower. -/
private noncomputable instance integralClosureQuotientResidueField_isScalarTower :
    IsScalarTower (A ⧸ p) (B ⧸ q) κq :=
  IsScalarTower.of_algebraMap_eq' (integralClosureResidueFieldMap_comp_quotient p q)

variable (q' : Ideal (integralClosure A L)) [q'.IsPrime] [q'.LiesOver p]

-- Proof sketch: apply the profinite invariant-theory transitivity theorem to the invariant
-- extension `A ⊆ integralClosure A L`; the hypotheses that `q` and `q'` both lie over `p`
-- identify their contractions to `A`.
/- Lemma 15.111.10 (1): if two prime ideals of the integral closure `B = integralClosure A L`
lie over the same prime ideal `p` of `A`, then some `σ ∈ Gal(L / K)` sends one to the other.
The finite-group owner theorem `Algebra.IsInvariant.exists_smul_of_under_eq` is not used as the
main entry here because the current statement header is broader. -/
theorem exists_gal_smul_eq_of_liesOver
    (p : Ideal A) (q q' : Ideal B)
    [p.IsPrime] [q.IsPrime] [q'.IsPrime] [q.LiesOver p] [q'.LiesOver p] :
    ∃ σ : Gal(L/K), σ • q = q' := sorry

-- Proof sketch: apply the residue-field normality statement for invariant extensions to the
-- invariant extension `A ⊆ integralClosure A L` and the prime `q` above `p`.
/-- Lemma 15.111.10 (2): if `q` is a prime of `B = integralClosure A L` lying over the prime
`p` of `A`, then the residue field extension `κ(q) / κ(p)` is normal. -/
theorem residueField_normal_of_liesOver :
    Normal κp κq := sorry

-- Proof sketch: use the profinite invariant-theory surjectivity theorem for the stabilizer of
-- `q`, then identify the resulting map on fraction fields with the canonical owner map from the
-- decomposition group to `Aut(κ(q) / κ(p))`.
/- Lemma 15.111.10 (3): if `q` is a prime of `B = integralClosure A L` lying over the prime
`p` of `A`, then the decomposition group of `q` surjects onto `Aut(κ(q) / κ(p))`. The public
surface should stay source-facing at this generality; the finite theorem
`IsFractionRing.stabilizerHom_surjective` is only a stronger companion specialization. -/
theorem stabilizerHom_surjective_of_liesOver :
    Function.Surjective (IsFractionRing.stabilizerHom Gal(L/K) p q κp κq) := by
  sorry

end

/-! ### Lemma_15_111_11 (from Chap15) -/
open scoped Pointwise
open AlgEquiv

universe u v w

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
variable {M : Type w} [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M] [IsGalois K M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M

/- Domain-style sampling for Lemma 15.111.11:
- primary domain: decomposition and inertia groups in a tower of integral closures under Galois
  restriction
- sampled owner declarations:
  `MulAction.stabilizer`,
  `Ideal.inertia`,
  `Ideal.under`,
  `AlgEquiv.restrictNormalHom`,
  `IsIntegralClosure.MulSemiringAction`
- best owner abstraction: the canonical subgroup owners `MulAction.stabilizer G I` and `I.inertia G`
  together with the restriction homomorphism `restrictNormalHom`
- primitive data: the canonical `B`-algebra structure on `C` induced by `L ⊆ M` and a prime ideal
  `r : Ideal C`
- derived API: the image equalities for the decomposition and inertia groups of the contracted
  prime `r.under B`

Layer triage:
- `source-facing`: the two image-equality statements in the tower
- `core/canonical`: `MulAction.stabilizer`, `Ideal.inertia`, and `restrictNormalHom`
- `bridge/view`: contraction of `r` to `B`, canonically expressed as `r.under B`

The file should keep the source-facing statements, but state them directly in terms of those owner
declarations instead of repeating the integral-closure map inline or using a parallel inertia
surface. -/

private noncomputable local instance : Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

/-- The canonical `Gal(M / K)`-action on the integral closure `C` of `A` in `M`. -/
private local instance integralClosureMulSemiringAction_top :
    MulSemiringAction Gal(M/K) C :=
  IsIntegralClosure.MulSemiringAction A K M C

/-- The canonical `Gal(L / K)`-action on the integral closure `B` of `A` in `L`. -/
private local instance integralClosureMulSemiringAction_base :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

-- Proof sketch: for `σ ∈ Gal(L / K)`, lift `σ` to some `τ ∈ Gal(M / K)` by surjectivity of
-- `restrictNormalHom`. Then `τ • r` and `r` contract to the same prime of `B`, so
-- Lemma `15.111.10` produces an element of `Gal(M / L)` carrying `τ • r` back to `r`. Composing
-- with `τ` yields an element of the decomposition group of `r` restricting to `σ`.
/-- Lemma 15.111.11 (1): if `q = B ∩ r` is the contraction of a prime `r ⊂ C`, then under the
restriction map `Gal(M / K) → Gal(L / K)` the image of the decomposition group of `r` is the
decomposition group of `q`. -/
theorem restrictNormalHom_image_decompositionGroup_eq
    (r : Ideal C) [r.IsPrime]
    :
    Subgroup.map (restrictNormalHom L)
      (MulAction.stabilizer Gal(M / K) r) =
    MulAction.stabilizer Gal(L / K) (r.under B) := sorry

-- Proof sketch: use the same lifting argument as in clause `(1)`, but now compare the induced
-- actions on the residue fields. Lemma `15.111.10` gives surjectivity from the decomposition group
-- onto residue-field automorphisms, so the lift may be adjusted by an element of `Gal(M / L)`
-- acting trivially on the residue field at `r`, placing the adjusted lift in the inertia group.
/-- Lemma 15.111.11 (2): if `q = B ∩ r` is the contraction of a prime `r ⊂ C`, then under the
restriction map `Gal(M / K) → Gal(L / K)` the image of the inertia group of `r` is the inertia
group of `q`. -/
theorem restrictNormalHom_image_inertiaGroup_eq
    (r : Ideal C) [r.IsPrime]
    :
    Subgroup.map (restrictNormalHom L)
      (r.inertia Gal(M / K)) =
    (r.under B).inertia Gal(L / K) := sorry

end
