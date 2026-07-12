import Mathlib
import StacksProject_2024.Chap10.Definition_10_32_1
import StacksProject_2024.Chap15.Lemma_15_111_2

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
      Ideal.map (FixedPoints.subring R G).subtype J := by
  -- The action on ideals is induced by the corresponding ring endomorphism of `R`.
  rw [Ideal.pointwise_smul_def, Ideal.map_map]
  -- Fixed elements are unchanged by every group element, so the composed map is just the subtype.
  have hcomp :
      (MulSemiringAction.toRingHom G R g).comp (FixedPoints.subring R G).subtype =
        (FixedPoints.subring R G).subtype := by
    ext a
    exact a.2 g
  simpa [hcomp]

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
variable (J : Ideal (FixedPoints.subring R G))

local notation "RFix" => FixedPoints.subring R G

local notation "JR" => fixedSubringIdealExtension J
local instance : MulSemiringAction G (R ⧸ JR) :=
  fixedSubringIdealMapQuotientMulSemiringAction J
local notation "QuotFix" => fixedSubringFixedQuotient J

/-- Helper for Lemma 15.111.4: the quotient map `R → R / JR` is equivariant for the induced
quotient action. -/
private theorem fixedSubringIdealExtension_quotientMk_map_smul
    (g : G) (x : R) :
    Ideal.Quotient.mk JR (g • x) =
      g • Ideal.Quotient.mk JR x := by
  -- The quotient action was defined so that the quotient map is equivariant.
  rfl

/-- Helper for Lemma 15.111.4: the quotient map `R → R / JR` as an equivariant ring homomorphism. -/
private def fixedSubringIdealExtension_quotientMkMulSemiringActionHom :
    R →+*[G] R ⧸ JR :=
  { toRingHom := Ideal.Quotient.mk JR
    map_smul' := fixedSubringIdealExtension_quotientMk_map_smul (R := R) (G := G) (J := J) }

/-- Helper for Lemma 15.111.4: composing the source-facing map with the quotient projection
`R^G → (R^G)/J` recovers the fixed-points map induced by `R → R / JR`. -/
private theorem fixedSubringQuotientToFixedQuotient_comp_mk
    [Finite G] :
    (fixedSubringQuotientToFixedQuotient J).comp (Ideal.Quotient.mk J) =
      (fixedSubringIdealExtension_quotientMkMulSemiringActionHom
        (R := R) (G := G) (J := J)).fixedPoints := by
  -- Route correction: expose the owner map from Lemma `15.111.2` and use its composition rule.
  rw [fixedSubringQuotientToFixedQuotient, RingHom.comp_assoc, Ideal.quotientMap_comp_mk]
  simpa [fixedSubringIdealExtension_quotientMkMulSemiringActionHom] using
    (fixedPointsQuotientToQuotientFixedPoints_comp_mk
      (R := R) (G := G) (I := JR)
      (hI := smul_fixedSubringIdeal_map (R := R) (G := G) J))

/-- Helper for Lemma 15.111.4: on a fixed representative, the source-facing map is the usual
quotient map into `R / JR`. -/
@[simp] private theorem fixedSubringQuotientToFixedQuotient_mk
    [Finite G]
    (x : RFix) :
    ((fixedSubringQuotientToFixedQuotient J (Ideal.Quotient.mk J x)) : R ⧸ JR) =
      Ideal.Quotient.mk JR x := by
  -- This is the owner computation rule specialized to the ideal `JR`.
  change
    (((fixedPointsQuotientToQuotientFixedPoints JR
        (smul_fixedSubringIdeal_map (R := R) (G := G) J))
          (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype JR) x)) : R ⧸ JR) =
      Ideal.Quotient.mk JR x
  simpa using
    (fixedPointsQuotientToQuotientFixedPoints_mk
      (R := R) (G := G) (I := JR)
      (hI := smul_fixedSubringIdeal_map (R := R) (G := G) J) x)

-- Proof sketch: apply Lemma `15.111.1` to the equivariant quotient map `R → R/JR`, using the
-- induced fixed quotient subring as codomain. The orbit polynomial obtained there descends to a
-- monic polynomial over `(R^G)/J`.
/-- Lemma 15.111.4: for every fixed class `b ∈ (R/JR)^G`, there is a monic polynomial over
`(R^G)/J` whose image in `(R/JR)^G[T]` is `(X - C b)^|G|`. -/
theorem exists_monic_polynomial_over_fixedSubringQuotient_map_eq_X_sub_C_pow
    [Finite G]
    (b : QuotFix) :
    ∃ P : Polynomial (RFix ⧸ J),
      P.Monic ∧
        P.map (fixedSubringQuotientToFixedQuotient J) = (X - C b) ^ Nat.card G := by
  -- Apply Lemma `15.111.1` to the equivariant quotient map `R → R / JR`.
  obtain ⟨Q, hQmonic, hQmap⟩ :=
    exists_monic_polynomial_over_fixedPoints_map_eq_X_sub_C_pow
      (fixedSubringIdealExtension_quotientMkMulSemiringActionHom
        (R := R) (G := G) (J := J))
      (Ideal.Quotient.mk_surjective (I := JR)) b
  refine ⟨Polynomial.map (Ideal.Quotient.mk J) Q, hQmonic.map _, ?_⟩
  -- Descend the orbit polynomial from `R^G` to `(R^G)/J`.
  calc
    Polynomial.map (fixedSubringQuotientToFixedQuotient J)
        (Polynomial.map (Ideal.Quotient.mk J) Q) =
      Polynomial.map
        ((fixedSubringQuotientToFixedQuotient J).comp (Ideal.Quotient.mk J)) Q := by
          rw [Polynomial.map_map]
    _ = Polynomial.map
        ((fixedSubringIdealExtension_quotientMkMulSemiringActionHom
          (R := R) (G := G) (J := J)).fixedPoints) Q := by
          rw [fixedSubringQuotientToFixedQuotient_comp_mk]
    _ = (X - C b) ^ Nat.card G := hQmap

/-- Helper for Lemma 15.111.4: if `x ∈ JR`, then each nonleading fixed coefficient of the orbit
polynomial of `x` already belongs to `J`. -/
private theorem coeff_charpoly_mem_fixedSubringIdeal_of_mem_fixedSubringIdealExtension
    [Fintype G] {x : R}
    (hx : x ∈ JR) (i : Fin (Fintype.card G)) :
    ⟨(MulSemiringAction.charpoly G x).coeff i,
      fun g ↦ MulSemiringAction.smul_coeff_charpoly x i g⟩ ∈ J := by
  sorry

/-- Helper for Lemma 15.111.4: if a fixed representative lies in `JR`, then every nonleading
coefficient of `(X - C x)^|G|` lies in `J`. -/
private theorem coeff_X_sub_C_pow_mem_fixedSubringIdeal
    [Fintype G] {x : RFix}
    (hx : (x : R) ∈ JR) (i : Fin (Fintype.card G)) :
    ((X - C x) ^ Fintype.card G).coeff i ∈ J := by
  -- Compare `(X - C x)^|G|` with the orbit polynomial in `R[X]`.
  have hchar :
      Polynomial.map (FixedPoints.subring R G).subtype ((X - C x) ^ Fintype.card G) =
        MulSemiringAction.charpoly G (x : R) := by
    calc
      Polynomial.map (FixedPoints.subring R G).subtype ((X - C x) ^ Fintype.card G) =
          (X - C ((x : R))) ^ Fintype.card G := by
            simp
      _ = ∏ _ : G, (X - C ((x : R))) := by
            simp
      _ = ∏ g : G, (X - C (g • (x : R))) := by
            refine Finset.prod_congr rfl ?_
            intro g _
            simp [x.2 g]
      _ = MulSemiringAction.charpoly G (x : R) := by
            rw [MulSemiringAction.charpoly_eq]
  have hcoeff_eq :
      ((X - C x) ^ Fintype.card G).coeff i =
        ⟨(MulSemiringAction.charpoly G (x : R)).coeff i,
          fun g ↦ MulSemiringAction.smul_coeff_charpoly (G := G) (x : R) i g⟩ := by
    apply Subtype.ext
    -- Taking coefficients transports the orbit-polynomial identity back to `R^G`.
    change (FixedPoints.subring R G).subtype (((X - C x) ^ Fintype.card G).coeff i) =
      (MulSemiringAction.charpoly G (x : R)).coeff i
    have hcoeff := congrArg (fun p : Polynomial R => p.coeff (i : ℕ)) hchar
    simpa only [Polynomial.coeff_map] using hcoeff
  -- Lemma `15.111.3` identifies these lower coefficients as elements of `J`.
  simpa [hcoeff_eq] using
    coeff_charpoly_mem_fixedSubringIdeal_of_mem_fixedSubringIdealExtension
      (R := R) (G := G) J hx i

/-- Helper for Lemma 15.111.4: if a fixed representative lies in `JR`, then `(X - C x)^|G|`
is distinguished at `J`. -/
private theorem X_sub_C_pow_isDistinguishedAt_of_mem_fixedSubringIdeal
    [Fintype G] [Nontrivial RFix] {x : RFix}
    (hx : (x : R) ∈ JR) :
    ((X - C x) ^ Fintype.card G).IsDistinguishedAt J := by
  refine ⟨?_, by simpa using (monic_X_sub_C x).pow (Fintype.card G)⟩
  rw [Polynomial.isWeaklyEisensteinAt_iff]
  have hnatDegree :
      ((X - C x) ^ Fintype.card G).natDegree = Fintype.card G := by
    rw [(monic_X_sub_C x).natDegree_pow, natDegree_X_sub_C, mul_one]
  intro n hn
  have hn' : n < Fintype.card G := by
    exact hnatDegree ▸ hn
  simpa using
    coeff_X_sub_C_pow_mem_fixedSubringIdeal
      (R := R) (G := G) (J := J) hx ⟨n, hn'⟩

/-- Helper for Lemma 15.111.4: a representative of a kernel class already lies in the extended
ideal `JR`. -/
private theorem fixedSubringQuotient_kernel_lift_mem_fixedSubringIdeal
    [Finite G]
    {a : RingHom.ker (fixedSubringQuotientToFixedQuotient J)} {x : RFix}
    (hx : Ideal.Quotient.mk J x = a.1) :
    (x : R) ∈ JR := by
  -- Translate the kernel equation to vanishing in `R / JR`.
  have ha_zero : fixedSubringQuotientToFixedQuotient J a.1 = 0 := by
    exact a.2
  have hx_zero :
      ((fixedSubringQuotientToFixedQuotient J (Ideal.Quotient.mk J x)) : R ⧸ JR) = 0 := by
    rw [hx]
    exact congrArg (fun z : QuotFix => (z : R ⧸ JR)) ha_zero
  -- The specialized computation rule identifies this with the usual quotient map.
  rw [fixedSubringQuotientToFixedQuotient_mk] at hx_zero
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx_zero

/-- Helper for Lemma 15.111.4: the source-facing map satisfies the Chapter 10 shift-power
generation hypothesis. -/
private theorem fixedSubringQuotientToFixedQuotient_shiftPowerPolynomialImageGenerating
    [Finite G] :
    (fixedSubringQuotientToFixedQuotient J).ShiftPowerPolynomialImageGenerating := by
  let f := fixedSubringQuotientToFixedQuotient J
  let _ : Algebra (RFix ⧸ J) QuotFix := f.toAlgebra
  -- Every fixed class in `(R / JR)^G` already satisfies the required shift-power relation.
  apply top_unique
  intro b _
  obtain ⟨P, -, hPmap⟩ :=
    exists_monic_polynomial_over_fixedSubringQuotient_map_eq_X_sub_C_pow
      (R := R) (G := G) (J := J) b
  exact Algebra.subset_adjoin ⟨Nat.card G, Nat.card_pos, P, hPmap⟩

-- Proof sketch: lift a kernel element to an invariant element of `JR`; then Lemma `15.111.3`
-- shows that every nonleading coefficient of its orbit polynomial dies modulo `J`, so the orbit
-- polynomial becomes `X^|G|`.
/-- A kernel element of `(R^G)/J → (R/JR)^G` satisfies `(X - C a)^|G| = X^|G|`. -/
theorem kernelElement_X_sub_pow_eq_X_pow
    [Finite G]
    (a : RingHom.ker (fixedSubringQuotientToFixedQuotient J)) :
    (X - C a.1) ^ Nat.card G = X ^ Nat.card G := by
  classical
  cases nonempty_fintype G
  rcases subsingleton_or_nontrivial RFix with hsub | hnontriv
  · letI : Subsingleton RFix := hsub
    letI : Subsingleton (RFix ⧸ J) := by infer_instance
    letI : Subsingleton (Polynomial (RFix ⧸ J)) := by infer_instance
    exact Subsingleton.elim _ _
  letI : Nontrivial RFix := hnontriv
  obtain ⟨x, hx_eq⟩ := Ideal.Quotient.mk_surjective a.1
  -- Read the kernel condition on the chosen representative inside `R / JR`.
  have hx : (x : R) ∈ JR :=
    fixedSubringQuotient_kernel_lift_mem_fixedSubringIdeal
      (R := R) (G := G) (J := J) hx_eq
  have hdist :
      ((X - C x) ^ Fintype.card G).IsDistinguishedAt J :=
    X_sub_C_pow_isDistinguishedAt_of_mem_fixedSubringIdeal
      (R := R) (G := G) (J := J) hx
  -- The distinguished-polynomial criterion collapses the image modulo `J` to `X^|G|`.
  have hmap :
      Polynomial.map (Ideal.Quotient.mk J) ((X - C x) ^ Fintype.card G) =
        X ^ Fintype.card G := by
    have hmap' := Polynomial.IsDistinguishedAt.map_eq_X_pow hdist
    have hnatDegree :
        ((X - C x) ^ Fintype.card G).natDegree = Fintype.card G := by
      rw [(monic_X_sub_C x).natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [hnatDegree] at hmap'
    exact hmap'
  calc
    (X - C a.1) ^ Nat.card G = (X - C (Ideal.Quotient.mk J x)) ^ Fintype.card G := by
      rw [← hx_eq, Nat.card_eq_fintype_card]
    _ = X ^ Fintype.card G := by
      simpa using hmap
    _ = X ^ Nat.card G := by
      rw [Nat.card_eq_fintype_card]

-- Proof sketch: the kernel identity above makes the kernel locally nilpotent, which is the
-- remaining source-facing input for the Chapter 10 shift-power criterion.
/-- The kernel of `(R^G)/J → (R/JR)^G` is locally nilpotent. -/
theorem fixedSubringQuotientToFixedQuotient_ker_isLocallyNilpotent
    [Finite G]
    :
    (RingHom.ker (fixedSubringQuotientToFixedQuotient J)).IsLocallyNilpotent := by
  rw [Ideal.isLocallyNilpotent_iff]
  intro a ha
  have hpow :=
    kernelElement_X_sub_pow_eq_X_pow (R := R) (G := G) (J := J) ⟨a, ha⟩
  -- Evaluate at `0` to read off a nilpotent power of the kernel element.
  have heval := congrArg (fun p : Polynomial (RFix ⧸ J) => p.eval 0) hpow
  have hneg_nil : IsNilpotent (-a) := by
    have hneg_pow : (-a) ^ Nat.card G = 0 ^ Nat.card G := by
      simpa [sub_eq_add_neg] using heval
    have hzero_pow : (0 : RFix ⧸ J) ^ Nat.card G = 0 := by
      exact zero_pow (Nat.card_pos.ne')
    exact ⟨Nat.card G, hneg_pow.trans hzero_pow⟩
  exact (isNilpotent_neg_iff.mp hneg_nil)

-- Proof sketch: combine the monic-polynomial statement and the locally nilpotent-kernel theorem
-- above with the canonical Chapter 10 criterion for shift-power generated maps.
/-- The canonical map `(R^G)/J → (R/JR)^G` is integral. -/
theorem fixedSubringQuotientToFixedQuotient_isIntegral
    [Finite G]
    :
    (fixedSubringQuotientToFixedQuotient J).IsIntegral := by
  -- The Chapter 10 criterion only needs the shift-power generation established above.
  exact RingHom.isIntegral_of_shiftPowerPolynomialImageGenerating
    (fixedSubringQuotientToFixedQuotient J)
    (fixedSubringQuotientToFixedQuotient_shiftPowerPolynomialImageGenerating
      (R := R) (G := G) (J := J))

-- Proof sketch: the same Chapter 10 criterion identifies the induced map on spectra as a
-- homeomorphism.
/-- The induced map `Spec((R/JR)^G) → Spec((R^G)/J)` is a homeomorphism. -/
theorem fixedSubringQuotientToFixedQuotient_isHomeomorph_comap
    [Finite G]
    :
    IsHomeomorph (PrimeSpectrum.comap (fixedSubringQuotientToFixedQuotient J)) := by
  let f := fixedSubringQuotientToFixedQuotient J
  have hgen : f.ShiftPowerPolynomialImageGenerating :=
    fixedSubringQuotientToFixedQuotient_shiftPowerPolynomialImageGenerating
      (R := R) (G := G) (J := J)
  have hker : (RingHom.ker f).IsLocallyNilpotent :=
    fixedSubringQuotientToFixedQuotient_ker_isLocallyNilpotent
      (R := R) (G := G) (J := J)
  -- Route correction: the spectrum statement comes from the Chapter 10 owner theorem once the
  -- shift-power generators and locally nilpotent kernel are available.
  exact PrimeSpectrum.isHomeomorph_comap f
    (RingHom.exists_pow_mem_range_of_shiftPowerPolynomialImageGenerating f hgen)
    (by simpa [Ideal.IsLocallyNilpotent] using hker)

-- Proof sketch: the residue-field clause is another consequence of the same shift-power
-- generation criterion applied to `(R^G)/J → (R/JR)^G`.
/-- The canonical map `(R^G)/J → (R/JR)^G` induces purely inseparable residue-field extensions. -/
theorem fixedSubringQuotientToFixedQuotient_hasPurelyInseparableResidueFieldExtensions
    [Finite G]
    :
    (fixedSubringQuotientToFixedQuotient J).HasPurelyInseparableResidueFieldExtensions := by
  -- This is the residue-field clause of the same Chapter 10 shift-power criterion.
  exact RingHom.hasPurelyInseparableResidueFieldExtensions_of_shiftPowerPolynomialImageGenerating
    (fixedSubringQuotientToFixedQuotient J)
    (fixedSubringQuotientToFixedQuotient_shiftPowerPolynomialImageGenerating
      (R := R) (G := G) (J := J))

end FixedIdealExtensionQuotient
