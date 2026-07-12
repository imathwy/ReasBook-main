import Mathlib
import StacksProject_2024.Chap10.Lemma_10_46_11
import StacksProject_2024.Chap15.Lemma_15_111_1

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Helper for Lemma 15.111.2: in the finite-group arguments, the quotient by a stable ideal
inherits the canonical induced action. -/
local instance quotientMulSemiringAction_finite
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    MulSemiringAction G (R ⧸ I) :=
  quotientMulSemiringAction I hI

/-- Helper for Lemma 15.111.2: the equivariant quotient map `R → R ⧸ I` is surjective. -/
theorem quotientMkMulSemiringActionHom_surjective
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    Function.Surjective (Ideal.Quotient.mk I) := by
  -- The underlying ring hom is definitionally the quotient map.
  simpa using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))

/-- Helper for Lemma 15.111.2: composing the fixed-points quotient map with the quotient projection
from `R^G` recovers the fixed-points map induced by `R → R ⧸ I`. -/
theorem fixedPointsQuotientToQuotientFixedPoints_comp_mk
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    letI := quotientMulSemiringAction I hI
    (fixedPointsQuotientToQuotientFixedPoints I hI).comp
        (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I)) =
      (quotientMkMulSemiringActionHom I hI).fixedPoints := by
  rfl

/-- Helper for Lemma 15.111.2: the canonical map
`R^G / (I ∩ R^G) → (R / I)^G` satisfies the shift-power generation hypothesis. -/
theorem fixedPointsQuotient_shiftPowerPolynomialImageGenerating
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    (fixedPointsQuotientToQuotientFixedPoints I hI).ShiftPowerPolynomialImageGenerating := by
  classical
  letI := quotientMulSemiringAction I hI
  let f := fixedPointsQuotientToQuotientFixedPoints I hI
  let _ : Algebra
      (RFix ⧸ Ideal.comap (FixedPoints.subring R G).subtype I)
      (FixedPoints.subring (R ⧸ I) G) := f.toAlgebra
  -- Every fixed class in `R ⧸ I` is one of the generators appearing in the Chapter 10 criterion.
  apply top_unique
  intro b _
  obtain ⟨Q, _, hQmap⟩ :=
    exists_monic_polynomial_over_fixedPoints_map_eq_X_sub_C_pow
      (quotientMkMulSemiringActionHom I hI)
      (quotientMkMulSemiringActionHom_surjective I hI) b
  refine Algebra.subset_adjoin ?_
  refine ⟨Nat.card G, Nat.card_pos, Polynomial.map
      (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I)) Q, ?_⟩
  -- Descend the orbit polynomial from `R^G` to the quotient of `R^G`.
  calc
    Polynomial.map f
        (Polynomial.map (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I)) Q) =
      Polynomial.map
        (f.comp
          (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I))) Q := by
        rw [Polynomial.map_map]
    _ = Polynomial.map ((quotientMkMulSemiringActionHom I hI).fixedPoints) Q := by
        rw [fixedPointsQuotientToQuotientFixedPoints_comp_mk]
    _ = (Polynomial.X - Polynomial.C b) ^ Nat.card G := by
        simpa using hQmap

/-- Helper for Lemma 15.111.2: the canonical map
`R^G / (I ∩ R^G) → (R / I)^G` has trivial kernel. -/
theorem fixedPointsQuotient_ker_eq_bot
    (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    RingHom.ker (fixedPointsQuotientToQuotientFixedPoints I hI) = ⊥ := by
  letI := quotientMulSemiringAction I hI
  -- Lift a kernel element to `R^G`, then translate vanishing in `R ⧸ I` back to membership in
  -- the defining ideal of the quotient.
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨y, rfl⟩ :=
    (Ideal.Quotient.mk_surjective x :
      ∃ y : FixedPoints.subring R G,
        Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I) y = x)
  change Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I) y = 0
  have hy_zero :
      ((fixedPointsQuotientToQuotientFixedPoints I hI
          (Ideal.Quotient.mk (Ideal.comap (FixedPoints.subring R G).subtype I) y)) : R ⧸ I) = 0 := by
    -- The kernel condition says the image is zero in the fixed subring of the quotient.
    exact congrArg (fun z : FixedPoints.subring (R ⧸ I) G => (z : R ⧸ I)) (by simpa using hx)
  rw [fixedPointsQuotientToQuotientFixedPoints_mk] at hy_zero
  refine eq_zero_iff_mem.mpr ?_
  simpa [Ideal.mem_comap] using (eq_zero_iff_mem.mp hy_zero)

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
  by
  let f := fixedPointsQuotientToQuotientFixedPoints I hI
  have hgen : f.ShiftPowerPolynomialImageGenerating :=
    fixedPointsQuotient_shiftPowerPolynomialImageGenerating I hI
  have hInt : f.IsIntegral :=
    RingHom.isIntegral_of_shiftPowerPolynomialImageGenerating f hgen
  have hKerLocNil : (RingHom.ker f).IsLocallyNilpotent := by
    rw [fixedPointsQuotient_ker_eq_bot I hI]
    simp [Ideal.IsLocallyNilpotent]
  have hHomeo : IsHomeomorph (comap f) := by
    -- The Chapter 10 owner theorem reduces the spectrum statement to positive powers in the
    -- image and local nilpotence of the kernel.
    exact PrimeSpectrum.isHomeomorph_comap f
      (RingHom.exists_pow_mem_range_of_shiftPowerPolynomialImageGenerating f hgen)
      (by simpa [Ideal.IsLocallyNilpotent] using hKerLocNil)
  have hResidue : f.HasPurelyInseparableResidueFieldExtensions :=
    RingHom.hasPurelyInseparableResidueFieldExtensions_of_shiftPowerPolynomialImageGenerating f hgen
  exact ⟨hInt, hHomeo, hResidue⟩

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
