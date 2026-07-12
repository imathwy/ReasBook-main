import DifferentialForms_Cartan_1970.VII.section29.«0004_Exercise_2».RecursiveCoefficientVariableBounds

open scoped BigOperators MvPowerSeries PowerSeries MvPowerSeries.WithPiTopology
open PowerSeries

universe u

section RecursiveImplicitSystemMajorant

variable {𝕜 : Type u} [CommRing 𝕜] [Norm 𝕜]
variable {n p : ℕ}

/-- The positive-degree norm profile of a `z`-series, regrouped by total `z`-degree and shifted
so that the total-degree `q + 1` slice becomes the coefficient of `X^(q + 1)`. Its coefficients
are the sums of the norms of the coefficients on each total-degree slice, which is the source-
faithful majorant datum needed to reuse the canonical one-variable owner
`PowerSeries.IsMajorantSeries`. -/
noncomputable def linearTailNormProfile (f : MvPowerSeries (Fin p) 𝕜) : ℝ⟦X⟧ :=
  PowerSeries.mk fun
    | 0 => 0
    | q + 1 =>
        Finset.sum (Finset.finAntidiagonal p (q + 1)) fun e ↦
          ‖MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) f‖

/-- The norm profile of a series in `(x, z)`, regrouped by total `x`-degree and total `z`-degree.
Its coefficient at `(a, b)` is the sum of the norms of the original coefficients whose total
`x`-degree is `a` and total `z`-degree is `b`, so the canonical two-variable owner
`MvPowerSeries.IsMajorantSeries` records the intended majorant inequality without allowing
cancellation inside a slice. -/
noncomputable def higherNormProfile (f : MvPowerSeries (Fin n ⊕ Fin p) 𝕜) : ℝ⟦X,Y⟧ :=
  fun d ↦
    Finset.sum ((Finset.finAntidiagonal n (d 0)).product (Finset.finAntidiagonal p (d 1)))
      fun e ↦
      ‖MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (Sum.elim e.1 e.2 : Fin n ⊕ Fin p → ℕ)) f‖

/-- The positive-degree tail of the geometric one-variable majorant attached to the parameters `M`
and `R`, with zero constant coefficient so that the canonical owner
`PowerSeries.IsMajorantSeries` applies to the linear-tail profile. -/
noncomputable def linearTailMajorantSeries (M R : NNReal) : NNReal⟦X⟧ :=
  PowerSeries.mk fun
    | 0 => 0
    | q + 1 => M * R⁻¹ ^ (q + 1)

/-- The quadratic two-variable majorant attached to the parameters `M` and `R`. -/
noncomputable def higherMajorantSeries (M R : NNReal) : NNReal⟦X,Y⟧ :=
  fun d ↦
    if 2 ≤ d 0 then
      M * R⁻¹ ^ (d 0 + d 1)
    else
      0

namespace RecursiveImplicitSystem

/-- Source-facing majorant data for the recursive system `(3)`: the constant term of each linear
coefficient series `Γᵢⱼ(z)` is bounded directly, the sum of the coefficient norms on each positive
total-`z`-degree slice is controlled by the canonical one-variable majorant owner from Section 27,
and the sum of the coefficient norms on each fixed total-`x`/total-`z` slice of the nonlinear
remainder is controlled by the canonical two-variable owner. -/
class IsMajorizedBy (S : RecursiveImplicitSystem 𝕜 n p) (M R : NNReal) : Prop where
  linearCoeff_constant_le (j i : Fin n) :
    ‖MvPowerSeries.constantCoeff (S.linearCoeff j i)‖ ≤ (M : ℝ)
  linearCoeff_tail_norm_isMajorantSeries (j i : Fin n) :
    PowerSeries.IsMajorantSeries
      (linearTailNormProfile (S.linearCoeff j i)) (linearTailMajorantSeries M R)
  higher_norm_isMajorantSeries (j : Fin n) :
    MvPowerSeries.IsMajorantSeries
      (higherNormProfile (S.higher j)) (higherMajorantSeries M R)

end RecursiveImplicitSystem

namespace FormalImplicitSolution

/-- A family of `NNReal`-coefficient series majorizes a family of formal series coefficientwise. -/
def IsMajorizedBy
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜)
    (Ξ : Fin n → MvPowerSeries (ParamIndex n p) NNReal) : Prop :=
  ∀ j d, ‖MvPowerSeries.coeff d (x j)‖ ≤ ((Ξ j) d : ℝ)

end FormalImplicitSolution

end RecursiveImplicitSystemMajorant

section ScalarQuadraticMajorant

variable {𝕜 : Type u} [CommRing 𝕜] [Norm 𝕜]
variable {n p : ℕ}

/-- The sum `Y₁ + ⋯ + Yₙ` of the parameter variables in the scalar quadratic majorant equation. -/
noncomputable def paramYSum : MvPowerSeries (ParamIndex n p) ℝ :=
  ∑ j : Fin n, MvPowerSeries.X (Sum.inl j)

/-- The sum `Z₁ + ⋯ + Zₚ` of the parameter variables in the scalar quadratic majorant equation. -/
noncomputable def paramZSum : MvPowerSeries (ParamIndex n p) ℝ :=
  ∑ k : Fin p, MvPowerSeries.X (Sum.inr k)

/-- Helper for Cartan section29 0004_Exercise_2: the cancelled nonlinear tail in the scalar
quadratic majorant operator. The subtraction of `1 + aX` removes the constant and linear pieces
from the geometric inverse, so only quadratic-and-higher powers remain. -/
noncomputable def scalarQuadraticTail
    (a : ℝ) (X : MvPowerSeries (ParamIndex n p) NNReal) :
    MvPowerSeries (ParamIndex n p) ℝ :=
  let Xr := MvPowerSeries.map NNReal.toRealHom X
  (1 - MvPowerSeries.C a * Xr)⁻¹ - 1 - MvPowerSeries.C a * Xr

/-- Helper for Cartan section29 0004_Exercise_2: at positive total degree, the cancelled scalar
tail is the finite sum of the quadratic-and-higher power contributions. The proof rewrites the
inverse as the geometric series and then discards all powers whose order is too large to
contribute to degree `d`. -/
private lemma coeff_scalarQuadraticTail_eq_sum_range
    (a : ℝ) {X : MvPowerSeries (ParamIndex n p) NNReal}
    (hX0 : MvPowerSeries.constantCoeff X = 0)
    (d : ParamIndex n p →₀ ℕ) (hd : 0 < paramDegree d) :
    MvPowerSeries.coeff d (scalarQuadraticTail (n := n) (p := p) a X) =
      (Finset.sum (Finset.range (paramDegree d - 1)) fun q =>
        MvPowerSeries.coeff d
          ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom X) ^ (q + 2))) := by
  let Xr := MvPowerSeries.map NNReal.toRealHom X
  let f : MvPowerSeries (ParamIndex n p) ℝ := MvPowerSeries.C a * Xr
  have hXr0 : MvPowerSeries.constantCoeff Xr = 0 := by
    simp [Xr, hX0, MvPowerSeries.constantCoeff_map]
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    simp [f, hXr0]
  have hgeom : (1 - f)⁻¹ = ∑' q : ℕ, f ^ q := by
    -- Rewrite the inverse by the convergent geometric series for a zero-constant-coefficient
    -- series.
    have hcc : MvPowerSeries.constantCoeff (1 - f) = (1 : ℝ) := by
      simp [hf0]
    calc
      (1 - f)⁻¹ = (1 - f)⁻¹ * ((1 - f) * ∑' q : ℕ, f ^ q) := by
        rw [MvPowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero
          (f := f) hf0, mul_one]
      _ = ((1 - f)⁻¹ * (1 - f)) * ∑' q : ℕ, f ^ q := by
        ac_rfl
      _ = (1 : MvPowerSeries (ParamIndex n p) ℝ) * ∑' q : ℕ, f ^ q := by
        rw [← MvPowerSeries.invOfUnit_eq' (φ := 1 - f) (u := 1) (by simpa using hcc),
          MvPowerSeries.invOfUnit_mul (φ := 1 - f) (u := 1) (by simpa using hcc)]
      _ = ∑' q : ℕ, f ^ q := by
        simp
  have hcoeffInv : MvPowerSeries.coeff d ((1 - f)⁻¹) =
      Finset.sum (Finset.range (paramDegree d + 1)) (fun q => MvPowerSeries.coeff d (f ^ q)) := by
    -- Only powers up to the total degree of `d` can contribute to the degree-`d` coefficient.
    have hcoeffTsum :
        MvPowerSeries.coeff d (∑' q : ℕ, f ^ q) = ∑' q : ℕ, MvPowerSeries.coeff d (f ^ q) := by
      simpa [MvPowerSeries.coeff_apply] using
        (tsum_apply (x := d)
          (MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hf0))
    rw [hgeom, hcoeffTsum]
    refine tsum_eq_sum ?_
    intro q hq
    apply MvPowerSeries.coeff_of_lt_order
    have hle : paramDegree d + 1 ≤ q := by
      exact Nat.not_lt.mp (fun hlt' => hq (Finset.mem_range.mpr hlt'))
    have hlt : paramDegree d < q := by
      omega
    have hlt' : ((paramDegree d : ℕ) : ℕ∞) < q := by
      exact_mod_cast hlt
    simpa [paramDegree_eq_degree] using
      (lt_of_lt_of_le hlt' (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero q hf0))
  have hd0 : d ≠ 0 := by
    intro hdz
    simpa [hdz, paramDegree] using hd.ne'
  have hcoeffOne : MvPowerSeries.coeff d (1 : MvPowerSeries (ParamIndex n p) ℝ) = 0 := by
    simp [MvPowerSeries.coeff_one, hd0]
  have hcoeffPow0 : MvPowerSeries.coeff d (f ^ 0) = 0 := by
    simpa using hcoeffOne
  have hcoeffPow1 : MvPowerSeries.coeff d (f ^ 1) = MvPowerSeries.coeff d f := by
    simp
  have hsum2 :
      Finset.sum (Finset.range 2) (fun q => MvPowerSeries.coeff d (f ^ q)) =
        MvPowerSeries.coeff d (f ^ 0) + MvPowerSeries.coeff d (f ^ 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp
  have hsumSplit :
      Finset.sum (Finset.range (paramDegree d + 1)) (fun q => MvPowerSeries.coeff d (f ^ q)) =
        Finset.sum (Finset.range 2) (fun q => MvPowerSeries.coeff d (f ^ q)) +
          Finset.sum (Finset.range (paramDegree d - 1))
            (fun q => MvPowerSeries.coeff d (f ^ (q + 2))) := by
    -- Split off the `q = 0` and `q = 1` terms, which are exactly the pieces cancelled in the
    -- definition of `scalarQuadraticTail`.
    have hsplit := Finset.sum_range_add (f := fun q ↦ MvPowerSeries.coeff d (f ^ q))
      2 (paramDegree d - 1)
    have hdeg : 2 + (paramDegree d - 1) = paramDegree d + 1 := by
      omega
    simpa [hdeg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsplit
  calc
    MvPowerSeries.coeff d (scalarQuadraticTail (n := n) (p := p) a X)
        = MvPowerSeries.coeff d ((1 - f)⁻¹) -
            MvPowerSeries.coeff d (1 : MvPowerSeries (ParamIndex n p) ℝ) -
            MvPowerSeries.coeff d f := by
              simp [scalarQuadraticTail, Xr, f, sub_eq_add_neg, add_comm, add_left_comm,
                add_assoc]
    _ = Finset.sum (Finset.range (paramDegree d + 1)) (fun q => MvPowerSeries.coeff d (f ^ q)) -
          MvPowerSeries.coeff d (1 : MvPowerSeries (ParamIndex n p) ℝ) -
          MvPowerSeries.coeff d f := by
            rw [hcoeffInv]
    _ = (Finset.sum (Finset.range 2) (fun q => MvPowerSeries.coeff d (f ^ q)) +
            Finset.sum (Finset.range (paramDegree d - 1))
              (fun q => MvPowerSeries.coeff d (f ^ (q + 2)))) -
          MvPowerSeries.coeff d (1 : MvPowerSeries (ParamIndex n p) ℝ) -
          MvPowerSeries.coeff d f := by
            rw [hsumSplit]
    _ = Finset.sum (Finset.range (paramDegree d - 1))
          (fun q => MvPowerSeries.coeff d (f ^ (q + 2))) := by
            rw [hsum2, hcoeffPow0, hcoeffPow1, hcoeffOne]
            ring

/-- Helper for Cartan section29 0004_Exercise_2: once the cancelled scalar tail is read at total
degree `e`, only the power terms with exponents `qx ∈ [2, paramDegree e]` can contribute, so the
same coefficient is unchanged after enlarging the owner sum to any higher cutoff
`paramDegree d`. -/
lemma coeffScalarQuadraticTail_eq_sum_IccWithin
    (a : ℝ)
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (hA0 : MvPowerSeries.constantCoeff A = 0)
    (d : ParamIndex n p →₀ ℕ)
    (e : ParamIndex n p →₀ ℕ)
    (hle : paramDegree e ≤ paramDegree d) :
    MvPowerSeries.coeff e (scalarQuadraticTail (n := n) (p := p) a A) =
      MvPowerSeries.coeff e
        (Finset.sum (Finset.Icc 2 (paramDegree d)) fun qx =>
          ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ qx)) := by
  let scaled : MvPowerSeries (ParamIndex n p) ℝ :=
    MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A
  have hscaled0 : MvPowerSeries.constantCoeff scaled = 0 := by
    simp [scaled, MvPowerSeries.constantCoeff_map, hA0]
  by_cases he0 : paramDegree e = 0
  · have hez : e = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) e).mp he0
    subst hez
    -- At total degree `0`, both the cancelled tail and every quadratic-or-higher power vanish.
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [scalarQuadraticTail, scaled, MvPowerSeries.constantCoeff_map, hA0]
    symm
    refine Finset.sum_eq_zero ?_
    intro qx hqx
    have hqxge : 2 ≤ qx := (Finset.mem_Icc.mp hqx).1
    have hqxne : qx ≠ 0 := by
      omega
    simp [hqxne]
  · have hepos : 0 < paramDegree e := Nat.pos_iff_ne_zero.mpr he0
    have hIccEqRange :
        Finset.sum (Finset.Icc 2 (paramDegree e))
            (fun qx => MvPowerSeries.coeff e (scaled ^ qx)) =
          Finset.sum (Finset.range (paramDegree e - 1))
            (fun q => MvPowerSeries.coeff e (scaled ^ (q + 2))) := by
      -- Reindex the owner sum by the shift `q ↦ q + 2`.
      rw [show Finset.Icc 2 (paramDegree e) =
          (Finset.range (paramDegree e - 1)).image (fun q => q + 2) by
            ext qx
            simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
            constructor
            · intro hqx
              refine ⟨qx - 2, ?_, by omega⟩
              omega
            · rintro ⟨q, hq, rfl⟩
              omega]
      simp
    have hIccExtend :
        Finset.sum (Finset.Icc 2 (paramDegree e))
            (fun qx => MvPowerSeries.coeff e (scaled ^ qx)) =
          Finset.sum (Finset.Icc 2 (paramDegree d))
            (fun qx => MvPowerSeries.coeff e (scaled ^ qx)) := by
      -- Terms past total degree `paramDegree e` have vanishing degree-`e` coefficient.
      refine Finset.sum_subset ?_ ?_
      · intro qx hqx
        simp only [Finset.mem_Icc] at hqx ⊢
        omega
      · intro qx hqx hnotmem
        have hqxge : 2 ≤ qx := (Finset.mem_Icc.mp hqx).1
        have hlt : paramDegree e < qx := by
          simp only [Finset.mem_Icc, hqxge, true_and] at hnotmem
          omega
        apply MvPowerSeries.coeff_of_lt_order
        have hlt' : ((paramDegree e : ℕ) : ℕ∞) < qx := by
          exact_mod_cast hlt
        simpa [scaled, paramDegree_eq_degree] using
          (lt_of_lt_of_le hlt'
            (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero qx hscaled0))
    -- The positive-degree tail is already the finite quadratic range sum, and enlarging the
    -- owner cutoff only adds zero-contributing terms.
    calc
      MvPowerSeries.coeff e (scalarQuadraticTail (n := n) (p := p) a A) =
          Finset.sum (Finset.range (paramDegree e - 1))
            (fun q => MvPowerSeries.coeff e (scaled ^ (q + 2))) := by
              simpa [scaled] using
                coeff_scalarQuadraticTail_eq_sum_range (n := n) (p := p) a hA0 e hepos
      _ = Finset.sum (Finset.Icc 2 (paramDegree e))
            (fun qx => MvPowerSeries.coeff e (scaled ^ qx)) := hIccEqRange.symm
      _ = Finset.sum (Finset.Icc 2 (paramDegree d))
            (fun qx => MvPowerSeries.coeff e (scaled ^ qx)) := hIccExtend
      _ = MvPowerSeries.coeff e
            (Finset.sum (Finset.Icc 2 (paramDegree d)) fun qx => scaled ^ qx) := by
              simp

/-- Helper for Cartan section29 0004_Exercise_2: the positive-degree coefficient of the cancelled
scalar tail depends only on lower-degree coefficients of the input series. After reducing to the
finite quadratic power sum, each summand is stable under lower-degree coefficient agreement by the
existing cutoff power-comparison lemma. -/
private lemma scalarQuadraticTail_coeff_eq_of_lowerCoeffEq
    (a : ℝ)
    {X Y : MvPowerSeries (ParamIndex n p) NNReal}
    (hX0 : MvPowerSeries.constantCoeff X = 0)
    (hY0 : MvPowerSeries.constantCoeff Y = 0)
    (d : ParamIndex n p →₀ ℕ) (hd : 0 < paramDegree d)
    (hXY : ∀ d', paramDegree d' < paramDegree d →
      MvPowerSeries.coeff d' X = MvPowerSeries.coeff d' Y) :
    MvPowerSeries.coeff d (scalarQuadraticTail (n := n) (p := p) a X) =
      MvPowerSeries.coeff d (scalarQuadraticTail (n := n) (p := p) a Y) := by
  rw [coeff_scalarQuadraticTail_eq_sum_range (n := n) (p := p) a hX0 d hd,
    coeff_scalarQuadraticTail_eq_sum_range (n := n) (p := p) a hY0 d hd]
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hEqScaled :
      ∀ e, paramDegree e < paramDegree d →
        MvPowerSeries.coeff e (MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom X) =
          MvPowerSeries.coeff e (MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom Y) := by
    intro e he
    simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map, hXY e he]
  -- Compare the surviving quadratic-and-higher power terms coefficientwise.
  exact coeff_pow_eq_of_coeff_eq_below_paramDegree_of_two_le (n := n) (p := p)
    (N := paramDegree d) (q := q + 2)
    (by omega)
    (by simp [MvPowerSeries.constantCoeff_map, hX0])
    (by simp [MvPowerSeries.constantCoeff_map, hY0])
    hEqScaled d rfl

/-- Helper for Cartan section29 0004_Exercise_2: the exact inner factor of the scalar majorant
operator, named once so later coefficient arguments do not have to keep re-associating the raw
sum `paramYSum + ((1 - aX)⁻¹ - 1 - aX)`. -/
noncomputable def scalarMajorantInner
    (a : ℝ) (X : MvPowerSeries (ParamIndex n p) NNReal) :
    MvPowerSeries (ParamIndex n p) ℝ :=
  paramYSum + scalarQuadraticTail (n := n) (p := p) a X

/-- Helper for Cartan section29 0004_Exercise_2: once the scalar operator is rewritten through
`scalarMajorantInner`, only the cancelled tail still depends on the unknown series. This is the
owner-level bridge that replaces the previous unstable whole-operator normalization route. -/
private lemma coeff_scalarMajorantInner_eq_of_lowerCoeffEq
    (a : ℝ)
    {X Y : MvPowerSeries (ParamIndex n p) NNReal}
    (hX0 : MvPowerSeries.constantCoeff X = 0)
    (hY0 : MvPowerSeries.constantCoeff Y = 0)
    (d : ParamIndex n p →₀ ℕ) (hd : 0 < paramDegree d)
    (hXY : ∀ d', paramDegree d' < paramDegree d →
      MvPowerSeries.coeff d' X = MvPowerSeries.coeff d' Y) :
    MvPowerSeries.coeff d (scalarMajorantInner (n := n) (p := p) a X) =
      MvPowerSeries.coeff d (scalarMajorantInner (n := n) (p := p) a Y) := by
  -- `paramYSum` is independent of the unknown series, so only the cancelled tail needs transport.
  simp [scalarMajorantInner,
    scalarQuadraticTail_coeff_eq_of_lowerCoeffEq (n := n) (p := p) a hX0 hY0 d hd hXY]

/-- The scalar majorant operator obtained from the family majorant after the symmetric
specialization `X₁ = ⋯ = Xₙ = X`. -/
noncomputable def scalarMajorantOperator
    (M R : NNReal) (X : MvPowerSeries (ParamIndex n p) NNReal) :
    MvPowerSeries (ParamIndex n p) ℝ :=
  let Xr := MvPowerSeries.map NNReal.toRealHom X
  MvPowerSeries.C (M : ℝ) *
      (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum)⁻¹ *
    (paramYSum +
      (1 - MvPowerSeries.C (((n : ℕ) : ℝ) / (R : ℝ)) * Xr)⁻¹ -
      1 -
      MvPowerSeries.C (((n : ℕ) : ℝ) / (R : ℝ)) * Xr)

/-- Helper for Cartan section29 0004_Exercise_2: the scalar majorant operator is the fixed outer
parameter factor multiplied by the named inner owner. Writing it this way keeps later coefficient
proofs in one stable normal form. -/
lemma scalarMajorantOperator_eq_outer_mul_inner
    (M R : NNReal) (X : MvPowerSeries (ParamIndex n p) NNReal) :
    scalarMajorantOperator (n := n) (p := p) M R X =
      (MvPowerSeries.C (M : ℝ) *
          (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹) *
        scalarMajorantInner (n := n) (p := p) (((n : ℕ) : ℝ) / (R : ℝ)) X := by
  -- Repackage the operator through the named inner owner before doing coefficient transport.
  dsimp [scalarMajorantOperator, scalarMajorantInner, scalarQuadraticTail]
  congr 1
  abel

/-- Helper for Cartan section29 0004_Exercise_2: after freezing the inner owner, the whole scalar
majorant operator also has lower-degree coefficient transport. The fixed outer `z`-factor is
handled by one `coeff_mul` expansion, and every inner coefficient on the antidiagonal lies at
total degree at most the target degree. -/
private lemma scalarMajorantOperator_coeff_eq_of_lowerCoeffEq
    (M R : NNReal)
    {X Y : MvPowerSeries (ParamIndex n p) NNReal}
    (hX0 : MvPowerSeries.constantCoeff X = 0)
    (hY0 : MvPowerSeries.constantCoeff Y = 0)
    (d : ParamIndex n p →₀ ℕ)
    (hXY : ∀ d', paramDegree d' < paramDegree d →
      MvPowerSeries.coeff d' X = MvPowerSeries.coeff d' Y) :
    MvPowerSeries.coeff d (scalarMajorantOperator (n := n) (p := p) M R X) =
      MvPowerSeries.coeff d (scalarMajorantOperator (n := n) (p := p) M R Y) := by
  classical
  have hinner :
      ∀ e, paramDegree e ≤ paramDegree d →
        MvPowerSeries.coeff e
            (scalarMajorantInner (n := n) (p := p) (((n : ℕ) : ℝ) / (R : ℝ)) X) =
          MvPowerSeries.coeff e
            (scalarMajorantInner (n := n) (p := p) (((n : ℕ) : ℝ) / (R : ℝ)) Y) := by
    intro e he
    by_cases he0 : paramDegree e = 0
    · have hez : e = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) e).mp he0
      subst hez
      -- The inner owner has vanishing constant coefficient on both sides.
      simp [scalarMajorantInner, scalarQuadraticTail, paramYSum,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_map, hX0, hY0]
    · have hpos : 0 < paramDegree e := Nat.pos_iff_ne_zero.mpr he0
      exact coeff_scalarMajorantInner_eq_of_lowerCoeffEq (n := n) (p := p)
        (((n : ℕ) : ℝ) / (R : ℝ)) hX0 hY0 e hpos
        (fun e' he' => hXY e' (lt_of_lt_of_le he' he))
  -- Expand the fixed outer factor once; every antidiagonal branch only needs the inner transport.
  rw [scalarMajorantOperator_eq_outer_mul_inner (n := n) (p := p) M R X,
    scalarMajorantOperator_eq_outer_mul_inner (n := n) (p := p) M R Y]
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl ?_
  intro e he
  have hsum : e.1 + e.2 = d := Finset.mem_antidiagonal.mp he
  have hdeg :
      paramDegree e.1 + paramDegree e.2 = paramDegree d := by
    rw [← hsum]
    simp [paramDegree, Finset.sum_add_distrib]
  have hle : paramDegree e.2 ≤ paramDegree d := by
    omega
  congr 1
  exact hinner e.2 hle

/-- Helper for Cartan section29 0004_Exercise_2: the scalar stage recursion inserts exactly one
new total degree at each step, using `Real.toNNReal` on the scalar operator coefficient so the
`NNReal` stage object exists before any separate nonnegativity readback lemma is available. -/
noncomputable def scalarMajorantApproximant
    (M R : NNReal) : ℕ → MvPowerSeries (ParamIndex n p) NNReal
  | 0 => 0
  | N + 1 => fun d ↦
      if _ : paramDegree d = N + 1 then
        Real.toNNReal <|
          MvPowerSeries.coeff d
            (scalarMajorantOperator (n := n) (p := p) M R
              (scalarMajorantApproximant M R N))
      else
        MvPowerSeries.coeff d (scalarMajorantApproximant M R N)

/-- Helper for Cartan section29 0004_Exercise_2: stage `N + 1` keeps every coefficient outside
the newly inserted total degree `N + 1`. -/
lemma scalarMajorantApproximant_coeff_step_eq
    (M R : NNReal)
    (N : ℕ) (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d ≠ N + 1) :
    MvPowerSeries.coeff d (scalarMajorantApproximant (n := n) (p := p) M R (N + 1)) =
      MvPowerSeries.coeff d (scalarMajorantApproximant (n := n) (p := p) M R N) := by
  -- Away from the inserted degree, the recursive definition just reuses the previous stage.
  change
    (if _hdeg : paramDegree d = N + 1 then
        Real.toNNReal
          (MvPowerSeries.coeff d
            (scalarMajorantOperator (n := n) (p := p) M R
              (scalarMajorantApproximant (n := n) (p := p) M R N)))
      else
        MvPowerSeries.coeff d
          (scalarMajorantApproximant (n := n) (p := p) M R N)) =
      MvPowerSeries.coeff d (scalarMajorantApproximant (n := n) (p := p) M R N)
  simp [hd]

/-- Helper for Cartan section29 0004_Exercise_2: at the inserted degree, stage `N + 1` is exactly
the `Real.toNNReal` image of the scalar operator coefficient from stage `N`. -/
lemma scalarMajorantApproximant_coeff_insert_eq
    (M R : NNReal)
    (N : ℕ) (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d = N + 1) :
    MvPowerSeries.coeff d (scalarMajorantApproximant (n := n) (p := p) M R (N + 1)) =
      Real.toNNReal
        (MvPowerSeries.coeff d
          (scalarMajorantOperator (n := n) (p := p) M R
            (scalarMajorantApproximant (n := n) (p := p) M R N))) := by
  -- On the inserted degree, the recursive branch is the `Real.toNNReal` coefficient insertion.
  change
    (if _hdeg : paramDegree d = N + 1 then
        Real.toNNReal
          (MvPowerSeries.coeff d
            (scalarMajorantOperator (n := n) (p := p) M R
              (scalarMajorantApproximant (n := n) (p := p) M R N)))
      else
        MvPowerSeries.coeff d
          (scalarMajorantApproximant (n := n) (p := p) M R N)) =
      Real.toNNReal
        (MvPowerSeries.coeff d
          (scalarMajorantOperator (n := n) (p := p) M R
            (scalarMajorantApproximant (n := n) (p := p) M R N)))
  simp [hd]

/-- Helper for Cartan section29 0004_Exercise_2: once a later comparison supplies the needed
nonnegativity, the inserted degree can be read back from `NNReal` to `ℝ` without changing the
coefficient. -/
lemma scalarMajorantApproximant_coeff_insert_readback
    (M R : NNReal)
    (N : ℕ) (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d = N + 1)
    (hnonneg :
      0 ≤ MvPowerSeries.coeff d
        (scalarMajorantOperator (n := n) (p := p) M R
          (scalarMajorantApproximant (n := n) (p := p) M R N))) :
    (((MvPowerSeries.coeff d
        (scalarMajorantApproximant (n := n) (p := p) M R (N + 1)) : NNReal) : ℝ)) =
      MvPowerSeries.coeff d
        (scalarMajorantOperator (n := n) (p := p) M R
          (scalarMajorantApproximant (n := n) (p := p) M R N)) := by
  -- The stage definition inserts `Real.toNNReal`; nonnegativity is exactly what turns it back
  -- into the original real coefficient.
  rw [scalarMajorantApproximant_coeff_insert_eq (n := n) (p := p) M R N d hd]
  exact Real.coe_toNNReal _ hnonneg

/-- Helper for Cartan section29 0004_Exercise_2: every scalar stage keeps vanishing constant
coefficient because the recursion only inserts positive total degrees. -/
lemma scalarMajorantApproximant_constantCoeff
    (M R : NNReal) :
    ∀ N, MvPowerSeries.constantCoeff
      (scalarMajorantApproximant (n := n) (p := p) M R N) = 0
  | 0 => by
      simp [scalarMajorantApproximant]
  | N + 1 => by
      -- Degree `0` is never the inserted positive degree, so the previous stage's zero constant
      -- coefficient is preserved.
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [scalarMajorantApproximant_coeff_step_eq (n := n) (p := p) M R N 0]
      · simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using
          scalarMajorantApproximant_constantCoeff M R N
      · simp [paramDegree]

/-- Helper for Cartan section29 0004_Exercise_2: coefficients above stage `N` still vanish. -/
private lemma scalarMajorantApproximant_coeff_eq_zero_of_lt
    (M R : NNReal) :
    ∀ N d, N < paramDegree d →
      MvPowerSeries.coeff d (scalarMajorantApproximant (n := n) (p := p) M R N) = 0
  | 0, d, _ => by
      simp [scalarMajorantApproximant]
  | N + 1, d, hd => by
      have hne : paramDegree d ≠ N + 1 := by
        omega
      rw [scalarMajorantApproximant_coeff_step_eq (n := n) (p := p) M R N d hne]
      exact scalarMajorantApproximant_coeff_eq_zero_of_lt M R N d (by omega)

/-- Helper for Cartan section29 0004_Exercise_2: once a coefficient has been inserted, all later
stages keep it unchanged. -/
private lemma scalarMajorantApproximant_stabilizes
    (M R : NNReal) (d : ParamIndex n p →₀ ℕ) :
    ∀ k,
      MvPowerSeries.coeff d
          (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d + k)) =
        MvPowerSeries.coeff d
          (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d))
  | 0 => by
      rfl
  | k + 1 => by
      have hstep :
          MvPowerSeries.coeff d
              (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d + k + 1)) =
            MvPowerSeries.coeff d
              (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d + k)) := by
        have hne : paramDegree d ≠ paramDegree d + k + 1 := by
          omega
        simpa [Nat.add_assoc] using
          scalarMajorantApproximant_coeff_step_eq (n := n) (p := p) M R
            (paramDegree d + k) d hne
      calc
        MvPowerSeries.coeff d
            (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d + (k + 1)))
            = MvPowerSeries.coeff d
                (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d + k + 1)) := by
                  simp [Nat.add_assoc]
        _ = MvPowerSeries.coeff d
              (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d + k)) := hstep
        _ = MvPowerSeries.coeff d
              (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d)) :=
            scalarMajorantApproximant_stabilizes M R d k

/-- Helper for Cartan section29 0004_Exercise_2: the stabilized scalar-stage coefficients define
the direct-limit candidate for the scalar majorant fixed point. -/
noncomputable def scalarMajorantLimit
    (M R : NNReal) : MvPowerSeries (ParamIndex n p) NNReal :=
  fun d ↦
    MvPowerSeries.coeff d
      (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d))

/-- Helper for Cartan section29 0004_Exercise_2: the direct-limit scalar series inherits the zero
constant coefficient from stage `0`. -/
lemma scalarMajorantLimit_constantCoeff
    (M R : NNReal) :
    MvPowerSeries.constantCoeff (scalarMajorantLimit (n := n) (p := p) M R) = 0 := by
  -- At degree `0`, the direct limit reads back the stage-`0` coefficient.
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change
    MvPowerSeries.coeff (0 : ParamIndex n p →₀ ℕ)
      (scalarMajorantApproximant (n := n) (p := p) M R
        (paramDegree (0 : ParamIndex n p →₀ ℕ))) = 0
  simp [scalarMajorantApproximant, paramDegree]

/-- Helper for Cartan section29 0004_Exercise_2: the direct-limit scalar series agrees with every
later stage on already-inserted coefficients. -/
lemma scalarMajorantLimit_coeff_eq_approximant
    (M R : NNReal)
    (d : ParamIndex n p →₀ ℕ) {N : ℕ}
    (hd : paramDegree d ≤ N) :
    MvPowerSeries.coeff d (scalarMajorantLimit (n := n) (p := p) M R) =
      MvPowerSeries.coeff d
        (scalarMajorantApproximant (n := n) (p := p) M R N) := by
  calc
    MvPowerSeries.coeff d (scalarMajorantLimit (n := n) (p := p) M R) =
        MvPowerSeries.coeff d
          (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d)) := rfl
    _ = MvPowerSeries.coeff d
          (scalarMajorantApproximant (n := n) (p := p) M R
            (paramDegree d + (N - paramDegree d))) := by
              symm
              exact scalarMajorantApproximant_stabilizes (n := n) (p := p) M R d
                (N - paramDegree d)
    _ = MvPowerSeries.coeff d
          (scalarMajorantApproximant (n := n) (p := p) M R N) := by
            rw [Nat.add_sub_of_le hd]

/-- Helper for Cartan section29 0004_Exercise_2: multiplying two real multivariable power series
with coefficientwise nonnegative coefficients preserves coefficientwise nonnegativity. -/
private lemma coeff_mul_nonneg_of_nonneg
    {φ ψ : MvPowerSeries (ParamIndex n p) ℝ}
    (hφ : ∀ d, 0 ≤ MvPowerSeries.coeff d φ)
    (hψ : ∀ d, 0 ≤ MvPowerSeries.coeff d ψ)
    (d : ParamIndex n p →₀ ℕ) :
    0 ≤ MvPowerSeries.coeff d (φ * ψ) := by
  classical
  -- Expand the Cauchy product and bound each antidiagonal summand separately.
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun e he ↦ mul_nonneg (hφ e.1) (hψ e.2)

/-- Helper for Cartan section29 0004_Exercise_2: if every coefficient of a real multivariable
power series is nonnegative, then the same is true for every power of that series. -/
private lemma coeff_pow_nonneg_of_nonneg
    {φ : MvPowerSeries (ParamIndex n p) ℝ}
    (hφ : ∀ d, 0 ≤ MvPowerSeries.coeff d φ) :
    ∀ q d, 0 ≤ MvPowerSeries.coeff d (φ ^ q)
  | 0, d => by
      by_cases hd : d = 0
      · subst hd
        simp
      · simp [MvPowerSeries.coeff_one, hd]
  | q + 1, d => by
      -- Rewrite the next power as a product and reuse the coefficientwise product bound.
      rw [pow_succ]
      exact coeff_mul_nonneg_of_nonneg
        (coeff_pow_nonneg_of_nonneg hφ q) hφ d

/-- Helper for Cartan section29 0004_Exercise_2: the sum of the `y`-variables has nonnegative
real coefficients coefficientwise. -/
private lemma coeff_paramYSum_nonneg
    (d : ParamIndex n p →₀ ℕ) :
    0 ≤ MvPowerSeries.coeff d (paramYSum (n := n) (p := p)) := by
  -- Each `y`-variable contributes either `0` or `1` to the target coefficient.
  classical
  rw [paramYSum]
  simpa using (Finset.sum_nonneg fun j hj ↦ by
    by_cases hdj : d = Finsupp.single (Sum.inl j) 1
    · simp [MvPowerSeries.coeff_X, hdj]
    · simp [MvPowerSeries.coeff_X, hdj])

/-- Helper for Cartan section29 0004_Exercise_2: the sum of the `z`-variables has nonnegative
real coefficients coefficientwise. -/
private lemma coeff_paramZSum_nonneg
    (d : ParamIndex n p →₀ ℕ) :
    0 ≤ MvPowerSeries.coeff d (paramZSum (n := n) (p := p)) := by
  -- Each `z`-variable contributes either `0` or `1` to the target coefficient.
  classical
  rw [paramZSum]
  simpa using (Finset.sum_nonneg fun k hk ↦ by
    by_cases hdk : d = Finsupp.single (Sum.inr k) 1
    · simp [MvPowerSeries.coeff_X, hdk]
    · simp [MvPowerSeries.coeff_X, hdk])

/-- Helper for Cartan section29 0004_Exercise_2: for a zero-constant multivariable power series,
the coefficient of `(1 - f)⁻¹` is the finite sum of the coefficients of the powers `f^q` whose
order can still contribute to the target total degree. -/
private lemma coeff_invOneSub_eq_sum_range
    {f : MvPowerSeries (ParamIndex n p) ℝ}
    (hf0 : MvPowerSeries.constantCoeff f = 0)
    (d : ParamIndex n p →₀ ℕ) :
    MvPowerSeries.coeff d ((1 - f)⁻¹) =
      Finset.sum (Finset.range (paramDegree d + 1)) fun q =>
        MvPowerSeries.coeff d (f ^ q) := by
  have hgeom : (1 - f)⁻¹ = ∑' q : ℕ, f ^ q := by
    -- Rewrite the inverse via the geometric series once the constant coefficient vanishes.
    have hcc : MvPowerSeries.constantCoeff (1 - f) = (1 : ℝ) := by
      simp [hf0]
    calc
      (1 - f)⁻¹ = (1 - f)⁻¹ * ((1 - f) * ∑' q : ℕ, f ^ q) := by
        rw [MvPowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero
          (f := f) hf0, mul_one]
      _ = ((1 - f)⁻¹ * (1 - f)) * ∑' q : ℕ, f ^ q := by
        ac_rfl
      _ = (1 : MvPowerSeries (ParamIndex n p) ℝ) * ∑' q : ℕ, f ^ q := by
        rw [← MvPowerSeries.invOfUnit_eq' (φ := 1 - f) (u := 1) (by simpa using hcc),
          MvPowerSeries.invOfUnit_mul (φ := 1 - f) (u := 1) (by simpa using hcc)]
      _ = ∑' q : ℕ, f ^ q := by
        simp
  have hcoeffTsum :
      MvPowerSeries.coeff d (∑' q : ℕ, f ^ q) = ∑' q : ℕ, MvPowerSeries.coeff d (f ^ q) := by
    simpa [MvPowerSeries.coeff_apply] using
      (tsum_apply (x := d)
        (MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hf0))
  rw [hgeom, hcoeffTsum]
  refine tsum_eq_sum ?_
  intro q hq
  apply MvPowerSeries.coeff_of_lt_order
  have hle : paramDegree d + 1 ≤ q := by
    exact Nat.not_lt.mp (fun hlt' => hq (Finset.mem_range.mpr hlt'))
  have hlt : paramDegree d < q := by
    omega
  have hlt' : ((paramDegree d : ℕ) : ℕ∞) < q := by
    exact_mod_cast hlt
  simpa [paramDegree_eq_degree] using
    (lt_of_lt_of_le hlt' (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero q hf0))

/-- Helper for Cartan section29 0004_Exercise_2: the geometric inverse of a zero-constant real
multivariable power series with nonnegative coefficients still has coefficientwise nonnegative
coefficients. -/
private lemma coeff_invOneSub_nonneg_of_nonneg
    {f : MvPowerSeries (ParamIndex n p) ℝ}
    (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : ∀ d, 0 ≤ MvPowerSeries.coeff d f)
    (d : ParamIndex n p →₀ ℕ) :
    0 ≤ MvPowerSeries.coeff d ((1 - f)⁻¹) := by
  have hgeom : (1 - f)⁻¹ = ∑' q : ℕ, f ^ q := by
    -- Rewrite the inverse via the geometric series once the constant coefficient vanishes.
    have hcc : MvPowerSeries.constantCoeff (1 - f) = (1 : ℝ) := by
      simp [hf0]
    calc
      (1 - f)⁻¹ = (1 - f)⁻¹ * ((1 - f) * ∑' q : ℕ, f ^ q) := by
        rw [MvPowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero
          (f := f) hf0, mul_one]
      _ = ((1 - f)⁻¹ * (1 - f)) * ∑' q : ℕ, f ^ q := by
        ac_rfl
      _ = (1 : MvPowerSeries (ParamIndex n p) ℝ) * ∑' q : ℕ, f ^ q := by
        rw [← MvPowerSeries.invOfUnit_eq' (φ := 1 - f) (u := 1) (by simpa using hcc),
          MvPowerSeries.invOfUnit_mul (φ := 1 - f) (u := 1) (by simpa using hcc)]
      _ = ∑' q : ℕ, f ^ q := by
        simp
  have hcoeff :
      MvPowerSeries.coeff d ((1 - f)⁻¹) =
        Finset.sum (Finset.range (paramDegree d + 1)) fun q =>
          MvPowerSeries.coeff d (f ^ q) := by
    -- Only powers up to the target total degree can contribute to the target coefficient.
    have hcoeffTsum :
        MvPowerSeries.coeff d (∑' q : ℕ, f ^ q) = ∑' q : ℕ, MvPowerSeries.coeff d (f ^ q) := by
      simpa [MvPowerSeries.coeff_apply] using
        (tsum_apply (x := d)
          (MvPowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hf0))
    rw [hgeom, hcoeffTsum]
    refine tsum_eq_sum ?_
    intro q hq
    apply MvPowerSeries.coeff_of_lt_order
    have hle : paramDegree d + 1 ≤ q := by
      exact Nat.not_lt.mp (fun hlt' => hq (Finset.mem_range.mpr hlt'))
    have hlt : paramDegree d < q := by
      omega
    have hlt' : ((paramDegree d : ℕ) : ℕ∞) < q := by
      exact_mod_cast hlt
    simpa [paramDegree_eq_degree] using
      (lt_of_lt_of_le hlt' (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero q hf0))
  rw [hcoeff]
  exact Finset.sum_nonneg fun q hq ↦ coeff_pow_nonneg_of_nonneg hf q d

/-- Helper for Cartan section29 0004_Exercise_2: the scalar majorant operator has nonnegative
real coefficients on every `NNReal` stage. This is the readback bridge used by the direct-limit
fixed-point proof. -/
private lemma coeffOuterGeometricFactor_nonneg
    (M R : NNReal)
    (d : ParamIndex n p →₀ ℕ) :
    0 ≤
      MvPowerSeries.coeff d
        ((MvPowerSeries.C (M : ℝ)) *
          (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹) := by
  -- The outer geometric factor is a nonnegative constant multiplied by a geometric inverse with
  -- coefficientwise nonnegative `z`-kernel.
  rw [MvPowerSeries.coeff_C_mul]
  refine mul_nonneg (by positivity) ?_
  refine coeff_invOneSub_nonneg_of_nonneg (n := n) (p := p)
    (f := MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p)) ?_ ?_ d
  · simp [paramZSum]
  · intro e
    rw [MvPowerSeries.coeff_C_mul]
    exact mul_nonneg (by positivity) (coeff_paramZSum_nonneg (n := n) (p := p) e)

lemma scalarMajorantOperator_coeff_nonneg
    (M R : NNReal)
    {X : MvPowerSeries (ParamIndex n p) NNReal}
    (hX0 : MvPowerSeries.constantCoeff X = 0)
    (d : ParamIndex n p →₀ ℕ) :
    0 ≤ MvPowerSeries.coeff d (scalarMajorantOperator (n := n) (p := p) M R X) := by
  let Xr : MvPowerSeries (ParamIndex n p) ℝ := MvPowerSeries.map NNReal.toRealHom X
  let a : ℝ := ((n : ℕ) : ℝ) / (R : ℝ)
  let b : ℝ := (R : ℝ)⁻¹
  have hXr : ∀ e, 0 ≤ MvPowerSeries.coeff e Xr := by
    intro e
    simp [Xr, MvPowerSeries.coeff_map]
  have hscaledXr : ∀ e, 0 ≤ MvPowerSeries.coeff e (MvPowerSeries.C a * Xr) := by
    intro e
    rw [MvPowerSeries.coeff_C_mul]
    exact mul_nonneg (by positivity) (hXr e)
  have houterSeries :
      ∀ e, 0 ≤ MvPowerSeries.coeff e
        ((1 - MvPowerSeries.C b * paramZSum (n := n) (p := p))⁻¹ : MvPowerSeries (ParamIndex n p) ℝ) := by
    intro e
    -- The geometric `z`-factor is a series with nonnegative coefficients.
    refine coeff_invOneSub_nonneg_of_nonneg (n := n) (p := p)
      (f := MvPowerSeries.C b * paramZSum (n := n) (p := p)) ?_ ?_ e
    · simp [paramZSum]
    · intro e'
      rw [MvPowerSeries.coeff_C_mul]
      exact mul_nonneg (by positivity) (coeff_paramZSum_nonneg (n := n) (p := p) e')
  have htail :
      ∀ e, 0 ≤ MvPowerSeries.coeff e (scalarQuadraticTail (n := n) (p := p) a X) := by
    intro e
    by_cases he0 : paramDegree e = 0
    · have hez : e = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) e).mp he0
      subst hez
      simp [scalarQuadraticTail, hX0]
    · have hpos : 0 < paramDegree e := Nat.pos_iff_ne_zero.mpr he0
      rw [coeff_scalarQuadraticTail_eq_sum_range (n := n) (p := p) a
        (by simp [hX0]) e hpos]
      exact Finset.sum_nonneg fun q hq ↦ coeff_pow_nonneg_of_nonneg hscaledXr (q + 2) e
  have hinner :
      ∀ e, 0 ≤ MvPowerSeries.coeff e (scalarMajorantInner (n := n) (p := p) a X) := by
    intro e
    -- The inner factor is the sum of the `y`-variables and the nonnegative quadratic tail.
    simpa [scalarMajorantInner] using
      add_nonneg (coeff_paramYSum_nonneg (n := n) (p := p) e) (htail e)
  rw [scalarMajorantOperator_eq_outer_mul_inner (n := n) (p := p) M R X]
  apply coeff_mul_nonneg_of_nonneg
  · intro e
    rw [MvPowerSeries.coeff_C_mul]
    exact mul_nonneg (by positivity) (houterSeries e)
  · exact hinner

/-- Helper for Cartan section29 0004_Exercise_2: the stabilized direct-limit scalar series really
is a fixed point of the scalar quadratic operator. The proof stays coefficientwise and compares
the limit with the predecessor stage only below the target total degree. -/
lemma scalarMajorantLimit_isFixedPoint
    (M R : NNReal) :
    MvPowerSeries.map NNReal.toRealHom (scalarMajorantLimit (n := n) (p := p) M R) =
      scalarMajorantOperator (n := n) (p := p) M R
        (scalarMajorantLimit (n := n) (p := p) M R) := by
  ext d
  by_cases hd0 : paramDegree d = 0
  · have hdz : d = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) d).mp hd0
    subst hdz
    -- The degree-zero coefficient is already zero on both sides.
    simp [scalarMajorantLimit_constantCoeff, scalarMajorantOperator_eq_outer_mul_inner,
      scalarMajorantInner, scalarQuadraticTail, paramYSum]
  · let N := paramDegree d - 1
    have hd : paramDegree d = N + 1 := by
      dsimp [N]
      omega
    have hprefix :
        ∀ e, paramDegree e < paramDegree d →
          MvPowerSeries.coeff e
            (scalarMajorantLimit (n := n) (p := p) M R) =
            MvPowerSeries.coeff e
              (scalarMajorantApproximant (n := n) (p := p) M R N) := by
      intro e he
      exact scalarMajorantLimit_coeff_eq_approximant (n := n) (p := p) M R e (by
        dsimp [N]
        omega)
    -- Read the inserted coefficient back from stage `N + 1`, then transport the operator from
    -- the predecessor stage to the direct limit using lower-degree coefficient agreement.
    calc
      (((MvPowerSeries.coeff d
          (scalarMajorantLimit (n := n) (p := p) M R) : NNReal) : ℝ)) =
          (((MvPowerSeries.coeff d
              (scalarMajorantApproximant (n := n) (p := p) M R (N + 1)) : NNReal) : ℝ)) := by
            congr 1
            exact scalarMajorantLimit_coeff_eq_approximant (n := n) (p := p) M R d (by
              simpa [hd])
      _ = MvPowerSeries.coeff d
            (scalarMajorantOperator (n := n) (p := p) M R
              (scalarMajorantApproximant (n := n) (p := p) M R N)) := by
              exact scalarMajorantApproximant_coeff_insert_readback (n := n) (p := p)
                M R N d hd
                (scalarMajorantOperator_coeff_nonneg (n := n) (p := p) M R
                  (scalarMajorantApproximant_constantCoeff (n := n) (p := p) M R N) d)
      _ = MvPowerSeries.coeff d
            (scalarMajorantOperator (n := n) (p := p) M R
              (scalarMajorantLimit (n := n) (p := p) M R)) := by
            symm
            exact scalarMajorantOperator_coeff_eq_of_lowerCoeffEq (n := n) (p := p) M R
              (scalarMajorantLimit_constantCoeff (n := n) (p := p) M R)
              (scalarMajorantApproximant_constantCoeff (n := n) (p := p) M R N)
              d hprefix

/-- Bridge/view layer: a scalar `NNReal`-valued majorant solves the symmetric quadratic equation
and dominates each component of a family majorant. -/
def IsScalarMajorantBridge
    (Ξ : Fin n → MvPowerSeries (ParamIndex n p) NNReal)
    (M R : NNReal) (X : MvPowerSeries (ParamIndex n p) NNReal) : Prop :=
  MvPowerSeries.map NNReal.toRealHom X = scalarMajorantOperator M R X ∧
    ∀ j d, ((Ξ j) d : ℝ) ≤ (X d : ℝ)

end ScalarQuadraticMajorant
