import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_57_1 (from Chap10) -/
universe u v

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain note: this item lies in graded commutative algebra and projective-spectrum topology.
It is a `core/canonical` recall: the owner abstraction is `ProjectiveSpectrum 𝒜`, while the
topology is derived canonically from that owner via `ProjectiveSpectrum.zariskiTopology`. No local
wrapper or parallel `Proj` point-space API is needed here. -/

/- Definition 10.57.1 (Stacks, Tag `00JN`) is recalled canonically by
`ProjectiveSpectrum 𝒜`: for an `ℕ`-graded commutative ring, its points are exactly the homogeneous
prime ideals that do not contain the irrelevant ideal. This is the source's `Proj(S)`. -/
recall ProjectiveSpectrum

/- Companion recall: the topological-space structure on `ProjectiveSpectrum 𝒜` is the canonical
Zariski topology used for `Proj(S)`. -/
recall ProjectiveSpectrum.zariskiTopology

end

/-! ### Lemma_10_57_2 (from Chap10) -/
universe u

open PrimeSpectrum

section

variable {S : Type u} [CommRing S]
variable (𝒜 : ℤ → Submodule ℤ S) [GradedRing 𝒜]

/-- Helper for Lemma 10.57.2: the restricted contraction map on homogeneous primes is continuous,
because it is the composition of the ambient spectrum map with the subtype inclusion. -/
lemma continuous_restricted_comap :
    Continuous
      ((comap (algebraMap (𝒜 0) S)) ∘
        (Subtype.val : { p : PrimeSpectrum S // p.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) := by
  -- Continuity is inherited from `PrimeSpectrum.comap` and the induced topology on the subtype.
  exact continuous_comap _ |>.comp continuous_subtype_val

/-- Helper for Lemma 10.57.2: a homogeneous unit in degree `d` has a homogeneous inverse in
degree `-d`. -/
lemma homogeneous_unit_inverse_component
    {d : ℤ} {f : S} (hf : f ∈ 𝒜 d) (hfu : IsUnit f) :
    ∃ g : 𝒜 (-d), (f : S) * (g : S) = 1 := by
  obtain ⟨g, hg⟩ := hfu.exists_right_inv
  refine ⟨DirectSum.decompose 𝒜 g (-d), ?_⟩
  -- Only the `-d`-component of the inverse contributes to the degree-zero part of `f * g`.
  have hcomp₀ :
      (DirectSum.decompose 𝒜 (f * g) (d + -d) : S) =
        f * (DirectSum.decompose 𝒜 g (-d) : S) :=
    DirectSum.coe_decompose_mul_add_of_left_mem (𝒜 := 𝒜) (i := d) (j := -d)
      (a := f) (b := g) hf
  have hcomp :
      (DirectSum.decompose 𝒜 (f * g) 0 : S) =
        f * (DirectSum.decompose 𝒜 g (-d) : S) := by
    have hcomp := hcomp₀
    rwa [add_neg_cancel] at hcomp
  -- Rewriting `f * g = 1` identifies that degree-zero component with the unit element.
  simpa [hg] using hcomp.symm

/-- Helper for Lemma 10.57.2: the source-faithful degree-zero correction attached to a homogeneous
element uses the positive-degree unit for negative indices and its homogeneous inverse for
nonnegative indices. -/
noncomputable def degree_zero_correction
    {d : ℤ} (f : 𝒜 d) (g : 𝒜 (-d)) (i : ℤ) (x : 𝒜 i) : S :=
  if _ : 0 ≤ i then
    (x : S) ^ Int.toNat d * (g : S) ^ Int.toNat i
  else
    (x : S) ^ Int.toNat d * (f : S) ^ Int.toNat (-i)

/-- Helper for Lemma 10.57.2: the correction term attached to a homogeneous element has degree
zero. -/
lemma degree_zero_correction_mem_degree_zero
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) (i : ℤ) (x : 𝒜 i) :
    degree_zero_correction (𝒜 := 𝒜) (d := d) (f := f) (g := g) (i := i) (x := x) ∈ 𝒜 0 := by
  -- The correction multiplies degree `d * i` by degree `-d * i`.
  by_cases hi : 0 ≤ i
  · rw [degree_zero_correction, dif_pos hi]
    have hxpow : (x : S) ^ Int.toNat d ∈ 𝒜 (Int.toNat d • i) :=
      SetLike.pow_mem_graded _ x.2
    have hgpow : (g : S) ^ Int.toNat i ∈ 𝒜 (Int.toNat i • (-d)) :=
      SetLike.pow_mem_graded _ g.2
    have hmul := SetLike.mul_mem_graded hxpow hgpow
    have hdmax : max d 0 = d := max_eq_left hd.le
    have himax : max i 0 = i := max_eq_left hi
    have hdeg : d * i + -(i * d) = 0 := by
      ring
    simpa [nsmul_eq_mul, hdmax, himax, hdeg] using hmul
  · rw [degree_zero_correction, dif_neg hi]
    have hni : 0 ≤ -i := by
      omega
    have hxpow : (x : S) ^ Int.toNat d ∈ 𝒜 (Int.toNat d • i) :=
      SetLike.pow_mem_graded _ x.2
    have hfpow : (f : S) ^ Int.toNat (-i) ∈ 𝒜 (Int.toNat (-i) • d) :=
      SetLike.pow_mem_graded _ f.2
    have hmul := SetLike.mul_mem_graded hxpow hfpow
    have hdmax : max d 0 = d := max_eq_left hd.le
    have hnimax : max (-i) 0 = -i := max_eq_left hni
    have hdeg : d * i + -(i * d) = 0 := by
      ring
    simpa [nsmul_eq_mul, hdmax, hnimax, hdeg] using hmul

/-- Helper for Lemma 10.57.2: in degree zero, the correction reduces to the plain positive power.
-/
lemma degree_zero_correction_eq_pow
    {d : ℤ} (f : 𝒜 d) (g : 𝒜 (-d)) (x : 𝒜 0) :
    degree_zero_correction (𝒜 := 𝒜) (d := d) (f := f) (g := g) (i := 0) (x := x) =
      (x : S) ^ Int.toNat d := by
  -- At degree zero the correcting factor is the trivial zeroth power.
  simp [degree_zero_correction]

/-- Helper for Lemma 10.57.2: package the source-faithful correction as an element of the
degree-zero piece. -/
noncomputable def degree_zero_corrected_component
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) (i : ℤ) (x : 𝒜 i) : 𝒜 0 :=
  ⟨degree_zero_correction (𝒜 := 𝒜) (d := d) (f := f) (g := g) (i := i) (x := x),
    degree_zero_correction_mem_degree_zero (𝒜 := 𝒜) (d := d) hd f g i x⟩

/-- Helper for Lemma 10.57.2: at the matching degree, the corrected component built from
`DirectSum.decompose` agrees with the corrected component of the original homogeneous element. -/
lemma degree_zero_corrected_component_of_mem_same
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) {i : ℤ} {x : S} (hx : x ∈ 𝒜 i) :
    degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i (DirectSum.decompose 𝒜 x i) =
      degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i ⟨x, hx⟩ := by
  -- The matching graded component is definitionally the original homogeneous element.
  have hdecomp : DirectSum.decompose 𝒜 x i = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact DirectSum.decompose_of_mem_same 𝒜 hx
  simpa [degree_zero_corrected_component, hdecomp]

/-- Helper for Lemma 10.57.2: an off-degree homogeneous component contributes the zero corrected
degree-zero term. -/
lemma degree_zero_corrected_component_of_mem_ne
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) {i j : ℤ} {x : S}
    (hx : x ∈ 𝒜 i) (hij : i ≠ j) :
    degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g j (DirectSum.decompose 𝒜 x j) = 0 := by
  -- Away from the true degree, the component vanishes, so the corrected term is zero.
  have hd_nat : 0 < Int.toNat d := by
    omega
  apply Subtype.ext
  simp [degree_zero_corrected_component, DirectSum.decompose_of_mem_ne 𝒜 hx hij,
    degree_zero_correction, Nat.ne_of_gt hd_nat]

/-- Helper for Lemma 10.57.2: the corrected carrier is first exposed as the source-faithful
underlying membership predicate before it is packaged into an ideal. -/
noncomputable def degree_zero_extension_carrier
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) (p₀ : PrimeSpectrum (𝒜 0)) : Set S :=
  { a | ∀ i,
      degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i
        (DirectSum.decompose 𝒜 a i) ∈ p₀.asIdeal }

/-- Helper for Lemma 10.57.2: the corrected carrier contains zero, which is the first easy piece
of the later ideal packaging. -/
lemma zero_mem_degree_zero_extension_carrier
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) (p₀ : PrimeSpectrum (𝒜 0)) :
    (0 : S) ∈ degree_zero_extension_carrier (𝒜 := 𝒜) (d := d) hd f g p₀ := by
  rw [degree_zero_extension_carrier]
  intro i
  -- Every homogeneous component of zero is zero, so each corrected degree-zero term is zero.
  have hzero :
      degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i
        (DirectSum.decompose 𝒜 (0 : S) i) = 0 := by
    apply Subtype.ext
    have hd_nat : 0 < Int.toNat d := by
      omega
    simp [degree_zero_corrected_component, degree_zero_correction, Nat.ne_of_gt hd_nat]
  rw [hzero]
  exact p₀.asIdeal.zero_mem

/-- Helper for Lemma 10.57.2: for a homogeneous input, membership in the corrected carrier is
equivalent to membership of the unique nonzero corrected component. -/
lemma degree_zero_extension_mem_iff_of_mem
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) (p₀ : PrimeSpectrum (𝒜 0))
    {i : ℤ} {x : S} (hx : x ∈ 𝒜 i) :
    x ∈ degree_zero_extension_carrier (𝒜 := 𝒜) (d := d) hd f g p₀ ↔
      degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i ⟨x, hx⟩ ∈ p₀.asIdeal := by
  refine ⟨fun h => ?_, fun h j => ?_⟩
  · -- For the matching degree, the universal carrier condition is exactly the desired term.
    simpa [degree_zero_extension_carrier] using
      (degree_zero_corrected_component_of_mem_same (𝒜 := 𝒜) (d := d) hd f g hx) ▸ h i
  · by_cases hij : j = i
    · -- At the distinguished degree, the only surviving component is the given homogeneous input.
      subst hij
      simpa [degree_zero_extension_carrier] using
        (degree_zero_corrected_component_of_mem_same (𝒜 := 𝒜) (d := d) hd f g hx).symm ▸ h
    · -- Off the distinguished degree, the component vanishes, so the corrected term is zero.
      have hji : i ≠ j := by
        exact fun hji_eq => hij hji_eq.symm
      simpa [degree_zero_extension_carrier] using
        (degree_zero_corrected_component_of_mem_ne (𝒜 := 𝒜) (d := d) hd f g hx hji) ▸
          (p₀.asIdeal.zero_mem : (0 : 𝒜 0) ∈ p₀.asIdeal)

/-- Helper for Lemma 10.57.2: the source-faithful owner ideal `𝔭₀S` is the extension of the
degree-zero prime along the inclusion `S₀ ↪ S`. -/
noncomputable def degree_zero_extension_ideal
    (p₀ : PrimeSpectrum (𝒜 0)) : Ideal S :=
  Ideal.map (algebraMap (𝒜 0) S) p₀.asIdeal

/-- Helper for Lemma 10.57.2: `𝔭₀S` is homogeneous because it is generated by degree-zero
homogeneous elements. -/
lemma degree_zero_extension_ideal_isHomogeneous
    (p₀ : PrimeSpectrum (𝒜 0)) :
    (degree_zero_extension_ideal (𝒜 := 𝒜) p₀).IsHomogeneous 𝒜 := by
  -- Route correction: follow Tag `00JO` with the literal owner `𝔭₀S`, rather than trying to
  -- package the corrected-carrier predicate itself as an ideal.
  have hp₀_span : Ideal.span (p₀.asIdeal : Set (𝒜 0)) = p₀.asIdeal := by
    simpa using (Submodule.span_eq p₀.asIdeal)
  rw [degree_zero_extension_ideal, ← hp₀_span, Ideal.map_span]
  -- Every generator comes from degree zero, so the generated ideal is homogeneous.
  refine Ideal.homogeneous_span 𝒜 _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact SetLike.isHomogeneousElem_coe x

/-- Helper for Lemma 10.57.2: generators from `𝔭₀` lie in the extended ideal `𝔭₀S`. -/
lemma degree_zero_extension_ideal_mem_of_mem_zero
    (p₀ : PrimeSpectrum (𝒜 0)) {x : 𝒜 0} (hx : x ∈ p₀.asIdeal) :
    (x : S) ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀ := by
  -- The extension ideal is defined by mapping along the degree-zero inclusion.
  exact Ideal.mem_map_of_mem (algebraMap (𝒜 0) S) hx

/-- Helper for Lemma 10.57.2: projecting the product with a degree-zero homogeneous factor back to
degree zero only keeps the degree-zero component of the other factor. -/
lemma decompose_mul_degree_zero_right (a : S) (x : 𝒜 0) :
    (DirectSum.decompose 𝒜 (a * (x : S)) 0 : S) =
      (DirectSum.decompose 𝒜 a 0 : S) * (x : S) := by
  -- This is the basic degree-zero projection identity used in the additive contraction step.
  simpa using
    (DirectSum.coe_decompose_mul_of_right_mem_zero (𝒜 := 𝒜) (a := a) (b := (x : S)) x.2)

/-- Helper for Lemma 10.57.2: the degree-zero projection of an element of the extension ideal
`𝔭₀S` already lies in `𝔭₀`. -/
lemma degree_zero_component_mem_of_mem_extension_ideal
    (p₀ : PrimeSpectrum (𝒜 0)) {y : S}
    (hy : y ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀) :
    DirectSum.decompose 𝒜 y 0 ∈ p₀.asIdeal := by
  have hp₀_span : Ideal.span (p₀.asIdeal : Set (𝒜 0)) = p₀.asIdeal := by
    simpa using (Submodule.span_eq p₀.asIdeal)
  rw [degree_zero_extension_ideal, ← hp₀_span, Ideal.map_span] at hy
  have hy' :
      y ∈ Ideal.span (Set.range fun z : p₀.asIdeal => (((z : 𝒜 0) : S))) := by
    -- Rewrite the extension ideal as the span of the literal degree-zero generators from `𝔭₀`.
    simpa [Set.image_eq_range] using hy
  rw [Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hy'
  rcases hy' with ⟨c, rfl⟩
  -- Project the finite generator expansion termwise to degree zero.
  simpa [Finsupp.sum, DirectSum.decompose_sum, DFinsupp.finset_sum_apply,
    AddSubmonoidClass.coe_finset_sum] using
    (show (∑ z ∈ c.support,
        DirectSum.decompose 𝒜 (c z * ((((z : p₀.asIdeal) : 𝒜 0) : S))) 0) ∈ p₀.asIdeal from by
      refine Ideal.sum_mem _ fun z hz => ?_
      have hterm :
          DirectSum.decompose 𝒜 (c z * ((((z : p₀.asIdeal) : 𝒜 0) : S))) 0 =
            DirectSum.decompose 𝒜 (c z) 0 * ((z : p₀.asIdeal) : 𝒜 0) := by
        -- Each summand is a coefficient times a genuine degree-zero generator, so only the
        -- degree-zero piece of the coefficient survives under projection.
        apply Subtype.ext
        simpa using
          (decompose_mul_degree_zero_right (𝒜 := 𝒜) (a := c z) (((z : p₀.asIdeal) : 𝒜 0)))
      rw [hterm]
      exact p₀.asIdeal.mul_mem_left _ z.2)

/-- Helper for Lemma 10.57.2: contracting `𝔭₀S` back to the degree-zero piece recovers `𝔭₀`
elementwise. -/
lemma degree_zero_extension_ideal_mem_iff_of_mem_zero
    (p₀ : PrimeSpectrum (𝒜 0)) (x : 𝒜 0) :
    (x : S) ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀ ↔ x ∈ p₀.asIdeal := by
  constructor
  · intro hx
    -- The new projection lemma implements the source identity `𝔭₀S ∩ S₀ = 𝔭₀`.
    simpa [DirectSum.decompose_of_mem_same 𝒜 x.2] using
      degree_zero_component_mem_of_mem_extension_ideal (𝒜 := 𝒜) p₀ hx
  · -- Generators from `𝔭₀` always lie in the extension ideal by definition of `Ideal.map`.
    exact degree_zero_extension_ideal_mem_of_mem_zero (𝒜 := 𝒜) p₀

/-- Helper for Lemma 10.57.2: the contraction of the extension ideal `𝔭₀S` is exactly `𝔭₀`. -/
lemma degree_zero_extension_ideal_comap
    (p₀ : PrimeSpectrum (𝒜 0)) :
    Ideal.comap (algebraMap (𝒜 0) S) (degree_zero_extension_ideal (𝒜 := 𝒜) p₀) = p₀.asIdeal := by
  -- The comap statement is the ideal-level restatement of the pending elementwise contraction.
  ext x
  change (((x : 𝒜 0) : S) ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀) ↔ x ∈ p₀.asIdeal
  simpa using degree_zero_extension_ideal_mem_iff_of_mem_zero (𝒜 := 𝒜) p₀ x

/-- Helper for Lemma 10.57.2: once the positive-degree unit and its inverse multiply to `1`,
their matching natural powers also cancel. -/
lemma homogeneous_unit_natpow_cancel
    {a b : S} (hab : a * b = 1) (n : ℕ) :
    a ^ n * b ^ n = 1 := by
  -- The source only needs the basic power cancellation coming from `(ab)^n = 1`.
  calc
    a ^ n * b ^ n = (a * b) ^ n := by
      rw [mul_pow]
    _ = 1 := by
      simp [hab]

/-- Helper for Lemma 10.57.2: if the corrected degree-zero term of a homogeneous element lands in
`𝔭₀`, then the source-faithful power `(a : S)^d` already lies in the extension ideal `𝔭₀S`. -/
lemma degree_zero_extension_pow_mem_of_corrected_mem
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d))
    (hfg : (f : S) * (g : S) = 1) (p₀ : PrimeSpectrum (𝒜 0)) {i : ℤ} (a : 𝒜 i)
    (ha : degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a ∈ p₀.asIdeal) :
    (a : S) ^ Int.toNat d ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀ := by
  let J := degree_zero_extension_ideal (𝒜 := 𝒜) p₀
  have hcorr_mem : ((degree_zero_corrected_component
      (𝒜 := 𝒜) (d := d) hd f g i a : 𝒜 0) : S) ∈ J :=
    degree_zero_extension_ideal_mem_of_mem_zero (𝒜 := 𝒜) p₀ ha
  have hgf : (g : S) * (f : S) = 1 := by
    simpa [mul_comm] using hfg
  -- The source proof splits on the sign of the degree and multiplies back by the matching power.
  by_cases hi : 0 ≤ i
  · have hcorr :
        ((degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a : 𝒜 0) : S) =
          (a : S) ^ Int.toNat d * (g : S) ^ Int.toNat i := by
      -- In the nonnegative-degree branch the correction uses the inverse component `g`.
      simp [degree_zero_corrected_component, degree_zero_correction, hi]
    rw [hcorr] at hcorr_mem
    have hmul : ((a : S) ^ Int.toNat d * (g : S) ^ Int.toNat i) * (f : S) ^ Int.toNat i ∈ J := by
      exact Ideal.mul_mem_right ((f : S) ^ Int.toNat i) J hcorr_mem
    have hcancel : (g : S) ^ Int.toNat i * (f : S) ^ Int.toNat i = 1 :=
      homogeneous_unit_natpow_cancel (a := (g : S)) (b := (f : S)) hgf (Int.toNat i)
    -- Reassociate the correcting factors so that the unit powers cancel.
    have hrewrite :
        ((a : S) ^ Int.toNat d * (g : S) ^ Int.toNat i) * (f : S) ^ Int.toNat i =
          (a : S) ^ Int.toNat d := by
      calc
        ((a : S) ^ Int.toNat d * (g : S) ^ Int.toNat i) * (f : S) ^ Int.toNat i =
            (a : S) ^ Int.toNat d * ((g : S) ^ Int.toNat i * (f : S) ^ Int.toNat i) := by
              ring_nf
        _ = (a : S) ^ Int.toNat d * 1 := by
              rw [hcancel]
        _ = (a : S) ^ Int.toNat d := by
              simp
    exact hrewrite ▸ hmul
  · have hcorr :
        ((degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a : 𝒜 0) : S) =
          (a : S) ^ Int.toNat d * (f : S) ^ Int.toNat (-i) := by
      -- In the negative-degree branch the correction uses the positive-degree unit `f`.
      simp [degree_zero_corrected_component, degree_zero_correction, hi]
    rw [hcorr] at hcorr_mem
    have hmul : ((a : S) ^ Int.toNat d * (f : S) ^ Int.toNat (-i)) * (g : S) ^ Int.toNat (-i) ∈ J := by
      exact Ideal.mul_mem_right ((g : S) ^ Int.toNat (-i)) J hcorr_mem
    have hcancel : (f : S) ^ Int.toNat (-i) * (g : S) ^ Int.toNat (-i) = 1 :=
      homogeneous_unit_natpow_cancel (a := (f : S)) (b := (g : S)) hfg (Int.toNat (-i))
    -- The same reassociation now cancels the positive-degree unit powers.
    have hrewrite :
        ((a : S) ^ Int.toNat d * (f : S) ^ Int.toNat (-i)) * (g : S) ^ Int.toNat (-i) =
          (a : S) ^ Int.toNat d := by
      calc
        ((a : S) ^ Int.toNat d * (f : S) ^ Int.toNat (-i)) * (g : S) ^ Int.toNat (-i) =
            (a : S) ^ Int.toNat d * ((f : S) ^ Int.toNat (-i) * (g : S) ^ Int.toNat (-i)) := by
              ring_nf
        _ = (a : S) ^ Int.toNat d * 1 := by
              rw [hcancel]
        _ = (a : S) ^ Int.toNat d := by
              simp
    exact hrewrite ▸ hmul

/-- Helper for Lemma 10.57.2: if a homogeneous element lies in `𝔭₀S`, then its corrected
degree-zero term lies in `𝔭₀`. -/
lemma degree_zero_corrected_component_mem_of_extension_mem
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) (p₀ : PrimeSpectrum (𝒜 0))
    {i : ℤ} (a : 𝒜 i)
    (ha : (a : S) ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀) :
    degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a ∈ p₀.asIdeal := by
  let J := degree_zero_extension_ideal (𝒜 := 𝒜) p₀
  have hd_nat : 0 < Int.toNat d := by
    omega
  have hpow : (a : S) ^ Int.toNat d ∈ J := by
    -- Start from the given homogeneous element in `J` and pass to the positive power used in the
    -- source correction term.
    exact J.pow_mem_of_mem ha _ hd_nat
  have hcorr_mem :
      ((degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a : 𝒜 0) : S) ∈ J := by
    by_cases hi : 0 ≤ i
    · -- In the nonnegative branch, the correction multiplies by a power of the inverse component.
      rw [show ((degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a : 𝒜 0) : S) =
          (a : S) ^ Int.toNat d * (g : S) ^ Int.toNat i by
            simp [degree_zero_corrected_component, degree_zero_correction, hi]]
      exact Ideal.mul_mem_right ((g : S) ^ Int.toNat i) J hpow
    · -- In the negative branch, the correction multiplies by a power of the positive-degree unit.
      rw [show ((degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a : 𝒜 0) : S) =
          (a : S) ^ Int.toNat d * (f : S) ^ Int.toNat (-i) by
            simp [degree_zero_corrected_component, degree_zero_correction, hi]]
      exact Ideal.mul_mem_right ((f : S) ^ Int.toNat (-i)) J hpow
  -- Contract the degree-zero corrected term from `𝔭₀S` back to `𝔭₀`.
  exact (degree_zero_extension_ideal_mem_iff_of_mem_zero (𝒜 := 𝒜) p₀
    (degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a)).mp hcorr_mem

/-- Helper for Lemma 10.57.2: on degree-zero elements, the corrected-carrier condition reduces to
the original prime `𝔭₀` by primality and positive powers. -/
lemma degree_zero_extension_carrier_mem_iff_of_mem_zero
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d)) (p₀ : PrimeSpectrum (𝒜 0)) (x : 𝒜 0) :
    (x : S) ∈ degree_zero_extension_carrier (𝒜 := 𝒜) (d := d) hd f g p₀ ↔ x ∈ p₀.asIdeal := by
  have hd_nat : 0 < Int.toNat d := by
    omega
  have hcorr :
      degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g 0 x = x ^ Int.toNat d := by
    -- In degree zero the corrected component is exactly the positive power in `S₀`.
    apply Subtype.ext
    simp [degree_zero_corrected_component, degree_zero_correction_eq_pow]
  -- The already-proved homogeneous carrier criterion becomes the prime-ideal power test.
  rw [degree_zero_extension_mem_iff_of_mem (𝒜 := 𝒜) (d := d) hd f g p₀ x.2, hcorr]
  exact p₀.2.pow_mem_iff_mem (r := x) _ hd_nat

/-- Helper for Lemma 10.57.2: the degree-zero correction is multiplicative on homogeneous
products. -/
lemma degree_zero_correction_mul
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d))
    (hfg : (f : S) * (g : S) = 1) {i j : ℤ} (a : 𝒜 i) (b : 𝒜 j) :
    degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g (i + j)
        ⟨(a : S) * (b : S), SetLike.mul_mem_graded a.2 b.2⟩ =
      degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g i a *
        degree_zero_corrected_component (𝒜 := 𝒜) (d := d) hd f g j b := by
  -- TODO: prove the source-faithful multiplicativity formula by splitting on the signs of `i`,
  -- `j`, and `i + j`, then cancelling the matching powers of the homogeneous unit and its inverse.
  sorry

/-- Helper for Lemma 10.57.2: if a corrected homogeneous product lands in `𝔭₀`, then one of the
source-faithful powers already lies in `𝔭₀S`. -/
lemma degree_zero_extension_mul_mem_or_mem_pow
    {d : ℤ} (hd : 0 < d) (f : 𝒜 d) (g : 𝒜 (-d))
    (hfg : (f : S) * (g : S) = 1) (p₀ : PrimeSpectrum (𝒜 0))
    {i j : ℤ} (a : 𝒜 i) (b : 𝒜 j)
    (hab : ((a : S) * (b : S)) ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀) :
    (a : S) ^ Int.toNat d ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀ ∨
      (b : S) ^ Int.toNat d ∈ degree_zero_extension_ideal (𝒜 := 𝒜) p₀ := by
  -- TODO: contract the corrected homogeneous product to `𝔭₀`, rewrite it with
  -- `degree_zero_correction_mul`, and apply primality of `𝔭₀` to lift one branch back to `𝔭₀S`.
  sorry

/-- Helper for Lemma 10.57.2: the radical `√(𝔭₀S)` is prime because homogeneous products landing
in `𝔭₀S` force a source-faithful power into `𝔭₀S`. -/
lemma degree_zero_extension_radical_prime
    (hunit : ∃ d > 0, ∃ f : 𝒜 d, IsUnit (f : S)) (p₀ : PrimeSpectrum (𝒜 0)) :
    (degree_zero_extension_ideal (𝒜 := 𝒜) p₀).radical.IsPrime := by
  -- TODO: combine the homogeneous product-power lemma with
  -- `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`.
  sorry

/-- Helper for Lemma 10.57.2: for a homogeneous prime `𝔭`, homogeneous membership in the radical
extension of its contraction to degree zero is equivalent to homogeneous membership in `𝔭`. -/
lemma degree_zero_extension_radical_mem_iff_of_mem
    (hunit : ∃ d > 0, ∃ f : 𝒜 d, IsUnit (f : S))
    (p : { q : PrimeSpectrum S // q.asIdeal.IsHomogeneous 𝒜 })
    {i : ℤ} (a : 𝒜 i) :
    let p₀ :=
      (((comap (algebraMap (𝒜 0) S)) ∘
          (Subtype.val : { q : PrimeSpectrum S // q.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) p)
    (a : S) ∈ (degree_zero_extension_ideal (𝒜 := 𝒜) p₀).radical ↔ (a : S) ∈ p.1.asIdeal := by
  -- TODO: forward uses `map_comap_le` and radical monotonicity; reverse uses the corrected
  -- degree-zero term together with `degree_zero_extension_pow_mem_of_corrected_mem`.
  sorry

/-- Helper for Lemma 10.57.2: the source-faithful inverse sends `𝔭₀` to `√(𝔭₀S)` viewed as a
homogeneous prime ideal of `S`. -/
noncomputable def degree_zero_extension_point
    (hunit : ∃ d > 0, ∃ f : 𝒜 d, IsUnit (f : S)) :
    PrimeSpectrum (𝒜 0) → { p : PrimeSpectrum S // p.asIdeal.IsHomogeneous 𝒜 } :=
  fun p₀ =>
    ⟨⟨(degree_zero_extension_ideal (𝒜 := 𝒜) p₀).radical,
        degree_zero_extension_radical_prime (𝒜 := 𝒜) hunit p₀⟩,
      (degree_zero_extension_ideal_isHomogeneous (𝒜 := 𝒜) p₀).radical⟩

/-- Helper for Lemma 10.57.2: contracting `√(𝔭₀S)` back to degree zero recovers `𝔭₀`. -/
lemma restricted_comap_left_inverse
    (hunit : ∃ d > 0, ∃ f : 𝒜 d, IsUnit (f : S))
    (p₀ : PrimeSpectrum (𝒜 0)) :
    ((comap (algebraMap (𝒜 0) S)) ∘
        (Subtype.val : { p : PrimeSpectrum S // p.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S))
      (degree_zero_extension_point (𝒜 := 𝒜) hunit p₀) =
        p₀ := by
  -- The inverse really is `𝔭₀ ↦ √(𝔭₀S)`, so contraction is just `comap_radical` plus
  -- the already-settled identity `𝔭₀S ∩ S₀ = 𝔭₀`.
  apply PrimeSpectrum.ext
  simp [degree_zero_extension_point, PrimeSpectrum.comap_asIdeal, Ideal.comap_radical,
    degree_zero_extension_ideal_comap, p₀.2.radical]

/-- Helper for Lemma 10.57.2: for a homogeneous prime `𝔭`, extending and then taking radicals from
its contraction to degree zero returns `𝔭`. -/
lemma degree_zero_extension_right_inverse
    (hunit : ∃ d > 0, ∃ f : 𝒜 d, IsUnit (f : S))
    (p : { q : PrimeSpectrum S // q.asIdeal.IsHomogeneous 𝒜 }) :
    degree_zero_extension_point (𝒜 := 𝒜) hunit
      (((comap (algebraMap (𝒜 0) S)) ∘
          (Subtype.val : { q : PrimeSpectrum S // q.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) p) =
        p := by
  let p₀ :=
    (((comap (algebraMap (𝒜 0) S)) ∘
        (Subtype.val : { q : PrimeSpectrum S // q.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) p)
  apply Subtype.ext
  apply PrimeSpectrum.ext
  ext x
  -- Compare the two homogeneous ideals componentwise, then use the homogeneous iff-criterion.
  change x ∈ (degree_zero_extension_ideal (𝒜 := 𝒜) p₀).radical ↔ x ∈ p.1.asIdeal
  rw [Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜)
      ((degree_zero_extension_ideal_isHomogeneous (𝒜 := 𝒜) p₀).radical),
    Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜) p.2]
  constructor
  · intro hx i
    simpa [p₀] using
      (degree_zero_extension_radical_mem_iff_of_mem (𝒜 := 𝒜) hunit p
        (a := DirectSum.decompose 𝒜 x i)).mp (hx i)
  · intro hx i
    simpa [p₀] using
      (degree_zero_extension_radical_mem_iff_of_mem (𝒜 := 𝒜) hunit p
        (a := DirectSum.decompose 𝒜 x i)).mpr (hx i)

/-- Helper for Lemma 10.57.2: the restricted contraction map is open because the image of each
subtype basic open `G ∩ D(g)` is a union of basic opens on `Spec(S₀)` coming from the corrected
homogeneous components of `g`. -/
lemma isOpenMap_restricted_comap
    (hunit : ∃ d > 0, ∃ f : 𝒜 d, IsUnit (f : S)) :
    IsOpenMap
      ((comap (algebraMap (𝒜 0) S)) ∘
        (Subtype.val : { p : PrimeSpectrum S // p.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) :=
  by
  -- TODO: for `g = ∑ gᵢ`, show the image of the subtype basic open `G ∩ D(g)` is the finite union
  -- of the basic opens defined by the corrected degree-zero components attached to the support of
  -- `DirectSum.decompose 𝒜 g`.
  sorry

/- Domain triage:
* primary domain: graded commutative algebra and spectral maps on homogeneous-prime loci;
* sampled declarations:
  `Ideal.IsHomogeneous`,
  `HomogeneousIdeal`,
  `GradedRing.projZeroRingHom'`,
  `PrimeSpectrum.isHomeomorph_comap`;
* best owner abstraction: the canonical spectrum map `comap (algebraMap (𝒜 0) S)`;
* layer: `bridge/view`;
* primitive data: the subtype `{ p : PrimeSpectrum S // p.asIdeal.IsHomogeneous 𝒜 }`;
* derived API: the restriction of `comap (algebraMap (𝒜 0) S)` along the subtype coercion.
-/

/-- Lemma 10.57.2 (Stacks, Tag `00JO`): if a `ℤ`-graded ring contains a homogeneous invertible
element in some positive degree, then the restriction of `PrimeSpectrum.comap` along
`algebraMap (𝒜 0) S` to the subtype of homogeneous prime ideals is a homeomorphism. The source
carries the induced topology from `Spec(S)`. -/
-- Proof sketch: this is the restriction of `PrimeSpectrum.comap` along `algebraMap (𝒜 0) S`.
-- For a prime `𝔭₀ ⊆ 𝒜 0`, the proof of Tag `00JO` constructs the inverse by sending
-- `𝔭₀` to `√(𝔭₀S)`, which is homogeneous and prime because a positive-degree homogeneous unit
-- lets one compare degrees with degree zero. To prove openness, if `g = ∑ gᵢ`, then the image of
-- `G ∩ D(g)` is `⋃ᵢ D(gᵢ^d / f^i)` in `Spec (𝒜 0)`.
@[stacks 00JO]
theorem Lemma_10_57_2
    (hunit : ∃ d > 0, ∃ f : 𝒜 d, IsUnit (f : S)) :
    IsHomeomorph
      ((comap (algebraMap (𝒜 0) S)) ∘
        (Subtype.val : { p : PrimeSpectrum S // p.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) := by
  classical
  -- Route correction: use the source-faithful inverse `𝔭₀ ↦ √(𝔭₀S)` rather than the false route
  -- of applying `PrimeSpectrum.isHomeomorph_comap` to all of `Spec(S)`.
  refine ⟨continuous_restricted_comap (𝒜 := 𝒜), isOpenMap_restricted_comap (𝒜 := 𝒜) hunit, ?_⟩
  constructor
  · intro p q hpq
    -- The right-inverse identity turns equality after contraction into equality of homogeneous
    -- primes upstairs.
    calc
      p =
          degree_zero_extension_point (𝒜 := 𝒜) hunit
            (((comap (algebraMap (𝒜 0) S)) ∘
                (Subtype.val :
                  { q : PrimeSpectrum S // q.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) p) := by
            symm
            exact degree_zero_extension_right_inverse (𝒜 := 𝒜) hunit p
      _ =
          degree_zero_extension_point (𝒜 := 𝒜) hunit
            (((comap (algebraMap (𝒜 0) S)) ∘
                (Subtype.val :
                  { q : PrimeSpectrum S // q.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) q) := by
            rw [hpq]
      _ = q := degree_zero_extension_right_inverse (𝒜 := 𝒜) hunit q
  · intro p₀
    -- The left-inverse identity gives a preimage for every degree-zero prime.
    refine ⟨degree_zero_extension_point (𝒜 := 𝒜) hunit p₀, ?_⟩
    exact restricted_comap_left_inverse (𝒜 := 𝒜) hunit p₀

end

/-! ### Lemma_10_57_3_Topology_on_Proj (from Chap10) -/
open AlgebraicGeometry ProjectiveSpectrum

noncomputable section

universe u v

section ProjectiveSpectrumTopology

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain triage: this file lies in graded commutative algebra and projective-spectrum topology.
the topological owner abstraction is `ProjectiveSpectrum 𝒜`, and its Zariski-topology API already
lives canonically under the weaker `[AddSubmonoidClass σ A]` assumptions. The stronger
scheme-level basic-open charts live on `Proj 𝒜` and are kept in a separate section below. The
non-recall lemmas here are source-facing bridges derived from the owner API rather than parallel
wrapper declarations. -/

/- The subset `D₊(f)` is open in `Proj(S)`. This is `ProjectiveSpectrum.isOpen_basicOpen`. -/
recall ProjectiveSpectrum.isOpen_basicOpen

variable (I : HomogeneousIdeal 𝒜)

/- The subsets `V₊(I)` are closed in `Proj(S)`. This is `ProjectiveSpectrum.isClosed_zeroLocus`
applied to a homogeneous ideal. -/
recall ProjectiveSpectrum.isClosed_zeroLocus

/- Closed subsets of `Proj(S)` are exactly zero loci of subsets of `A`. This is the owner theorem
`ProjectiveSpectrum.isClosed_iff_zeroLocus`. -/
recall ProjectiveSpectrum.isClosed_iff_zeroLocus

/-- A subset of `Proj(S)` is closed exactly when it is the zero locus of its vanishing ideal. -/
theorem isClosed_iff_eq_zeroLocus_vanishingIdeal (T : Set (ProjectiveSpectrum 𝒜)) :
    IsClosed T ↔ T = zeroLocus 𝒜 (vanishingIdeal T : Set A) := by
  constructor
  · intro hT
    simpa [hT.closure_eq] using (zeroLocus_vanishingIdeal_eq_closure 𝒜 T).symm
  · intro hT
    rw [hT]
    exact isClosed_zeroLocus 𝒜 (vanishingIdeal T : Set A)

/-- Every closed subset of `Proj(S)` is the zero locus of a homogeneous ideal. -/
-- Proof sketch: apply `isClosed_iff_eq_zeroLocus_vanishingIdeal` and use the canonical
-- homogeneous ideal `vanishingIdeal T`.
theorem isClosed_iff_exists_zeroLocus_homogeneousIdeal (T : Set (ProjectiveSpectrum 𝒜)) :
    IsClosed T ↔ ∃ I : HomogeneousIdeal 𝒜, T = zeroLocus 𝒜 (I : Set A) := by
  constructor
  · intro hT
    exact ⟨vanishingIdeal T, (isClosed_iff_eq_zeroLocus_vanishingIdeal 𝒜 T).mp hT⟩
  · rintro ⟨I, rfl⟩
    simpa using isClosed_zeroLocus 𝒜 (I : Set A)

/-- The zero locus of a homogeneous ideal is empty exactly when its radical contains the irrelevant
ideal. -/
-- Proof sketch: if the irrelevant ideal lies in `√I`, then no relevant homogeneous prime contains
-- `I`. Conversely, if `V₊(I)` is empty and some positive-degree homogeneous element is not in
-- `√I`, localize away from it and use the affine chart together with the existence of a prime in a
-- nonzero localization to construct a point of `Proj(S)` containing `I`.
theorem zeroLocus_eq_empty_iff_irrelevant_le_radical :
    zeroLocus 𝒜 (I : Set A) = ∅ ↔
      HomogeneousIdeal.irrelevant 𝒜 ≤ I.radical := sorry

end ProjectiveSpectrumTopology

section ProjBasicOpens

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- The scheme-level basis and chart constructions are owned by `Proj 𝒜`; this section keeps the
stronger `[AddSubgroupClass σ A]` context exactly where the scheme API needs it. -/

/- Lemma 10.57.3 (Topology on Proj): the standard opens `D₊(f)` form a basis for the topology on
`Proj(S)`. This is the canonical mathlib theorem `AlgebraicGeometry.Proj.isBasis_basicOpen`. -/
recall Proj.isBasis_basicOpen

/- The standard opens satisfy `D₊(fg) = D₊(f) ∩ D₊(g)`. This is
`AlgebraicGeometry.Proj.basicOpen_mul`. -/
recall Proj.basicOpen_mul

/-- Separating the degree-zero and positive-degree pieces of a basic open. -/
-- Proof sketch: start from `Proj.basicOpen_eq_iSup_proj 𝒜 g`, isolate the `i = 0` summand, and
-- reindex the remaining supremum by the subtype of positive degrees.
theorem proj_basicOpen_eq_projZero_sup_iSup_pos (g : A) :
    Proj.basicOpen 𝒜 g =
      Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) := sorry

/-- A degree-zero basic open is the union of the positive-degree charts cut out by its multiples. -/
-- Proof sketch: the right-hand side is contained in `D₊(g₀)` by `Proj.basicOpen_mono`. For the
-- converse, if `g₀ ∉ p`, use that `p` is relevant to choose a positive-degree homogeneous element
-- outside `p`; then its product with `g₀` is still outside `p`.
theorem proj_basicOpen_degreeZero_eq_iSup_mul (g₀ : 𝒜 0) :
    Proj.basicOpen 𝒜 (g₀ : A) =
      ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1, Proj.basicOpen 𝒜 ((g₀ : A) * (f : A)) := sorry

/- For a homogeneous element of positive degree, the affine chart `D₊(f)` is canonically
isomorphic to `Spec(S_(f))`. This is `AlgebraicGeometry.Proj.basicOpenIsoSpec`. -/
recall Proj.basicOpenIsoSpec

end ProjBasicOpens

/-! ### Example_10_57_4 (from Chap10) -/
open scoped DirectSum
open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace Polynomial

variable (R : Type u) [CommRing R]

/-- The standard `ℕ`-grading on `R[X]`, transported from the canonical grading on the additive
monoid algebra model `R[ℕ]` via `Polynomial.toFinsuppIsoLinear`. -/
abbrev standardGrading (n : ℕ) : Submodule R R[X] :=
  Submodule.map (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap (AddMonoidAlgebra.grade R n)

instance instSetLikeGradedMonoidStandardGrading : SetLike.GradedMonoid (standardGrading R) where
  one_mem := by
    refine ⟨AddMonoidAlgebra.single 0 (1 : R), AddMonoidAlgebra.single_mem_grade 0 1, ?_⟩
    ext n
    change
      ((Polynomial.toFinsuppIso R).symm (AddMonoidAlgebra.single 0 (1 : R))).coeff n =
        (1 : R[X]).coeff n
    rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.single_apply]
    simp [coeff_one, eq_comm]
  mul_mem {i j} a b ha hb := by
    rcases ha with ⟨a', ha', rfl⟩
    rcases hb with ⟨b', hb', rfl⟩
    refine ⟨a' * b', SetLike.mul_mem_graded ha' hb', ?_⟩
    ext n
    exact congrArg (fun p : R[X] ↦ p.coeff n) ((Polynomial.toFinsuppIso R).symm.map_mul a' b')

/-- Helper for Example 10.57.4: a homogeneous polynomial of degree `n` in the standard grading
is a scalar multiple of `X ^ n`. -/
theorem standardGrading_eq_C_mul_X_pow_of_mem {n : ℕ} {f : R[X]}
    (hf : f ∈ standardGrading R n) :
    f = Polynomial.C (f.coeff n) * Polynomial.X ^ n := by
  rcases hf with ⟨g, hg, rfl⟩
  -- Compare coefficients: outside degree `n` everything vanishes, and at degree `n` we keep
  -- exactly the `n`-th coefficient.
  ext i
  change ((Polynomial.toFinsuppIso R).symm g).coeff i =
    (Polynomial.C (((Polynomial.toFinsuppIso R).symm g).coeff n) * Polynomial.X ^ n).coeff i
  rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  by_cases hi : i = n
  · subst hi
    simp
  · have hmem := (AddMonoidAlgebra.mem_grade_iff R n g).mp hg
    have hnot : i ∉ g.support := by
      intro hi_support
      exact hi (by simpa using hmem hi_support)
    have hgi : g i = 0 := Finsupp.notMem_support_iff.mp hnot
    have hni : ¬n = i := by simpa [eq_comm] using hi
    simp [hgi, hni]

/-- Helper for Example 10.57.4: the `n`-th graded piece of the standard grading is canonically a
copy of `R`, represented by the monomial `a X^n`. -/
private noncomputable def standardGradingCoeffEquiv (n : ℕ) :
    R ≃ₗ[R] standardGrading R n where
  toFun a := by
    refine ⟨Polynomial.C a * Polynomial.X ^ n, ?_⟩
    refine ⟨AddMonoidAlgebra.single n a, AddMonoidAlgebra.single_mem_grade n a, ?_⟩
    ext i
    change ((Polynomial.toFinsuppIso R).symm (AddMonoidAlgebra.single n a)).coeff i =
      (Polynomial.C a * Polynomial.X ^ n).coeff i
    rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp,
      Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, AddMonoidAlgebra.single_apply]
  invFun f := f.1.coeff n
  left_inv a := by
    simp
  right_inv f := by
    apply Subtype.ext
    exact (Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R f.2).symm
  map_add' a b := by
    apply Subtype.ext
    simp [add_mul]
  map_smul' c a := by
    apply Subtype.ext
    simp [Algebra.smul_def, mul_assoc]

/-- Helper for Example 10.57.4: the coefficient representation identifies `R[X]` with the direct
sum of its standard graded pieces. -/
private noncomputable def standardGradingComponentEquiv (n : ℕ) :
    AddMonoidAlgebra.grade R n ≃ₗ[R] standardGrading R n :=
  Submodule.equivMapOfInjective (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap
    (Polynomial.toFinsuppIsoLinear R).symm.injective (AddMonoidAlgebra.grade R n)

/-- Helper for Example 10.57.4: the standard grading inherits the canonical decomposition of the
additive monoid algebra grading through `Polynomial.toFinsuppIsoLinear`. -/
private noncomputable abbrev standardGradingDecomposeLinearEquiv :
    R[X] ≃ₗ[R] ⨁ n, standardGrading R n :=
  (Polynomial.toFinsuppIsoLinear R).trans <|
    (DirectSum.decomposeLinearEquiv (AddMonoidAlgebra.grade R : ℕ → Submodule R _)).trans <|
      DirectSum.congrLinearEquiv fun n ↦ standardGradingComponentEquiv R n

/-- Helper for Example 10.57.4: the inverse of the transported decomposition is the canonical
recomposition map from the direct sum of graded pieces. -/
private theorem standardGradingDecomposeLinearEquiv_symm_eq_coe :
    (standardGradingDecomposeLinearEquiv R).symm.toLinearMap =
      DirectSum.coeLinearMap (standardGrading R) := by
  apply DirectSum.linearMap_ext
  intro n
  ext x i
  have hx :
      (standardGradingDecomposeLinearEquiv R).symm
          ((DirectSum.lof R ℕ (fun j ↦ ↥(standardGrading R j)) n) x) = x := by
    have hcongr :
        ((DirectSum.congrLinearEquiv fun j ↦ standardGradingComponentEquiv R j).symm
            ((DirectSum.lof R ℕ (fun j ↦ ↥(standardGrading R j)) n) x)) =
          DirectSum.lof R ℕ (fun j ↦ ↥(AddMonoidAlgebra.grade R j)) n
            ((standardGradingComponentEquiv R n).symm x) := by
      change DirectSum.lmap (fun j ↦ (standardGradingComponentEquiv R j).symm.toLinearMap)
          ((DirectSum.lof R ℕ (fun j ↦ ↥(standardGrading R j)) n) x) =
        DirectSum.lof R ℕ (fun j ↦ ↥(AddMonoidAlgebra.grade R j)) n
          ((standardGradingComponentEquiv R n).symm x)
      simpa using
        (DirectSum.lmap_lof (R := R)
          (f := fun j ↦ (standardGradingComponentEquiv R j).symm.toLinearMap) n x)
    change
      (Polynomial.toFinsuppIsoLinear R).symm
          (((DirectSum.decomposeLinearEquiv (AddMonoidAlgebra.grade R)).symm
              ((DirectSum.congrLinearEquiv fun j ↦ standardGradingComponentEquiv R j).symm
                ((DirectSum.lof R ℕ (fun j ↦ ↥(standardGrading R j)) n) x))) :
            AddMonoidAlgebra R ℕ) = x
    rw [hcongr]
    rw [DirectSum.decomposeLinearEquiv_symm_lof]
    exact Submodule.map_equivMapOfInjective_symm_apply
      (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap
      (Polynomial.toFinsuppIsoLinear R).symm.injective (AddMonoidAlgebra.grade R n) x
  simpa using congrArg (fun p : Polynomial R ↦ p.coeff i) hx

theorem standardGrading_isInternal : DirectSum.IsInternal (standardGrading R) := by
  unfold DirectSum.IsInternal
  change Function.Bijective (DirectSum.coeLinearMap (standardGrading R))
  rw [← standardGradingDecomposeLinearEquiv_symm_eq_coe R]
  exact ⟨(standardGradingDecomposeLinearEquiv R).symm.injective,
    (standardGradingDecomposeLinearEquiv R).symm.surjective⟩

instance instGradedAlgebraStandardGrading : GradedAlgebra (standardGrading R) :=
  DirectSum.IsInternal.gradedAlgebra (standardGrading_isInternal R)

/-- Helper for Example 10.57.4: the chosen decomposition sends a polynomial to its monomial
homogeneous pieces. -/
theorem standardGrading_decompose_eq_C_coeff_mul_X_pow (f : R[X]) (n : ℕ) :
    ((DirectSum.decompose (standardGrading R) f) n : Polynomial R) =
      Polynomial.C (f.coeff n) * Polynomial.X ^ n := by
  classical
  have hsum :
      (∑ i ∈ DFinsupp.support (DirectSum.decompose (standardGrading R) f),
          (((DirectSum.decompose (standardGrading R) f) i : Polynomial R).coeff n)) = f.coeff n := by
    simpa [Polynomial.coeff_sum] using
      congrArg (fun p : Polynomial R ↦ p.coeff n)
        (DirectSum.sum_support_decompose (standardGrading R) f)
  have hcoeff :
      (((DirectSum.decompose (standardGrading R) f) n : Polynomial R).coeff n) = f.coeff n := by
    rw [Finset.sum_eq_single n ?_ ?_] at hsum
    · simpa using hsum
    · intro j hj hjn
      have hzero :
          (((DirectSum.decompose (standardGrading R) f) j : Polynomial R).coeff n) = 0 := by
        have hmono :=
          Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R
            (DirectSum.decompose (standardGrading R) f j).2
        rw [hmono]
        rw [Polynomial.coeff_C_mul_X_pow]
        simpa [hjn.symm] using (if_neg (h := hjn.symm) :
          (if n = j then (↑((DirectSum.decompose (standardGrading R) f j)).coeff j) else 0) = 0)
      simp [hzero]
    · intro hn
      have hzero : DirectSum.decompose (standardGrading R) f n = 0 :=
        DFinsupp.notMem_support_iff.mp hn
      have hzero' : ((DirectSum.decompose (standardGrading R) f n : standardGrading R n) :
          Polynomial R) = 0 := by
        simpa using congrArg Subtype.val hzero
      simp [hzero']
  have hmono :=
    Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R
      (DirectSum.decompose (standardGrading R) f n).2
  rw [hmono]
  simp [hcoeff]

/-- The degree-zero piece of the standard grading is canonically `R`, via constant polynomials. -/
private theorem eq_single_zero_of_mem_grade_zero {x : AddMonoidAlgebra R ℕ}
    (hx : x ∈ AddMonoidAlgebra.grade R 0) :
    x = AddMonoidAlgebra.single 0 (x 0) := by
  ext n
  by_cases hn : n = 0
  · subst hn
    simp
  · have hx' := (AddMonoidAlgebra.mem_grade_iff R 0 x).mp hx
    have hnot : n ∉ x.support := by
      intro hn'
      exact hn (by simpa using hx' hn')
    simp [hn, Finsupp.notMem_support_iff.mp hnot]

private noncomputable def addMonoidAlgebraGradeZeroRingEquiv :
    ↥(AddMonoidAlgebra.grade R 0) ≃+* R where
  toFun x := x.1 0
  invFun r := ⟨AddMonoidAlgebra.single 0 r, AddMonoidAlgebra.single_mem_grade 0 r⟩
  left_inv x := by
    apply Subtype.ext
    exact (eq_single_zero_of_mem_grade_zero R x.2).symm
  right_inv r := by
    simp
  map_mul' x y := by
    change (x.1 * y.1) 0 = x.1 0 * y.1 0
    rw [eq_single_zero_of_mem_grade_zero R x.2, eq_single_zero_of_mem_grade_zero R y.2]
    simp
  map_add' x y := by
    simp

private noncomputable def standardGradingDegreeZeroToAddMonoidAlgebra :
    ↥(standardGrading R 0) ≃+* ↥(AddMonoidAlgebra.grade R 0) where
  toFun p := by
    refine ⟨Polynomial.toFinsuppIso R p.1, ?_⟩
    rcases p.2 with ⟨q, hq, hq'⟩
    have h : q = Polynomial.toFinsuppIso R p.1 := by
      simpa using congrArg (Polynomial.toFinsuppIso R) hq'
    simpa [h] using hq
  invFun q := ⟨(Polynomial.toFinsuppIso R).symm q.1, ⟨q.1, q.2, rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp
  map_mul' p q := by
    rfl
  map_add' p q := by
    rfl

private noncomputable def standardGradingDegreeZeroRingEquiv : ↥(standardGrading R 0) ≃+* R :=
  (standardGradingDegreeZeroToAddMonoidAlgebra R).trans (addMonoidAlgebraGradeZeroRingEquiv R)

end Polynomial

section

variable (R : Type u) [CommRing R]

local notation "𝒮" => Polynomial.standardGrading R

private noncomputable def standardGradingDegreeZeroSpecIso :
    Spec (.of ↥(𝒮 0)) ≅ Spec (.of R) :=
  (Scheme.Spec.mapIso (Polynomial.standardGradingDegreeZeroRingEquiv R).toCommRingCatIso.op).symm

/-- Helper for Example 10.57.4: the polynomial `X` is homogeneous of degree `1` for the standard
grading. -/
private theorem standardGrading_X_mem : (Polynomial.X : Polynomial R) ∈ 𝒮 1 := by
  refine ⟨AddMonoidAlgebra.single 1 (1 : R), AddMonoidAlgebra.single_mem_grade 1 1, ?_⟩
  ext n
  change
    ((Polynomial.toFinsuppIso R).symm (AddMonoidAlgebra.single 1 (1 : R))).coeff n =
      Polynomial.X.coeff n
  rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.single_apply]
  by_cases hn : n = 1
  · subst hn
    simp
  · simp [Polynomial.coeff_X]

/-- Helper for Example 10.57.4: every positive-degree homogeneous polynomial is divisible by `X`,
so the irrelevant ideal lies in `(X)`. -/
private theorem standardGrading_irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤
      Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)) := by
  refine (HomogeneousIdeal.toIdeal_irrelevant_le (𝒜 := 𝒮)
    (I := Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)))).2 ?_
  intro i hi f hf
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi) with ⟨n, rfl⟩
  -- Rewrite a positive-degree homogeneous polynomial as a multiple of `X`.
  have hX : (Polynomial.X : Polynomial R) ∈
      Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)) :=
    Ideal.subset_span (by simp)
  have hmul :
      (Polynomial.C (f.coeff (Nat.succ n)) * Polynomial.X ^ n) * Polynomial.X ∈
        Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)) :=
    Ideal.mul_mem_left (Ideal.span ({(Polynomial.X : Polynomial R)} : Set (Polynomial R)))
      (Polynomial.C (f.coeff (Nat.succ n)) * Polynomial.X ^ n) hX
  rw [Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R hf, pow_succ]
  simpa [mul_assoc] using hmul

/-- Helper for Example 10.57.4: a relevant homogeneous prime of the standard grading cannot
contain `X`. -/
private theorem standardGrading_X_not_mem_asHomogeneousIdeal (p : ProjectiveSpectrum 𝒮) :
    (Polynomial.X : Polynomial R) ∉ p.asHomogeneousIdeal := by
  intro hX
  refine p.not_irrelevant_le ?_
  exact (standardGrading_irrelevant_le_span_X R).trans <| Ideal.span_le.mpr fun f hf ↦ by
    simpa [Set.mem_singleton_iff.mp hf] using hX

/-- Helper for Example 10.57.4: constant polynomials are exactly the degree-zero part of the
standard grading. -/
private theorem standardGrading_C_mem_zero (r : R) : Polynomial.C r ∈ 𝒮 0 := by
  simpa using SetLike.algebraMap_mem_graded (Polynomial.standardGrading R) r

/-- Helper for Example 10.57.4: the single chart `D₊(X)` already covers the whole projective
spectrum for the standard grading. -/
private theorem standard_grading_basicOpen_X_eq_top :
    Proj.basicOpen 𝒮 (Polynomial.X : Polynomial R) = ⊤ := by
  -- Check the defining condition of the basic open set pointwise.
  apply TopologicalSpace.Opens.ext
  ext p
  simp [standardGrading_X_not_mem_asHomogeneousIdeal]

/-- Helper for Example 10.57.4: a homogeneous fraction `a / X^n` in the unique chart is equal to
the constant fraction determined by the coefficient of `a` in degree `n`. -/
private theorem standard_grading_away_X_mk_eq_fromZeroRingHom
    (n : ℕ) (a : Polynomial R) (ha : a ∈ 𝒮 n) :
    HomogeneousLocalization.Away.mk 𝒮 (standardGrading_X_mem R) n a
        (by simpa [nsmul_eq_mul] using ha) =
      HomogeneousLocalization.fromZeroRingHom 𝒮 (Submonoid.powers (Polynomial.X : Polynomial R))
        ⟨Polynomial.C (a.coeff n), standardGrading_C_mem_zero R (a.coeff n)⟩ := by
  -- Compare both classes in the ordinary localization away from `X`.
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R ha,
    Localization.mk_eq_mk'_apply]
  -- After rewriting `a`, the numerator already has the form `C(a_n) * X^n`.
  have hrhs :
      ((HomogeneousLocalization.fromZeroRingHom 𝒮 (Submonoid.powers (Polynomial.X : Polynomial R)))
          ⟨Polynomial.C ((Polynomial.C (a.coeff n) * Polynomial.X ^ n).coeff n),
            standardGrading_C_mem_zero R ((Polynomial.C (a.coeff n) * Polynomial.X ^ n).coeff n)⟩).val =
        algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))
          (Polynomial.C (a.coeff n)) := by
    simpa [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk'_apply] using
      (IsLocalization.mk'_one (M := Submonoid.powers (Polynomial.X : Polynomial R))
        (S := Localization.Away (Polynomial.X : Polynomial R))
        (Polynomial.C (a.coeff n)))
  rw [hrhs]
  symm
  exact IsLocalization.eq_mk'_of_mul_eq (S := Localization.Away (Polynomial.X : Polynomial R))
    (z := Polynomial.C (a.coeff n)) (by simp)

/-- Helper for Example 10.57.4: every degree-zero class in `S[X]_X` comes from a constant
polynomial. -/
private theorem standard_grading_away_X_fromZeroRingHom_surjective :
    Function.Surjective
      (HomogeneousLocalization.fromZeroRingHom 𝒮
        (Submonoid.powers (Polynomial.X : Polynomial R))) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒮
    (standardGrading_X_mem R) z
  have ha' : a ∈ 𝒮 n := by
    simpa [nsmul_eq_mul] using ha
  -- Normalize the given fraction `a / X^n` to the constant fraction `C(a_n) / 1`.
  refine ⟨⟨Polynomial.C (a.coeff n), standardGrading_C_mem_zero R (a.coeff n)⟩, ?_⟩
  simpa using (standard_grading_away_X_mk_eq_fromZeroRingHom R n a ha').symm

/-- Helper for Example 10.57.4: multiplying a constant polynomial by `X^n` cannot annihilate it
unless the constant itself is zero. -/
private theorem X_pow_mul_C_eq_zero_iff (n : ℕ) (r : R) :
    Polynomial.X ^ n * Polynomial.C r = 0 ↔ r = 0 := by
  constructor
  · intro h
    have h' : Polynomial.C r * Polynomial.X ^ n = 0 := by
      rw [mul_comm] at h
      exact h
    have hcoeff := congrArg (fun p : Polynomial R ↦ p.coeff n) h'
    simpa [Polynomial.coeff_C_mul_X_pow] using hcoeff
  · intro hr
    simp [hr]

/-- Helper for Example 10.57.4: the chart map from the degree-zero piece into the localization
away from `X` is injective. -/
private theorem standard_grading_away_X_fromZeroRingHom_injective :
    Function.Injective
      (HomogeneousLocalization.fromZeroRingHom 𝒮
        (Submonoid.powers (Polynomial.X : Polynomial R))) := by
  intro a b hab
  apply Subtype.ext
  -- Rewrite equality of homogeneous fractions as equality in the ordinary localization.
  have hval := congrArg HomogeneousLocalization.val hab
  change
    Localization.mk a.1 (1 : Submonoid.powers (Polynomial.X : Polynomial R)) =
      Localization.mk b.1 (1 : Submonoid.powers (Polynomial.X : Polynomial R)) at hval
  have hmap :
      algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)) a.1 =
        algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)) b.1 := by
    rw [Localization.mk_one_eq_algebraMap, Localization.mk_one_eq_algebraMap] at hval
    exact hval
  have hzero :
      algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)) (a.1 - b.1) =
        0 := by
    rw [map_sub, hmap, sub_self]
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (M := Submonoid.powers (Polynomial.X : Polynomial R))
    (S := Localization.Away (Polynomial.X : Polynomial R)) (a.1 - b.1)).mp hzero
  rcases m with ⟨m, hm_mem⟩
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff m (Polynomial.X : Polynomial R)).mp hm_mem
  have hconst : a.1 - b.1 ∈ 𝒮 0 := (𝒮 0).sub_mem a.2 b.2
  have hconst_eq :
      a.1 - b.1 = Polynomial.C ((a.1 - b.1).coeff 0) := by
    simpa using Polynomial.standardGrading_eq_C_mul_X_pow_of_mem R hconst
  have hcoeff_zero : (a.1 - b.1).coeff 0 = 0 := by
    -- Clear the localization denominator by a power of `X`, then inspect coefficient `n`.
    have hmul_zero :
        Polynomial.X ^ n * Polynomial.C ((a.1 - b.1).coeff 0) = 0 := by
      rw [hconst_eq] at hm
      exact hm
    exact (X_pow_mul_C_eq_zero_iff R n ((a.1 - b.1).coeff 0)).mp hmul_zero
  have hsub : a.1 - b.1 = 0 := by
    calc
      a.1 - b.1 = Polynomial.C ((a.1 - b.1).coeff 0) := hconst_eq
      _ = 0 := by simp [hcoeff_zero]
  exact sub_eq_zero.mp hsub

/-- Helper for Example 10.57.4: the degree-zero ring of the localization away from `X` is exactly
the degree-zero graded piece. -/
private noncomputable def standard_grading_away_X_equiv_degree_zero :
    HomogeneousLocalization.Away 𝒮 (Polynomial.X : Polynomial R) ≃+* ↥(𝒮 0) :=
  (RingEquiv.ofBijective
    (HomogeneousLocalization.fromZeroRingHom 𝒮
      (Submonoid.powers (Polynomial.X : Polynomial R)))
    ⟨standard_grading_away_X_fromZeroRingHom_injective R,
      standard_grading_away_X_fromZeroRingHom_surjective R⟩).symm

/-- Example 10.57.4 (1), map form: if `S = R[X]` with `deg(X) = 1`, then the natural map
`Proj(S) → Spec(R)` is the degree-zero structure morphism followed by the canonical identification
`Spec(S₀) ≅ Spec(R)`. -/
noncomputable def polynomial_standardGrading_toSpec :
    Proj 𝒮 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒮 ≫ (standardGradingDegreeZeroSpecIso R).hom

private instance : IsIso (Proj.toSpecZero 𝒮) := by
  let hm : 0 < (1 : ℕ) := zero_lt_one
  let e :
      ↥(𝒮 0) ≃+* HomogeneousLocalization.Away 𝒮 (Polynomial.X : Polynomial R) :=
    (standard_grading_away_X_equiv_degree_zero R).symm
  have haway_top :
      (Proj.awayι 𝒮 (Polynomial.X : Polynomial R) (standardGrading_X_mem R) hm).opensRange = ⊤ := by
    -- The single chart `D₊(X)` already covers the whole projective spectrum.
    rw [Proj.opensRange_awayι]
    exact standard_grading_basicOpen_X_eq_top R
  haveI :
      IsIso (Proj.awayι 𝒮 (Polynomial.X : Polynomial R) (standardGrading_X_mem R) hm) :=
    AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _ haway_top
  haveI :
      IsIso
        (Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom 𝒮
            (Submonoid.powers (Polynomial.X : Polynomial R))))) := by
    -- The chart ring is canonically identified with the degree-zero piece.
    simpa [e, standard_grading_away_X_equiv_degree_zero] using
      (inferInstance : IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom)
  let g : Spec (.of ↥(𝒮 0)) ⟶ Proj 𝒮 :=
    (asIso (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.fromZeroRingHom 𝒮
        (Submonoid.powers (Polynomial.X : Polynomial R)))))).inv ≫
      Proj.awayι 𝒮 (Polynomial.X : Polynomial R) (standardGrading_X_mem R) hm
  -- Route correction: use the single chart `D₊(X)=Proj`, then identify its coordinate ring with
  -- the degree-zero piece by the normalized-fraction equivalence above.
  refine isIso_of_hom_comp_eq_id g ?_
  simp [g, Proj.awayι_toSpecZero]

instance : IsIso (polynomial_standardGrading_toSpec R) := by
  change IsIso (Proj.toSpecZero 𝒮 ≫ (standardGradingDegreeZeroSpecIso R).hom)
  infer_instance

/-- Example 10.57.4 (1), canonical form: `Proj(R[X])` with `deg(X) = 1` is canonically isomorphic
to `Spec(R)`. -/
noncomputable def polynomial_standardGrading_isoSpec :
    Proj 𝒮 ≅ Spec (.of R) :=
  asIso (polynomial_standardGrading_toSpec R)

-- Example 10.57.4 (2): if `p` is a point of `Proj(R[X])` for the standard grading, equivalently a
-- relevant homogeneous prime ideal of `R[X]`, then `p` is the extension of its contraction to `R`.
-- Equivalently, for `p₀ = p ∩ R`, one has `p = p₀R[X]`.
-- Proof sketch: under `polynomial_standardGrading_isoSpec R`, the point `p` corresponds to its
-- contraction along `C : R →+* R[X]`, so its underlying ideal is the extension of that contracted
-- prime.
/-- Helper for Example 10.57.4: if a polynomial belongs to a projective point, then every
coefficient lies in the contracted prime of the base ring. -/
private theorem polynomial_standardGrading_coeff_mem_comap_of_mem_point
    (p : ProjectiveSpectrum 𝒮) {f : Polynomial R}
    (hf : f ∈ p.asHomogeneousIdeal.toIdeal) (n : ℕ) :
    f.coeff n ∈ Ideal.comap Polynomial.C p.asHomogeneousIdeal.toIdeal := by
  -- Homogeneity lets us test membership coefficientwise on the graded summands.
  have hcomp :
      ((DirectSum.decompose 𝒮 f) n : Polynomial R) ∈ p.asHomogeneousIdeal.toIdeal :=
    (Ideal.IsHomogeneous.mem_iff 𝒮 p.asHomogeneousIdeal.isHomogeneous).mp hf n
  rw [Polynomial.standardGrading_decompose_eq_C_coeff_mul_X_pow R f n] at hcomp
  have hprime : Ideal.IsPrime p.asHomogeneousIdeal.toIdeal := inferInstance
  have hXpow :
      (Polynomial.X : Polynomial R) ^ n ∉ p.asHomogeneousIdeal.toIdeal := by
    cases n with
    | zero =>
        have hne : p.asHomogeneousIdeal.toIdeal ≠ ⊤ := Ideal.IsPrime.ne_top (I := _) hprime
        simpa using (Ideal.ne_top_iff_one _).mp hne
    | succ k =>
        intro hpow
        have hX :
            (Polynomial.X : Polynomial R) ∈ p.asHomogeneousIdeal.toIdeal :=
          (Ideal.IsPrime.pow_mem_iff_mem (I := p.asHomogeneousIdeal.toIdeal)
            (r := (Polynomial.X : Polynomial R)) hprime (Nat.succ k) (Nat.succ_pos k)).mp hpow
        exact standardGrading_X_not_mem_asHomogeneousIdeal R p hX
  -- Primality removes the `X ^ n` factor, leaving only the constant coefficient.
  simpa [Ideal.mem_comap] using (hprime.mem_or_mem hcomp).resolve_right hXpow

theorem polynomial_standardGrading_point_asIdeal_eq_map_comap_C
    (p : ProjectiveSpectrum 𝒮) :
    p.asHomogeneousIdeal.toIdeal =
      Ideal.map Polynomial.C (Ideal.comap Polynomial.C p.asHomogeneousIdeal.toIdeal) := by
  apply le_antisymm
  · intro f hf
    -- Check membership in the extension ideal coefficientwise.
    rw [Ideal.mem_map_C_iff]
    intro n
    exact polynomial_standardGrading_coeff_mem_comap_of_mem_point R p hf n
  · -- Extension after contraction is always contained in the original ideal.
    exact Ideal.map_comap_le

end
