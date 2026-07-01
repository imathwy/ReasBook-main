import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

-- Declarations for this item will be appended below by the statement pipeline.

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
