import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_46_4 (from Chap10) -/
universe u v w

open scoped TensorProduct
open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

variable (f : R →+* S)

namespace RingHom

/-- Source-facing generator predicate for Lemma 10.46.4: `S` is generated as an `R`-algebra by
elements whose squares and cubes lie in the image of `f`. -/
def IsGeneratedBySquareCubeImage (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  Algebra.adjoin R {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range} = ⊤

end RingHom

/-- Helper for Lemma 10.46.4: in a field extension, an element whose square and cube come from the
base field already comes from the base field. -/
lemma mem_range_of_sq_mem_range_and_cube_mem_range
    {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] {a : L}
    (h2 : a ^ 2 ∈ Set.range (algebraMap K L))
    (h3 : a ^ 3 ∈ Set.range (algebraMap K L)) :
    a ∈ Set.range (algebraMap K L) := by
  by_cases ha : a = 0
  · -- Zero is always in the image of the algebra map.
    refine ⟨0, ?_⟩
    simp [ha]
  · rcases h2 with ⟨x, hx⟩
    rcases h3 with ⟨y, hy⟩
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have hx_ne_zero : x ≠ 0 := by
      intro hx_zero
      apply ha
      apply (pow_eq_zero_iff two_ne_zero).mp
      simpa [hx_zero] using hx.symm
    refine ⟨y * x⁻¹, ?_⟩
    calc
      algebraMap K L (y * x⁻¹) = algebraMap K L y * (algebraMap K L x)⁻¹ := by
        simp
      _ = a ^ 3 * (a ^ 2)⁻¹ := by
        rw [hy, hx]
      _ = a := by
        rw [pow_succ', mul_assoc, mul_inv_cancel₀ ha2, mul_one]

/-- Helper for Lemma 10.46.4: in a field, an element is determined by its square and cube. -/
lemma eq_of_sq_eq_sq_and_cube_eq_cube
    {K : Type*} [Field K] {a b : K}
    (h2 : a ^ 2 = b ^ 2) (h3 : a ^ 3 = b ^ 3) :
    a = b := by
  by_cases ha : a = 0
  · -- Vanishing of one side forces vanishing of the other side from the square identity.
    have hb : b = 0 := by
      apply (pow_eq_zero_iff two_ne_zero).mp
      simpa [ha] using h2.symm
    simpa [ha, hb]
  · have hb : b ≠ 0 := by
      intro hb
      apply ha
      apply (pow_eq_zero_iff two_ne_zero).mp
      simpa [hb] using h2
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
    calc
      a = a ^ 3 * (a ^ 2)⁻¹ := by
        rw [pow_succ', mul_assoc, mul_inv_cancel₀ ha2, mul_one]
      _ = b ^ 3 * (b ^ 2)⁻¹ := by
        rw [h3, h2]
      _ = b := by
        rw [pow_succ', mul_assoc, mul_inv_cancel₀ hb2, mul_one]

/-- Helper for Lemma 10.46.4: square/cube generators are integral, hence the whole extension is
integral. -/
lemma isIntegral_of_isGeneratedBySquareCubeImage
    (f : R →+* S) (hgen : f.IsGeneratedBySquareCubeImage) :
    f.IsIntegral := by
  let _ : Algebra R S := f.toAlgebra
  let G : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
  have hIntegralMap : (algebraMap R S).IsIntegral := by
    rw [algebraMap_isIntegral_iff]
    have hIntegralAdjoin : Algebra.IsIntegral R (Algebra.adjoin R G) := by
      -- Each chosen generator satisfies a monic quadratic equation over `R`.
      refine Algebra.IsIntegral.adjoin ?_
      intro x hx
      rcases hx with ⟨hx2, _hx3⟩
      rcases hx2 with ⟨r, hr⟩
      exact IsIntegral.of_pow (show 0 < 2 by decide) (hr ▸ isIntegral_algebraMap)
    have hgen' : Algebra.adjoin R G = ⊤ := by
      simpa [RingHom.IsGeneratedBySquareCubeImage, G] using hgen
    have hIntegralTop : Algebra.IsIntegral R (⊤ : Subalgebra R S) := by
      rw [← hgen']
      exact hIntegralAdjoin
    -- Remove the final coercion through the top subalgebra.
    exact (Subalgebra.topEquiv (R := R) (A := S)).isIntegral_iff.mp hIntegralTop
  simpa [RingHom.algebraMap_toAlgebra] using hIntegralMap

/-- Helper for Lemma 10.46.4: the image of `S / q` inside `κ(q)` is generated as a subring by the
image of `R` together with the chosen square/cube generators. -/
lemma residueField_image_range_eq_closure
    (hgen : f.IsGeneratedBySquareCubeImage)
    (q : PrimeSpectrum S) :
    let _ : Algebra R S := f.toAlgebra
    let G : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
    let gS : S →ₐ[R] q.asIdeal.ResidueField := IsScalarTower.toAlgHom R S q.asIdeal.ResidueField
    ((algebraMap (S ⧸ q.asIdeal) q.asIdeal.ResidueField) : S ⧸ q.asIdeal →+* q.asIdeal.ResidueField).range =
      Subring.closure
        (Set.range (algebraMap R q.asIdeal.ResidueField) ∪ ((gS : S → q.asIdeal.ResidueField) '' G)) := by
  let _ : Algebra R S := f.toAlgebra
  let G : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
  let gS : S →ₐ[R] q.asIdeal.ResidueField := IsScalarTower.toAlgHom R S q.asIdeal.ResidueField
  have hgen' : Algebra.adjoin R G = ⊤ := by
    simpa [RingHom.IsGeneratedBySquareCubeImage, G] using hgen
  have hs_alg : gS.range = Algebra.adjoin R ((gS : S → q.asIdeal.ResidueField) '' G) := by
    -- Map the source-generation hypothesis into the residue field and record the resulting image.
    calc
      gS.range = (⊤ : Subalgebra R S).map gS := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x, by trivial, rfl⟩
        · rintro ⟨x, -, rfl⟩
          exact ⟨x, rfl⟩
      _ = (Algebra.adjoin R G).map gS := by
        rw [hgen'.symm]
      _ = Algebra.adjoin R ((gS : S → q.asIdeal.ResidueField) '' G) := by
        rw [AlgHom.map_adjoin]
  have hs : (gS : S →+* q.asIdeal.ResidueField).range =
      Subring.closure
        (Set.range (algebraMap R q.asIdeal.ResidueField) ∪ ((gS : S → q.asIdeal.ResidueField) '' G)) := by
    -- Convert the algebra-adjoin description into the corresponding subring closure statement.
    simpa [Algebra.adjoin_eq_ring_closure] using congrArg Subalgebra.toSubring hs_alg
  have hrange :
      ((algebraMap (S ⧸ q.asIdeal) q.asIdeal.ResidueField) : S ⧸ q.asIdeal →+* q.asIdeal.ResidueField).range =
        (gS : S →+* q.asIdeal.ResidueField).range := by
    -- Passing from `S` to `S / q` does not change the image inside `κ(q)`.
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rcases Ideal.Quotient.mk_surjective x with ⟨s, rfl⟩
      refine ⟨s, ?_⟩
      simp [gS]
    · rintro y ⟨s, rfl⟩
      refine ⟨Ideal.Quotient.mk q.asIdeal s, ?_⟩
      simp [gS]
  rw [hrange]
  exact hs

/-- Helper for Lemma 10.46.4: the subfield of `κ(q)` generated by the image of `R` together with
the chosen square/cube generators is all of `κ(q)`. -/
lemma residueField_closure_eq_top
    (hgen : f.IsGeneratedBySquareCubeImage)
    (q : PrimeSpectrum S) :
    let _ : Algebra R S := f.toAlgebra
    let G : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
    Subfield.closure
      (Set.range (algebraMap R q.asIdeal.ResidueField) ∪
        ((algebraMap S q.asIdeal.ResidueField) '' G)) = ⊤ := by
  let _ : Algebra R S := f.toAlgebra
  let G : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
  let gA : S ⧸ q.asIdeal →+* q.asIdeal.ResidueField := algebraMap _ _
  have hgA : Function.Injective gA := q.asIdeal.injective_algebraMap_quotient_residueField
  have hs :
      gA.range =
        Subring.closure
          (Set.range (algebraMap R q.asIdeal.ResidueField) ∪
            ((algebraMap S q.asIdeal.ResidueField) '' G)) := by
    simpa [G] using residueField_image_range_eq_closure (f := f) hgen q
  have hlift :
      IsFractionRing.lift hgA = RingHom.id q.asIdeal.ResidueField := by
    -- The fraction-ring lift of the identity embedding is the identity on `κ(q)`.
    apply IsFractionRing.lift_unique hgA
    intro x
    simpa [gA]
  have hfieldRange :
      (IsFractionRing.lift hgA : q.asIdeal.ResidueField →+* q.asIdeal.ResidueField).fieldRange = ⊤ := by
    rw [hlift, RingHom.fieldRange_eq_top_iff]
    exact fun x => ⟨x, rfl⟩
  -- The fraction field of `S / q` is generated by the image of `S / q`.
  rw [← hfieldRange]
  exact (IsFractionRing.lift_fieldRange_eq_of_range_eq hgA hs).symm

/-- Helper for Lemma 10.46.4: if the square and cube of an element lie in the range of a field
homomorphism, then the element lies in the corresponding field range. -/
lemma mem_fieldRange_of_sq_mem_range_and_cube_mem_range
    {K : Type*} {L : Type*} [Field K] [Field L] (φ : K →+* L) {a : L}
    (h2 : a ^ 2 ∈ Set.range φ) (h3 : a ^ 3 ∈ Set.range φ) :
    a ∈ φ.fieldRange := by
  letI : Algebra φ.fieldRange L := φ.fieldRange.subtype.toAlgebra
  have h2' : a ^ 2 ∈ Set.range (algebraMap φ.fieldRange L) := by
    rcases h2 with ⟨x, hx⟩
    refine ⟨⟨φ x, ⟨x, rfl⟩⟩, ?_⟩
    simpa [RingHom.algebraMap_toAlgebra] using hx
  have h3' : a ^ 3 ∈ Set.range (algebraMap φ.fieldRange L) := by
    rcases h3 with ⟨x, hx⟩
    refine ⟨⟨φ x, ⟨x, rfl⟩⟩, ?_⟩
    simpa [RingHom.algebraMap_toAlgebra] using hx
  -- Apply the field-valued square/cube criterion after restricting to the image subfield.
  rcases mem_range_of_sq_mem_range_and_cube_mem_range (K := φ.fieldRange) (L := L) h2' h3' with
    ⟨b, hb⟩
  -- The witness already lies in the range subfield, and its image is the target element.
  simpa [RingHom.algebraMap_toAlgebra] using hb ▸ b.2

/-- Lemma 10.46.4, residue-field clause: if `S` is generated as an `R`-algebra by elements whose
squares and cubes lie in the image of `f`, then for every prime `q` of `S` the induced map
`κ(q ∩ R) → κ(q)` is bijective. This is source-facing: it does not strengthen the conclusion to
surjectivity on stalks. -/
theorem residueFieldMap_bijective_of_isGeneratedBySquareCubeImage
    (hgen : f.IsGeneratedBySquareCubeImage)
    (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := comap f q
    Function.Bijective (Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl) := by
  let _ : Algebra R S := f.toAlgebra
  let p : PrimeSpectrum R := comap f q
  let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
  refine ⟨RingHom.injective fκ, ?_⟩
  have hclosure_le :
      Subfield.closure
        (Set.range (algebraMap R q.asIdeal.ResidueField) ∪
          ((algebraMap S q.asIdeal.ResidueField) ''
            {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range})) ≤
        fκ.fieldRange := by
    refine Subfield.closure_le.mpr ?_
    intro y hy
    rcases hy with hyR | hyG
    · rcases hyR with ⟨r, rfl⟩
      -- Base-field elements lie in the residue-field map range by functoriality.
      exact ⟨algebraMap R p.asIdeal.ResidueField r, by
        calc
          fκ (algebraMap R p.asIdeal.ResidueField r) =
              algebraMap S q.asIdeal.ResidueField (f r) := by
                simpa [fκ] using
                  (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal f rfl r)
          _ = algebraMap R q.asIdeal.ResidueField r := by
                simpa [RingHom.algebraMap_toAlgebra] using
                  (IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField r)⟩
    · rcases hyG with ⟨x, hx, rfl⟩
      rcases hx with ⟨hx2, hx3⟩
      have hx2' : (algebraMap S q.asIdeal.ResidueField x) ^ 2 ∈ Set.range fκ := by
        rcases hx2 with ⟨r, hr⟩
        refine ⟨algebraMap R p.asIdeal.ResidueField r, ?_⟩
        calc
          fκ (algebraMap R p.asIdeal.ResidueField r) =
              algebraMap S q.asIdeal.ResidueField (f r) := by
                simpa [fκ] using
                  (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal f rfl r)
          _ = algebraMap S q.asIdeal.ResidueField (x ^ 2) := by simpa [hr]
          _ = (algebraMap S q.asIdeal.ResidueField x) ^ 2 := by simp [pow_two]
      have hx3' : (algebraMap S q.asIdeal.ResidueField x) ^ 3 ∈ Set.range fκ := by
        rcases hx3 with ⟨r, hr⟩
        refine ⟨algebraMap R p.asIdeal.ResidueField r, ?_⟩
        calc
          fκ (algebraMap R p.asIdeal.ResidueField r) =
              algebraMap S q.asIdeal.ResidueField (f r) := by
                simpa [fκ] using
                  (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal f rfl r)
          _ = algebraMap S q.asIdeal.ResidueField (x ^ 3) := by simpa [hr]
          _ = (algebraMap S q.asIdeal.ResidueField x) ^ 3 := by simp [pow_succ']
      -- Each chosen generator image already lies in the intermediate field `fκ.fieldRange`.
      exact mem_fieldRange_of_sq_mem_range_and_cube_mem_range (φ := fκ) hx2' hx3'
  have hfieldRange_top : fκ.fieldRange = ⊤ := by
    -- Route correction: the source proof works through the whole generated subfield, not a direct
    -- surjectivity claim on `Set.range fκ`.
    apply top_unique
    rw [← residueField_closure_eq_top (f := f) hgen q]
    exact hclosure_le
  -- Once the field range is all of `κ(q)`, surjectivity is immediate.
  simpa [p, fκ] using (RingHom.fieldRange_eq_top_iff.mp hfieldRange_top)

/-- Helper for Lemma 10.46.4: transporting the residue-field map back along a residue-field
equivalence does not change its kernel. -/
lemma transported_residue_inverse_kernel_eq
    {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (e : p.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField) :
    RingHom.ker (e.symm.toRingHom.comp (algebraMap S q.asIdeal.ResidueField)) = q.asIdeal := by
  -- Kernels are unchanged after composing with the injective inverse equivalence.
  rw [RingHom.ker_comp_of_injective (g := algebraMap S q.asIdeal.ResidueField) e.symm.injective]
  simpa using (Ideal.ker_algebraMap_residueField (R := S) (I := q.asIdeal))

/-- Helper for Lemma 10.46.4: transport the canonical map `S → κ(q)` back along a chosen
residue-field equivalence `κ(p) ≃ₐ[R] κ(q)`. -/
noncomputable def transported_residue_inverse_toAlgHom
    [Algebra R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (e : p.asIdeal.ResidueField ≃ₐ[R] q.asIdeal.ResidueField) :
    S →ₐ[R] p.asIdeal.ResidueField :=
  e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)

/-- Helper for Lemma 10.46.4: the transported inverse agrees with the original `R`-algebra map on
elements coming from `R`. -/
lemma transported_residue_inverse_toAlgHom_comp
    [Algebra R S]
    {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (e : p.asIdeal.ResidueField ≃ₐ[R] q.asIdeal.ResidueField) :
    ∀ r : R,
      transported_residue_inverse_toAlgHom e ((algebraMap R S) r) =
        algebraMap R p.asIdeal.ResidueField r := by
  intro r
  -- Applying `e` collapses the transported inverse back to the canonical residue-field map.
  apply e.injective
  calc
    e ((transported_residue_inverse_toAlgHom e) ((algebraMap R S) r)) =
        algebraMap R q.asIdeal.ResidueField r := by
          simp [transported_residue_inverse_toAlgHom]
    _ = e (algebraMap R p.asIdeal.ResidueField r) := by
          symm
          simp

/-- Helper for Lemma 10.46.4: fibers of `Spec(S) → Spec(R)` are singletons under the
square/cube-generation hypothesis. -/
theorem comap_injective_of_isGeneratedBySquareCubeImage
    (hgen : f.IsGeneratedBySquareCubeImage) :
    Function.Injective (comap f) := by
  -- Route correction: compare the two transported maps `S → κ(p)` and then read off their
  -- kernels, instead of trying to force injectivity directly from the generator ranges.
  let _ : Algebra R S := f.toAlgebra
  intro q q' hqq'
  generalize hpSpec : comap f q = p
  let G : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
  have hp : p.asIdeal = q.asIdeal.comap f := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hpSpec.symm
  have hq'Spec : comap f q' = p := by
    exact hqq'.symm.trans hpSpec
  have hp' : p.asIdeal = q'.asIdeal.comap f := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq'Spec.symm
  have htop : Algebra.adjoin R G = ⊤ := by
    simpa [RingHom.IsGeneratedBySquareCubeImage, G] using hgen
  have hbij_q :
      Function.Bijective (Ideal.ResidueField.map p.asIdeal q.asIdeal f hp) := by
    cases hpSpec
    simpa using
      (residueFieldMap_bijective_of_isGeneratedBySquareCubeImage (f := f) hgen q)
  have hbij_q' :
      Function.Bijective (Ideal.ResidueField.map p.asIdeal q'.asIdeal f hp') := by
    cases hq'Spec
    simpa using
      (residueFieldMap_bijective_of_isGeneratedBySquareCubeImage (f := f) hgen q')
  let e :
      p.asIdeal.ResidueField ≃ₐ[R] q.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S) hp)
      (by simpa using hbij_q)
  let e' :
      p.asIdeal.ResidueField ≃ₐ[R] q'.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ p.asIdeal q'.asIdeal (Algebra.ofId R S) hp')
      (by simpa using hbij_q')
  let ψ : S →ₐ[R] p.asIdeal.ResidueField := transported_residue_inverse_toAlgHom e
  let ψ' : S →ₐ[R] p.asIdeal.ResidueField := transported_residue_inverse_toAlgHom e'
  have hψ : ∀ r : R, ψ (f r) = algebraMap R p.asIdeal.ResidueField r := by
    intro r
    simpa [RingHom.algebraMap_toAlgebra f, ψ, e] using
      transported_residue_inverse_toAlgHom_comp e r
  have hψ' : ∀ r : R, ψ' (f r) = algebraMap R p.asIdeal.ResidueField r := by
    intro r
    simpa [RingHom.algebraMap_toAlgebra f, ψ', e'] using
      transported_residue_inverse_toAlgHom_comp e' r
  have hEqOn : Set.EqOn ψ ψ' G := by
    intro x hx
    rcases hx with ⟨hx2, hx3⟩
    rcases hx2 with ⟨r2, hr2⟩
    rcases hx3 with ⟨r3, hr3⟩
    -- Each generator has matching square and cube under both transported maps.
    apply eq_of_sq_eq_sq_and_cube_eq_cube
    · calc
        (ψ x) ^ 2 = ψ (x ^ 2) := by
          symm
          exact map_pow ψ x 2
        _ = ψ (f r2) := by simpa [hr2]
        _ = algebraMap R p.asIdeal.ResidueField r2 := hψ r2
        _ = ψ' (f r2) := by symm; exact hψ' r2
        _ = ψ' (x ^ 2) := by simpa [hr2]
        _ = (ψ' x) ^ 2 := by
          exact map_pow ψ' x 2
    · calc
        (ψ x) ^ 3 = ψ (x ^ 3) := by
          symm
          exact map_pow ψ x 3
        _ = ψ (f r3) := by simpa [hr3]
        _ = algebraMap R p.asIdeal.ResidueField r3 := hψ r3
        _ = ψ' (f r3) := by symm; exact hψ' r3
        _ = ψ' (x ^ 3) := by simpa [hr3]
        _ = (ψ' x) ^ 3 := by
          exact map_pow ψ' x 3
  have hψ_eq : ψ = ψ' :=
    AlgHom.ext_of_adjoin_eq_top (R := R) (s := G) htop hEqOn
  have hker_eq :
      RingHom.ker ψ.toRingHom = RingHom.ker ψ'.toRingHom := by
    simpa using congrArg RingHom.ker (congrArg AlgHom.toRingHom hψ_eq)
  have hker_q : RingHom.ker ψ.toRingHom = q.asIdeal := by
    -- Unfold the transported map once and identify its kernel with `q`.
    simpa [ψ, e, transported_residue_inverse_toAlgHom] using
      transported_residue_inverse_kernel_eq
        (p := p) (q := q) (e := (e : p.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField))
  have hker_q' : RingHom.ker ψ'.toRingHom = q'.asIdeal := by
    -- The same kernel description applies to the second transported map.
    simpa [ψ', e', transported_residue_inverse_toAlgHom] using
      transported_residue_inverse_kernel_eq
        (p := p) (q := q') (e := (e' : p.asIdeal.ResidueField ≃+* q'.asIdeal.ResidueField))
  exact PrimeSpectrum.ext_iff.mpr <|
    calc
      q.asIdeal = RingHom.ker ψ.toRingHom := hker_q.symm
      _ = RingHom.ker ψ'.toRingHom := hker_eq
      _ = q'.asIdeal := hker_q'

-- Proof sketch: the generating hypothesis shows that after passing to a residue field, every
-- residue class is generated by elements whose square and cube lie in the smaller residue field,
-- hence already lie in it. This gives bijectivity on residue fields. Integrality coming from the
-- same square-cube relation makes `Spec(S) → Spec(R)` closed, while the nilpotent-kernel
-- hypothesis gives dense image; bijectivity on fibers then upgrades the spectral map to a
-- homeomorphism. After base change, the same square-cube generation condition and locally
-- nilpotent-kernel condition are preserved for the canonical map `R' → R' ⊗[R] S`.

/-- If the kernel of `f` is locally nilpotent and `S` is generated by elements whose squares and
cubes lie in the image of `f`, then the induced map on prime spectra is a homeomorphism. -/
theorem isHomeomorph_comap_of_isGeneratedBySquareCubeImage
    (hgen : f.IsGeneratedBySquareCubeImage)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    IsHomeomorph (comap f) := by
  have hInt : f.IsIntegral := isIntegral_of_isGeneratedBySquareCubeImage (f := f) hgen
  have hclosed : IsClosedMap (comap f) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hInt
  have hdense : DenseRange (comap f) := by
    -- The locally nilpotent-kernel hypothesis is exactly the dense-image criterion.
    exact (denseRange_comap_iff_ker_le_nilRadical f).2 (by simpa [Ideal.IsLocallyNilpotent] using hker)
  have hsurj : Function.Surjective (comap f) := by
    rw [← Set.range_eq_univ]
    rw [← hclosed.isClosed_range.closure_eq, hdense.closure_range]
  have hbij : Function.Bijective (comap f) :=
    ⟨comap_injective_of_isGeneratedBySquareCubeImage (f := f) hgen, hsurj⟩
  -- A bijective closed map between spectral spaces is a homeomorphism.
  exact (isHomeomorph_iff_continuous_isClosedMap_bijective).2
    ⟨continuous_comap f, hclosed, hbij⟩

variable {R' : Type w} [CommRing R'] [Algebra R R']

/-- For any ring map `R → R'`, the canonical base-changed map `R' → R' ⊗[R] S` again has codomain
generated by elements whose squares and cubes lie in its image. -/
theorem isGeneratedBySquareCubeImage_baseChange_of_isGeneratedBySquareCubeImage
    (hgen : f.IsGeneratedBySquareCubeImage) :
    let _ : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f'.IsGeneratedBySquareCubeImage := by
  let _ : Algebra R S := f.toAlgebra
  let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
  let G : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
  dsimp [RingHom.IsGeneratedBySquareCubeImage]
  have htop :
      Algebra.adjoin R' (((1 : R') ⊗ₜ[R] ·) '' G) = ⊤ := by
    -- The original generating set still generates after literal base change.
    simpa [RingHom.IsGeneratedBySquareCubeImage, G] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := R') (s := G) hgen
  have hsubset :
      (((1 : R') ⊗ₜ[R] ·) '' G) ⊆
        {y : R' ⊗[R] S | y ^ 2 ∈ f'.range ∧ y ^ 3 ∈ f'.range} := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨hx2, hx3⟩
    constructor
    · rcases hx2 with ⟨r, hr⟩
      refine ⟨algebraMap R R' r, ?_⟩
      calc
        f' (algebraMap R R' r) = (1 : R') ⊗ₜ[R] f r := by
          calc
            f' (algebraMap R R' r) = algebraMap R (R' ⊗[R] S) r := by
              rw [← IsScalarTower.algebraMap_apply R R' (R' ⊗[R] S)]
            _ = (1 : R') ⊗ₜ[R] f r := by
              simpa [RingHom.algebraMap_toAlgebra] using
                (Algebra.TensorProduct.algebraMap_apply' (R := R) (A := R') (B := S) r)
        _ = (1 : R') ⊗ₜ[R] (x ^ 2) := by
          simpa [hr]
        _ = ((1 : R') ⊗ₜ[R] x) ^ 2 := by
          simp [pow_two]
    · rcases hx3 with ⟨r, hr⟩
      refine ⟨algebraMap R R' r, ?_⟩
      calc
        f' (algebraMap R R' r) = (1 : R') ⊗ₜ[R] f r := by
          calc
            f' (algebraMap R R' r) = algebraMap R (R' ⊗[R] S) r := by
              rw [← IsScalarTower.algebraMap_apply R R' (R' ⊗[R] S)]
            _ = (1 : R') ⊗ₜ[R] f r := by
              simpa [RingHom.algebraMap_toAlgebra] using
                (Algebra.TensorProduct.algebraMap_apply' (R := R) (A := R') (B := S) r)
        _ = (1 : R') ⊗ₜ[R] (x ^ 3) := by
          simpa [hr]
        _ = ((1 : R') ⊗ₜ[R] x) ^ 3 := by
          simp [pow_succ']
  have hadjoin_le :
      Algebra.adjoin R' (((1 : R') ⊗ₜ[R] ·) '' G) ≤
        Algebra.adjoin R'
          {y : R' ⊗[R] S | y ^ 2 ∈ f'.range ∧ y ^ 3 ∈ f'.range} := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    exact Algebra.subset_adjoin (hsubset hy)
  have htop_le :
      (⊤ : Subalgebra R' (R' ⊗[R] S)) ≤
        Algebra.adjoin R'
          {y : R' ⊗[R] S | y ^ 2 ∈ f'.range ∧ y ^ 3 ∈ f'.range} := by
    rw [← htop]
    exact hadjoin_le
  exact top_unique htop_le

-- Proof sketch: the homeomorphism clause comes from `PrimeSpectrum.isHomeomorph_comap` after
-- converting the square/cube generation hypothesis into the positive-power bridge, while the
-- residue-field clause is the theorem above. For the base-change part, local nilpotence of the
-- kernel is only asserted under the full square/cube generation and locally nilpotent-kernel
-- hypotheses of Lemma `10.46.4`; it is not a standalone consequence of local nilpotence of
-- `ker f` alone.
/-- Lemma 10.46.4, source-facing full statement: if `ker f` is locally nilpotent and `S` is
generated as an `R`-algebra by elements whose squares and cubes lie in the image of `f`, then
`Spec(S) → Spec(R)` is a homeomorphism and every induced map on residue fields is bijective.
Moreover, after any base change `R → R'`, the canonical map `R' → R' ⊗[R] S` again satisfies the
same generation hypothesis and has locally nilpotent kernel. -/
theorem isHomeomorph_comap_and_residueFieldMap_bijective_and_baseChange_of_isGeneratedBySquareCubeImage
    (hgen : f.IsGeneratedBySquareCubeImage)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    IsHomeomorph (comap f) ∧
      (∀ q : PrimeSpectrum S,
        let p : PrimeSpectrum R := comap f q
        Function.Bijective (Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl)) ∧
      ∀ {R' : Type w} [CommRing R'] [Algebra R R'],
        let _ : Algebra R S := f.toAlgebra
        let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
        f'.IsGeneratedBySquareCubeImage ∧
          (RingHom.ker f').IsLocallyNilpotent := by
  refine ⟨?_, ?_, ?_⟩
  · -- The spectral map is a homeomorphism by the preceding theorem.
    exact isHomeomorph_comap_of_isGeneratedBySquareCubeImage (f := f) hgen hker
  · -- Residue-field bijectivity was proved directly from the square/cube generators.
    intro q
    exact residueFieldMap_bijective_of_isGeneratedBySquareCubeImage (f := f) hgen q
  · intro R' _ _
    let _ : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    have hhomeo : IsHomeomorph (comap f) :=
      isHomeomorph_comap_of_isGeneratedBySquareCubeImage (f := f) hgen hker
    have hsurj' : Function.Surjective (comap f') :=
      specComap_surjective_stable_under_baseChange
        (R := R) (S := S) (R' := R') hhomeo.surjective
    have hker' : (RingHom.ker f').IsLocallyNilpotent := by
      -- Surjectivity of spectra after base change rewrites back to the nilradical condition.
      exact (denseRange_comap_iff_ker_le_nilRadical f').mp hsurj'.denseRange
    exact ⟨isGeneratedBySquareCubeImage_baseChange_of_isGeneratedBySquareCubeImage
      (f := f) (R' := R') hgen, hker'⟩

-- Proof sketch: combine the source-facing theorem above with the separate base-change generation
-- clause, and then reapply the homeomorphism and residue-field statements to the canonical
-- base-changed map using the base-change hypotheses packaged by the full theorem.
/-- Companion derived form of Lemma 10.46.4: under the same hypotheses, every base change
`R' → R' ⊗[R] S` also induces a homeomorphism on spectra and bijective residue-field maps. -/
theorem isHomeomorph_comap_and_residueFieldMap_bijective_after_baseChange_of_isGeneratedBySquareCubeImage
    (hgen : f.IsGeneratedBySquareCubeImage)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    IsHomeomorph (comap f) ∧
      (∀ q : PrimeSpectrum S,
        let p : PrimeSpectrum R := comap f q
        Function.Bijective (Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl)) ∧
      ∀ {R' : Type w} [CommRing R'] [Algebra R R'],
        let _ : Algebra R S := f.toAlgebra
        let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
        IsHomeomorph (comap f') ∧
          ∀ q' : PrimeSpectrum (R' ⊗[R] S),
            let p' : PrimeSpectrum R' := comap f' q'
            Function.Bijective (Ideal.ResidueField.map p'.asIdeal q'.asIdeal f' rfl) := by
  rcases
      isHomeomorph_comap_and_residueFieldMap_bijective_and_baseChange_of_isGeneratedBySquareCubeImage
        (f := f) hgen hker with
    ⟨hhomeo, hres, hbase⟩
  refine ⟨hhomeo, hres, ?_⟩
  intro R' _ _
  let _ : Algebra R S := f.toAlgebra
  let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
  rcases hbase (R' := R') with ⟨hgen', hker'⟩
  refine ⟨isHomeomorph_comap_of_isGeneratedBySquareCubeImage (f := f') hgen' hker', ?_⟩
  intro q'
  exact residueFieldMap_bijective_of_isGeneratedBySquareCubeImage (f := f') hgen' q'

end

/-! ### Lemma_10_46_5 (from Chap10) -/
open MvPolynomial

local notation "Pxy" => MvPolynomial (Fin 2) ℤ
local notation "x" => (X (0 : Fin 2) : Pxy)
local notation "y" => (X (1 : Fin 2) : Pxy)

section

variable (p n m : ℕ)

-- Primitive data: the four generators appearing in the source statement.
local notation "mixedPowerMultipleGenerators" =>
  ({x ^ (p ^ n), p ^ n • x, y ^ (p ^ m), p ^ m • y} : Set Pxy)

-- Derived owner object: the `ℤ`-subalgebra generated by those four elements.
local notation "mixedPowerMultipleSubalgebra" =>
  Algebra.adjoin ℤ mixedPowerMultipleGenerators

/-- Helper for Lemma 10.46.5: multiplying the linear generator `p^k • z` by the constant
polynomial `p^(a-k)` recovers the larger multiple `p^a • z`. -/
lemma scaled_linear_multiple_eq
    {a k : ℕ} (z : Pxy) (hk : k ≤ a) :
    (((p ^ (a - k) : ℕ) : Pxy) * (p ^ k • z : Pxy)) = p ^ a • z := by
  -- First rewrite the smaller multiple as multiplication by the constant polynomial `p^k`.
  calc
    (((p ^ (a - k) : ℕ) : Pxy) * (p ^ k • z : Pxy))
        = (((p ^ (a - k) : ℕ) : Pxy) * (((p ^ k : ℕ) : Pxy) * z)) := by
            simp only [nsmul_eq_mul]
    -- Then combine the two scalar factors into the single power `p^a`.
    _ = (((p ^ (a - k) * p ^ k : ℕ) : Pxy) * z) := by
          simp only [Nat.cast_mul, mul_assoc]
    _ = (((p ^ a : ℕ) : Pxy) * z) := by
          congr 1
          rw [← pow_add, Nat.sub_add_cancel hk]
    -- Finally return to scalar multiplication notation.
    _ = p ^ a • z := by
          simp only [nsmul_eq_mul]

/-- Helper for Lemma 10.46.5: once `a` dominates `n` and `m`, the multiple `p^a (x + y)` is
already generated by the two linear generators. -/
lemma sum_multiple_mem_mixedPowerMultipleSubalgebra_of_le
    {a : ℕ} (hn : n ≤ a) (hm : m ≤ a) :
    p ^ a • (x + y) ∈ mixedPowerMultipleSubalgebra := by
  have hx_generator : p ^ n • x ∈ mixedPowerMultipleSubalgebra := by
    -- The displayed linear `x`-generator is one of the adjoined generators.
    exact Algebra.subset_adjoin (by simp)
  have hy_generator : p ^ m • y ∈ mixedPowerMultipleSubalgebra := by
    -- The displayed linear `y`-generator is also adjoined by definition.
    exact Algebra.subset_adjoin (by simp)
  have hx_large : p ^ a • x ∈ mixedPowerMultipleSubalgebra := by
    -- Rewrite `p^a • x` as a constant polynomial times the generator `p^n • x`.
    rw [← scaled_linear_multiple_eq (p := p) (a := a) (k := n) (z := x) hn]
    exact Subalgebra.mul_mem mixedPowerMultipleSubalgebra
      (Subalgebra.algebraMap_mem mixedPowerMultipleSubalgebra ((p ^ (a - n) : ℕ) : ℤ))
      hx_generator
  have hy_large : p ^ a • y ∈ mixedPowerMultipleSubalgebra := by
    -- The same normalization works for the `y`-generator.
    rw [← scaled_linear_multiple_eq (p := p) (a := a) (k := m) (z := y) hm]
    exact Subalgebra.mul_mem mixedPowerMultipleSubalgebra
      (Subalgebra.algebraMap_mem mixedPowerMultipleSubalgebra ((p ^ (a - m) : ℕ) : ℤ))
      hy_generator
  -- Split the large multiple of `x + y` into the sum of the two normalized generators.
  simpa [nsmul_eq_mul, mul_add] using
    Subalgebra.add_mem mixedPowerMultipleSubalgebra hx_large hy_large

/-- Helper for Lemma 10.46.5: splitting exponents into quotient and remainder rewrites a product
of the four generators as the raw monomial with the corresponding `p`-power coefficient. -/
lemma split_residue_monomial_eq
    (d i j : ℕ) :
    ((d : Pxy) * (p ^ n • x) ^ (i % p ^ n) * (x ^ (p ^ n)) ^ (i / p ^ n) *
      (p ^ m • y) ^ (j % p ^ m) * (y ^ (p ^ m)) ^ (j / p ^ m)) =
      x ^ i * y ^ j * (((p ^ (n * (i % p ^ n) + m * (j % p ^ m)) * d : ℕ)) : Pxy) := by
  have hxpow : x ^ i = (x ^ (p ^ n)) ^ (i / p ^ n) * x ^ (i % p ^ n) := by
    -- Decompose the `x`-exponent into its quotient and remainder modulo `p^n`.
    calc
      x ^ i = x ^ (i % p ^ n + i / p ^ n * p ^ n) := by rw [Nat.mod_add_div']
      _ = x ^ (i % p ^ n) * x ^ (i / p ^ n * p ^ n) := by rw [pow_add]
      _ = x ^ (i % p ^ n) * (x ^ (p ^ n)) ^ (i / p ^ n) := by
            rw [Nat.mul_comm, pow_mul]
      _ = (x ^ (p ^ n)) ^ (i / p ^ n) * x ^ (i % p ^ n) := by ac_rfl
  have hypow : y ^ j = (y ^ (p ^ m)) ^ (j / p ^ m) * y ^ (j % p ^ m) := by
    -- Do the same quotient-remainder split for the `y`-exponent modulo `p^m`.
    calc
      y ^ j = y ^ (j % p ^ m + j / p ^ m * p ^ m) := by rw [Nat.mod_add_div']
      _ = y ^ (j % p ^ m) * y ^ (j / p ^ m * p ^ m) := by rw [pow_add]
      _ = y ^ (j % p ^ m) * (y ^ (p ^ m)) ^ (j / p ^ m) := by
            rw [Nat.mul_comm, pow_mul]
      _ = (y ^ (p ^ m)) ^ (j / p ^ m) * y ^ (j % p ^ m) := by ac_rfl
  have hcoeff_nat :
      p ^ (n * (i % p ^ n) + m * (j % p ^ m)) * d =
        (p ^ n) ^ (i % p ^ n) * (p ^ m) ^ (j % p ^ m) * d := by
    -- Rewrite the scalar coefficient using the same exponent splitting on the prime powers.
    rw [pow_add, pow_mul, pow_mul]
  have hcoeff :
      ((((p ^ (n * (i % p ^ n) + m * (j % p ^ m)) * d : ℕ)) : Pxy)) =
        (((p ^ n : ℕ) : Pxy) ^ (i % p ^ n)) * (((p ^ m : ℕ) : Pxy) ^ (j % p ^ m)) * (d : Pxy) := by
    -- Cast the natural-number coefficient identity into the polynomial ring.
    simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun t : ℕ => (t : Pxy)) hcoeff_nat
  -- Normalize both sides to the same commutative product of generators and constants.
  calc
    ((d : Pxy) * (p ^ n • x) ^ (i % p ^ n) * (x ^ (p ^ n)) ^ (i / p ^ n) *
        (p ^ m • y) ^ (j % p ^ m) * (y ^ (p ^ m)) ^ (j / p ^ m))
      = (d : Pxy) * ((((p ^ n : ℕ) : Pxy) * x) ^ (i % p ^ n)) * (x ^ (p ^ n)) ^ (i / p ^ n) *
          ((((p ^ m : ℕ) : Pxy) * y) ^ (j % p ^ m)) * (y ^ (p ^ m)) ^ (j / p ^ m) := by
            simp only [nsmul_eq_mul]
    _ = (d : Pxy) * ((((p ^ n : ℕ) : Pxy) ^ (i % p ^ n) * x ^ (i % p ^ n))) *
          (x ^ (p ^ n)) ^ (i / p ^ n) *
          ((((p ^ m : ℕ) : Pxy) ^ (j % p ^ m) * y ^ (j % p ^ m))) *
          (y ^ (p ^ m)) ^ (j / p ^ m) := by
            rw [mul_pow, mul_pow]
    _ = x ^ i * y ^ j * (((p ^ (n * (i % p ^ n) + m * (j % p ^ m)) * d : ℕ)) : Pxy) := by
          rw [hxpow, hypow, hcoeff]
          ac_rfl

/-- Helper for Lemma 10.46.5: enough `p`-divisibility in the coefficient lets a monomial factor
through the four displayed generators. -/
lemma binomial_summand_mem_mixedPowerMultipleSubalgebra
    {c i j : ℕ}
    (hc : p ^ (n * (i % p ^ n) + m * (j % p ^ m)) ∣ c) :
    (x ^ i * y ^ j * c : Pxy) ∈ mixedPowerMultipleSubalgebra := by
  rcases hc with ⟨d, rfl⟩
  have hd_mem : (d : Pxy) ∈ mixedPowerMultipleSubalgebra := by
    -- Constant polynomials always belong to any `ℤ`-subalgebra.
    simpa using Subalgebra.algebraMap_mem mixedPowerMultipleSubalgebra (d : ℤ)
  have hx_linear_mem : p ^ n • x ∈ mixedPowerMultipleSubalgebra := by
    -- The linear `x`-generator is adjoined by construction.
    exact Algebra.subset_adjoin (by simp)
  have hx_power_mem : x ^ (p ^ n) ∈ mixedPowerMultipleSubalgebra := by
    -- The pure `x^(p^n)` generator is also in the adjoin.
    exact Algebra.subset_adjoin (by simp)
  have hy_linear_mem : p ^ m • y ∈ mixedPowerMultipleSubalgebra := by
    -- The linear `y`-generator is part of the generating set as well.
    exact Algebra.subset_adjoin (by simp)
  have hy_power_mem : y ^ (p ^ m) ∈ mixedPowerMultipleSubalgebra := by
    -- Finally `y^(p^m)` is one of the four displayed generators.
    exact Algebra.subset_adjoin (by simp)
  -- Rewrite the raw monomial into the structured product of constants and the four generators.
  rw [← split_residue_monomial_eq (p := p) (n := n) (m := m) (d := d) (i := i) (j := j)]
  exact Subalgebra.mul_mem mixedPowerMultipleSubalgebra
    (Subalgebra.mul_mem mixedPowerMultipleSubalgebra
      (Subalgebra.mul_mem mixedPowerMultipleSubalgebra
        (Subalgebra.mul_mem mixedPowerMultipleSubalgebra
          hd_mem
          (Subalgebra.pow_mem mixedPowerMultipleSubalgebra hx_linear_mem _))
        (Subalgebra.pow_mem mixedPowerMultipleSubalgebra hx_power_mem _))
      (Subalgebra.pow_mem mixedPowerMultipleSubalgebra hy_linear_mem _))
    (Subalgebra.pow_mem mixedPowerMultipleSubalgebra hy_power_mem _)

/-- Helper for Lemma 10.46.5: the binomial coefficient at a prime power carries enough
`p`-divisibility to absorb the residues modulo `p^n` and `p^m`. -/
lemma choose_prime_power_dvd_residue_scale
    (hp : Nat.Prime p) {a0 i : ℕ} (ha0 : a0 = n * p ^ n + m * p ^ m + n + m)
    (hi : i ≤ p ^ a0) :
    p ^ (n * (i % p ^ n) + m * ((p ^ a0 - i) % p ^ m)) ∣ Nat.choose (p ^ a0) i := by
  let j := p ^ a0 - i
  have hresidue_bound :
      n * (i % p ^ n) + m * (j % p ^ m) ≤ n * p ^ n + m * p ^ m := by
    -- Each residue is bounded by the corresponding modulus.
    have hi_mod : i % p ^ n ≤ p ^ n := le_of_lt (Nat.mod_lt _ (pow_pos hp.pos _))
    have hj_mod : j % p ^ m ≤ p ^ m := le_of_lt (Nat.mod_lt _ (pow_pos hp.pos _))
    exact add_le_add (Nat.mul_le_mul_left _ hi_mod) (Nat.mul_le_mul_left _ hj_mod)
  by_cases hri : i % p ^ n = 0
  · by_cases hrj : j % p ^ m = 0
    · -- If both residues vanish, there is no `p`-power to absorb.
      simp [j, hri, hrj]
    · have hj0 : j ≠ 0 := by
        -- A nonzero residue forces the underlying number to be nonzero.
        intro hj0
        exact hrj (by simp [j, hj0])
      have hj_not_dvd : ¬ p ^ m ∣ j := by
        -- Divisibility by `p^m` would force the residue modulo `p^m` to vanish.
        intro hj_dvd
        exact hrj (Nat.mod_eq_zero_of_dvd hj_dvd)
      have hmult_lt : multiplicity p j < m := by
        -- Convert the nondivisibility statement into a multiplicity bound.
        let hf : FiniteMultiplicity p j := Nat.finiteMultiplicity_iff.2
          ⟨hp.ne_one, Nat.pos_of_ne_zero hj0⟩
        exact hf.multiplicity_lt_iff_not_dvd.mpr hj_not_dvd
      have hbase_bound : n * p ^ n + m * p ^ m ≤ a0 - multiplicity p j := by
        -- The chosen exponent `a0` dominates the residual scale by at least `n + m`.
        have hmult_nm : multiplicity p j ≤ n + m := by
          exact le_trans (le_of_lt hmult_lt) (by simpa [add_comm] using Nat.le_add_left m n)
        have hsum : (n * p ^ n + m * p ^ m) + multiplicity p j ≤ a0 := by
          simpa [ha0, add_assoc, add_left_comm, add_comm] using
            add_le_add_left hmult_nm (n * p ^ n + m * p ^ m)
        exact Nat.le_sub_of_add_le hsum
      have hpow :
          p ^ (n * (i % p ^ n) + m * (j % p ^ m)) ∣ Nat.choose (p ^ a0) j := by
        -- Apply the prime-power valuation formula to the complementary index `j`.
        apply pow_dvd_of_le_emultiplicity
        rw [Nat.Prime.emultiplicity_choose_prime_pow hp (show j ≤ p ^ a0 by
          exact Nat.sub_le _ _) hj0]
        exact_mod_cast le_trans hresidue_bound hbase_bound
      have hsymm : Nat.choose (p ^ a0) j = Nat.choose (p ^ a0) i := by
        -- Replace the complementary index with the original binomial coefficient.
        simpa [j] using Nat.choose_symm hi
      rw [hsymm] at hpow
      simpa [j, hri] using hpow
  · have hi0 : i ≠ 0 := by
      -- A nonzero residue also forces `i` itself to be nonzero.
      intro hi0
      exact hri (by simp [hi0])
    have hi_not_dvd : ¬ p ^ n ∣ i := by
      -- Divisibility by `p^n` would force the residue modulo `p^n` to vanish.
      intro hi_dvd
      exact hri (Nat.mod_eq_zero_of_dvd hi_dvd)
    have hmult_lt : multiplicity p i < n := by
      -- Convert the nondivisibility statement into a multiplicity bound.
      let hf : FiniteMultiplicity p i := Nat.finiteMultiplicity_iff.2
        ⟨hp.ne_one, Nat.pos_of_ne_zero hi0⟩
      exact hf.multiplicity_lt_iff_not_dvd.mpr hi_not_dvd
    have hbase_bound : n * p ^ n + m * p ^ m ≤ a0 - multiplicity p i := by
      -- The chosen exponent `a0` also dominates the scale coming from the `i`-branch.
      have hmult_nm : multiplicity p i ≤ n + m := by
        exact le_trans (le_of_lt hmult_lt) (Nat.le_add_right n m)
      have hsum : (n * p ^ n + m * p ^ m) + multiplicity p i ≤ a0 := by
        simpa [ha0, add_assoc, add_left_comm, add_comm] using
          add_le_add_left hmult_nm (n * p ^ n + m * p ^ m)
      exact Nat.le_sub_of_add_le hsum
    -- The valuation formula now applies directly to the index `i`.
    apply pow_dvd_of_le_emultiplicity
    rw [Nat.Prime.emultiplicity_choose_prime_pow hp hi hi0]
    exact_mod_cast le_trans hresidue_bound hbase_bound

/-- Helper for Lemma 10.46.5: the chosen `p`-power of `x + y` lies in the generated
subalgebra after expanding by the binomial theorem term-by-term. -/
lemma binomial_power_mem_mixedPowerMultipleSubalgebra
    (hp : Nat.Prime p) :
    (x + y) ^ (p ^ (n * p ^ n + m * p ^ m + n + m)) ∈ mixedPowerMultipleSubalgebra := by
  let a0 := n * p ^ n + m * p ^ m + n + m
  let N := p ^ a0
  -- Expand by the binomial theorem and treat each summand separately.
  rw [show (p ^ (n * p ^ n + m * p ^ m + n + m)) = N by rfl, add_pow]
  refine Subalgebra.sum_mem _ ?_
  intro i hi
  have hi' : i ≤ N := by
    exact Nat.lt_succ_iff.mp (by simpa [N] using hi)
  have hcoeff :
      p ^ (n * (i % p ^ n) + m * ((N - i) % p ^ m)) ∣ Nat.choose N i := by
    -- This is the arithmetic divisibility estimate from the source proof.
    simpa [a0, N] using
      choose_prime_power_dvd_residue_scale (p := p) (n := n) (m := m) hp (a0 := a0) rfl
        (by simpa [N] using hi')
  -- The structural summand lemma packages the algebraic factorization through the generators.
  simpa [N, mul_assoc, mul_left_comm, mul_comm] using
    binomial_summand_mem_mixedPowerMultipleSubalgebra (p := p) (n := n) (m := m)
      (c := Nat.choose N i) (i := i) (j := N - i) hcoeff

/-- Lemma 10.46.5: for a prime `p` and natural numbers `n` and `m`, some `p`-power makes both
`(x + y)^(p^a)` and `p^a (x + y)` lie in the `ℤ`-subalgebra of `ℤ[x, y]` generated by
`x^(p^n)`, `p^n x`, `y^(p^m)`, and `p^m y`. -/
-- Proof sketch: choose `a` large compared to `n` and `m`, for example the value suggested in the
-- text. The linear term belongs to the generated `ℤ`-subalgebra once `a ≥ n` and `a ≥ m`. For the
-- `p^a`-th power, expand by the binomial theorem and write each exponent modulo `p^n` and `p^m`;
-- the `p`-adic valuation estimate on the binomial coefficients shows that every term acquires
-- enough factors of `p` to lie in the `ℤ`-subalgebra generated by the four displayed elements.
theorem exists_power_and_multiple_of_sum_mem_mixedPowerMultipleSubalgebra
    (hp : Nat.Prime p) :
    ∃ a : ℕ,
      (x + y) ^ (p ^ a) ∈ mixedPowerMultipleSubalgebra ∧
        p ^ a • (x + y) ∈ mixedPowerMultipleSubalgebra := by
  let a0 := n * p ^ n + m * p ^ m + n + m
  refine ⟨a0, ?_, ?_⟩
  · -- The high power belongs term-by-term after the binomial expansion.
    simpa [a0] using
      binomial_power_mem_mixedPowerMultipleSubalgebra (p := p) (n := n) (m := m) hp
  · -- The linear term is immediate because `a0` dominates both `n` and `m`.
    refine sum_multiple_mem_mixedPowerMultipleSubalgebra_of_le (p := p) (n := n) (m := m)
      (a := a0) ?_ ?_
    · simpa [a0, add_assoc, add_left_comm, add_comm] using
        Nat.le_add_right n (n * p ^ n + m * p ^ m + m)
    · simpa [a0, add_assoc, add_left_comm, add_comm] using
        Nat.le_add_right m (n * p ^ n + m * p ^ m + n)

end

/-! ### Lemma_10_46_6 (from Chap10) -/
universe u v

open IntermediateField

variable {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k']

private theorem mem_range_of_smul_nat_mem_range {p n : ℕ} [Fact p.Prime]
    (hchar : ringChar k ≠ p) {x : k'}
    (hx : p ^ n • x ∈ (algebraMap k k').range) : x ∈ (algebraMap k k').range := by
  rcases hx with ⟨y, hy⟩
  have hp : Nat.Prime p := Fact.out
  have hp_ne_zero : (p : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k hp hchar
  have hpn_ne_zero : ((p ^ n : k)) ≠ 0 := pow_ne_zero n hp_ne_zero
  have hmap_ne_zero : (algebraMap k k' (p ^ n : k)) ≠ 0 := by
    intro h
    exact hpn_ne_zero <| (FaithfulSMul.algebraMap_injective k k') <| by simpa using h
  refine ⟨(p ^ n : k)⁻¹ * y, ?_⟩
  calc
    algebraMap k k' ((p ^ n : k)⁻¹ * y)
        = (algebraMap k k' (p ^ n : k))⁻¹ * algebraMap k k' y := by simp
    _ = (algebraMap k k' (p ^ n : k))⁻¹ * ((p ^ n : k') * x) := by simp [hy]
    _ = ((algebraMap k k' (p ^ n : k))⁻¹ * algebraMap k k' (p ^ n : k)) * x := by
      simp [mul_assoc]
    _ = x := by rw [inv_mul_cancel₀ hmap_ne_zero, one_mul]

/-- The elements of `k'` whose some positive `p`-power and corresponding `p^n`-multiple already
lie in the image of `k`. -/
def elements_with_pow_and_scalar_mem (k : Type u) (k' : Type v) [Field k] [Field k']
    [Algebra k k'] (p : ℕ) : Set k' :=
  {x : k' |
    ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ (algebraMap k k').range ∧
      p ^ n • x ∈ (algebraMap k k').range}

/-- The extension `k'/k` is either trivial, or it has characteristic `p` and is purely
inseparable. -/
def trivial_or_char_p_purely_inseparable (k : Type u) (k' : Type v) [Field k] [Field k']
    [Algebra k k'] (p : ℕ) : Prop :=
  Function.Surjective (algebraMap k k') ∨ ringChar k = p ∧ IsPurelyInseparable k k'

/-- Lemma 10.46.6: the extension `k'/k` is generated by elements `x` for which some positive
power `x^(p^n)` and the corresponding multiple `p^n x` already lie in `k` if and only if the
extension is trivial, or it has characteristic `p` and is purely inseparable. -/
-- Proof sketch: if `ringChar k ≠ p`, then each scalar `(p ^ n : k')` is nonzero, so the condition
-- `p ^ n • x ∈ (algebraMap k k').range` already forces `x ∈ (algebraMap k k').range`;
-- hence the displayed generators all come from `k`, and the extension is trivial. In
-- characteristic `p`, the scalar condition is automatic for `n > 0`, and the remaining power
-- condition is exactly the canonical criterion
-- `IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`.
theorem generated_by_elements_with_pow_and_scalar_mem_iff
    {p : ℕ} [Fact p.Prime] :
    adjoin k (elements_with_pow_and_scalar_mem k k' p) = ⊤ ↔
      trivial_or_char_p_purely_inseparable k k' p := by
  constructor
  · intro hgen
    suffices hcriterion :
        Function.Surjective (algebraMap k k') ∨ ringChar k = p ∧ IsPurelyInseparable k k' by
      simpa [trivial_or_char_p_purely_inseparable] using hcriterion
    by_cases hchar : ringChar k = p
    · -- In characteristic `p`, the scalar condition becomes automatic, so the
      -- remaining power condition is exactly the canonical adjoin criterion.
      right
      refine ⟨hchar, ?_⟩
      haveI : CharP k p := ringChar.of_eq hchar
      haveI : ExpChar k p := inferInstance
      have hpi_adjoin :
          IsPurelyInseparable k (adjoin k (elements_with_pow_and_scalar_mem k k' p)) := by
        rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem (F := k) (E := k') p]
        intro x hx
        rcases hx with ⟨n, hn, hpow, hsmul⟩
        exact ⟨n, hpow⟩
      letI : IsPurelyInseparable k (adjoin k (elements_with_pow_and_scalar_mem k k' p)) :=
        hpi_adjoin
      let e : adjoin k (elements_with_pow_and_scalar_mem k k' p) ≃ₐ[k] k' :=
        (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
      exact e.isPurelyInseparable
    · -- Outside characteristic `p`, the scalar condition already forces each
      -- generator to lie in the base field image, so the extension is trivial.
      left
      intro x
      have hsubset_bot :
          elements_with_pow_and_scalar_mem k k' p ⊆ (⊥ : IntermediateField k k') := by
        intro y hy
        rcases hy with ⟨n, hn, hpow, hsmul⟩
        exact IntermediateField.mem_bot.mpr (mem_range_of_smul_nat_mem_range hchar hsmul)
      have hadjoin_le_bot :
          adjoin k (elements_with_pow_and_scalar_mem k k' p) ≤ (⊥ : IntermediateField k k') :=
        IntermediateField.adjoin_le_iff.mpr hsubset_bot
      have htop_le_bot : (⊤ : IntermediateField k k') ≤ (⊥ : IntermediateField k k') := by
        simpa [hgen] using hadjoin_le_bot
      have hx_top : x ∈ (⊤ : IntermediateField k k') := by
        simp
      exact IntermediateField.mem_bot.mp (htop_le_bot hx_top)
  · intro hcases
    have hcriterion :
        Function.Surjective (algebraMap k k') ∨ ringChar k = p ∧ IsPurelyInseparable k k' := by
      simpa [trivial_or_char_p_purely_inseparable] using hcases
    rcases hcriterion with hsurj | ⟨hchar, hpi⟩
    · -- If every element already comes from `k`, then the displayed generator
      -- set is all of `k'`, so adjoining it gives the whole field.
      refine eq_top_iff.mpr ?_
      intro x hx_top
      obtain ⟨y, hy⟩ := hsurj x
      have hpow_mem : x ^ (p ^ 1) ∈ (algebraMap k k').range := by
        refine ⟨y ^ (p ^ 1), ?_⟩
        simp [hy]
      have hsmul_mem : p ^ 1 • x ∈ (algebraMap k k').range := by
        refine ⟨p ^ 1 • y, ?_⟩
        simp [hy]
      exact subset_adjoin k _ ⟨1, Nat.one_pos, hpow_mem, hsmul_mem⟩
    · -- In characteristic `p`, pure inseparability gives a power-in-range
      -- witness, and increasing the exponent makes the scalar term vanish.
      haveI : CharP k p := ringChar.of_eq hchar
      haveI : ExpChar k p := inferInstance
      haveI : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
      letI : IsPurelyInseparable k k' := hpi
      refine eq_top_iff.mpr ?_
      intro x hx_top
      obtain ⟨n, hpow⟩ := IsPurelyInseparable.pow_mem (F := k) (E := k') (q := p) (x := x)
      obtain ⟨y, hy⟩ := hpow
      have hpow_mem : x ^ (p ^ (n + 1)) ∈ (algebraMap k k').range := by
        refine ⟨y ^ p, ?_⟩
        calc
          algebraMap k k' (y ^ p) = (algebraMap k k' y) ^ p := by simp
          _ = (x ^ (p ^ n)) ^ p := by simpa [hy]
          _ = x ^ (p ^ n * p) := by rw [pow_mul]
          _ = x ^ (p * p ^ n) := by rw [Nat.mul_comm]
          _ = x ^ (p ^ (n + 1)) := by rw [Nat.pow_succ']
      have hp_pow_zero : ((p ^ (n + 1) : ℕ) : k') = 0 := by
        rw [CharP.cast_eq_zero_iff k' p]
        refine ⟨p ^ n, ?_⟩
        rw [Nat.pow_succ, Nat.mul_comm]
      have hsmul_zero : p ^ (n + 1) • x = 0 := by
        rw [nsmul_eq_mul, hp_pow_zero, zero_mul]
      have hsmul_mem : p ^ (n + 1) • x ∈ (algebraMap k k').range := by
        refine ⟨0, ?_⟩
        rw [hsmul_zero]
        simp
      exact subset_adjoin k _ ⟨n + 1, Nat.succ_pos _, hpow_mem, hsmul_mem⟩
