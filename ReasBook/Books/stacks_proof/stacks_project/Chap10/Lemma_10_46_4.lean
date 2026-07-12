import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_32_1
import StacksProject_2024.Chap10.Lemma_10_30_3
import StacksProject_2024.Chap10.Lemma_10_30_6

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 0EUH]
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
@[stacks 0EUH]
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
