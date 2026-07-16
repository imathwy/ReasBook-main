import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Definition_10_32_1
import stacks_proof.stacks_project.Chap10.Lemma_10_46_4
import stacks_proof.stacks_project.Chap10.Lemma_10_46_5
import stacks_proof.stacks_project.Chap10.Lemma_10_46_6
import stacks_proof.stacks_project.Chap10.Lemma_10_46_8

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {p : ℕ} [Fact p.Prime] (f : R →+* S)

namespace RingHom

/-- Source-facing generator predicate for Lemma 10.46.7: `S` is generated as an `R`-algebra by
elements `x` such that some positive `p^n`-th power of `x` and the corresponding scalar multiple
`p^n • x` both lie in the image of `f`. -/
def IsGeneratedByPrimePowerAndScalarImage (f : R →+* S) (p : ℕ) [Fact p.Prime] : Prop :=
  let _ : Algebra R S := f.toAlgebra
  Algebra.adjoin R
      {x : S |
        ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range} = ⊤

end RingHom

/- The homeomorphism owner theorem used below is the canonical theorem
`PrimeSpectrum.isHomeomorph_comap`. -/
recall PrimeSpectrum.isHomeomorph_comap

/-- Helper for Lemma 10.46.7: base-ring elements satisfy the prime-power/scalar-image predicate
with exponent `1`. -/
lemma primePowerAndScalarImage_map_mem
    (r : R) :
    ∃ n : ℕ, 0 < n ∧ (f r) ^ (p ^ n) ∈ f.range ∧ p ^ n • f r ∈ f.range := by
  -- The source proof treats base-ring elements as trivial generators.
  refine ⟨1, Nat.one_pos, ?_, ?_⟩
  · exact ⟨r ^ (p ^ 1), by simp⟩
  · exact ⟨p ^ 1 • r, by simp⟩

/-- Helper for Lemma 10.46.7: the generator predicate is multiplicatively closed. -/
lemma primePowerAndScalarImage_mul_mem
    {x y : S}
    (hx : ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range)
    (hy : ∃ m : ℕ, 0 < m ∧ y ^ (p ^ m) ∈ f.range ∧ p ^ m • y ∈ f.range) :
    ∃ a : ℕ, 0 < a ∧ (x * y) ^ (p ^ a) ∈ f.range ∧ p ^ a • (x * y) ∈ f.range := by
  rcases hx with ⟨n, hn, hxpow, hxsmul⟩
  rcases hy with ⟨m, hm, hypow, hysmul⟩
  refine ⟨n + m, by omega, ?_, ?_⟩
  · rcases hxpow with ⟨rx, hrx⟩
    rcases hypow with ⟨ry, hry⟩
    refine ⟨rx ^ (p ^ m) * ry ^ (p ^ n), ?_⟩
    -- Raise each source witness to the complementary `p`-power and multiply them.
    calc
      f (rx ^ (p ^ m) * ry ^ (p ^ n))
          = f (rx ^ (p ^ m)) * f (ry ^ (p ^ n)) := by simp
      _ = (f rx) ^ (p ^ m) * (f ry) ^ (p ^ n) := by simp
      _ = (x ^ (p ^ n)) ^ (p ^ m) * (y ^ (p ^ m)) ^ (p ^ n) := by simp [hrx, hry]
      _ = x ^ (p ^ n * p ^ m) * y ^ (p ^ m * p ^ n) := by rw [pow_mul, pow_mul]
      _ = x ^ (p ^ (n + m)) * y ^ (p ^ (n + m)) := by rw [Nat.pow_add, Nat.mul_comm]
      _ = (x * y) ^ (p ^ (n + m)) := by rw [mul_pow]
  · rcases hxsmul with ⟨rx, hrx⟩
    rcases hysmul with ⟨ry, hry⟩
    refine ⟨rx * ry, ?_⟩
    -- Multiplying the two scalar witnesses produces the desired larger scalar multiple.
    calc
      f (rx * ry) = f rx * f ry := by simp
      _ = (p ^ n • x) * (p ^ m • y) := by simp [hrx, hry]
      _ = p ^ (n + m) • (x * y) := by
            simp [nsmul_eq_mul, Nat.pow_add, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 10.46.7: the generator predicate is additively closed by evaluating the
universal polynomial statement from Lemma `10.46.5`. -/
lemma primePowerAndScalarImage_add_mem
    {x y : S}
    (hx : ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range)
    (hy : ∃ m : ℕ, 0 < m ∧ y ^ (p ^ m) ∈ f.range ∧ p ^ m • y ∈ f.range) :
    ∃ a : ℕ, 0 < a ∧ (x + y) ^ (p ^ a) ∈ f.range ∧ p ^ a • (x + y) ∈ f.range := by
  rcases hx with ⟨n, hn, hxpow, hxsmul⟩
  rcases hy with ⟨m, hm, hypow, hysmul⟩
  let φ : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] S := MvPolynomial.aeval ![x, y]
  let G : Set (MvPolynomial (Fin 2) ℤ) :=
    {MvPolynomial.X (0 : Fin 2) ^ (p ^ n), p ^ n • MvPolynomial.X (0 : Fin 2),
      MvPolynomial.X (1 : Fin 2) ^ (p ^ m), p ^ m • MvPolynomial.X (1 : Fin 2)}
  have hmem_range :
      ∀ z : MvPolynomial (Fin 2) ℤ, z ∈ Algebra.adjoin ℤ G → φ z ∈ f.range := by
    intro z hz
    -- Any polynomial built from the four displayed generators evaluates into `f.range`.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
    · intro z hzG
      simp only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hzG
      rcases hzG with rfl | rfl | rfl | rfl
      · simpa [φ] using hxpow
      · simpa [φ] using hxsmul
      · simpa [φ] using hypow
      · simpa [φ] using hysmul
    · intro z
      exact ⟨(z : R), by simpa [φ] using (f.map_intCast z)⟩
    · intro z w _ _ hz hw
      rcases hz with ⟨rz, hrz⟩
      rcases hw with ⟨rw, hrw⟩
      refine ⟨rz + rw, ?_⟩
      calc
        f (rz + rw) = f rz + f rw := by simp
        _ = φ z + φ w := by rw [hrz, hrw]
        _ = φ (z + w) := by simp [φ]
    · intro z w _ _ hz hw
      rcases hz with ⟨rz, hrz⟩
      rcases hw with ⟨rw, hrw⟩
      refine ⟨rz * rw, ?_⟩
      calc
        f (rz * rw) = f rz * f rw := by simp
        _ = φ z * φ w := by rw [hrz, hrw]
        _ = φ (z * w) := by simp [φ]
  let a : ℕ := n * p ^ n + m * p ^ m + n + m
  have ha_pos : 0 < a := by
    -- The explicit exponent from Lemma `10.46.5` is visibly positive because both witnesses are.
    dsimp [a]
    omega
  have hpow_mem_poly :
      (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ (p ^ a) ∈ Algebra.adjoin ℤ G := by
    -- This is the polynomial half of Lemma `10.46.5`.
    simpa [G, a] using
      binomial_power_mem_mixedPowerMultipleSubalgebra (p := p) (n := n) (m := m) (Fact.out)
  have hsmul_mem_poly :
      p ^ a • (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ∈ Algebra.adjoin ℤ G := by
    -- The linear half of Lemma `10.46.5` applies because the chosen exponent dominates `n` and `m`.
    refine sum_multiple_mem_mixedPowerMultipleSubalgebra_of_le (p := p) (n := n) (m := m) (a := a)
      ?_ ?_
    · dsimp [a]
      omega
    · dsimp [a]
      omega
  refine ⟨a, ha_pos, ?_, ?_⟩
  · -- Evaluate the polynomial power statement at `(x, y)`.
    simpa [φ, a] using hmem_range _ hpow_mem_poly
  · -- Evaluate the polynomial scalar-multiple statement at `(x, y)`.
    simpa [φ, a] using hmem_range _ hsmul_mem_poly

/-- Helper for Lemma 10.46.7: once the displayed generators adjoin to all of `S`, every element
of `S` satisfies the prime-power/scalar-image predicate. -/
lemma mem_primePowerAndScalarImage_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p) :
    ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range := by
  let _ : Algebra R S := f.toAlgebra
  let G : Set S :=
    {x : S | ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range}
  have hgen' : Algebra.adjoin R G = ⊤ := by
    simpa [RingHom.IsGeneratedByPrimePowerAndScalarImage, G] using hgen
  intro x
  have hx : x ∈ Algebra.adjoin R G := by
    rw [hgen']
    simp
  -- The source proof shows the predicate defines an `R`-subalgebra, then uses generation.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact hy
  · intro r
    simpa [RingHom.algebraMap_toAlgebra] using primePowerAndScalarImage_map_mem (f := f) (p := p) r
  · intro y z _ _ hy hz
    exact primePowerAndScalarImage_add_mem (f := f) (p := p) hy hz
  · intro y z _ _ hy hz
    exact primePowerAndScalarImage_mul_mem (f := f) (p := p) hy hz

/-- Helper for Lemma 10.46.7: the image of `S / q` inside `κ(q)` is generated as a subring by the
image of `R` together with the images of elements satisfying the prime-power/scalar-image
predicate. -/
lemma residueField_image_range_eq_closure_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p)
    (q : PrimeSpectrum S) :
    let _ : Algebra R S := f.toAlgebra
    let G : Set S :=
      {x : S | ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range}
    let gS : S →ₐ[R] q.asIdeal.ResidueField := IsScalarTower.toAlgHom R S q.asIdeal.ResidueField
    ((algebraMap (S ⧸ q.asIdeal) q.asIdeal.ResidueField) : S ⧸ q.asIdeal →+* q.asIdeal.ResidueField).range =
      Subring.closure
        (Set.range (algebraMap R q.asIdeal.ResidueField) ∪ ((gS : S → q.asIdeal.ResidueField) '' G)) := by
  let _ : Algebra R S := f.toAlgebra
  let G : Set S :=
    {x : S | ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range}
  let gS : S →ₐ[R] q.asIdeal.ResidueField := IsScalarTower.toAlgHom R S q.asIdeal.ResidueField
  have hgen' : Algebra.adjoin R G = ⊤ := by
    simpa [RingHom.IsGeneratedByPrimePowerAndScalarImage, G] using hgen
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
  have hs :
      (gS : S →+* q.asIdeal.ResidueField).range =
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

/-- Helper for Lemma 10.46.7: the subfield of `κ(q)` generated by the image of `R` together with
the images of the prime-power/scalar-image generators is all of `κ(q)`. -/
lemma residueField_closure_eq_top_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p)
    (q : PrimeSpectrum S) :
    let _ : Algebra R S := f.toAlgebra
    let G : Set S :=
      {x : S | ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range}
    Subfield.closure
      (Set.range (algebraMap R q.asIdeal.ResidueField) ∪
        ((algebraMap S q.asIdeal.ResidueField) '' G)) = ⊤ := by
  let _ : Algebra R S := f.toAlgebra
  let G : Set S :=
    {x : S | ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range}
  let gA : S ⧸ q.asIdeal →+* q.asIdeal.ResidueField := algebraMap _ _
  have hgA : Function.Injective gA := q.asIdeal.injective_algebraMap_quotient_residueField
  have hs :
      gA.range =
        Subring.closure
          (Set.range (algebraMap R q.asIdeal.ResidueField) ∪
            ((algebraMap S q.asIdeal.ResidueField) '' G)) := by
    simpa [G] using
      residueField_image_range_eq_closure_of_isGeneratedByPrimePowerAndScalarImage
        (f := f) (p := p) hgen q
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

/-- Helper for Lemma 10.46.7: a source generator transports to a residue-field generator for the
induced map `κ(q ∩ R) → κ(q)`. -/
lemma residueField_generator_image_mem_primePowerAndScalarImage
    (q : PrimeSpectrum S)
    {x : S}
    (hx : ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range) :
    let p' : PrimeSpectrum R := comap f q
    let fκ := Ideal.ResidueField.map p'.asIdeal q.asIdeal f rfl
    let _ : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    algebraMap S q.asIdeal.ResidueField x ∈
      elements_with_pow_and_scalar_mem p'.asIdeal.ResidueField q.asIdeal.ResidueField p := by
  let p' : PrimeSpectrum R := comap f q
  let fκ : p'.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p'.asIdeal q.asIdeal f rfl
  let _ : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
  rcases hx with ⟨n, hn, hxpow, hxsmul⟩
  refine ⟨n, hn, ?_, ?_⟩
  · rcases hxpow with ⟨r, hr⟩
    refine ⟨algebraMap R p'.asIdeal.ResidueField r, ?_⟩
    -- Transport the power witness along the canonical residue-field map.
    calc
      fκ (algebraMap R p'.asIdeal.ResidueField r) =
          algebraMap S q.asIdeal.ResidueField (f r) := by
            simpa [fκ] using
              (Ideal.ResidueField.map_algebraMap p'.asIdeal q.asIdeal f rfl r)
      _ = algebraMap S q.asIdeal.ResidueField (x ^ (p ^ n)) := by simpa [hr]
      _ = (algebraMap S q.asIdeal.ResidueField x) ^ (p ^ n) := by simp
  · rcases hxsmul with ⟨r, hr⟩
    refine ⟨algebraMap R p'.asIdeal.ResidueField r, ?_⟩
    -- The scalar witness transports in exactly the same way.
    calc
      fκ (algebraMap R p'.asIdeal.ResidueField r) =
          algebraMap S q.asIdeal.ResidueField (f r) := by
            simpa [fκ] using
              (Ideal.ResidueField.map_algebraMap p'.asIdeal q.asIdeal f rfl r)
      _ = algebraMap S q.asIdeal.ResidueField (p ^ n • x) := by simpa [hr]
      _ = p ^ n • algebraMap S q.asIdeal.ResidueField x := by simp

-- Proof sketch: pass the displayed generation condition to each residue-field map
-- `κ(q ∩ R) → κ(q)`. Lemma `10.46.6` then gives exactly the source-facing alternative:
-- either the residue-field map is surjective, or the source has characteristic `p` and the target
-- extension is purely inseparable.
/-- Lemma 10.46.7, source-facing residue-field clause: the generator predicate above implies the
residue-field criterion from Lemma `10.46.6` at every prime of `S`. -/
@[stacks 0BRA]
theorem residueFieldMapsSurjectiveOrCharPPurelyInseparable_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p)
    (q : PrimeSpectrum S) :
    let p' : PrimeSpectrum R := comap f q
    let fκ := Ideal.ResidueField.map p'.asIdeal q.asIdeal f rfl
    let _ : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    Function.Surjective fκ ∨
      ringChar p'.asIdeal.ResidueField = p ∧
        IsPurelyInseparable p'.asIdeal.ResidueField q.asIdeal.ResidueField := by
  let _ : Algebra R S := f.toAlgebra
  let p' : PrimeSpectrum R := comap f q
  let fκ : p'.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p'.asIdeal q.asIdeal f rfl
  let _ : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
  let G : Set S :=
    {x : S | ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range}
  have hclosure_le :
      Subfield.closure
        (Set.range (algebraMap p'.asIdeal.ResidueField q.asIdeal.ResidueField) ∪
          ((algebraMap S q.asIdeal.ResidueField) '' G)) ≤
        (IntermediateField.adjoin p'.asIdeal.ResidueField
          (elements_with_pow_and_scalar_mem
            p'.asIdeal.ResidueField q.asIdeal.ResidueField p)).toSubfield := by
    refine Subfield.closure_le.mpr ?_
    intro y hy
    rcases hy with hyR | hyG
    · exact IntermediateField.set_range_subset _ hyR
    · rcases hyG with ⟨x, hx, rfl⟩
      -- Each chosen generator image already lies in the adjoined predicate set.
      exact IntermediateField.subset_adjoin p'.asIdeal.ResidueField _ <|
        residueField_generator_image_mem_primePowerAndScalarImage
          (f := f) (p := p) q hx
  have hadjoin_top :
      IntermediateField.adjoin p'.asIdeal.ResidueField
        (elements_with_pow_and_scalar_mem p'.asIdeal.ResidueField q.asIdeal.ResidueField p) = ⊤ := by
    -- Route correction: prove top generation through the closure/top lemma, then invoke Lemma `10.46.6`.
    have hclosure_top_R :
        Subfield.closure
          (Set.range (algebraMap R q.asIdeal.ResidueField) ∪
            ((algebraMap S q.asIdeal.ResidueField) '' G)) = ⊤ := by
      simpa [G] using
        residueField_closure_eq_top_of_isGeneratedByPrimePowerAndScalarImage
          (f := f) (p := p) hgen q
    have hbase_subset :
        Set.range (algebraMap R q.asIdeal.ResidueField) ⊆
          Set.range (algebraMap p'.asIdeal.ResidueField q.asIdeal.ResidueField) := by
      intro y hy
      rcases hy with ⟨r, rfl⟩
      refine ⟨algebraMap R p'.asIdeal.ResidueField r, ?_⟩
      calc
        algebraMap p'.asIdeal.ResidueField q.asIdeal.ResidueField (algebraMap R p'.asIdeal.ResidueField r)
            = fκ (algebraMap R p'.asIdeal.ResidueField r) := by rfl
        _ = algebraMap S q.asIdeal.ResidueField (f r) := by
              simpa [fκ] using
                (Ideal.ResidueField.map_algebraMap p'.asIdeal q.asIdeal f rfl r)
        _ = algebraMap R q.asIdeal.ResidueField r := by
              simpa [RingHom.algebraMap_toAlgebra] using
                (IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField r)
    have hclosure_top :
        Subfield.closure
          (Set.range (algebraMap p'.asIdeal.ResidueField q.asIdeal.ResidueField) ∪
            ((algebraMap S q.asIdeal.ResidueField) '' G)) = ⊤ := by
      apply top_unique
      rw [← hclosure_top_R]
      exact Subfield.closure_le.mpr <|
        Set.union_subset
          (fun y hy => Subfield.subset_closure (Or.inl (hbase_subset hy)))
          (fun y hy => Subfield.subset_closure (Or.inr hy))
    apply top_unique
    intro y hy
    have hy' :
        y ∈ Subfield.closure
          (Set.range (algebraMap p'.asIdeal.ResidueField q.asIdeal.ResidueField) ∪
            ((algebraMap S q.asIdeal.ResidueField) '' G)) := by
      rw [hclosure_top]
      simpa using hy
    exact hclosure_le hy'
  -- Apply the field-level criterion from Lemma `10.46.6` to the generated residue field.
  simpa [trivial_or_char_p_purely_inseparable, fκ] using
    (generated_by_elements_with_pow_and_scalar_mem_iff
      (k := p'.asIdeal.ResidueField) (k' := q.asIdeal.ResidueField) (p := p)).mp hadjoin_top

-- Proof sketch: apply the source-facing residue-field clause above at each prime `q : Spec(S)`
-- and then package the purely inseparable branch into the owner predicate
-- `RingHom.HasPurelyInseparableResidueFieldExtensions`.
private theorem hasPurelyInseparableResidueFieldExtensions_of_residueFieldCriterion
    (hres : ∀ q : PrimeSpectrum S,
      let p' : PrimeSpectrum R := comap f q
      let fκ := Ideal.ResidueField.map p'.asIdeal q.asIdeal f rfl
      let _ : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
      Function.Surjective fκ ∨
        ringChar p'.asIdeal.ResidueField = p ∧
          IsPurelyInseparable p'.asIdeal.ResidueField q.asIdeal.ResidueField) :
    f.HasPurelyInseparableResidueFieldExtensions := by
  intro q
  let p' : PrimeSpectrum R := comap f q
  let fκ : p'.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p'.asIdeal q.asIdeal f rfl
  let _ : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
  have hcases :
      Function.Surjective fκ ∨
        ringChar p'.asIdeal.ResidueField = p ∧
          IsPurelyInseparable p'.asIdeal.ResidueField q.asIdeal.ResidueField := by
    simpa [p', fκ] using hres q
  rcases hcases with hsurj | hpi
  · -- A surjective residue-field map is an algebra isomorphism, hence purely inseparable.
    let e : p'.asIdeal.ResidueField ≃ₐ[p'.asIdeal.ResidueField] q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective (Algebra.ofId p'.asIdeal.ResidueField q.asIdeal.ResidueField)
        ⟨FaithfulSMul.algebraMap_injective p'.asIdeal.ResidueField q.asIdeal.ResidueField, hsurj⟩
    exact e.isPurelyInseparable
  · exact hpi.2

/-- Lemma 10.46.7, bridge/view form: the generator predicate implies the owner predicate
`RingHom.HasPurelyInseparableResidueFieldExtensions`. -/
@[stacks 0BRA]
theorem hasPurelyInseparableResidueFieldExtensions_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p) :
    f.HasPurelyInseparableResidueFieldExtensions := by
  exact
    hasPurelyInseparableResidueFieldExtensions_of_residueFieldCriterion
      f
      (residueFieldMapsSurjectiveOrCharPPurelyInseparable_of_isGeneratedByPrimePowerAndScalarImage
        f hgen)

-- Proof sketch: the same generators show that every element of `S` has some positive power in the
-- image of `f`, which is the source-facing bridge needed for `PrimeSpectrum.isHomeomorph_comap`.
/-- Under the generation hypothesis of Lemma 10.46.7, every element of `S` has a positive power in
the image of `f`. -/
theorem exists_pow_mem_range_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p) :
    ∀ x : S, ∃ n > 0, x ^ n ∈ f.range := by
  intro x
  rcases
      mem_primePowerAndScalarImage_of_isGeneratedByPrimePowerAndScalarImage
        (f := f) (p := p) hgen x with
    ⟨n, hn, hxpow, -⟩
  have hp : Nat.Prime p := Fact.out
  -- Forget the scalar half of the witness and keep the positive `p^n`-power.
  exact ⟨p ^ n, Nat.pow_pos hp.pos, hxpow⟩

-- Proof sketch: combine the positive-power-in-range bridge above with the locally nilpotent kernel
-- hypothesis and apply the canonical theorem `PrimeSpectrum.isHomeomorph_comap`.
/-- Lemma 10.46.7, homeomorphism clause: if in addition `ker f` is locally nilpotent, then
`Spec(S) → Spec(R)` is a homeomorphism. -/
@[stacks 0BRA]
theorem isHomeomorph_comap_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    IsHomeomorph (comap f) := by
  exact PrimeSpectrum.isHomeomorph_comap f
    (exists_pow_mem_range_of_isGeneratedByPrimePowerAndScalarImage f hgen)
    (by simpa [Ideal.IsLocallyNilpotent] using hker)

variable {R' : Type w} [CommRing R'] [Algebra R R']

/-- Helper for Lemma 10.46.7: after base change, an element coming from `R` maps to the pure tensor
`1 ⊗ₜ[R] f r`. -/
lemma baseChange_algebraMap_eq_one_tmul
    (r : R) :
    let _ : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f' (algebraMap R R' r) = (1 : R') ⊗ₜ[R] f r := by
  let _ : Algebra R S := f.toAlgebra
  let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
  -- Rewrite through the scalar tower and then use the canonical tensor-product algebra map formula.
  calc
    f' (algebraMap R R' r) = algebraMap R (R' ⊗[R] S) r := by
      rw [← IsScalarTower.algebraMap_apply R R' (R' ⊗[R] S)]
    _ = (1 : R') ⊗ₜ[R] f r := by
      simpa [RingHom.algebraMap_toAlgebra] using
        (Algebra.TensorProduct.algebraMap_apply' (R := R) (A := R') (B := S) r)

/-- Helper for Lemma 10.46.7: tensoring with `1` commutes with the natural-number scalar multiple
appearing in the scalar witness. -/
lemma one_tmul_nsmul_eq_natCast_mul
    (x : S) (n : ℕ) :
    let _ : Algebra R S := f.toAlgebra
    (1 : R') ⊗ₜ[R] (p ^ n • x) = (p ^ n : R' ⊗[R] S) * ((1 : R') ⊗ₜ[R] x) := by
  let _ : Algebra R S := f.toAlgebra
  -- Move the scalar to the left tensor factor and then rewrite the resulting tensor as a product.
  calc
    (1 : R') ⊗ₜ[R] (p ^ n • x) = (((p ^ n : R) • (1 : R')) ⊗ₜ[R] x) := by
      simpa [Algebra.smul_def] using
        (TensorProduct.smul_tmul (R := R) (r := (p ^ n : R)) (m := (1 : R')) (n := x)).symm
    _ = ((p ^ n : R') ⊗ₜ[R] x) := by
      simp [Algebra.smul_def]
    _ = (p ^ n : R' ⊗[R] S) * ((1 : R') ⊗ₜ[R] x) := by
      symm
      rw [Algebra.TensorProduct.natCast_def]
      simpa using
        (Algebra.TensorProduct.tmul_mul_tmul
          (R := R) (a₁ := (p ^ n : R')) (a₂ := (1 : R')) (b₁ := (1 : S)) (b₂ := x))

/-- Helper for Lemma 10.46.7: a scalar witness `f r = p^n • x` remains a scalar witness after base
change. -/
lemma baseChange_scalar_witness_eq
    (x : S) (n : ℕ) (r : R)
    (hr : f r = p ^ n • x) :
    let _ : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f' (algebraMap R R' r) = p ^ n • ((1 : R') ⊗ₜ[R] x) := by
  let _ : Algebra R S := f.toAlgebra
  let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
  -- Normalize the source element to `1 ⊗ₜ[R] f r` and then transport the scalar witness through
  -- the tensor-product `nsmul` identity.
  calc
    f' (algebraMap R R' r) = (1 : R') ⊗ₜ[R] f r := by
      simpa using baseChange_algebraMap_eq_one_tmul (f := f) (R' := R') r
    _ = (1 : R') ⊗ₜ[R] (p ^ n • x) := by simpa [hr]
    _ = p ^ n • ((1 : R') ⊗ₜ[R] x) := by
      simpa [nsmul_eq_mul] using
        one_tmul_nsmul_eq_natCast_mul
          (f := f) (p := p) (R' := R') (x := x) (n := n)

/-- Lemma 10.46.7, base-change generation clause: for every ring map `R → R'`, the canonical
base-changed map `R' → R' ⊗[R] S` satisfies the same generation hypothesis. -/
@[stacks 0BRA]
theorem isGeneratedByPrimePowerAndScalarImage_baseChange_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p) :
    let _ : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f'.IsGeneratedByPrimePowerAndScalarImage p := by
  let _ : Algebra R S := f.toAlgebra
  let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
  let G : Set S :=
    {x : S | ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range}
  dsimp [RingHom.IsGeneratedByPrimePowerAndScalarImage]
  have htop :
      Algebra.adjoin R' (((1 : R') ⊗ₜ[R] ·) '' G) = ⊤ := by
    -- The original generating set still generates after literal base change.
    simpa [RingHom.IsGeneratedByPrimePowerAndScalarImage, G] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := R') (s := G) hgen
  have hsubset :
      (((1 : R') ⊗ₜ[R] ·) '' G) ⊆
        {y : R' ⊗[R] S |
          ∃ n : ℕ, 0 < n ∧ y ^ (p ^ n) ∈ f'.range ∧ p ^ n • y ∈ f'.range} := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨n, hn, hxpow, hxsmul⟩
    refine ⟨n, hn, ?_, ?_⟩
    · rcases hxpow with ⟨r, hr⟩
      refine ⟨algebraMap R R' r, ?_⟩
      -- Transport the power witness along the canonical tensor-product algebra map.
      calc
        f' (algebraMap R R' r) = (1 : R') ⊗ₜ[R] f r := by
          simpa using baseChange_algebraMap_eq_one_tmul (f := f) (R' := R') r
        _ = (1 : R') ⊗ₜ[R] (x ^ (p ^ n)) := by simpa [hr]
        _ = ((1 : R') ⊗ₜ[R] x) ^ (p ^ n) := by simp
    · rcases hxsmul with ⟨r, hr⟩
      refine ⟨algebraMap R R' r, ?_⟩
      -- The scalar witness survives after base change by the dedicated tensor-product rewrite.
      simpa using
        baseChange_scalar_witness_eq
          (f := f) (R' := R') (p := p) (x := x) (n := n) (r := r) hr
  have hadjoin_le :
      Algebra.adjoin R' (((1 : R') ⊗ₜ[R] ·) '' G) ≤
        Algebra.adjoin R'
          {y : R' ⊗[R] S |
            ∃ n : ℕ, 0 < n ∧ y ^ (p ^ n) ∈ f'.range ∧ p ^ n • y ∈ f'.range} := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    exact Algebra.subset_adjoin (hsubset hy)
  have htop_le :
      (⊤ : Subalgebra R' (R' ⊗[R] S)) ≤
        Algebra.adjoin R'
          {y : R' ⊗[R] S |
            ∃ n : ℕ, 0 < n ∧ y ^ (p ^ n) ∈ f'.range ∧ p ^ n • y ∈ f'.range} := by
    rw [← htop]
    exact hadjoin_le
  exact top_unique htop_le

-- Proof sketch: combine the base-change generation clause above with stability of locally
-- nilpotent kernels under arbitrary base change.
/-- Lemma 10.46.7, source-facing full base-change clause: for every ring map `R → R'`, if `ker f`
is locally nilpotent, then the canonical base-changed map `R' → R' ⊗[R] S` satisfies the same
generation hypothesis and has locally nilpotent kernel. -/
@[stacks 0BRA]
theorem isGeneratedByPrimePowerAndScalarImage_and_ker_baseChange_isLocallyNilpotent_of_isGeneratedByPrimePowerAndScalarImage
    (hgen : f.IsGeneratedByPrimePowerAndScalarImage p)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    let _ : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f'.IsGeneratedByPrimePowerAndScalarImage p ∧
      (RingHom.ker f').IsLocallyNilpotent := by
  let _ : Algebra R S := f.toAlgebra
  let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
  have hhomeo : IsHomeomorph (comap f) :=
    isHomeomorph_comap_of_isGeneratedByPrimePowerAndScalarImage (f := f) (p := p) hgen hker
  have hsurj' : Function.Surjective (comap f') :=
    specComap_surjective_stable_under_baseChange
      (R := R) (S := S) (R' := R') hhomeo.surjective
  have hker' : (RingHom.ker f').IsLocallyNilpotent := by
    -- Surjectivity of spectra after base change rewrites back to the nilradical condition.
    exact (denseRange_comap_iff_ker_le_nilRadical f').mp hsurj'.denseRange
  exact ⟨isGeneratedByPrimePowerAndScalarImage_baseChange_of_isGeneratedByPrimePowerAndScalarImage
    (f := f) (p := p) (R' := R') hgen, hker'⟩

end
