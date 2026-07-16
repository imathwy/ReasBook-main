import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_7_8.RegularPrimeResidueEvaluation

open scoped Representation

noncomputable section

universe v w

namespace Representation

section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: on `p`-regular conjugacy classes, owner evaluation sends the
zero owner element to the constant function `0`. -/
@[simp] private theorem owner_pregular_eval_zero
    (c : PRegularConjClass G p) :
    owner_pregular_eval (A := A) (K := K) (G := G) (p := p) 0 c = 0 := by
  obtain ⟨x, rfl⟩ := pRegularConjClass_ofSubtype_surjective (G := G) (p := p) c
  simp [owner_pregular_eval_ofSubtype]

/-- Helper for Exercise 12-12.7-8: on `p`-regular conjugacy classes, owner evaluation sends the
unit owner element to the constant function `1`. -/
@[simp] private theorem owner_pregular_eval_one
    (c : PRegularConjClass G p) :
    owner_pregular_eval (A := A) (K := K) (G := G) (p := p) 1 c = 1 := by
  obtain ⟨x, rfl⟩ := pRegularConjClass_ofSubtype_surjective (G := G) (p := p) c
  simp [owner_pregular_eval_ofSubtype]

/-- Helper for Exercise 12-12.7-8: evaluating an `A`-scalar inside the owner subalgebra on a
`p`-regular conjugacy class returns the corresponding scalar in `K`. -/
@[simp] private theorem owner_pregular_eval_algebraMap
    (a : A) (c : PRegularConjClass G p) :
    owner_pregular_eval (A := A) (K := K) (G := G) (p := p)
        (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a) c =
      algebraMap A K a := by
  obtain ⟨x, rfl⟩ := pRegularConjClass_ofSubtype_surjective (G := G) (p := p) c
  simp [owner_pregular_eval_ofSubtype]

/-- Helper for Exercise 12-12.7-8: on `p`-regular conjugacy classes, owner evaluation is
additive. -/
@[simp] private theorem owner_pregular_eval_add
    (f g : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (c : PRegularConjClass G p) :
    owner_pregular_eval (A := A) (K := K) (G := G) (p := p) (f + g) c =
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c +
        owner_pregular_eval (A := A) (K := K) (G := G) (p := p) g c := by
  obtain ⟨x, rfl⟩ := pRegularConjClass_ofSubtype_surjective (G := G) (p := p) c
  simp [owner_pregular_eval_ofSubtype]

/-- Helper for Exercise 12-12.7-8: on `p`-regular conjugacy classes, owner evaluation is
multiplicative. -/
@[simp] private theorem owner_pregular_eval_mul
    (f g : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (c : PRegularConjClass G p) :
    owner_pregular_eval (A := A) (K := K) (G := G) (p := p) (f * g) c =
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c *
        owner_pregular_eval (A := A) (K := K) (G := G) (p := p) g c := by
  obtain ⟨x, rfl⟩ := pRegularConjClass_ofSubtype_surjective (G := G) (p := p) c
  simp [owner_pregular_eval_ofSubtype]

/-- Helper for Exercise 12-12.7-8: reducing chosen `A`-lifts modulo `M` commutes with addition.
-/
private theorem residueFieldOfLiftedValue_add
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {z w : K} (hz : z ∈ Set.range (algebraMap A K))
    (hw : w ∈ Set.range (algebraMap A K))
    (hsum : z + w ∈ Set.range (algebraMap A K)) :
    residueFieldOfLiftedValue (A := A) (K := K) (p := p) M (z + w) hsum =
      residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z hz +
        residueFieldOfLiftedValue (A := A) (K := K) (p := p) M w hw := by
  let a : A := Classical.choose hz
  let b : A := Classical.choose hw
  have ha : algebraMap A K a = z := Classical.choose_spec hz
  have hb : algebraMap A K b = w := Classical.choose_spec hw
  have hab : algebraMap A K (a + b) = z + w := by
    calc
      algebraMap A K (a + b) = algebraMap A K a + algebraMap A K b := map_add _ _ _
      _ = z + w := by rw [ha, hb]
  rw [residueFieldOfLiftedValue_eq_algebraMap
      (A := A) (K := K) (p := p) M hsum (a + b) hab,
    residueFieldOfLiftedValue_eq_algebraMap (A := A) (K := K) (p := p) M hz a ha,
    residueFieldOfLiftedValue_eq_algebraMap (A := A) (K := K) (p := p) M hw b hb,
    map_add]

/-- Helper for Exercise 12-12.7-8: reducing chosen `A`-lifts modulo `M` commutes with
multiplication. -/
private theorem residueFieldOfLiftedValue_mul
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {z w : K} (hz : z ∈ Set.range (algebraMap A K))
    (hw : w ∈ Set.range (algebraMap A K))
    (hprod : z * w ∈ Set.range (algebraMap A K)) :
    residueFieldOfLiftedValue (A := A) (K := K) (p := p) M (z * w) hprod =
      residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z hz *
        residueFieldOfLiftedValue (A := A) (K := K) (p := p) M w hw := by
  let a : A := Classical.choose hz
  let b : A := Classical.choose hw
  have ha : algebraMap A K a = z := Classical.choose_spec hz
  have hb : algebraMap A K b = w := Classical.choose_spec hw
  have hab : algebraMap A K (a * b) = z * w := by
    calc
      algebraMap A K (a * b) = algebraMap A K a * algebraMap A K b := map_mul _ _ _
      _ = z * w := by rw [ha, hb]
  rw [residueFieldOfLiftedValue_eq_algebraMap
      (A := A) (K := K) (p := p) M hprod (a * b) hab,
    residueFieldOfLiftedValue_eq_algebraMap (A := A) (K := K) (p := p) M hz a ha,
    residueFieldOfLiftedValue_eq_algebraMap (A := A) (K := K) (p := p) M hw b hb,
    map_mul]

/-- Helper for Exercise 12-12.7-8: if one has a global theorem saying every owner value on every
`p`-regular class already comes from `A`, then the pointwise residue evaluator respects
`A`-scalars. -/
private theorem owner_pregular_residue_eval_of_range_algebraMap
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hRange :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        ∀ c : PRegularConjClass G p,
          owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
            Set.range (algebraMap A K))
    (a : A) :
    owner_pregular_residue_eval_of_range (A := A) (K := K) (G := G) (p := p) M
        (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a)
        (hRange (algebraMap A
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a)) =
      algebraMap A (PRegularConjClass G p → M.1.asIdeal.ResidueField) a := by
  ext c
  rw [owner_pregular_residue_eval_of_range]
  simpa using
    (residueFieldOfLiftedValue_eq_algebraMap
      (A := A) (K := K) (p := p) M
      (hRange (algebraMap A
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a) c)
      a
      (by simpa using
        (owner_pregular_eval_algebraMap (A := A) (K := K) (G := G) (p := p) a c).symm))

/-- Helper for Exercise 12-12.7-8: if every owner value on every `p`-regular class already comes
from `A`, then the pointwise residue evaluator is additive. -/
private theorem owner_pregular_residue_eval_of_range_add
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hRange :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        ∀ c : PRegularConjClass G p,
          owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
            Set.range (algebraMap A K))
    (f g : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    owner_pregular_residue_eval_of_range (A := A) (K := K) (G := G) (p := p) M
        (f + g) (hRange (f + g)) =
      owner_pregular_residue_eval_of_range (A := A) (K := K) (G := G) (p := p) M f (hRange f) +
        owner_pregular_residue_eval_of_range (A := A) (K := K) (G := G) (p := p) M g (hRange g) := by
  ext c
  let z := owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c
  let w := owner_pregular_eval (A := A) (K := K) (G := G) (p := p) g c
  have hsumVal :
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) (f + g) c = z + w := by
    simp [z, w]
  have hsumRange : z + w ∈ Set.range (algebraMap A K) := by
    simpa [hsumVal] using hRange (f + g) c
  calc
    (owner_pregular_residue_eval_of_range
        (A := A) (K := K) (G := G) (p := p) M (f + g) (hRange (f + g))) c
      = residueFieldOfLiftedValue (A := A) (K := K) (p := p) M (z + w)
          hsumRange := by
            dsimp [owner_pregular_residue_eval_of_range]
            exact
              residueFieldOfLiftedValue_congr
                (A := A) (K := K) (p := p) M
                (hRange (f + g) c) hsumRange hsumVal
    _ = residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z (hRange f c) +
          residueFieldOfLiftedValue (A := A) (K := K) (p := p) M w (hRange g c) := by
            simpa [z, w] using
              (residueFieldOfLiftedValue_add
                (A := A) (K := K) (p := p) M
                (hz := hRange f c) (hw := hRange g c)
                (hsum := hsumRange))
    _ =
        (owner_pregular_residue_eval_of_range
          (A := A) (K := K) (G := G) (p := p) M f (hRange f)) c +
          (owner_pregular_residue_eval_of_range
            (A := A) (K := K) (G := G) (p := p) M g (hRange g)) c := by
              simp [owner_pregular_residue_eval_of_range, z, w]

/-- Helper for Exercise 12-12.7-8: if every owner value on every `p`-regular class already comes
from `A`, then the pointwise residue evaluator is multiplicative. -/
private theorem owner_pregular_residue_eval_of_range_mul
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hRange :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        ∀ c : PRegularConjClass G p,
          owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
            Set.range (algebraMap A K))
    (f g : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    owner_pregular_residue_eval_of_range (A := A) (K := K) (G := G) (p := p) M
        (f * g) (hRange (f * g)) =
      owner_pregular_residue_eval_of_range (A := A) (K := K) (G := G) (p := p) M f (hRange f) *
        owner_pregular_residue_eval_of_range (A := A) (K := K) (G := G) (p := p) M g (hRange g) := by
  ext c
  let z := owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c
  let w := owner_pregular_eval (A := A) (K := K) (G := G) (p := p) g c
  have hprodVal :
      owner_pregular_eval (A := A) (K := K) (G := G) (p := p) (f * g) c = z * w := by
    simp [z, w]
  have hprodRange : z * w ∈ Set.range (algebraMap A K) := by
    simpa [hprodVal] using hRange (f * g) c
  calc
    (owner_pregular_residue_eval_of_range
        (A := A) (K := K) (G := G) (p := p) M (f * g) (hRange (f * g))) c
      = residueFieldOfLiftedValue (A := A) (K := K) (p := p) M (z * w)
          hprodRange := by
            dsimp [owner_pregular_residue_eval_of_range]
            exact
              residueFieldOfLiftedValue_congr
                (A := A) (K := K) (p := p) M
                (hRange (f * g) c) hprodRange hprodVal
    _ = residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z (hRange f c) *
          residueFieldOfLiftedValue (A := A) (K := K) (p := p) M w (hRange g c) := by
            simpa [z, w] using
              (residueFieldOfLiftedValue_mul
                (A := A) (K := K) (p := p) M
                (hz := hRange f c) (hw := hRange g c)
                (hprod := hprodRange))
    _ =
        (owner_pregular_residue_eval_of_range
          (A := A) (K := K) (G := G) (p := p) M f (hRange f)) c *
          (owner_pregular_residue_eval_of_range
            (A := A) (K := K) (G := G) (p := p) M g (hRange g)) c := by
              simp [owner_pregular_residue_eval_of_range, z, w]

/-- Helper for Exercise 12-12.7-8: once the missing global `A`-valuedness theorem for owner
values is supplied, the source-level residue evaluator on `p`-regular conjugacy classes packages
into the desired owner-factor `A`-algebra map. -/
private noncomputable def owner_pregular_residue_eval_algHom_of_range
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hRange :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        ∀ c : PRegularConjClass G p,
          owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
            Set.range (algebraMap A K)) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G →ₐ[A]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField) where
  toFun f :=
    owner_pregular_residue_eval_of_range (A := A) (K := K) (G := G) (p := p) M f (hRange f)
  map_zero' := by
    ext c
    rw [owner_pregular_residue_eval_of_range]
    simpa using
      (residueFieldOfLiftedValue_eq_algebraMap
        (A := A) (K := K) (p := p) M (hRange 0 c) 0
        (by simpa using
          (owner_pregular_eval_zero (A := A) (K := K) (G := G) (p := p) c).symm))
  map_one' := by
    ext c
    rw [owner_pregular_residue_eval_of_range]
    simpa using
      (residueFieldOfLiftedValue_eq_algebraMap
        (A := A) (K := K) (p := p) M (hRange 1 c) 1
        (by simpa using
          (owner_pregular_eval_one (A := A) (K := K) (G := G) (p := p) c).symm))
  map_mul' f g := owner_pregular_residue_eval_of_range_mul
    (A := A) (K := K) (G := G) (p := p) M hRange f g
  map_add' f g := owner_pregular_residue_eval_of_range_add
    (A := A) (K := K) (G := G) (p := p) M hRange f g
  commutes' a := by
    simpa using
      owner_pregular_residue_eval_of_range_algebraMap
        (A := A) (K := K) (G := G) (p := p) M hRange a

/-- Helper for Exercise 12-12.7-8: once the missing global `A`-valuedness theorem for owner
values is supplied, the packaged owner-factor evaluator is already constant on `Γ_K`-orbits of
`PRegularConjClass G p`. -/
private theorem owner_pregular_residue_eval_algHom_of_range_invariant
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hRange :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        ∀ c : PRegularConjClass G p,
          owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
            Set.range (algebraMap A K))
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (t : ΓK) (c : PRegularConjClass G p) :
    (owner_pregular_residue_eval_algHom_of_range
      (A := A) (K := K) (G := G) (p := p) M hRange f) (t • c) =
      (owner_pregular_residue_eval_algHom_of_range
        (A := A) (K := K) (G := G) (p := p) M hRange f) c := by
  exact owner_pregular_residue_eval_of_range_invariant
    (A := A) (K := K) (G := G) (p := p) M f (hRange f) t c

/-- Helper for Exercise 12-12.7-8: once the missing global `A`-valuedness theorem for owner
values is supplied, the packaged owner-factor evaluator has the expected representative-level zero
criterion. -/
private theorem owner_pregular_residue_eval_algHom_of_range_ofSubtype_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hRange :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        ∀ c : PRegularConjClass G p,
          owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c ∈
            Set.range (algebraMap A K))
    (x : {x : G // IsPRegular p x})
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    (owner_pregular_residue_eval_algHom_of_range
      (A := A) (K := K) (G := G) (p := p) M hRange f)
        (PRegularConjClass.ofSubtype p x) = 0 ↔
      ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
  exact owner_pregular_residue_eval_of_range_ofSubtype_zero_iff
    (A := A) (K := K) (G := G) (p := p) M f (hRange f) x

section IntegralClosureResidueEvaluator

variable [IsIntegralClosure A ℤ K]

/-- Helper for Exercise 12-12.7-8: after isolating the fiber transport, the remaining source
route needs an owner-level evaluator on honest `p`-regular representative classes. This is the
missing `A`-algebra map on the owner factor before the fiber tensor product is reassembled by the
universal property. -/
noncomputable def owner_pregular_residue_eval_algHom
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G →ₐ[A]
      (PRegularConjClass G p → M.1.asIdeal.ResidueField) :=
  { toFun := fun f ↦
      owner_pregular_residue_eval_of_isIntegralClosure
        (A := A) (K := K) (G := G) (p := p) M f
    map_zero' := by
      ext c
      rw [owner_pregular_residue_eval_of_isIntegralClosure]
      simpa using
        (residueFieldOfLiftedValue_eq_algebraMap
          (A := A) (K := K) (p := p) M
          (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
            (A := A) (K := K) (G := G) (p := p) (f := 0) c)
          0
          (by
            simpa using
              (owner_pregular_eval_zero (A := A) (K := K) (G := G) (p := p) c).symm))
    map_one' := by
      ext c
      rw [owner_pregular_residue_eval_of_isIntegralClosure]
      simpa using
        (residueFieldOfLiftedValue_eq_algebraMap
          (A := A) (K := K) (p := p) M
          (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
            (A := A) (K := K) (G := G) (p := p) (f := 1) c)
          1
          (by
            simpa using
              (owner_pregular_eval_one (A := A) (K := K) (G := G) (p := p) c).symm))
    map_mul' := by
      intro f g
      ext c
      let z := owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c
      let w := owner_pregular_eval (A := A) (K := K) (G := G) (p := p) g c
      have hprodVal :
          owner_pregular_eval (A := A) (K := K) (G := G) (p := p) (f * g) c = z * w := by
        simp [z, w]
      have hprodRange : z * w ∈ Set.range (algebraMap A K) := by
        simpa [hprodVal] using
          owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
            (A := A) (K := K) (G := G) (p := p) (f := f * g) c
      calc
        (owner_pregular_residue_eval_of_isIntegralClosure
            (A := A) (K := K) (G := G) (p := p) M (f * g)) c
          = residueFieldOfLiftedValue (A := A) (K := K) (p := p) M (z * w)
              hprodRange := by
                dsimp [owner_pregular_residue_eval_of_isIntegralClosure]
                exact
                  residueFieldOfLiftedValue_congr
                    (A := A) (K := K) (p := p) M
                    (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                      (A := A) (K := K) (G := G) (p := p) (f := f * g) c)
                    hprodRange hprodVal
        _ = residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z
              (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                (A := A) (K := K) (G := G) (p := p) (f := f) c) *
            residueFieldOfLiftedValue (A := A) (K := K) (p := p) M w
              (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                (A := A) (K := K) (G := G) (p := p) (f := g) c) := by
                  simpa [z, w] using
                    residueFieldOfLiftedValue_mul
                      (A := A) (K := K) (p := p) M
                      (hz := owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                        (A := A) (K := K) (G := G) (p := p) (f := f) c)
                      (hw := owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                        (A := A) (K := K) (G := G) (p := p) (f := g) c)
                      (hprod := hprodRange)
        _ =
            (owner_pregular_residue_eval_of_isIntegralClosure
              (A := A) (K := K) (G := G) (p := p) M f) c *
              (owner_pregular_residue_eval_of_isIntegralClosure
                (A := A) (K := K) (G := G) (p := p) M g) c := by
                  simp [owner_pregular_residue_eval_of_isIntegralClosure, z, w]
    map_add' := by
      intro f g
      ext c
      let z := owner_pregular_eval (A := A) (K := K) (G := G) (p := p) f c
      let w := owner_pregular_eval (A := A) (K := K) (G := G) (p := p) g c
      have hsumVal :
          owner_pregular_eval (A := A) (K := K) (G := G) (p := p) (f + g) c = z + w := by
        simp [z, w]
      have hsumRange : z + w ∈ Set.range (algebraMap A K) := by
        simpa [hsumVal] using
          owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
            (A := A) (K := K) (G := G) (p := p) (f := f + g) c
      calc
        (owner_pregular_residue_eval_of_isIntegralClosure
            (A := A) (K := K) (G := G) (p := p) M (f + g)) c
          = residueFieldOfLiftedValue (A := A) (K := K) (p := p) M (z + w)
              hsumRange := by
                dsimp [owner_pregular_residue_eval_of_isIntegralClosure]
                exact
                  residueFieldOfLiftedValue_congr
                    (A := A) (K := K) (p := p) M
                    (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                      (A := A) (K := K) (G := G) (p := p) (f := f + g) c)
                    hsumRange hsumVal
        _ = residueFieldOfLiftedValue (A := A) (K := K) (p := p) M z
              (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                (A := A) (K := K) (G := G) (p := p) (f := f) c) +
            residueFieldOfLiftedValue (A := A) (K := K) (p := p) M w
              (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                (A := A) (K := K) (G := G) (p := p) (f := g) c) := by
                  simpa [z, w] using
                    residueFieldOfLiftedValue_add
                      (A := A) (K := K) (p := p) M
                      (hz := owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                        (A := A) (K := K) (G := G) (p := p) (f := f) c)
                      (hw := owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
                        (A := A) (K := K) (G := G) (p := p) (f := g) c)
                      (hsum := hsumRange)
        _ =
            (owner_pregular_residue_eval_of_isIntegralClosure
              (A := A) (K := K) (G := G) (p := p) M f) c +
              (owner_pregular_residue_eval_of_isIntegralClosure
                (A := A) (K := K) (G := G) (p := p) M g) c := by
                  simp [owner_pregular_residue_eval_of_isIntegralClosure, z, w]
    commutes' := by
      intro a
      ext c
      rw [owner_pregular_residue_eval_of_isIntegralClosure]
      simpa using
        (residueFieldOfLiftedValue_eq_algebraMap
          (A := A) (K := K) (p := p) M
          (owner_pregular_eval_mem_range_on_pRegular_classes_of_isIntegralClosure
            (A := A) (K := K) (G := G) (p := p)
            (f := algebraMap A
              (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a) c)
          a
          (by
            simpa using
              (owner_pregular_eval_algebraMap
                (A := A) (K := K) (G := G) (p := p) a c).symm)) }

/-- Helper for Exercise 12-12.7-8: Serre's representative-level evaluator on the owner factor is
constant on `Γ_K`-orbits of `PRegularConjClass G p`. -/
theorem owner_pregular_residue_eval_invariant
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (t : ΓK) (c : PRegularConjClass G p) :
    (owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) M f) (t • c) =
      (owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) M f) c := by
  exact owner_pregular_residue_eval_of_isIntegralClosure_invariant
    (A := A) (K := K) (G := G) (p := p) M f t c

/-- Helper for Exercise 12-12.7-8: on an honest `p`-regular representative, the owner-factor
evaluator vanishes exactly when the corresponding character value is congruent modulo the fixed
maximal ideal `M`. -/
theorem owner_pregular_residue_eval_ofSubtype_zero_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (x : {x : G // IsPRegular p x})
    (f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :
    (owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) M f)
        (PRegularConjClass.ofSubtype p x) = 0 ↔
      ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1 := by
  exact owner_pregular_residue_eval_of_isIntegralClosure_ofSubtype_zero_iff
    (A := A) (K := K) (G := G) (p := p) M x f

/-- Helper for Exercise 12-12.7-8: the constant scalar functions and the owner-factor residue
evaluator commute in the target function ring. -/
theorem owner_pregular_residue_eval_commutes
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    ∀ a : M.1.asIdeal.ResidueField,
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        Commute
          (Pi.constAlgHom (R := M.1.asIdeal.ResidueField)
            (A := PRegularConjClass G p) (B := M.1.asIdeal.ResidueField) a)
          (owner_pregular_residue_eval_algHom (A := A) (K := K) (G := G) M f) := by
  intro a f
  exact Commute.all _ _

end IntegralClosureResidueEvaluator

end RegularPrime

end

end Representation
