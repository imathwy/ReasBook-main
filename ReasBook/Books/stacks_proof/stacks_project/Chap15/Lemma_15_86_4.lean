import Mathlib
import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap10.Lemma_10_134_3
import StacksProject_2024.Chap10.Lemma_10_149_3
import StacksProject_2024.Chap10.Remark_10_69_7_Other_types_of_regular_sequences
import StacksProject_2024.Chap15.Definition_15_33_2
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_69_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_32_3
import StacksProject_2024.Chap15.Lemma_15_33_6
import StacksProject_2024.Chap15.Lemma_15_67_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open ComplexShape
open scoped NaiveCotangent

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [RingHom.IsLocalCompleteIntersection (algebraMap A B)]

local notation "CpxB" => CochainComplex (ModuleCat B) ℤ

/- Domain triage:
- primary domain: local complete intersection ring maps and the derived invariants of the
  canonical naive cotangent complex `NL_{B⁄A}`;
- sampled owner declarations:
  - `RingHom.IsLocalCompleteIntersection`, the chapter owner for the source-facing lci property;
  - `naiveCotangentObject A B`, the Chapter 10 bridge/view object of `NL_{B⁄A}` in `D(B)`;
  - `K.IsPerfect` and `HasTorAmplitudeIn`, the chapter owners for the two target
    derived properties.
- best owner abstraction: the primitive public datum is the lci owner
  `RingHom.IsLocalCompleteIntersection (algebraMap A B)`, while a chosen presentation
  `P : Generators A B (Fin n)` is bridge data supplied by Definition `15.33.2`.
- layer triage:
  - `source-facing`: the lci-facing perfectness and tor-amplitude theorems below;
  - `core/canonical`: `HasTorAmplitudeIn` and `DerivedCategory.IsPerfect` on
    `naiveCotangentObject A B`;
  - `bridge/view`: the chosen finite presentation witness from Definition `15.33.2`, used only
    internally in the proof. -/

/-- Helper for Lemma 15.86.4: every Koszul-regular ideal is quasi-regular. -/
theorem Ideal.IsKoszulRegularIdeal.isQuasiRegular
    {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsKoszulRegularIdeal) :
    I.IsQuasiRegularIdeal := by
  -- Proof comment: first upgrade to the intermediate `H₁`-regular owner, then apply the
  -- sequence-level bridge from `H₁`-regularity to quasi-regularity.
  have hH1 : I.IsH1RegularIdeal :=
    Ideal.IsKoszulRegularIdeal.isH1Regular_of_koszulRegular (I := I) hI
  rw [Ideal.isH1RegularIdeal_iff] at hH1
  rw [Ideal.isQuasiRegularIdeal_iff]
  intro p hp hIp
  rcases hH1 p hp hIp with ⟨g, hg, r, f, hf, hspan⟩
  exact ⟨g, hg, r, f, by
    simpa [RingTheory.Sequence.IsH1RegularSequence] using hf.isQuasiRegular, hspan⟩

/-- Helper for Lemma 15.86.4: a zero `B`-module is finite. -/
theorem module_finite_of_isZero (M : ModuleCat B) (hM : IsZero M) :
    Module.Finite B M := by
  -- Proof comment: identify the zero module with the one-point module and transport finiteness.
  let _ : Subsingleton ↥M := ModuleCat.subsingleton_of_isZero hM
  let e : ModuleCat.of B PUnit ≅ M :=
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of B PUnit)).isoZero ≪≫ hM.isoZero.symm
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.86.4: a zero `B`-module is projective. -/
theorem module_projective_of_isZero (M : ModuleCat B) (hM : IsZero M) :
    Module.Projective B M := by
  -- Proof comment: every zero module is free on the empty basis, hence projective.
  let _ : Subsingleton ↥M := ModuleCat.subsingleton_of_isZero hM
  let _ : Module.Free B ↥M := Module.Free.of_subsingleton (R := B) (N := ↥M)
  exact Module.Projective.of_free

/-- Helper for Lemma 15.86.4: all higher terms of a presentation naive cotangent chain complex
vanish. -/
theorem naiveCotangentChainComplex_X_succ_succ_isZero
    (E : Algebra.Extension A B) (n : ℕ) :
    IsZero (E.naiveCotangentChainComplex.X (n + 2)) := by
  -- Proof comment: `naiveCotangentChainComplex` is literally built as a two-term chain complex.
  let succZero :
      ∀ {X₀ X₁ : ModuleCat B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, by simp⟩
  let C := E.naiveCotangentChainComplex
  have hs : (succZero (C.d (n + 1) n)).1 = ModuleCat.of B PUnit := rfl
  have hX : C.X (n + 2) ≅ (succZero (C.d (n + 1) n)).1 := by
    simpa [C, Algebra.Extension.naiveCotangentChainComplex] using
      (ChainComplex.mk'XIso
        (ModuleCat.of B E.CotangentSpace)
        (ModuleCat.of B (ULift E.Cotangent))
        (ModuleCat.ofHom (E.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
        succZero n)
  exact
    IsZero.of_iso
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of B PUnit))
      (hX ≪≫ eqToIso hs)

/-- Helper for Lemma 15.86.4: the chosen cochain representative is supported in degrees
`≥ -1`. -/
theorem presentation_naiveCotangent_isStrictlyGE
    {n : ℕ} (P : Algebra.Generators A B (Fin n)) :
    CochainComplex.IsStrictlyGE
      ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)
      (-1) := by
  -- Proof comment: extending from chain degree `j` to cochain degree `-j` leaves only degrees
  -- `0` and `-1`.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hnonneg : 0 ≤ -i - 2 := by omega
  have hexists : ∃ n : ℕ, i = -((n + 2 : ℕ) : ℤ) := by
    refine ⟨Int.toNat (-i - 2), ?_⟩
    have htoNat : ((Int.toNat (-i - 2) : ℕ) : ℤ) = -i - 2 :=
      Int.toNat_of_nonneg hnonneg
    omega
  rcases hexists with ⟨n, rfl⟩
  exact
    (naiveCotangentChainComplex_X_succ_succ_isZero (A := A) (B := B) P.toExtension n).of_iso
      (P.toExtension.naiveCotangentChainComplex.extendXIso
        embeddingDownNat
        (show embeddingDownNat.f (n + 2) = -((n + 2 : ℕ) : ℤ) by rfl))

/-- Helper for Lemma 15.86.4: the chosen cochain representative is supported in degrees
`≤ 0`. -/
theorem presentation_naiveCotangent_isStrictlyLE_zero
    {n : ℕ} (P : Algebra.Generators A B (Fin n)) :
    CochainComplex.IsStrictlyLE
      ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat)
      0 := by
  -- Proof comment: positive cochain degrees do not occur in the extension of a chain complex on
  -- `ℕ`.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact
    P.toExtension.naiveCotangentChainComplex.isZero_extend_X embeddingDownNat i fun j hij ↦ by
      have hnonpos : (embeddingDownNat.f j : ℤ) ≤ 0 := by
        simp [ComplexShape.embeddingDownNat]
      omega

/-- Helper for Lemma 15.86.4: degree `-1` of the chosen representative is the lifted conormal
module. -/
noncomputable def presentation_naiveCotangent_degree_negOne_equiv
    {n : ℕ} (P : Algebra.Generators A B (Fin n)) :
    ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X (-1))) ≃ₗ[B]
      ULift P.toExtension.Cotangent := by
  -- Proof comment: chain degree `1` becomes cochain degree `-1`.
  simpa [Algebra.Extension.naiveCotangentChainComplex] using
    (((P.toExtension.naiveCotangentChainComplex).extendXIso embeddingDownNat
      (show embeddingDownNat.f 1 = (-1 : ℤ) by rfl)).toLinearEquiv)

/-- Helper for Lemma 15.86.4: degree `0` of the chosen representative is the cotangent-space
module. -/
noncomputable def presentation_naiveCotangent_degree_zero_equiv
    {n : ℕ} (P : Algebra.Generators A B (Fin n)) :
    ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X 0)) ≃ₗ[B]
      P.toExtension.CotangentSpace := by
  -- Proof comment: chain degree `0` stays in cochain degree `0`.
  simpa [Algebra.Extension.naiveCotangentChainComplex] using
    (((P.toExtension.naiveCotangentChainComplex).extendXIso embeddingDownNat
      (show embeddingDownNat.f 0 = (0 : ℤ) by rfl)).toLinearEquiv)

/-- Helper for Lemma 15.86.4: the presentation cotangent owner is the quotient-owner conormal
module after transporting scalars along the canonical quotient-kernel algebra equivalence. -/
theorem presentation_cotangent_finite_projective_of_quasi_regular_kernel
    {n : ℕ} (P : Algebra.Generators A B (Fin n))
    (hker : P.ker.IsQuasiRegularIdeal) :
    Module.FiniteProjective B P.toExtension.Cotangent := by
  -- Proof comment: for a presentation, the degree `-1` owner is exactly the conormal module
  -- `P.ker / P.ker²`, so the quasi-regular ideal theorem is already the needed source theorem.
  -- Route correction: the remaining blocker is the exact quotient-owner to presentation-owner
  -- transport from `P.ker.Cotangent` over `P.Ring ⧸ P.ker` to `P.toExtension.Cotangent` over `B`.
  -- TODO: package the canonical quotient-kernel algebra equivalence together with the owner-level
  -- cotangent identification into a `B`-linear equivalence, then transport
  -- `Ideal.cotangent_finite_projective_of_isQuasiRegularIdeal hker` across it.
  let _ := hker
  sorry

/-- Helper for Lemma 15.86.4: degree `-1` of the chosen representative is finite projective. -/
theorem presentation_naiveCotangent_degree_negOne_finite_projective
    {n : ℕ} (P : Algebra.Generators A B (Fin n))
    (hker : P.ker.IsQuasiRegularIdeal) :
    Module.Finite B ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X (-1))) ∧
      Module.Projective B ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X (-1))) := by
  -- Proof comment: identify degree `-1` with `ULift P.toExtension.Cotangent`, then transport the
  -- finite-projective structure from the conormal term.
  have hcot :
      Module.FiniteProjective B P.toExtension.Cotangent :=
    presentation_cotangent_finite_projective_of_quasi_regular_kernel (A := A) (B := B) P hker
  let _ : Module.Finite B P.toExtension.Cotangent := hcot.1
  let _ : Module.Projective B P.toExtension.Cotangent := hcot.2
  let _ : Module.Finite B (ULift P.toExtension.Cotangent) :=
    Module.Finite.equiv ULift.moduleEquiv.symm
  let _ : Module.Projective B (ULift P.toExtension.Cotangent) :=
    Module.Projective.of_equiv ULift.moduleEquiv.symm
  let e := presentation_naiveCotangent_degree_negOne_equiv (A := A) (B := B) P
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- Helper for Lemma 15.86.4: degree `0` of the chosen representative is finite projective. -/
theorem presentation_naiveCotangent_degree_zero_finite_projective
    {n : ℕ} (P : Algebra.Generators A B (Fin n)) :
    Module.Finite B ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X 0)) ∧
      Module.Projective B ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X 0)) := by
  -- Proof comment: the presentation cotangent-space basis makes degree `0` free.
  let _ : Module.Free B P.toExtension.CotangentSpace :=
    Module.Free.of_basis P.cotangentSpaceBasis
  let _ : Module.Finite B P.toExtension.CotangentSpace :=
    Module.Finite.of_basis P.cotangentSpaceBasis
  let _ : Module.Projective B P.toExtension.CotangentSpace :=
    Module.Projective.of_free
  let e := presentation_naiveCotangent_degree_zero_equiv (A := A) (B := B) P
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- Helper for Lemma 15.86.4: degree `0` of the chosen representative is flat. -/
theorem presentation_naiveCotangent_degree_zero_flat
    {n : ℕ} (P : Algebra.Generators A B (Fin n)) :
    Module.Flat B ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X 0)) := by
  -- Proof comment: the degree-zero term is linearly equivalent to the free cotangent-space term.
  let _ : Module.Free B P.toExtension.CotangentSpace :=
    Module.Free.of_basis P.cotangentSpaceBasis
  let _ : Module.Flat B P.toExtension.CotangentSpace :=
    Module.Flat.of_free (R := B) (M := P.toExtension.CotangentSpace)
  exact Module.Flat.of_linearEquiv
    (presentation_naiveCotangent_degree_zero_equiv (A := A) (B := B) P)

/-- Helper for Lemma 15.86.4: the chosen presentation model is a bounded finite-projective
cochain complex. -/
theorem presentation_naiveCotangent_isBoundedFiniteProjective_of_quasi_regular_kernel
    {n : ℕ} (P : Algebra.Generators A B (Fin n))
    (hker : P.ker.IsQuasiRegularIdeal) :
    CochainComplex.IsBoundedFiniteProjective
      ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB) := by
  -- Proof comment: the only nonzero degrees are `-1` and `0`, and these are handled by the
  -- conormal theorem and the cotangent-space basis.
  refine ⟨⟨-1, 0, ?_, ?_⟩, ?_, ?_⟩
  · exact presentation_naiveCotangent_isStrictlyGE (A := A) (B := B) P
  · exact presentation_naiveCotangent_isStrictlyLE_zero (A := A) (B := B) P
  · intro i
    by_cases hzero : i = 0
    · subst hzero
      exact (presentation_naiveCotangent_degree_zero_finite_projective (A := A) (B := B) P).1
    by_cases hnegOne : i = -1
    · subst hnegOne
      exact
        (presentation_naiveCotangent_degree_negOne_finite_projective
          (A := A) (B := B) P hker).1
    have hi : i < -1 ∨ 0 < i := by omega
    have hXi : IsZero ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X i)) := by
      let C : CpxB := ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB)
      have hGE : C.IsStrictlyGE (-1) := by
        simpa [C] using presentation_naiveCotangent_isStrictlyGE (A := A) (B := B) P
      have hLE : C.IsStrictlyLE 0 := by
        simpa [C] using presentation_naiveCotangent_isStrictlyLE_zero (A := A) (B := B) P
      rcases hi with hi | hi
      · simpa [C] using C.isZero_of_isStrictlyGE (-1) i hi
      · simpa [C] using C.isZero_of_isStrictlyLE 0 i hi
    exact module_finite_of_isZero (B := B) _ hXi
  · intro i
    by_cases hzero : i = 0
    · subst hzero
      exact (presentation_naiveCotangent_degree_zero_finite_projective (A := A) (B := B) P).2
    by_cases hnegOne : i = -1
    · subst hnegOne
      exact
        (presentation_naiveCotangent_degree_negOne_finite_projective
          (A := A) (B := B) P hker).2
    have hi : i < -1 ∨ 0 < i := by omega
    have hXi : IsZero ((((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB).X i)) := by
      let C : CpxB := ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB)
      have hGE : C.IsStrictlyGE (-1) := by
        simpa [C] using presentation_naiveCotangent_isStrictlyGE (A := A) (B := B) P
      have hLE : C.IsStrictlyLE 0 := by
        simpa [C] using presentation_naiveCotangent_isStrictlyLE_zero (A := A) (B := B) P
      rcases hi with hi | hi
      · simpa [C] using C.isZero_of_isStrictlyGE (-1) i hi
      · simpa [C] using C.isZero_of_isStrictlyLE 0 i hi
    exact module_projective_of_isZero (B := B) _ hXi

/-- Helper for Lemma 15.86.4: the canonical self-presentation object is isomorphic to the chosen
finite presentation model in the derived category. -/
noncomputable def presentation_naiveCotangentObject_iso
    {n : ℕ} (P : Algebra.Generators A B (Fin n)) :
    naiveCotangentObject A B ≅
      DerivedCategory.Q.obj
        (((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB)) := by
  -- Route correction: the public Chapter 10 comparison still hits the `self`-presentation versus
  -- `Fin n` universe/index mismatch here.
  -- TODO: rebuild the default-hom chain homotopy equivalence locally in the `Fin n` setting and
  -- descend it through `DerivedCategory.quotientCompQhIso`.
  let _ := P
  sorry

/-- Helper for Lemma 15.86.4: the chosen presentation model already has projective amplitude in
`[-1, 0]`. -/
theorem presentation_naiveCotangent_hasProjectiveAmplitude_of_quasi_regular_kernel
    {n : ℕ} (P : Algebra.Generators A B (Fin n))
    (hker : P.ker.IsQuasiRegularIdeal) :
    HasProjectiveAmplitudeIn
      (DerivedCategory.Q.obj
        (((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB)))
      (-1) 0 := by
  -- Proof comment: the same two-term bounded finite-projective representative from the source
  -- proof gives projective amplitude without any additional algebra.
  let L : CpxB :=
    ((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB)
  have hLbounded :
      CochainComplex.IsBoundedFiniteProjective L := by
    -- Proof comment: package the bounded finite-projective structure once and reuse it below.
    simpa [L] using
      presentation_naiveCotangent_isBoundedFiniteProjective_of_quasi_regular_kernel
        (A := A) (B := B) P hker
  refine ⟨L, Iso.refl _, ?_, ?_, ?_⟩
  · -- Proof comment: the representative has no cohomology below degree `-1`.
    simpa [L] using presentation_naiveCotangent_isStrictlyGE (A := A) (B := B) P
  · -- Proof comment: the representative has no cohomology above degree `0`.
    simpa [L] using presentation_naiveCotangent_isStrictlyLE_zero (A := A) (B := B) P
  · intro i
    -- Proof comment: bounded finite-projective terms supply the projectivity of every degree.
    let _ : CochainComplex.IsBoundedFiniteProjective L := hLbounded
    let _ : Module.Projective B (L.X i) := hLbounded.projective i
    infer_instance

/-- Helper for Lemma 15.86.4: the explicit two-term presentation model has tor-amplitude in
`[-1, 0]`. -/
theorem presentation_naiveCotangent_hasTorAmplitude_of_quasi_regular_kernel
    {n : ℕ} (P : Algebra.Generators A B (Fin n))
    (hker : P.ker.IsQuasiRegularIdeal) :
    HasTorAmplitudeIn
      (DerivedCategory.Q.obj
        (((P.toExtension.naiveCotangentChainComplex).extend embeddingDownNat : CpxB)))
      (-1) 0 := by
  -- TODO: deduce tor-amplitude from the same explicit two-term representative by combining the
  -- boundedness of `presentation_naiveCotangent_isBoundedFiniteProjective_of_quasi_regular_kernel`
  -- with the termwise flatness of projective modules and
  -- `hasTorAmplitudeIn_of_bounded_of_termwise_hasTorAmplitudeIn`.
  let _ := hker
  sorry

/-- Lemma 15.86.4: if `A → B` is a local complete intersection ring map, then the naive
cotangent complex `NL_{B/A}` is perfect and has tor-amplitude in `[-1, 0]`. -/
@[stacks 0FV0]
theorem naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection
    :
    (naiveCotangentObject A B).IsPerfect ∧
      HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0 := by
  -- TODO: follow the source proof by choosing a finite `Fin n` presentation with Koszul-regular
  -- kernel, proving the degree `-1` conormal term finite projective over `B`, and then
  -- transporting the resulting bounded two-term model back to `naiveCotangentObject A B` via the
  -- missing `Fin n` default-hom comparison in `presentation_naiveCotangentObject_iso`.
  sorry

/-- For a local complete intersection ring map, the naive cotangent complex `NL_{B/A}` is
perfect in `D(B)`. -/
theorem naiveCotangent_isPerfect_of_isLocalCompleteIntersection
    :
    (naiveCotangentObject A B).IsPerfect :=
  naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection.1

/-- For a local complete intersection ring map, the naive cotangent complex `NL_{B/A}` has
tor-amplitude in `[-1, 0]`. -/
theorem naiveCotangent_hasTorAmplitude_of_isLocalCompleteIntersection
    :
    HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0 :=
  naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection.2

end
