import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeFiberEvaluation
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_6

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

/-- Helper for Exercise 12-12.7-8: the ambient finite group `G` may be treated as a `Fintype`
inside the separator layer. -/
private local instance : Fintype G := Fintype.ofFinite G

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]
variable [IsIntegralClosure A ℤ K]

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: the underlying natural number of `p : Nat.Primes` is prime. -/
private local instance : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩

/-- Helper for Exercise 12-12.7-8: the `p`-regular `Γ_K`-classes form a finite type. -/
private local instance : Fintype (PRegularGaloisPowerClass ΓK p) := Fintype.ofFinite _

/-- Helper for Exercise 12-12.7-8: equality on `p`-regular `Γ_K`-classes is decidable. -/
private local instance : DecidableEq (PRegularGaloisPowerClass ΓK p) := Classical.decEq _

/-- Helper for Exercise 12-12.7-8: Serre's separator-character construction can be specialized to
the fixed maximal ideal `M`. It produces an owner element whose realized function is supported on
the chosen `p`-regular `Γ_K`-class and whose distinguished value survives modulo `M`. -/
private theorem exists_owner_separator_for_fixed_maximal
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (x : {x : G // IsPRegular p x}) :
    ∃ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
      ∃ φ : G → A,
        ((algebraMap A K) ∘ φ) = (f : G → K) ∧
          φ x.1 ∉ M.1.asIdeal ∧
          ∀ s (hs : IsPRegular p s),
            pRegularGaloisPowerClassMk ΓK p ⟨s, hs⟩ ≠ pRegularGaloisPowerClassMk ΓK p x →
              (f : G → K) s = 0 := by
  classical
  -- `A` is integrally closed: it is the integral closure of `ℤ` in its fraction field `K`.
  haveI : IsIntegrallyClosed A :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (K := K)).mpr
      (IsIntegrallyClosedIn.of_isIntegralClosure ℤ)
  let P : Sylow p N[ΓK](x.1) :=
    Classical.choice (inferInstance : Nonempty (Sylow p N[ΓK](x.1)))
  let H := associatedGammaPElementarySubgroup ΓK x.1 P
  obtain ⟨ψ, χ, φ, hχ, hφ, hnonzero, hvanish⟩ :=
    exists_associatedGammaPElementary_character_nonzero_mod_primeIdeals_vanishing_off_galoisClass
      (K := K) (A := A) (p := p) x.1 x.2 P
  refine ⟨H.characterRingOverFieldAlgebraScalarExtensionInduction ψ, φ, ?_, ?_, ?_⟩
  · -- Repackage the chosen `A`-valued lift with the induced owner element.
    refine hφ.trans ?_
    ext s
    simpa [H] using congrFun hχ s
  · let Q : PrimeSpectrum A := ⟨M.1.asIdeal, inferInstance⟩
    have hp_zero : ((p : ℕ) : M.1.asIdeal.ResidueField) = 0 := by
      exact M.2.2.cast_eq_zero
    have hp_mem : (p : A) ∈ M.1.asIdeal := by
      exact (Ideal.algebraMap_residueField_eq_zero (I := M.1.asIdeal) (x := (p : A))).mp <| by
        simpa using hp_zero
    have hp_span : Ideal.span ({(p : A)} : Set A) ≤ Q.asIdeal := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact hp_mem
    simpa [Q] using hnonzero Q hp_span
  · intro s hs hs_ne
    -- Away from the chosen `Γ_K`-class, the separator character already vanishes on
    -- `p`-regular representatives.
    rw [← congrFun hχ s]
    simpa [H] using hvanish s hs hs_ne

/-- Helper for Exercise 12-12.7-8: Serre's separator owner from Lemma `12-12.7-6` already gives
an element of the fixed fiber whose canonical evaluator is nonzero on the chosen `p`-regular
`Γ_K`-class and vanishes on every different representative class. -/
private theorem exists_regular_fiber_separator_on_representatives
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (x : {x : G // IsPRegular p x}) :
    ∃ ξ : M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G),
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
          (pRegularGaloisPowerClassMk ΓK p x) ≠ 0 ∧
        ∀ y : {y : G // IsPRegular p y},
          pRegularGaloisPowerClassMk ΓK p y ≠ pRegularGaloisPowerClassMk ΓK p x →
            (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ)
              (pRegularGaloisPowerClassMk ΓK p y) = 0 := by
  obtain ⟨f, φ, hφ, hnonzero, hvanish⟩ :=
    exists_owner_separator_for_fixed_maximal
      (A := A) (K := K) (G := G) M x
  refine ⟨(Algebra.TensorProduct.includeRight
      (R := A) (A := M.1.asIdeal.ResidueField)
      (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) f, ?_, ?_⟩
  · intro hzero
    -- If the separator vanished on its distinguished class, the quotient-level zero criterion
    -- would force the distinguished `A`-value into `M`, contradicting the source witness.
    have hx_mem :=
      (regular_fiber_eval_family_includeRight_zero_iff
        (A := A) (K := K) (G := G) (p := p) M
        (pRegularGaloisPowerClassMk ΓK p x) f).mp hzero x rfl
    rcases hx_mem with ⟨a, ha⟩
    have hphi_x : algebraMap A K (φ x.1) = (f : G → K) x.1 := by
      simpa [Function.comp] using congrFun hφ x.1
    have hax : a.1 = φ x.1 :=
      (IsFractionRing.injective A K) <| by
        calc
          algebraMap A K a.1 = (f : G → K) x.1 := ha
          _ = algebraMap A K (φ x.1) := hphi_x.symm
    have hx_in : φ x.1 ∈ M.1.asIdeal := by
      simpa [hax] using a.2
    exact hnonzero hx_in
  · intro y hy
    -- Away from the distinguished class, the owner separator already vanishes on every
    -- representative, so the quotient-level zero criterion closes immediately.
    refine
      (regular_fiber_eval_family_includeRight_zero_iff
        (A := A) (K := K) (G := G) (p := p) M
        (pRegularGaloisPowerClassMk ΓK p y) f).mpr ?_
    intro z hz
    have hzx :
        pRegularGaloisPowerClassMk ΓK p z ≠ pRegularGaloisPowerClassMk ΓK p x := by
      intro hzx_eq
      exact hy (hz.symm.trans hzx_eq)
    have hfz : (f : G → K) z.1 = 0 := hvanish z.1 z.2 hzx
    refine ⟨0, ?_⟩
    simp [hfz]

/-- Helper for Exercise 12-12.7-8: every `p`-regular `Γ_K`-class admits a fixed-fiber separator
whose canonical evaluator is nonzero exactly at that class and zero on all distinct classes. -/
private theorem exists_regular_fiber_separator_for_class
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    ∃ ξ : M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G),
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c ≠ 0 ∧
        ∀ d : PRegularGaloisPowerClass ΓK p, d ≠ c →
          (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) d = 0 := by
  obtain ⟨x, rfl⟩ := pRegularGaloisPowerClassMk_surjective (G := G) ΓK p c
  obtain ⟨ξ, hξ_ne, hξ_zero⟩ :=
    exists_regular_fiber_separator_on_representatives
      (A := A) (K := K) (G := G) M x
  refine ⟨ξ, hξ_ne, ?_⟩
  intro d hd
  obtain ⟨y, rfl⟩ := pRegularGaloisPowerClassMk_surjective (G := G) ΓK p d
  exact hξ_zero y hd

/-- Helper for Exercise 12-12.7-8: normalize Serre's separator at the chosen `p`-regular
`Γ_K`-class so that the canonical fixed-fiber evaluator becomes the corresponding delta
function. -/
private noncomputable def normalized_regular_fiber_separator
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :=
  let ξ :=
    Classical.choose
      (exists_regular_fiber_separator_for_class
        (A := A) (K := K) (G := G) (p := p) M c)
  let v := (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c
  algebraMap M.1.asIdeal.ResidueField
      (M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) v⁻¹ * ξ

/-- Helper for Exercise 12-12.7-8: the normalized separator attached to `c` evaluates to `1` at
`c` and to `0` on every distinct `p`-regular `Γ_K`-class. -/
private theorem normalized_regular_fiber_separator_apply
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c d : PRegularGaloisPowerClass ΓK p) :
    (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
        (normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c)) d =
      if c = d then 1 else 0 := by
  classical
  let ξ :=
    Classical.choose
      (exists_regular_fiber_separator_for_class
        (A := A) (K := K) (G := G) (p := p) M c)
  let hξ :=
    Classical.choose_spec
      (exists_regular_fiber_separator_for_class
        (A := A) (K := K) (G := G) (p := p) M c)
  rcases hξ with ⟨hξ_ne, hξ_zero⟩
  by_cases hcd : c = d
  · subst hcd
    -- Normalize by the inverse of the distinguished nonzero value at `c`.
    let ec :
        (M.1.asIdeal.Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) →+*
          M.1.asIdeal.ResidueField :=
      (Pi.evalRingHom
        (fun _ : PRegularGaloisPowerClass ΓK p ↦ M.1.asIdeal.ResidueField) c).comp
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
    have hcomm :
        ec
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
              (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹)) =
          ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹ := by
      simpa [ec] using
        congrArg
          (fun g : PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField ↦ g c)
          ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).commutes
            (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹))
    calc
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
          (normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c)) c =
          ec (normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c) := by
        rfl
      _ = ec
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
              (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹) * ξ) := by
        rfl
      _ = ec
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
              (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹)) *
            ec ξ := by
        simpa [ec] using
          ec.map_mul
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
              (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹))
            ξ
      _ = ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹ *
            (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c := by
        rw [hcomm]
        rfl
      _ = 1 := inv_mul_cancel₀ hξ_ne
      _ = if c = c then 1 else 0 := by simp
  · have hzero :
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) d = 0 :=
      hξ_zero d (by simpa [eq_comm] using hcd)
    -- Away from `c`, the original separator already vanishes, so the normalized one does too.
    let ed :
        (M.1.asIdeal.Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) →+*
          M.1.asIdeal.ResidueField :=
      (Pi.evalRingHom
        (fun _ : PRegularGaloisPowerClass ΓK p ↦ M.1.asIdeal.ResidueField) d).comp
        (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
    have hcomm :
        ed
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
              (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹)) =
          ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹ := by
      simpa [ed] using
        congrArg
          (fun g : PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField ↦ g d)
          ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).commutes
            (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹))
    calc
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M
          (normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c)) d =
          ed (normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c) := by
        rfl
      _ = ed
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
              (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹) * ξ) := by
        rfl
      _ = ed
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
              (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹)) *
            ed ξ := by
        simpa [ed] using
          ed.map_mul
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
              (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹))
            ξ
      _ = ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹ *
            (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) d := by
        rw [hcomm]
        rfl
      _ = (((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) c)⁻¹) * 0 := by
        rw [hzero]
      _ = 0 := by simp
      _ = if c = d then 1 else 0 := by rw [if_neg hcd]

/-- Helper for Exercise 12-12.7-8: Serre's separator characters make the canonical evaluator on
the fixed fiber over `M` surjective. -/
theorem regular_fiber_eval_family_surjective_from_separators
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Surjective (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M) := by
  classical
  intro ψ
  let ξ :
      M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) :=
    ∑ c, algebraMap M.1.asIdeal.ResidueField
        (M.1.asIdeal.Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) (ψ c) *
      normalized_regular_fiber_separator (A := A) (K := K) (G := G) (p := p) M c
  refine ⟨ξ, ?_⟩
  ext d
  let ed :
      (M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) →+*
        M.1.asIdeal.ResidueField :=
    (Pi.evalRingHom
      (fun _ : PRegularGaloisPowerClass ΓK p ↦ M.1.asIdeal.ResidueField) d).comp
      (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).toRingHom
  calc
    (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M ξ) d =
        ed ξ := by
        rfl
    _ =
        ∑ c : PRegularGaloisPowerClass ΓK p,
          ed
            (algebraMap M.1.asIdeal.ResidueField
              (M.1.asIdeal.Fiber
                (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) (ψ c) *
              normalized_regular_fiber_separator
                (A := A) (K := K) (G := G) (p := p) M c) := by
        simpa [ed, ξ] using
          map_sum ed
            (fun c : PRegularGaloisPowerClass ΓK p ↦
              algebraMap M.1.asIdeal.ResidueField
                (M.1.asIdeal.Fiber
                  (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) (ψ c) *
                normalized_regular_fiber_separator
                  (A := A) (K := K) (G := G) (p := p) M c)
            Finset.univ
    _ =
        ∑ c : PRegularGaloisPowerClass ΓK p,
          ψ c * (if c = d then 1 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        have hcomm :
            ed
                (algebraMap M.1.asIdeal.ResidueField
                  (M.1.asIdeal.Fiber
                    (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) (ψ c)) =
              ψ c := by
          simpa [ed] using
            congrArg
              (fun g : PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField ↦ g d)
              ((regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M).commutes
                (ψ c))
        have hsep :
            ed
                (normalized_regular_fiber_separator
                  (A := A) (K := K) (G := G) (p := p) M c) =
              if c = d then 1 else 0 := by
          simpa [ed] using
            normalized_regular_fiber_separator_apply
              (A := A) (K := K) (G := G) (p := p) M c d
        calc
          ed
              (algebraMap M.1.asIdeal.ResidueField
                (M.1.asIdeal.Fiber
                  (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) (ψ c) *
                normalized_regular_fiber_separator
                  (A := A) (K := K) (G := G) (p := p) M c) =
              ed
                (algebraMap M.1.asIdeal.ResidueField
                  (M.1.asIdeal.Fiber
                    (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) (ψ c)) *
                ed
                  (normalized_regular_fiber_separator
                    (A := A) (K := K) (G := G) (p := p) M c) := by
            simpa [ed] using
              ed.map_mul
                (algebraMap M.1.asIdeal.ResidueField
                  (M.1.asIdeal.Fiber
                    (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) (ψ c))
                (normalized_regular_fiber_separator
                  (A := A) (K := K) (G := G) (p := p) M c)
          _ = ψ c * (if c = d then 1 else 0) := by
            by_cases hcd : c = d
            · subst hcd
              rw [hcomm, hsep]
            · rw [hcomm, hsep, if_neg hcd]
    _ = ψ d := by
          rw [Finset.sum_eq_single d]
          · simp
          · intro c hc hcd
            rw [if_neg hcd]
            simp
          · intro hd
            exact (hd (Finset.mem_univ d)).elim

end RegularPrime

end

end Representation
