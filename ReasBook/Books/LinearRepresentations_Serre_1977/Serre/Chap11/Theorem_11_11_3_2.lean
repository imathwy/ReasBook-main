import Mathlib
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_1
import LinearRepresentations_Serre_1977.Chap09.Theorem_9_9_2_1
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_4
import LinearRepresentations_Serre_1977.Chap11.Lemma_11_11_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open Representation
open scoped Pointwise Representation SubgroupInduction

noncomputable section

universe v

section

variable {G : Type} [Group G] [Finite G]
variable {I : Type v}

/- Source/core/bridge triage:
* `source-facing`: Serre's detection theorem for an arbitrary family of subgroups `(H i)`.
* `core/canonical`: `Subgroup.characterRingInduction`, and for finite families the owner
  `Representation.artinInducedCharacterSubmodule`.
* `bridge/view`: none new here; the theorem is already most natural as a statement about the
  supremum of the canonical induction ranges inside `R(G)`.

Primitive data versus derived API:
the primitive input is the family `H` together with the equality
`⨆ i, (H i).characterRingInduction.range = ⊤`. The conjugacy-containment conclusion for
`p`-elementary subgroups is derived from that owner-level hypothesis, so no extra local wrapper is
introduced around the induction submodules. -/

-- Proof sketch: if a `p`-elementary subgroup `E` were not contained in any conjugate of the
-- family `(H i)`, choose a `p'`-element `x` whose associated subgroup contains `E`. Apply Lemma
-- `11-11.3-1` to each `H i` to show that every induced summand is divisible by `p` at `x` in the
-- algebraic-integer sense. Hence every element of the supremum of the canonical submodules
-- `(H i).characterRingInduction.range ≤ R(G)` has the same divisibility property. The hypothesis
-- `⨆ i, (H i).characterRingInduction.range = ⊤` then forces the unit character of `G` to be
-- divisible by `p` at `x`, which is impossible.
omit [Finite G] in
/-- Helper for Theorem 11-11.3-2: if a `p`-elementary decomposition of `E` has cyclic factor
`⟨x⟩`, then `E` lies in the associated subgroup attached to `x`. -/
lemma exists_le_associatedPElementarySubgroup_of_decomposition
    {p : ℕ} {E : Subgroup G} {x : E} {P : Subgroup E}
    (hE : IsPElementaryDecomposition p (Subgroup.zpowers x) P) :
    ∃ Q : Sylow p (Subgroup.centralizer ({((x : G))} : Set G)),
      E ≤ associatedPElementarySubgroup p (x : G) Q := by
  letI : Fact p.Prime := ⟨hE.prime⟩
  let CGx : Subgroup G := Subgroup.centralizer ({((x : G))} : Set G)
  let P' : Subgroup G := P.map E.subtype
  have hxC : x ∈ Subgroup.zpowers x :=
    Subgroup.mem_zpowers x
  have hP'_le_centralizer : P' ≤ CGx := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hE.commute ⟨x, hxC⟩ ⟨y, hy⟩).map E.subtype).symm.eq
  have hP' : IsPGroup p P' :=
    hE.isPGroup.of_surjective (E.subtype.subgroupMap P) (E.subtype.subgroupMap_surjective P)
  have hP'_centralizer : IsPGroup p (P'.subgroupOf CGx) :=
    hP'.of_equiv (Subgroup.subgroupOfEquivOfLe hP'_le_centralizer).symm
  obtain ⟨Q, hPQ⟩ := hP'_centralizer.exists_le_sylow
  have hP'_le_Qmap : P' ≤ Subgroup.map CGx.subtype (Q : Subgroup CGx) := by
    calc
      P' = Subgroup.map CGx.subtype (P'.subgroupOf CGx) := by
        symm
        exact Subgroup.map_subgroupOf_eq_of_le hP'_le_centralizer
      _ ≤ Subgroup.map CGx.subtype (Q : Subgroup CGx) := Subgroup.map_mono hPQ
  have hE_eq :
      E = Subgroup.zpowers (x : G) ⊔ P' := by
    calc
      E = (⊤ : Subgroup E).map E.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (Subgroup.zpowers x ⊔ P).map E.subtype := by rw [← hE.isComplement.sup_eq_top]
      _ = Subgroup.zpowers (E.subtype x) ⊔ P' := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      _ = Subgroup.zpowers (x : G) ⊔ P.map E.subtype := by rfl
  refine ⟨Q, ?_⟩
  calc
    E = Subgroup.zpowers (x : G) ⊔ P' := hE_eq
    _ ≤ Subgroup.zpowers (x : G) ⊔ Subgroup.map CGx.subtype (Q : Subgroup CGx) :=
      sup_le_sup le_rfl hP'_le_Qmap
    _ = associatedPElementarySubgroup p (x : G) Q := by
      simp [associatedPElementarySubgroup, CGx]
omit [Finite G] in
/-- Helper for Theorem 11-11.3-2: every `p`-elementary subgroup is contained in an associated
`p`-elementary subgroup attached to a `p'`-element generating its cyclic factor. -/
lemma exists_associatedPElementary_overgroup_of_isPElementary
    (p : ℕ) (E : Subgroup G) (hE : IsPElementary p E) :
    ∃ x : E, ∃ Q : Sylow p (Subgroup.centralizer ({((x : G))} : Set G)),
      IsPRegular p (x : G) ∧ E ≤ associatedPElementarySubgroup p (x : G) Q := by
  rcases hE with ⟨C, P, hEP⟩
  obtain ⟨x, hxC⟩ := C.isCyclic_iff_exists_zpowers_eq_top.mp hEP.cyclic
  have hx_regular : IsPRegular p x := by
    have hx_mem : x ∈ C := by
      rw [← hxC]
      exact Subgroup.mem_zpowers x
    have hx_mem' : x ∈ ((↑C : Set E)) := hx_mem
    have hx_mem_regular : x ∈ ({y : E | IsPRegular p y} : Set E) := by
      rw [hEP.cyclic_factor_eq_setOf_isPRegular] at hx_mem'
      exact hx_mem'
    exact hx_mem_regular
  have hEP' : IsPElementaryDecomposition p (Subgroup.zpowers x) P := by
    simpa [hxC] using hEP
  obtain ⟨Q, hEQ⟩ :=
    exists_le_associatedPElementarySubgroup_of_decomposition
      (E := E) (x := x) (P := P) hEP'
  refine ⟨x, Q, ?_, hEQ⟩
  simpa [IsPRegular, Subgroup.orderOf_mk] using hx_regular

/-- Helper for Theorem 11-11.3-2: every value of an element of the integral character ring is an
algebraic integer. -/
lemma characterRing_value_isIntegral
    (K : Subgroup G) (η : R(K)) (k : K) :
    IsIntegral ℤ (η k) := by
  -- Evaluate the algebraic-adjoin description of `R(K)` at the fixed element `k`.
  refine Algebra.adjoin_induction
      (p := fun f _ ↦ IsIntegral ℤ (f k))
      ?_ ?_ ?_ ?_ η.property
  · rintro χ ⟨ρ, hfd, hirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hfd
    letI : ρ.ρ.IsIrreducible := hirr
    simpa using Representation.char_isIntegral ρ.ρ k
  · intro n
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ n))
  · intro f g hf hg hf_int hg_int
    exact hf_int.add hg_int
  · intro f g hf hg hf_int hg_int
    exact hf_int.mul hg_int

/-- Helper for Theorem 11-11.3-2: the value at a `p'`-element of a character induced from `H` is
an algebraic-integer multiple of `p` whenever `H` contains no conjugate of the relevant
associated subgroup. -/
lemma induced_characterRing_value_eq_prime_multiple_of_algebraicInteger
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (x : G) (hx : IsPRegular p x)
    (P : Sylow p (Subgroup.centralizer ({x} : Set G)))
    (hH : ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup p x P ≤ H)
    (η : R(H)) :
    ∃ a : integralClosure ℤ ℂ,
      (a : ℂ) * (p : ℂ) = ((H.characterRingInduction η : R(G)) : G → ℂ) x := by
  let ψ : H → integralClosure ℤ ℂ :=
    fun h ↦
      Classical.choose <|
        (IsIntegralClosure.isIntegral_iff
          (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).mp
          (characterRing_value_isIntegral H η h)
  have hψ_coe (h : H) : ((ψ h : integralClosure ℤ ℂ) : ℂ) = η h :=
    Classical.choose_spec <|
      (IsIntegralClosure.isIntegral_iff
        (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).mp
        (characterRing_value_isIntegral H η h)
  have hη_class : _root_.IsClassFunction (η : H → ℂ) :=
    Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ) η η.property
  have hψ_class : _root_.IsClassFunction ψ := by
    -- The chosen integral lift is still constant on conjugacy classes because its complex values
    -- agree pointwise with the class function `η`.
    refine ⟨?_⟩
    intro y z hyz
    apply IsIntegralClosure.algebraMap_injective (integralClosure ℤ ℂ) ℤ ℂ
    calc
      (((ψ y : integralClosure ℤ ℂ) : ℂ)) = η y := hψ_coe y
      _ = η z := hη_class.factorsThrough hyz
      _ = (((ψ z : integralClosure ℤ ℂ) : ℂ)) := (hψ_coe z).symm
  have hind :
      (⟨Ind[H](fun h ↦ (ψ h : ℂ)) x, H.inducedClassFunction_apply_isIntegral ψ hψ_class x⟩ :
        integralClosure ℤ ℂ) ∈
        Ideal.span ({(p : integralClosure ℤ ℂ)} : Set (integralClosure ℤ ℂ)) :=
    Subgroup.inducedClassFunction_apply_mem_span_prime_of_no_conjugate_associatedPElementary
      (H := H) (x := x) hx P hH ψ hψ_class
  have hψ_eq : (fun h : H ↦ ((ψ h : integralClosure ℤ ℂ) : ℂ)) = (η : H → ℂ) := by
    funext h
    exact hψ_coe h
  have hind' :
      (⟨((H.characterRingInduction η : R(G)) : G → ℂ) x, by
          simpa [Subgroup.characterRingInduction_apply, hψ_eq] using
            H.inducedClassFunction_apply_isIntegral ψ hψ_class x⟩ :
        integralClosure ℤ ℂ) ∈
        Ideal.span ({(p : integralClosure ℤ ℂ)} : Set (integralClosure ℤ ℂ)) := by
    simpa [Subgroup.characterRingInduction_apply, hψ_eq] using hind
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hind'
  refine ⟨a, ?_⟩
  simpa using congrArg ((↑) : integralClosure ℤ ℂ → ℂ) ha

/-- Helper for Theorem 11-11.3-2: `1` is not a multiple of a prime inside the algebraic integers
of `ℂ`. -/
lemma one_ne_prime_multiple_of_algebraicInteger
    {p : ℕ} (hp : Nat.Prime p) :
    ¬ ∃ a : integralClosure ℤ ℂ, (a : ℂ) * (p : ℂ) = 1 := by
  rintro ⟨a, ha⟩
  have hintC : IsIntegral ℤ (algebraMap (integralClosure ℤ ℂ) ℂ a) := by
    exact (IsIntegralClosure.isIntegral_iff
      (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).2 ⟨a, rfl⟩
  have hEq : algebraMap ℚ ℂ (((1 : ℤ) : ℚ) / p) = algebraMap (integralClosure ℤ ℂ) ℂ a := by
    have hpC : (p : ℂ) ≠ 0 := by
      exact_mod_cast hp.ne_zero
    calc
      algebraMap ℚ ℂ (((1 : ℤ) : ℚ) / p) = (1 : ℂ) / p := by
        norm_num [Rat.cast_def]
      _ = algebraMap (integralClosure ℤ ℂ) ℂ a := by
        exact (div_eq_iff hpC).2 ha.symm
  have hintQ : IsIntegral ℤ ((((1 : ℤ) : ℚ) / p)) := by
    exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp <| by
      rw [hEq]
      exact hintC
  rcases (show ∃ z : ℤ, algebraMap ℤ ℚ z = (((1 : ℤ) : ℚ) / p) by
      simpa [IsLocalization.IsInteger] using UniqueFactorizationMonoid.integer_of_integral hintQ)
    with ⟨z, hz⟩
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hzmul := congrArg (fun x : ℚ ↦ x * p) hz
  field_simp [hpq] at hzmul
  have hz' : (1 : ℚ) = p * z := by
    simpa [mul_comm] using hzmul.symm
  have hdiv : (p : ℤ) ∣ 1 := by
    refine ⟨z, ?_⟩
    exact_mod_cast hz'
  have hdivNat : p ∣ 1 := by
    exact_mod_cast hdiv
  exact hp.not_dvd_one hdivNat

/-- Theorem 11-11.3-2: if the character ring `R(G)` is the supremum of the submodules generated by
characters induced from the family `(H i)`, viewed canonically as submodules of `R(G)`, then every
`p`-elementary subgroup of `G` is contained in a conjugate of one of the `H i`. -/
theorem isPElementary_le_conjugate_of_characterRing_eq_iSup_characterRingInduction_range
    (H : I → Subgroup G)
    (hR : (⨆ i, (H i).characterRingInduction.range) = ⊤)
    (p : ℕ) (E : Subgroup G) (hE : IsPElementary p E) :
    ∃ i : I, ∃ g : G, E ≤ MulAut.conj g • H i := by
  classical
  letI : Fact p.Prime := ⟨hE.prime⟩
  obtain ⟨x, Q, hx, hE_assoc⟩ :=
    exists_associatedPElementary_overgroup_of_isPElementary p E hE
  by_contra hcontra
  have hno_assoc (i : I) :
      ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup p (x : G) Q ≤ H i := by
    intro g hg
    apply hcontra
    refine ⟨i, g⁻¹, ?_⟩
    calc
      E ≤ associatedPElementarySubgroup p (x : G) Q := hE_assoc
      _ ≤ MulAut.conj g⁻¹ • H i := by
        -- Transport membership through the inverse conjugation map using the assumed inclusion
        -- into the conjugate of `H i`.
        intro y hy
        refine Subgroup.mem_map.2 ?_
        refine ⟨MulAut.conj g y, hg ?_, ?_⟩
        · exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
        · simpa using MulAut.apply_inv_self G (MulAut.conj g) y
  have hone :
      (1 : R(G)) ∈ (⨆ i, (H i).characterRingInduction.range) := by
    have hone_top : (1 : R(G)) ∈ (⊤ : Submodule ℤ (R(G))) := by
      simp
    rw [← hR] at hone_top
    exact hone_top
  have hdiv :
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) * (p : ℂ) = ((1 : R(G)) : G → ℂ) x := by
    -- `iSup`-induction propagates the divisibility-by-`p` property from each induction range to
    -- the whole supremum, hence to the unit character.
    refine Submodule.iSup_induction
        (p := fun i ↦ (H i).characterRingInduction.range)
        (motive := fun χ : R(G) ↦
          ∃ a : integralClosure ℤ ℂ, (a : ℂ) * (p : ℂ) = χ x)
        hone ?_ ?_ ?_
    · intro i χ hχ
      rcases hχ with ⟨η, rfl⟩
      exact induced_characterRing_value_eq_prime_multiple_of_algebraicInteger
        (H := H i) (x := x) hx Q (hno_assoc i) η
    · refine ⟨0, ?_⟩
      simp
    · intro χ ψ hχ hψ
      rcases hχ with ⟨a, ha⟩
      rcases hψ with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      calc
        (((a + b : integralClosure ℤ ℂ) : ℂ) * (p : ℂ))
            = (a : ℂ) * (p : ℂ) + (b : ℂ) * (p : ℂ) := by
                simp [add_mul]
        _ = χ x + ψ x := by rw [ha, hb]
        _ = (χ + ψ) x := by rfl
  rcases hdiv with ⟨a, ha⟩
  have hone_value : (a : ℂ) * (p : ℂ) = 1 := by
    simpa using ha
  exact one_ne_prime_multiple_of_algebraicInteger hE.prime ⟨a, hone_value⟩

end
