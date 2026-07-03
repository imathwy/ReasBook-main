import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_1
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1

-- Stable elementary-detection infrastructure extracted from Remark 11-11.1-3.

noncomputable section

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation TensorProduct

variable {G : Type} [Group G] [Finite G]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

omit [Finite G] in
/-- Helper for Remark 11-11.1-3: every ordinary character belongs to the realized integral scalar
extension.
-/
private theorem mem_characterRingScalarExtension_overIntegers_of_mem_characterRing
    (χ : G → ℂ) (hχ : χ ∈ R(G)) :
    χ ∈ Representation.characterRingScalarExtension ℤ G :=
  Submodule.subset_span hχ

omit [Finite G] in
/-- Helper for Remark 11-11.1-3: the realized integral scalar extension is closed under pointwise
multiplication.
-/
private theorem mul_mem_characterRingScalarExtension_overIntegers {f g : G → ℂ}
    (hf : f ∈ Representation.characterRingScalarExtension ℤ G)
    (hg : g ∈ Representation.characterRingScalarExtension ℤ G) :
    f * g ∈ Representation.characterRingScalarExtension ℤ G := by
  revert g hg
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      intro g hg
      induction hg using Submodule.span_induction with
      | mem φ hφ =>
          exact Submodule.subset_span ((R(G)).mul_mem hψ hφ)
      | zero =>
          exact by
            simp
      | add g₁ g₂ _ _ ih₁ ih₂ =>
          simpa [Pi.mul_apply, mul_add] using
            (Representation.characterRingScalarExtension ℤ G).add_mem ih₁ ih₂
      | smul a g _ ih =>
          simpa [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def, mul_assoc, mul_left_comm,
            mul_comm] using
              (Representation.characterRingScalarExtension ℤ G).smul_mem a ih
  | zero =>
      intro g hg
      exact by
        simp
  | add f₁ f₂ _ _ ih₁ ih₂ =>
      intro g hg
      simpa [Pi.mul_apply, add_mul] using
        (Representation.characterRingScalarExtension ℤ G).add_mem (ih₁ hg) (ih₂ hg)
  | smul a f _ ih =>
      intro g hg
      simpa [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
        using (Representation.characterRingScalarExtension ℤ G).smul_mem a (ih hg)

/-- Helper for Remark 11-11.1-3: multiplying an induced class function by an ambient class
function rewrites as induction of the product with the subgroup restriction.
-/
private theorem induced_mul_eq_induced_mul_classFunctionRestriction_local
    (H : Subgroup G) (ψ : H → ℂ) (φ : classFunctionSubmodule ℂ G) :
    Subgroup.inducedClassFunction H ψ * (φ : G → ℂ) =
      Subgroup.inducedClassFunction H
        (fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → ℂ) h) := by
  simpa using
    Representation.induced_mul_eq_induced_mul_classFunctionRestriction (G := G) H ψ φ

omit [Finite G] in
/-- Helper for Remark 11-11.1-3: the unit character acts trivially by pointwise multiplication on
class functions.
-/
private theorem one_character_mul_classFunction_local (φ : classFunctionSubmodule ℂ G) :
    ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) = (φ : G → ℂ) := by
  ext x
  simp

/-- Helper for Remark 11-11.1-3: a coherent integral family of local characters takes the same
value on any two subgroup elements that are conjugate in the ambient group. -/
private theorem coherent_character_family_value_eq_of_isConj
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (φX : (H : X) → R(H.1))
    (hres :
      ∀ {H H' : X} (hH'H : H'.1 ≤ H.1),
        ((hH'H ↾R[ℂ]) (φX H) : R(H'.1)) = φX H')
    (hconj :
      ∀ (H : X) (s : G) (hHs : (s •ᶜ H.1) ∈ X),
        Subgroup.characterRingTransport ((MulAut.conj s).subgroupMap H.1).symm (φX H) =
          φX ⟨s •ᶜ H.1, hHs⟩)
    {H K : X} {x : H.1} {y : K.1}
    (hxy : IsConj (x : G) (y : G)) :
    ((φX H : R(H.1)) : H.1 → ℂ) x = ((φX K : R(K.1)) : K.1 → ℂ) y := by
  rcases isConj_iff.1 hxy with ⟨s, hs⟩
  let J : X := ⟨s •ᶜ H.1, elementary_mem_of_conj X hXelem H.2 s⟩
  have hyJ : (y : G) ∈ J.1 := by
    change (y : G) ∈ H.1.map (MulAut.conj s).toMonoidHom
    rw [Subgroup.mem_map_equiv (f := MulAut.conj s) (K := H.1)]
    change s⁻¹ * (y : G) * s ∈ H.1
    have hsy : s⁻¹ * (y : G) * s = x := by
      calc
        s⁻¹ * (y : G) * s = s⁻¹ * (s * x * s⁻¹) * s := by rw [hs]
        _ = x := by simp [mul_assoc]
    rw [hsy]
    exact x.2
  let yJ : J.1 := ⟨y, hyJ⟩
  let C : Subgroup G := Subgroup.zpowers (y : G)
  let CX : X := ⟨C, (hXelem _).2 (Subgroup.isElementary_zpowers (y : G))⟩
  let yC : C := ⟨y, Subgroup.mem_zpowers (y : G)⟩
  have hCJ : C ≤ J.1 := Subgroup.zpowers_le.2 hyJ
  have hCYK :
      ((φX CX : R(C)) : C → ℂ) yC = ((φX K : R(K.1)) : K.1 → ℂ) y := by
    have hrestrict := congrArg
      (fun χ : R(CX.1) ↦ ((χ : C → ℂ) yC))
      (hres (H := K) (H' := CX) (Subgroup.zpowers_le.2 y.2))
    simpa [CX, C, yC, Subgroup.characterRingOverFieldRestrictionOfLe_apply] using hrestrict.symm
  have hCYJ :
      ((φX CX : R(C)) : C → ℂ) yC = ((φX J : R(J.1)) : J.1 → ℂ) yJ := by
    have hrestrict := congrArg
      (fun χ : R(CX.1) ↦ ((χ : C → ℂ) yC))
      (hres (H := J) (H' := CX) hCJ)
    simpa [CX, C, yC, J, yJ, Subgroup.characterRingOverFieldRestrictionOfLe_apply] using
      hrestrict.symm
  have hJH :
      ((φX J : R(J.1)) : J.1 → ℂ) yJ = ((φX H : R(H.1)) : H.1 → ℂ) x := by
    have hxeq : (((MulAut.conj s).subgroupMap H.1).symm yJ) = x := by
      apply Subtype.ext
      change s⁻¹ * ((yJ : J.1) : G) * s = x
      calc
        s⁻¹ * ((yJ : J.1) : G) * s = s⁻¹ * (s * x * s⁻¹) * s := by
          change s⁻¹ * (y : G) * s = s⁻¹ * (s * x * s⁻¹) * s
          rw [hs]
        _ = x := by simp [mul_assoc]
    have htransport := congrArg
      (fun χ : R(J.1) ↦ ((χ : J.1 → ℂ) yJ))
      (hconj H s J.2)
    simpa [J, Subgroup.characterRingTransport_apply, hxeq] using htransport.symm
  calc
    ((φX H : R(H.1)) : H.1 → ℂ) x = ((φX J : R(J.1)) : J.1 → ℂ) yJ := hJH.symm
    _ = ((φX CX : R(C)) : C → ℂ) yC := hCYJ.symm
    _ = ((φX K : R(K.1)) : K.1 → ℂ) y := hCYK

/-- Helper for Remark 11-11.1-3: a coherent integral family of local characters glues to a global
bundled class function. -/
theorem exists_glued_classFunction_of_coherent_character_family_on_elementarySubgroups
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (φX : (H : X) → R(H.1))
    (hres :
      ∀ {H H' : X} (hH'H : H'.1 ≤ H.1),
        ((hH'H ↾R[ℂ]) (φX H) : R(H'.1)) = φX H')
    (hconj :
      ∀ (H : X) (s : G) (hHs : (s •ᶜ H.1) ∈ X),
        Subgroup.characterRingTransport ((MulAut.conj s).subgroupMap H.1).symm (φX H) =
          φX ⟨s •ᶜ H.1, hHs⟩) :
    ∃ φ : classFunctionSubmodule ℂ G,
      ∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) = (φX H : H.1 → ℂ) := by
  classical
  let witnessH : G → X := fun g ↦
    ⟨Subgroup.zpowers g, (hXelem _).2 (Subgroup.isElementary_zpowers g)⟩
  let witnessx : ∀ g : G, (witnessH g).1 := fun g ↦ ⟨g, Subgroup.mem_zpowers g⟩
  let χfun : G → ℂ := fun g ↦
    ((φX (witnessH g) : R((witnessH g).1)) : (witnessH g).1 → ℂ) (witnessx g)
  have hχclass : _root_.IsClassFunction χfun := by
    refine ⟨?_⟩
    intro g g' hgg'
    have hgg'_conj : IsConj g g' := (ConjClasses.mk_eq_mk_iff_isConj).1 hgg'
    simpa [χfun, witnessx] using
      coherent_character_family_value_eq_of_isConj X hXelem φX hres hconj
        (H := witnessH g) (K := witnessH g') (x := witnessx g) (y := witnessx g') hgg'_conj
  refine ⟨⟨χfun, (mem_classFunctionSubmodule_iff ℂ _).2 hχclass⟩, ?_⟩
  intro H
  ext x
  change
    ((φX (witnessH (x : G)) : R((witnessH (x : G)).1)) :
        (witnessH (x : G)).1 → ℂ) (witnessx (x : G)) =
      ((φX H : R(H.1)) : H.1 → ℂ) x
  exact coherent_character_family_value_eq_of_isConj X hXelem φX hres hconj
    (H := witnessH (x : G)) (K := H) (x := witnessx (x : G)) (y := x) <|
      (by simpa [witnessx] using IsConj.refl (x : G))

/-- Helper for Remark 11-11.1-3: if the restrictions of a bundled class function to all
elementary subgroups lie in the corresponding integral character rings, then the ambient class
function already lies in `R(G)`. -/
private theorem induced_mem_characterRingScalarExtension_of_mem_overIntegers
    (H : Subgroup G) {f : H → ℂ}
    (hf : f ∈ Representation.characterRingScalarExtension ℤ H) :
    Subgroup.inducedClassFunction H f ∈ Representation.characterRingScalarExtension ℤ G := by
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      let χR : R(H) := ⟨χ, hχ⟩
      have hindMem : Subgroup.inducedClassFunction H χ ∈ R(G) := by
        simpa [χR] using Subgroup.inducedClassFunction_mem_characterRing H χR
      exact mem_characterRingScalarExtension_overIntegers_of_mem_characterRing
        (Subgroup.inducedClassFunction H χ) hindMem
  | zero =>
      have hzero : Subgroup.inducedClassFunction H (0 : H → ℂ) = (0 : G → ℂ) := by
        ext g
        simp [Subgroup.inducedClassFunction]
      rw [hzero]
      exact (zero_mem (Representation.characterRingScalarExtension ℤ G) :
        (0 : G → ℂ) ∈ Representation.characterRingScalarExtension ℤ G)
  | add f g _ _ hf hg =>
      simpa [Subgroup.inducedClassFunction_map_add] using
        (Representation.characterRingScalarExtension ℤ G).add_mem hf hg
  | smul a f _ hf =>
      rw [Subgroup.inducedClassFunction_map_smul]
      exact (Representation.characterRingScalarExtension ℤ G).smul_mem a hf

/-- Helper for Remark 11-11.1-3: every Brauer submodule element detects the realized integral
scalar extension after multiplication by the class function `φ`. -/
private theorem pElementaryInducedCharacterSpan_mul_classFunction_mem_characterRingScalarExtension
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsElementary H →
      (H.classFunctionRestriction φ : H → ℂ) ∈ Representation.characterRingScalarExtension ℤ H)
    (p : Nat.Primes) {χ : R(G)} (hχ : χ ∈ Representation.pElementaryInducedCharacterSpan (p : ℕ) G) :
    ((χ : G → ℂ) * (φ : G → ℂ)) ∈ Representation.characterRingScalarExtension ℤ G := by
  classical
  let _ : DecidablePred (fun H : Subgroup G ↦ IsPElementary (p : ℕ) H) := Classical.decPred _
  rw [Representation.pElementaryInducedCharacterSpan] at hχ
  simp_rw [Representation.artinInducedCharacterSubmodule] at hχ
  refine Submodule.iSup_induction
      (p := fun H :
        { H : Subgroup G |
          H ∈ Finset.filter (fun H : Subgroup G ↦ IsPElementary (p : ℕ) H) Finset.univ } ↦
        LinearMap.range (Representation.Subgroup.characterRingInduction H.1))
      (motive := fun ξ : R(G) ↦
        ((ξ : G → ℂ) * (φ : G → ℂ)) ∈ Representation.characterRingScalarExtension ℤ G)
      hχ ?_ ?_ ?_
  · intro H ξ hξ
    rcases H with ⟨H, hHmem⟩
    rcases hξ with ⟨η, rfl⟩
    have hH : IsPElementary (p : ℕ) H := by
      simpa using (Finset.mem_filter.mp hHmem).2
    have hη :
        ((η : R(H)) : H → ℂ) ∈ Representation.characterRingScalarExtension ℤ H :=
      mem_characterRingScalarExtension_overIntegers_of_mem_characterRing _ η.property
    have hφH :
        (H.classFunctionRestriction φ : H → ℂ) ∈ Representation.characterRingScalarExtension ℤ H :=
      hres H ⟨p, hH⟩
    have hmul :
        ((η : R(H)) : H → ℂ) * (H.classFunctionRestriction φ : H → ℂ) ∈
          Representation.characterRingScalarExtension ℤ H :=
      mul_mem_characterRingScalarExtension_overIntegers hη hφH
    have hind :
        Subgroup.inducedClassFunction H
          ((((η : R(H)) : H → ℂ) * (H.classFunctionRestriction φ : H → ℂ)) : H → ℂ) ∈
          Representation.characterRingScalarExtension ℤ G :=
      induced_mem_characterRingScalarExtension_of_mem_overIntegers H hmul
    rw [Representation.Subgroup.characterRingInduction_apply,
      induced_mul_eq_induced_mul_classFunctionRestriction_local]
    exact hind
  · exact by
      simp [zero_mul]
  · intro ξ η hξ hη
    simpa [add_mul] using (Representation.characterRingScalarExtension ℤ G).add_mem hξ hη

/-- Helper for Remark 11-11.1-3: if the restrictions of a bundled class function to all
elementary subgroups lie in the corresponding integral character rings, then the ambient class
function already lies in `R(G)`. -/
theorem classFunction_mem_characterRing_of_restrict_mem_on_elementarySubgroups
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : X, (H.1.classFunctionRestriction φ : H.1 → ℂ) ∈ R(H.1)) :
    (φ : G → ℂ) ∈ R(G) := by
  have hresScalar :
      ∀ H : Subgroup G, IsElementary H →
        (H.classFunctionRestriction φ : H → ℂ) ∈ Representation.characterRingScalarExtension ℤ H := by
    intro H hH
    let HX : X := ⟨H, (hXelem H).2 hH⟩
    have hspanH :
        Representation.characterRingScalarExtension ℤ H = (R(H)).toSubmodule := by
      rw [Representation.characterRingScalarExtension]
      exact Submodule.span_eq ((R(H)).toSubmodule : Submodule ℤ (H → ℂ))
    simpa [HX, hspanH] using hres HX
  have hspanG :
      Representation.characterRingScalarExtension ℤ G = (R(G)).toSubmodule := by
    rw [Representation.characterRingScalarExtension]
    exact Submodule.span_eq ((R(G)).toSubmodule : Submodule ℤ (G → ℂ))
  have hone :
      ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) ∈ Representation.characterRingScalarExtension ℤ G := by
    have hone' : (1 : R(G)) ∈ (⨆ p : Nat.Primes, Representation.pElementaryInducedCharacterSpan (p : ℕ) G) := by
      simpa using character_mem_iSup_pElementaryInducedCharacterSpan (G := G) (1 : R(G))
    refine Submodule.iSup_induction
        (p := fun p : Nat.Primes ↦ Representation.pElementaryInducedCharacterSpan (p : ℕ) G)
        (motive := fun χ : R(G) ↦
          ((χ : G → ℂ) * (φ : G → ℂ)) ∈ Representation.characterRingScalarExtension ℤ G)
        hone' ?_ ?_ ?_
    · intro p χ hχ
      exact pElementaryInducedCharacterSpan_mul_classFunction_mem_characterRingScalarExtension
        φ hresScalar p hχ
    · exact by
        simp [zero_mul]
    · intro χ ψ hχ hψ
      simpa [add_mul] using (Representation.characterRingScalarExtension ℤ G).add_mem hχ hψ
  have hφScalar :
      (φ : G → ℂ) ∈ Representation.characterRingScalarExtension ℤ G := by
    rw [← one_character_mul_classFunction_local φ]
    exact hone
  simpa [hspanG] using hφScalar

end CharacterizationOfCharacters

end Representation
