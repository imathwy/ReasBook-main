import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_1_2
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_5_2
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_5
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_1
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_1_4
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1.Index
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace Representation

section FrobeniusTheorem

open scoped Representation TensorProduct BigOperators SubgroupInduction

variable {G : Type u} [Group G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]

/-- Helper for Theorem 11-11.2-1: a finite group has finitely many conjugacy classes. -/
local instance theorem_11_11_2_1_conjClasses_fintype
    (H : Type w) [Group H] [Finite H] : Fintype (ConjClasses H) :=
  Fintype.ofFinite (ConjClasses H)

/-- Helper for Theorem 11-11.2-1: finite groups carry their canonical `Fintype` structure. -/
local instance theorem_11_11_2_1_group_fintype
    (H : Type w) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

/-- Helper for Theorem 11-11.2-1: finite subgroups inherit their canonical `Fintype` structure. -/
local instance theorem_11_11_2_1_subgroup_fintype [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Helper for Theorem 11-11.2-1: finite groups use classical decidable equality when theorem
statements involve explicit root-fiber equations. -/
local instance theorem_11_11_2_1_group_decidableEq
    (H : Type w) [Group H] [Finite H] : DecidableEq H :=
  Classical.decEq H

/-- Helper for Theorem 11-11.2-1: `n`th-power membership in a conjugacy class is classically
decidable on finite groups. -/
local instance theorem_11_11_2_1_nthPow_mem_conjClass_decidablePred
    (H : Type w) [Group H] [Finite H] (n : ℕ+) (c : ConjClasses H) :
    DecidablePred (fun x : H ↦ x ^ (n : ℕ) ∈ c.carrier) :=
  Classical.decPred _

/-- Helper for Theorem 11-11.2-1: the ambient roots-of-unity hypothesis restricts to every
subgroup. -/
private theorem subgroup_roots_hypothesis_of_ambient_roots
    [Finite G] (H : Subgroup G)
    (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ∀ z : ℂˣ, z ^ Nat.card H = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)) := by
  intro z hz
  have hdiv : Nat.card H ∣ Nat.card G := by
    simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H
  rcases hdiv with ⟨m, hm⟩
  -- Raise the subgroup relation `z ^ |H| = 1` to the quotient power `m` to recover the ambient
  -- relation required by `hroots`.
  apply hroots z
  rw [hm, pow_mul]
  have hz' : z ^ Fintype.card H = 1 := by
    simpa [Nat.card_eq_fintype_card] using hz
  simp [hz']

/-- Helper for Theorem 11-11.2-1: precomposing an ordinary complex character with a
multiplicative equivalence preserves character-ring membership. -/
private theorem mem_characterRing_of_precomp_mulEquiv_local
    {H : Type w} [Group H] [Finite H] {J : Type*} [Group J] [Finite J]
    (e : H ≃* J) {χ : J → ℂ} (hχ : χ ∈ R(J)) :
    (fun h : H ↦ χ (e h)) ∈ R(H) := by
  -- Transport each honest complex character generator through `e`, then close under the ring
  -- operations generating `R(H)`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    letI : FiniteDimensional ℂ ρ := hρfd
    let τρ : Representation ℂ H ρ := ρ.ρ.comp e.toMonoidHom
    have hτρ : τρ.character = fun h : H ↦ ρ.ρ.character (e h) := by
      -- Character transport across precomposition is pointwise definitional.
      ext h
      rfl
    exact hτρ ▸ Representation.rep_character_mem_characterRing (Rep.of τρ)
  · intro n
    exact (R(H)).algebraMap_mem n
  · intro f g _ _ hf hg
    simpa using (R(H)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa using (R(H)).mul_mem hf hg

/-- Helper for Theorem 11-11.2-1: precomposing a realized scalar-extension function with a
multiplicative equivalence preserves realized scalar-extension membership. -/
private theorem mem_characterRingScalarExtension_precomp_mulEquiv_local
    {H : Type w} [Group H] [Finite H] {J : Type*} [Group J] [Finite J]
    (e : H ≃* J) {f : J → ℂ} (hf : f ∈ characterRingScalarExtension A J) :
    (fun h : H ↦ f (e h)) ∈ characterRingScalarExtension A H := by
  rw [characterRingScalarExtension] at hf ⊢
  refine
    Submodule.span_induction
      (s := (R(J) : Set (J → ℂ)))
      (p := fun ψ _ ↦ (fun h : H ↦ ψ (e h)) ∈ Submodule.span A (R(H) : Set (H → ℂ)))
      ?_ ?_ ?_ ?_ hf
  · intro ψ hψ
    -- A generator stays inside the ordinary character ring after transport along `e`.
    exact Submodule.subset_span <|
      mem_characterRing_of_precomp_mulEquiv_local (e := e) hψ
  · change (0 : H → ℂ) ∈ Submodule.span A (R(H) : Set (H → ℂ))
    exact zero_mem (Submodule.span A (R(H) : Set (H → ℂ)))
  · intro ψ ξ _ _ hψ hξ
    simpa using Submodule.add_mem (Submodule.span A (R(H) : Set (H → ℂ))) hψ hξ
  · intro a ψ _ hψ
    simpa [Pi.smul_apply, Algebra.smul_def] using
      Submodule.smul_mem (Submodule.span A (R(H) : Set (H → ℂ))) a hψ

/-- Helper for Theorem 11-11.2-1: precomposing a bundled class function with a multiplicative
equivalence preserves the class-function condition. -/
private theorem classFunction_precomp_mulEquiv_mem_local
    {H : Type w} [Group H] [Finite H] {J : Type*} [Group J] [Finite J]
    (e : H ≃* J) (φ : classFunctionSubmodule ℂ J) :
    (fun h : H ↦ (φ : J → ℂ) (e h)) ∈ classFunctionSubmodule ℂ H := by
  let hφ : _root_.IsClassFunction (φ : J → ℂ) := (mem_classFunctionSubmodule_iff ℂ _).1 φ.2
  refine (mem_classFunctionSubmodule_iff ℂ _).2 ?_
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hxyH : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  have hxyJ : IsConj (e x) (e y) := by
    rw [isConj_iff] at hxyH ⊢
    rcases hxyH with ⟨a, ha⟩
    refine ⟨e a, ?_⟩
    simpa using congrArg e ha
  exact _root_.IsClassFunction.eq_of_isConj hφ hxyJ

/-- Helper for Theorem 11-11.2-1: normalized class-function pairing is unchanged after
precomposing both arguments with a multiplicative equivalence. -/
private theorem groupFunctionPairing_precomp_mulEquiv_local
    {H : Type w} [Group H] [Finite H] {J : Type*} [Group J] [Finite J]
    (e : H ≃* J) (φ ψ : J → ℂ) :
    Representation.groupFunctionPairingOverField ℂ
        (fun h : H ↦ φ (e h))
        (fun h : H ↦ ψ (e h)) =
      Representation.groupFunctionPairingOverField ℂ φ ψ := by
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype J := Fintype.ofFinite J
  have hcard : Fintype.card H = Fintype.card J := Fintype.card_congr e.toEquiv
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField,
    hcard]
  congr 1
  simpa [MulEquiv.map_inv] using
    (Equiv.sum_comp e.toEquiv (fun g : J ↦ φ g⁻¹ * ψ g))

/-- Helper for Theorem 11-11.2-1: transporting both a degree-`1` character and a class function
along a multiplicative equivalence leaves their pairing unchanged. -/
private theorem linear_character_pairing_precomp_mulEquiv_local
    {H : Type w} [Group H] [Finite H] {J : Type*} [Group J] [Finite J]
    (e : H ≃* J) (χ : H →* ℂˣ) (φ : classFunctionSubmodule ℂ J) :
    ⟪χ.toCharacterRing,
      (fun h : H ↦ (φ : J → ℂ) (e h))⟫ =
      ⟪(χ.comp e.symm.toMonoidHom).toCharacterRing, φ⟫ := by
  -- Precomposing both pairing arguments along `e` identifies the transported pairing with the
  -- original one on the target group.
  have hleft :
      (χ.toCharacterRing : H → ℂ) = fun h : H ↦ (χ h : ℂ) := by
    ext h
    simp [MonoidHom.toCharacterRing_apply]
  have hright :
      ((χ.comp e.symm.toMonoidHom).toCharacterRing : J → ℂ) =
        fun j : J ↦ (χ (e.symm j) : ℂ) := by
    ext j
    simp [MonoidHom.toCharacterRing_apply]
  rw [hleft, hright]
  simpa using
    groupFunctionPairing_precomp_mulEquiv_local
      (e := e)
      (φ := fun j : J ↦ (χ (e.symm j) : ℂ))
      (ψ := (φ : J → ℂ))

/-- Helper for Theorem 11-11.2-1: Brauer's elementary-subgroup detection lifts a class function
from realized elementary restrictions to the global tensor character ring. -/
private theorem classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups_local
    [Finite G] (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsElementary H →
      (fun h : H ↦ (φ : G → ℂ) h) ∈ characterRingScalarExtension A H) :
    ∃ ψ : A ⊗R(G), (ψ : G → ℂ) = (φ : G → ℂ) := by
  classical
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  let φ₀ : classFunctionSubmodule ℂ (Shrink.{0} G) :=
    ⟨fun x ↦ (φ : G → ℂ) (e x), classFunction_precomp_mulEquiv_mem_local (e := e) φ⟩
  have hres₀ :
      ∀ H₀ : Subgroup (Shrink.{0} G), IsElementary H₀ →
        (fun h : H₀ ↦ (φ₀ : Shrink.{0} G → ℂ) h) ∈ characterRingScalarExtension A H₀ := by
    intro H₀ hH₀
    let H : Subgroup G := H₀.map e.toMonoidHom
    let eH : H₀ ≃* H := H₀.equivMapOfInjective e.toMonoidHom e.injective
    have hH : IsElementary H := isElementary_of_mulEquiv_local eH hH₀
    have hHmem :
        (fun h : H ↦ (φ : G → ℂ) h) ∈ characterRingScalarExtension A H :=
      hres H hH
    -- Pull the realized restriction on the mapped subgroup back through the subgroup equivalence.
    simpa [φ₀, H, eH] using
      mem_characterRingScalarExtension_precomp_mulEquiv_local
        (A := A) (e := eH) hHmem
  obtain ⟨ψ₀, hψ₀⟩ :=
    classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups_of_brauer_span
      (G := Shrink.{0} G) (A := A)
      (hbrauer := by
        -- Route correction: apply Chapter `10.10.5.1` on the small owner `Shrink G`, then rewrite
        -- the theorem-local Brauer owners back to the Chapter `10` owners.
        simpa [pElementaryInducedCharacterSpan_local, Representation.pElementaryInducedCharacterSpan,
          artinInducedCharacterSubmodule_local, Representation.artinInducedCharacterSubmodule,
          Subgroup.characterRingInduction_local, Representation.Subgroup.characterRingInduction]
          using (iSup_pElementaryInducedCharacterSpan_eq_top (G := Shrink.{0} G)))
      φ₀ hres₀
  have hmem₀ : (φ₀ : Shrink.{0} G → ℂ) ∈ characterRingScalarExtension A (Shrink.{0} G) := by
    -- The small-owner tensor witness realizes `φ₀`, hence `φ₀` already lies in the realized span.
    have hψ₀mem : (ψ₀ : Shrink.{0} G → ℂ) ∈
        characterRingScalarExtension A (Shrink.{0} G) :=
      tensorCharacterRing_mem_characterRingScalarExtension (A := A) ψ₀
    simpa [hψ₀] using hψ₀mem
  have hmem :
      (fun g : G ↦ (φ₀ : Shrink.{0} G → ℂ) (e.symm g)) ∈ characterRingScalarExtension A G := by
    -- Push the realized small-owner function back along the inverse shrink equivalence.
    exact
      mem_characterRingScalarExtension_precomp_mulEquiv_local
        (A := A) (e := e.symm) hmem₀
  have hφ : (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
    simpa [e, φ₀] using hmem
  -- Convert the realized scalar-extension membership back to an owner element of `A ⊗ R(G)`.
  exact tensorCharacter_exists_of_mem_characterRingScalarExtension (A := A) hφ

omit [Algebra A ℂ] in
/-- Helper for Theorem 11-11.2-1: an `A`-valued class function is the sum of its conjugacy-class
coefficients against the indicator basis. -/
private theorem classFunction_eq_sum_conjClass_indicator
    {H : Type w} [Group H] [Finite H] (φ : classFunctionSubmodule A H) :
    (φ : H → A) =
      fun x : H ↦
        ∑ c : ConjClasses H,
          ((mem_classFunctionSubmodule_iff A _).1 φ.2).lift c * c.indicator x := by
  classical
  let hφ : _root_.IsClassFunction (φ : H → A) := (mem_classFunctionSubmodule_iff A _).1 φ.2
  funext x
  let c₀ : ConjClasses H := ConjClasses.mk x
  have hxmem : x ∈ c₀.carrier := by
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr rfl
  -- The conjugacy-class indicators form a partition indexed by `ConjClasses H`.
  calc
    (φ : H → A) x = hφ.lift c₀ := by
      simpa [c₀] using (_root_.IsClassFunction.lift_mk hφ x).symm
    _ =
        ∑ c : ConjClasses H,
          hφ.lift c * c.indicator x := by
            rw [Finset.sum_eq_single c₀]
            · simp [c₀, ConjClasses.indicator, hxmem]
            · intro c _ hc
              have hnot : x ∉ c.carrier := by
                intro hx
                have hc' : c = c₀ := by
                  exact (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm
                exact hc hc'
              simp [ConjClasses.indicator, hnot]
            · simp [c₀, ConjClasses.indicator, hxmem]
    _ =
        (fun x : H ↦
          ∑ c : ConjClasses H,
            ((mem_classFunctionSubmodule_iff A _).1 φ.2).lift c * c.indicator x) x := by
              simp

/-- Helper for Theorem 11-11.2-1: the weighted Adams transform is again a bundled complex-valued
class function. -/
private theorem weightedAdamsClassFunction_mem [Finite G]
    (n : ℕ+) (f : classFunctionSubmodule A G) :
    (fun g ↦
      algebraMap A ℂ
        ((((orderOf g / Nat.gcd (orderOf g) (n : ℕ)) : ℕ) : A) * Ψ^n(f) g)) ∈
      classFunctionSubmodule ℂ G := by
  let hf : _root_.IsClassFunction (f : G → A) := (mem_classFunctionSubmodule_iff A _).1 f.2
  let hadams : _root_.IsClassFunction (Ψ^n((f : G → A))) := isClassFunction_adamsOperator n hf
  refine (mem_classFunctionSubmodule_iff ℂ _).2 ?_
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hxy_conj : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  have hadams_eq : Ψ^n(f) x = Ψ^n(f) y := by
    exact _root_.IsClassFunction.eq_of_isConj hadams hxy_conj
  rcases hxy_conj with ⟨a, ha⟩
  have hord : orderOf x = orderOf y := by
    simpa using SemiconjBy.orderOf_eq (a := (a : G)) ha
  have hA :
      ((((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) : A) * Ψ^n(f) x) =
        ((((orderOf y / Nat.gcd (orderOf y) (n : ℕ)) : ℕ) : A) * Ψ^n(f) y) := by
    simp [hord, hadams_eq]
  exact congrArg (algebraMap A ℂ) hA

/-- Helper for Theorem 11-11.2-1: the corrected global Frobenius-weighted Adams transform is a
bundled complex-valued class function. -/
private theorem globalWeightedAdamsClassFunction_mem [Finite G]
    (n : ℕ+) (f : classFunctionSubmodule A G) :
    (fun g ↦
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) * Ψ^n(f) g)) ∈
      classFunctionSubmodule ℂ G := by
  let hf : _root_.IsClassFunction (f : G → A) := (mem_classFunctionSubmodule_iff A _).1 f.2
  let hadams : _root_.IsClassFunction (Ψ^n((f : G → A))) := isClassFunction_adamsOperator n hf
  refine (mem_classFunctionSubmodule_iff ℂ _).2 ?_
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hxy_conj : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  have hadams_eq : Ψ^n(f) x = Ψ^n(f) y := by
    exact _root_.IsClassFunction.eq_of_isConj hadams hxy_conj
  have hA :
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) * Ψ^n(f) x) =
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) * Ψ^n(f) y) := by
    simp [hadams_eq]
  exact congrArg (algebraMap A ℂ) hA

/-- Helper for Theorem 11-11.2-1: the corrected global Frobenius-weighted Adams transform,
packaged as a bundled complex class function. -/
private def globalWeightedAdamsClassFunction [Finite G]
    (n : ℕ+) (f : classFunctionSubmodule A G) : classFunctionSubmodule ℂ G :=
  ⟨fun g ↦
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) * Ψ^n(f) g),
    globalWeightedAdamsClassFunction_mem (A := A) n f⟩

/-- Helper for Theorem 11-11.2-1: the weighted Adams transform packaged as a bundled complex class
function. -/
private def weightedAdamsClassFunction [Finite G]
    (n : ℕ+) (f : classFunctionSubmodule A G) : classFunctionSubmodule ℂ G :=
  ⟨fun g ↦
      algebraMap A ℂ
        ((((orderOf g / Nat.gcd (orderOf g) (n : ℕ)) : ℕ) : A) * Ψ^n(f) g),
    weightedAdamsClassFunction_mem (A := A) n f⟩

/-- Helper for Theorem 11-11.2-1: after restricting to a subgroup, the weighted Adams transform is
the indicator-basis expansion of the restricted source class function. -/
private theorem weighted_adams_restriction_eq_sum_conjClass_indicator
    [Finite G] (n : ℕ+) (f : classFunctionSubmodule A G) (H : Subgroup G) :
    (fun h : H ↦ (weightedAdamsClassFunction (A := A) n f : G → ℂ) h) =
      ∑ c : ConjClasses H,
        (((mem_classFunctionSubmodule_iff A _).1
          (subgroupClassFunctionRestriction (A := A) H f).2).lift c) •
          (fun h : H ↦
            algebraMap A ℂ
              ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
                Ψ^n((c.indicator : H → A)) h)) := by
  classical
  let fH : classFunctionSubmodule A H := subgroupClassFunctionRestriction (A := A) H f
  let a : ConjClasses H → A :=
    fun c ↦ ((mem_classFunctionSubmodule_iff A _).1 fH.2).lift c
  let w : H → A := fun h ↦ (((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A)
  -- Expand the restricted source class function in the indicator basis, then transport the same
  -- finite decomposition through the Adams operator and the pointwise weight.
  funext h
  have hdecomp :
      (fH : H → A) = fun x : H ↦ ∑ c : ConjClasses H, a c * c.indicator x := by
    simpa [fH, a] using classFunction_eq_sum_conjClass_indicator (A := A) fH
  have hEval :
      Ψ^n(fH) h = ∑ c : ConjClasses H, a c * Ψ^n((c.indicator : H → A)) h := by
    simpa [Representation.adamsOperator] using
      congrArg (fun φ : H → A ↦ φ (h ^ (n : ℕ))) hdecomp
  have hweighted :
      w h * Ψ^n(fH) h =
        ∑ c : ConjClasses H, a c * (w h * Ψ^n((c.indicator : H → A)) h) := by
    calc
      w h * Ψ^n(fH) h = w h * ∑ c : ConjClasses H, a c * Ψ^n((c.indicator : H → A)) h := by
        rw [hEval]
      _ = ∑ c : ConjClasses H, w h * (a c * Ψ^n((c.indicator : H → A)) h) := by
        rw [Finset.mul_sum]
      _ = ∑ c : ConjClasses H, a c * (w h * Ψ^n((c.indicator : H → A)) h) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        ring
  -- This is the promised pointwise rewrite of the restricted weighted Adams transform.
  calc
    (weightedAdamsClassFunction (A := A) n f : G → ℂ) h
        = algebraMap A ℂ (w h * Ψ^n(fH) h) := by
            simp [weightedAdamsClassFunction, Representation.adamsOperator, fH,
              subgroupClassFunctionRestriction, w]
    _ = ∑ c : ConjClasses H, algebraMap A ℂ (a c * (w h * Ψ^n((c.indicator : H → A)) h)) := by
      simpa [map_sum] using congrArg (algebraMap A ℂ) hweighted
    _ =
        (∑ c : ConjClasses H, a c •
          (fun x : H ↦
            algebraMap A ℂ
              (w x * Ψ^n((c.indicator : H → A)) x))) h := by
          simp [a, w, Algebra.smul_def, map_mul]

/-- Helper for Theorem 11-11.2-1: the conjugacy-class indicator basis vectors are the only
remaining arithmetic case in the elementary-subgroup pairing argument. -/
private theorem weighted_adams_indicator_apply_eq_orderOf_pow_of_mem
    (n : ℕ+) {H : Type w} [Group H] [Finite H] (c : ConjClasses H) (h : H)
    (hsroot : h ^ (n : ℕ) ∈ c.carrier) :
    algebraMap A ℂ
        ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
          Ψ^n((c.indicator : H → A)) h) =
      algebraMap A ℂ (((orderOf (h ^ (n : ℕ))) : ℕ) : A) := by
  -- On the root fiber of `c`, the indicator contributes `1` and the Frobenius weight becomes
  -- `orderOf (h ^ n)`.
  have hweight : orderOf h / Nat.gcd (orderOf h) (n : ℕ) = orderOf (h ^ (n : ℕ)) := by
    symm
    simpa using (orderOf_pow (n := (n : ℕ)) h)
  simp [Representation.adamsOperator, ConjClasses.indicator, hsroot, hweight]

/-- Helper for Theorem 11-11.2-1: the weighted indicator vanishes away from the `n`th-power fiber
of the chosen conjugacy class. -/
private theorem weighted_adams_indicator_apply_eq_zero_of_not_mem
    (n : ℕ+) {H : Type w} [Group H] [Finite H] (c : ConjClasses H) (h : H)
    (hsroot : h ^ (n : ℕ) ∉ c.carrier) :
    algebraMap A ℂ
        ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
          Ψ^n((c.indicator : H → A)) h) =
      0 := by
  -- Outside the root fiber, the indicator factor is already zero.
  simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]

/-- Helper for Theorem 11-11.2-1: the conjugacy-class indicator basis vectors are the only
remaining arithmetic case in the elementary-subgroup pairing argument. -/
private theorem weighted_adams_indicator_apply_eq_if
    (n : ℕ+) {H : Type w} [Group H] [Finite H] (c : ConjClasses H) (h : H) :
    algebraMap A ℂ
        ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
          Ψ^n((c.indicator : H → A)) h) =
      algebraMap A ℂ
        ((((orderOf (h ^ (n : ℕ))) : ℕ) : A) * c.indicator (h ^ (n : ℕ))) := by
  -- The weighted indicator is supported exactly on the `n`th-power preimage of `c`, and on that
  -- support the Frobenius weight is the order of `h ^ n`.
  by_cases hsroot : h ^ (n : ℕ) ∈ c.carrier
  · rw [weighted_adams_indicator_apply_eq_orderOf_pow_of_mem (A := A) n c h hsroot]
    simp [ConjClasses.indicator, hsroot]
  · rw [weighted_adams_indicator_apply_eq_zero_of_not_mem (A := A) n c h hsroot]
    simp [ConjClasses.indicator, hsroot]

/-- Helper for Theorem 11-11.2-1: a degree-`1` character on a product group factors through the
two coordinate inclusions. -/
private theorem linearCharacter_on_prod_apply_eq_mul
    {C P : Type w} [Group C] [Group P]
    (χ : C × P →* ℂˣ) (a : C) (u : P) :
    χ (a, u) = (χ.comp (MonoidHom.inl C P) a) * (χ.comp (MonoidHom.inr C P) u) := by
  -- Split the product element into the two coordinate inclusions and use multiplicativity.
  calc
    χ (a, u) = χ ((a, 1) * (1, u)) := by simp
    _ = χ (a, 1) * χ (1, u) := by rw [map_mul]
    _ = (χ.comp (MonoidHom.inl C P) a) * (χ.comp (MonoidHom.inr C P) u) := by
          rfl

/-- Helper for Theorem 11-11.2-1: transporting the weighted-indicator root fiber along an
elementary product decomposition rewrites the subgroup sum as a sum over product coordinates. -/
private theorem filtered_weighted_indicator_rootFiber_sum_eq_sum_over_elementary_product
    {H : Type w} [Group H] [Finite H] [Fintype H]
    (n : ℕ+) (c : ConjClasses H) (χ : H →* ℂˣ)
    {p : ℕ} {C P : Subgroup H} (hCP : IsPElementaryDecomposition p C P) :
    let _ : DecidablePred fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
    let _ : DecidablePred fun y : C × P ↦
        ((hCP.isComplement.prodMulEquiv hCP.commute) y : H) ^ (n : ℕ) ∈ c.carrier :=
      Classical.decPred _
    Finset.sum (Finset.univ.filter fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier)
        (fun h ↦ (χ h : ℂ)) =
      Finset.sum (Finset.univ.filter fun y : C × P ↦
          ((hCP.isComplement.prodMulEquiv hCP.commute) y : H) ^ (n : ℕ) ∈ c.carrier)
        (fun y ↦ (χ ((hCP.isComplement.prodMulEquiv hCP.commute) y) : ℂ)) := by
  let _ : DecidablePred fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
  let _ : DecidablePred fun y : C × P ↦
      ((hCP.isComplement.prodMulEquiv hCP.commute) y : H) ^ (n : ℕ) ∈ c.carrier :=
    Classical.decPred _
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  -- Rewrite the filtered fiber sum as an indicator sum, then reindex it along the product
  -- equivalence coming from the elementary decomposition.
  calc
    Finset.sum (Finset.univ.filter fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier)
        (fun h ↦ (χ h : ℂ))
      = ∑ h : H, if h ^ (n : ℕ) ∈ c.carrier then (χ h : ℂ) else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ y : C × P,
          if (e y : H) ^ (n : ℕ) ∈ c.carrier then (χ (e y) : ℂ) else 0 := by
          symm
          simpa [e] using
            Equiv.sum_comp e.toEquiv
              (fun h : H ↦ if h ^ (n : ℕ) ∈ c.carrier then (χ h : ℂ) else 0)
    _ = Finset.sum (Finset.univ.filter fun y : C × P ↦
          (e y : H) ^ (n : ℕ) ∈ c.carrier)
        (fun y ↦ (χ (e y) : ℂ)) := by
          rw [Finset.sum_filter]

/-- Helper for Theorem 11-11.2-1: an elementary group admits a cyclic-times-`p`-group
decomposition along which the relevant `n`th-root fiber sum can be reindexed. -/
private theorem exists_filtered_weighted_indicator_rootFiber_sum_reindex
    {H : Type w} [Group H] [Finite H] [Fintype H]
    (n : ℕ+) (c : ConjClasses H) (χ : H →* ℂˣ) (hH : IsElementary H) :
    ∃ (p : ℕ) (C P : Subgroup H) (hCP : IsPElementaryDecomposition p C P),
      let _ : DecidablePred fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
      let _ : DecidablePred fun y : C × P ↦
          ((hCP.isComplement.prodMulEquiv hCP.commute) y : H) ^ (n : ℕ) ∈ c.carrier :=
        Classical.decPred _
      Finset.sum (Finset.univ.filter fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier)
          (fun h ↦ (χ h : ℂ)) =
        Finset.sum (Finset.univ.filter fun y : C × P ↦
            ((hCP.isComplement.prodMulEquiv hCP.commute) y : H) ^ (n : ℕ) ∈ c.carrier)
          (fun y ↦ (χ ((hCP.isComplement.prodMulEquiv hCP.commute) y) : ℂ)) := by
  rcases hH with ⟨p, C, P, hCP⟩
  refine ⟨p, C, P, hCP, ?_⟩
  -- This is the source-faithful reduction from an elementary group to its `C × P`
  -- decomposition before the remaining p-group orbit arithmetic.
  simpa using
    filtered_weighted_indicator_rootFiber_sum_eq_sum_over_elementary_product
      (n := n) (c := c) (χ := χ) hCP

/-- Helper for Theorem 11-11.2-1: after transporting the root-fiber sum through an elementary
product decomposition, the degree-`1` character factors through the two coordinates. -/
private theorem elementary_rootfiber_sum_reindex_with_factored_character
    {H : Type w} [Group H] [Finite H] [Fintype H]
    (n : ℕ+) (c : ConjClasses H) (χ : H →* ℂˣ)
    {p : ℕ} {C P : Subgroup H} (hCP : IsPElementaryDecomposition p C P) :
    let e := hCP.isComplement.prodMulEquiv hCP.commute
    let χe : C × P →* ℂˣ := χ.comp e.toMonoidHom
    let _ : DecidablePred fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
    let _ : DecidablePred fun y : C × P ↦ ((e y : H) ^ (n : ℕ) ∈ c.carrier) :=
      Classical.decPred _
    Finset.sum (Finset.univ.filter fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier)
        (fun h ↦ (χ h : ℂ)) =
      Finset.sum (Finset.univ.filter fun y : C × P ↦ (e y : H) ^ (n : ℕ) ∈ c.carrier)
        (fun y ↦
          ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
            ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)) := by
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  let χe : C × P →* ℂˣ := χ.comp e.toMonoidHom
  let _ : DecidablePred fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
  let _ : DecidablePred fun y : C × P ↦ ((e y : H) ^ (n : ℕ) ∈ c.carrier) :=
    Classical.decPred _
  -- First put the statement into the explicit sum form hidden behind the theorem-local `let`s.
  dsimp
  -- First reindex the filtered root-fiber sum along the elementary product decomposition.
  rw [filtered_weighted_indicator_rootFiber_sum_eq_sum_over_elementary_product
    (n := n) (c := c) (χ := χ) hCP]
  -- Then factor the transported linear character through the two coordinate inclusions.
  refine Finset.sum_congr rfl ?_
  intro y hy
  simpa [e, χe] using
    congrArg (fun z : ℂˣ ↦ (z : ℂ))
      (linearCharacter_on_prod_apply_eq_mul (χ := χe) y.1 y.2)

/-- Helper for Theorem 11-11.2-1: the same elementary reindexing works for the inverse character
summand `χ(s⁻¹)` once the source route is rewritten through `χ⁻¹`. -/
private theorem elementary_inverse_rootfiber_sum_reindex_local
    {H : Type w} [Group H] [Finite H] [Fintype H]
    (n : ℕ+) (c : ConjClasses H) (χ : H →* ℂˣ)
    {p : ℕ} {C P : Subgroup H} (hCP : IsPElementaryDecomposition p C P) :
    let e := hCP.isComplement.prodMulEquiv hCP.commute
    let χe : C × P →* ℂˣ := (χ.comp e.toMonoidHom)⁻¹
    let _ : DecidablePred fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
    let _ : DecidablePred fun y : C × P ↦ ((e y : H) ^ (n : ℕ) ∈ c.carrier) :=
      Classical.decPred _
    ∑ h : H, (if h ^ (n : ℕ) ∈ c.carrier then (χ h⁻¹ : ℂ) else 0 : ℂ) =
      ∑ y : C × P,
        (if (e y : H) ^ (n : ℕ) ∈ c.carrier then
          ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
            ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)
        else 0 : ℂ) := by
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  let χinv : H →* ℂˣ := χ⁻¹
  let χe : C × P →* ℂˣ := (χ.comp e.toMonoidHom)⁻¹
  let _ : DecidablePred fun h : H ↦ h ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
  let _ : DecidablePred fun y : C × P ↦ ((e y : H) ^ (n : ℕ) ∈ c.carrier) :=
    Classical.decPred _
  -- Route correction: reindex the total `if`-sum directly along the product equivalence and then
  -- factor the transported inverse character through the two coordinates.
  calc
    ∑ h : H, (if h ^ (n : ℕ) ∈ c.carrier then (χ h⁻¹ : ℂ) else 0 : ℂ)
        = ∑ h : H, (if h ^ (n : ℕ) ∈ c.carrier then (χinv h : ℂ) else 0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            simp [χinv]
    _ = ∑ y : C × P,
          if (e y : H) ^ (n : ℕ) ∈ c.carrier then (((χinv.comp e.toMonoidHom) y : ℂˣ) : ℂ)
          else 0 := by
            simpa [e] using
              (Equiv.sum_comp e.toEquiv
                (fun h : H ↦ if h ^ (n : ℕ) ∈ c.carrier then (χinv h : ℂ) else 0)).symm
    _ = ∑ y : C × P,
          (if (e y : H) ^ (n : ℕ) ∈ c.carrier then
            ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
              ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)
          else 0 : ℂ) := by
            -- On the support, the transported inverse character splits through the two
            -- coordinate inclusions of `C × P`.
            refine Finset.sum_congr rfl ?_
            intro y hy
            by_cases hyroot : (e y : H) ^ (n : ℕ) ∈ c.carrier
            · have hχe :
                (((χinv.comp e.toMonoidHom) y : ℂˣ) : ℂ) = (χe y : ℂ) := by
                  simp [χinv, χe, e]
              rw [hχe]
              simp [hyroot]
              exact congrArg (fun z : ℂˣ ↦ (z : ℂ))
                (linearCharacter_on_prod_apply_eq_mul (χ := χe) y.1 y.2)
            · simp [hyroot]

/-- Helper for Theorem 11-11.2-1: the elementary-subgroup basis pairing rewrites as the normalized
`n`th-root sum over the chosen conjugacy class. -/
private theorem weighted_adams_indicator_pairing_eq_root_sum
    [Finite G] (n : ℕ+) (H : Subgroup G) (χ : H →* ℂˣ) (c : ConjClasses H) :
    ⟪χ.toCharacterRing,
      fun h : H ↦
        algebraMap A ℂ
          ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
            Ψ^n((c.indicator : H → A)) h)⟫ =
      (Nat.card H : ℂ)⁻¹ *
        ∑ s : H,
          algebraMap A ℂ
              ((((orderOf (s ^ (n : ℕ))) : ℕ) : A) * c.indicator (s ^ (n : ℕ))) *
            (χ s⁻¹ : ℂ) := by
  -- Rewrite the pairing so the weighted indicator is evaluated directly at `s`, then collapse its
  -- values to the root-fiber formula from `weighted_adams_indicator_apply_eq_if`.
  rw [Representation.groupFunctionPairing_comm]
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  refine congrArg (fun x : ℂ ↦ (Nat.card H : ℂ)⁻¹ * x) ?_
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [weighted_adams_indicator_apply_eq_if (A := A) n c s]
  simp [MonoidHom.toCharacterRing_apply]

/-- Helper for Theorem 11-11.2-1: the weighted-indicator pairing may be rewritten as a normalized
root-sum whose summand is supported exactly on the `n`th-root fiber of the chosen conjugacy
class. -/
private theorem weighted_adams_indicator_pairing_eq_root_sum_if
    [Finite G] (n : ℕ+) (H : Subgroup G) (χ : H →* ℂˣ) (c : ConjClasses H) :
    let _ : DecidablePred fun s : H ↦ s ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
    ⟪χ.toCharacterRing,
      fun h : H ↦
        algebraMap A ℂ
          ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
            Ψ^n((c.indicator : H → A)) h)⟫ =
      (Nat.card H : ℂ)⁻¹ *
        ∑ s : H,
          if s ^ (n : ℕ) ∈ c.carrier then
            algebraMap A ℂ (((orderOf (s ^ (n : ℕ))) : ℕ) : A) * (χ s⁻¹ : ℂ)
          else 0 := by
  let _ : DecidablePred fun s : H ↦ s ^ (n : ℕ) ∈ c.carrier := Classical.decPred _
  -- First rewrite the pairing as the unrestricted root sum from the previous helper.
  rw [weighted_adams_indicator_pairing_eq_root_sum (A := A) n H χ c]
  refine congrArg (fun z : ℂ ↦ (Nat.card H : ℂ)⁻¹ * z) ?_
  -- The indicator kills exactly the terms away from the root fiber.
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsroot : s ^ (n : ℕ) ∈ c.carrier
  · simp [ConjClasses.indicator, hsroot]
  · simp [ConjClasses.indicator, hsroot]

/-- Helper for Theorem 11-11.2-1: elements in the same conjugacy class have the same order. -/
private theorem orderOf_eq_of_mem_conjClass_local
    {H : Type w} [Group H] [Finite H] {c : ConjClasses H} (g : c.carrier) {x : H}
    (hx : x ∈ c.carrier) :
    orderOf x = orderOf (g : H) := by
  have hxmk : ConjClasses.mk x = c := ConjClasses.mem_carrier_iff_mk_eq.mp hx
  have hgmk : ConjClasses.mk (g : H) = c := ConjClasses.mem_carrier_iff_mk_eq.mp g.property
  have hconj : ConjClasses.mk x = ConjClasses.mk (g : H) := hxmk.trans hgmk.symm
  rcases ConjClasses.mk_eq_mk_iff_isConj.mp hconj with ⟨a, ha⟩
  simpa using SemiconjBy.orderOf_eq (a := (a : H)) ha

/-- Helper for Theorem 11-11.2-1: on a nonempty `n`th-root fiber of a fixed conjugacy class, the
weighted-indicator pairing reduces to the class order times the normalized root-fiber character
sum. -/
private theorem weighted_adams_indicator_pairing_eq_class_order_root_sum
    {H : Type w} [Group H] [Finite H]
    (n : ℕ+) (χ : H →* ℂˣ) (d : ConjClasses H) (g : d.carrier) :
    let _ : DecidablePred fun s : H ↦ s ^ (n : ℕ) ∈ d.carrier := Classical.decPred _
    ⟪χ.toCharacterRing,
      fun h : H ↦
        algebraMap A ℂ
          ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
            Ψ^n((d.indicator : H → A)) h)⟫ =
      algebraMap A ℂ (((orderOf (g : H) : ℕ) : A)) *
        ((Nat.card H : ℂ)⁻¹ *
          ∑ s : H,
            if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) := by
  let _ : DecidablePred fun s : H ↦ s ^ (n : ℕ) ∈ d.carrier := Classical.decPred _
  let c : ℂ := algebraMap A ℂ (((orderOf (g : H) : ℕ) : A))
  -- Rewrite the pairing as a normalized sum over the `n`th-root fiber of `d`.
  rw [Representation.groupFunctionPairing_comm]
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  simpa [MonoidHom.toCharacterRing_apply] using
    (calc
      (Nat.card H : ℂ)⁻¹ *
          ∑ s : H,
            (algebraMap A ℂ
                ((((orderOf s / Nat.gcd (orderOf s) (n : ℕ)) : ℕ) : A) *
                  Ψ^n((d.indicator : H → A)) s)) * (χ s⁻¹ : ℂ)
        =
          (Nat.card H : ℂ)⁻¹ *
            ∑ s : H,
              if s ^ (n : ℕ) ∈ d.carrier then
                algebraMap A ℂ (((orderOf (s ^ (n : ℕ)) : ℕ) : A)) * (χ s⁻¹ : ℂ)
              else 0 := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro s hs
                by_cases hsroot : s ^ (n : ℕ) ∈ d.carrier
                · rw [weighted_adams_indicator_apply_eq_orderOf_pow_of_mem (A := A) n d s hsroot]
                  simp [hsroot, mul_assoc]
                · rw [weighted_adams_indicator_apply_eq_zero_of_not_mem (A := A) n d s hsroot]
                  simp [hsroot]
      _ =
          (Nat.card H : ℂ)⁻¹ *
            ∑ s : H,
              if s ^ (n : ℕ) ∈ d.carrier then c * (χ s⁻¹ : ℂ) else 0 := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro s hs
                by_cases hsroot : s ^ (n : ℕ) ∈ d.carrier
                · have hord : orderOf (s ^ (n : ℕ)) = orderOf (g : H) :=
                    orderOf_eq_of_mem_conjClass_local (g := g) hsroot
                  simp [c, hsroot, hord]
                · simp [hsroot]
      _ =
          (Nat.card H : ℂ)⁻¹ *
            (c * ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) := by
              congr 1
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro s hs
              by_cases hsroot : s ^ (n : ℕ) ∈ d.carrier <;> simp [hsroot]
      _ =
          c *
            ((Nat.card H : ℂ)⁻¹ *
              ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) := by
                ring
      _ =
          algebraMap A ℂ (((orderOf (g : H) : ℕ) : A)) *
            ((Nat.card H : ℂ)⁻¹ *
              ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) := by
                rfl)

/-- Helper for Theorem 11-11.2-1: a nontrivial degree-`1` character on a finite group has total
sum `0`. -/
private theorem sum_linearCharacter_eq_zero_of_ne_one_local
    {H : Type w} [Group H] [Finite H] (χ : H →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ x : H, (χ x : ℂ) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : H, χ g ≠ 1 := by
    by_contra hnot
    apply hχ
    ext x
    have hx : χ x = 1 := by
      by_contra hx
      exact hnot ⟨x, hx⟩
    simpa using congrArg (fun u : ℂˣ ↦ (u : ℂ)) hx
  let s : ℂ := ∑ x : H, (χ x : ℂ)
  have htranslate : (χ g : ℂ) * s = s := by
    -- Left translation permutes the finite group, so multiplying each term by `χ g` preserves
    -- the total sum.
    calc
      (χ g : ℂ) * s = ∑ x : H, (χ g : ℂ) * (χ x : ℂ) := by
        simpa [s] using Finset.mul_sum (Finset.univ) (fun x : H ↦ (χ x : ℂ)) (χ g : ℂ)
      _ = ∑ x : H, (χ (g * x) : ℂ) := by
        exact Fintype.sum_congr
          (fun x : H ↦ (χ g : ℂ) * (χ x : ℂ))
          (fun x : H ↦ (χ (g * x) : ℂ))
          (fun x ↦ by simp [map_mul])
      _ = s := by
        simpa [s] using Equiv.sum_comp (Equiv.mulLeft g) (fun x : H ↦ (χ x : ℂ))
  have hgC : (χ g : ℂ) ≠ 1 := by
    intro hgC
    apply hg
    ext
    simpa using hgC
  have hfactor : ((χ g : ℂ) - 1) * s = 0 := by
    calc
      ((χ g : ℂ) - 1) * s = (χ g : ℂ) * s - s := by ring
      _ = s - s := by rw [htranslate]
      _ = 0 := sub_self s
  have hs : s = 0 := by
    refine (mul_eq_zero.mp hfactor).resolve_left ?_
    exact sub_ne_zero.mpr hgC
  simpa [s] using hs

/-- Helper for Theorem 11-11.2-1: in a commutative group, the `n`th-power fiber above `a0 ^ n`
is a translate of the kernel of `powMonoidHom n`. -/
private theorem cyclic_rootfiber_eq_powKer_translate_local
    {C : Type w} [CommGroup C] (n : ℕ) (a a0 : C) :
    a ^ n = a0 ^ n ↔ ∃ k : (powMonoidHom n : C →* C).ker, a = a0 * k := by
  constructor
  · intro ha
    -- Rewrite the fiber equation by translating `a` back by `a0⁻¹`, which lands in the kernel.
    refine ⟨⟨a0⁻¹ * a, ?_⟩, ?_⟩
    · change (powMonoidHom n : C →* C) (a0⁻¹ * a) = 1
      calc
        (powMonoidHom n : C →* C) (a0⁻¹ * a) = (a0⁻¹ * a) ^ n := rfl
        _ = (a0⁻¹) ^ n * a ^ n := by
              rw [mul_pow]
        _ = (a0 ^ n)⁻¹ * a ^ n := by
              simp
        _ = 1 := by
              simp [ha]
    · simp
  · rintro ⟨k, rfl⟩
    -- Conversely, translating a kernel element by `a0` preserves the same `n`th power.
    have hk1 : (k : C) ^ n = 1 := by
      change (powMonoidHom n : C →* C) k = 1
      exact k.2
    calc
      (a0 * (k : C)) ^ n = a0 ^ n * (k : C) ^ n := by
        rw [mul_pow]
      _ = a0 ^ n := by
            simp [hk1]

/-- Helper for Theorem 11-11.2-1: the value of a linear character on a finite group lies in the
image of `A` once the ambient roots-of-unity hypothesis is available. -/
private theorem linear_character_value_mem_range_of_roots_hypothesis_local
    {H : Type w} [Group H] [Finite H] (χ : H →* ℂˣ) (h : H)
    (hrootsH : ∀ z : ℂˣ, z ^ Nat.card H = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ((χ h : ℂ) ∈ Set.range (algebraMap A ℂ)) := by
  -- The character value has finite order dividing `|H|`, so it is one of the roots controlled by
  -- the source hypothesis.
  apply hrootsH (χ h)
  have hdiv : orderOf h ∣ Nat.card H := by
    simpa using (orderOf_dvd_natCard h)
  rcases hdiv with ⟨m, hm⟩
  rw [hm, pow_mul]
  have hpow_order : (χ h) ^ orderOf h = 1 := by
    -- The linear character sends the order relation of `h` to the same order relation in `ℂˣ`.
    have hpow_image : χ (h ^ orderOf h) = 1 := by
      simpa using congrArg χ (pow_orderOf_eq_one h)
    calc
      (χ h) ^ orderOf h = χ (h ^ orderOf h) := by
        symm
        exact map_pow χ h (orderOf h)
      _ = 1 := hpow_image
  simp [hpow_order]

/-- Helper for Theorem 11-11.2-1: on a finite cyclic group, the subgroup-gcd-normalized inverse
`n`th-power fiber sum of a degree-`1` character already lands in the image of `A`. -/
private theorem cyclic_inverse_rootfiber_sum_mem_range_local
    {C : Type w} [Group C] [Finite C] [DecidableEq C] (hC : IsCyclic C)
    (n : ℕ+) (χ : C →* ℂˣ) (a0 : C)
    (hrootsC : ∀ z : ℂˣ, z ^ Nat.card C = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    (((Nat.gcd (Nat.card C) (n : ℕ) : ℂ)⁻¹) *
        Finset.sum (Finset.univ.filter fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ))
          fun a ↦ (χ a⁻¹ : ℂ)) ∈
      Set.range (algebraMap A ℂ) := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  let _ : CommGroup C := hC.commGroup
  let K : Subgroup C := (powMonoidHom (n : ℕ) : C →* C).ker
  let _ : Finite K := Finite.of_injective ((↑) : K → C) Subtype.val_injective
  let _ : Fintype K := Fintype.ofFinite K
  let χinv : C →* ℂˣ := χ⁻¹
  -- Reindex the filtered fiber through the translate of the power-map kernel.
  have hsum_subtype :
      Finset.sum (Finset.univ.filter fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ))
          (fun a ↦ (χ a⁻¹ : ℂ)) =
        Finset.sum (Finset.univ.subtype fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ))
          (fun a ↦ (χ a⁻¹ : ℂ)) := by
    simpa using
      (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ)) (f := fun a ↦ (χ a⁻¹ : ℂ))).symm
  let eFiber : K ≃ {a : C // a ^ (n : ℕ) = a0 ^ (n : ℕ)} :=
    { toFun := fun k ↦ ⟨a0 * k, by
        have hk1 : (k : C) ^ (n : ℕ) = 1 := by
          change (powMonoidHom (n : ℕ) : C →* C) k = 1
          exact k.2
        calc
          (a0 * k) ^ (n : ℕ) = a0 ^ (n : ℕ) * (k : C) ^ (n : ℕ) := by
            rw [mul_pow]
          _ = a0 ^ (n : ℕ) := by
                simp [hk1]
      ⟩
      invFun := fun a ↦ ⟨a0⁻¹ * a, by
        -- Translating back by `a0⁻¹` lands in the kernel because the two `n`th powers agree.
        change (powMonoidHom (n : ℕ) : C →* C) (a0⁻¹ * a) = 1
        calc
          (powMonoidHom (n : ℕ) : C →* C) (a0⁻¹ * a) = (a0⁻¹ * a) ^ (n : ℕ) := rfl
          _ = (a0⁻¹) ^ (n : ℕ) * a ^ (n : ℕ) := by
                rw [mul_pow]
          _ = (a0 ^ (n : ℕ))⁻¹ * a ^ (n : ℕ) := by
                simp
          _ = 1 := by
                simp [a.property]
      ⟩
      left_inv := by
        intro k
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp [mul_comm] }
  have hsum_equiv :
      Finset.sum (Finset.univ.subtype fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ))
          (fun a ↦ (χ a⁻¹ : ℂ)) =
        ∑ k : K, (χinv (a0 * k : C) : ℂ) := by
    simpa [χinv, eFiber] using
      (Fintype.sum_equiv eFiber.symm
        (fun a : {a : C // a ^ (n : ℕ) = a0 ^ (n : ℕ)} ↦ (χ a⁻¹ : ℂ))
        (fun k : K ↦ (χinv (a0 * k : C) : ℂ))
        (by
          intro a
          simp [χinv, eFiber, mul_comm]))
  let χK : K →* ℂˣ := χinv.comp K.subtype
  have hsum_translate :
      (∑ k : K, (χinv (a0 * k : C) : ℂ)) = (χinv a0 : ℂ) * ∑ k : K, (χK k : ℂ) := by
    -- Factor the translated inverse character sum into the value at `a0` times the kernel sum.
    calc
      (∑ k : K, (χinv (a0 * k : C) : ℂ)) = ∑ k : K, (χinv a0 : ℂ) * (χK k : ℂ) := by
        apply Fintype.sum_congr
        intro k
        simp [χK, χinv, map_mul]
      _ = (χinv a0 : ℂ) * ∑ k : K, (χK k : ℂ) := by
            simpa using
              (Finset.mul_sum Finset.univ (fun k : K ↦ (χK k : ℂ)) (χinv a0 : ℂ)).symm
  by_cases hχK : χK = 1
  · -- If the restriction to the kernel is trivial, the normalized fiber sum collapses to
    -- the inverse character value at `a0`.
    have hsumK : ∑ k : K, (χK k : ℂ) = Nat.card K := by
      rw [hχK]
      simp [Nat.card_eq_fintype_card]
    have hcardK : Nat.card K = Nat.gcd (Nat.card C) (n : ℕ) := by
      simpa [K] using IsCyclic.card_powMonoidHom_ker (G := C) (d := (n : ℕ))
    have hvalue_mem : (χinv a0 : ℂ) ∈ Set.range (algebraMap A ℂ) := by
      simpa [χinv] using
        linear_character_value_mem_range_of_roots_hypothesis_local
          (A := A) χ a0⁻¹ hrootsC
    rw [hsum_subtype, hsum_equiv, hsum_translate, hsumK, hcardK]
    have hmain :
        ((Nat.gcd (Nat.card C) (n : ℕ) : ℂ)⁻¹) *
            ((χinv a0 : ℂ) * (Nat.gcd (Nat.card C) (n : ℕ) : ℂ)) =
          (χinv a0 : ℂ) := by
      calc
        ((Nat.gcd (Nat.card C) (n : ℕ) : ℂ)⁻¹) *
            ((χinv a0 : ℂ) * (Nat.gcd (Nat.card C) (n : ℕ) : ℂ)) =
          (((Nat.gcd (Nat.card C) (n : ℕ) : ℂ)⁻¹) *
              (Nat.gcd (Nat.card C) (n : ℕ) : ℂ)) * (χinv a0 : ℂ) := by
                ring
        _ = (χinv a0 : ℂ) := by
              simp
    rw [hmain]
    exact hvalue_mem
  · -- If the restriction to the kernel is nontrivial, the translated kernel sum vanishes.
    have hsumK : ∑ k : K, (χK k : ℂ) = 0 :=
      sum_linearCharacter_eq_zero_of_ne_one_local χK hχK
    rw [hsum_subtype, hsum_equiv, hsum_translate, hsumK]
    exact ⟨0, by simp⟩

/-- Helper for Theorem 11-11.2-1: after the elementary `C × P` rewrite, the inverse-character
root-fiber sum factors into independent cyclic and `p`-group sums. -/
private theorem elementary_inverse_rootfiber_sum_factor_local
    {C : Type w} {P : Type*} [CommGroup C] [Group P] [Fintype C] [Fintype P]
    (n : ℕ+) (χC : C →* ℂˣ) (χP : P →* ℂˣ) (a0 : C) (dP : ConjClasses P) :
    let _ : DecidablePred fun y : C × P ↦
      y.1 ^ (n : ℕ) = a0 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier := Classical.decPred _
    let _ : DecidablePred fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ) := Classical.decPred _
    let _ : DecidablePred fun u : P ↦ u ^ (n : ℕ) ∈ dP.carrier := Classical.decPred _
    ∑ y : C × P,
      (if y.1 ^ (n : ℕ) = a0 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier then
        ((χC y.1 : ℂˣ) : ℂ) * ((χP y.2 : ℂˣ) : ℂ)
      else 0 : ℂ) =
      (∑ a : C, (if a ^ (n : ℕ) = a0 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) else 0 : ℂ)) *
        (∑ u : P, (if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0 : ℂ)) := by
  let _ : DecidablePred fun y : C × P ↦
      y.1 ^ (n : ℕ) = a0 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier := Classical.decPred _
  let _ : DecidablePred fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ) := Classical.decPred _
  let _ : DecidablePred fun u : P ↦ u ^ (n : ℕ) ∈ dP.carrier := Classical.decPred _
  let sP : ℂ :=
    ∑ u : P, (if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0 : ℂ)
  -- Rewrite the product-type sum as an iterated sum and separate the conjunction into the
  -- cyclic factor and the `P`-factor.
  calc
    ∑ y : C × P,
        (if y.1 ^ (n : ℕ) = a0 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier then
          ((χC y.1 : ℂˣ) : ℂ) * ((χP y.2 : ℂˣ) : ℂ)
        else 0 : ℂ)
      = ∑ a : C, ∑ u : P,
          (if a ^ (n : ℕ) = a0 ^ (n : ℕ) ∧ u ^ (n : ℕ) ∈ dP.carrier then
            ((χC a : ℂˣ) : ℂ) * ((χP u : ℂˣ) : ℂ)
          else 0 : ℂ) := by
            simp [Fintype.sum_prod_type]
    _ = ∑ a : C, (if a ^ (n : ℕ) = a0 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) * sP else 0 : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          by_cases ha0 : a ^ (n : ℕ) = a0 ^ (n : ℕ)
          · calc
              ∑ u : P,
                  (if a ^ (n : ℕ) = a0 ^ (n : ℕ) ∧ u ^ (n : ℕ) ∈ dP.carrier then
                    ((χC a : ℂˣ) : ℂ) * ((χP u : ℂˣ) : ℂ)
                  else 0 : ℂ)
                = ∑ u : P,
                    (if u ^ (n : ℕ) ∈ dP.carrier then
                      ((χC a : ℂˣ) : ℂ) * ((χP u : ℂˣ) : ℂ)
                    else 0 : ℂ) := by
                      refine Finset.sum_congr rfl ?_
                      intro u hu
                      simp [ha0, and_left_comm, and_assoc]
              _ = ∑ u : P,
                    ((χC a : ℂˣ) : ℂ) *
                      (if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0 : ℂ) := by
                        refine Finset.sum_congr rfl ?_
                        intro u hu
                        by_cases hu0 : u ^ (n : ℕ) ∈ dP.carrier <;> simp [hu0]
              _ = ((χC a : ℂˣ) : ℂ) * sP := by
                    rw [Finset.mul_sum]
              _ = (if a ^ (n : ℕ) = a0 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) * sP else 0 : ℂ) := by
                    simp [ha0]
          · simp [ha0]
    _ = ∑ a : C,
          ((if a ^ (n : ℕ) = a0 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) else 0 : ℂ) * sP) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            by_cases ha0 : a ^ (n : ℕ) = a0 ^ (n : ℕ) <;> simp [ha0]
    _ = (∑ a : C, (if a ^ (n : ℕ) = a0 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) else 0 : ℂ)) * sP := by
          rw [Finset.sum_mul]
    _ =
        (∑ a : C, (if a ^ (n : ℕ) = a0 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) else 0 : ℂ)) *
          (∑ u : P, (if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0 : ℂ)) := by
            rfl

/-- Helper for Theorem 11-11.2-1: pairing an integral virtual character with a degree-`1`
character lands in the image of `ℤ`. -/
private theorem pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
    {H : Type w} [Group H] [Finite H] (η : R(H)) (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing, (η : H → ℂ)⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
  let S : Set (H → ℂ) :=
    { ψ |
        ∃ (X : Type w) (_ : AddCommGroup X) (_ : Module ℂ X)
          (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
          ψ = σ.character }
  have hmul_span :
      ∀ {f g : H → ℂ},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hfg : ∀ g : H → ℂ, g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          have hψ' :
              ∃ (X : Type w) (_ : AddCommGroup X) (_ : Module ℂ X)
                (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
                ψ = σ.character := by
            simpa [S] using hψ
          rcases hψ' with ⟨X, _instXAdd, _instXMod, _instXfd, σ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              have hξ' :
                  ∃ (Y : Type w) (_ : AddCommGroup Y) (_ : Module ℂ Y)
                    (_ : FiniteDimensional ℂ Y) (τ : Representation ℂ H Y),
                    ξ = τ.character := by
                simpa [S] using hξ
              rcases hξ' with ⟨Y, _instYAdd, _instYMod, _instYfd, τ, rfl⟩
              let π : Representation ℂ H (TensorProduct ℂ X Y) := σ.tprod τ
              -- Tensor products realize pointwise products of honest characters.
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct ℂ X Y, inferInstance, inferInstance, inferInstance, π, ?_⟩
              change σ.character * τ.character = (σ.tprod τ).character
              exact (Representation.char_tensor (ρ := σ) (σ := τ)).symm
          | zero =>
              have hzero_mul : σ.character * (0 : H → ℂ) = 0 := by
                ext x
                simp
              rw [hzero_mul]
              exact
                (Submodule.zero_mem (Submodule.span ℤ S) : (0 : H → ℂ) ∈ Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              have hmul_zsmul : σ.character * (n • ξ) = n • (σ.character * ξ) := by
                ext x
                simp [zsmul_eq_mul, mul_left_comm]
              rw [hmul_zsmul]
              exact Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          have hzero_mul : (0 : H → ℂ) * g = 0 := by
            ext x
            simp
          rw [hzero_mul]
          exact (Submodule.zero_mem (Submodule.span ℤ S) : (0 : H → ℂ) ∈ Submodule.span ℤ S)
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  have hηspan : (η : H → ℂ) ∈ Submodule.span ℤ S := by
    -- Reduce the bundled character ring element to the `ℤ`-span of honest characters.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ η.2
    · intro ψ hψ
      rcases hψ with ⟨σ, hσfd, _hσirr, rfl⟩
      exact Submodule.subset_span
        ⟨(σ : Type w), inferInstance, inferInstance, hσfd, σ.ρ, rfl⟩
    · intro n
      have htriv :
          (Representation.trivial ℂ H (ULift.{w} ℂ)).character = (1 : H → ℂ) := by
        ext x
        simp [Representation.character, Representation.trivial]
      have hmap :
          algebraMap ℤ (H → ℂ) n =
            n • (Representation.trivial ℂ H (ULift.{w} ℂ)).character := by
        ext x
        simp [htriv]
      rw [hmap]
      exact
        Submodule.smul_mem (Submodule.span ℤ S) n <|
          Submodule.subset_span
            ⟨ULift.{w} ℂ, inferInstance, inferInstance, inferInstance,
              Representation.trivial ℂ H (ULift.{w} ℂ), rfl⟩
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  -- Commute the pairing so the `ℤ`-span induction hits the integral character input.
  rw [Representation.groupFunctionPairing_comm]
  have hpair_span :
      ∀ f : H → ℂ, f ∈ Submodule.span ℤ S →
        ⟪f, χ.toCharacterRing⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem ψ hψ =>
        have hψ' :
            ∃ (X : Type w) (_ : AddCommGroup X) (_ : Module ℂ X)
              (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
              ψ = σ.character := by
          simpa [S] using hψ
        rcases hψ' with ⟨X, _instXAdd, _instXMod, _instXfd, σ, rfl⟩
        have hcard_ne : (Nat.card H : ℂ) ≠ 0 := by
          exact_mod_cast Nat.card_pos.ne'
        letI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard_ne
        have hpair :
            ⟪σ.character, χ.toCharacterRing⟫ =
              Module.finrank ℂ (σ.IntertwiningMap χ.toRepresentation) := by
          simpa [MonoidHom.toCharacterRing_apply] using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              (K := ℂ) σ χ.toRepresentation)
        refine ⟨(Module.finrank ℂ (σ.IntertwiningMap χ.toRepresentation) : ℤ), ?_⟩
        simpa using hpair.symm
    | zero =>
        refine ⟨0, ?_⟩
        simp [Representation.groupFunctionPairingOverField]
    | add ψ ξ _ _ hψ hξ =>
        rcases hψ with ⟨a, ha⟩
        rcases hξ with ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        calc
          algebraMap ℤ ℂ (a + b) = algebraMap ℤ ℂ a + algebraMap ℤ ℂ b := by simp
          _ = groupFunctionPairingOverField ℂ ψ (χ.toCharacterRing : H → ℂ) +
                groupFunctionPairingOverField ℂ ξ (χ.toCharacterRing : H → ℂ) := by
              rw [ha, hb]
          _ = groupFunctionPairingOverField ℂ (ψ + ξ) (χ.toCharacterRing : H → ℂ) := by
              rw [Representation.groupFunctionPairing_add_left]
    | smul n ψ _ hψ =>
        rcases hψ with ⟨a, ha⟩
        refine ⟨n * a, ?_⟩
        calc
          algebraMap ℤ ℂ (n * a) = (n : ℂ) * algebraMap ℤ ℂ a := by
            simp [map_mul, mul_comm]
          _ = (n : ℂ) * groupFunctionPairingOverField ℂ ψ (χ.toCharacterRing : H → ℂ) := by
              rw [ha]
          _ = groupFunctionPairingOverField ℂ (n • ψ) (χ.toCharacterRing : H → ℂ) := by
              symm
              simpa [zsmul_eq_mul] using
                (Representation.groupFunctionPairing_smul_left
                  (a := (n : ℂ)) (φ := ψ) (ψ := (χ.toCharacterRing : H → ℂ)))
  exact hpair_span (η : H → ℂ) hηspan

/-- Helper for Theorem 11-11.2-1: pairing any realized scalar-extension element with a
degree-`1` character lands in the image of `A`. -/
private theorem pairing_mem_range_of_mem_characterRingScalarExtension_with_linear_character
    {H : Type w} [Group H] [Finite H] {f : H → ℂ}
    (hf : f ∈ characterRingScalarExtension A H) (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing, f⟫ ∈ Set.range (algebraMap A ℂ) := by
  -- Induct over the defining `A`-span, reducing generators to the integral pairing lemma above.
  induction hf using Submodule.span_induction with
  | mem η hη =>
      let ηR : R(H) := ⟨η, hη⟩
      rcases
          pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
            (H := H) ηR χ with
        ⟨n, hn⟩
      refine ⟨(n : A), ?_⟩
      simpa [ηR] using hn
  | zero =>
      refine ⟨0, ?_⟩
      simp [Representation.groupFunctionPairingOverField]
  | add f g _ _ hf hg =>
      rcases hf with ⟨a, ha⟩
      rcases hg with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      calc
        algebraMap A ℂ (a + b) = algebraMap A ℂ a + algebraMap A ℂ b := by
          simp [map_add]
        _ = ⟪χ.toCharacterRing, f⟫ + ⟪χ.toCharacterRing, g⟫ := by
              rw [ha, hb]
        _ = ⟪χ.toCharacterRing, f + g⟫ := by
              symm
              exact Representation.groupFunctionPairing_add_right
                (χ.toCharacterRing : H → ℂ) f g
  | smul a f _ hf =>
      rcases hf with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        algebraMap A ℂ (a * b) = algebraMap A ℂ a * algebraMap A ℂ b := by
          simp [map_mul]
        _ = algebraMap A ℂ a * ⟪χ.toCharacterRing, f⟫ := by
              rw [hb]
        _ = ⟪χ.toCharacterRing, a • f⟫ := by
              symm
              simpa [Algebra.smul_def] using
                (Representation.groupFunctionPairing_smul_right
                  (algebraMap A ℂ a) (χ.toCharacterRing : H → ℂ) f)

/-- Helper for Theorem 11-11.2-1: if each indicator basis vector on a finite subgroup contributes
an `A`-valued pairing, then any finite `A`-linear combination of those weighted indicator vectors
does as well. -/
private theorem weighted_adams_pairing_mem_range_of_indicator_expansion
    {H : Type w} [Group H] [Finite H]
    (n : ℕ+)
    (χ : H →* ℂˣ)
    (a : ConjClasses H → A)
    (hpair :
      ∀ c : ConjClasses H,
        ⟪χ.toCharacterRing,
          fun h : H ↦
            algebraMap A ℂ
              ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
                Ψ^n((c.indicator : H → A)) h)⟫ ∈
          Set.range (algebraMap A ℂ)) :
    ⟪χ.toCharacterRing,
      ∑ c : ConjClasses H,
        a c •
          (fun h : H ↦
            algebraMap A ℂ
              ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
                Ψ^n((c.indicator : H → A)) h))⟫ ∈
      Set.range (algebraMap A ℂ) := by
  classical
  let ψ : ConjClasses H → H → ℂ := fun c h ↦
    algebraMap A ℂ
      ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
        Ψ^n((c.indicator : H → A)) h)
  have huniv :
      (∑ c : ConjClasses H, a c • ψ c) =
        Finset.sum Finset.univ (fun c ↦ a c • ψ c) := by
    simp
  rw [huniv]
  let s : Finset (ConjClasses H) := Finset.univ
  change ⟪χ.toCharacterRing, Finset.sum s (fun c ↦ a c • ψ c)⟫ ∈ Set.range (algebraMap A ℂ)
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp [Representation.groupFunctionPairingOverField]
  | @insert c s hc ih =>
      have hterm :
          ⟪χ.toCharacterRing, a c • ψ c⟫ ∈ Set.range (algebraMap A ℂ) := by
        rcases hpair c with ⟨b, hb⟩
        refine ⟨a c * b, ?_⟩
        calc
          algebraMap A ℂ (a c * b) = algebraMap A ℂ (a c) * algebraMap A ℂ b := by
            simp [map_mul]
          _ = algebraMap A ℂ (a c) * ⟪χ.toCharacterRing, ψ c⟫ := by
                rw [hb]
          _ = ⟪χ.toCharacterRing, a c • ψ c⟫ := by
                symm
                simpa [Algebra.smul_def] using
                  (Representation.groupFunctionPairing_smul_right
                    (algebraMap A ℂ (a c))
                    (χ.toCharacterRing : H → ℂ)
                    (ψ c))
      rcases hterm with ⟨u, hu⟩
      rcases ih with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      calc
        algebraMap A ℂ (u + v) = algebraMap A ℂ u + algebraMap A ℂ v := by
          simp [map_add]
        _ = ⟪χ.toCharacterRing, a c • ψ c⟫ +
              ⟪χ.toCharacterRing, Finset.sum s (fun d ↦ a d • ψ d)⟫ := by
              rw [hu, hv]
        _ = ⟪χ.toCharacterRing, a c • ψ c + Finset.sum s (fun d ↦ a d • ψ d)⟫ := by
              symm
              exact Representation.groupFunctionPairing_add_right
                (χ.toCharacterRing : H → ℂ) (a c • ψ c) (Finset.sum s (fun d ↦ a d • ψ d))
        _ = ⟪χ.toCharacterRing, Finset.sum (insert c s) (fun d ↦ a d • ψ d)⟫ := by
              simp [Finset.sum_insert, hc]

/-- Helper for Theorem 11-11.2-1: once the weighted indicator basis pairings on `K` are known to
land in the image of `A`, the same holds for the restriction of the weighted Adams transform of
any `A`-valued class function on the ambient group. -/
private theorem weighted_adams_restricted_pairing_mem_range_of_indicator_basis
    {H : Type w} [Group H] [Finite H]
    (n : ℕ+) (f : classFunctionSubmodule A H) (K : Subgroup H) (χ : K →* ℂˣ)
    (hpair :
      ∀ c : ConjClasses K,
        ⟪χ.toCharacterRing,
          fun k : K ↦
            algebraMap A ℂ
              ((((orderOf k / Nat.gcd (orderOf k) (n : ℕ)) : ℕ) : A) *
                Ψ^n((c.indicator : K → A)) k)⟫ ∈
          Set.range (algebraMap A ℂ)) :
    ⟪χ.toCharacterRing,
      fun k : K ↦ (weightedAdamsClassFunction (G := H) (A := A) n f : H → ℂ) k⟫ ∈
      Set.range (algebraMap A ℂ) := by
  let a : ConjClasses K → A :=
    fun c ↦ ((mem_classFunctionSubmodule_iff A _).1
      (subgroupClassFunctionRestriction (A := A) K f).2).lift c
  have hrestrict :
      (fun k : K ↦ (weightedAdamsClassFunction (G := H) (A := A) n f : H → ℂ) k) =
        ∑ c : ConjClasses K,
          a c •
            (fun k : K ↦
              algebraMap A ℂ
                ((((orderOf k / Nat.gcd (orderOf k) (n : ℕ)) : ℕ) : A) *
                  Ψ^n((c.indicator : K → A)) k)) := by
    -- Expand the restricted source in the indicator basis and transport the decomposition through
    -- the weighted Adams operator.
    simpa [a] using
      weighted_adams_restriction_eq_sum_conjClass_indicator (G := H) (A := A) n f K
  rw [hrestrict]
  exact weighted_adams_pairing_mem_range_of_indicator_expansion (A := A) n χ a hpair

/-- Helper for Theorem 11-11.2-1: once the arithmetic basis pairings on `K` are known, the same
specialized pairing statement holds for the weighted Adams transform of a single conjugacy-class
indicator on the ambient group. -/
private theorem weighted_adams_indicator_restricted_pairing_mem_range_of_indicator_basis
    {H : Type w} [Group H] [Finite H]
    (n : ℕ+) (c : ConjClasses H) (K : Subgroup H) (χ : K →* ℂˣ)
    (hpair :
      ∀ d : ConjClasses K,
        ⟪χ.toCharacterRing,
          fun k : K ↦
            algebraMap A ℂ
              ((((orderOf k / Nat.gcd (orderOf k) (n : ℕ)) : ℕ) : A) *
                Ψ^n((d.indicator : K → A)) k)⟫ ∈
          Set.range (algebraMap A ℂ)) :
    ⟪χ.toCharacterRing,
      fun k : K ↦
        (weightedAdamsClassFunction (G := H) (A := A) n c.indicatorClassFunctionSubmodule :
          H → ℂ) k⟫ ∈
      Set.range (algebraMap A ℂ) := by
  -- This is the indicator specialization of the general restriction-expansion lemma above.
  simpa using
    weighted_adams_restricted_pairing_mem_range_of_indicator_basis
      (H := H) (A := A) n c.indicatorClassFunctionSubmodule K χ hpair

/-- Helper for Theorem 11-11.2-1: for a subgroup `K ≤ H`, the only remaining pairing work for the
restricted weighted indicator is the basis-case arithmetic on the conjugacy classes of `K`. -/
private theorem weighted_adams_indicator_restricted_pairing_mem_range_on_subgroup
    {H : Type w} [Group H] [Finite H]
    (n : ℕ+) (c : ConjClasses H) (K : Subgroup H) (χ : K →* ℂˣ)
    (hpair :
      ∀ d : ConjClasses K,
        ⟪χ.toCharacterRing,
          fun k : K ↦
            algebraMap A ℂ
              ((((orderOf k / Nat.gcd (orderOf k) (n : ℕ)) : ℕ) : A) *
                Ψ^n((d.indicator : K → A)) k)⟫ ∈
          Set.range (algebraMap A ℂ)) :
    ⟪χ.toCharacterRing,
      fun k : K ↦
        (weightedAdamsClassFunction (G := H) (A := A) n c.indicatorClassFunctionSubmodule :
          H → ℂ) k⟫ ∈
      Set.range (algebraMap A ℂ) := by
  -- Reduce the restricted pairing to the already-proved indicator-expansion lemma on `K`.
  simpa using
    weighted_adams_indicator_restricted_pairing_mem_range_of_indicator_basis
      (H := H) (A := A) n c K χ hpair

/-- Helper for Theorem 11-11.2-1: once every elementary restriction of the weighted indicator on
`H` is realized in LinearRepresentations_Serre_1977's scalar extension, the indicator itself already lies in that scalar
extension. -/
private theorem weighted_adams_indicator_mem_characterRingScalarExtension_of_elementary_restrictions
    [Finite G] (n : ℕ+) (H : Subgroup G) (c : ConjClasses H)
    (hres : ∀ K : Subgroup H, IsElementary K →
      (fun k : K ↦
        (weightedAdamsClassFunction (G := H) (A := A) n c.indicatorClassFunctionSubmodule :
          H → ℂ) k) ∈ characterRingScalarExtension A K) :
    (fun h : H ↦
      algebraMap A ℂ
        ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
          Ψ^n((c.indicator : H → A)) h)) ∈
      characterRingScalarExtension A H := by
  -- Package the weighted indicator as a bundled class function on `H`, descend it through the
  -- local Brauer criterion, then forget back to the realized-span view.
  let φ : classFunctionSubmodule ℂ H :=
    weightedAdamsClassFunction (G := H) (A := A) n c.indicatorClassFunctionSubmodule
  obtain ⟨ψ, hψ⟩ :=
    classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups_local
      (G := H) (A := A) φ hres
  have hmem : (ψ : H → ℂ) ∈ characterRingScalarExtension A H :=
    tensorCharacterRing_mem_characterRingScalarExtension (A := A) ψ
  have hφmem : (φ : H → ℂ) ∈ characterRingScalarExtension A H := by
    simpa [hψ] using hmem
  simpa [φ, weightedAdamsClassFunction] using hφmem

/-- Helper for Theorem 11-11.2-1: the elementary subgroup pairing hypothesis transports to the
`Shrink` model used by the existing detector. -/
private theorem pairing_hypothesis_transport_to_shrink_local
    {H : Type w} [Group H] [Finite H] (φ : classFunctionSubmodule ℂ H)
    (hpair : ∀ (K : Subgroup H) (_ : IsElementary K) (χ : K →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction K φ⟫ ∈
        Set.range (algebraMap A ℂ)) :
    let H₀ := Shrink.{0} H
    let e : H₀ ≃* H := Shrink.mulEquiv
    let φ₀ : classFunctionSubmodule ℂ H₀ :=
      ⟨fun x ↦ (φ : H → ℂ) (e x), classFunction_precomp_mulEquiv_mem_local (e := e) φ⟩
    ∀ (K₀ : Subgroup H₀) (_ : IsElementary K₀) (χ₀ : K₀ →* ℂˣ),
      ⟪χ₀.toCharacterRing, Subgroup.classFunctionRestriction K₀ φ₀⟫ ∈
        Set.range (algebraMap A ℂ) := by
  classical
  dsimp
  intro K₀ hK₀ χ₀
  let e : Shrink.{0} H ≃* H := Shrink.mulEquiv
  let K : Subgroup H := K₀.map e.toMonoidHom
  let eK : K₀ ≃* K := K₀.equivMapOfInjective e.toMonoidHom e.injective
  let χ : K →* ℂˣ := χ₀.comp eK.symm.toMonoidHom
  have hK : IsElementary K := isElementary_of_mulEquiv_local eK hK₀
  have hmapped :
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction K φ⟫ ∈
        Set.range (algebraMap A ℂ) :=
    hpair K hK χ
  -- Reindex the pairing on the mapped subgroup back along the subgroup equivalence `eK`.
  have htransport :
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction K φ⟫ =
        ⟪χ₀.toCharacterRing,
          Subgroup.classFunctionRestriction K₀
            ⟨fun x : Shrink.{0} H ↦ (φ : H → ℂ) (e x),
              classFunction_precomp_mulEquiv_mem_local (e := e) φ⟩⟫ := by
    -- The restricted shrink class function is exactly the precomposition of the mapped subgroup
    -- restriction along `eK`.
    simpa [K, e, eK, χ, Subgroup.classFunctionRestriction] using
      (linear_character_pairing_precomp_mulEquiv_local
        (e := eK) (χ := χ₀) (φ := Subgroup.classFunctionRestriction K φ)).symm
  rw [← htransport]
  exact hmapped

/-- Helper for Theorem 11-11.2-1: on an elementary ambient group, if every degree-`1` pairing on
each elementary subgroup lands in the image of `A`, then the ambient class function already
belongs to the realized scalar extension. -/
private theorem elementary_classFunction_mem_characterRingScalarExtension_of_pairing_mem_range_local
    {H : Type w} [Group H] [Finite H] (hH : IsElementary H) (φ : classFunctionSubmodule ℂ H)
    (hpair : ∀ (K : Subgroup H) (_ : IsElementary K) (χ : K →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction K φ⟫ ∈
        Set.range (algebraMap A ℂ)) :
    (φ : H → ℂ) ∈ characterRingScalarExtension A H := by
  let H₀ : Type := Shrink.{0} H
  let e : H₀ ≃* H := Shrink.mulEquiv
  let φ₀ : classFunctionSubmodule ℂ H₀ :=
    ⟨fun x ↦ (φ : H → ℂ) (e x), classFunction_precomp_mulEquiv_mem_local (e := e) φ⟩
  have hpair₀ :
      ∀ (K₀ : Subgroup H₀) (_ : IsElementary K₀) (χ₀ : K₀ →* ℂˣ),
        ⟪χ₀.toCharacterRing, Subgroup.classFunctionRestriction K₀ φ₀⟫ ∈
          Set.range (algebraMap A ℂ) := by
    -- Route correction: instead of rebuilding the Chapter `11.1` basis argument at universe `w`,
    -- shrink to a small owner and transport the pairing hypothesis there.
    simpa [H₀, e, φ₀] using
      pairing_hypothesis_transport_to_shrink_local (A := A) (H := H) φ hpair
  obtain ⟨ξ₀, hξ₀⟩ :=
    classFunction_lifts_to_tensorCharacterRing_of_pairing_mem_range_on_elementary_linearCharacters
      (G := H₀) (A := A) φ₀ hpair₀
  have hmem₀ : (φ₀ : H₀ → ℂ) ∈ characterRingScalarExtension A H₀ := by
    -- The small-owner tensor witness realizes `φ₀`, so `φ₀` lies in the corresponding realized
    -- scalar extension.
    have hξmem : (ξ₀ : H₀ → ℂ) ∈ characterRingScalarExtension A H₀ :=
      tensorCharacterRing_mem_characterRingScalarExtension (A := A) ξ₀
    simpa [hξ₀] using hξmem
  have hmem :
      (fun h : H ↦ (φ₀ : H₀ → ℂ) (e.symm h)) ∈ characterRingScalarExtension A H := by
    -- Pull the realized small-owner witness back along the inverse shrink equivalence.
    exact
      mem_characterRingScalarExtension_precomp_mulEquiv_local
        (A := A) (e := e.symm) hmem₀
  simpa [H₀, e, φ₀] using hmem

/-- Helper for Theorem 11-11.2-1: on a nonempty `n`th-root fiber inside a subgroup conjugacy
class, the class order divides the corrected global Frobenius weight `|G| / gcd(|G|, n)`. -/
private theorem class_order_dvd_global_frobenius_weight_of_exists_root
    [Finite G] (n : ℕ+) (H : Subgroup G) (c : ConjClasses H) (g : c.carrier)
    (hex : ∃ h : H, h ^ (n : ℕ) ∈ c.carrier) :
    orderOf (g : H) ∣ Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) := by
  rcases hex with ⟨h, hh⟩
  let m : ℕ := orderOf h
  let g₁ : ℕ := Nat.gcd m (n : ℕ)
  let g₂ : ℕ := Nat.gcd (Nat.card G) (n : ℕ)
  have hm_cardH : m ∣ Nat.card H := by
    simpa [m] using (orderOf_dvd_natCard h)
  have hm_cardG : m ∣ Nat.card G := by
    exact dvd_trans hm_cardH (Subgroup.card_subgroup_dvd_card H)
  have hg₁_m : g₁ ∣ m := by
    exact Nat.gcd_dvd_left m (n : ℕ)
  have hg₁_g₂ : g₁ ∣ g₂ := by
    exact Nat.dvd_gcd (dvd_trans hg₁_m hm_cardG) (Nat.gcd_dvd_right m (n : ℕ))
  have hclass_order :
      orderOf (g : H) = m / g₁ := by
    calc
      orderOf (g : H) = orderOf (h ^ (n : ℕ)) := by
        symm
        exact orderOf_eq_of_mem_conjClass_local (g := g) hh
      _ = orderOf h / Nat.gcd (orderOf h) (n : ℕ) := by
        simpa using (orderOf_pow (n := (n : ℕ)) h)
      _ = m / g₁ := by
        rfl
  have hdiv_aux : m / g₁ ∣ Nat.card G / g₁ := by
    refine ⟨Nat.card G / m, ?_⟩
    -- Split the ambient group order first by the root order, then by the common gcd with `n`.
    simpa [Nat.mul_comm, m, g₁] using (Nat.div_mul_div hm_cardG hg₁_m).symm
  have hcop_base : Nat.Coprime (m / g₁) ((n : ℕ) / g₁) := by
    simpa [m, g₁] using
      Nat.gcd_div_gcd_div_gcd_of_pos_right (Nat.pos_of_ne_zero n.ne_zero)
  have hfactor_dvd : g₂ / g₁ ∣ (n : ℕ) / g₁ := by
    refine ⟨(n : ℕ) / g₂, ?_⟩
    -- The extra denominator removed from `|G|` already divides the corresponding factor of `n`.
    simpa [Nat.mul_comm, g₂, g₁] using
      (Nat.div_mul_div (Nat.gcd_dvd_right (Nat.card G) (n : ℕ)) hg₁_g₂).symm
  have hcop : Nat.Coprime (m / g₁) (g₂ / g₁) := by
    exact Nat.Coprime.of_dvd_right hfactor_dvd hcop_base
  have hprod :
      (Nat.card G / g₂) * (g₂ / g₁) = Nat.card G / g₁ := by
    -- Re-associate the ambient denominator as the class-order factor times the remaining quotient.
    simpa [g₂, g₁] using
      (Nat.div_mul_div (Nat.gcd_dvd_left (Nat.card G) (n : ℕ)) hg₁_g₂)
  have hfinal : m / g₁ ∣ Nat.card G / g₂ := by
    exact hcop.dvd_of_dvd_mul_right (hprod ▸ hdiv_aux)
  simpa [hclass_order, g₂] using hfinal

/-- Helper for Theorem 11-11.2-1: if the chosen subgroup conjugacy class has no `n`th roots, then
the corrected global weighted indicator already vanishes pointwise. -/
private theorem global_weighted_indicator_eq_zero_of_no_root
    [Finite G] (n : ℕ+) (H : Subgroup G) (d : ConjClasses H)
    (hroot : ¬ ∃ h : H, h ^ (n : ℕ) ∈ d.carrier) :
    (fun h : H ↦
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
          Ψ^n((d.indicator : H → A)) h)) = 0 := by
  -- With no `n`th roots in `d`, the Adams-transformed indicator is zero at every point.
  funext h
  have hhroot : h ^ (n : ℕ) ∉ d.carrier := by
    intro hh
    exact hroot ⟨h, hh⟩
  simp [Representation.adamsOperator, ConjClasses.indicator, hhroot]

/-- Helper for Theorem 11-11.2-1: in the nonempty-root case, the corrected global weighted
indicator is an `A`-scalar multiple of the local pointwise-weighted indicator. -/
private theorem global_weighted_indicator_eq_smul_local_weighted_indicator
    [Finite G] (n : ℕ+) (H : Subgroup G) (d : ConjClasses H) (g : d.carrier)
    (hex : ∃ h : H, h ^ (n : ℕ) ∈ d.carrier) :
    (fun h : H ↦
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
          Ψ^n((d.indicator : H → A)) h)) =
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : H)) : ℕ) : A) •
        fun h : H ↦
          algebraMap A ℂ
            ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
              Ψ^n((d.indicator : H → A)) h)) := by
  have hdiv :
      orderOf (g : H) ∣ Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) :=
    class_order_dvd_global_frobenius_weight_of_exists_root (G := G) n H d g hex
  · funext h
    by_cases hsroot : h ^ (n : ℕ) ∈ d.carrier
    · have hweight :
        orderOf h / Nat.gcd (orderOf h) (n : ℕ) = orderOf (g : H) := by
        calc
          orderOf h / Nat.gcd (orderOf h) (n : ℕ) = orderOf (h ^ (n : ℕ)) := by
            symm
            simpa using (orderOf_pow (n := (n : ℕ)) h)
          _ = orderOf (g : H) := by
            exact orderOf_eq_of_mem_conjClass_local (g := g) hsroot
      have hcoeff_nat :
          Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) =
            (Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : H)) *
              (orderOf h / Nat.gcd (orderOf h) (n : ℕ)) := by
        rw [hweight]
        exact (Nat.div_mul_cancel hdiv).symm
      have hcoeff :
          (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) : ℕ) : A)) =
            (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : H) : ℕ) : A) *
              (((orderOf h / Nat.gcd (orderOf h) (n : ℕ) : ℕ) : A))) := by
        calc
          (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) : ℕ) : A)) =
              (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : H) *
                  (orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A)) := by
                    exact congrArg (fun m : ℕ ↦ (m : A)) hcoeff_nat
          _ =
              (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : H) : ℕ) : A) *
                (((orderOf h / Nat.gcd (orderOf h) (n : ℕ) : ℕ) : A))) := by
                  simp
      have hadams : Ψ^n((d.indicator : H → A)) h = 1 := by
        simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
      -- On the root fiber, both indicators are `1`, so only the scalar comparison remains.
      rw [Pi.smul_apply, hadams, hcoeff, Algebra.smul_def]
      simp [map_mul]
    · have hadams : Ψ^n((d.indicator : H → A)) h = 0 := by
        simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
      -- Off the root fiber, the Adams-transformed indicator already vanishes on both sides.
      rw [Pi.smul_apply, hadams, Algebra.smul_def]
      simp

/-- Helper for Theorem 11-11.2-1: after restricting to a subgroup, the corrected global
Frobenius-weighted Adams transform expands in the conjugacy-class indicator basis. -/
private theorem global_weighted_adams_restriction_eq_sum_conjClass_indicator
    [Finite G] (n : ℕ+) (f : classFunctionSubmodule A G) (H : Subgroup G) :
    (fun h : H ↦ (globalWeightedAdamsClassFunction (A := A) n f : G → ℂ) h) =
      ∑ c : ConjClasses H,
        (((mem_classFunctionSubmodule_iff A _).1
          (subgroupClassFunctionRestriction (A := A) H f).2).lift c) •
          (fun h : H ↦
            algebraMap A ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
                Ψ^n((c.indicator : H → A)) h)) := by
  classical
  let fH : classFunctionSubmodule A H := subgroupClassFunctionRestriction (A := A) H f
  let a : ConjClasses H → A :=
    fun c ↦ ((mem_classFunctionSubmodule_iff A _).1 fH.2).lift c
  let k : A := (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A)
  -- Expand the restricted source class function in the indicator basis, then transport the same
  -- finite decomposition through the Adams operator and the corrected global Frobenius weight.
  funext h
  have hdecomp :
      (fH : H → A) = fun x : H ↦ ∑ c : ConjClasses H, a c * c.indicator x := by
    simpa [fH, a] using classFunction_eq_sum_conjClass_indicator (A := A) fH
  have hEval :
      Ψ^n(fH) h = ∑ c : ConjClasses H, a c * Ψ^n((c.indicator : H → A)) h := by
    simpa [Representation.adamsOperator] using
      congrArg (fun φ : H → A ↦ φ (h ^ (n : ℕ))) hdecomp
  have hweighted :
      k * Ψ^n(fH) h =
        ∑ c : ConjClasses H, a c * (k * Ψ^n((c.indicator : H → A)) h) := by
    calc
      k * Ψ^n(fH) h = k * ∑ c : ConjClasses H, a c * Ψ^n((c.indicator : H → A)) h := by
        rw [hEval]
      _ = ∑ c : ConjClasses H, k * (a c * Ψ^n((c.indicator : H → A)) h) := by
        rw [Finset.mul_sum]
      _ = ∑ c : ConjClasses H, a c * (k * Ψ^n((c.indicator : H → A)) h) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        ring
  -- This is the promised indicator-basis expansion of the restricted corrected weighted transform.
  calc
    (globalWeightedAdamsClassFunction (A := A) n f : G → ℂ) h
        = algebraMap A ℂ (k * Ψ^n(fH) h) := by
            simp [globalWeightedAdamsClassFunction, Representation.adamsOperator, fH,
              subgroupClassFunctionRestriction, k]
    _ = ∑ c : ConjClasses H, algebraMap A ℂ (a c * (k * Ψ^n((c.indicator : H → A)) h)) := by
      simpa [map_sum] using congrArg (algebraMap A ℂ) hweighted
    _ =
        (∑ c : ConjClasses H, a c •
          (fun x : H ↦
            algebraMap A ℂ
              (k * Ψ^n((c.indicator : H → A)) x))) h := by
          simp [a, k, Algebra.smul_def, map_mul]

/-- Helper for Theorem 11-11.2-1: if each corrected global indicator basis pairing lands in the
image of `A`, then the same is true for any finite `A`-linear combination of those basis
vectors. -/
private theorem global_weighted_pairing_mem_range_of_indicator_expansion
    {H : Type w} [Group H] [Finite H]
    (n : ℕ+) (χ : H →* ℂˣ) (a : ConjClasses H → A)
    (hpair :
      ∀ c : ConjClasses H,
        ⟪χ.toCharacterRing,
          fun h : H ↦
            algebraMap A ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
                Ψ^n((c.indicator : H → A)) h)⟫ ∈
          Set.range (algebraMap A ℂ)) :
    ⟪χ.toCharacterRing,
      ∑ c : ConjClasses H,
        a c •
          (fun h : H ↦
            algebraMap A ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
                Ψ^n((c.indicator : H → A)) h))⟫ ∈
      Set.range (algebraMap A ℂ) := by
  classical
  let ψ : ConjClasses H → H → ℂ := fun c h ↦
    algebraMap A ℂ
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
        Ψ^n((c.indicator : H → A)) h)
  have huniv :
      (∑ c : ConjClasses H, a c • ψ c) =
        Finset.sum Finset.univ (fun c ↦ a c • ψ c) := by
    simp
  rw [huniv]
  let s : Finset (ConjClasses H) := Finset.univ
  change ⟪χ.toCharacterRing, Finset.sum s (fun c ↦ a c • ψ c)⟫ ∈ Set.range (algebraMap A ℂ)
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp [Representation.groupFunctionPairingOverField]
  | @insert c s hc ih =>
      have hterm :
          ⟪χ.toCharacterRing, a c • ψ c⟫ ∈ Set.range (algebraMap A ℂ) := by
        rcases hpair c with ⟨b, hb⟩
        refine ⟨a c * b, ?_⟩
        calc
          algebraMap A ℂ (a c * b) = algebraMap A ℂ (a c) * algebraMap A ℂ b := by
            simp [map_mul]
          _ = algebraMap A ℂ (a c) * ⟪χ.toCharacterRing, ψ c⟫ := by
                rw [hb]
          _ = ⟪χ.toCharacterRing, a c • ψ c⟫ := by
                symm
                simpa [Algebra.smul_def] using
                  (Representation.groupFunctionPairing_smul_right
                    (algebraMap A ℂ (a c))
                    (χ.toCharacterRing : H → ℂ)
                    (ψ c))
      rcases hterm with ⟨u, hu⟩
      rcases ih with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      calc
        algebraMap A ℂ (u + v) = algebraMap A ℂ u + algebraMap A ℂ v := by
          simp [map_add]
        _ = ⟪χ.toCharacterRing, a c • ψ c⟫ +
              ⟪χ.toCharacterRing, Finset.sum s (fun d ↦ a d • ψ d)⟫ := by
              rw [hu, hv]
        _ = ⟪χ.toCharacterRing, a c • ψ c + Finset.sum s (fun d ↦ a d • ψ d)⟫ := by
              symm
              exact Representation.groupFunctionPairing_add_right
                (χ.toCharacterRing : H → ℂ) (a c • ψ c) (Finset.sum s (fun d ↦ a d • ψ d))
        _ = ⟪χ.toCharacterRing, Finset.sum (insert c s) (fun d ↦ a d • ψ d)⟫ := by
              simp [Finset.sum_insert, hc]

/-- Helper for Theorem 11-11.2-1: the corrected global weighted indicator is itself a bundled
class function on any finite subgroup. -/
private theorem global_weighted_indicator_mem_classFunctionSubmodule
    [Finite G] {H : Type w} [Group H] [Finite H]
    (n : ℕ+) (c : ConjClasses H) :
    (fun h : H ↦
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
          Ψ^n((c.indicator : H → A)) h)) ∈
      classFunctionSubmodule ℂ H := by
  let hf : _root_.IsClassFunction (c.indicator : H → A) :=
    (mem_classFunctionSubmodule_iff A _).1 c.indicatorClassFunctionSubmodule.2
  let hadams : _root_.IsClassFunction (Ψ^n((c.indicator : H → A))) :=
    isClassFunction_adamsOperator n hf
  refine (mem_classFunctionSubmodule_iff ℂ _).2 ?_
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hxy_conj : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  have hadams_eq : Ψ^n((c.indicator : H → A)) x = Ψ^n((c.indicator : H → A)) y := by
    exact _root_.IsClassFunction.eq_of_isConj hadams hxy_conj
  have hA :
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
        Ψ^n((c.indicator : H → A)) x) =
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
          Ψ^n((c.indicator : H → A)) y) := by
    simp [hadams_eq]
  exact congrArg (algebraMap A ℂ) hA

/-- Helper for Theorem 11-11.2-1: conjugacy-class membership is preserved by transporting along a
multiplicative equivalence. -/
private theorem conjClasses_map_mem_carrier_mulEquiv_iff_local
    {H : Type w} [Group H] {J : Type*} [Group J]
    (e : H ≃* J) (d : ConjClasses H) (h : H) :
    e h ∈ (ConjClasses.map e.toMonoidHom d).carrier ↔ h ∈ d.carrier := by
  rcases ConjClasses.exists_rep d with ⟨x, rfl⟩
  -- After choosing a representative, transport the conjugacy witness across `e` or `e.symm`.
  constructor
  · intro hh
    have hmk : ConjClasses.mk (e h) = ConjClasses.mk (e x) := by
      simpa [ConjClasses.map] using (ConjClasses.mem_carrier_iff_mk_eq.mp hh)
    have hconj : IsConj h x := by
      simpa using e.symm.toMonoidHom.map_isConj ((ConjClasses.mk_eq_mk_iff_isConj).mp hmk)
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr ((ConjClasses.mk_eq_mk_iff_isConj).mpr hconj)
  · intro hh
    have hmk : ConjClasses.mk h = ConjClasses.mk x :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hh
    have hconj : IsConj (e h) (e x) := by
      exact e.toMonoidHom.map_isConj ((ConjClasses.mk_eq_mk_iff_isConj).mp hmk)
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr <|
      by simpa [ConjClasses.map] using (ConjClasses.mk_eq_mk_iff_isConj).mpr hconj

/-- Helper for Theorem 11-11.2-1: transporting a conjugacy-class indicator from `K` to
`K.map H.subtype` along the canonical subgroup equivalence preserves the corrected global weighted
pairing. -/
private theorem global_weighted_indicator_pairing_transport_from_subgroup_embedding_local
    [Finite G] (n : ℕ+) (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (d : ConjClasses K) :
    let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
    let d' : ConjClasses (K.map H.subtype) := ConjClasses.map e.toMonoidHom d
    ⟪χ.toCharacterRing,
      fun k : K ↦
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
            Ψ^n((d.indicator : K → A)) k)⟫ =
      ⟪(mappedLinearCharacter_local (G := G) H K χ).toCharacterRing,
        (⟨fun y : K.map H.subtype ↦
            algebraMap A ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
                Ψ^n((d'.indicator : K.map H.subtype → A)) y),
          global_weighted_indicator_mem_classFunctionSubmodule
            (A := A) (G := G) n d'⟩ :
          classFunctionSubmodule ℂ (K.map H.subtype))⟫ := by
  classical
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  let d' : ConjClasses (K.map H.subtype) := ConjClasses.map e.toMonoidHom d
  let φ' : classFunctionSubmodule ℂ (K.map H.subtype) :=
    ⟨fun y : K.map H.subtype ↦
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
            Ψ^n((d'.indicator : K.map H.subtype → A)) y),
      global_weighted_indicator_mem_classFunctionSubmodule (A := A) (G := G) n d'⟩
  have hprecomp :
      (fun k : K ↦ (φ' : K.map H.subtype → ℂ) (e k)) =
        (fun k : K ↦
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
              Ψ^n((d.indicator : K → A)) k)) := by
    funext k
    by_cases hk : k ^ (n : ℕ) ∈ d.carrier
    · have hk' : (e k) ^ (n : ℕ) ∈ d'.carrier := by
        -- Transport the chosen `n`th root from `K` to the mapped subgroup.
        simpa [d', e, map_pow] using
          (conjClasses_map_mem_carrier_mulEquiv_iff_local
            (e := e) (d := d) (h := k ^ (n : ℕ))).2 hk
      have hind : (d.indicator : K → A) (k ^ (n : ℕ)) = 1 := by
        simp [ConjClasses.indicator, hk]
      have hind' : (d'.indicator : K.map H.subtype → A) ((e k) ^ (n : ℕ)) = 1 := by
        simp [ConjClasses.indicator, hk']
      simp [φ', Representation.adamsOperator, hind, hind']
    · have hk' : (e k) ^ (n : ℕ) ∉ d'.carrier := by
        intro hk'
        have hk'' : k ^ (n : ℕ) ∈ d.carrier := by
          exact
            (conjClasses_map_mem_carrier_mulEquiv_iff_local
              (e := e) (d := d) (h := k ^ (n : ℕ))).1 <|
              by simpa [d', e, map_pow] using hk'
        exact hk hk''
      have hind : (d.indicator : K → A) (k ^ (n : ℕ)) = 0 := by
        simp [ConjClasses.indicator, hk]
      have hind' : (d'.indicator : K.map H.subtype → A) ((e k) ^ (n : ℕ)) = 0 := by
        simp [ConjClasses.indicator, hk']
      simp [φ', Representation.adamsOperator, hind, hind']
  -- Reindex the pairing along `K ≃ K.map H.subtype`, now that the indicator transport is explicit.
  have hpair :=
    linear_character_pairing_precomp_mulEquiv_local
      (e := e) (χ := χ) (φ := φ')
  -- First rewrite the pulled-back indicator class function to the original indicator on `K`.
  rw [hprecomp] at hpair
  simpa [e, d', φ', mappedLinearCharacter_local] using hpair

/-- Helper for Theorem 11-11.2-1: the subgroup Frobenius quotient
`|H| / gcd(|H|, n)` divides the ambient quotient `|G| / gcd(|G|, n)`. -/
private theorem subgroup_frobenius_quotient_dvd_global_frobenius_quotient
    [Finite G] (n : ℕ+) (H : Subgroup G) :
    Nat.card H / Nat.gcd (Nat.card H) (n : ℕ) ∣
      Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) := by
  let a : ℕ := Nat.card H
  let b : ℕ := Nat.card G
  let gA : ℕ := Nat.gcd a (n : ℕ)
  let gB : ℕ := Nat.gcd b (n : ℕ)
  have hab : a ∣ b := by
    simpa [a, b] using Subgroup.card_subgroup_dvd_card H
  have hgAgB : gA ∣ gB := by
    exact Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left a (n : ℕ)) hab) (Nat.gcd_dvd_right a (n : ℕ))
  have hq_dvd_bgA : a / gA ∣ b / gA := by
    rcases hab with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    calc
      b / gA = (a * m) / gA := by rw [hm]
      _ = (m * a) / gA := by rw [Nat.mul_comm]
      _ = m * (a / gA) := by
        exact Nat.mul_div_assoc m (Nat.gcd_dvd_left a (n : ℕ))
      _ = (a / gA) * m := by rw [Nat.mul_comm]
  have hfactor_dvd : gB / gA ∣ (n : ℕ) / gA := by
    refine ⟨(n : ℕ) / gB, ?_⟩
    -- The extra denominator added when passing from `H` to `G` still comes from the `n`-part.
    simpa [Nat.mul_comm, gA, gB] using
      (Nat.div_mul_div (Nat.gcd_dvd_right b (n : ℕ)) hgAgB).symm
  have hcop_base : Nat.Coprime (a / gA) ((n : ℕ) / gA) := by
    simpa [a, gA] using
      Nat.gcd_div_gcd_div_gcd_of_pos_right (Nat.pos_of_ne_zero n.ne_zero)
  have hcop : Nat.Coprime (a / gA) (gB / gA) := by
    exact Nat.Coprime.of_dvd_right hfactor_dvd hcop_base
  have hprod :
      (b / gB) * (gB / gA) = b / gA := by
    -- Re-associate the ambient denominator into the subgroup quotient and the remaining factor.
    simpa [gA, gB] using (Nat.div_mul_div (Nat.gcd_dvd_left b (n : ℕ)) hgAgB)
  have hq_dvd_prod : a / gA ∣ (b / gB) * (gB / gA) := by
      exact hprod ▸ hq_dvd_bgA
  exact hcop.dvd_of_dvd_mul_right hq_dvd_prod

/-- Helper for Theorem 11-11.2-1: in an elementary decomposition `H ≃ C × P`, the subgroup
`gcd(|H|, n)` factor splits into the cyclic and `p`-group gcd factors. -/
private theorem elementary_decomposition_gcd_card_eq_mul_local
    {H : Type w} [Group H] [Finite H] {p : ℕ} {C P : Subgroup H}
    (hCP : IsPElementaryDecomposition p C P) (n : ℕ+) :
    Nat.gcd (Nat.card H) (n : ℕ) =
      Nat.gcd (Nat.card C) (n : ℕ) * Nat.gcd (Nat.card P) (n : ℕ) := by
  letI : Fact (Nat.Prime p) := ⟨hCP.prime⟩
  have hcard : Nat.card H = Nat.card C * Nat.card P := by
    -- The elementary decomposition identifies `H` with the product of its two factors.
    symm
    exact hCP.isComplement.card_mul
  have hcop : Nat.Coprime (Nat.card C) (Nat.card P) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hCP.isPGroup
    rw [hm]
    exact hCP.coprime_card.symm.pow_right m
  calc
    Nat.gcd (Nat.card H) (n : ℕ) = Nat.gcd (Nat.card C * Nat.card P) (n : ℕ) := by
      rw [hcard]
    _ = Nat.gcd (Nat.card C) (n : ℕ) * Nat.gcd (Nat.card P) (n : ℕ) := by
      -- Coprimeness of the factor orders lets the gcd distribute across the product.
      simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        hcop.gcd_mul (k := (n : ℕ))

/-- Helper for Theorem 11-11.2-1: on an honest subgroup, the corrected global weighted indicator
pairing rewrites as an ambient integral scalar times the subgroup-gcd-normalized inverse
root-fiber sum. -/
private theorem global_weighted_rootfiber_sum_eq_integral_scalar_mul_subgroup_gcd_sum_local
    [Finite G] (n : ℕ+) (H : Subgroup G) (d : ConjClasses H) (χ : H →* ℂˣ)
    (g : d.carrier) (hroot : ∃ h : H, h ^ (n : ℕ) ∈ d.carrier) :
    ⟪χ.toCharacterRing,
      fun h : H ↦
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
            Ψ^n((d.indicator : H → A)) h)⟫ =
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) /
            (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) : ℕ) : A)) *
        ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
          ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) := by
  let kG : ℕ := Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)
  let kH : ℕ := Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)
  let m : ℕ := kG / orderOf (g : H)
  let S : ℂ := ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0
  have hkH_dvd : kH ∣ kG := by
    -- The subgroup quotient divides the ambient one by the earlier Frobenius-weight lemma.
    simpa [kG, kH] using
      subgroup_frobenius_quotient_dvd_global_frobenius_quotient (G := G) n H
  have hm_dvd : orderOf (g : H) ∣ kG := by
    -- The chosen conjugacy-class order divides the ambient corrected Frobenius weight.
    simpa [kG, m] using
      class_order_dvd_global_frobenius_weight_of_exists_root (G := G) n H d g hroot
  let ψ : H → ℂ := fun h : H ↦
    algebraMap A ℂ
      ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : A) *
        Ψ^n((d.indicator : H → A)) h)
  have hsmul :
      (fun h : H ↦
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
            Ψ^n((d.indicator : H → A)) h)) =
        ((((m : ℕ) : A)) • ψ) := by
    -- First rewrite the global weight as the scalar multiple of the local weighted indicator.
    simpa [kG, m, ψ] using
      global_weighted_indicator_eq_smul_local_weighted_indicator
        (A := A) (G := G) n H d g hroot
  have hpair_smul :
      ⟪χ.toCharacterRing,
        fun h : H ↦
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
              Ψ^n((d.indicator : H → A)) h)⟫ =
        algebraMap A ℂ (((m : ℕ) : A)) * ⟪χ.toCharacterRing, ψ⟫ := by
    -- Move the subgroup scalar outside the pairing after the source-faithful global-to-local
    -- rewrite.
    rw [hsmul]
    simpa [ψ, Algebra.smul_def] using
      (Representation.groupFunctionPairing_smul_right
        (a := algebraMap A ℂ (((m : ℕ) : A)))
        (φ := (χ.toCharacterRing : H → ℂ))
        (ψ := ψ))
  have hlocal :
      ⟪χ.toCharacterRing, ψ⟫ =
        algebraMap A ℂ (((orderOf (g : H) : ℕ) : A)) *
          ((Nat.card H : ℂ)⁻¹ * S) := by
    -- The local weighted indicator pairing is exactly the class-order root-fiber sum.
    simpa [ψ, S] using
      weighted_adams_indicator_pairing_eq_class_order_root_sum
        (A := A) (n := n) (χ := χ) (d := d) g
  have hm_mul :
      algebraMap A ℂ (((m : ℕ) : A)) *
          algebraMap A ℂ (((orderOf (g : H) : ℕ) : A)) =
        algebraMap A ℂ (((kG : ℕ) : A)) := by
    -- The class order was chosen precisely so that it cancels the denominator in `m`.
    calc
      algebraMap A ℂ (((m : ℕ) : A)) * algebraMap A ℂ (((orderOf (g : H) : ℕ) : A))
          = algebraMap A ℂ (((m * orderOf (g : H) : ℕ) : A)) := by
              simp [map_mul]
      _ = algebraMap A ℂ (((kG : ℕ) : A)) := by
            rw [Nat.div_mul_cancel hm_dvd]
  have hcard_ne_zero : (Nat.card H : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hgcd_ne_zero : ((Nat.gcd (Nat.card H) (n : ℕ) : ℕ) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right n.ne_zero)
  have hkH_norm :
      ((kH : ℂ) * (Nat.card H : ℂ)⁻¹) =
        ((Nat.gcd (Nat.card H) (n : ℕ) : ℂ)⁻¹) := by
    -- Replace the subgroup quotient `|H| / gcd(|H|, n)` by the reciprocal subgroup gcd.
    rw [show ((kH : ℕ) : ℂ) =
        (((Nat.card H / Nat.gcd (Nat.card H) (n : ℕ) : ℕ) : ℂ)) by rfl]
    rw [Nat.cast_div (Nat.gcd_dvd_left (Nat.card H) (n : ℕ))]
    · field_simp [hcard_ne_zero, hgcd_ne_zero]
    · exact hgcd_ne_zero
  have hnormalize :
      algebraMap A ℂ (((kG / kH : ℕ) : A)) *
          ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) * S) =
        algebraMap A ℂ (((kG : ℕ) : A)) * ((Nat.card H : ℂ)⁻¹ * S) := by
    -- Normalize the remaining denominator from `|H|` to `gcd(|H|, n)`.
    calc
      algebraMap A ℂ (((kG / kH : ℕ) : A)) *
          ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) * S)
          =
        algebraMap A ℂ (((kG / kH : ℕ) : A)) * (((kH : ℂ) * (Nat.card H : ℂ)⁻¹) * S) := by
            rw [hkH_norm]
      _ =
          ((algebraMap A ℂ (((kG / kH : ℕ) : A)) * ((kH : ℕ) : ℂ)) *
            ((Nat.card H : ℂ)⁻¹ * S)) := by
              ring
      _ =
          ((algebraMap A ℂ (((kG / kH : ℕ) : A)) *
              algebraMap A ℂ (((kH : ℕ) : A))) *
            ((Nat.card H : ℂ)⁻¹ * S)) := by
              simp
      _ = algebraMap A ℂ ((((kG / kH) * kH : ℕ) : A)) * ((Nat.card H : ℂ)⁻¹ * S) := by
            simp [map_mul]
      _ = algebraMap A ℂ (((kG : ℕ) : A)) * ((Nat.card H : ℂ)⁻¹ * S) := by
            rw [Nat.div_mul_cancel hkH_dvd]
  -- Combine the scalar rewrite and the local pairing identity, then normalize the remaining
  -- subgroup denominator.
  calc
    ⟪χ.toCharacterRing,
      fun h : H ↦
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
            Ψ^n((d.indicator : H → A)) h)⟫ =
        algebraMap A ℂ (((m : ℕ) : A)) * ⟪χ.toCharacterRing, ψ⟫ := hpair_smul
    _ =
        algebraMap A ℂ (((m : ℕ) : A)) *
          (algebraMap A ℂ (((orderOf (g : H) : ℕ) : A)) *
            ((Nat.card H : ℂ)⁻¹ * S)) := by
              rw [hlocal]
    _ =
        (algebraMap A ℂ (((m : ℕ) : A)) *
          algebraMap A ℂ (((orderOf (g : H) : ℕ) : A))) *
            ((Nat.card H : ℂ)⁻¹ * S) := by
              ring
    _ = algebraMap A ℂ (((kG : ℕ) : A)) * ((Nat.card H : ℂ)⁻¹ * S) := by
          rw [hm_mul]
    _ =
        algebraMap A ℂ ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) /
            (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) : ℕ) : A)) *
          ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) * S) := by
            simpa [kG, kH] using hnormalize.symm
    _ =
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) /
              (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) : ℕ) : A)) *
          ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
            ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) := by
              rfl

/-- Helper for Theorem 11-11.2-1: on an elementary subgroup, the subgroup-gcd-normalized inverse
root-fiber sum factors into a cyclic contribution and a `p`-group contribution. -/
private theorem elementary_inverse_rootfiber_sum_eq_cyclic_factor_mul_pgroup_factor_local
    {H : Type w} [Group H] [Finite H] [Fintype H]
    (n : ℕ+) (d : ConjClasses H) (χ : H →* ℂˣ)
    {p : ℕ} {C P : Subgroup H} (hCP : IsPElementaryDecomposition p C P)
    (h0 : H) (hh0 : h0 ^ (n : ℕ) ∈ d.carrier) :
    let e := hCP.isComplement.prodMulEquiv hCP.commute
    let χe : C × P →* ℂˣ := (χ.comp e.toMonoidHom)⁻¹
    let y0 : C × P := e.symm h0
    ∃ dP : ConjClasses P,
      ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
          ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) =
        ((((Nat.gcd (Nat.card C) (n : ℕ) : ℕ) : ℂ)⁻¹) *
            ∑ a : C,
              (if a ^ (n : ℕ) = y0.1 ^ (n : ℕ) then
                ((χe.comp (MonoidHom.inl C P) a : ℂˣ) : ℂ)
              else 0 : ℂ)) *
          ((((Nat.gcd (Nat.card P) (n : ℕ) : ℕ) : ℂ)⁻¹) *
            ∑ u : P,
              (if u ^ (n : ℕ) ∈ dP.carrier then
                ((χe.comp (MonoidHom.inr C P) u : ℂˣ) : ℂ)
              else 0 : ℂ)) := by
  classical
  letI : IsCyclic C := hCP.cyclic
  letI : CommGroup C := IsCyclic.commGroup
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  let χe : C × P →* ℂˣ := (χ.comp e.toMonoidHom)⁻¹
  let y0 : C × P := e.symm h0
  obtain ⟨dP, hdP⟩ :=
    elementary_prod_rootfiber_filter_split_local (n := n) (d := d) hCP h0 hh0
  refine ⟨dP, ?_⟩
  have hreindex :
      ∑ s : H, (if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0 : ℂ) =
        ∑ y : C × P,
          (if (e y : H) ^ (n : ℕ) ∈ d.carrier then
            ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
              ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)
          else 0 : ℂ) := by
    -- Reindex the inverse-character sum along the elementary product equivalence.
    simpa [e, χe] using
      elementary_inverse_rootfiber_sum_reindex_local
        (n := n) (c := d) (χ := χ) hCP
  have hsplit :
      ∑ y : C × P,
        (if (e y : H) ^ (n : ℕ) ∈ d.carrier then
          ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
            ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)
        else 0 : ℂ) =
      ∑ y : C × P,
        (if y.1 ^ (n : ℕ) = y0.1 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier then
          ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
            ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)
        else 0 : ℂ) := by
    -- Split the transported root condition into the cyclic power equation and the `P`-class test.
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hyroot : (e y : H) ^ (n : ℕ) ∈ d.carrier
    · have hyroot' : y.1 ^ (n : ℕ) = y0.1 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier :=
        (hdP y).1 hyroot
      simp [hyroot, hyroot']
    · have hyroot' : ¬ (y.1 ^ (n : ℕ) = y0.1 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier) := by
        intro hyroot'
        exact hyroot ((hdP y).2 hyroot')
      simp [hyroot, hyroot']
  have hfactor :
      ∑ y : C × P,
        (if y.1 ^ (n : ℕ) = y0.1 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier then
          ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
            ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)
        else 0 : ℂ) =
      (∑ a : C,
          (if a ^ (n : ℕ) = y0.1 ^ (n : ℕ) then
            ((χe.comp (MonoidHom.inl C P) a : ℂˣ) : ℂ)
          else 0 : ℂ)) *
        (∑ u : P,
          (if u ^ (n : ℕ) ∈ dP.carrier then
            ((χe.comp (MonoidHom.inr C P) u : ℂˣ) : ℂ)
          else 0 : ℂ)) := by
    -- Once the root predicate is split, the product-group sum factors into independent sums.
    simpa [y0] using
      elementary_inverse_rootfiber_sum_factor_local
        (n := n)
        (χC := χe.comp (MonoidHom.inl C P))
        (χP := χe.comp (MonoidHom.inr C P))
        (a0 := y0.1) (dP := dP)
  have hgcd :
      (((Nat.gcd (Nat.card H) (n : ℕ) : ℕ) : ℂ)) =
        (((Nat.gcd (Nat.card C) (n : ℕ) * Nat.gcd (Nat.card P) (n : ℕ) : ℕ) : ℂ)) := by
    exact congrArg (fun m : ℕ ↦ (m : ℂ))
      (elementary_decomposition_gcd_card_eq_mul_local hCP n)
  -- Rewrite the subgroup sum through the product decomposition, then distribute the normalized
  -- denominator using the subgroup-cardinality gcd factorization.
  calc
    ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
        ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) =
      ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
        ∑ y : C × P,
          (if (e y : H) ^ (n : ℕ) ∈ d.carrier then
            ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
              ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)
          else 0 : ℂ)) := by
            rw [hreindex]
    _ =
      ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
        ∑ y : C × P,
          (if y.1 ^ (n : ℕ) = y0.1 ^ (n : ℕ) ∧ y.2 ^ (n : ℕ) ∈ dP.carrier then
            ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
              ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)
          else 0 : ℂ)) := by
            rw [hsplit]
    _ =
      ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
        ((∑ a : C,
            (if a ^ (n : ℕ) = y0.1 ^ (n : ℕ) then
              ((χe.comp (MonoidHom.inl C P) a : ℂˣ) : ℂ)
            else 0 : ℂ)) *
          (∑ u : P,
            (if u ^ (n : ℕ) ∈ dP.carrier then
              ((χe.comp (MonoidHom.inr C P) u : ℂˣ) : ℂ)
            else 0 : ℂ)))) := by
              rw [hfactor]
    _ =
      ((((Nat.gcd (Nat.card C) (n : ℕ) : ℕ) : ℂ)⁻¹) *
          ∑ a : C,
            (if a ^ (n : ℕ) = y0.1 ^ (n : ℕ) then
              ((χe.comp (MonoidHom.inl C P) a : ℂˣ) : ℂ)
            else 0 : ℂ)) *
        ((((Nat.gcd (Nat.card P) (n : ℕ) : ℕ) : ℂ)⁻¹) *
          ∑ u : P,
            (if u ^ (n : ℕ) ∈ dP.carrier then
              ((χe.comp (MonoidHom.inr C P) u : ℂˣ) : ℂ)
            else 0 : ℂ)) := by
              rw [hgcd, Nat.cast_mul, mul_inv_rev]
              ring

/-- Helper for Theorem 11-11.2-1: finite sums of already `A`-valued complex numbers stay
`A`-valued. -/
private theorem finset_sum_mem_range_algebraMap_local
    {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, f i ∈ Set.range (algebraMap A ℂ)) :
    Finset.sum s f ∈ Set.range (algebraMap A ℂ) :=
  -- TODO: prove this by induction on `s`, combining the witnesses for each summand by
  -- additivity of `algebraMap`.
  sorry

/-- Helper for Theorem 11-11.2-1: summing the normalized inverse root-fiber sums over all
conjugacy classes recovers the total sum of the linear character. -/
private theorem sum_inverse_rootfiber_sum_over_classes_local
    {P : Type*} [Group P] [Finite P] (n : ℕ+) (χP : P →* ℂˣ) :
    (∑ dP : ConjClasses P,
      ∑ u : P, if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else (0 : ℂ)) =
        ∑ u : P, ((χP u : ℂˣ) : ℂ) :=
  -- TODO: exchange the two finite sums and use that each element `u ^ n` belongs to exactly one
  -- conjugacy class.
  sorry

/-- Helper for Theorem 11-11.2-1: the normalized total sum of a linear character is already
`A`-valued. -/
private theorem normalized_total_linear_character_sum_mem_range_local
    {P : Type*} [Group P] [Finite P] (n : ℕ+) (χP : P →* ℂˣ) :
    ((((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) * ∑ u : P, ((χP u : ℂˣ) : ℂ)) ∈
      Set.range (algebraMap A ℂ) := by
  by_cases hχ : χP = 1
  · obtain ⟨m, hm⟩ := Nat.gcd_dvd_left (Nat.card P) (n : ℕ)
    refine ⟨(m : A), ?_⟩
    have hg_pos : 0 < Nat.gcd (Nat.card P) (n : ℕ) := by
      exact Nat.gcd_pos_of_pos_right (Nat.card P) n.pos
    have hg_ne :
        (((Nat.gcd (Nat.card P) (n : ℕ) : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast hg_pos.ne'
    -- In the trivial-character case the total sum is `|P|`, so normalization divides by `gcd`.
    subst hχ
    calc
      algebraMap A ℂ (m : A) = (m : ℂ) := by
        simp
      _ = (((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) * (Nat.card P : ℂ) := by
            symm
            have hm' :
                (Nat.card P : ℂ) =
                  (Nat.gcd (Nat.card P) (n : ℕ) : ℂ) * (m : ℂ) := by
              exact_mod_cast hm
            calc
              (((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) * (Nat.card P : ℂ)
                  = (((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) *
                      ((Nat.gcd (Nat.card P) (n : ℕ) : ℂ) * (m : ℂ)) := by
                        rw [hm']
              _ = ((((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) *
                    (Nat.gcd (Nat.card P) (n : ℕ) : ℂ)) * (m : ℂ) := by
                      rw [mul_assoc]
              _ = (m : ℂ) := by
                    rw [inv_mul_cancel₀ hg_ne, one_mul]
      _ =
          ((((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) *
              ∑ u : P, (((1 : P →* ℂˣ) u : ℂˣ) : ℂ)) := by
                simp
  · -- A nontrivial linear character has total sum `0`, so the normalized total sum vanishes.
    refine ⟨0, ?_⟩
    have hsum : ∑ u : P, ((χP u : ℂˣ) : ℂ) = 0 :=
      sum_linearCharacter_eq_zero_of_ne_one_local χP hχ
    simp [hsum]

/-- Helper for Theorem 11-11.2-1: a nonunit conjugacy class in a finite `p`-group has order
`p^b` with `b > 0`. -/
private theorem nonunit_class_order_eq_prime_pow_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {dP : ConjClasses P} (hdP : dP ≠ ConjClasses.mk (1 : P)) (g : dP.carrier) :
    ∃ b : ℕ, 0 < b ∧ orderOf (g : P) = p ^ b := by
  -- The `p`-group hypothesis forces a `p`-power order, and nontriviality rules out `b = 0`.
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf (p := p) (G := P)).mp hP (g : P)
  refine ⟨b, ?_, hb⟩
  by_contra hb0
  have hb_eq : b = 0 := Nat.eq_zero_of_not_pos hb0
  have horder : orderOf (g : P) = 1 := by
    simpa [hb_eq] using hb
  have hg1 : (g : P) = 1 := orderOf_eq_one_iff.mp horder
  apply hdP
  calc
    dP = ConjClasses.mk (g : P) := (ConjClasses.mem_carrier_iff_mk_eq.mp g.property).symm
    _ = ConjClasses.mk (1 : P) := by simp [hg1]

/-- Helper for Theorem 11-11.2-1: any root landing in a fixed nonunit conjugacy class has order
obtained from the class order by shifting by the `p`-adic valuation of `n`. -/
private theorem nonunit_root_order_eq_padic_shift_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (n : ℕ+) {dP : ConjClasses P} (hdP : dP ≠ ConjClasses.mk (1 : P)) {x : P}
    (hx : x ^ (n : ℕ) ∈ dP.carrier) :
    ∃ b : ℕ, 0 < b ∧ orderOf x = p ^ (padicValNat p (n : ℕ) + b) := by
  -- First identify the nontrivial `p`-power order of the image `x ^ n`.
  obtain ⟨b, hbpos, hb⟩ :=
    nonunit_class_order_eq_prime_pow_local (p := p) hP hdP ⟨x ^ (n : ℕ), hx⟩
  have hxpow : orderOf (x ^ (n : ℕ)) = p ^ b := by
    simpa using hb
  -- Then separate `n` into its `p`-part and prime-to-`p` part.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := p) (G := P)).mp hP x
  let a : ℕ := padicValNat p (n : ℕ)
  let m : ℕ := Nat.divMaxPow (n : ℕ) p
  have hp : Nat.Prime p := Fact.out
  have hx_ne_one : x ≠ 1 := by
    intro hx1
    apply hdP
    have hx_unit : (1 : P) ^ (n : ℕ) ∈ dP.carrier := by
      simpa [hx1] using hx
    simpa using (ConjClasses.mem_carrier_iff_mk_eq.mp hx_unit).symm
  have hn : (n : ℕ) = p ^ a * m := by
    simpa [a, m] using (pow_padicValNat_mul_divMaxPow p (n : ℕ)).symm
  have hp1 : 1 < p := hp.one_lt
  have hn0 : (n : ℕ) ≠ 0 := ne_of_gt n.pos
  have hpm : ¬ p ∣ m := by
    simpa [m] using (Nat.not_dvd_divMaxPow (n := (n : ℕ)) hp1 hn0)
  have hkpos : 0 < k := by
    by_contra hk0
    have hk_eq : k = 0 := Nat.eq_zero_of_not_pos hk0
    have horder_one : orderOf x = 1 := by
      simpa [hk_eq] using hk
    exact hx_ne_one (orderOf_eq_one_iff.mp horder_one)
  have hcop : Nat.Coprime (p ^ k) m := by
    rw [Nat.coprime_pow_left_iff hkpos]
    exact hp.coprime_iff_not_dvd.2 hpm
  have hcop' : Nat.Coprime (orderOf x) m := by
    simpa [hk] using hcop
  have hxm : orderOf (x ^ m) = p ^ k := by
    simpa [hk] using (Nat.Coprime.orderOf_pow (y := x) (m := m) hcop')
  have hxpm : orderOf ((x ^ m) ^ (p ^ a)) = p ^ b := by
    calc
      orderOf ((x ^ m) ^ (p ^ a)) = orderOf (x ^ (m * p ^ a)) := by
        rw [pow_mul]
      _ = orderOf (x ^ (n : ℕ)) := by
            simp [hn, Nat.mul_comm]
      _ = p ^ b := hxpow
  -- The nontriviality of `x ^ n` forces at least `a` copies of `p` in `orderOf x`.
  have hka : a ≤ k := by
    by_contra hak
    have hle : k ≤ a := Nat.le_of_lt (lt_of_not_ge hak)
    have hpow1' : orderOf ((x ^ m) ^ (p ^ a)) = p ^ k / p ^ k := by
      simpa [hxm, Nat.gcd_eq_left (pow_dvd_pow p hle)] using
        (orderOf_pow' (x := x ^ m) (n := p ^ a) (pow_ne_zero _ hp.ne_zero))
    have hpow1 : orderOf ((x ^ m) ^ (p ^ a)) = 1 := by
      rw [hpow1']
      exact Nat.div_self (pow_pos hp.pos _)
    have hone : p ^ b = 1 := by
      calc
        p ^ b = orderOf ((x ^ m) ^ (p ^ a)) := hxpm.symm
        _ = 1 := hpow1
    have hbzero : b = 0 := Nat.pow_right_injective hp.two_le hone
    omega
  -- Now compute the exact shift in the exponent.
  have hdiv : p ^ a ∣ p ^ k := by
    exact pow_dvd_pow p hka
  have hpowk : orderOf ((x ^ m) ^ (p ^ a)) = p ^ (k - a) := by
    have hdiv' : p ^ a ∣ orderOf (x ^ m) := by
      simpa [hxm] using hdiv
    have horder :=
      orderOf_pow_of_dvd (x := x ^ m) (n := p ^ a) (pow_ne_zero _ hp.ne_zero) hdiv'
    have hdiv_eq : p ^ k / p ^ a = p ^ (k - a) := by
      apply Nat.div_eq_of_eq_mul_left (pow_pos hp.pos _)
      calc
        p ^ k = p ^ ((k - a) + a) := by
          rw [Nat.sub_add_cancel hka]
        _ = p ^ (k - a) * p ^ a := by
              rw [Nat.pow_add]
    simpa [hxm, hdiv_eq] using horder
  have hkb : k - a = b := by
    apply Nat.pow_right_injective hp.two_le
    simpa [hxpm] using hpowk.symm
  refine ⟨b, hbpos, ?_⟩
  rw [hk]
  have hsum : k = a + b := by
    omega
  simp [a, hsum]

/-- Helper for Theorem 11-11.2-1: the explicit exponents `1 + p^b t` preserve the `n`th-power
fiber once the root order is known. -/
private theorem nonunit_exponent_nth_power_eq_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {x : P} (b t : ℕ)
    (horder : orderOf x = p ^ (padicValNat p (n : ℕ) + b)) :
    (x ^ (1 + p ^ b * t)) ^ (n : ℕ) = x ^ (n : ℕ) := by
  let a : ℕ := padicValNat p (n : ℕ)
  let m : ℕ := Nat.divMaxPow (n : ℕ) p
  have hn : (n : ℕ) = p ^ a * m := by
    simpa [a, m] using (pow_padicValNat_mul_divMaxPow p (n : ℕ)).symm
  have hexp : ((1 + p ^ b * t) * (n : ℕ)) = (n : ℕ) + p ^ (a + b) * (m * t) := by
    rw [hn, Nat.pow_add]
    ring
  -- Expand the exponent and peel off a multiple of `orderOf x`.
  calc
    (x ^ (1 + p ^ b * t)) ^ (n : ℕ) = x ^ ((1 + p ^ b * t) * (n : ℕ)) := by
      rw [pow_mul]
    _ = x ^ ((n : ℕ) + p ^ (a + b) * (m * t)) := by
          rw [hexp]
    _ = x ^ (n : ℕ) * (x ^ (p ^ (a + b))) ^ (m * t) := by
          rw [pow_add, pow_mul]
    _ = x ^ (n : ℕ) * 1 := by
          congr 1
          rw [show p ^ (a + b) = orderOf x by
            simpa [a, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using horder.symm]
          simp [pow_orderOf_eq_one x]
    _ = x ^ (n : ℕ) := by
          simp

/-- Helper for Theorem 11-11.2-1: the source exponent family stays inside the same `n`th-root
fiber. -/
private theorem nonunit_exponent_mem_nth_root_fiber_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {dP : ConjClasses P} {x : P} (b t : ℕ)
    (hx : x ^ (n : ℕ) ∈ dP.carrier)
    (horder : orderOf x = p ^ (padicValNat p (n : ℕ) + b)) :
    (x ^ (1 + p ^ b * t)) ^ (n : ℕ) ∈ dP.carrier := by
  -- Replace the new `n`th power by the original one, then reuse the fiber hypothesis.
  simpa [nonunit_exponent_nth_power_eq_local (p := p) n b t horder] using hx

/-- Helper for Theorem 11-11.2-1: the parameterized character sum over one exponent cycle is
explicitly either `0` or a `p^a`-multiple of a single character value. -/
private theorem nonunit_parameter_character_sum_eq_zero_or_padic_multiple_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (χP : P →* ℂˣ) (x : P) (a b : ℕ)
    (horder : orderOf x = p ^ (a + b)) :
    ∑ i : Fin (p ^ a), (χP (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
      = if (χP (x ^ (p ^ b)) : ℂ) = 1 then (p ^ a : ℂ) * (χP x : ℂ) else 0 := by
  let z : ℂ := (χP (x ^ (p ^ b)) : ℂ)
  have hz : z ^ (p ^ a) = 1 := by
    dsimp [z]
    have hpowx : (x ^ (p ^ b)) ^ (p ^ a) = 1 := by
      have hp : Nat.Prime p := Fact.out
      have hdiv : p ^ b ∣ orderOf x := by
        rw [horder, Nat.pow_add, Nat.mul_comm]
        exact dvd_mul_of_dvd_left (dvd_refl (p ^ b)) (p ^ a)
      have htmp := orderOf_pow_of_dvd (x := x) (n := p ^ b) (pow_ne_zero _ hp.ne_zero) hdiv
      have hdiv_eq : p ^ (a + b) / p ^ b = p ^ a := by
        rw [Nat.pow_add, Nat.mul_comm]
        exact Nat.mul_div_right (p ^ a) (pow_pos hp.pos _)
      have hpoword : orderOf (x ^ (p ^ b)) = p ^ a := by
        simpa [horder, hdiv_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htmp
      simpa [hpoword] using pow_orderOf_eq_one (x ^ (p ^ b))
    simpa [map_pow] using congrArg (fun g : P ↦ (χP g : ℂ)) hpowx
  let geom : ℂ := Finset.sum (Finset.range (p ^ a)) fun i ↦ z ^ i
  have hgeom : geom = if z = 1 then (p ^ a : ℂ) else 0 := by
    by_cases h1 : z = 1
    · simp [geom, h1]
    · have hmul : geom * (z - 1) = 0 := by
        calc
          geom * (z - 1) = z ^ (p ^ a) - 1 := by
            simpa [geom] using geom_sum_mul z (p ^ a)
          _ = 0 := by
                simp [hz]
      have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hsum_zero : geom = 0 := (mul_eq_zero.mp hmul).resolve_right hzsub
      simp [geom, h1, hsum_zero]
  -- Factor out the first character value and evaluate the geometric progression.
  calc
    ∑ i : Fin (p ^ a), (χP (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
        = (χP x : ℂ) * geom := by
            calc
              (∑ i : Fin (p ^ a), (χP (x ^ (1 + p ^ b * (i : ℕ))) : ℂ))
                  = ∑ i : Fin (p ^ a), (χP x : ℂ) * ((χP (x ^ (p ^ b)) : ℂ)) ^ (i : ℕ) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      calc
                        (χP (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
                            = (χP x : ℂ) ^ (1 + p ^ b * (i : ℕ)) := by
                                simp
                        _ = (χP x : ℂ) * ((χP x : ℂ) ^ (p ^ b)) ^ (i : ℕ) := by
                              rw [pow_add, pow_one, pow_mul]
                        _ = (χP x : ℂ) * ((χP (x ^ (p ^ b)) : ℂ)) ^ (i : ℕ) := by
                              simp [map_pow]
              _ = (χP x : ℂ) * ∑ i : Fin (p ^ a), z ^ (i : ℕ) := by
                    rw [Finset.mul_sum]
              _ = (χP x : ℂ) * geom := by
                    simp_rw [Fin.sum_univ_eq_sum_range, geom]
    _ = if z = 1 then (p ^ a : ℂ) * (χP x : ℂ) else 0 := by
          by_cases h1 : z = 1
          · simp [geom, hgeom, h1, mul_comm]
          · simp [geom, hgeom, h1]

/-- Helper for Theorem 11-11.2-1: a root of order `p^(a+b)` has `n`th power of order `p^b`,
where `a = padicValNat p n`. -/
private theorem nonunit_nth_power_order_eq_prime_pow_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {x : P} {b : ℕ} (hbpos : 0 < b)
    (horder : orderOf x = p ^ (padicValNat p (n : ℕ) + b)) :
    orderOf (x ^ (n : ℕ)) = p ^ b := by
  let a : ℕ := padicValNat p (n : ℕ)
  let m : ℕ := Nat.divMaxPow (n : ℕ) p
  have hp : Nat.Prime p := Fact.out
  have hn : (n : ℕ) = p ^ a * m := by
    simpa [a, m] using (pow_padicValNat_mul_divMaxPow p (n : ℕ)).symm
  have hp1 : 1 < p := hp.one_lt
  have hn0 : (n : ℕ) ≠ 0 := ne_of_gt n.pos
  have hpm : ¬ p ∣ m := by
    simpa [m] using (Nat.not_dvd_divMaxPow (n := (n : ℕ)) hp1 hn0)
  have habpos : 0 < a + b := Nat.add_pos_right _ hbpos
  have hcop : Nat.Coprime (p ^ (a + b)) m := by
    rw [Nat.coprime_pow_left_iff habpos]
    exact hp.coprime_iff_not_dvd.2 hpm
  have hcop' : Nat.Coprime (orderOf x) m := by
    simpa [a, horder] using hcop
  have hxm : orderOf (x ^ m) = p ^ (a + b) := by
    simpa [a, horder] using (Nat.Coprime.orderOf_pow (y := x) (m := m) hcop')
  have hdiv : p ^ a ∣ orderOf (x ^ m) := by
    rw [hxm]
    exact pow_dvd_pow p (Nat.le_add_right a b)
  have hpow :
      orderOf ((x ^ m) ^ (p ^ a)) = p ^ (a + b) / p ^ a := by
    simpa [hxm] using
      (orderOf_pow_of_dvd (x := x ^ m) (n := p ^ a)
        (pow_ne_zero _ hp.ne_zero) hdiv)
  have hdiv_eq : p ^ (a + b) / p ^ a = p ^ b := by
    calc
      p ^ (a + b) / p ^ a = (p ^ a * p ^ b) / p ^ a := by
        rw [Nat.pow_add]
      _ = p ^ b := Nat.mul_div_right (p ^ b) (pow_pos hp.pos _)
  calc
    orderOf (x ^ (n : ℕ)) = orderOf ((x ^ m) ^ (p ^ a)) := by
      rw [hn, Nat.mul_comm, pow_mul]
    _ = p ^ (a + b) / p ^ a := hpow
    _ = p ^ b := hdiv_eq

/-- Helper for Theorem 11-11.2-1: all roots in the same nonunit `n`th-root fiber have the same
order. -/
private theorem nonunit_root_order_eq_uniform_shift_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (n : ℕ+) {dP : ConjClasses P} (hdP : dP ≠ ConjClasses.mk (1 : P)) {g x : P}
    (hg : g ^ (n : ℕ) ∈ dP.carrier) (hx : x ^ (n : ℕ) ∈ dP.carrier) :
    orderOf x = orderOf g := by
  -- Compare the common `n`th-power order inside the conjugacy class and recover the root order.
  obtain ⟨bx, hbxpos, hxorder⟩ :=
    nonunit_root_order_eq_padic_shift_local (p := p) hP n hdP hx
  obtain ⟨bg, hbgpos, hgorder⟩ :=
    nonunit_root_order_eq_padic_shift_local (p := p) hP n hdP hg
  have hxn : orderOf (x ^ (n : ℕ)) = p ^ bx :=
    nonunit_nth_power_order_eq_prime_pow_local (p := p) n hbxpos hxorder
  have hgn : orderOf (g ^ (n : ℕ)) = p ^ bg :=
    nonunit_nth_power_order_eq_prime_pow_local (p := p) n hbgpos hgorder
  have hsame : orderOf (x ^ (n : ℕ)) = orderOf (g ^ (n : ℕ)) := by
    exact orderOf_eq_of_mem_conjClass_local ⟨g ^ (n : ℕ), hg⟩ hx
  have hpoweq : p ^ bx = p ^ bg := by
    simpa [hxn, hgn] using hsame
  have hbeq : bx = bg := Nat.pow_right_injective (Fact.out : Nat.Prime p).two_le hpoweq
  calc
    orderOf x = p ^ (padicValNat p (n : ℕ) + bx) := hxorder
    _ = p ^ (padicValNat p (n : ℕ) + bg) := by
          simp [hbeq]
    _ = orderOf g := hgorder.symm

/-- Helper for Theorem 11-11.2-1: the source exponent parametrization of a nonunit orbit is
injective on the parameter `Fin (p^a)`. -/
private theorem nonunit_exponent_embedding_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {dP : ConjClasses P} (b : ℕ)
    (x : {y : P // y ^ (n : ℕ) ∈ dP.carrier})
    (horder : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b)) :
    Function.Injective
      (fun i : Fin (p ^ padicValNat p (n : ℕ)) ↦
        (⟨(x : P) ^ (1 + p ^ b * (i : ℕ)),
          nonunit_exponent_mem_nth_root_fiber_local (p := p) n b i x.property horder⟩ :
          {y : P // y ^ (n : ℕ) ∈ dP.carrier})) := by
  intro i j hij
  have hij_pow :
      (x : P) ^ (1 + p ^ b * (i : ℕ)) = (x : P) ^ (1 + p ^ b * (j : ℕ)) := by
    exact congrArg Subtype.val hij
  have hmod :
      1 + p ^ b * (i : ℕ) ≡ 1 + p ^ b * (j : ℕ) [MOD orderOf (x : P)] :=
    (pow_eq_pow_iff_modEq).mp hij_pow
  have hmul :
      p ^ b * (i : ℕ) ≡ p ^ b * (j : ℕ) [MOD orderOf (x : P)] := by
    exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl 1) hmod
  have hmul' :
      p ^ b * (i : ℕ) ≡ p ^ b * (j : ℕ)
        [MOD p ^ b * p ^ padicValNat p (n : ℕ)] := by
    simpa [horder, Nat.pow_add, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hmul
  have hparam :
      (i : ℕ) ≡ (j : ℕ) [MOD p ^ padicValNat p (n : ℕ)] := by
    exact Nat.ModEq.mul_left_cancel' (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero) hmul'
  have hi_lt : (i : ℕ) < p ^ padicValNat p (n : ℕ) := i.isLt
  have hj_lt : (j : ℕ) < p ^ padicValNat p (n : ℕ) := j.isLt
  have hij_val : (i : ℕ) = (j : ℕ) := by
    rcases le_total (i : ℕ) (j : ℕ) with hle | hle
    · have hdiv : p ^ padicValNat p (n : ℕ) ∣ (j : ℕ) - (i : ℕ) := by
        exact (Nat.modEq_iff_dvd' hle).mp hparam
      have hlt : (j : ℕ) - (i : ℕ) < p ^ padicValNat p (n : ℕ) := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) hj_lt
      have hzero : (j : ℕ) - (i : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      exact Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hzero)
    · have hdiv : p ^ padicValNat p (n : ℕ) ∣ (i : ℕ) - (j : ℕ) := by
        exact (Nat.modEq_iff_dvd' hle).mp hparam.symm
      have hlt : (i : ℕ) - (j : ℕ) < p ^ padicValNat p (n : ℕ) := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) hi_lt
      have hzero : (i : ℕ) - (j : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hle
  exact Fin.ext hij_val

/-- Helper for Theorem 11-11.2-1: one explicit nonunit exponent cycle, packaged as an embedding
from `Fin (p^a)` into the root fiber. -/
private noncomputable def nonunit_exponent_cycle_embedding_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) (dP : ConjClasses P) (b : ℕ)
    (x : {y : P // y ^ (n : ℕ) ∈ dP.carrier})
    (horder : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b)) :
    Fin (p ^ padicValNat p (n : ℕ)) ↪ {y : P // y ^ (n : ℕ) ∈ dP.carrier} :=
  { toFun := fun i ↦
      ⟨(x : P) ^ (1 + p ^ b * (i : ℕ)),
        nonunit_exponent_mem_nth_root_fiber_local (p := p) n b i x.property horder⟩
    inj' := nonunit_exponent_embedding_local (p := p) n b x horder }

/-- Helper for Theorem 11-11.2-1: the explicit exponent cycle through a nonunit root. -/
private noncomputable def nonunit_exponent_cycle_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) (dP : ConjClasses P) (b : ℕ)
    (x : {y : P // y ^ (n : ℕ) ∈ dP.carrier})
    (horder : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b)) :
    Finset {y : P // y ^ (n : ℕ) ∈ dP.carrier} :=
  let _ := Classical.decEq {y : P // y ^ (n : ℕ) ∈ dP.carrier}
  Finset.univ.map (nonunit_exponent_cycle_embedding_local (p := p) n dP b x horder)

/-- Helper for Theorem 11-11.2-1: the normalized average of one exponent cycle is already
`A`-valued. -/
private theorem pgroup_exponent_cycle_average_mem_range_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {dP : ConjClasses P} (χP : P →* ℂˣ) (b : ℕ)
    (x : {y : P // y ^ (n : ℕ) ∈ dP.carrier})
    (horder : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b))
    (hrootsP : ∀ z : ℂˣ, z ^ Nat.card P = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ((((p ^ padicValNat p (n : ℕ) : ℕ) : ℂ)⁻¹) *
        Finset.sum
          (nonunit_exponent_cycle_local (p := p) n dP b x horder)
          (fun y ↦ ((χP y : ℂˣ) : ℂ))) ∈
      Set.range (algebraMap A ℂ) :=
  -- TODO: use the parameter-sum formula for one exponent cycle and split into the
  -- `χP (x^(p^b)) = 1` and `≠ 1` cases.
  sorry

/-- Helper for Theorem 11-11.2-1: every explicit exponent cycle contains its chosen base point. -/
private theorem nonunit_exponent_cycle_self_mem_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {dP : ConjClasses P} (b : ℕ)
    (x : {y : P // y ^ (n : ℕ) ∈ dP.carrier})
    (horder : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b)) :
    x ∈ nonunit_exponent_cycle_local (p := p) n dP b x horder := by
  classical
  -- The parameter `0` returns the original root.
  refine Finset.mem_map.mpr ?_
  refine ⟨0, by simp, ?_⟩
  apply Subtype.ext
  simp [nonunit_exponent_cycle_embedding_local]

/-- Helper for Theorem 11-11.2-1: every explicit exponent cycle has cardinality `p^a`. -/
private theorem nonunit_exponent_cycle_card_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {dP : ConjClasses P} (b : ℕ)
    (x : {y : P // y ^ (n : ℕ) ∈ dP.carrier})
    (horder : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b)) :
    (nonunit_exponent_cycle_local (p := p) n dP b x horder).card =
      p ^ padicValNat p (n : ℕ) := by
  classical
  -- The cycle is the image of `Fin (p^a)` under an embedding.
  simp [nonunit_exponent_cycle_local]

/-- Helper for Theorem 11-11.2-1: if one root lies in another explicit exponent cycle, then the
second cycle is contained in the first. -/
private theorem nonunit_exponent_cycle_subset_of_mem_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {dP : ConjClasses P} (b : ℕ)
    (x y : {z : P // z ^ (n : ℕ) ∈ dP.carrier})
    (hx : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b))
    (hy : orderOf (y : P) = p ^ (padicValNat p (n : ℕ) + b))
    (hxy : y ∈ nonunit_exponent_cycle_local (p := p) n dP b x hx) :
    nonunit_exponent_cycle_local (p := p) n dP b y hy ⊆
      nonunit_exponent_cycle_local (p := p) n dP b x hx := by
  classical
  intro z hz
  -- Unpack both memberships into parameters and compose the exponents modulo the common order.
  rcases Finset.mem_map.mp hxy with ⟨i, -, rfl⟩
  rcases Finset.mem_map.mp hz with ⟨j, -, rfl⟩
  let a : ℕ := padicValNat p (n : ℕ)
  let k₀ : ℕ := (i : ℕ) + (j : ℕ) + p ^ b * (i : ℕ) * (j : ℕ)
  let k : Fin (p ^ a) := ⟨k₀ % p ^ a, Nat.mod_lt _ (pow_pos (Fact.out : Nat.Prime p).pos _)⟩
  refine Finset.mem_map.mpr ?_
  refine ⟨k, by simp, ?_⟩
  apply Subtype.ext
  have hk_eq :
      (1 + p ^ b * (i : ℕ)) * (1 + p ^ b * (j : ℕ)) = 1 + p ^ b * k₀ := by
    dsimp [k₀]
    ring
  have hk_le : (k : ℕ) ≤ k₀ := by
    dsimp [k]
    exact Nat.mod_le _ _
  have hk_div : p ^ a ∣ k₀ - (k : ℕ) := by
    exact (Nat.modEq_iff_dvd' hk_le).mp (by
      simpa [k, a] using Nat.mod_modEq k₀ (p ^ a))
  have hpow_mod' :
      1 + p ^ b * (k : ℕ) ≡ 1 + p ^ b * k₀ [MOD p ^ (a + b)] := by
    have hle : 1 + p ^ b * (k : ℕ) ≤ 1 + p ^ b * k₀ := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        add_le_add_left (Nat.mul_le_mul_left _ hk_le) 1
    apply (Nat.modEq_iff_dvd' hle).mpr
    rw [Nat.add_sub_add_left]
    rw [← Nat.mul_sub_left_distrib]
    have hmul : p ^ a * p ^ b ∣ (k₀ - (k : ℕ)) * p ^ b :=
      Nat.mul_dvd_mul_right hk_div (p ^ b)
    simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have hpow_mod :
      1 + p ^ b * (k : ℕ) ≡ (1 + p ^ b * (i : ℕ)) * (1 + p ^ b * (j : ℕ))
        [MOD p ^ (a + b)] := by
    simpa [hk_eq] using hpow_mod'
  have hpow_eq :
      (x : P) ^ (1 + p ^ b * (k : ℕ)) =
        (x : P) ^ ((1 + p ^ b * (i : ℕ)) * (1 + p ^ b * (j : ℕ))) := by
    exact (pow_eq_pow_iff_modEq).mpr (by simpa [a, hx] using hpow_mod)
  calc
    (x : P) ^ (1 + p ^ b * (k : ℕ))
        = (x : P) ^ ((1 + p ^ b * (i : ℕ)) * (1 + p ^ b * (j : ℕ))) := hpow_eq
    _ = ((x : P) ^ (1 + p ^ b * (i : ℕ))) ^ (1 + p ^ b * (j : ℕ)) := by
          rw [pow_mul]

/-- Helper for Theorem 11-11.2-1: two explicit exponent cycles coincide as soon as they
intersect. -/
private theorem nonunit_exponent_cycle_eq_of_mem_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {dP : ConjClasses P} (b : ℕ)
    (x y : {z : P // z ^ (n : ℕ) ∈ dP.carrier})
    (hx : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b))
    (hy : orderOf (y : P) = p ^ (padicValNat p (n : ℕ) + b))
    (hxy : y ∈ nonunit_exponent_cycle_local (p := p) n dP b x hx) :
    nonunit_exponent_cycle_local (p := p) n dP b y hy =
      nonunit_exponent_cycle_local (p := p) n dP b x hx := by
  classical
  -- The overlap inclusion and the common cardinality `p^a` force equality.
  apply Finset.eq_of_subset_of_card_le
  · exact nonunit_exponent_cycle_subset_of_mem_local (p := p) n b x y hx hy hxy
  · rw [nonunit_exponent_cycle_card_local, nonunit_exponent_cycle_card_local]

/-- Helper for Theorem 11-11.2-1: two explicit exponent cycles are equal exactly when one base
point lies in the other cycle. -/
private theorem nonunit_exponent_cycle_eq_iff_mem_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (n : ℕ+) {dP : ConjClasses P} (b : ℕ)
    (x y : {z : P // z ^ (n : ℕ) ∈ dP.carrier})
    (hx : orderOf (x : P) = p ^ (padicValNat p (n : ℕ) + b))
    (hy : orderOf (y : P) = p ^ (padicValNat p (n : ℕ) + b)) :
    nonunit_exponent_cycle_local (p := p) n dP b y hy =
      nonunit_exponent_cycle_local (p := p) n dP b x hx ↔
        y ∈ nonunit_exponent_cycle_local (p := p) n dP b x hx := by
  classical
  constructor
  · intro hEq
    simpa [hEq] using nonunit_exponent_cycle_self_mem_local (p := p) n b y hy
  · intro hxy
    exact nonunit_exponent_cycle_eq_of_mem_local (p := p) n b x y hx hy hxy

/-- Helper for Theorem 11-11.2-1: once a nonunit root exists, the normalizing factor for the
`p`-group root-fiber sum is exactly `p^a = gcd(|P|, n)`. -/
private theorem nonunit_padic_generator_eq_gcd_card_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (n : ℕ+) {b : ℕ}
    (hcard_div : p ^ (padicValNat p (n : ℕ) + b) ∣ Nat.card P) :
    Nat.gcd (Nat.card P) (n : ℕ) = p ^ padicValNat p (n : ℕ) := by
  let a : ℕ := padicValNat p (n : ℕ)
  let m : ℕ := Nat.divMaxPow (n : ℕ) p
  have hp : Nat.Prime p := Fact.out
  have hn : (n : ℕ) = p ^ a * m := by
    simpa [a, m] using (pow_padicValNat_mul_divMaxPow p (n : ℕ)).symm
  have hp1 : 1 < p := hp.one_lt
  have hn0 : (n : ℕ) ≠ 0 := ne_of_gt n.pos
  have hpm : ¬ p ∣ m := by
    simpa [m] using (Nat.not_dvd_divMaxPow (n := (n : ℕ)) hp1 hn0)
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hP
  have hak : a ≤ k := by
    rw [hk] at hcard_div
    have hpow : p ^ (a + b) ∣ p ^ k := by
      simpa [a] using hcard_div
    have hle := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpow
    exact le_trans (Nat.le_add_right a b) hle
  have hcop : Nat.Coprime m (p ^ (k - a)) := by
    exact hp.coprime_pow_of_not_dvd (m := k - a) hpm
  have hk_split : p ^ k = p ^ (k - a) * p ^ a := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hak]
  calc
    Nat.gcd (Nat.card P) (n : ℕ) = Nat.gcd (p ^ k) (p ^ a * m) := by
      rw [hk, hn]
    _ = Nat.gcd (p ^ k) (m * p ^ a) := by
          rw [Nat.mul_comm]
    _ = Nat.gcd (p ^ (k - a) * p ^ a) (m * p ^ a) := by
          rw [hk_split]
    _ = Nat.gcd (p ^ (k - a)) m * p ^ a := by
          rw [Nat.gcd_mul_right]
    _ = 1 * p ^ a := by
          rw [Nat.gcd_comm, (Nat.coprime_iff_gcd_eq_one.mp hcop)]
    _ = p ^ a := by
          simp

/-- Helper for Theorem 11-11.2-1: the nonunit `p`-group root-fiber sum is controlled by the
source orbit decomposition into exponent cycles. -/
private theorem nonunit_pgroup_inverse_rootfiber_sum_mem_range_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (n : ℕ+) (dP : ConjClasses P) (χP : P →* ℂˣ)
    (hrootsP : ∀ z : ℂˣ, z ^ Nat.card P = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)))
    (hdP : dP ≠ ConjClasses.mk (1 : P))
    (hroot : ∃ u : P, u ^ (n : ℕ) ∈ dP.carrier) :
    ((((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) *
        ∑ u : P, if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0) ∈
      Set.range (algebraMap A ℂ) :=
  -- TODO: decompose the nonunit root-fiber into exponent cycles and sum the already-controlled
  -- cycle averages.
  sorry

/-- Helper for Theorem 11-11.2-1: the unit root-fiber sum is recovered from the normalized total
linear-character sum after subtracting the already-controlled nonunit classes. -/
private theorem unit_class_pgroup_inverse_rootfiber_sum_mem_range_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (n : ℕ+) (χP : P →* ℂˣ)
    (hrootsP : ∀ z : ℂˣ, z ^ Nat.card P = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ((((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) *
        ∑ u : P,
          if u ^ (n : ℕ) ∈ (ConjClasses.mk (1 : P)).carrier then ((χP u : ℂˣ) : ℂ) else 0) ∈
      Set.range (algebraMap A ℂ) :=
  -- TODO: recover the unit class by subtracting the nonunit class contributions from the
  -- normalized total character sum.
  sorry

/-- Helper for Theorem 11-11.2-1: on a finite `p`-group, the normalized root-fiber sum of a
degree-`1` character already lands in the image of `A` under the ambient roots-of-unity
hypothesis. -/
private theorem pgroup_inverse_rootfiber_sum_mem_range_local
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (n : ℕ+) (dP : ConjClasses P) (χP : P →* ℂˣ)
    (hrootsP : ∀ z : ℂˣ, z ^ Nat.card P = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ((((Nat.gcd (Nat.card P) (n : ℕ) : ℂ))⁻¹) *
        ∑ u : P, if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0) ∈
      Set.range (algebraMap A ℂ) := by
  -- Route correction: the old `ℤ`-valued target was false. The remaining source-faithful work is
  -- the p-group closure statement valued directly in `A`, with the roots hypothesis carried on
  -- `P`.
  classical
  by_cases hdP : dP = ConjClasses.mk (1 : P)
  · -- The unit class is recovered from the normalized total sum by subtracting nonunit classes.
    subst hdP
    simpa using
      unit_class_pgroup_inverse_rootfiber_sum_mem_range_local
        (A := A) (p := p) hP n χP hrootsP
  · by_cases hroot : ∃ u : P, u ^ (n : ℕ) ∈ dP.carrier
    · -- A nonempty nonunit fiber is handled by the orbit decomposition into exponent cycles.
      exact nonunit_pgroup_inverse_rootfiber_sum_mem_range_local
        (A := A) (p := p) hP n dP χP hrootsP hdP hroot
    · -- If the fiber is empty then every summand vanishes.
      refine ⟨0, ?_⟩
      have hsum :
          (∑ u : P, if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else (0 : ℂ)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro u hu
        by_cases huroot : u ^ (n : ℕ) ∈ dP.carrier
        · exact False.elim (hroot ⟨u, huroot⟩)
        · simp [huroot]
      -- Rewrite the root-fiber sum to zero before simplifying the scalar factor.
      rw [hsum]
      simp

/-- Helper for Theorem 11-11.2-1: on an elementary subgroup, the subgroup-gcd-normalized inverse
root-fiber sum should be closed by the source `C × P` decomposition. -/
private theorem elementary_subgroup_gcd_inverse_rootfiber_sum_mem_range_on_subgroup_local
    [Finite G] (n : ℕ+) (H : Subgroup G) (hH : IsElementary H) (d : ConjClasses H)
    (χ : H →* ℂˣ)
    (hrootsH : ∀ z : ℂˣ, z ^ Nat.card H = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)))
    (hroot : ∃ h : H, h ^ (n : ℕ) ∈ d.carrier) :
    ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
        ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) ∈
      Set.range (algebraMap A ℂ) := by
  classical
  -- Route correction: the remaining source-faithful work is now isolated here on the honest
  -- subgroup `H ≤ G`, with the ambient scalar algebra already removed.
  let _ : Fintype H := Fintype.ofFinite H
  rcases hH with ⟨p, C, P, hCP⟩
  letI : Fact (Nat.Prime p) := ⟨hCP.prime⟩
  letI : IsCyclic C := hCP.cyclic
  letI : CommGroup C := IsCyclic.commGroup
  obtain ⟨h0, hh0⟩ := hroot
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  let χe : C × P →* ℂˣ := (χ.comp e.toMonoidHom)⁻¹
  let χC : C →* ℂˣ := χe.comp (MonoidHom.inl C P)
  let χP : P →* ℂˣ := χe.comp (MonoidHom.inr C P)
  let y0 : C × P := e.symm h0
  obtain ⟨dP, hfactor⟩ :=
    elementary_inverse_rootfiber_sum_eq_cyclic_factor_mul_pgroup_factor_local
      (n := n) (d := d) (χ := χ) hCP h0 hh0
  have hfactor_local :
      ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
          ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) =
        ((((Nat.gcd (Nat.card C) (n : ℕ) : ℕ) : ℂ)⁻¹) *
            ∑ a : C,
              (if a ^ (n : ℕ) = y0.1 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) else 0 : ℂ)) *
          ((((Nat.gcd (Nat.card P) (n : ℕ) : ℕ) : ℂ)⁻¹) *
            ∑ u : P,
              (if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0 : ℂ)) := by
    -- Normalize the source `C × P` factorization to the theorem-local aliases.
    simpa [e, χe, χC, χP, y0] using hfactor
  have hrootsC :
      ∀ z : ℂˣ, z ^ Nat.card C = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)) :=
    subgroup_roots_hypothesis_of_ambient_roots (G := H) (A := A) C hrootsH
  have hrootsP :
      ∀ z : ℂˣ, z ^ Nat.card P = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)) :=
    subgroup_roots_hypothesis_of_ambient_roots (G := H) (A := A) P hrootsH
  have hcyclic :
      ((((Nat.gcd (Nat.card C) (n : ℕ) : ℕ) : ℂ)⁻¹) *
          ∑ a : C,
            (if a ^ (n : ℕ) = y0.1 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) else 0 : ℂ)) ∈
        Set.range (algebraMap A ℂ) := by
    -- The cyclic factor is already handled by the finite cyclic root-fiber theorem.
    simpa [χC, Finset.sum_filter, map_inv] using
      cyclic_inverse_rootfiber_sum_mem_range_local
        (A := A) (hC := hCP.cyclic) (n := n) (χ := χC⁻¹) (a0 := y0.1) hrootsC
  have hpgroup :
      ((((Nat.gcd (Nat.card P) (n : ℕ) : ℕ) : ℂ)⁻¹) *
          ∑ u : P,
            (if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0 : ℂ)) ∈
        Set.range (algebraMap A ℂ) := by
    -- The `P`-factor now closes directly in `A`, so no separate `ℤ → A` bridge remains.
    simpa [χP] using
      pgroup_inverse_rootfiber_sum_mem_range_local
        (A := A) (hP := hCP.isPGroup) (n := n) (dP := dP) (χP := χP) hrootsP
  rcases hcyclic with ⟨a, ha⟩
  rcases hpgroup with ⟨b, hb⟩
  rw [hfactor_local]
  refine ⟨a * b, ?_⟩
  -- Multiply the cyclic and `P`-group `A`-valued witnesses directly inside `A`.
  calc
    algebraMap A ℂ (a * b) =
      algebraMap A ℂ a * algebraMap A ℂ b := by
        simp [map_mul]
    _ =
        ((((Nat.gcd (Nat.card C) (n : ℕ) : ℕ) : ℂ)⁻¹) *
            ∑ a : C,
              (if a ^ (n : ℕ) = y0.1 ^ (n : ℕ) then ((χC a : ℂˣ) : ℂ) else 0 : ℂ)) *
          ((((Nat.gcd (Nat.card P) (n : ℕ) : ℕ) : ℂ)⁻¹) *
            ∑ u : P,
              (if u ^ (n : ℕ) ∈ dP.carrier then ((χP u : ℂˣ) : ℂ) else 0 : ℂ)) := by
        -- The chosen witnesses realize each factor separately, so the product is immediate.
        rw [ha, hb]

/-- Helper for Theorem 11-11.2-1: on an elementary subgroup of `G`, each corrected global
weighted indicator pairing lands in the image of `A`. -/
private theorem elementary_global_weighted_indicator_pairing_mem_range_on_subgroup_local
    [Finite G] (n : ℕ+) (H : Subgroup G) (hH : IsElementary H) (χ : H →* ℂˣ)
    (d : ConjClasses H)
    (hrootsH : ∀ z : ℂˣ, z ^ Nat.card H = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ⟪χ.toCharacterRing,
      fun h : H ↦
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
            Ψ^n((d.indicator : H → A)) h)⟫ ∈
      Set.range (algebraMap A ℂ) := by
  classical
  by_cases hroot : ∃ h : H, h ^ (n : ℕ) ∈ d.carrier
  · -- Route correction: the cyclic root-fiber branch is now isolated by
    -- `global_weighted_indicator_pairing_transport_from_subgroup_embedding_local`. The remaining
    -- source-faithful work now splits cleanly into the scalar rewrite on `H` and the isolated
    -- subgroup-gcd root-fiber theorem.
    let g : d.carrier := ⟨Classical.choose hroot ^ (n : ℕ), Classical.choose_spec hroot⟩
    have hpair_eq :
        ⟪χ.toCharacterRing,
          fun h : H ↦
            algebraMap A ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
                Ψ^n((d.indicator : H → A)) h)⟫ =
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) /
                (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) : ℕ) : A)) *
            ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
              ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) := by
      -- Freeze the ambient scalar rewrite before invoking the subgroup-owned root-fiber theorem.
      simpa using
        global_weighted_rootfiber_sum_eq_integral_scalar_mul_subgroup_gcd_sum_local
          (A := A) (G := G) n H d χ g hroot
    have hsum :
        ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
            ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) ∈
          Set.range (algebraMap A ℂ) :=
      elementary_subgroup_gcd_inverse_rootfiber_sum_mem_range_on_subgroup_local
        (A := A) (G := G) n H hH d χ hrootsH hroot
    rw [hpair_eq]
    rcases hsum with ⟨b, hb⟩
    refine ⟨(((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) /
        (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) : ℕ) : A) * b, ?_⟩
    calc
      algebraMap A ℂ
          (((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) /
              (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) : ℕ) : A) * b)) =
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) /
              (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) : ℕ) : A)) *
          algebraMap A ℂ b := by
            simp [map_mul]
      _ =
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) /
                (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) : ℕ) : A)) *
            ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ))⁻¹) *
              ∑ s : H, if s ^ (n : ℕ) ∈ d.carrier then (χ s⁻¹ : ℂ) else 0) := by
                rw [hb]
  · have hzero :
        (fun h : H ↦
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
              Ψ^n((d.indicator : H → A)) h)) = 0 := by
      -- If the `n`th-root fiber is empty, the corrected indicator already vanishes pointwise.
      simpa using
        global_weighted_indicator_eq_zero_of_no_root (A := A) (G := G) n H d hroot
    rw [hzero]
    refine ⟨0, ?_⟩
    simp [Representation.groupFunctionPairingOverField]

/-- Helper for Theorem 11-11.2-1: once the corrected global basis pairings on a subgroup `K` are
known, the same holds for the restriction of the corrected global weighted indicator from the
ambient group. -/
private theorem global_weighted_indicator_restricted_pairing_mem_range_of_basis_cases
    {H : Type w} [Group H] [Finite H] [Finite G]
    (n : ℕ+) (c : ConjClasses H) (K : Subgroup H)
    (hpair :
      ∀ χ : K →* ℂˣ, ∀ d : ConjClasses K,
        ⟪χ.toCharacterRing,
          fun k : K ↦
            algebraMap A ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
                Ψ^n((d.indicator : K → A)) k)⟫ ∈
          Set.range (algebraMap A ℂ)) :
    ∀ χ : K →* ℂˣ,
      ⟪χ.toCharacterRing,
        fun k : K ↦
          (fun h : H ↦
            algebraMap A ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
                Ψ^n((c.indicator : H → A)) h)) k⟫ ∈
        Set.range (algebraMap A ℂ) := by
  intro χ
  let cK : classFunctionSubmodule A K :=
    subgroupClassFunctionRestriction (A := A) K c.indicatorClassFunctionSubmodule
  let a : ConjClasses K → A :=
    fun d ↦ ((mem_classFunctionSubmodule_iff A _).1
      cK.2).lift d
  let kG : A := (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A)
  have hrestrict :
      (fun k : K ↦
        (fun h : H ↦
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
              Ψ^n((c.indicator : H → A)) h)) k) =
        ∑ d : ConjClasses K,
          a d •
            (fun k : K ↦
              algebraMap A ℂ
                ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
                  Ψ^n((d.indicator : K → A)) k)) := by
    -- Expand the restricted indicator class function in the conjugacy-class basis of `K`, then
    -- transport the same finite decomposition through the Adams operator and the fixed global
    -- Frobenius weight coming from `G`.
    funext k
    have hdecomp :
        (cK : K → A) = fun x : K ↦ ∑ d : ConjClasses K, a d * d.indicator x := by
      simpa [cK, a] using classFunction_eq_sum_conjClass_indicator (A := A) cK
    have hEval :
        Ψ^n(cK) k = ∑ d : ConjClasses K, a d * Ψ^n((d.indicator : K → A)) k := by
      simpa [Representation.adamsOperator] using
        congrArg (fun φ : K → A ↦ φ (k ^ (n : ℕ))) hdecomp
    have hweighted :
        kG * Ψ^n(cK) k =
          ∑ d : ConjClasses K, a d * (kG * Ψ^n((d.indicator : K → A)) k) := by
      calc
        kG * Ψ^n(cK) k = kG * ∑ d : ConjClasses K, a d * Ψ^n((d.indicator : K → A)) k := by
          rw [hEval]
        _ = ∑ d : ConjClasses K, kG * (a d * Ψ^n((d.indicator : K → A)) k) := by
          rw [Finset.mul_sum]
        _ = ∑ d : ConjClasses K, a d * (kG * Ψ^n((d.indicator : K → A)) k) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          ring
    calc
      (fun k : K ↦
        (fun h : H ↦
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
              Ψ^n((c.indicator : H → A)) h)) k) k
          = algebraMap A ℂ (kG * Ψ^n(cK) k) := by
              simp [kG, cK, subgroupClassFunctionRestriction, Representation.adamsOperator]
      _ = ∑ d : ConjClasses K, algebraMap A ℂ (a d * (kG * Ψ^n((d.indicator : K → A)) k)) := by
        simpa [map_sum] using congrArg (algebraMap A ℂ) hweighted
      _ =
          (∑ d : ConjClasses K, a d •
            (fun x : K ↦
              algebraMap A ℂ
                (kG * Ψ^n((d.indicator : K → A)) x))) k := by
            simp [a, kG, Algebra.smul_def, map_mul]
  rw [hrestrict]
  exact
    global_weighted_pairing_mem_range_of_indicator_expansion
      (G := G) (A := A) n χ a (hpair χ)

/-- Helper for Theorem 11-11.2-1: on an elementary subgroup, each corrected global weighted
indicator basis vector already belongs to the realized scalar extension. -/
private theorem global_weighted_indicator_mem_characterRingScalarExtension_on_elementary
    [Finite G] (n : ℕ+) (H : Subgroup G) (hH : IsElementary H) (c : ConjClasses H)
    (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    (fun h : H ↦
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
          Ψ^n((c.indicator : H → A)) h)) ∈
      characterRingScalarExtension A H := by
  let φ : classFunctionSubmodule ℂ H :=
    ⟨fun h : H ↦
        algebraMap A ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
            Ψ^n((c.indicator : H → A)) h),
      global_weighted_indicator_mem_classFunctionSubmodule (A := A) (G := G) n c⟩
  have hpair :
      ∀ (K : Subgroup H) (_ : IsElementary K) (χ : K →* ℂˣ),
        ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction K φ⟫ ∈
          Set.range (algebraMap A ℂ) := by
    intro K hK χ
    let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
    let d' : ConjClasses K → ConjClasses (K.map H.subtype) :=
      fun d ↦ ConjClasses.map e.toMonoidHom d
    have hKmap : IsElementary (K.map H.subtype) :=
      isElementary_of_mulEquiv_local e hK
    have hrootsKmap :
        ∀ z : ℂˣ, z ^ Nat.card (K.map H.subtype) = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ)) :=
      subgroup_roots_hypothesis_of_ambient_roots (A := A) (K.map H.subtype) hroots
    -- Expand the restricted corrected global indicator in the conjugacy-class basis of `K`.
    simpa [φ, subgroupClassFunctionRestriction] using
      global_weighted_indicator_restricted_pairing_mem_range_of_basis_cases
        (G := G) (A := A) n c K
        (fun ξ d ↦ by
          -- Prove the basis pairing on the honest subgroup `K.map H.subtype ≤ G`, then pull the
          -- result back along the canonical subgroup equivalence `K ≃ K.map H.subtype`.
          rw [global_weighted_indicator_pairing_transport_from_subgroup_embedding_local
            (G := G) (A := A) n H K ξ d]
          simpa [e, d'] using
            elementary_global_weighted_indicator_pairing_mem_range_on_subgroup_local
              (G := G) (A := A) n (K.map H.subtype) hKmap
              (mappedLinearCharacter_local (G := G) H K ξ) (d' d) hrootsKmap) χ
  -- Feed the corrected pairing criterion into the existing shrink-based detector on elementary
  -- groups.
  simpa [φ] using
    elementary_classFunction_mem_characterRingScalarExtension_of_pairing_mem_range_local
      (A := A) hH φ hpair

/-- Helper for Theorem 11-11.2-1: the restriction of the corrected global Frobenius-weighted
Adams transform to an elementary subgroup already lies in the realized scalar extension. -/
private theorem global_weighted_adams_restriction_mem_characterRingScalarExtension_on_elementary
    [Finite G] (n : ℕ+) (f : classFunctionSubmodule A G) (H : Subgroup G) (hH : IsElementary H)
    (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    (fun h : H ↦ (globalWeightedAdamsClassFunction (A := A) n f : G → ℂ) h) ∈
      characterRingScalarExtension A H := by
  classical
  let a : ConjClasses H → A :=
    fun c ↦ ((mem_classFunctionSubmodule_iff A _).1
      (subgroupClassFunctionRestriction (A := A) H f).2).lift c
  let ψ : ConjClasses H → H → ℂ := fun c h ↦
    algebraMap A ℂ
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) *
        Ψ^n((c.indicator : H → A)) h)
  have hη_eq :
      (fun h : H ↦ (globalWeightedAdamsClassFunction (A := A) n f : G → ℂ) h) =
        ∑ c : ConjClasses H, a c • ψ c := by
    -- This is the source-faithful indicator expansion for the corrected global weighted Adams
    -- transform after restriction to `H`.
    simpa [a, ψ] using
      global_weighted_adams_restriction_eq_sum_conjClass_indicator (A := A) n f H
  rw [hη_eq]
  -- Sum the already-realized corrected indicator basis vectors with the coefficients of the
  -- restricted source class function.
  refine Submodule.sum_mem (characterRingScalarExtension A H) ?_
  intro c hc
  exact
    (characterRingScalarExtension A H).smul_mem (a c) <|
      by
        simpa [ψ] using
          global_weighted_indicator_mem_characterRingScalarExtension_on_elementary
            (A := A) n H hH c hroots

-- Proof sketch: apply Frobenius's theorem of Section `11.2` to the Adams transform `Ψ^n f`; the
-- global factor `|G| / gcd(|G|, n)` clears the denominators in the irreducible-character
-- expansion, producing an element of the tensor product owner `A ⊗ R(G)` whose realization is the
-- weighted Adams transform.
/-- Theorem 11-11.2-1: if `A` contains the `Nat.card G`-th roots of unity, then every
`A`-valued class function has Frobenius's weighted Adams transform
`g ↦ (Nat.card G / gcd (Nat.card G, n)) Ψ^n(f)(g)` realized by an element of `A ⊗ R(G)`.

This matches LinearRepresentations_Serre_1977's source statement: the multiplier is the global group-order factor
`|G| / (|G|, n)`, not the pointwise order factor `orderOf g / (orderOf g, n)`. The latter is a
stronger and false statement even for coefficient rings containing all `|G|`-th roots of unity. -/
theorem frobenius_weighted_adamsOperator_lifts_to_tensorCharacterRing
    [Finite G] (n : ℕ+) (f : classFunctionSubmodule A G)
    (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    ∃ χ : A ⊗R(G),
      χ =
        fun g ↦
          algebraMap A ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) * Ψ^n(f) g) := by
  let φ : classFunctionSubmodule ℂ G := globalWeightedAdamsClassFunction (A := A) n f
  obtain ⟨χ, hχ⟩ :=
    classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups_local
      (G := G) (A := A) φ (fun H hH ↦
        global_weighted_adams_restriction_mem_characterRingScalarExtension_on_elementary
          (A := A) n f H hH hroots)
  -- The corrected weighted Adams transform is now realized by the tensor character returned by
  -- the Brauer-descent theorem.
  refine ⟨χ, ?_⟩
  simpa [φ, globalWeightedAdamsClassFunction] using hχ

/-- Companion bridge form of Theorem 11-11.2-1 in the complex-function realization of
`A ⊗ R(G)`. -/
theorem frobenius_weighted_adamsOperator_mem_characterRingScalarExtension
    [Finite G] (n : ℕ+) (f : classFunctionSubmodule A G)
    (hroots : ∀ z : ℂˣ, z ^ Nat.card G = 1 → ((z : ℂ) ∈ Set.range (algebraMap A ℂ))) :
    (fun g ↦
      algebraMap A ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : A) * Ψ^n(f) g)) ∈
      characterRingScalarExtension A G := by
  rcases frobenius_weighted_adamsOperator_lifts_to_tensorCharacterRing n f hroots with ⟨χ, hχ⟩
  exact hχ ▸ tensorCharacterRing_mem_characterRingScalarExtension χ

end FrobeniusTheorem

end Representation
