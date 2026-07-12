import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_4_1
import LinearRepresentations_Serre_1977.Chap09.Corollary_9_9_2_2
import LinearRepresentations_Serre_1977.Chap09.Proposition_9_9_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Representation
open scoped BigOperators Representation SubgroupInduction

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type} [CommRing A] [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]

attribute [local instance] Fintype.ofFinite

omit [Finite G] [IsIntegralClosure A ℤ ℂ] in
/-- Helper for Exercise 10-10.3-4: coefficientwise complexification preserves the class-function
condition for a bundled `A`-valued class function. -/
lemma complexified_classFunction_mem_classFunctionSubspace
    (ψ : classFunctionSubmodule A G) :
    (algebraMap A ℂ ∘ ψ) ∈ _root_.classFunctionSubspace G := by
  -- Postcomposing the existing class-function owner by `algebraMap A ℂ` keeps conjugacy
  -- invariance intact.
  rw [_root_.mem_classFunctionSubspace_iff]
  exact ((mem_classFunctionSubmodule_iff A (ψ : G → A)).1 ψ.2).comp (algebraMap A ℂ)

/-- Helper for Exercise 10-10.3-4: package the coefficientwise complexification of a bundled
`A`-valued class function in the canonical complex class-function owner. -/
def complexified_classFunctionSubspace_of_classFunctionSubmodule
    (ψ : classFunctionSubmodule A G) :
    _root_.classFunctionSubspace G :=
  ⟨algebraMap A ℂ ∘ ψ, complexified_classFunction_mem_classFunctionSubspace ψ⟩

/-- Helper for Exercise 10-10.3-4: multiplying an induced class function by a global class
function amounts to inducing the product with the restricted global factor. -/
lemma induced_mul_eq_induced_mul_restriction
    (H : Subgroup G) (ψ : H → ℂ) (χ : _root_.classFunctionSubspace G) :
    Ind[H](ψ) * (χ : G → ℂ) = Ind[H](fun h : H ↦ ψ h * χ h) := by
  classical
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * x * s ∈ H
  · have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hχ : χ (s⁻¹ * x * s) = χ x := by
      exact (χ.2 : _root_.IsClassFunction (χ : G → ℂ)).eq_of_isConj <|
        isConj_iff.2 ⟨s, by group⟩
    have hχ' : χ (s⁻¹ * (x * s)) = χ x := by
      simpa [mul_assoc] using hχ
    simp [hs', hχ', mul_comm, mul_assoc]
  · simp [hs]

omit [Finite G] in
/-- Helper for Exercise 10-10.3-4: a linear character value is integral over `ℤ` because it is a
root of unity. -/
lemma linear_character_value_isIntegral
    {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (h : H) :
    IsIntegral ℤ ((χ h : ℂ)) := by
  -- The value of a linear character is a root of unity of order dividing `orderOf h`.
  apply IsIntegral.of_pow (n := orderOf h)
  · exact orderOf_pos h
  · rw [show ((χ h : ℂ) ^ orderOf h) = 1 by
      have hpowUnits : (χ h) ^ orderOf h = 1 := by
        rw [← map_pow]
        simp [pow_orderOf_eq_one h]
      exact congrArg (fun z : ℂˣ => (z : ℂ)) hpowUnits]
    exact isIntegral_one

/-- Helper for Exercise 10-10.3-4: every linear character value lifts through `algebraMap A ℂ`
because `A` is the integral closure of `ℤ` in `ℂ`. -/
lemma linear_character_value_mem_range
    {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (h : H) :
    (χ h : ℂ) ∈ Set.range (algebraMap A ℂ) := by
  -- Convert integrality of the value into actual membership in the integral-closure ring.
  exact
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).mp
      (linear_character_value_isIntegral χ h)

/-- Helper for Exercise 10-10.3-4: the linear characters of a finite commutative group form a
finite type. -/
local instance linearCharacterFinite_ex1034
    {H : Type} [CommGroup H] [Finite H] :
    Finite (H →* ℂˣ) := by
  let eDual : (H →* ℂˣ) ≃* H :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G := H) (M := ℂ))
  exact Finite.of_equiv H eDual.symm.toEquiv

/-- Helper for Exercise 10-10.3-4: the linear characters of a finite commutative group admit the
canonical `Fintype` structure coming from finiteness. -/
local instance linearCharacterFintype_ex1034
    {H : Type} [CommGroup H] [Finite H] :
    Fintype (H →* ℂˣ) := Fintype.ofFinite (H →* ℂˣ)

/-- Helper for Exercise 10-10.3-4: on a finite commutative group, the sum of all linear
characters vanishes away from the identity. -/
lemma commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one_ex1034
    {H : Type} [CommGroup H] [Finite H] {h : H} (hh : h ≠ 1) :
    ∑ χ : H →* ℂˣ, (χ h : ℂ) = 0 := by
  classical
  obtain ⟨φ, hφh⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G := H) (M := ℂ) hh
  let e : (H →* ℂˣ) ≃ (H →* ℂˣ) :=
    { toFun := fun χ ↦ φ * χ
      invFun := fun χ ↦ φ⁻¹ * χ
      left_inv := by
        intro χ
        simp
      right_inv := by
        intro χ
        simp }
  have hsum :
      ∑ χ : H →* ℂˣ, ((φ * χ) h : ℂ) =
        ∑ χ : H →* ℂˣ, (χ h : ℂ) := by
    exact Fintype.sum_equiv e
      (fun χ : H →* ℂˣ ↦ ((φ * χ) h : ℂ))
      (fun χ : H →* ℂˣ ↦ (χ h : ℂ))
      (fun χ ↦ rfl)
  have hmul :
      ∑ χ : H →* ℂˣ, ((φ * χ) h : ℂ) =
        (φ h : ℂ) * ∑ χ : H →* ℂˣ, (χ h : ℂ) := by
    -- Pull the fixed scalar `φ(h)` out of the finite sum.
    simp [Finset.mul_sum]
  have hfactor :
      (((φ h : ℂ) - 1) * ∑ χ : H →* ℂˣ, (χ h : ℂ)) = 0 := by
    -- Compare the unchanged sum with its translate by multiplication with `φ`.
    calc
      (((φ h : ℂ) - 1) * ∑ χ : H →* ℂˣ, (χ h : ℂ)) =
          (φ h : ℂ) * ∑ χ : H →* ℂˣ, (χ h : ℂ) -
            ∑ χ : H →* ℂˣ, (χ h : ℂ) := by
              ring
      _ = 0 := by
        rw [← hmul, hsum, sub_self]
  have hne : ((φ h : ℂ) - 1) ≠ 0 := by
    intro hzero
    have hcast : (φ h : ℂ) = 1 := sub_eq_zero.mp hzero
    apply hφh
    ext
    simpa using hcast
  exact (mul_eq_zero.mp hfactor).resolve_left hne

/-- Helper for Exercise 10-10.3-4: the regular character of a finite commutative group is the sum
of all degree-`1` complex characters. -/
lemma commGroup_regularCharacter_eq_sum_linearCharacters_ex1034
    {H : Type} [CommGroup H] [Finite H] :
    (leftRegular ℂ H).character = ∑ χ : H →* ℂˣ, (χ.toCharacterRing : H → ℂ) := by
  let _ : Fintype H := Fintype.ofFinite H
  ext h
  by_cases hh : h = 1
  · subst hh
    -- At the identity, every linear character contributes `1`, so only the count remains.
    rw [Representation.leftRegular_character_one (k := ℂ) (G := H), Finset.sum_apply]
    have hcard : Fintype.card H = Fintype.card (H →* ℂˣ) := by
      simpa using
        (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (G := H) (M := ℂ)).symm
    simp [hcard]
  · -- Away from the identity, the translated character sum collapses to zero.
    rw [Representation.leftRegular_character_eq_zero_of_ne_one (k := ℂ) (G := H) hh,
      Finset.sum_apply]
    simpa using (commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one_ex1034 (H := H) hh).symm

/-- Helper for Exercise 10-10.3-4: the `|H|`-point mass at any element of a finite cyclic group is
an `A`-linear combination of linear characters, hence belongs to the scalar-extended character
ring. -/
lemma point_mass_card_mem_characterRingScalarExtension
    {H : Type} [CommGroup H] [Finite H] [DecidableEq H] (u : H) :
    (fun h : H ↦ if h = u then (Nat.card H : ℂ) else 0) ∈
      Representation.characterRingScalarExtension A H := by
  classical
  let b : (H →* ℂˣ) → A := fun χ ↦
    Classical.choose (linear_character_value_mem_range (A := A) χ u⁻¹)
  have hb : ∀ χ : H →* ℂˣ, algebraMap A ℂ (b χ) = (χ u⁻¹ : ℂ) := by
    intro χ
    exact Classical.choose_spec (linear_character_value_mem_range (A := A) χ u⁻¹)
  have hdecomp :
      (fun h : H ↦ if h = u then (Nat.card H : ℂ) else 0) =
        ∑ χ : H →* ℂˣ, b χ • ((χ.toCharacterRing : R(H)) : H → ℂ) := by
    ext h
    have hiff : u⁻¹ * h = 1 ↔ h = u := by
      constructor
      · intro hone
        calc
          h = 1 * h := by simp
          _ = u * (u⁻¹ * h) := by group
          _ = u := by rw [hone, mul_one]
      · intro hh
        subst hh
        simp
    -- Expand the point mass via the finite Fourier decomposition over all linear characters.
    calc
      (if h = u then (Nat.card H : ℂ) else 0)
          = ∑ χ : H →* ℂˣ, (χ u⁻¹ : ℂ) * (χ h : ℂ) := by
              symm
              calc
                ∑ χ : H →* ℂˣ, (χ u⁻¹ : ℂ) * (χ h : ℂ)
                    = ∑ χ : H →* ℂˣ, (χ (u⁻¹ * h) : ℂ) := by
                        refine Fintype.sum_congr
                          (fun χ : H →* ℂˣ ↦ (χ u⁻¹ : ℂ) * (χ h : ℂ))
                          (fun χ : H →* ℂˣ ↦ (χ (u⁻¹ * h) : ℂ)) ?_
                        intro χ
                        simp [map_mul]
                _ = (leftRegular ℂ H).character (u⁻¹ * h) := by
                      symm
                      simpa using
                        congrFun (commGroup_regularCharacter_eq_sum_linearCharacters_ex1034 (H := H))
                          (u⁻¹ * h)
                _ = if u⁻¹ * h = 1 then (Nat.card H : ℂ) else 0 := by
                      simpa using
                        (Representation.leftRegular_character_eq_ite (k := ℂ) (G := H) (u⁻¹ * h))
                _ = if h = u then (Nat.card H : ℂ) else 0 := by
                      by_cases hone : u⁻¹ * h = 1
                      · have hh : h = u := hiff.mp hone
                        simp [hh]
                      · have hh : h ≠ u := by
                          intro hh
                          exact hone (hiff.mpr hh)
                        simp [hone, hh]
      _ = ∑ χ : H →* ℂˣ, algebraMap A ℂ (b χ) * (χ h : ℂ) := by
            refine Fintype.sum_congr
              (fun χ : H →* ℂˣ ↦ (χ u⁻¹ : ℂ) * (χ h : ℂ))
              (fun χ : H →* ℂˣ ↦ algebraMap A ℂ (b χ) * (χ h : ℂ)) ?_
            intro χ
            simp [hb χ]
      _ = (∑ χ : H →* ℂˣ, b χ • ((χ.toCharacterRing : R(H)) : H → ℂ)) h := by
            simp [Algebra.smul_def]
  rw [hdecomp]
  -- Sum the scalar-extended linear characters term by term.
  refine Submodule.sum_mem (Representation.characterRingScalarExtension A H) ?_
  intro χ hχ
  exact Submodule.smul_mem _ (b χ)
    (Representation.mem_characterRingScalarExtension_of_mem_characterRing (A := A)
      ((χ.toCharacterRing : R(H)) : H → ℂ) χ.toCharacterRing.property)

omit [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ] in
/-- Helper for Exercise 10-10.3-4: if each value of a bundled `A`-valued class function lies in
the ideal `|G|A`, then the quotient by `|G|` can be chosen compatibly on conjugacy classes, hence
again defines a bundled class function. -/
lemma class_function_quotient_exists_of_groupOrder_mem_ideal
    (f : classFunctionSubmodule A G)
    (hf_mem_span : ∀ x : G, f x ∈ Ideal.span {(Nat.card G : A)}) :
    ∃ q : classFunctionSubmodule A G, ∀ x : G, f x = (Nat.card G : A) * q x := by
  classical
  let fClasses : ConjClasses G → A := classFunctionSubmodule.equivFun A G f
  let qClasses : ConjClasses G → A := fun c ↦
    Classical.choose <| show ∃ a : A, a * (Nat.card G : A) = fClasses c from by
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
      simpa [fClasses] using Ideal.mem_span_singleton'.mp (hf_mem_span x)
  have hqClasses : ∀ c : ConjClasses G, fClasses c = (Nat.card G : A) * qClasses c := by
    intro c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    change f x = (Nat.card G : A) * qClasses (ConjClasses.mk x)
    have hq : qClasses (ConjClasses.mk x) * (Nat.card G : A) = f x :=
      by
        simpa [fClasses, qClasses] using
          (Classical.choose_spec
            (show ∃ a : A, a * (Nat.card G : A) = fClasses (ConjClasses.mk x) from by
              simpa [fClasses] using Ideal.mem_span_singleton'.mp (hf_mem_span x)))
    calc
      f x = qClasses (ConjClasses.mk x) * (Nat.card G : A) := hq.symm
      _ = (Nat.card G : A) * qClasses (ConjClasses.mk x) := by
        ac_rfl
  let q : classFunctionSubmodule A G := (classFunctionSubmodule.equivFun A G).symm qClasses
  refine ⟨q, ?_⟩
  intro x
  -- Evaluate the chosen quotient on the conjugacy class of `x` and transport it back through the
  -- canonical equivalence with functions on `ConjClasses G`.
  simpa [fClasses, qClasses, q] using hqClasses (ConjClasses.mk x)

/-- Helper for Exercise 10-10.3-4: once the cyclic subgroup function is known to be the
coefficientwise complexification of an `A`-valued class function with values in `|H|A`, its
induction lies in the cyclic induced-character span. -/
lemma cyclic_card_mul_function_induced_mem_cyclicInducedCharacterSpan
    (H : Subgroup G) (hH : IsCyclic H) (φ : H → ℂ)
    (hdiv : ∀ h : H, ∃ a : A, φ h = algebraMap A ℂ ((Nat.card H : A) * a)) :
    Ind[H](φ) ∈ Representation.cyclicInducedCharacterSpan A G := by
  letI : CommGroup H := IsCyclic.commGroup
  classical
  have hclass_comm {f : H → ℂ} : _root_.IsClassFunction f := by
    refine ⟨?_⟩
    intro x y hxy
    rcases ConjClasses.mk_eq_mk_iff_isConj.mp hxy with ⟨c, hc⟩
    apply congrArg f
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  let a : H → A := fun h ↦ Classical.choose (hdiv h)
  have ha : ∀ h : H, φ h = algebraMap A ℂ ((Nat.card H : A) * a h) := by
    intro h
    exact Classical.choose_spec (hdiv h)
  let δ : H → H → ℂ := fun u h ↦ if u = h then Nat.card H else 0
  let φcf : _root_.classFunctionSubspace H :=
    ⟨φ, (_root_.mem_classFunctionSubspace_iff _).2 hclass_comm⟩
  have hscalar : (φcf : H → ℂ) ∈ Representation.characterRingScalarExtension A H := by
    have hdecomp :
        (φcf : H → ℂ) = ∑ u : H, a u • δ u := by
      ext h
      calc
        φcf h = algebraMap A ℂ ((Nat.card H : A) * a h) := ha h
        _ = (a h • δ h) h := by
          simp [δ, Pi.smul_apply, Algebra.smul_def, map_mul, mul_comm]
        _ = ∑ u : H, (a u • δ u) h := by
          simp [δ, Pi.smul_apply]
        _ = (∑ u : H, a u • δ u) h := by
          simp only [Finset.sum_apply]
    refine hdecomp ▸ ?_
    refine Submodule.sum_mem (Representation.characterRingScalarExtension A H) ?_
    intro u hu
    have hδscalar : δ u ∈ Representation.characterRingScalarExtension A H := by
      -- Realize `δ u` as the `|H|`-point mass obtained from the finite Fourier decomposition over
      -- all linear characters of the cyclic group `H`.
      simpa [δ, eq_comm] using
        point_mass_card_mem_characterRingScalarExtension (A := A) (H := H) u
    exact Submodule.smul_mem
      (Representation.characterRingScalarExtension A H)
      (a u)
      hδscalar
  let P : (H → ℂ) → Prop :=
    fun g ↦ Ind[H](g) ∈ Representation.cyclicInducedCharacterSpan A G
  have hP : P (φcf : H → ℂ) := by
    rw [Representation.characterRingScalarExtension] at hscalar
    refine Submodule.span_induction
      (s := (R(H) : Set (H → ℂ)))
      (p := fun g _ ↦ P g)
      ?_ ?_ ?_ ?_ hscalar
    · intro g hg
      simpa [P] using
        Representation.inducedClassFunction_mem_cyclicInducedCharacterSpan (A := A) H hH ⟨g, hg⟩
    · have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext x
        simp [Subgroup.inducedClassFunction]
      change Ind[H]((0 : H → ℂ)) ∈ Representation.cyclicInducedCharacterSpan A G
      rw [hzero]
      exact
        (Submodule.zero_mem (Representation.cyclicInducedCharacterSpan A G) :
          (0 : G → ℂ) ∈ Representation.cyclicInducedCharacterSpan A G)
    · intro f₁ f₂ hf₁ hf₂ hf₁_mem hf₂_mem
      simpa [P, Subgroup.inducedClassFunction_map_add] using
        Submodule.add_mem (Representation.cyclicInducedCharacterSpan A G) hf₁_mem hf₂_mem
    · intro a' g hg hg_mem
      simpa [P, Subgroup.inducedClassFunction_map_smul] using
        Submodule.smul_mem (Representation.cyclicInducedCharacterSpan A G) a' hg_mem
  simpa [P, φcf] using hP

-- Source/core/bridge triage:
-- * source-facing: an `A`-valued class function whose values lie in the ideal `|G|A`.
-- * core/canonical owners: `classFunctionSubmodule A G` and
--   `Representation.cyclicInducedCharacterSpan A G`.
-- * bridge/view: the coefficientwise complexification `algebraMap A ℂ ∘ f`.
-- * primitive data: `f : classFunctionSubmodule A G` together with the pointwise ideal-membership
--   hypothesis.
-- * derived API: membership of the coefficientwise complexification in the cyclic induced-character
--   span.
--
-- Proof sketch: write each value of `f` as `(Nat.card G : A) * a_x` with `a_x ∈ A`, use the same
-- Brauer-induction argument as in Lemma `10-10.3-1` but with coefficients in the ideal
-- `(Nat.card G)A`, and then compose with `algebraMap A ℂ` coefficientwise to regard the
-- resulting class function as a complex-valued element of the `A`-span of characters induced from
-- cyclic subgroups.
/-- Exercise 10-10.3-4: an `A`-valued class function on `G`, packaged in the canonical owner
`classFunctionSubmodule A G`, whose values all lie in the ideal generated by `|G|` becomes,
after applying `algebraMap A ℂ` pointwise, an element of the `A`-span of characters induced from
cyclic subgroups of `G`. -/
theorem classFunction_complexification_mem_cyclicInducedCharacterSpan_of_groupOrder_mem_ideal
    (f : classFunctionSubmodule A G)
    (hf_mem_span : ∀ x : G, f x ∈ Ideal.span {(Nat.card G : A)}) :
    (algebraMap A ℂ ∘ f) ∈ cyclicInducedCharacterSpan A G := by
  classical
  obtain ⟨q, hq⟩ :=
    class_function_quotient_exists_of_groupOrder_mem_ideal (f := f) hf_mem_span
  let χ : _root_.classFunctionSubspace G :=
    complexified_classFunctionSubspace_of_classFunctionSubmodule q
  have hcomplexified_decomp :
      (algebraMap A ℂ ∘ f) =
        ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](fun h : H ↦ θ[H] h * χ h) := by
    -- Rewrite `algebraMap A ℂ ∘ f` as `|G| • χ`, then reuse the same cyclic-subgroup expansion
    -- of `|G| • 1` as in Lemma `10-10.3-1`.
    calc
      (algebraMap A ℂ ∘ f) = ((Nat.card G : ℂ) • (χ : G → ℂ)) := by
        ext x
        calc
          algebraMap A ℂ (f x) = algebraMap A ℂ ((Nat.card G : A) * q x) := by
            rw [hq x]
          _ = (Nat.card G : ℂ) * χ x := by
            simp [χ, complexified_classFunctionSubspace_of_classFunctionSubmodule, map_mul]
          _ = (((Nat.card G : ℂ) • (χ : G → ℂ)) x) := by
            simp
      _ = ((Nat.card G : ℂ) • (1 : G → ℂ)) * (χ : G → ℂ) := by
        ext x
        simp
      _ = (∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H])) * (χ : G → ℂ) := by
        rw [_root_.sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ)]
      _ = ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](fun h : H ↦ θ[H] h * χ h) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro H hH
        simpa using induced_mul_eq_induced_mul_restriction H (θ[H]) χ
  rw [hcomplexified_decomp]
  -- Each cyclic summand has values in `|H|A`, so the unresolved cyclic closing lemma applies.
  refine Submodule.sum_mem (Representation.cyclicInducedCharacterSpan A G) ?_
  intro H hH
  refine cyclic_card_mul_function_induced_mem_cyclicInducedCharacterSpan (A := A) H
    (Subgroup.mem_cyclicSubgroups.1 hH) (fun h : H ↦ θ[H] h * χ h) ?_
  intro h
  by_cases hh : Subgroup.zpowers h = ⊤
  · refine ⟨q h, ?_⟩
    simp [χ, complexified_classFunctionSubspace_of_classFunctionSubmodule,
      Representation.cyclicGroupTheta, hh, map_mul]
  · refine ⟨0, ?_⟩
    simp [χ, complexified_classFunctionSubspace_of_classFunctionSubmodule,
      Representation.cyclicGroupTheta, hh]

end
