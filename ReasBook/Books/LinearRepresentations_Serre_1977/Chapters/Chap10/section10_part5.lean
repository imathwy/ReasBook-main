import Mathlib
import Mathlib.Data.ZMod.QuotientRing

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_10_3_1 (from Chap10) -/
open scoped BigOperators Representation SubgroupInduction

noncomputable section

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type} [CommRing A] [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]

attribute [local instance] Fintype.ofFinite

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's divisibility criterion for a bundled class function on `G`.
-- * core/canonical owner for the bundled complex class function: `classFunctionSubspace G`.
-- * bridge/view: `cyclicInducedCharacterSpan A G` as the target ambient `A`-submodule of
--   `G → ℂ`.
-- * primitive data: `φ : classFunctionSubspace G` and the pointwise divisibility hypothesis.
-- * derived API: membership of `φ` in the cyclic induced-character span.

/-- Helper for Lemma 10-10.3-1: on a commutative group, every function is a class function. -/
lemma isClassFunction_of_commGroup
    {H : Type} [CommGroup H] {f : H → ℂ} : _root_.IsClassFunction f := by
  refine ⟨?_⟩
  intro x y hxy
  rcases ConjClasses.mk_eq_mk_iff_isConj.mp hxy with ⟨c, hc⟩
  apply congrArg f
  simpa [mul_comm, mul_left_comm, mul_assoc] using hc

/-- Helper for Lemma 10-10.3-1: multiplying an induced class function by a global class function
amounts to inducing the product with the restriction. -/
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
  · -- Compare the two summands after replacing `χ x` with the conjugacy-invariant value
    -- `χ (s⁻¹ * x * s)`.
    have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hχ : χ (s⁻¹ * x * s) = χ x := by
      exact (χ.2 : _root_.IsClassFunction (χ : G → ℂ)).eq_of_isConj <|
        isConj_iff.2 ⟨s, by group⟩
    have hχ' : χ (s⁻¹ * (x * s)) = χ x := by
      simpa [mul_assoc] using hχ
    simp [hs', hχ', mul_comm, mul_assoc]
  · simp [hs]

/-- Helper for Lemma 10-10.3-1: scaling by `|G|⁻¹` turns a `|G|`-divisible class function into an
integer-valued one. -/
lemma scaled_classFunction_integer_valued
    (φ : _root_.classFunctionSubspace G)
    (hdiv : ∀ x, ∃ n : ℤ, φ x = ((Nat.card G : ℤ) * n : ℂ)) :
    ∀ x : G, ∃ n : ℤ, (((Nat.card G : ℂ)⁻¹ • φ : _root_.classFunctionSubspace G) x) = (n : ℂ) := by
  intro x
  rcases hdiv x with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  -- Cancel the nonzero factor `|G|` after rewriting `φ x` with the divisibility hypothesis.
  calc
    (((Nat.card G : ℂ)⁻¹ • φ : _root_.classFunctionSubspace G) x)
        = (Nat.card G : ℂ)⁻¹ * (((Nat.card G : ℤ) * n : ℂ)) := by
            simp [hn]
    _ = (n : ℂ) := by
          field_simp [hcard]
          ac_rfl

/-- Helper for Lemma 10-10.3-1: multiplying LinearRepresentations_Serre_1977's `θ[H]` by an integer-valued function produces
values divisible by `|H|`. -/
lemma theta_mul_integer_function_dvd_subgroup_order
    (H : Subgroup G) (η : G → ℂ)
    (hη : ∀ g : G, ∃ n : ℤ, η g = (n : ℂ)) :
    ∀ h : H, ∃ n : ℤ, θ[H] h * η h = ((Nat.card H : ℤ) * n : ℂ) := by
  intro h
  by_cases hh : Subgroup.zpowers h = ⊤
  · rcases hη h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simp [Representation.cyclicGroupTheta, hh, hn]
  · refine ⟨0, ?_⟩
    simp [Representation.cyclicGroupTheta, hh]

/-- Helper for Lemma 10-10.3-1: a finite commutative group has finitely many complex linear
characters. -/
local instance linearCharacterFinite
    {B : Type} [CommGroup B] [Finite B] :
    Finite (B →* ℂˣ) := by
  let eDual : (B →* ℂˣ) ≃* B :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G := B) (M := ℂ))
  exact Finite.of_equiv B eDual.symm.toEquiv

/-- Helper for Lemma 10-10.3-1: the linear characters of a finite commutative group form a finite
type. -/
local instance linearCharacterFintype
    {B : Type} [CommGroup B] [Finite B] :
    Fintype (B →* ℂˣ) := Fintype.ofFinite (B →* ℂˣ)

/-- Helper for Lemma 10-10.3-1: the character of a permutation representation counts fixed
points. -/
lemma of_mulAction_character_eq_ncard_fixedBy_local
    {B : Type} [Group B] {X : Type} [MulAction B X] [Finite X] (s : B) :
    (Representation.ofMulAction ℂ B X).character s = ↑(MulAction.fixedBy X s).ncard := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  calc
    (Representation.ofMulAction ℂ B X).character s
        = Matrix.trace
            (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
              ((Representation.ofMulAction ℂ B X) s)) := by
              rw [Representation.character,
                LinearMap.trace_eq_matrix_trace ℂ Finsupp.basisSingleOne]
    _ = ∑ x : X, if s • x = x then 1 else 0 := by
          simp [Matrix.trace, LinearMap.toMatrix_apply, Representation.ofMulAction_single,
            Finsupp.single_apply]
    _ = ↑((Finset.univ.filter fun x : X ↦ s • x = x).card) := by
          simp
    _ = ↑((MulAction.fixedBy X s).toFinset.card) := by
          congr
          ext x
          simp [MulAction.mem_fixedBy]
    _ = ↑(MulAction.fixedBy X s).ncard := by
          rw [← Set.ncard_eq_toFinset_card']

/-- Helper for Lemma 10-10.3-1: a nonidentity element fixes no point in the left regular action. -/
lemma leftRegular_fixedBy_eq_empty_of_ne_one_local
    {B : Type} [Group B] {s : B} (hs : s ≠ 1) :
    MulAction.fixedBy B s = ∅ := by
  -- A fixed point for left multiplication forces `s = 1` by right cancellation.
  rw [Set.eq_empty_iff_forall_notMem]
  intro b hb
  have hmul : s * b = b := by
    simpa [MulAction.mem_fixedBy] using hb
  have hs' : s = 1 := by
    rwa [mul_eq_right] at hmul
  exact hs hs'

/-- Helper for Lemma 10-10.3-1: the regular character takes the value `|B|` at the identity. -/
lemma leftRegular_character_one_local
    {B : Type} [Group B] [Finite B] :
    (Representation.leftRegular ℂ B).character (1 : B) = ↑(Nat.card B) := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  rw [of_mulAction_character_eq_ncard_fixedBy_local]
  simp [MulAction.fixedBy_one_eq_univ]

/-- Helper for Lemma 10-10.3-1: the regular character vanishes away from the identity. -/
lemma leftRegular_character_eq_zero_of_ne_one_local
    {B : Type} [Group B] [Finite B] {s : B} (hs : s ≠ 1) :
    (Representation.leftRegular ℂ B).character s = 0 := by
  classical
  rw [of_mulAction_character_eq_ncard_fixedBy_local,
    leftRegular_fixedBy_eq_empty_of_ne_one_local hs]
  simp

/-- Helper for Lemma 10-10.3-1: on a finite commutative group, the sum of all linear characters
vanishes away from the identity. -/
lemma commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one
    {B : Type} [CommGroup B] [Finite B] {b : B} (hb : b ≠ 1) :
    ∑ χ : B →* ℂˣ, (χ b : ℂ) = 0 := by
  classical
  obtain ⟨φ, hφb⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G := B) (M := ℂ) hb
  let e : (B →* ℂˣ) ≃ (B →* ℂˣ) :=
    { toFun := fun χ ↦ φ * χ
      invFun := fun χ ↦ φ⁻¹ * χ
      left_inv := by
        intro χ
        simp
      right_inv := by
        intro χ
        simp }
  have hsum :
      ∑ χ : B →* ℂˣ, ((φ * χ) b : ℂ) =
        ∑ χ : B →* ℂˣ, (χ b : ℂ) := by
    exact Fintype.sum_equiv e
      (fun χ : B →* ℂˣ ↦ ((φ * χ) b : ℂ))
      (fun χ : B →* ℂˣ ↦ (χ b : ℂ))
      (fun χ ↦ rfl)
  have hmul :
      ∑ χ : B →* ℂˣ, ((φ * χ) b : ℂ) =
        (φ b : ℂ) * ∑ χ : B →* ℂˣ, (χ b : ℂ) := by
    -- Pull the fixed linear-character value `φ(b)` out of the finite sum.
    simp [Finset.mul_sum]
  have hfactor :
      (((φ b : ℂ) - 1) * ∑ χ : B →* ℂˣ, (χ b : ℂ)) = 0 := by
    -- Compare the invariant sum with its translate by the nontrivial character `φ`.
    calc
      (((φ b : ℂ) - 1) * ∑ χ : B →* ℂˣ, (χ b : ℂ)) =
          (φ b : ℂ) * ∑ χ : B →* ℂˣ, (χ b : ℂ) -
            ∑ χ : B →* ℂˣ, (χ b : ℂ) := by
              ring
      _ = 0 := by
            rw [← hmul, hsum, sub_self]
  have hne : ((φ b : ℂ) - 1) ≠ 0 := by
    intro hzero
    have hcast : (φ b : ℂ) = 1 := sub_eq_zero.mp hzero
    apply hφb
    ext
    simpa using hcast
  exact (mul_eq_zero.mp hfactor).resolve_left hne

/-- Helper for Lemma 10-10.3-1: the regular character of a finite commutative group is the sum of
all of its linear characters. -/
lemma commGroup_regularCharacter_eq_sum_linearCharacters
    {B : Type} [CommGroup B] [Finite B] :
    (Representation.leftRegular ℂ B).character =
      ∑ χ : B →* ℂˣ, χ.toRepresentation.character := by
  ext b
  by_cases hb : b = 1
  · subst hb
    -- At the identity, every linear character has value `1`, so only the number of characters
    -- matters.
    have hleft :
        (Representation.leftRegular ℂ B).character (1 : B) = (Nat.card B : ℂ) := by
      simpa using leftRegular_character_one_local (B := B)
    rw [hleft, Finset.sum_apply]
    have hcard : Fintype.card B = Fintype.card (B →* ℂˣ) := by
      simpa using
        (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (G := B) (M := ℂ)).symm
    simp [hcard]
  · -- Away from the identity, the translation argument forces the total character sum to vanish.
    have hleft :
        (Representation.leftRegular ℂ B).character b = 0 := by
      exact leftRegular_character_eq_zero_of_ne_one_local (B := B) hb
    rw [hleft, Finset.sum_apply]
    simpa using
      (commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one (B := B) hb).symm

/-- Helper for Lemma 10-10.3-1: a linear character value is integral over `ℤ` because it is a
root of unity. -/
lemma linear_character_value_isIntegral
    {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (h : H) :
    IsIntegral ℤ ((χ h : ℂ)) := by
  apply IsIntegral.of_pow (n := orderOf h)
  · exact orderOf_pos h
  · rw [show ((χ h : ℂ) ^ orderOf h) = 1 by
      have hpowUnits : (χ h) ^ orderOf h = 1 := by
        rw [← map_pow]
        simp [pow_orderOf_eq_one h]
      exact congrArg (fun z : ℂˣ => (z : ℂ)) hpowUnits]
    exact isIntegral_one

/-- Helper for Lemma 10-10.3-1: a class function whose values are divisible by the group order has
integral pairings with every linear character, hence those pairings lie in the integral closure
ring `A`. -/
lemma linear_character_pairing_mem_range_of_card_dvd_values
    {H : Type} [Group H] [Finite H]
    (φ : _root_.classFunctionSubspace H)
    (hdiv : ∀ h : H, ∃ n : ℤ, φ h = ((Nat.card H : ℤ) * n : ℂ))
    (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing, φ⟫ ∈ Set.range (algebraMap A ℂ) := by
  let n : H → ℤ := fun h ↦ Classical.choose (hdiv h)
  have hn : ∀ h : H, φ h = ((Nat.card H : ℤ) * n h : ℂ) := by
    intro h
    exact Classical.choose_spec (hdiv h)
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hpair :
      ⟪χ.toCharacterRing, φ⟫ = ∑ t : H, (χ t⁻¹ : ℂ) * (n t : ℂ) := by
    -- Rewrite the normalized pairing so the factor `|H|⁻¹` cancels against the divisibility
    -- built into `hdiv`.
    rw [Representation.groupFunctionPairingOverField]
    calc
      (Fintype.card H : ℂ)⁻¹ * ∑ t : H, (χ.toCharacterRing : H → ℂ) t⁻¹ * φ t
          = (Fintype.card H : ℂ)⁻¹ *
              ∑ t : H, (χ t⁻¹ : ℂ) * (((Fintype.card H : ℤ) * n t : ℂ)) := by
              congr 1
              refine Fintype.sum_congr (fun t : H ↦ (χ.toCharacterRing : H → ℂ) t⁻¹ * φ t)
                (fun t : H ↦ (χ t⁻¹ : ℂ) * (((Fintype.card H : ℤ) * n t : ℂ))) ?_
              intro t
              simpa [Nat.card_eq_fintype_card] using
                congrArg (fun z : ℂ => (χ t⁻¹ : ℂ) * z) (hn t)
      _ = ∑ t : H, (χ t⁻¹ : ℂ) * (n t : ℂ) := by
            rw [Finset.mul_sum]
            refine Fintype.sum_congr
              (fun t : H ↦ (Fintype.card H : ℂ)⁻¹ *
                ((χ t⁻¹ : ℂ) * (((Fintype.card H : ℤ) * n t : ℂ))))
              (fun t : H ↦ (χ t⁻¹ : ℂ) * (n t : ℂ)) ?_
            intro t
            field_simp [hcard]
            ac_rfl
  have hsum : IsIntegral ℤ (∑ t : H, (χ t⁻¹ : ℂ) * (n t : ℂ)) := by
    -- Each summand is a product of an algebraic-integer root of unity with an ordinary integer.
    refine IsIntegral.sum (s := Finset.univ) (fun t : H ↦ (χ t⁻¹ : ℂ) * (n t : ℂ)) ?_
    intro t ht
    exact IsIntegral.mul (linear_character_value_isIntegral χ t⁻¹) isIntegral_algebraMap
  exact (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).1 (hpair ▸ hsum)

/-- Helper for Lemma 10-10.3-1: on a finite cyclic group, the `|H|`-weighted delta function at a
point is an `A`-linear combination of linear characters. -/
lemma exists_weighted_delta_linear_character_expansion
    {B : Type} [CommGroup B] [Finite B] [DecidableEq B] (u : B) :
    ∃ coeff : (B →* ℂˣ) → A,
    (fun h : B ↦ if u = h then (Nat.card B : ℂ) else 0) =
        ∑ χ : B →* ℂˣ, coeff χ • χ.toRepresentation.character := by
  classical
  let coeff : (B →* ℂˣ) → A := fun χ ↦
    Classical.choose <|
      (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).1
        (linear_character_value_isIntegral χ u⁻¹)
  have hcoeff : ∀ χ : B →* ℂˣ, algebraMap A ℂ (coeff χ) = (χ u⁻¹ : ℂ) := by
    intro χ
    exact Classical.choose_spec <|
      (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).1
        (linear_character_value_isIntegral χ u⁻¹)
  refine ⟨coeff, ?_⟩
  ext h
  calc
    (fun x : B ↦ if u = x then (Nat.card B : ℂ) else 0) h
        = (Representation.leftRegular ℂ B).character (u⁻¹ * h) := by
            by_cases hu : u = h
            · subst hu
              simpa using leftRegular_character_one_local (B := B)
            · have hne : u⁻¹ * h ≠ 1 := by
                intro h1
                apply hu
                have hm := congrArg (fun t : B ↦ u * t) h1
                simpa [mul_assoc] using hm.symm
              simpa [hu] using
                (leftRegular_character_eq_zero_of_ne_one_local (B := B) hne).symm
    _ = ∑ χ : B →* ℂˣ, (χ (u⁻¹ * h) : ℂ) := by
          simpa [Finset.sum_apply] using
            congrArg (fun φ : B → ℂ => φ (u⁻¹ * h))
              (commGroup_regularCharacter_eq_sum_linearCharacters (B := B))
    _ = (∑ χ : B →* ℂˣ, coeff χ • χ.toRepresentation.character) h := by
          simp [Finset.sum_apply, hcoeff, Algebra.smul_def, map_mul, mul_assoc]

/-- Helper for Lemma 10-10.3-1: inducing a `|H|`-weighted delta function from a cyclic subgroup
lands in the cyclic induced-character span. -/
lemma weighted_delta_induced_mem_cyclicInducedCharacterSpan
    (H : Subgroup G) (hH : IsCyclic H) [DecidableEq H] (u : H) :
    Ind[H](fun h : H ↦ if u = h then (Nat.card H : ℂ) else 0) ∈
      Representation.cyclicInducedCharacterSpan A G := by
  classical
  letI : CommGroup H := IsCyclic.commGroup
  obtain ⟨coeff, hcoeff⟩ :=
    exists_weighted_delta_linear_character_expansion (A := A) (B := H) u
  -- Expand the weighted delta function into linear characters and induce termwise.
  have hsum :
      ∀ s : Finset (H →* ℂˣ),
        Ind[H](s.sum fun χ ↦ coeff χ • χ.toRepresentation.character) ∈
          Representation.cyclicInducedCharacterSpan A G := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
          ext g
          simp [Subgroup.inducedClassFunction]
        simpa [hzero]
    | @insert χ s hχ hs =>
        have hχmem : Ind[H](coeff χ • χ.toRepresentation.character) ∈
            Representation.cyclicInducedCharacterSpan A G := by
          have hbase : Ind[H](χ.toRepresentation.character) ∈
              Representation.cyclicInducedCharacterSpan A G := by
            simpa using
              Representation.inducedClassFunction_mem_cyclicInducedCharacterSpan
                (A := A) H hH χ.toCharacterRing
          simpa [Subgroup.inducedClassFunction_map_smul] using
            (Representation.cyclicInducedCharacterSpan A G).smul_mem (coeff χ) hbase
        simpa [Finset.sum_insert, hχ, Subgroup.inducedClassFunction_map_add] using
          Submodule.add_mem (Representation.cyclicInducedCharacterSpan A G) hχmem hs
  rw [hcoeff]
  exact hsum Finset.univ

/-- Helper for Lemma 10-10.3-1: on a cyclic subgroup, a class function with values divisible by
that subgroup order is already an `A`-linear combination of linear characters, so its induction
lies in the cyclic induced-character span of `G`. -/
lemma cyclic_divisible_function_induced_mem_cyclicInducedCharacterSpan
    (H : Subgroup G) (hH : IsCyclic H) (f : H → ℂ)
    (hdiv : ∀ h : H, ∃ n : ℤ, f h = ((Nat.card H : ℤ) * n : ℂ)) :
    Ind[H](f) ∈ Representation.cyclicInducedCharacterSpan A G := by
  classical
  let n : H → ℤ := fun h ↦ Classical.choose (hdiv h)
  have hn : ∀ h : H, f h = ((Nat.card H : ℤ) * n h : ℂ) := by
    intro h
    exact Classical.choose_spec (hdiv h)
  let δ : H → H → ℂ := fun u h ↦ if u = h then (Nat.card H : ℂ) else 0
  have hdecomp :
      f = ∑ u : H, (n u : A) • δ u := by
    ext h
    -- Decompose `f` into its weighted delta functions, one for each subgroup element.
    calc
      f h = ((Nat.card H : ℤ) * n h : ℂ) := hn h
      _ = (algebraMap A ℂ (n h : A)) * (Nat.card H : ℂ) := by
            simp [Nat.cast_mul, mul_comm]
      _ = ∑ u : H, (algebraMap A ℂ (n u : A)) * δ u h := by
            simp [δ]
      _ = (∑ u : H, (n u : A) • δ u) h := by
            simp [δ, Pi.smul_apply, Algebra.smul_def, mul_assoc]
  -- Route correction: replace the blocked basis argument by the explicit weighted-delta expansion
  -- coming from the regular character decomposition on the cyclic subgroup `H`.
  have hsum :
      ∀ s : Finset H,
        Ind[H](s.sum fun u ↦ (n u : A) • δ u) ∈
          Representation.cyclicInducedCharacterSpan A G := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
          ext g
          simp [Subgroup.inducedClassFunction]
        simpa [hzero]
    | @insert u s hu hs =>
        have hudelta : Ind[H](δ u) ∈ Representation.cyclicInducedCharacterSpan A G :=
          weighted_delta_induced_mem_cyclicInducedCharacterSpan
            (A := A) (H := H) hH (u := u)
        have husmul : Ind[H]((n u : A) • δ u) ∈
            Representation.cyclicInducedCharacterSpan A G := by
          simpa [Subgroup.inducedClassFunction_map_smul] using
            (Representation.cyclicInducedCharacterSpan A G).smul_mem (n u : A) hudelta
        simpa [Finset.sum_insert, hu, Subgroup.inducedClassFunction_map_add] using
          Submodule.add_mem (Representation.cyclicInducedCharacterSpan A G) husmul hs
  simpa [hdecomp] using hsum Finset.univ

-- Proof sketch: write `f = |G| χ` with `χ` integer-valued. Use Proposition `9-9.4-1` to express
-- the constant function `|G|` as a sum of the `Ind_C^G(θ_C)`, multiply by `χ`, and rewrite each
-- term as an induced class function from `C`. For cyclic `C`, the coefficients obtained by
-- pairing with irreducible characters are algebraic integers, so each restricted term is an
-- `A`-linear combination of characters of `C`; inducing up gives the required membership.
/-- Lemma 10-10.3-1: every complex-valued class function on `G`, packaged in the canonical owner
`classFunctionSubspace G`, whose values are integers divisible by `|G|` belongs to the `A`-span
of the characters induced from cyclic subgroups of `G`. -/
theorem classFunction_mem_cyclicInducedCharacterSpan_of_groupOrder_dvd_values
    (φ : _root_.classFunctionSubspace G)
    (hdiv : ∀ x, ∃ n : ℤ, φ x = ((Nat.card G : ℤ) * n : ℂ)) :
    (φ : G → ℂ) ∈ Representation.cyclicInducedCharacterSpan A G := by
  let χ : _root_.classFunctionSubspace G := (Nat.card G : ℂ)⁻¹ • φ
  have hχ_int : ∀ x : G, ∃ n : ℤ, χ x = (n : ℂ) :=
    scaled_classFunction_integer_valued φ hdiv
  have hφ_decomp :
      (φ : G → ℂ) =
        ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](fun h : H ↦ θ[H] h * χ h) := by
    -- Rewrite `φ = |G| • χ` and then expand `|G| • 1` using Proposition `9-9.4-1`.
    calc
      (φ : G → ℂ) = ((Nat.card G : ℂ) • (χ : G → ℂ)) := by
        ext x
        rcases hχ_int x with ⟨n, hn⟩
        simp [χ]
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
  rw [hφ_decomp]
  refine Submodule.sum_mem (Representation.cyclicInducedCharacterSpan A G) ?_
  intro H hH
  exact cyclic_divisible_function_induced_mem_cyclicInducedCharacterSpan (A := A) H
    (Subgroup.mem_cyclicSubgroups.1 hH)
    (fun h : H ↦ θ[H] h * χ h)
    (theta_mul_integer_function_dvd_subgroup_order H (χ : G → ℂ) hχ_int)

end

end

/-! ### Lemma_10_10_3_2 (from Chap10) -/
open Representation
open scoped Representation
open IsLocalization

universe u v

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]
variable {p : ℕ} [Fact p.Prime]

attribute [local instance] Fintype.ofFinite

local instance : CoeFun ↥(characterRingScalarExtension A G) (fun _ ↦ G → ℂ) where
  coe χ := χ.1

/-- Helper for Lemma 10-10.3-2: on the cyclic subgroup generated by `x`, we work with the degree-1
complex characters `H →* ℂˣ` through their values in `H → ℂ`. -/
def linearCharacterFunctions (H : Type u) [Group H] [Finite H] : Set (H → ℂ) :=
  Set.range fun ρ : H →* ℂˣ ↦ (ρ.toCharacterRing : H → ℂ)

/-- Helper for Lemma 10-10.3-2: each degree-1 character lies in the `ℤ`-span generated by all
degree-1 characters. -/
theorem linearCharacter_mem_span
    {H : Type u} [Group H] [Finite H] (ρ : H →* ℂˣ) :
    (ρ.toCharacterRing : H → ℂ) ∈ Submodule.span ℤ (linearCharacterFunctions H) :=
  Submodule.subset_span ⟨ρ, rfl⟩

/-- Helper for Lemma 10-10.3-2: a sufficiently large power of `p` kills the `p`-unipotent part,
so `x` and its `p'`-component have the same `p^k`th power. -/
theorem exists_p_power_eq_pRegularComponent_pow (x : G) :
    ∃ k : ℕ, x ^ (p ^ k) = (pRegularComponent p x) ^ (p ^ k) := by
  let hdecomp :=
    p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)
  rcases hdecomp.isPElement with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hpowu : (pUnipotentComponent p x) ^ (p ^ k) = 1 := by
    simpa [hk] using pow_orderOf_eq_one (pUnipotentComponent p x)
  -- Raising the canonical commuting decomposition to `p^k` kills the `p`-part.
  calc
    x ^ (p ^ k) = ((pUnipotentComponent p x) * (pRegularComponent p x)) ^ (p ^ k) := by
      exact congrArg (fun g : G ↦ g ^ (p ^ k)) hdecomp.eq_mul
    _ = (pUnipotentComponent p x) ^ (p ^ k) * (pRegularComponent p x) ^ (p ^ k) := by
      rw [hdecomp.commute.mul_pow]
    _ = (pRegularComponent p x) ^ (p ^ k) := by
      rw [hpowu, one_mul]

/-- Helper for Lemma 10-10.3-2: quotient equality of the `p^k`th powers of two integer values
forces congruence modulo `p` of the original integers. -/
theorem int_modEq_of_qpow_quotient_eq_mod_p
    (m n : ℤ) (k : ℕ)
    (h : Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((m : A) ^ (p ^ k)) =
      Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((n : A) ^ (p ^ k))) :
    m ≡ n [ZMOD p] := by
  let q : ℕ := p ^ k
  let d : ℤ := m ^ q - n ^ q
  -- Read the quotient equality as divisibility of the difference by `p` inside `A`.
  have hmem : ((m : A) ^ q - (n : A) ^ q) ∈ Ideal.span ({(p : A)} : Set A) := by
    simpa [q] using (Ideal.Quotient.eq.mp h)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  -- Move the divisibility relation to `ℂ`, where the witness is visibly the rational number
  -- `(m^q - n^q) / p`.
  have haC : (d : ℂ) = p * algebraMap A ℂ a := by
    have haA : ((d : ℤ) : A) = a * (p : A) := by
      calc
        (((d : ℤ) : A)) = (m : A) ^ q - (n : A) ^ q := by
          simp [d]
        _ = a * (p : A) := by
          simpa using ha.symm
    have haC' := congrArg (algebraMap A ℂ) haA
    simpa [d, map_mul, mul_comm] using haC'
  have hintC : IsIntegral ℤ (algebraMap A ℂ a) := by
    exact (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).2 ⟨a, rfl⟩
  have hintQ : IsIntegral ℤ (((d : ℤ) : ℚ) / p) := by
    have hpC : (p : ℂ) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hqC : algebraMap ℚ ℂ (((d : ℤ) : ℚ) / p) = algebraMap A ℂ a := by
      calc
        algebraMap ℚ ℂ (((d : ℤ) : ℚ) / p) = ((d : ℂ) / p) := by
          norm_num [Rat.cast_def]
        _ = algebraMap A ℂ a := by
          exact (div_eq_iff hpC).2 (by simpa [mul_comm] using haC)
    exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp <| by
      rw [hqC]
      exact hintC
  -- Since `(m^q - n^q) / p` is an integer, the difference is divisible by `p` in `ℤ`.
  have hdiv : (p : ℤ) ∣ d := by
    rcases (show ∃ z : ℤ, algebraMap ℤ ℚ z = (((d : ℤ) : ℚ) / p) by
      simpa [IsLocalization.IsInteger] using UniqueFactorizationMonoid.integer_of_integral hintQ)
      with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hpq : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hzmul := congrArg (fun x : ℚ ↦ x * p) hz
    field_simp [hpq] at hzmul
    have hz' : (d : ℚ) = p * z := by
      simpa [mul_comm] using hzmul.symm
    exact_mod_cast hz'
  -- Pass the divisibility statement to `ZMod p`, where Frobenius `x ↦ x^(p^k)` is the identity.
  have hpow : ((m : ZMod p) ^ q) = ((n : ZMod p) ^ q) := by
    have hdiv' : (p : ℤ) ∣ -d := Int.dvd_neg.mpr hdiv
    have hdiv'' : (p : ℤ) ∣ (n ^ q - m ^ q : ℤ) := by
      simpa [d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiv'
    simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub (m ^ q) (n ^ q) p).2 hdiv''
  have hm : (m : ZMod p) ^ q = (m : ZMod p) := by
    simp [q, ZMod.pow_card_pow]
  have hn : (n : ZMod p) ^ q = (n : ZMod p) := by
    simp [q, ZMod.pow_card_pow]
  rw [hm, hn] at hpow
  exact (ZMod.intCast_eq_intCast_iff m n p).mp hpow

/-- Helper for Lemma 10-10.3-2: a degree-`1` character takes equal `p^k`th powers at two group
elements with the same `p^k`th power, so any chosen integer values at those points have equal
`p^k`th powers in the quotient by `(p)`. -/
theorem linear_character_qpow_quotient_eq_of_pow_eq
    {H : Type u} [Group H] [Finite H]
    (ρ : H →* ℂˣ) {y z : H} {m n : ℤ} {k : ℕ}
    (hm : (ρ.toCharacterRing : H → ℂ) y = (m : ℂ))
    (hn : (ρ.toCharacterRing : H → ℂ) z = (n : ℂ))
    (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((m : A) ^ (p ^ k)) =
      Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((n : A) ^ (p ^ k)) := by
  have hy :
      ((ρ.toCharacterRing : H → ℂ) y) ^ (p ^ k) =
        (ρ.toCharacterRing : H → ℂ) (y ^ (p ^ k)) := by
    simpa using congrArg (fun u : ℂˣ ↦ (u : ℂ)) (ρ.map_pow y (p ^ k)).symm
  have hz :
      ((ρ.toCharacterRing : H → ℂ) z) ^ (p ^ k) =
        (ρ.toCharacterRing : H → ℂ) (z ^ (p ^ k)) := by
    simpa using congrArg (fun u : ℂˣ ↦ (u : ℂ)) (ρ.map_pow z (p ^ k)).symm
  -- The power map on a degree-`1` character converts the group-theoretic equality `y^q = z^q`
  -- into equality of the corresponding integer `q`th powers in `ℂ`.
  have hpowC : ((m : ℂ) ^ (p ^ k)) = ((n : ℂ) ^ (p ^ k)) := by
    calc
      (m : ℂ) ^ (p ^ k) = ((ρ.toCharacterRing : H → ℂ) y) ^ (p ^ k) := by
        rw [hm]
      _ = (ρ.toCharacterRing : H → ℂ) (y ^ (p ^ k)) := hy
      _ = (ρ.toCharacterRing : H → ℂ) (z ^ (p ^ k)) := by
        simpa [hpow]
      _ = ((ρ.toCharacterRing : H → ℂ) z) ^ (p ^ k) := hz.symm
      _ = (n : ℂ) ^ (p ^ k) := by
        rw [hn]
  have hpowZ : m ^ (p ^ k) = n ^ (p ^ k) := by
    exact_mod_cast hpowC
  have hpowA : ((m : A) ^ (p ^ k)) = ((n : A) ^ (p ^ k)) := by
    simpa using congrArg (fun t : ℤ ↦ (t : A)) hpowZ
  simpa [hpowA]

/-- Helper for Lemma 10-10.3-2: the principal-ideal quotient `A ⧸ (p)` has characteristic `p`
because `p` is not a unit in an integral closure of `ℤ` inside `ℂ`. -/
theorem quotient_span_prime_charP :
    CharP (A ⧸ Ideal.span ({(p : A)} : Set A)) p := by
  have hp_nonunit : ¬ IsUnit (p : A) := by
    intro hp_unit
    rcases hp_unit with ⟨u, hu⟩
    let a : A := ↑u⁻¹
    have ha_mul : a * (p : A) = 1 := by
      calc
        a * (p : A) = (↑u⁻¹ : A) * ↑u := by
          rw [hu]
        _ = 1 := by
          simp
    -- If `p` were invertible in `A`, then `1 / p` would be an algebraic integer.
    have hmap : algebraMap A ℂ a * p = 1 := by
      simpa [map_mul] using congrArg (algebraMap A ℂ) ha_mul
    have hEq : algebraMap ℚ ℂ (((1 : ℤ) : ℚ) / p) = algebraMap A ℂ a := by
      have hpC : (p : ℂ) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      calc
        algebraMap ℚ ℂ (((1 : ℤ) : ℚ) / p) = (1 : ℂ) / p := by
          norm_num [Rat.cast_def]
        _ = algebraMap A ℂ a := by
          exact (div_eq_iff hpC).2 hmap.symm
    have hintC : IsIntegral ℤ (algebraMap A ℂ a) := by
      exact (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).2 ⟨a, rfl⟩
    have hintQ : IsIntegral ℤ ((((1 : ℤ) : ℚ) / p)) := by
      exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp <| by
        rw [hEq]
        exact hintC
    rcases (show ∃ z : ℤ, algebraMap ℤ ℚ z = (((1 : ℤ) : ℚ) / p) by
        simpa [IsLocalization.IsInteger] using UniqueFactorizationMonoid.integer_of_integral hintQ)
      with ⟨z, hz⟩
    have hpq : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hzmul := congrArg (fun x : ℚ ↦ x * p) hz
    field_simp [hpq] at hzmul
    have hz' : (1 : ℚ) = p * z := by
      simpa [mul_comm] using hzmul.symm
    have hdiv : (p : ℤ) ∣ 1 := by
      refine ⟨z, ?_⟩
      exact_mod_cast hz'
    have hdivNat : p ∣ 1 := by
      exact_mod_cast hdiv
    exact (Fact.out : Nat.Prime p).not_dvd_one hdivNat
  exact CharP.quotient A p (by simpa using hp_nonunit)

/-- Helper for Lemma 10-10.3-2: an irreducible complex character of a finite cyclic group comes
from a degree-`1` character. -/
theorem exists_linear_character_of_irreducible_rep
    {H : Type u} [Group H] [Finite H] [IsCyclic H]
    (ρ : Rep ℂ H) [FiniteDimensional ℂ ρ] [ρ.ρ.IsIrreducible] :
    ∃ α : H →* ℂˣ, ρ.ρ.character = α.toRepresentation.character := by
  letI : CommGroup H := IsCyclic.commGroup
  have hdim : Module.finrank ℂ ρ = 1 := by
    simpa using Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ.ρ
  let scalarEquiv : ℂ ≃ₗ[ℂ] (ρ →ₗ[ℂ] ρ) :=
    LinearEquiv.smul_id_of_finrank_eq_one hdim
  have hscalar (c : ℂ) : scalarEquiv c = c • LinearMap.id :=
    LinearEquiv.smul_id_of_finrank_eq_one_apply hdim c
  let α₀ : H → ℂ := fun h ↦ scalarEquiv.symm (ρ.ρ h)
  have hα₀_eq (h : H) : ρ.ρ h = α₀ h • LinearMap.id := by
    calc
      ρ.ρ h = scalarEquiv (α₀ h) := by
        simp [α₀]
      _ = α₀ h • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    have hscalar1 : scalarEquiv (1 : ℂ) = (1 : ρ →ₗ[ℂ] ρ) := by
      simpa using hscalar (1 : ℂ)
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = ρ.ρ 1 := by
        simp [α₀]
      _ = (1 : ρ →ₗ[ℂ] ρ) := by
        simp
      _ = scalarEquiv 1 := hscalar1.symm
  have hα₀_mul (h₁ h₂ : H) : α₀ (h₁ * h₂) = α₀ h₁ * α₀ h₂ := by
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (h₁ * h₂)) = ρ.ρ (h₁ * h₂) := by
        simp [α₀]
      _ = ρ.ρ h₁ * ρ.ρ h₂ := by
        simp
      _ = (α₀ h₁ * α₀ h₂) • LinearMap.id := by
        rw [hα₀_eq, hα₀_eq]
        ext x
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ h₁ * α₀ h₂) := (hscalar _).symm
  have hα₀_ne_zero (h : H) : α₀ h ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ ρ := by
      simpa [hdim]
    letI : Nontrivial ρ := Module.nontrivial_of_finrank_pos hpos
    intro hzero
    have hzeroMap : ρ.ρ h = 0 := by
      simp [hα₀_eq, hzero]
    have hmul : ρ.ρ h * ρ.ρ h⁻¹ = (1 : ρ →ₗ[ℂ] ρ) := by
      simpa using (ρ.ρ.map_mul h h⁻¹).symm
    have hone : (1 : ρ →ₗ[ℂ] ρ) ≠ 0 := one_ne_zero
    have hidzero : (1 : ρ →ₗ[ℂ] ρ) = 0 := by
      calc
        (1 : ρ →ₗ[ℂ] ρ) = ρ.ρ h * ρ.ρ h⁻¹ := hmul.symm
        _ = 0 := by
          rw [hzeroMap]
          simp
    exact hone hidzero
  let α : H →* ℂˣ :=
    { toFun := fun h ↦ Units.mk0 (α₀ h) (hα₀_ne_zero h)
      map_one' := by
        ext
        simpa using hα₀_one
      map_mul' h₁ h₂ := by
        ext
        simpa using hα₀_mul h₁ h₂ }
  -- Re-express the irreducible character through the resulting degree-`1` character.
  refine ⟨α, ?_⟩
  ext h
  rw [MonoidHom.toRepresentation_character_apply, Representation.character, hα₀_eq]
  simp [hdim, α]

/-- Helper for Lemma 10-10.3-2: a degree-`1` character has lift values in `A` whose `p^k`th
powers agree whenever the underlying group elements have the same `p^k`th power. -/
theorem exists_lifts_of_linear_character_values_with_pow_eq
    {H : Type u} [Group H] [Finite H]
    (ρ : H →* ℂˣ) {y z : H} {k : ℕ}
    (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = (ρ y : ℂ) ∧
      algebraMap A ℂ az = (ρ z : ℂ) ∧
      ay ^ (p ^ k) = az ^ (p ^ k) := by
  -- The values of a linear character are roots of unity, hence algebraic integers, so they lift
  -- to `A` by the integral-closure hypothesis.
  have hyInt : IsIntegral ℤ ((ρ y : ℂ)) := by
    apply IsIntegral.of_pow (n := orderOf y)
    · exact orderOf_pos y
    · rw [show ((ρ y : ℂ) ^ orderOf y) = 1 by
        have hpowUnits : (ρ y) ^ orderOf y = 1 := by
          rw [← map_pow]
          simp [pow_orderOf_eq_one y]
        exact congrArg (fun w : ℂˣ ↦ (w : ℂ)) hpowUnits]
      exact isIntegral_one
  have hzInt : IsIntegral ℤ ((ρ z : ℂ)) := by
    apply IsIntegral.of_pow (n := orderOf z)
    · exact orderOf_pos z
    · rw [show ((ρ z : ℂ) ^ orderOf z) = 1 by
        have hpowUnits : (ρ z) ^ orderOf z = 1 := by
          rw [← map_pow]
          simp [pow_orderOf_eq_one z]
        exact congrArg (fun w : ℂˣ ↦ (w : ℂ)) hpowUnits]
      exact isIntegral_one
  obtain ⟨ay, hay⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).1 hyInt
  obtain ⟨az, haz⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).1 hzInt
  refine ⟨ay, az, hay, haz, ?_⟩
  -- The group-theoretic equality of `p^k`th powers transfers to the chosen lifts.
  let h_inj : Function.Injective (algebraMap A ℂ) :=
    IsIntegralClosure.algebraMap_injective A ℤ ℂ
  apply h_inj
  calc
    algebraMap A ℂ (ay ^ (p ^ k)) = (ρ y : ℂ) ^ (p ^ k) := by
      rw [map_pow, hay]
    _ = (ρ (y ^ (p ^ k)) : ℂ) := by
      simp
    _ = (ρ (z ^ (p ^ k)) : ℂ) := by
      simp [hpow]
    _ = (ρ z : ℂ) ^ (p ^ k) := by
      simp
    _ = algebraMap A ℂ (az ^ (p ^ k)) := by
      rw [map_pow, haz]

/-- Helper for Lemma 10-10.3-2: on a finite cyclic group, every ordinary character admits lifts at
`y` and `z` whose `p^k`th powers agree modulo `(p)` once `y^(p^k) = z^(p^k)`. -/
theorem cyclic_character_qpow_quotient_eq
    {H : Type u} [Group H] [Finite H] [IsCyclic H]
    {ψ : H → ℂ} (hψ : ψ ∈ R(H)) {y z : H} {k : ℕ}
    (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = ψ y ∧
      algebraMap A ℂ az = ψ z ∧
      (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ay) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) az) ^ (p ^ k) := by
  let I : Ideal A := Ideal.span ({(p : A)} : Set A)
  let mk : A →+* A ⧸ I := Ideal.Quotient.mk I
  letI : CommGroup H := IsCyclic.commGroup
  letI : CharP (A ⧸ I) p := quotient_span_prime_charP (A := A) (p := p)
  let P : (g : H → ℂ) → g ∈ R(H) → Prop := fun g _ ↦
    ∃ ay az : A,
      algebraMap A ℂ ay = g y ∧
      algebraMap A ℂ az = g z ∧
      (mk ay) ^ (p ^ k) = (mk az) ^ (p ^ k)
  -- The character ring is generated by irreducible characters; on a cyclic group those are
  -- degree-`1`, and the Frobenius step is then stable under `+` and `*`.
  refine Algebra.adjoin_induction (p := P) ?_ ?_ ?_ ?_ hψ
  · intro χ hχ
    rcases hχ with ⟨ρ, -, hρirr, rfl⟩
    obtain ⟨α, hα⟩ := exists_linear_character_of_irreducible_rep (ρ := ρ)
    obtain ⟨ay, az, hay, haz, hpowA⟩ :=
      exists_lifts_of_linear_character_values_with_pow_eq (A := A) (p := p) α hpow
    refine ⟨ay, az, ?_, ?_, ?_⟩
    · simpa [hα]
    · simpa [hα]
    · simpa [mk] using congrArg mk hpowA
  · intro n
    refine ⟨n, n, ?_, ?_, ?_⟩
    · simp
    · simp
    · rfl
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay + uy, az + uz, ?_, ?_, ?_⟩
    · simp [hay, huy]
    · simp [haz, huz]
    · calc
        mk ((ay + uy) ^ (p ^ k)) = (mk (ay + uy)) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay + mk uy) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay) ^ (p ^ k) + (mk uy) ^ (p ^ k) := by
          simpa using add_pow_char_pow (mk ay) (mk uy) p k
        _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
          rw [hq, hr]
        _ = (mk (az + uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az + uz)) ^ (p ^ k) = (mk az + mk uz) ^ (p ^ k) := by
              simp [mk]
            _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
              simpa using add_pow_char_pow (mk az) (mk uz) p k
        _ = mk ((az + uz) ^ (p ^ k)) := by
          simp [mk]
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay * uy, az * uz, ?_, ?_, ?_⟩
    · simp [hay, huy, map_mul]
    · simp [haz, huz, map_mul]
    · calc
        mk ((ay * uy) ^ (p ^ k)) = (mk (ay * uy)) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay * mk uy) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay) ^ (p ^ k) * (mk uy) ^ (p ^ k) := by
          simpa using mul_pow (mk ay) (mk uy) (p ^ k)
        _ = (mk az) ^ (p ^ k) * (mk uz) ^ (p ^ k) := by
          rw [hq, hr]
        _ = (mk (az * uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az * uz)) ^ (p ^ k) = (mk az * mk uz) ^ (p ^ k) := by
              simp [mk]
            _ = (mk az) ^ (p ^ k) * (mk uz) ^ (p ^ k) := by
              simpa using mul_pow (mk az) (mk uz) (p ^ k)
        _ = mk ((az * uz) ^ (p ^ k)) := by
          simp [mk]

/-- Helper for Lemma 10-10.3-2: the same Frobenius comparison extends from the ordinary cyclic
character ring to its scalar extension `A ⊗ R(H)`. -/
theorem tensor_character_qpow_quotient_eq_of_mem_characterRingScalarExtension
    {H : Type u} [Group H] [Finite H] [IsCyclic H]
    {f : H → ℂ} (hf : f ∈ characterRingScalarExtension A H)
    {y z : H} {k : ℕ} (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = f y ∧
      algebraMap A ℂ az = f z ∧
      (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ay) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) az) ^ (p ^ k) := by
  let I : Ideal A := Ideal.span ({(p : A)} : Set A)
  let mk : A →+* A ⧸ I := Ideal.Quotient.mk I
  letI : CharP (A ⧸ I) p := quotient_span_prime_charP (A := A) (p := p)
  let P : (H → ℂ) → Prop := fun g ↦
    ∃ ay az : A,
      algebraMap A ℂ ay = g y ∧
      algebraMap A ℂ az = g z ∧
      (mk ay) ^ (p ^ k) = (mk az) ^ (p ^ k)
  -- Route correction: instead of extracting an explicit basis of linear characters first, push the
  -- Frobenius-compatible lift property through the `A`-span directly.
  refine Submodule.span_induction
    (s := (R(H) : Set (H → ℂ)))
    (p := fun g _ ↦ P g)
    ?_ ?_ ?_ ?_ hf
  · intro ψ hψ
    exact cyclic_character_qpow_quotient_eq (A := A) (p := p) hψ hpow
  · refine ⟨0, 0, ?_, ?_, rfl⟩
    · simp
    · simp
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay + uy, az + uz, ?_, ?_, ?_⟩
    · simp [hay, huy]
    · simp [haz, huz]
    · calc
        mk ((ay + uy) ^ (p ^ k)) = (mk (ay + uy)) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay + mk uy) ^ (p ^ k) := by
          simp [mk]
        _ = (mk ay) ^ (p ^ k) + (mk uy) ^ (p ^ k) := by
          simpa using add_pow_char_pow (mk ay) (mk uy) p k
        _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
          rw [hq, hr]
        _ = (mk (az + uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az + uz)) ^ (p ^ k) = (mk az + mk uz) ^ (p ^ k) := by
              simp [mk]
            _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
              simpa using add_pow_char_pow (mk az) (mk uz) p k
        _ = mk ((az + uz) ^ (p ^ k)) := by
          simp [mk]
  · intro a g _ hg
    rcases hg with ⟨ay, az, hay, haz, hq⟩
    refine ⟨a * ay, a * az, ?_, ?_, ?_⟩
    · calc
        algebraMap A ℂ (a * ay) = algebraMap A ℂ a * algebraMap A ℂ ay := by
          simp [map_mul]
        _ = algebraMap A ℂ a * g y := by
          rw [hay]
        _ = (a • g) y := by
          simp [Pi.smul_apply, Algebra.smul_def]
    · calc
        algebraMap A ℂ (a * az) = algebraMap A ℂ a * algebraMap A ℂ az := by
          simp [map_mul]
        _ = algebraMap A ℂ a * g z := by
          rw [haz]
        _ = (a • g) z := by
          simp [Pi.smul_apply, Algebra.smul_def]
    · calc
        mk ((a * ay) ^ (p ^ k)) = (mk (a * ay)) ^ (p ^ k) := by
          simp [mk]
        _ = (mk a * mk ay) ^ (p ^ k) := by
          simp [mk]
        _ = (mk a) ^ (p ^ k) * (mk ay) ^ (p ^ k) := by
          simpa using mul_pow (mk a) (mk ay) (p ^ k)
        _ = (mk a) ^ (p ^ k) * (mk az) ^ (p ^ k) := by
          rw [hq]
        _ = (mk (a * az)) ^ (p ^ k) := by
          symm
          calc
            (mk (a * az)) ^ (p ^ k) = (mk a * mk az) ^ (p ^ k) := by
              simp [mk]
            _ = (mk a) ^ (p ^ k) * (mk az) ^ (p ^ k) := by
              simpa using mul_pow (mk a) (mk az) (p ^ k)
        _ = mk ((a * az) ^ (p ^ k)) := by
          simp [mk]

/-- Helper for Lemma 10-10.3-2: after restricting to the cyclic subgroup generated by `x`, the
character-theoretic Frobenius step should identify the quotient classes of the `p^k`th powers of
the two chosen integer values. -/
theorem qpow_quotient_eq_of_restriction_to_zpowers
    (χ : A ⊗R(G)) (x : G) (m n : ℤ)
    (hm : χ x = (m : ℂ))
    (hn : χ (pRegularComponent p x) = (n : ℂ))
    (k : ℕ) :
    let H : Subgroup G := Subgroup.zpowers x
    let xH : H := ⟨x, Subgroup.mem_zpowers x⟩
    let xrH : H :=
      ⟨pRegularComponent p x,
        (p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)).right_mem_zpowers⟩
    xH ^ (p ^ k) = xrH ^ (p ^ k) →
      Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((m : A) ^ (p ^ k)) =
        Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((n : A) ^ (p ^ k)) := by
  intro H xH xrH hxpow
  let f : H → ℂ := ((H.tensorCharacterRingRestriction χ : A ⊗R(H)) : H → ℂ)
  have hf : f ∈ characterRingScalarExtension A H := by
    exact tensorCharacterRing_mem_characterRingScalarExtension (H.tensorCharacterRingRestriction χ)
  have hfx : f xH = (m : ℂ) := by
    -- Restriction to `H = ⟨x⟩` keeps the value at the chosen generator unchanged.
    calc
      f xH = χ x := by
        change ((H.tensorCharacterRingRestriction χ : A ⊗R(H)) : H → ℂ) xH = χ x
        rw [Subgroup.tensorCharacterRingRestriction_apply (A := A)]
      _ = (m : ℂ) := by
        simpa using hm
  have hfxr : f xrH = (n : ℂ) := by
    -- The same evaluation identity holds at the chosen `p'`-component inside `H`.
    calc
      f xrH = χ (pRegularComponent p x) := by
        change ((H.tensorCharacterRingRestriction χ : A ⊗R(H)) : H → ℂ) xrH =
          χ (pRegularComponent p x)
        rw [Subgroup.tensorCharacterRingRestriction_apply (A := A)]
      _ = (n : ℂ) := by
        simpa using hn
  obtain ⟨ay, az, hay, haz, hq⟩ :=
    tensor_character_qpow_quotient_eq_of_mem_characterRingScalarExtension
      (A := A) (p := p) hf hxpow
  have haym : ay = (m : A) := by
    let h_inj : Function.Injective (algebraMap A ℂ) :=
      IsIntegralClosure.algebraMap_injective A ℤ ℂ
    apply h_inj
    calc
      algebraMap A ℂ ay = f xH := hay
      _ = (m : ℂ) := hfx
      _ = algebraMap A ℂ (m : A) := by
        simp
  have hazn : az = (n : A) := by
    let h_inj : Function.Injective (algebraMap A ℂ) :=
      IsIntegralClosure.algebraMap_injective A ℤ ℂ
    apply h_inj
    calc
      algebraMap A ℂ az = f xrH := haz
      _ = (n : ℂ) := hfxr
      _ = algebraMap A ℂ (n : A) := by
        simp
  -- Rewrite the abstract lifted endpoints back to the chosen integers `m` and `n`.
  simpa [haym, hazn] using hq

-- Proof sketch: restrict `χ` to the cyclic subgroup generated by `x`, write it as an `A`-linear
-- combination of degree-one characters, compare the values at `x` and at the chosen `p`-regular
-- component `pRegularComponent p x` after raising to a sufficiently large `p`-power, and then use
-- the integer-valued hypothesis together with the integrality of `A` over `ℤ` inside `ℂ` to
-- compare any chosen integral representatives modulo `p`.
/-- Lemma 10-10.3-2: if `χ ∈ A ⊗ R(G)` takes integer values, then any chosen integer
representatives of the values of `χ` at `x` and at the chosen `p'`-component
`pRegularComponent p x` are congruent modulo `p`. -/
theorem integerValued_tensorCharacter_modEq_pRegularComponent
    (χ : A ⊗R(G))
    (hInt : ∀ g : G, ∃ n : ℤ, χ g = (n : ℂ)) (x : G)
    (m n : ℤ) (hm : χ x = (m : ℂ))
    (hn : χ (pRegularComponent p x) = (n : ℂ)) :
    m ≡ n [ZMOD p] := by
  -- First record that the chosen representatives agree with the integer-valued witnesses supplied
  -- by `hInt`; this keeps the source-facing arithmetic data aligned with the tensor character.
  rcases hInt x with ⟨mx, hmx⟩
  rcases hInt (pRegularComponent p x) with ⟨nx, hnx⟩
  have hmC : (m : ℂ) = (mx : ℂ) := by
    calc
      (m : ℂ) = χ x := by simpa using hm.symm
      _ = (mx : ℂ) := by simpa using hmx
  have hnC : (n : ℂ) = (nx : ℂ) := by
    calc
      (n : ℂ) = χ (pRegularComponent p x) := by simpa using hn.symm
      _ = (nx : ℂ) := by simpa using hnx
  have hm_eq : m = mx := by
    exact_mod_cast hmC
  have hn_eq : n = nx := by
    exact_mod_cast hnC
  -- Route correction: instead of treating the Chapter 11 Adams theorem as the main engine, first
  -- restrict to the cyclic subgroup generated by `x` and rewrite the restricted character as an
  -- `A`-linear combination of degree-1 characters.
  let H : Subgroup G := Subgroup.zpowers x
  have hxH : x ∈ H := Subgroup.mem_zpowers x
  have hxrH : pRegularComponent p x ∈ H := by
    exact (p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)).right_mem_zpowers
  let xH : H := ⟨x, hxH⟩
  let xrH : H := ⟨pRegularComponent p x, hxrH⟩
  obtain ⟨k, hkpow⟩ := exists_p_power_eq_pRegularComponent_pow (p := p) x
  have hxpowH : xH ^ p ^ k = xrH ^ p ^ k := by
    apply Subtype.ext
    simpa [xH, xrH] using hkpow
  -- The only remaining input is the cyclic linear-character/Frobenius package on `H = ⟨x⟩`.
  have hquot :
      Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((m : A) ^ (p ^ k)) =
        Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((n : A) ^ (p ^ k)) := by
    -- The restriction to `H` together with `hxpowH` is exactly the source-proof input for the
    -- cyclic reduction.
    simpa [H, xH, xrH] using
      qpow_quotient_eq_of_restriction_to_zpowers (p := p) χ x m n hm hn k hxpowH
  have hquot' :
      Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((mx : A) ^ (p ^ k)) =
        Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((nx : A) ^ (p ^ k)) := by
    simpa [hm_eq, hn_eq] using hquot
  -- The arithmetic descent is now separated from the cyclic character theory.
  rw [hm_eq, hn_eq]
  exact int_modEq_of_qpow_quotient_eq_mod_p (A := A) (p := p) mx nx k hquot'

/-- Bridge/view form of Lemma 10-10.3-2 in the canonical realized owner
`characterRingScalarExtension A G`, with `A` viewed as an integral closure of `ℤ` in `ℂ`. -/
theorem integerValued_character_modEq_pRegularComponent_of_mem_characterRingScalarExtension
    (χ : characterRingScalarExtension A G)
    (hInt : ∀ g : G, ∃ n : ℤ, χ g = (n : ℂ)) (x : G)
    (m n : ℤ) (hm : χ x = (m : ℂ))
    (hn : χ (pRegularComponent p x) = (n : ℂ)) :
    m ≡ n [ZMOD p] := by
  obtain ⟨χ', hχ'⟩ := (R(G)).toSubmodule.surjective_tensorToSpan A χ
  change A ⊗R(G) at χ'
  change (R(G)).toSubmodule.tensorToSpan A χ' = χ at hχ'
  have hχ'_apply : (χ' : G → ℂ) = χ :=
    congrArg ((↑) : characterRingScalarExtension A G → G → ℂ) hχ'
  have hInt' : ∀ g : G, ∃ k : ℤ, χ' g = (k : ℂ) := by
    intro g
    rcases hInt g with ⟨k, hk⟩
    exact ⟨k, by simpa [hχ'_apply] using hk⟩
  exact integerValued_tensorCharacter_modEq_pRegularComponent χ' hInt' x m n
    (by simpa [hχ'_apply] using hm)
    (by simpa [hχ'_apply] using hn)

end
