import Mathlib
import Serre.Chap02.Remark_2_2_1_2
import Serre.Chap09.Corollary_9_9_2_2
import Serre.Chap09.Proposition_9_9_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Representation SubgroupInduction

noncomputable section

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type} [CommRing A] [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]

attribute [local instance] Fintype.ofFinite

-- Source/core/bridge triage:
-- * source-facing: Serre's divisibility criterion for a bundled class function on `G`.
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

/-- Helper for Lemma 10-10.3-1: multiplying Serre's `θ[H]` by an integer-valued function produces
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
