import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_4
import LinearRepresentations_Serre_1977.Chap10.Lemma_10_10_3_1
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension

open Representation
open scoped Representation SubgroupInduction TensorProduct

noncomputable section

universe u v

section

variable {G : Type u} [Group G]

attribute [local instance] Classical.propDecidable

local notation "C(" x ")" => Subgroup.centralizer ({x} : Set G)

-- Source/core/bridge triage:
-- * source-facing: Brauer's auxiliary virtual character on the associated subgroup `H`.
-- * core/canonical: Serre's integral character-ring owner `R(H)`.
-- * bridge/view: its underlying explicit function `H → ℂ`, and later the scalar extension
--   `(1 : A) ⊗ ψ₀` in `A ⊗R(H)`.

/-- The explicit complex-valued function underlying Brauer's auxiliary character on the associated
subgroup. -/
noncomputable def brauerAssociatedAuxiliaryFunction (p : ℕ) (x : G)
    (P : Sylow p C(x)) :
    associatedPElementarySubgroup p x P → ℂ :=
  fun h ↦
    if ∃ y : P, h.1 = x * (C(x)).subtype y then
      (orderOf x : ℂ)
    else
      0

section

variable [Finite G]
variable {p : ℕ} [Fact p.Prime]

variable (x : G) (P : Sylow p C(x))

local notation "H" => associatedPElementarySubgroup p x P

/-- Helper for Lemma 10-10.3-3: the linear characters of a finite commutative group form a finite
type. -/
local instance lemma_10_10_3_3_linearCharacterFinite
    {B : Type u} [CommGroup B] [Finite B] :
    Finite (B →* ℂˣ) := by
  let eDual : (B →* ℂˣ) ≃* B :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G := B) (M := ℂ))
  exact Finite.of_equiv B eDual.symm.toEquiv

/-- Helper for Lemma 10-10.3-3: finite linear-character sets inherit their canonical `Fintype`
structure. -/
local instance lemma_10_10_3_3_linearCharacterFintype
    {B : Type u} [CommGroup B] [Finite B] :
    Fintype (B →* ℂˣ) := Fintype.ofFinite (B →* ℂˣ)

/-- Helper for Lemma 10-10.3-3: the generator `x` belongs to the associated subgroup. -/
lemma associatedPElementary_generator_mem (p : ℕ) (x : G) (P : Sylow p C(x)) :
    x ∈ associatedPElementarySubgroup p x P := by
  -- The associated subgroup contains the cyclic factor `⟨x⟩` by construction.
  exact zpowers_le_associatedPElementarySubgroup p x P <|
    Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

/-- Helper for Lemma 10-10.3-3: the ambient point `x` lies in the cyclic factor viewed inside the
associated subgroup. -/
lemma associatedPElementary_zpowers_generator_subgroup_mem (p : ℕ) (x : G) (P : Sylow p C(x)) :
    ((⟨x, associatedPElementary_generator_mem p x P⟩ :
        associatedPElementarySubgroup p x P)) ∈
      (Subgroup.zpowers x).subgroupOf (associatedPElementarySubgroup p x P) := by
  -- Inside the ambient associated subgroup, the same element still belongs to `⟨x⟩`.
  exact Subgroup.mem_subgroupOf.mpr <| Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

/-- Helper for Lemma 10-10.3-3: the distinguished point of the cyclic factor is the element
represented by `x`. -/
noncomputable def associatedPElementary_zpowers_generator (p : ℕ) (x : G) (P : Sylow p C(x)) :
    (Subgroup.zpowers x).subgroupOf (associatedPElementarySubgroup p x P) :=
  ⟨⟨x, associatedPElementary_generator_mem p x P⟩,
    associatedPElementary_zpowers_generator_subgroup_mem p x P⟩

/-- Helper for Lemma 10-10.3-3: the cyclic factor of the associated subgroup has order
`orderOf x`. -/
lemma associatedPElementary_zpowers_card_eq_orderOf (x : G) (P : Sylow p C(x)) :
    Nat.card ((Subgroup.zpowers x).subgroupOf (associatedPElementarySubgroup p x P)) = orderOf x := by
  have hz :
      Subgroup.zpowers x ≤ associatedPElementarySubgroup p x P :=
    zpowers_le_associatedPElementarySubgroup p x P
  -- The subgroup-of view does not change the cyclic factor, so its cardinal is still `orderOf x`.
  simpa using
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz).toEquiv).trans (Nat.card_zpowers x)

/-- Helper for Lemma 10-10.3-3: project the associated subgroup to its cyclic `⟨x⟩`-factor using
the canonical `p`-elementary decomposition. -/
noncomputable def associatedPElementary_zpowers_projection
    (x : G) (hx : IsPRegular p x) (P : Sylow p C(x)) :
    associatedPElementarySubgroup p x P →*
      (Subgroup.zpowers x).subgroupOf (associatedPElementarySubgroup p x P) :=
  let hdecomp := associatedPElementarySubgroup_decomposition x hx P
  let e := hdecomp.isComplement.prodMulEquiv hdecomp.commute
  (MonoidHom.fst _ _).comp e.symm.toMonoidHom

/-- Helper for Lemma 10-10.3-3: the first coordinate in the associated decomposition is `x`
exactly on the explicit support coset `xP`. -/
lemma associatedPElementary_zpowers_projection_eq_generator_iff
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x)
    (h : associatedPElementarySubgroup p x P) :
    associatedPElementary_zpowers_projection x hx P h =
        associatedPElementary_zpowers_generator p x P ↔
      ∃ y : P, h.1 = x * (C(x)).subtype y := by
  let H' := associatedPElementarySubgroup p x P
  let C₀ : Subgroup H' := (Subgroup.zpowers x).subgroupOf H'
  let Pimg : Subgroup G := Subgroup.map C(x).subtype (P : Subgroup C(x))
  let P₀ : Subgroup H' := Pimg.subgroupOf H'
  let hdecomp := associatedPElementarySubgroup_decomposition x hx P
  let e := hdecomp.isComplement.prodMulEquiv hdecomp.commute
  let u : C₀ := associatedPElementary_zpowers_generator p x P
  constructor
  · intro hπ
    let hp : P₀ := (e.symm h).2
    have hcoords : e.symm h = (u, hp) := by
      -- Once the cyclic coordinate is fixed to `u`, the pair is determined by its `P`-coordinate.
      ext
      · simpa [associatedPElementary_zpowers_projection, H', C₀, P₀, hdecomp, e, u] using hπ
      · rfl
    have hh : h = e (u, hp) := by
      simpa [e] using congrArg e hcoords
    have hp_mem :
        (((hp : P₀) : H') : G) ∈ Pimg := by
      exact Subgroup.mem_subgroupOf.mp hp.2
    rcases (Subgroup.mem_map.1 hp_mem) with ⟨y, hyP, hyEq⟩
    refine ⟨⟨y, hyP⟩, ?_⟩
    -- Unfold the product equivalence only at the final multiplication identity.
    simpa [hyEq, H', C₀, P₀, Pimg, e, u, associatedPElementary_zpowers_generator,
      Subgroup.IsComplement'.prodMulEquiv, MonoidHom.noncommCoprod_apply] using
      congrArg Subtype.val hh
  · rintro ⟨y, hy⟩
    have hyPimg : ((C(x)).subtype y : G) ∈ Pimg := by
      exact Subgroup.mem_map.2 ⟨(y : C(x)), y.2, rfl⟩
    have hyH : ((C(x)).subtype y : G) ∈ H' := by
      change ((C(x)).subtype y : G) ∈ Subgroup.zpowers x ⊔ Pimg
      exact (le_sup_right : Pimg ≤ Subgroup.zpowers x ⊔ Pimg) hyPimg
    let hp : P₀ := ⟨⟨(C(x)).subtype y, hyH⟩, Subgroup.mem_subgroupOf.mpr hyPimg⟩
    have hp_val : (((hp : P₀) : H') : G) = (C(x)).subtype y := by
      -- The `P₀` witness was built from the same ambient element `(C(x)).subtype y`.
      rfl
    have hh : h = e (u, hp) := by
      -- The explicit witness `y` exactly reconstructs `h` from the `C₀ × P₀` coordinates.
      apply Subtype.ext
      calc
        h.1 = x * (C(x)).subtype y := hy
        _ = x * (((hp : P₀) : H') : G) := by rw [hp_val]
        _ = (e (u, hp) : H').1 := by
          simpa [H', C₀, P₀, Pimg, e, u, associatedPElementary_zpowers_generator,
            Subgroup.IsComplement'.prodMulEquiv, MonoidHom.noncommCoprod_apply]
    have hcoords : e.symm h = (u, hp) := by
      simpa [e] using congrArg e.symm hh
    -- Read off the first coordinate from the reconstructed decomposition.
    simpa [associatedPElementary_zpowers_projection, H', C₀, P₀, hdecomp, e, u] using
      congrArg Prod.fst hcoords

/-- Helper for Lemma 10-10.3-3: Brauer's explicit auxiliary function is the pullback of the
weighted delta function at the distinguished point of the cyclic factor. -/
lemma brauerAssociatedAuxiliaryFunction_eq_pullback_weighted_delta
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x) :
    brauerAssociatedAuxiliaryFunction p x P =
      fun h : associatedPElementarySubgroup p x P ↦
        if associatedPElementary_zpowers_projection x hx P h =
            associatedPElementary_zpowers_generator p x P then
          (Nat.card ((Subgroup.zpowers x).subgroupOf (associatedPElementarySubgroup p x P)) : ℂ)
        else
          0 := by
  funext h
  have hiff :=
    associatedPElementary_zpowers_projection_eq_generator_iff x P hx h
  have hcard :
      Nat.card ((Subgroup.zpowers x).subgroupOf (associatedPElementarySubgroup p x P)) =
        orderOf x :=
    associatedPElementary_zpowers_card_eq_orderOf (p := p) x P
  by_cases hh :
      associatedPElementary_zpowers_projection x hx P h =
        associatedPElementary_zpowers_generator p x P
  · have hwitness : ∃ y : P, h.1 = x * (C(x)).subtype y := hiff.mp hh
    -- On the support coset, both descriptions take the same constant value.
    rw [brauerAssociatedAuxiliaryFunction, if_pos hwitness, if_pos hh, hcard]
  · have hnot : ¬ ∃ y : P, h.1 = x * (C(x)).subtype y := by
      intro hwitness
      exact hh (hiff.mpr hwitness)
    -- Away from that coset, both descriptions vanish.
    rw [brauerAssociatedAuxiliaryFunction, if_neg hnot, if_neg hh]

/-- Helper for Lemma 10-10.3-3: pulling back a linear character from the cyclic factor gives an
element of the scalar-extended character ring on the associated subgroup. -/
lemma pulled_back_linear_character_mem_characterRingScalarExtension
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x)
    (χ :
      (Subgroup.zpowers x).subgroupOf (associatedPElementarySubgroup p x P) →* ℂˣ) :
    (fun h : associatedPElementarySubgroup p x P ↦
      ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ)) ∈
      characterRingScalarExtension (↥(integralClosure ℤ ℂ))
        (associatedPElementarySubgroup p x P) := by
  let η : R(associatedPElementarySubgroup p x P) :=
    (χ.comp (associatedPElementary_zpowers_projection x hx P)).toCharacterRing
  have hη :
      ((η : R(associatedPElementarySubgroup p x P)) :
          associatedPElementarySubgroup p x P → ℂ) ∈
        characterRingScalarExtension (↥(integralClosure ℤ ℂ))
          (associatedPElementarySubgroup p x P) := by
    -- The pullback remains an honest linear character of the associated subgroup.
    exact mem_characterRingScalarExtension_of_mem_characterRing
      (A := ↥(integralClosure ℤ ℂ)) _ η.property
  have hchar :
      (fun h : associatedPElementarySubgroup p x P ↦
        ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ)) =
      (χ.comp (associatedPElementary_zpowers_projection x hx P)).toRepresentation.character := by
    -- Evaluate the degree-`1` character pointwise to recover the explicit complex-valued function.
    ext h
    simp [MonoidHom.toRepresentation_character_apply]
  -- Unpack the owner character to the explicit class function used in the cyclic expansion.
  change (χ.comp (associatedPElementary_zpowers_projection x hx P)).toRepresentation.character ∈
    characterRingScalarExtension (↥(integralClosure ℤ ℂ))
      (associatedPElementarySubgroup p x P) at hη
  exact hchar.symm ▸ hη

/-- Helper for Lemma 10-10.3-3: the weighted delta function on a finite cyclic group still admits
the standard linear-character expansion after shrinking the carrier to a small universe. -/
lemma exists_weighted_delta_linear_character_expansion_shrink
    {B : Type u} [CommGroup B] [Finite B] [DecidableEq B] (u : B) :
    ∃ coeff : (B →* ℂˣ) → ↥(integralClosure ℤ ℂ),
      (fun h : B ↦ if u = h then (Nat.card B : ℂ) else 0) =
        ∑ χ : B →* ℂˣ, coeff χ • χ.toRepresentation.character := by
  classical
  let e : B ≃* Shrink.{0} B := Shrink.mulEquiv.symm
  let charEquiv : (B →* ℂˣ) ≃ (Shrink.{0} B →* ℂˣ) := e.monoidHomCongrLeftEquiv
  have hcard : Nat.card B = Nat.card (Shrink.{0} B) := by
    simpa using Nat.card_congr e.toEquiv
  obtain ⟨coeff₀, hcoeff₀⟩ :=
    exists_weighted_delta_linear_character_expansion
      (A := ↥(integralClosure ℤ ℂ)) (B := Shrink.{0} B) (e u)
  let coeff : (B →* ℂˣ) → ↥(integralClosure ℤ ℂ) := fun χ ↦ coeff₀ (charEquiv χ)
  refine ⟨coeff, ?_⟩
  ext h
  calc
    (if u = h then (Nat.card B : ℂ) else 0) =
        if e u = e h then (Nat.card (Shrink.{0} B) : ℂ) else 0 := by
          by_cases huh : u = h
          · subst huh
            simp [hcard]
          · have heh : e u ≠ e h := by
              intro heq
              exact huh (e.injective heq)
            simp [huh, heh, hcard]
    _ = ∑ ρ : Shrink.{0} B →* ℂˣ, coeff₀ ρ • ρ.toRepresentation.character (e h) := by
          simpa [Finset.sum_apply] using congrFun hcoeff₀ (e h)
    _ = ∑ χ : B →* ℂˣ, coeff χ • χ.toRepresentation.character h := by
          symm
          simpa [coeff, charEquiv, e, MonoidHom.toRepresentation_character_apply] using
            (Fintype.sum_equiv charEquiv
              (fun χ : B →* ℂˣ ↦ coeff χ • χ.toRepresentation.character h)
              (fun ρ : Shrink.{0} B →* ℂˣ ↦ coeff₀ ρ • ρ.toRepresentation.character (e h))
              (fun χ ↦ by
                simp [coeff, charEquiv, e, MonoidHom.toRepresentation_character_apply]))
    _ = (∑ χ : B →* ℂˣ, coeff χ • χ.toRepresentation.character) h := by
          simp [Finset.sum_apply]

-- Proof sketch: the textbook witness lives naturally in the scalar-extended owner
-- `(integralClosure ℤ ℂ) ⊗ R(H)`, not in the integral owner `R(H)`. The direct support and
-- induction arguments below therefore work with the explicit function itself, postponing the owner
-- upgrade to the final existence theorem.
/-- The explicit Brauer auxiliary function belongs to the algebraic-integer scalar extension of the
associated subgroup character ring. -/
theorem brauerAssociatedAuxiliaryFunction_mem_characterRingScalarExtension
    (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x) :
    brauerAssociatedAuxiliaryFunction p x P ∈
      characterRingScalarExtension (↥(integralClosure ℤ ℂ))
        (associatedPElementarySubgroup p x P) := by
  classical
  let H' := associatedPElementarySubgroup p x P
  let C₀ : Subgroup H' := (Subgroup.zpowers x).subgroupOf H'
  let hdecomp := associatedPElementarySubgroup_decomposition x hx P
  letI : IsCyclic C₀ := by
    simpa [C₀] using hdecomp.cyclic
  letI : CommGroup C₀ := IsCyclic.commGroup
  let u : C₀ := associatedPElementary_zpowers_generator p x P
  have hrewrite :
      brauerAssociatedAuxiliaryFunction p x P =
        fun h : H' ↦
          if associatedPElementary_zpowers_projection x hx P h = u then
            (Nat.card C₀ : ℂ)
          else
            0 := by
    -- Route correction: rewrite the explicit support condition as a pullback from the cyclic
    -- factor before expanding it into characters.
    simpa [C₀, u] using
      brauerAssociatedAuxiliaryFunction_eq_pullback_weighted_delta x P hx
  obtain ⟨coeff, hcoeff⟩ :=
    exists_weighted_delta_linear_character_expansion_shrink (u := u)
  have hpullback :
      (fun h : H' ↦
        if associatedPElementary_zpowers_projection x hx P h = u then
          (Nat.card C₀ : ℂ)
        else
          0) =
        ∑ χ : C₀ →* ℂˣ,
          coeff χ •
            fun h : H' ↦
              ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ) := by
    -- Pull the cyclic weighted-delta expansion back along the projection `H → C₀` pointwise.
    ext h
    have hpoint :
        (if u = associatedPElementary_zpowers_projection x hx P h then
          (Nat.card C₀ : ℂ)
        else
          0) =
          (∑ χ : C₀ →* ℂˣ, coeff χ • χ.toRepresentation.character)
            (associatedPElementary_zpowers_projection x hx P h) := by
      simpa [Finset.sum_apply] using
        congrFun hcoeff (associatedPElementary_zpowers_projection x hx P h)
    calc
      (if associatedPElementary_zpowers_projection x hx P h = u then
        (Nat.card C₀ : ℂ)
      else
        0) =
          (if u = associatedPElementary_zpowers_projection x hx P h then
            (Nat.card C₀ : ℂ)
          else
            0) := by
              by_cases hEq : u = associatedPElementary_zpowers_projection x hx P h
              · rw [if_pos hEq.symm, if_pos hEq]
              · have hEq' : ¬ associatedPElementary_zpowers_projection x hx P h = u := by
                  intro hu
                  exact hEq hu.symm
                rw [if_neg hEq', if_neg hEq]
      _ = (∑ χ : C₀ →* ℂˣ, coeff χ • χ.toRepresentation.character)
            (associatedPElementary_zpowers_projection x hx P h) := hpoint
      _ = ∑ χ : C₀ →* ℂˣ,
            coeff χ • χ.toRepresentation.character
              (associatedPElementary_zpowers_projection x hx P h) := by
              simp [Finset.sum_apply]
      _ = ∑ χ : C₀ →* ℂˣ,
            coeff χ •
              ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ) := by
              refine Fintype.sum_congr
                (fun χ : C₀ →* ℂˣ ↦
                  coeff χ • χ.toRepresentation.character
                    (associatedPElementary_zpowers_projection x hx P h))
                (fun χ : C₀ →* ℂˣ ↦
                  coeff χ •
                    ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ)) ?_
              intro χ
              simp [Algebra.smul_def, MonoidHom.toRepresentation_character_apply]
      _ = (∑ χ : C₀ →* ℂˣ,
            coeff χ •
              fun h : H' ↦
                ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ)) h := by
              simp [Finset.sum_apply, Pi.smul_apply]
  rw [hrewrite, hpullback]
  refine Submodule.sum_mem _ ?_
  intro χ hχ
  have hbase :
      (fun h : H' ↦
        ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ)) ∈
        characterRingScalarExtension (↥(integralClosure ℤ ℂ)) H' := by
    -- Each pulled-back linear character is still an honest character of `H`.
    exact pulled_back_linear_character_mem_characterRingScalarExtension
      (p := p) x P hx χ
  have hsmul :
      coeff χ •
          (fun h : H' ↦
            ((χ.comp (associatedPElementary_zpowers_projection x hx P)) h : ℂ)) ∈
        characterRingScalarExtension (↥(integralClosure ℤ ℂ)) H' := by
    exact (characterRingScalarExtension (↥(integralClosure ℤ ℂ)) H').smul_mem (coeff χ) hbase
  -- This is exactly the summand appearing in the pulled-back weighted-delta expansion.
  simpa [Pi.smul_apply, Algebra.smul_def] using hsmul

/-- Helper for Lemma 10-10.3-3: every realized element of the scalar extension on a finite group
comes from an actual tensor character owner element. -/
lemma tensorCharacter_exists_of_mem_characterRingScalarExtension_local
    {K : Type u} [Group K] [Finite K] {f : K → ℂ}
    (hf : f ∈ characterRingScalarExtension (↥(integralClosure ℤ ℂ)) K) :
    ∃ χ : (↥(integralClosure ℤ ℂ)) ⊗R(K), (χ : K → ℂ) = f := by
  let fχ : characterRingScalarExtension (↥(integralClosure ℤ ℂ)) K := ⟨f, hf⟩
  obtain ⟨χ, hχ⟩ :=
    (R(K)).toSubmodule.surjective_tensorToSpan (↥(integralClosure ℤ ℂ)) fχ
  change (↥(integralClosure ℤ ℂ)) ⊗R(K) at χ
  change (R(K)).toSubmodule.tensorToSpan (↥(integralClosure ℤ ℂ)) χ = fχ at hχ
  -- Forget the subtype after surjectivity of the realization map.
  refine ⟨χ, ?_⟩
  simpa [fχ] using
    congrArg ((↑) : characterRingScalarExtension (↥(integralClosure ℤ ℂ)) K → K → ℂ) hχ

-- Proof sketch: by construction, the auxiliary function takes the value `orderOf x` on the coset
-- `xP` and `0` elsewhere, so every value is the image of an integer.
/-- The explicit Brauer auxiliary function on `H` takes integer values. -/
theorem brauerAssociatedAuxiliaryFunction_integerValued
    (P : Sylow p C(x)) (h : associatedPElementarySubgroup p x P) :
    ∃ n : ℤ, brauerAssociatedAuxiliaryFunction p x P h = (n : ℂ) := by
  -- Route correction: bind `P` explicitly so Lean keeps the Sylow parameter rather than replacing
  -- the section variable by a synthetic placeholder inside the theorem type.
  -- Reduce immediately to the defining `if`-formula of the source-facing function.
  unfold brauerAssociatedAuxiliaryFunction
  split_ifs with hh
  · refine ⟨orderOf x, ?_⟩
    simp
  · refine ⟨0, ?_⟩
    simp

end

end

end
