import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Serre.Chap01.Definition_1_1_4_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped MatrixGroups

noncomputable section

universe u

section UpperTriangularSubgroup

variable (k : Type u) [CommRing k]

-- Source/core/bridge triage for Exercise 7-7.4-3:
-- * source-facing: the subgroup `H ≤ SL(2, k)` of upper triangular matrices and its linear
--   character `χ_ω`.
-- * core/canonical owners sampled in this domain: `Matrix.BlockTriangular` for the upper
--   triangular condition, `MonoidHom.toRepresentation` for the degree-one representation,
--   `Rep.of`/`Rep.ind` for the bundled Chapter 7 induction owner, and
--   `Representation.ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint` for the Mackey
--   irreducibility criterion phrased through that owner.
-- * bridge/view: the subgroup-owner map `sl2UpperTriangularSubgroup.topLeft k` extracting the
--   top-left unit, from which `χ_ω` is obtained by composition with `ω`.
-- * primitive data: the subgroup `sl2UpperTriangularSubgroup k` and its source-facing character
--   `sl2UpperTriangularSubgroup.character k ω`.
-- * derived API: the induced irreducibility statement, which should be expressed through the
--   bundled owner `Rep.ind ... (Rep.of ...)`.

local notation "M₂" => Matrix (Fin 2) (Fin 2) k

/-- The subgroup `H ≤ SL(2, k)` of upper triangular matrices, namely the matrices
`[[a, b], [0, d]]`. -/
def sl2UpperTriangularSubgroup : Subgroup (SL(2, k)) where
  carrier := { g | (g : M₂).BlockTriangular id }
  one_mem' := by
    simpa using (Matrix.blockTriangular_one :
      Matrix.BlockTriangular (1 : M₂) id)
  mul_mem' := by
    intro g h hg hh
    exact hg.mul hh
  inv_mem' := by
    intro g hg
    have hdet : IsUnit (((g : M₂)).det) := by
      simp [g.det_coe]
    change (((g⁻¹ : SL(2, k)) : M₂).BlockTriangular id)
    rw [show ((g⁻¹ : SL(2, k)) : M₂) = ((g : M₂)⁻¹) by
      rw [Matrix.SpecialLinearGroup.coe_inv,
        Matrix.nonsing_inv_apply (g : M₂) hdet]
      simp [g.det_coe]]
    let _ : Invertible (g : M₂) := Matrix.invertibleOfIsUnitDet (g : M₂) hdet
    simpa using Matrix.blockTriangular_inv_of_blockTriangular hg

namespace sl2UpperTriangularSubgroup

/-- Membership in `sl2UpperTriangularSubgroup` is exactly the canonical upper-triangular
predicate on the underlying `2 × 2` matrix. -/
@[simp] theorem mem_iff (g : SL(2, k)) :
    g ∈ sl2UpperTriangularSubgroup k ↔ ((g : M₂).BlockTriangular id) :=
  Iff.rfl

/-- An upper triangular element of `SL(2, k)` has vanishing lower-left entry. -/
private theorem apply_one_zero (g : sl2UpperTriangularSubgroup k) :
    ((g : SL(2, k)) 1 0) = 0 := by
  simpa using g.2 (show (0 : Fin 2) < 1 by decide)

/-- For an upper triangular element of `SL(2, k)`, the diagonal entries multiply to `1`. -/
private theorem topLeft_mul_bottomRight (h : sl2UpperTriangularSubgroup k) :
    ((h : SL(2, k)) 0 0) * ((h : SL(2, k)) 1 1) = 1 := by
  have hdet : (((h : SL(2, k)) : M₂).det) = 1 := (h : SL(2, k)).det_coe
  rw [Matrix.det_of_upperTriangular h.2, Fin.prod_univ_two] at hdet
  exact hdet

/-- The canonical monoid hom sending an upper triangular element of `SL(2, k)` to its top-left
unit. -/
def topLeft : sl2UpperTriangularSubgroup k →* kˣ where
  toFun h :=
    ⟨((h : SL(2, k)) 0 0), ((h : SL(2, k)) 1 1),
      topLeft_mul_bottomRight k h,
      by simpa [mul_comm] using topLeft_mul_bottomRight k h⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' h h' := by
    apply Units.ext
    change ((h * h' : sl2UpperTriangularSubgroup k) : SL(2, k)) 0 0 =
      ((h : SL(2, k)) 0 0) * ((h' : SL(2, k)) 0 0)
    simp [Matrix.mul_apply, Fin.sum_univ_two, apply_one_zero k h']

/-- The underlying value of `topLeft h` is the top-left entry of `h`. -/
@[simp] theorem topLeft_val (h : sl2UpperTriangularSubgroup k) :
    ((topLeft k h : kˣ) : k) = ((h : SL(2, k)) 0 0) :=
  rfl

/-- The degree-one character `χ_ω` of the upper triangular subgroup of `SL(2, k)`, defined by
`χ_ω([[a, b], [0, d]]) = ω(a)`. -/
def character (ω : kˣ →* ℂˣ) : sl2UpperTriangularSubgroup k →* ℂˣ :=
  ω.comp (topLeft k)

end sl2UpperTriangularSubgroup

end UpperTriangularSubgroup

section Irreducibility

variable (k : Type) [Field k] [Finite k]

open Rep (of)

local notation "M₂" => Matrix (Fin 2) (Fin 2) k
local notation "H" => sl2UpperTriangularSubgroup k

/-- Helper for Exercise 7-7.4-3: an element of `SL(2, k)` outside the upper triangular subgroup
has nonzero lower-left entry. -/
lemma lower_left_ne_zero_of_not_mem_upperTriangular
    {s : SL(2, k)} (hs : s ∉ H) : ((s : M₂) 1 0) ≠ 0 := by
  -- The only obstruction to upper triangularity in size `2` is the `(1,0)` entry.
  intro h10
  apply hs
  show ((s : M₂).BlockTriangular id)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  simpa using h10

/-- Helper for Exercise 7-7.4-3: the Mackey conjugation map
`H ∩ sHs⁻¹ → H`, written explicitly for the upper triangular subgroup of `SL(2, k)`. -/
noncomputable def sl2_upper_triangular_mackey_conj_hom (s : SL(2, k)) :
    Representation.mackeySubgroup H H s →* H :=
  (((MulAut.conj s⁻¹).toMonoidHom.comp (sl2UpperTriangularSubgroup k).subtype).restrict
      (Representation.mackeySubgroup H H s)).codRestrict H fun x ↦ x.2

/-- Helper for Exercise 7-7.4-3: every element outside the upper triangular subgroup yields a
Mackey-subgroup element whose top-left entry is `u` and whose conjugate top-left entry is
`u⁻¹`. -/
lemma exists_mackey_test_element_with_topLeft_values
    {s : SL(2, k)} (hs : s ∉ H) (u : kˣ) :
    ∃ x : Representation.mackeySubgroup H H s,
      sl2UpperTriangularSubgroup.topLeft k x.1 = u ∧
        sl2UpperTriangularSubgroup.topLeft k (sl2_upper_triangular_mackey_conj_hom (k := k) s x) =
          u⁻¹ := by
  let a : k := (s : M₂) 0 0
  let c : k := (s : M₂) 1 0
  have hc : c ≠ 0 := by
    -- The off-Borel hypothesis is exactly the denominator nonvanishing needed below.
    simpa [c] using lower_left_ne_zero_of_not_mem_upperTriangular (k := k) hs
  let t : k := a * (((u⁻¹ : kˣ) : k) - (u : k)) / c
  let xM : M₂ := !![(u : k), t; 0, ((u⁻¹ : kˣ) : k)]
  have hxM_det : xM.det = 1 := by
    -- The witness matrix already has determinant `u * u⁻¹ = 1`.
    rw [show xM = !![(u : k), t; 0, ((u⁻¹ : kˣ) : k)] by rfl, Matrix.det_fin_two]
    simp [xM, t]
  let xSL : SL(2, k) := ⟨xM, hxM_det⟩
  have hxH_mem : xSL ∈ H := by
    -- The witness is visibly upper triangular.
    show ((xSL : M₂).BlockTriangular id)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [xSL, xM] at hij ⊢
  let xH : H := ⟨xSL, hxH_mem⟩
  have hx_conj_mem : xH ∈ Representation.mackeySubgroup H H s := by
    -- Conjugating by `s` cancels the lower-left entry by the chosen value of `t`.
    have hx_conj_triangular : ((((s⁻¹ : SL(2, k)) : M₂) * xM) * (s : M₂)).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      have hsdet : ((s : M₂) 0 0) * (s : M₂) 1 1 - (s : M₂) 0 1 * (s : M₂) 1 0 = 1 := by
        have hsdet0 := s.det_coe
        rwa [Matrix.det_fin_two] at hsdet0
      rw [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
        Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      simp [xM]
      dsimp [t, a, c] at *
      field_simp [hc]
      ring_nf
      simp
    change (((MulAut.conj s⁻¹).toMonoidHom.comp (sl2UpperTriangularSubgroup k).subtype) xH) ∈ H
    rw [sl2UpperTriangularSubgroup.mem_iff]
    simpa [MulAut.conj, xH, xSL, Matrix.mul_assoc] using hx_conj_triangular
  let x : Representation.mackeySubgroup H H s := ⟨xH, hx_conj_mem⟩
  refine ⟨x, ?_, ?_⟩
  · -- The first top-left value is built into the witness matrix.
    apply Units.ext
    simp [sl2UpperTriangularSubgroup.topLeft_val, x, xH, xSL, xM]
  · -- The conjugated top-left entry becomes `u⁻¹` by the determinant-one identity of `s`.
    apply Units.ext
    have hsdet : ((s : M₂) 0 0) * (s : M₂) 1 1 - (s : M₂) 0 1 * (s : M₂) 1 0 = 1 := by
      have hsdet0 := s.det_coe
      rwa [Matrix.det_fin_two] at hsdet0
    have hc : ((s : M₂) 1 0) ≠ 0 := by
      exact lower_left_ne_zero_of_not_mem_upperTriangular (k := k) hs
    have htopLeftAdj :
        (((s : M₂).adjugate * xM * (s : M₂)) 0 0) = ((u⁻¹ : kˣ) : k) := by
      rw [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
        Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      simp [xM]
      dsimp [t, a, c] at *
      field_simp [hc]
      ring_nf
      have hmul :
          (s : M₂) 1 1 * (u : k) * (s : M₂) 0 0 * ((u⁻¹ : kˣ) : k) -
              (s : M₂) 1 0 * (s : M₂) 0 1
            = (s : M₂) 0 0 * (s : M₂) 1 1 - (s : M₂) 0 1 * (s : M₂) 1 0 := by
        calc
          (s : M₂) 1 1 * (u : k) * (s : M₂) 0 0 * ((u⁻¹ : kˣ) : k) - (s : M₂) 1 0 * (s : M₂) 0 1
              = (s : M₂) 0 0 * (s : M₂) 1 1 * ((u : k) * ((u⁻¹ : kˣ) : k)) -
                  (s : M₂) 0 1 * (s : M₂) 1 0 := by
                    ring
          _ = (s : M₂) 0 0 * (s : M₂) 1 1 - (s : M₂) 0 1 * (s : M₂) 1 0 := by
                simp
      exact hmul.trans hsdet
    simpa [sl2_upper_triangular_mackey_conj_hom, sl2UpperTriangularSubgroup.topLeft_val,
      MulAut.conj, x, xH, xSL, Matrix.mul_assoc, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.nonsing_inv_apply, s.det_coe] using htopLeftAdj

/-- Helper for Exercise 7-7.4-3: a complex linear endomorphism of the one-dimensional space `ℂ`
is determined by its value at `1`. -/
lemma complex_linear_apply_eq_mul_apply_one (T : ℂ →ₗ[ℂ] ℂ) (z : ℂ) :
    T z = z * T 1 := by
  -- Write `z` as `z • 1` and then use linearity.
  calc
    T z = T (z • (1 : ℂ)) := by simp
    _ = z • T 1 := by rw [LinearMap.map_smul]
    _ = z * T 1 := by simp [smul_eq_mul]

/-- Helper for Exercise 7-7.4-3: if two representations on the line `ℂ` act differently on some
group element, then every intertwiner between them is zero. -/
lemma hom_zero_of_action_on_one_mismatch
    {Γ : Type*} [Group Γ] {ρ σ : Representation ℂ Γ ℂ}
    (h : ∃ g : Γ, (ρ g) 1 ≠ (σ g) 1) :
    ∀ f : Rep.of ρ ⟶ Rep.of σ, f = 0 := by
  intro f
  rcases h with ⟨g, hg⟩
  have hscalar : (ρ g) 1 * Rep.Hom.hom f 1 = (σ g) 1 * Rep.Hom.hom f 1 := by
    -- Evaluate the intertwining relation at `1` and rewrite each linear map by its value on `1`.
    calc
      (ρ g) 1 * Rep.Hom.hom f 1 = Rep.Hom.hom f ((ρ g) 1) := by
        symm
        simpa using complex_linear_apply_eq_mul_apply_one (Rep.Hom.hom f) ((ρ g) 1)
      _ = (σ g) (Rep.Hom.hom f 1) := by
        simpa using Representation.IntertwiningMap.isIntertwining ρ σ (Rep.Hom.hom f) g (1 : ℂ)
      _ = (σ g) 1 * Rep.Hom.hom f 1 := by
        simpa using complex_linear_apply_eq_mul_apply_one (σ g) (Rep.Hom.hom f 1)
  have hFone : Rep.Hom.hom f 1 = 0 := by
    -- A nonzero value at `1` would force the two scalar actions to coincide.
    by_contra hFone
    exact hg (mul_right_cancel₀ hFone hscalar)
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  -- Once the map kills `1`, linearity forces it to vanish everywhere.
  have hz : (Rep.Hom.hom f) z = z * Rep.Hom.hom f 1 := by
    simpa using complex_linear_apply_eq_mul_apply_one (Rep.Hom.hom f) z
  simp [hz, hFone]

/-- Helper for Exercise 7-7.4-3: if `ω²` is nontrivial, then some unit `u` satisfies
`(ω u)^2 ≠ 1`. -/
lemma exists_unit_sq_ne_one_of_character_sq_ne_one
    (ω : kˣ →* ℂˣ) (hω : (ω ^ 2 : kˣ →* ℂˣ) ≠ 1) :
    ∃ u : kˣ, (ω u) ^ 2 ≠ 1 := by
  -- Otherwise every value of `ω²` would be `1`, forcing `ω² = 1`.
  by_contra h
  apply hω
  ext u
  push Not at h
  simpa [pow_two] using congrArg (fun z : ℂˣ => (z : ℂ)) (h u)

-- Proof sketch: apply Mackey's irreducibility criterion to the pair
-- `(SL(2, k), sl2UpperTriangularSubgroup)` and the bundled induced owner
-- `Rep.ind (sl2UpperTriangularSubgroup k).subtype
--   (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)`.
-- The unique nontrivial double-coset representative is the Weyl element, and the resulting
-- intertwining space is zero exactly when `ω^2` is nontrivial.
/-- Exercise 7-7.4-3: if `k` is a finite field and `ω : kˣ →* ℂˣ` satisfies `ω^2 ≠ 1`, then the
representation of `SL(2, k)` induced from the degree-one character `χ_ω` of the upper triangular
subgroup `H = {[[a, b], [0, d]]}` is irreducible. -/
theorem sl2UpperTriangularCharacter_induced_isIrreducible_of_sq_ne_one
    (ω : kˣ →* ℂˣ) (hω : (ω ^ 2 : kˣ →* ℂˣ) ≠ 1) :
    (Rep.ind (sl2UpperTriangularSubgroup k).subtype
      (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)).ρ.IsIrreducible := by
  let hcard_nat : Nat.card (SL(2, k)) ≠ 0 :=
    (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  letI : NeZero (Nat.card (SL(2, k)) : ℂ) := ⟨by
    exact_mod_cast hcard_nat⟩
  -- Route correction: rather than passing to a global Bruhat representative, use Proposition
  -- `7-7.4-1` exactly as stated and kill each off-Borel Mackey intertwiner by an explicit
  -- witness in `H ∩ sHs⁻¹`.
  have hcriterion :=
    Representation.ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
      (k := ℂ) (V := ℂ)
      (sl2UpperTriangularSubgroup k)
      (sl2UpperTriangularSubgroup.character k ω).toRepresentation
  refine hcriterion.2 ?_
  constructor
  · -- A character line is already irreducible.
    simpa using MonoidHom.toRepresentation_isIrreducible (sl2UpperTriangularSubgroup.character k ω)
  · intro s hs f
    obtain ⟨u, hu⟩ := exists_unit_sq_ne_one_of_character_sq_ne_one (k := k) ω hω
    obtain ⟨x, hx_top, hx_conj_top⟩ :=
      exists_mackey_test_element_with_topLeft_values (k := k) hs u
    have hω_units_ne : ω u ≠ ω u⁻¹ := by
      -- Equality of the two character values would force `(ω u)^2 = 1`.
      intro hEq
      apply hu
      calc
        (ω u) ^ 2 = ω u * ω u := by simp [pow_two]
        _ = ω u * ω u⁻¹ := by rw [hEq]
        _ = ω (u * u⁻¹) := by rw [← map_mul]
        _ = 1 := by simp
    have hω_ne : (ω u : ℂ) ≠ (ω u⁻¹ : ℂ) := by
      intro hEq
      apply hω_units_ne
      exact Units.ext hEq
    have hsource :
        (((Representation.mackeyTwist H H
            (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation) s).ρ x) (1 : ℂ)) =
          (ω u⁻¹ : ℂ) := by
      -- On the twisted side, the explicit conjugation map sends the witness top-left entry to
      -- `u⁻¹`.
      change (((sl2UpperTriangularSubgroup.character k ω).toRepresentation
          (sl2_upper_triangular_mackey_conj_hom (k := k) s x)) (1 : ℂ)) = (ω u⁻¹ : ℂ)
      simp [MonoidHom.toRepresentation, LinearMap.lsmul_apply, sl2UpperTriangularSubgroup.character,
        hx_conj_top]
    have htarget :
        (((Rep.res (Representation.mackeySubgroup H H s).subtype
            (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)).ρ x) (1 : ℂ)) =
          (ω u : ℂ) := by
      -- On the restricted side, the same witness still has top-left entry `u`.
      change (((sl2UpperTriangularSubgroup.character k ω).toRepresentation x.1) (1 : ℂ)) =
        (ω u : ℂ)
      simp [MonoidHom.toRepresentation, LinearMap.lsmul_apply, sl2UpperTriangularSubgroup.character,
        hx_top]
    have hsource_target_ne :
        (((Representation.mackeyTwist H H
            (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation) s).ρ x) (1 : ℂ)) ≠
          (((Rep.res (Representation.mackeySubgroup H H s).subtype
            (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)).ρ x) (1 : ℂ)) := by
      rw [hsource, htarget]
      exact hω_ne.symm
    exact hom_zero_of_action_on_one_mismatch
      (ρ := (Representation.mackeyTwist H H
        (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation) s).ρ)
      (σ := (Rep.res (Representation.mackeySubgroup H H s).subtype
        (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)).ρ)
      ⟨x, hsource_target_ne⟩ f

end Irreducibility
