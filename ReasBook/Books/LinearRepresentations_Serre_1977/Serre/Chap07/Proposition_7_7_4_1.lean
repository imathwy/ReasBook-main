import Mathlib.LinearAlgebra.Projection
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_3_1
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_3_2
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientMainProposition7741 (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

omit [Finite G] [NeZero (Nat.card G : k)] in
/-- Helper for Proposition 7-7.4-1: transporting a Mackey coordinate along an equality of double
cosets preserves and reflects vanishing. -/
theorem mackey_coordinate_equiv_of_same_doubleCoset_eq_zero_iff
    (H : Subgroup G) (ρ : Representation k H V)
    {s t : G}
    (hst : DoubleCoset.mk H H s = DoubleCoset.mk H H t)
    (f : mackeyTwist H H (of ρ) s ⟶
      Rep.res (mackeySubgroup H H s).subtype (of ρ)) :
    (mackey_coordinate_equiv_of_same_doubleCoset (k := k) H ρ
      (s := s) (t := t) hst f = 0) ↔ f = 0 := by
  constructor
  · intro hf
    -- The same-double-coset transport is a linear equivalence, so its image can vanish only when
    -- the original coordinate already vanishes.
    exact
      (mackey_coordinate_equiv_of_same_doubleCoset (k := k) H ρ
        (s := s) (t := t) hst).injective <| by
          simpa using hf
  · intro hf
    -- Conversely, the transport sends the zero coordinate to zero.
    rw [hf]
    simp

/-- Proposition 7-7.4-1: Mackey's irreducibility criterion for an induced representation
`Ind_H^G(ρ)`: it is irreducible exactly when `ρ` is irreducible and all off-subgroup Mackey
intertwining spaces vanish. -/
theorem ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
    [IsAlgClosed k] (H : Subgroup G) (ρ : Representation k H V) :
    (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible ↔
      ρ.IsIrreducible ∧
        ∀ s ∉ H,
          ∀ f : mackeyTwist H H (of ρ) s ⟶
              Rep.res (mackeySubgroup H H s).subtype (of ρ),
            f = 0 := by
  -- Follow Serre's Schur step over an algebraically closed field: global endomorphisms of an
  -- irreducible induced representation are scalar, while an off-identity Mackey singleton has zero
  -- identity coordinate.
  constructor
  · intro hInd
    have hρ : ρ.IsIrreducible := isIrreducible_of_ind_isIrreducible H ρ hInd
    refine ⟨hρ, ?_⟩
    intro s hs f
    letI : ρ.IsIrreducible := hρ
    let q : DoubleCoset.Quotient (H : Set G) H := DoubleCoset.mk H H s
    have hq : q ≠ DoubleCoset.mk H H (1 : G) :=
      doubleCoset_ne_identity_of_not_mem H hs
    have hrep_not_mem : doubleCosetRepresentative H q ∉ H :=
      doubleCosetRepresentative_not_mem_of_ne_identity H hq
    -- Package the contradiction at the representative-indexed Mackey coordinate used by the global
    -- coordinate equivalence.
    let fq :
        mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
          Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ) :=
      (mackey_coordinate_equiv_of_same_doubleCoset (k := k) H ρ
        (s := s) (t := doubleCosetRepresentative H q)
        (by
          calc
            DoubleCoset.mk H H s = q := rfl
            _ = DoubleCoset.mk H H (doubleCosetRepresentative H q) := by
              symm
              exact doubleCosetRepresentative_spec H q)) f
    have hf_zero_of_fq_zero : fq = 0 → f = 0 := by
      -- Reuse the new transport lemma to pull vanishing back across the double-coset
      -- identification instead of re-proving injectivity inline.
      intro hfq
      exact
        (mackey_coordinate_equiv_of_same_doubleCoset_eq_zero_iff
          (k := k) H ρ
          (s := s) (t := doubleCosetRepresentative H q)
          (by
            calc
              DoubleCoset.mk H H s = q := rfl
              _ = DoubleCoset.mk H H (doubleCosetRepresentative H q) := by
                symm
                exact doubleCosetRepresentative_spec H q)
          f).1 <| by
            simpa [fq] using hfq
    let e := induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ
    let xi := singleton_mackey_coordinate_family (k := k) H ρ q fq
    let F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ) := e.symm xi
    have hF_coordinates : e F = xi := by
      simp [F, e]
    by_cases hfq : fq = 0
    · exact hf_zero_of_fq_zero hfq
    have hF_bij : Function.Bijective F.hom :=
      bijective_of_singleton_coordinate_nonzero_of_ind_isIrreducible (k := k) H ρ
        hInd q fq F hF_coordinates hfq
    have hidentity_coordinate_zero :
        (e F) (DoubleCoset.mk H H (1 : G)) = 0 := by
      -- Package the singleton-support computation at the identity double coset into a reusable
      -- coordinate vanishing lemma.
      exact singleton_off_identity_identity_coordinate_eq_zero H ρ hq fq F
        hF_coordinates
    let gF : Rep.of ρ ⟶ Rep.of ρ :=
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        ((e F) (DoubleCoset.mk H H (1 : G)))
    have hgF_zero : gF = 0 := by
      -- The new identity-coordinate helper upgrades the zero coordinate directly to the zero
      -- self-intertwiner of `ρ`.
      simpa [gF] using
        singleton_off_identity_identity_self_hom_eq_zero H ρ hq fq F hF_coordinates
    have hproj_unit_zero :
        ∀ v : V,
          inducedIdentityCopyProjection H ρ
            (F.hom (Representation.IndV.mk H.subtype ρ 1 v)) = 0 := by
      -- The identity Mackey coordinate of the singleton family vanishes, so the transported
      -- endomorphism has zero unit-copy projection on the unit generators.
      intro v
      exact singleton_off_identity_family_projection_eq_zero (k := k) H ρ hq fq F
        hF_coordinates v
    have hrestricted_identity_block_zero :
        ∀ h : H, ∀ v : V,
          (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom
            (Representation.IndV.mk H.subtype ρ (h : G) v)).down = 0 := by
      -- The corrected frontier extends the vanishing from the unit generator to the entire
      -- identity Mackey block viewed through the restricted Frobenius map.
      intro h v
      exact singleton_off_identity_restricted_hom_identity_block_eq_zero (k := k) H ρ
        hq fq F hF_coordinates h v
    have hF_not_bijective : ¬ Function.Bijective F.hom := by
      exact off_identity_singleton_not_bijective_of_ind_isIrreducible
        (k := k) H ρ hInd hq fq hfq F hF_coordinates
    exact False.elim (hF_not_bijective hF_bij)
  · rintro ⟨hρ, hdisjoint⟩
    letI : ρ.IsIrreducible := hρ
    letI : Nontrivial V := irreducible_nontrivial ρ
    letI : Nontrivial (Representation.IndV H.subtype ρ) := by
      -- The unit-coset copy embeds the nontrivial space `V` into the induced representation.
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine ⟨⟨Representation.IndV.mk H.subtype ρ 1 v, 0, ?_⟩⟩
      intro hEq
      have hEq' : Representation.IndV.mk H.subtype ρ 1 v =
          Representation.IndV.mk H.subtype ρ 1 (0 : V) := by
        simpa using hEq
      have := induced_unit_generator_injective (k := k) H ρ hEq'
      exact hv this
    -- It suffices to show that every nonzero endomorphism of the induced representation is
    -- bijective; the coordinate equivalence reduces such an endomorphism to its identity block.
    refine isIrreducible_of_semisimple_and_nonzero_endomorphisms_bijective
      (τ := (Rep.ind H.subtype (of ρ)).ρ) ?_
    intro F hF_ne
    let τ : Rep k G := Rep.ind H.subtype (of ρ)
    let Fhom : τ ⟶ τ := (Rep.homLinearEquiv τ τ).symm F
    let e := induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ
    let g : Rep.of ρ ⟶ Rep.of ρ :=
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        ((e Fhom) (DoubleCoset.mk H H (1 : G)))
    have hsupport :
        ∀ q : DoubleCoset.Quotient (H : Set G) H,
          q ≠ DoubleCoset.mk H H (1 : G) → (e Fhom) q = 0 := by
      intro q hq
      -- Every off-identity coordinate is one of the disjoint Mackey intertwining spaces.
      have hnotmem : doubleCosetRepresentative H q ∉ H :=
        doubleCosetRepresentative_not_mem_of_ne_identity H hq
      exact hdisjoint (doubleCosetRepresentative H q) hnotmem ((e Fhom) q)
    have hFhom_eq :
        Fhom = Rep.indMap H.subtype g :=
      endomorphism_eq_indMap_of_identity_supported (k := k) H ρ Fhom hsupport
    have hF_eq :
        F = (Rep.indMap H.subtype g).hom := by
      have := congrArg (Rep.homLinearEquiv τ τ) hFhom_eq
      simpa [Fhom] using this
    have hg_ne : g ≠ 0 := by
      intro hg
      apply hF_ne
      rw [hF_eq, hg]
      ext x
      simp [Rep.indMap]
    have hg_bij : Function.Bijective g.hom := by
      -- A nonzero endomorphism of the irreducible `H`-representation `ρ` is bijective.
      exact
        (Representation.IsIrreducible.bijective_or_eq_zero
          (ρ := ρ) (σ := ρ) (f := g.hom)).resolve_right <| by
            intro hg_zero
            exact hg_ne (Rep.hom_ext hg_zero)
    -- The previous induction lemma transports bijectivity from `g` to the global endomorphism `F`.
    simpa [hF_eq] using
      (induced_map_bijective_iff_self_hom_bijective (k := k) H ρ g).2 hg_bij
end MackeyIrreducibilityCriterion
#print axioms  ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
end Representation
