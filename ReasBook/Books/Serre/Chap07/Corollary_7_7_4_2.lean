import Mathlib
import Serre.Chap07.Proposition_7_7_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Representation

noncomputable section

universe u v

namespace Representation

section

open Rep (of)

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {W : Type v} [AddCommGroup W] [Module k W]

-- Source/core/bridge triage:
-- * source-facing: Serre's normal-subgroup form of Mackey's irreducibility criterion.
-- * core/canonical owners: `Rep.ind`, `Rep.of`, `Representation.IsIrreducible`,
--   `Representation.Equiv`, and the Chapter 7 conjugation owner `ρ ^ s`.
-- * bridge/view: this corollary keeps the source-facing ordinary representation `ρ`, but phrases
--   induction through the bundled owner `Rep.ind H.subtype (of ρ)` rather than a parallel raw
--   induced-representation surface. The irreducibility transport for conjugates already lives on
--   the owner file `Proposition_7_7_3_1.lean`, so this corollary reuses it rather than
--   redefining it.
-- * primitive data: a normal subgroup `H ≤ G` and a representation `ρ : Representation k H W`.
-- * derived API: irreducibility of the induced owner, irreducibility of conjugates via
--   `Representation.IsIrreducible.pow`, and nonisomorphism with conjugates.

-- Proof sketch: apply Proposition `7-7.4-1`. When `H` is normal, the Mackey subgroup `H_s`
-- is canonically the whole subgroup, and the Mackey twist is restriction of `Rep.of ρ` along the
-- conjugation automorphism `MulAut.conjNormal s⁻¹ : H ≃* H`, so the disjointness condition
-- becomes the nonexistence of an equivalence between `ρ` and its conjugate `ρ^s`; the owner
-- theorem `Representation.IsIrreducible.pow` supplies the corresponding irreducibility transport.
-- The same field, algebraic-closure, and Maschke nonvanishing hypotheses are inherited from
-- Proposition `7-7.4-1`.
/-- Helper for Corollary 7-7.4-2: if `H` is normal, then the Mackey subgroup `H_s` attached to
`H` and `s` is all of `H`. -/
theorem mackeySubgroup_self_eq_top_of_normal
    (H : Subgroup G) [H.Normal] (s : G) :
    mackeySubgroup H H s = ⊤ := by
  -- Normality makes the conjugation condition defining `H_s` automatic for every `h ∈ H`.
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    simpa [mackeySubgroup, mul_assoc] using
      (Subgroup.Normal.conj_mem' inferInstance (x : G) x.2 s)

/-- Helper for Corollary 7-7.4-2: an irreducible representation has a nontrivial carrier space. -/
theorem irreducible_nontrivial_for_normal_corollary
    {H : Subgroup G} (ρ : Representation k H W) [ρ.IsIrreducible] : Nontrivial W := by
  -- If the carrier were subsingleton, the zero and whole subrepresentations would coincide.
  classical
  by_contra hW
  letI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  exact bot_ne_top hbot_top

/-- Helper for Corollary 7-7.4-2: forgetting the `Rep` packaging in the normal Mackey coordinate
produces an intertwiner from `ρ ^ s` to `ρ`. -/
noncomputable def normal_mackey_intertwining_to_conjugate
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) (s : G) :
    ((mackeyTwist H H (of ρ) s).ρ).IntertwiningMap
        ((Rep.res (mackeySubgroup H H s).subtype (of ρ)).ρ) →ₗ[k]
      ((ρ ^ s).IntertwiningMap ρ) where
  toFun f := by
    refine
      { toLinearMap := f.toLinearMap
        isIntertwining' := ?_ }
    intro h
    ext w
    have hhK_mem : h ∈ mackeySubgroup H H s := by
      simpa [mackeySubgroup, mul_assoc] using
        (Subgroup.Normal.conj_mem' inferInstance (h : G) h.2 s)
    let hK : mackeySubgroup H H s := ⟨h, hhK_mem⟩
    have hcomm := Representation.IntertwiningMap.isIntertwining (f := f) (g := hK) (v := w)
    have hhconj_mem : s⁻¹ * ↑h * s ∈ H := by
      simpa [mackeySubgroup] using hhK_mem
    have hconj_eq :
        ((MulAut.conjNormal s).symm h) = ⟨s⁻¹ * ↑h * s, hhconj_mem⟩ := by
      ext
      simp [MulAut.conjNormal_symm_apply, mul_assoc]
    simpa [Representation.pow_apply, hK, mackeyTwist, Rep.res_obj_ρ, hconj_eq] using hcomm
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_smul' a f := by
    apply Representation.IntertwiningMap.ext
    rfl

/-- Helper for Corollary 7-7.4-2: an intertwiner `ρ ^ s → ρ` restricts to the normal-case Mackey
coordinate map. -/
noncomputable def normal_mackey_intertwining_from_conjugate
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) (s : G) :
    ((ρ ^ s).IntertwiningMap ρ) →ₗ[k]
      ((mackeyTwist H H (of ρ) s).ρ).IntertwiningMap
        ((Rep.res (mackeySubgroup H H s).subtype (of ρ)).ρ) where
  toFun g := by
    refine LinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ := (mackeyTwist H H (of ρ) s).ρ)
      (σ := (Rep.res (mackeySubgroup H H s).subtype (of ρ)).ρ)
      g.toLinearMap ?_
    intro x w
    have hconj_mem : s⁻¹ * ↑x.1 * s ∈ H := by
      simpa [mul_assoc] using (Subgroup.Normal.conj_mem' inferInstance (x.1 : G) x.1.2 s)
    have hconj_eq :
        ((MulAut.conjNormal s).symm x.1) = ⟨s⁻¹ * ↑x.1 * s, hconj_mem⟩ := by
      ext
      simp [MulAut.conjNormal_symm_apply, mul_assoc]
    simpa [Representation.pow_apply, mackeyTwist, Rep.res_obj_ρ, hconj_eq] using
      (Representation.IntertwiningMap.isIntertwining (f := g) (g := x.1) (v := w))
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_smul' a f := by
    apply Representation.IntertwiningMap.ext
    rfl

/-- Helper for Corollary 7-7.4-2: after forgetting the `Rep` packaging, the normal-case Mackey
coordinate maps are exactly the intertwining maps from `ρ ^ s` to `ρ`. -/
noncomputable def normal_mackey_intertwining_equiv_conjugate
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) (s : G) :
    ((mackeyTwist H H (of ρ) s).ρ).IntertwiningMap
        ((Rep.res (mackeySubgroup H H s).subtype (of ρ)).ρ) ≃ₗ[k]
      ((ρ ^ s).IntertwiningMap ρ) where
  __ := normal_mackey_intertwining_to_conjugate (H := H) ρ s
  invFun := normal_mackey_intertwining_from_conjugate (H := H) ρ s
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    rfl
  right_inv g := by
    apply Representation.IntertwiningMap.ext
    rfl

/-- Helper for Corollary 7-7.4-2: in the normal-subgroup case, the Mackey-coordinate morphisms are
exactly the intertwining maps from the conjugate representation `ρ ^ s` to `ρ`. -/
noncomputable def normal_mackey_hom_equiv_conjugate
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) (s : G) :
    (mackeyTwist H H (of ρ) s ⟶ Rep.res (mackeySubgroup H H s).subtype (of ρ)) ≃ₗ[k]
      ((ρ ^ s).IntertwiningMap ρ) :=
  (Rep.homLinearEquiv _ _) ≪≫ₗ normal_mackey_intertwining_equiv_conjugate (H := H) ρ s

/-- Helper for Corollary 7-7.4-2: under irreducibility, Mackey disjointness in the normal case is
exactly nonisomorphism with the conjugate representation. -/
theorem normal_mackey_disjoint_iff_not_isomorphic
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) [ρ.IsIrreducible] (s : G) :
    (∀ f : mackeyTwist H H (of ρ) s ⟶ Rep.res (mackeySubgroup H H s).subtype (of ρ), f = 0) ↔
      ¬ Nonempty ((ρ ^ s).Equiv ρ) := by
  constructor
  · intro h hiso
    rcases hiso with ⟨e⟩
    let eHom := normal_mackey_hom_equiv_conjugate (H := H) ρ s
    have hmackey_zero : eHom.symm e.toIntertwiningMap = 0 := h (eHom.symm e.toIntertwiningMap)
    have hzero : e.toIntertwiningMap = 0 := by
      simpa using congrArg eHom hmackey_zero
    letI : Nontrivial W := irreducible_nontrivial_for_normal_corollary ρ
    have hnot_bijective_zero : ¬ Function.Bijective (0 : (ρ ^ s).IntertwiningMap ρ) := by
      intro hzero_bij
      obtain ⟨x, hx⟩ := exists_ne (0 : W)
      exact hx <| hzero_bij.injective (by simp)
    exact hnot_bijective_zero <| by simpa [hzero] using e.bijective
  · intro h f
    let eHom := normal_mackey_hom_equiv_conjugate (H := H) ρ s
    have hpow : (ρ ^ s).IsIrreducible := Representation.IsIrreducible.pow ρ s
    letI : (ρ ^ s).IsIrreducible := hpow
    by_contra hf
    have hne : eHom f ≠ 0 := by
      intro hzero
      exact hf (eHom.injective hzero)
    rcases Representation.IsIrreducible.bijective_or_eq_zero
        (ρ := ρ ^ s) (σ := ρ) (f := eHom f) with hbij | hzero
    · exact h ⟨(eHom f).ofBijective hbij⟩
    · exact hne hzero

/-- Corollary 7-7.4-2: if `H` is normal in `G`, then the induced representation `Ind_H^G(ρ)` is
irreducible if and only if `ρ` is irreducible and, for every `s ∉ H`, the conjugate
representation `ρ^s` is not isomorphic to `ρ`. -/
theorem ind_isIrreducible_iff_isIrreducible_and_not_isomorphic_to_conjugates
    [IsAlgClosed k] (H : Subgroup G) [H.Normal] (ρ : Representation k H W) :
    (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible ↔
      ρ.IsIrreducible ∧
        ∀ s : G, s ∉ H →
          ¬ Nonempty ((ρ ^ s).Equiv ρ) := by
  -- Route correction: specialize the Mackey criterion and rewrite each Mackey-coordinate vanishing
  -- condition as the absence of an equivalence `ρ ^ s ≃ ρ`.
  refine (ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint (H := H) (ρ := ρ)).trans ?_
  constructor
  · rintro ⟨hρ, hmackey⟩
    refine ⟨hρ, ?_⟩
    intro s hs
    letI : ρ.IsIrreducible := hρ
    exact (normal_mackey_disjoint_iff_not_isomorphic (H := H) ρ s).1 (hmackey s hs)
  · rintro ⟨hρ, hconj⟩
    refine ⟨hρ, ?_⟩
    intro s hs f
    letI : ρ.IsIrreducible := hρ
    exact (normal_mackey_disjoint_iff_not_isomorphic (H := H) ρ s).2 (hconj s hs) f

end

end Representation
