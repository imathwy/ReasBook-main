import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Representation

section

open Module.End Polynomial

variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

-- Source/core/bridge triage:
-- * source-facing: the Chapter 6 character bounds for a finite-order element of a
--   finite-dimensional complex representation.
-- * core/canonical owner: `Representation ℂ G V`, together with the canonical character owner
--   `Representation.character` and the identity-value theorem `Representation.char_one`.
-- * bridge/view: scalar-action consequences are exposed as theorem-level API, not as packaged
--   auxiliary data.
--
-- Primitive data: the representation `ρ`, the element `s`, and the finite-order hypothesis `hs`.
-- Derived API: the equality-to-identity criterion is the character-at-`1` reformulation of the
-- scalar-action equality case.

private lemma charpoly_root_pow_orderOf_eq_one_local
    (ρ : Representation ℂ G V) (s : G) {μ : ℂ}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    μ ^ orderOf s = 1 := by
  -- Push the finite-order relation from `s` to the endomorphism `ρ s`.
  have hρs_pow_eq_one : (ρ s) ^ orderOf s = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  -- Then push the eigenvalue relation through the same power.
  have hμeig : HasEigenvalue (ρ s) μ :=
    (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).2 <|
      (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).1 hμ
  have hμpow : HasEigenvalue (1 : Module.End ℂ V) (μ ^ orderOf s) := by
    simpa [hρs_pow_eq_one] using hμeig.pow (orderOf s)
  obtain ⟨v, hv⟩ := hμpow.exists_hasEigenvector
  -- A nonzero eigenvector for the identity forces the eigenvalue to be `1`.
  have hsmul : (μ ^ orderOf s - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← hv.apply_eq_smul]
    simp
  exact sub_eq_zero.mp <| (smul_eq_zero_iff_left hv.2).mp hsmul

/-- Helper for Exercise 6-6.5-7: every characteristic root of `ρ s` lies on the unit circle when
`s` has finite order. -/
lemma charpoly_root_norm_eq_one_of_isOfFinOrder
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s)
    {μ : ℂ} (hμ : μ ∈ (ρ s).charpoly.roots) :
    ‖μ‖ = 1 := by
  -- The previous helper reduces the norm statement to a root-of-unity calculation.
  have hpow : μ ^ orderOf s = 1 := charpoly_root_pow_orderOf_eq_one_local ρ s hμ
  exact Complex.norm_eq_one_of_pow_eq_one hpow hs.orderOf_pos.ne'

/-- Helper for Exercise 6-6.5-7: a sum of unit complex numbers has norm at most its cardinality. -/
lemma multiset_sum_norm_le_card_of_forall_norm_eq_one
    (zs : Multiset ℂ) (hz : ∀ z ∈ zs, ‖z‖ = 1) :
    ‖zs.sum‖ ≤ zs.card := by
  -- Apply the triangle inequality and then replace every summand norm by `1`.
  calc
    ‖zs.sum‖ ≤ (zs.map fun z ↦ ‖z‖).sum := norm_multiset_sum_le _
    _ = (zs.map fun _ ↦ (1 : ℝ)).sum := by
      refine congrArg Multiset.sum ?_
      exact Multiset.map_congr rfl fun z hz_mem ↦ by simpa using hz z hz_mem
    _ = zs.card := by simp

/-- Helper for Exercise 6-6.5-7: equality in the triangle inequality for a multiset of unit
complex numbers forces all entries to coincide. -/
lemma multiset_exists_eq_of_norm_sum_eq_card_of_forall_norm_eq_one
    (zs : Multiset ℂ) (hz : ∀ z ∈ zs, ‖z‖ = 1) (hsum : ‖zs.sum‖ = zs.card) :
    ∃ w : ℂ, ∀ z ∈ zs, z = w := by
  induction zs using Multiset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      intro z hz_mem
      simp at hz_mem
  | @cons a zs ih =>
      by_cases hzs_zero : zs = 0
      · refine ⟨a, ?_⟩
        intro z hz_mem
        simp [hzs_zero] at hz_mem
        simp [hz_mem]
      have ha : ‖a‖ = 1 := hz a (by simp)
      have hz_tail : ∀ z ∈ zs, ‖z‖ = 1 := fun z hz_mem ↦ hz z (by simp [hz_mem])
      have hsum' : ‖a + zs.sum‖ = zs.card + 1 := by
        simpa using hsum
      have htail_le : ‖zs.sum‖ ≤ zs.card :=
        multiset_sum_norm_le_card_of_forall_norm_eq_one zs hz_tail
      have hnorm_add : ‖a + zs.sum‖ ≤ ‖a‖ + ‖zs.sum‖ := norm_add_le _ _
      -- Equality for the whole sum forces equality for the tail as well.
      have htail_eq : ‖zs.sum‖ = zs.card := by
        nlinarith [hsum', ha, htail_le, hnorm_add]
      have hadd_eq : ‖a + zs.sum‖ = ‖a‖ + ‖zs.sum‖ := by
        nlinarith [hsum', ha, htail_eq, hnorm_add]
      rcases ih hz_tail htail_eq with ⟨w, hw⟩
      -- Equality in the two-term triangle inequality shows `a` points in the same direction as
      -- the tail sum.
      have hsameray : SameRay ℝ a zs.sum :=
        (sameRay_iff_norm_add).2 <| by simpa using hadd_eq
      have hsameray_eq : zs.sum = ‖zs.sum‖ • a := by
        simpa [ha] using (sameRay_iff_norm_smul_eq).1 hsameray
      have hzs : zs = Multiset.replicate zs.card w :=
        (Multiset.eq_replicate_card).2 fun z hz_mem ↦ hw z hz_mem
      have hcard_pos : 0 < zs.card := by
        rw [Multiset.card_pos_iff_exists_mem]
        exact Multiset.exists_mem_of_ne_zero hzs_zero
      have hsum_tail : zs.sum = (zs.card : ℝ) • w := by
        rw [hzs]
        simp
      have hscalar_eq : (zs.card : ℝ) • w = (zs.card : ℝ) • a := by
        calc
          (zs.card : ℝ) • w = zs.sum := hsum_tail.symm
          _ = ‖zs.sum‖ • a := hsameray_eq
          _ = (zs.card : ℝ) • a := by rw [htail_eq]
      have hw_eq_a : w = a :=
        (smul_right_injective ℂ
          (show (zs.card : ℝ) ≠ 0 by exact_mod_cast hcard_pos.ne')).eq_iff.mp hscalar_eq
      refine ⟨w, ?_⟩
      intro z hz_mem
      rcases Multiset.mem_cons.1 hz_mem with rfl | hz_mem
      · exact hw_eq_a.symm
      · exact hw z hz_mem

/-- Helper for Exercise 6-6.5-7: a finite-order endomorphism over `ℂ` is semisimple. -/
lemma representation_isSemisimple_of_isOfFinOrder
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    Module.End.IsSemisimple (ρ s) := by
  -- The endomorphism is annihilated by `X ^ orderOf s - 1`.
  have hpow : (ρ s) ^ orderOf s = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hsep : ((X ^ orderOf s - (1 : ℂ[X]))).Separable := by
    rw [Polynomial.X_pow_sub_one_separable_iff]
    exact_mod_cast hs.orderOf_pos.ne'
  have haeval : Polynomial.aeval (ρ s) (X ^ orderOf s - (1 : ℂ[X])) = 0 := by
    simp [hpow]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval

/-- Helper for Exercise 6-6.5-7: a semisimple complex endomorphism with only one eigenvalue is a
scalar endomorphism. -/
lemma eq_smul_id_of_isSemisimple_of_unique_eigenvalue
    {f : Module.End ℂ V} (hf : f.IsSemisimple)
    {z : ℂ} (hz : ∀ μ : ℂ, HasEigenvalue f μ → μ = z) :
    f = z • 1 := by
  -- Shift by `z`; then it suffices to show the shifted operator has only eigenvalue `0`.
  have hshift : (f - algebraMap ℂ (Module.End ℂ V) z).IsSemisimple :=
    (Module.End.isSemisimple_sub_algebraMap_iff (f := f) (μ := z)).2 hf
  have hzero : f - algebraMap ℂ (Module.End ℂ V) z = 0 := by
    refine (Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue hshift).2 ?_
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    -- An eigenvector for `f - z` with eigenvalue `μ` is an eigenvector for `f` with eigenvalue
    -- `μ + z`.
    have hv_mem : v ∈ f.eigenspace (μ + z) := by
      rw [mem_eigenspace_iff]
      calc
        f v =
            ((f - algebraMap ℂ (Module.End ℂ V) z) +
              algebraMap ℂ (Module.End ℂ V) z) v := by
              simp
        _ = ((f - algebraMap ℂ (Module.End ℂ V) z) v) +
              ((algebraMap ℂ (Module.End ℂ V) z) v) := by
              simp
        _ = μ • v + z • v := by simp [hv.apply_eq_smul]
        _ = (μ + z) • v := by simp [add_smul]
    have hf_eig : HasEigenvalue f (μ + z) := by
      rw [Module.End.hasEigenvalue_iff]
      exact (Submodule.ne_bot_iff _).2 ⟨v, hv_mem, hv.2⟩
    have hz' : μ + z = z := hz (μ + z) hf_eig
    exact add_right_cancel (show μ + z = 0 + z by simpa using hz')
  simpa [sub_eq_zero] using hzero

/-- The modulus of the character value of a finite-dimensional complex representation is bounded by
its degree, equivalently by its value at the identity via `Representation.char_one`. -/
-- Proof sketch: if `s` has finite order, then `ρ s` also has finite order. Over `ℂ`, the
-- eigenvalues of `ρ s` are roots of unity, hence all have modulus `1`, and `ρ.character s` is
-- their sum counted with multiplicity; the triangle inequality gives the bound.
theorem character_norm_le_char_one
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    ‖ρ.character s‖ ≤ Module.finrank ℂ V := by
  -- Rewrite the character as the sum of the characteristic roots.
  rw [Representation.character, trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  calc
    ‖(ρ s).charpoly.roots.sum‖ ≤ ((ρ s).charpoly.roots.map fun μ ↦ ‖μ‖).sum := by
      exact norm_multiset_sum_le _
    _ = ((ρ s).charpoly.roots.map fun _ ↦ (1 : ℝ)).sum := by
      refine congrArg Multiset.sum ?_
      exact Multiset.map_congr rfl fun μ hμ ↦ by
        simpa using charpoly_root_norm_eq_one_of_isOfFinOrder ρ s hs hμ
    _ = ((ρ s).charpoly.roots.card : ℝ) := by simp
    _ = (ρ s).charpoly.natDegree := by
      rw [← Polynomial.Splits.natDegree_eq_card_roots (f := (ρ s).charpoly) (IsAlgClosed.splits _)]
    _ = Module.finrank ℂ V := by
      simpa using (LinearMap.charpoly_natDegree (f := ρ s))

/-- Exercise 6-6.5-7: equality in the character bound occurs exactly when the representing
endomorphism is a homothety. -/
-- Proof sketch: write `ρ.character s` as the sum of the eigenvalues of `ρ s`, which are roots of
-- unity. Equality in the triangle inequality for a sum of complex numbers of modulus `1` holds
-- exactly when they all coincide, which says precisely that all eigenvalues of `ρ s` are equal and
-- therefore `ρ s` is a scalar endomorphism.
theorem character_norm_eq_char_one_iff_exists_smul_id
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    ‖ρ.character s‖ = Module.finrank ℂ V ↔ ∃ z : ℂ, ρ s = z • 1 := by
  constructor
  · intro hnorm
    -- Equality in the norm bound forces all characteristic roots to be equal.
    have hroots_sum : ‖(ρ s).charpoly.roots.sum‖ = ((ρ s).charpoly.roots.card : ℝ) := by
      calc
        ‖(ρ s).charpoly.roots.sum‖ = ‖ρ.character s‖ := by
          rw [Representation.character,
            trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
        _ = Module.finrank ℂ V := hnorm
        _ = (ρ s).charpoly.natDegree := by
          simpa using (LinearMap.charpoly_natDegree (f := ρ s)).symm
        _ = ((ρ s).charpoly.roots.card : ℝ) := by
          rw [Polynomial.Splits.natDegree_eq_card_roots (f := (ρ s).charpoly)
            (IsAlgClosed.splits _)]
    have hconst : ∃ z : ℂ, ∀ μ ∈ (ρ s).charpoly.roots, μ = z := by
      refine multiset_exists_eq_of_norm_sum_eq_card_of_forall_norm_eq_one _ ?_ hroots_sum
      intro μ hμ
      exact charpoly_root_norm_eq_one_of_isOfFinOrder ρ s hs hμ
    rcases hconst with ⟨z, hz⟩
    have hunique : ∀ μ : ℂ, HasEigenvalue (ρ s) μ → μ = z := by
      intro μ hμ
      have hroot : μ ∈ (ρ s).charpoly.roots := by
        refine (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).2 ?_
        exact (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).1 hμ
      exact hz μ hroot
    -- Route correction: the equality case is closed directly from the root geometry and
    -- semisimplicity of a finite-order operator, without importing later Chapter 6 items.
    exact ⟨z,
      eq_smul_id_of_isSemisimple_of_unique_eigenvalue
        (representation_isSemisimple_of_isOfFinOrder ρ s hs) hunique⟩
  · rintro ⟨z, hz⟩
    -- A scalar operator has character `z * dim`; in positive dimension `z` is itself an
    -- eigenvalue, so its norm is `1`.
    by_cases hdim : Module.finrank ℂ V = 0
    · simp [Representation.character, hz, hdim]
    · have hdim_pos : 0 < Module.finrank ℂ V := Nat.pos_of_ne_zero hdim
      have hz_eig : HasEigenvalue (ρ s) z := by
        rw [Module.End.hasEigenvalue_iff]
        rcases (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := V)).1 hdim_pos with
          ⟨v, hv⟩
        exact (Submodule.ne_bot_iff _).2 ⟨v, by rw [mem_eigenspace_iff, hz]; simp, hv⟩
      have hz_root : z ∈ (ρ s).charpoly.roots :=
        (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).2 <|
          (hasEigenvalue_iff_isRoot_charpoly (ρ s) z).1 hz_eig
      have hz_norm : ‖z‖ = 1 := charpoly_root_norm_eq_one_of_isOfFinOrder ρ s hs hz_root
      have hchar : ρ.character s = z * Module.finrank ℂ V := by
        simp [Representation.character, hz]
      rw [hchar]
      simp [hz_norm]

/-- A finite-dimensional complex representation sends a finite-order element `s` to the identity
exactly when the character at `s` equals the degree of the representation, equivalently the
character at `1` via `Representation.char_one`. -/
-- Proof sketch: if `ρ s = 1`, then the character is the trace of the identity, hence the degree.
-- Conversely, if `ρ.character s = ρ.character 1`, then `Representation.char_one` rewrites this as
-- equality in the previous criterion, so `ρ s` is scalar; comparing traces shows that the scalar
-- is `1`.
theorem eq_one_iff_character_eq_char_one
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    ρ s = 1 ↔ ρ.character s = ρ.character 1 := by
  constructor
  · intro hs_one
    -- The forward implication is the trace computation for the identity endomorphism.
    rw [Representation.character, hs_one, Representation.char_one]
    simp
  · intro hchar
    -- Rewrite the character equality as equality in the norm bound.
    have hnorm : ‖ρ.character s‖ = Module.finrank ℂ V := by
      rw [hchar, Representation.char_one]
      simp
    rcases (character_norm_eq_char_one_iff_exists_smul_id ρ s hs).1 hnorm with ⟨z, hz⟩
    by_cases hdim : Module.finrank ℂ V = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.mp hdim
      exact Subsingleton.elim _ _
    · -- In positive dimension, comparing traces forces the scalar to be `1`.
      have hzchar : (Module.finrank ℂ V : ℂ) = z * Module.finrank ℂ V := by
        have hzchar' : ρ.character s = z * Module.finrank ℂ V := by
          simp [Representation.character, hz]
        rw [hchar, Representation.char_one] at hzchar'
        exact hzchar'
      have hz_eq_one : z = 1 := by
        apply mul_right_cancel₀ (show (Module.finrank ℂ V : ℂ) ≠ 0 by exact_mod_cast hdim)
        simpa [mul_comm] using hzchar.symm
      simpa [hz_eq_one] using hz

end

end Representation
