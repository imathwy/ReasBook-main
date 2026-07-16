import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators SubgroupInduction

universe u v w uk

namespace Representation

section InducedCharacters

open Subgroup

variable {k : Type uk} [Field k]
variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {W : Type (max w uk)} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

local instance subgroupDecidablePred (H : Subgroup G) : DecidablePred fun g : G ↦ g ∈ H :=
  Classical.decPred _

omit [FiniteDimensional k V] in
/-- The character of a finite-dimensional representation over any field is a class function. -/
theorem character_isClassFunction (ρ : Representation k G V) : IsClassFunction ρ.character := by
  refine ⟨?_⟩
  intro x y hxy
  rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp hxy) with ⟨a, ha⟩
  rw [← ha]
  exact (ρ.char_conj x a).symm

/-- Helper for Theorem 3-3.3-4: the chosen representatives identify the coinduced model with the
space of `W`-valued functions on the representative set by evaluating at inverse
representatives. -/
noncomputable def coindRepresentativeEquiv
    (H : Subgroup G) (θ : Representation k H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) :
    Representation.coindV H.subtype θ ≃ₗ[k] (↥(R : Set G) → W) where
  toFun f r := f.1 ((r : G)⁻¹)
  invFun ξ :=
    ⟨fun g ↦
      let x := hR.equiv g⁻¹
      θ x.2⁻¹ (ξ x.1), by
      intro h g
      -- Move the subgroup factor in the complement decomposition to the coefficient in `θ`.
      simpa [mul_assoc, ← Module.End.mul_apply, ← map_mul] using
        congrArg
          (fun x : ↥(R : Set G) × H ↦ θ x.2⁻¹ (ξ x.1))
          (hR.equiv_mul_right g⁻¹ h⁻¹)⟩
  map_add' _ _ := by
    ext r
    simp
  map_smul' _ _ := by
    ext r
    simp
  left_inv f := by
    ext g
    let x := hR.equiv g⁻¹
    have hg : ((x.2 : H) : G)⁻¹ * ((x.1 : (R : Set G)) : G)⁻¹ = g := by
      simpa [x, mul_inv_rev] using congrArg Inv.inv (hR.equiv_fst_mul_equiv_snd g⁻¹)
    -- The complement decomposition of `g⁻¹` rewrites `g` in the form needed for the coinduction
    -- relation.
    change θ x.2⁻¹ (f.1 (((x.1 : ↥(R : Set G)) : G)⁻¹)) = f.1 g
    simpa [hg] using
      ((f.2 x.2⁻¹ (((x.1 : (R : Set G)) : G)⁻¹)).symm)
  right_inv ξ := by
    ext r
    -- At a representative inverse, the complement decomposition is the trivial one `r * 1`.
    have hfst :
        (hR.equiv (r : G)).fst = r :=
      hR.equiv_fst_eq_self_of_mem_of_one_mem (show (1 : G) ∈ H by simp) r.property
    have hsnd :
        (hR.equiv (r : G)).snd = (1 : H) :=
      hR.equiv_snd_eq_one_of_mem_of_one_mem (show (1 : G) ∈ H by simp) r.property
    dsimp
    simp [hfst, hsnd]

/-- Helper for Theorem 3-3.3-4: the representative attached to the left coset of `u * r`. -/
noncomputable def representative_target
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G)) : ↥(R : Set G) :=
  (hR.equiv (u * r)).fst

/-- Helper for Theorem 3-3.3-4: the subgroup element in the decomposition `u * r = r_u * t_u`. -/
noncomputable def representative_element
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G)) : H :=
  (hR.equiv (u * r)).snd

/-- Helper for Theorem 3-3.3-4: the chosen representative `r` is fixed by multiplication by `u`
exactly when `r⁻¹ * u * r` lies in `H`. -/
lemma representative_target_eq_self_iff
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G)) :
    representative_target H R hR u r = r ↔ (r : G)⁻¹ * u * r ∈ H := by
  constructor
  · intro hr
    change (hR.equiv (u * r)).fst = r at hr
    have hdecomp := hR.equiv_fst_mul_equiv_snd (u * r)
    rw [hr] at hdecomp
    have ht : (((representative_element H R hR u r : H) : G)) = (r : G)⁻¹ * u * r := by
      change (((hR.equiv (u * r)).snd : H) : G) = (r : G)⁻¹ * u * r
      -- Rewrite the complement decomposition of `u * r` using the fixed-point hypothesis.
      calc
        (((hR.equiv (u * r)).snd : H) : G)
            = (r : G)⁻¹ * ((r : G) * (((hR.equiv (u * r)).snd : H) : G)) := by
                simp
        _ = (r : G)⁻¹ * (u * r) := by rw [hdecomp]
        _ = (r : G)⁻¹ * u * r := by simp [mul_assoc]
    simpa [ht] using (representative_element H R hR u r).property
  · intro hur
    have hleft : LeftCosetEquivalence H (u * r : G) (r : G) := by
      simpa [LeftCosetEquivalence, leftCoset_eq_iff, mul_assoc] using H.inv_mem hur
    have hfst :
        (hR.equiv (u * r)).fst = (hR.equiv (r : G)).fst :=
      (hR.equiv_fst_eq_iff_leftCosetEquivalence).2 hleft
    -- Both `r` and the chosen representative of `u * r` lie in `R`, so equality of left cosets
    -- forces equality of representatives.
    change (hR.equiv (u * r)).fst = r
    exact hfst.trans (hR.equiv_fst_eq_self_of_mem_of_one_mem
      (show (1 : G) ∈ H by simp) r.property)

/-- Helper for Theorem 3-3.3-4: on a fixed representative, the subgroup factor in the complement
decomposition is exactly `r⁻¹ * u * r`. -/
lemma representative_element_eq_conj_of_target_eq_self
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G))
    (hr : representative_target H R hR u r = r) :
    representative_element H R hR u r =
      ⟨(r : G)⁻¹ * u * r, (representative_target_eq_self_iff H R hR u r).1 hr⟩ := by
  ext
  -- Once the representative is fixed, the complement decomposition `u * r = r * t` identifies
  -- the subgroup term with the conjugate `r⁻¹ * u * r`.
  change (hR.equiv (u * r)).fst = r at hr
  have hdecomp := hR.equiv_fst_mul_equiv_snd (u * r)
  rw [hr] at hdecomp
  change (((hR.equiv (u * r)).snd : H) : G) = (r : G)⁻¹ * u * r
  calc
    (((hR.equiv (u * r)).snd : H) : G)
        = (r : G)⁻¹ * ((r : G) * (((hR.equiv (u * r)).snd : H) : G)) := by
            simp
    _ = (r : G)⁻¹ * (u * r) := by rw [hdecomp]
    _ = (r : G)⁻¹ * u * r := by simp [mul_assoc]

/-- Helper for Theorem 3-3.3-4: the inverse translate of the target representative decomposes as
the original representative times the inverse subgroup element from `u * r = r_u * t_u`. -/
lemma representative_inverse_target_decomposition
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G)) :
    hR.equiv (u⁻¹ * representative_target H R hR u r) =
      (r, (representative_element H R hR u r)⁻¹) := by
  -- Rewriting the complement decomposition of `u * r` gives the inverse translate directly.
  apply hR.equiv.symm.injective
  simp only [Subgroup.IsComplement.equiv_symm_apply]
  rw [hR.equiv_fst_mul_equiv_snd]
  have hdecomp :
      (representative_target H R hR u r : G) *
          (((representative_element H R hR u r : H) : G)) =
        u * r :=
    hR.equiv_fst_mul_equiv_snd (u * r)
  calc
    u⁻¹ * representative_target H R hR u r
        = u⁻¹ * (representative_target H R hR u r *
            (((representative_element H R hR u r : H) : G) *
              (((representative_element H R hR u r)⁻¹ : H) : G))) := by
            simp
    _ = u⁻¹ * (((representative_target H R hR u r : G) *
            (((representative_element H R hR u r : H) : G))) *
              (((representative_element H R hR u r)⁻¹ : H) : G)) := by
          simp [mul_assoc]
    _ = u⁻¹ * ((u * r) * (((representative_element H R hR u r)⁻¹ : H) : G)) := by
          rw [hdecomp]
    _ = (r : G) * (((representative_element H R hR u r)⁻¹ : H) : G) := by
          simp [mul_assoc]

/-- Helper for Theorem 3-3.3-4: the representative in the decomposition of `u⁻¹ * s` is `r`
exactly when `s` is the representative attached to `u * r`. -/
lemma representative_inverse_fst_eq_iff
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r s : ↥(R : Set G)) :
    (hR.equiv (u⁻¹ * s : G)).fst = r ↔ s = representative_target H R hR u r := by
  constructor
  · intro hs
    have hdecomp := hR.equiv_fst_mul_equiv_snd (u⁻¹ * s : G)
    rw [hs] at hdecomp
    have hs_eq :
        (s : G) = u * r * (((hR.equiv (u⁻¹ * s : G)).snd : H) : G) := by
      have hs_eq' :
          u * ((r : G) * (((hR.equiv (u⁻¹ * s : G)).snd : H) : G)) = (s : G) := by
        simpa [mul_assoc] using congrArg (fun x : G ↦ u * x) hdecomp
      simpa [mul_assoc] using hs_eq'.symm
    have hs_mem : (s : G)⁻¹ * (u * r) ∈ H := by
      rw [hs_eq]
      simp [mul_assoc]
    have hleft : LeftCosetEquivalence H (s : G) (u * r : G) := by
      simpa [LeftCosetEquivalence, leftCoset_eq_iff] using hs_mem
    have hfst :
        (hR.equiv (s : G)).fst = (hR.equiv (u * r : G)).fst :=
      (hR.equiv_fst_eq_iff_leftCosetEquivalence).2 hleft
    have hs_self :
        (hR.equiv (s : G)).fst = s :=
      hR.equiv_fst_eq_self_of_mem_of_one_mem (show (1 : G) ∈ H by simp) s.property
    exact hs_self.symm.trans hfst
  · intro hs
    subst s
    simpa using congrArg Prod.fst (representative_inverse_target_decomposition H R hR u r)

/-- Helper for Theorem 3-3.3-4: after transporting the coinduced action to the representative
coordinate model, a single basis vector at `r` is sent to the single basis vector at the
representative of `u * r`, with coefficient twisted by the corresponding subgroup element. -/
lemma coindRepresentativeEquiv_action_single
    (H : Subgroup G) (θ : Representation k H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G)
    [DecidableEq ↥(R : Set G)]
    (r : ↥(R : Set G)) (w : W) :
    let T_u : (↥(R : Set G) → W) →ₗ[k] (↥(R : Set G) → W) :=
      (coindRepresentativeEquiv H θ R hR).conj ((θ.coind H.subtype) u)
    T_u (Pi.single r w) =
      Pi.single (representative_target H R hR u r)
        (θ (representative_element H R hR u r) w) := by
  classical
  -- Evaluate the conjugated coinduced action at each representative coordinate.
  ext s
  simp only [LinearEquiv.conj_apply_apply, Pi.single_apply]
  show
    (((θ.coind H.subtype) u) ((coindRepresentativeEquiv H θ R hR).symm (Pi.single r w))).1
        ((s : G)⁻¹) =
      if s = representative_target H R hR u r then
        θ (representative_element H R hR u r) w
      else 0
  change
    ((coindRepresentativeEquiv H θ R hR).symm (Pi.single r w)).1 ((s : G)⁻¹ * u) =
      if s = representative_target H R hR u r then
        θ (representative_element H R hR u r) w
      else 0
  by_cases hs : s = representative_target H R hR u r
  · subst s
    -- At the target representative, the decomposition of `u⁻¹ * r_u` is exactly `r * t_u⁻¹`.
    have hpair :
        hR.equiv ((((representative_target H R hR u r : G)⁻¹) * u)⁻¹) =
          (r, (representative_element H R hR u r)⁻¹) := by
      simpa [representative_target, representative_element, mul_inv_rev] using
        representative_inverse_target_decomposition H R hR u r
    have hsnd :
        (hR.equiv (u⁻¹ * representative_target H R hR u r)).snd =
          (representative_element H R hR u r)⁻¹ := by
      simpa using congrArg Prod.snd
        (representative_inverse_target_decomposition H R hR u r)
    have hfst :
        (hR.equiv ((((representative_target H R hR u r : G)⁻¹) * u)⁻¹)).fst = r := by
      simpa [representative_target, representative_element, mul_inv_rev] using
        congrArg Prod.fst (representative_inverse_target_decomposition H R hR u r)
    rw [if_pos rfl]
    dsimp [coindRepresentativeEquiv]
    rw [hpair]
    simp [representative_target, representative_element]
  · rw [if_neg hs]
    have hfst_ne : (hR.equiv (u⁻¹ * s : G)).fst ≠ r := by
      intro hfst
      exact hs ((representative_inverse_fst_eq_iff H R hR u r s).1 hfst)
    simpa [coindRepresentativeEquiv, hfst_ne, mul_inv_rev]

/-- Helper for Theorem 3-3.3-4: each diagonal matrix entry of the transported coinduced action is
zero unless the representative is fixed; on a fixed representative, it is the corresponding
diagonal entry of the subgroup action. -/
lemma representative_action_diag_entry
    (H : Subgroup G) (θ : Representation k H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G)
    [DecidableEq ↥(R : Set G)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bW : Module.Basis ι k W) (r : ↥(R : Set G)) (i : ι) :
    let T_u : (↥(R : Set G) → W) →ₗ[k] (↥(R : Set G) → W) :=
      (coindRepresentativeEquiv H θ R hR).conj ((θ.coind H.subtype) u)
    LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, i⟩ ⟨r, i⟩ =
      if hfix : representative_target H R hR u r = r then
        LinearMap.toMatrix bW bW (θ (representative_element H R hR u r)) i i
      else 0 := by
  classical
  -- The diagonal entry is the `⟨r,i⟩`-coordinate of the image of the corresponding product-basis
  -- vector under the transported action.
  let T_u : (↥(R : Set G) → W) →ₗ[k] (↥(R : Set G) → W) :=
    (coindRepresentativeEquiv H θ R hR).conj ((θ.coind H.subtype) u)
  change LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, i⟩ ⟨r, i⟩ = _
  rw [LinearMap.toMatrix_apply]
  rw [Pi.basis_apply]
  have haction :
      T_u (Pi.single r (bW i)) =
        Pi.single (representative_target H R hR u r)
          (θ (representative_element H R hR u r) (bW i)) := by
    simpa [T_u] using coindRepresentativeEquiv_action_single H θ R hR u r (bW i)
  rw [haction]
  rw [Pi.basis_repr]
  by_cases hfix : representative_target H R hR u r = r
  · rw [hfix]
    simp [LinearMap.toMatrix_apply]
  · simpa [hfix]

/-- Helper for Theorem 3-3.3-4: the trace of the transported coinduced action is the sum of the
subgroup characters over the representatives fixed by `u`. -/
lemma trace_representative_action_eq_sum
    (H : Subgroup G) (θ : Representation k H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G)
    [DecidableEq ↥(R : Set G)] :
    let T_u : (↥(R : Set G) → W) →ₗ[k] (↥(R : Set G) → W) :=
      (coindRepresentativeEquiv H θ R hR).conj ((θ.coind H.subtype) u)
    LinearMap.trace k (↥(R : Set G) → W) T_u =
      ∑ r : ↥(R : Set G),
        if hfix : representative_target H R hR u r = r then
          θ.character (representative_element H R hR u r)
        else 0 := by
  classical
  let T_u : (↥(R : Set G) → W) →ₗ[k] (↥(R : Set G) → W) :=
    (coindRepresentativeEquiv H θ R hR).conj ((θ.coind H.subtype) u)
  let bW := Module.Free.chooseBasis k W
  -- The product basis turns the global trace into a sum of diagonal blocks indexed by
  -- representatives and basis vectors of `W`.
  change LinearMap.trace k (↥(R : Set G) → W) T_u =
      ∑ r : ↥(R : Set G),
        if hfix : representative_target H R hR u r = r then
          θ.character (representative_element H R hR u r)
        else 0
  rw [LinearMap.trace_eq_matrix_trace k (Pi.basis fun _ ↦ bW) T_u]
  rw [Matrix.trace, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp_rw [Matrix.diag_apply]
  refine Finset.sum_congr rfl ?_
  intro r _
  by_cases hfix : representative_target H R hR u r = r
  · simp [hfix]
    -- On a fixed representative, the whole diagonal block is the matrix of the subgroup action.
    have hdiag :
        ∀ i,
          LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, i⟩ ⟨r, i⟩ =
            LinearMap.toMatrix bW bW (θ (representative_element H R hR u r)) i i := by
      intro i
      simpa [T_u, hfix] using
        representative_action_diag_entry (H := H) (θ := θ) (R := R) (hR := hR) (u := u)
          (bW := bW) (r := r) (i := i)
    calc
      ∑ s,
          LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, s⟩ ⟨r, s⟩
          =
          ∑ s, LinearMap.toMatrix bW bW (θ (representative_element H R hR u r)) s s := by
            refine Finset.sum_congr rfl ?_
            intro s _
            exact hdiag s
      _ = θ.character (representative_element H R hR u r) := by
            -- The inner diagonal sum is the ordinary trace formula for the subgroup operator.
            simpa [Representation.character, Matrix.trace] using
              (LinearMap.trace_eq_matrix_trace k bW
                (θ (representative_element H R hR u r))).symm
  · simp [hfix]
    -- Off the fixed-point locus, the transported action has zero diagonal entries.
    have hdiag :
        ∀ i,
          LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, i⟩ ⟨r, i⟩ = 0 := by
      intro i
      simpa [T_u, hfix] using
        representative_action_diag_entry (H := H) (θ := θ) (R := R) (hR := hR) (u := u)
          (bW := bW) (r := r) (i := i)
    calc
      ∑ s,
          LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, s⟩ ⟨r, s⟩
          = ∑ s, (0 : k) := by
              refine Finset.sum_congr rfl ?_
              intro s _
              exact hdiag s
      _ = 0 := by simp

/-- Helper for Theorem 3-3.3-4: the subtype-indexed sum over fixed representatives is exactly the
textbook `Finset` sum over `r ∈ R` with the condition `r⁻¹ * u * r ∈ H`. -/
lemma representative_subtype_sum_eq_finset_sum
    (H : Subgroup G) (θ : Representation k H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G)
    [DecidableEq ↥(R : Set G)] :
    (∑ r : ↥(R : Set G),
      if hfix : representative_target H R hR u r = r then
        θ.character (representative_element H R hR u r)
      else 0) =
      ∑ r ∈ R,
        if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else 0 := by
  classical
  -- Rewrite the subtype sum as the sum over the attached finset of representatives.
  let attachSum : k := R.attach.sum fun r ↦
      if hfix : representative_target H R hR u r = r then
        θ.character (representative_element H R hR u r)
      else 0
  have hattach :
      attachSum =
        ∑ r ∈ R,
          if hur : r⁻¹ * u * r ∈ H then
            θ.character ⟨r⁻¹ * u * r, hur⟩
          else 0 := by
    dsimp [attachSum]
    rw [← Finset.sum_attach (s := R)
      (f := fun r : G ↦
        if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else 0)]
    refine Finset.sum_congr rfl ?_
    intro r hr
    by_cases hfix : representative_target H R hR u r = r
    · have hur : (r : G)⁻¹ * u * r ∈ H :=
        (representative_target_eq_self_iff H R hR u r).1 hfix
      -- On the fixed branch, the subgroup element in the decomposition is the expected conjugate.
      have hchar :
          θ.character (representative_element H R hR u r) =
            θ.character ⟨(r : G)⁻¹ * u * r, hur⟩ := by
        simpa using congrArg θ.character
          (representative_element_eq_conj_of_target_eq_self H R hR u r hfix)
      simpa [hfix, hur] using hchar
    · have hur : ¬ ((r : G)⁻¹ * u * r ∈ H) := by
        intro hur
        exact hfix ((representative_target_eq_self_iff H R hR u r).2 hur)
      simpa [hfix, hur]
  change attachSum = ∑ r ∈ R, if hur : r⁻¹ * u * r ∈ H then θ.character ⟨r⁻¹ * u * r, hur⟩ else 0
  exact hattach

-- Proof sketch: first identify `ρ.character` with the canonical induced class function
-- `Ind[H](θ.character)` by `character_eq_inducedClassFunction_of_equiv_induced`. The quotient-level
-- owner formula `character_eq_leftCosetInductionSum_of_equiv_induced` rewrites this value as the
-- standard sum over left cosets, and the remaining step is the source-facing reindexing of that
-- quotient sum by the chosen representatives `r ∈ R`.
omit [FiniteDimensional k V] in
/-- Theorem 3-3.3-4: if `ρ` is equivalent to the representation induced from `θ` on the subgroup
`H`, then for any finite system `R` of representatives of the left cosets `G / H`, the
character value
`ρ.character u` is the sum of the values of `θ.character` over those representatives `r ∈ R` with
`r⁻¹ * u * r ∈ H`. The source complex formula is the specialization `k = ℂ`. -/
theorem character_eq_sum_over_representatives_of_equiv_induced
    (ρ : Representation k G V) (H : Subgroup G) (θ : Representation k H W)
    (e : ρ.Equiv (ind H.subtype θ)) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G) :
    ρ.character u =
      ∑ r ∈ R,
        if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else 0 := by
  classical
  -- Route correction: the finite-group quotient-sum bridge is stronger than the current theorem.
  -- We instead pass to the finite-index coinduced model controlled by the chosen representatives.
  letI : H.FiniteIndex := (hR.finite_left_iff).1 inferInstance
  calc
    ρ.character u = (ind H.subtype θ).character u := by
      -- Equivalent representations have the same character.
      simpa using congrFun (Representation.char_iso e) u
    _ = (θ.coind H.subtype).character u := by
        -- Finite index identifies the induced and coinduced character values.
      simpa [Rep.of_ρ] using congrFun
        (Representation.char_iso
          (Representation.equivOfIso
            (Rep.indCoindIso (k := k) (S := H) (A := Rep.of θ)))) u
    _ = ∑ r : ↥(R : Set G),
          if hfix : representative_target H R hR u r = r then
            θ.character (representative_element H R hR u r)
          else 0 := by
        -- Rewrite the raw coinduced trace through representative coordinates.
        rw [Representation.character]
        have hcoord :
            LinearMap.trace k ↥(Representation.coindV H.subtype θ) ((θ.coind H.subtype) u)
              =
              LinearMap.trace k (↥(R : Set G) → W)
                ((coindRepresentativeEquiv H θ R hR).conj ((θ.coind H.subtype) u)) := by
          simpa using
            (LinearMap.trace_conj' ((θ.coind H.subtype) u)
              (coindRepresentativeEquiv H θ R hR)).symm
        have hsum := trace_representative_action_eq_sum
          (H := H) (θ := θ) (R := R) (hR := hR) (u := u)
        exact hcoord.trans hsum
    _ = ∑ r ∈ R,
          if hur : r⁻¹ * u * r ∈ H then
            θ.character ⟨r⁻¹ * u * r, hur⟩
          else 0 := by
        -- Rewriting the fixed-point condition gives the textbook representative sum.
        simpa using
          representative_subtype_sum_eq_finset_sum (H := H) (θ := θ) (R := R) (hR := hR) (u := u)

end InducedCharacters

end Representation
