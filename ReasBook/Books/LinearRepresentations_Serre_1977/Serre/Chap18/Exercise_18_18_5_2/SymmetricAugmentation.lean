import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.GeneralFieldAugmentation

/-!
# Irreducibility of the standard module of a full symmetric group (support for Exercise 18.5.2)

The semisimple criterion `permutationAugmentationRepresentation_isIrreducible_of_two_pretransitive_overField`
(in `GeneralFieldAugmentation.lean`) proves irreducibility of the augmentation (standard) module via a
Schur/`End`-dimension argument, which requires the whole group order `|G|` to be invertible — useless in
the modular characteristic-`3` branch of Exercise 18.5.2, where `|S₄| = 24 = 0`.

Here we prove the *modular-robust* statement for the **full symmetric group** `Equiv.Perm X`: the
augmentation constituent of `k[X]` is irreducible whenever only `|X|` is invertible in `k`.  The proof is
the classical one and uses no semisimplicity: any nonzero subrepresentation `U` contains a nonzero vector
`w`; since `|X|` is invertible `w` is non-constant, so `w − (a\,b)·w = (w_a − w_b)(e_a − e_b)` is a nonzero
multiple of a coordinate difference, hence `e_a − e_b ∈ U`; transitivity of `Equiv.Perm X` on ordered pairs
then moves it to every coordinate difference, and the differences span the augmentation kernel, so `U = ⊤`.

For `S₄ = Equiv.Perm (Fin 4)` acting on `Fin 4` we have `|X| = 4 = 1 ≠ 0` in characteristic `3`, so this
gives irreducibility of the degree-`3` standard model `std` in characteristic `3`.
-/

attribute [-instance] Field.henselian

noncomputable section

open Representation

namespace Representation

universe u v

variable {k : Type u} [Field k] {X : Type v}

/-- For the full symmetric group there is a permutation carrying any ordered pair of distinct points to
any other ordered pair of distinct points. -/
theorem exists_perm_pair_eq [Finite X] {a b c d : X} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm X, σ a = c ∧ σ b = d := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (![a, b]) (![c, d])
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
  exact ⟨σ, by have := hσ 0; simpa using this, by have := hσ 1; simpa using this⟩

/-- The transposition-difference identity: `w − (a\,b)·w = (w_a − w_b)(e_a − e_b)`. -/
theorem ofMulAction_swap_sub_eq [DecidableEq X] (w : X →₀ k) (a b : X) :
    w - ofMulAction k (Equiv.Perm X) X (Equiv.swap a b) w
      = (w a - w b) • (Finsupp.single a (1 : k) - Finsupp.single b 1) := by
  ext y
  simp only [Finsupp.coe_sub, Pi.sub_apply, ofMulAction_apply, Equiv.Perm.smul_def,
    Equiv.swap_inv, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply,
    Finsupp.coe_sub]
  by_cases hya : y = a
  · subst hya; by_cases hyb : y = b
    · subst hyb; simp
    · rw [Equiv.swap_apply_left]; simp [Ne.symm hyb]
  · by_cases hyb : y = b
    · subst hyb; rw [Equiv.swap_apply_right]; simp [Ne.symm hya]
    · rw [Equiv.swap_apply_of_ne_of_ne hya hyb, if_neg (Ne.symm hya), if_neg (Ne.symm hyb)]; ring

/-- The augmentation kernel `{f : ∑ f = 0}` is spanned by the coordinate differences `e_c − e_d`. -/
theorem augmentation_ker_le_span_diff [Nonempty X] :
    LinearMap.ker (permutationAugmentationLinearMap k X) ≤
      Submodule.span k (Set.range
        (fun p : X × X => Finsupp.single p.1 (1 : k) - Finsupp.single p.2 1)) := by
  classical
  set D := Submodule.span k (Set.range
    (fun p : X × X => Finsupp.single p.1 (1 : k) - Finsupp.single p.2 1)) with hD
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hmem : ∀ f : X →₀ k, f - Finsupp.single x₀ (permutationAugmentationLinearMap k X f) ∈ D := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
        have hsplit : (p + q) - Finsupp.single x₀ (permutationAugmentationLinearMap k X (p + q))
            = (p - Finsupp.single x₀ (permutationAugmentationLinearMap k X p))
              + (q - Finsupp.single x₀ (permutationAugmentationLinearMap k X q)) := by
          rw [map_add, Finsupp.single_add]; abel
        rw [hsplit]; exact D.add_mem hp hq
    | single x c =>
        have haug : permutationAugmentationLinearMap k X (Finsupp.single x c) = c := by
          simp [permutationAugmentationLinearMap]
        rw [haug]
        have hsingle : Finsupp.single x c - Finsupp.single x₀ c
            = c • (Finsupp.single x (1 : k) - Finsupp.single x₀ 1) := by
          simp [smul_sub, Finsupp.smul_single]
        rw [hsingle]
        exact D.smul_mem c (Submodule.subset_span ⟨(x, x₀), rfl⟩)
  intro f hf
  rw [LinearMap.mem_ker] at hf
  have hf' := hmem f
  rw [hf, Finsupp.single_zero, sub_zero] at hf'
  exact hf'

/-- **Modular-robust irreducibility of the standard module.**  For the full symmetric group
`Equiv.Perm X` acting on a finite set `X` with at least two elements, the augmentation constituent of
`k[X]` is irreducible as soon as `|X|` is invertible in `k`.  No invertibility of the (much larger) group
order is required, so this applies in the modular characteristic-`3` branch of Exercise 18.5.2. -/
theorem permutationAugmentationRepresentation_isIrreducible_of_perm_overField
    [Finite X] [Nontrivial X] [Invertible (Nat.card X : k)] :
    (permutationAugmentationRepresentation k (Equiv.Perm X) X).IsIrreducible := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  set K := (permutationAugmentationSubrepresentation k (Equiv.Perm X) X).toSubmodule with hK
  set σ := permutationAugmentationRepresentation k (Equiv.Perm X) X with hσ
  show IsSimpleOrder (Subrepresentation σ)
  -- `K` is the augmentation kernel `ker(∑)`.
  have hKker : K = LinearMap.ker (permutationAugmentationLinearMap k X) := rfl
  -- a nonzero element of `K` (a coordinate difference).
  obtain ⟨a₀, b₀, hab₀⟩ := exists_pair_ne X
  have hdiff_mem : ∀ c d : X, Finsupp.single c (1 : k) - Finsupp.single d 1 ∈ K := by
    intro c d
    rw [hKker, LinearMap.mem_ker, map_sub]
    simp [permutationAugmentationLinearMap]
  -- The lattice of subrepresentations is nontrivial.
  haveI : Nontrivial (Subrepresentation σ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbt
    have hsub : (⊥ : Submodule k K) = ⊤ := by
      have := congrArg Subrepresentation.toSubmodule hbt
      simpa using this
    have hne : (⟨_, hdiff_mem a₀ b₀⟩ : K) ≠ 0 := by
      intro h0
      have : Finsupp.single a₀ (1 : k) - Finsupp.single b₀ 1 = 0 := congrArg Subtype.val h0
      have hval := congrFun (congrArg (DFunLike.coe) this) a₀
      simp [Finsupp.single_apply, hab₀, Ne.symm hab₀] at hval
    have hmem : (⟨_, hdiff_mem a₀ b₀⟩ : K) ∈ (⊥ : Submodule k K) := by
      rw [hsub]; trivial
    rw [Submodule.mem_bot] at hmem
    exact hne hmem
  refine IsSimpleOrder.of_forall_eq_top (α := Subrepresentation σ) ?_
  intro U hU
  -- `U ≠ ⊥` gives a nonzero `w ∈ K` with `∑ w = 0`.
  have hUsub : U.toSubmodule ≠ ⊥ := by
    intro hUb
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa using hUb
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUsub
  set w : X →₀ k := (u : X →₀ k) with hw
  have hw_ne : w ≠ 0 := by
    intro h0
    exact hu_ne (Subtype.ext (by simpa [hw] using h0))
  have hw_ker : permutationAugmentationLinearMap k X w = 0 := by
    have : w ∈ K := u.2
    rwa [hKker, LinearMap.mem_ker] at this
  -- `w` is non-constant.
  have hnonconst : ∃ a b : X, w a ≠ w b := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x₁, hx₁⟩ := Finsupp.support_nonempty_iff.mpr hw_ne
    have hc : w x₁ ≠ 0 := Finsupp.mem_support_iff.mp hx₁
    -- every coordinate equals `w x₁`, so `∑ = |X| • (w x₁)`.
    have hsumeq : permutationAugmentationLinearMap k X w = ∑ x : X, w x := by
      have h1 : permutationAugmentationLinearMap k X w = ∑ x ∈ w.support, w x := by
        simp [permutationAugmentationLinearMap, Finsupp.lsum_apply, Finsupp.sum]
      rw [h1]
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro x _ hx
      rwa [Finsupp.notMem_support_iff] at hx
    have hconst : ∀ x : X, w x = w x₁ := fun x => hcon x x₁
    have hsum2 : ∑ x : X, w x = (Fintype.card X : k) * w x₁ := by
      rw [Finset.sum_congr rfl (fun x _ => hconst x)]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hsumeq, hsum2] at hw_ker
    haveI : Invertible (Fintype.card X : k) := by
      rw [← Nat.card_eq_fintype_card]; infer_instance
    have hcard_ne : (Fintype.card X : k) ≠ 0 := (isUnit_of_invertible _).ne_zero
    exact hc ((mul_eq_zero.mp hw_ker).resolve_left hcard_ne)
  obtain ⟨a, b, hab⟩ := hnonconst
  have hab' : a ≠ b := fun h => hab (by rw [h])
  -- `e_a − e_b ∈ U`.
  set τ := Equiv.swap a b with hτ
  have hστ_mem : σ τ u ∈ U.toSubmodule := U.apply_mem_toSubmodule τ hu_mem
  have hsub_mem : u - σ τ u ∈ U.toSubmodule := U.toSubmodule.sub_mem hu_mem hστ_mem
  -- identify `u − τ·u` with `(w_a − w_b) • (e_a − e_b)` inside `K`.
  have hdiff_ab : u - σ τ u = (w a - w b) • (⟨_, hdiff_mem a b⟩ : K) := by
    apply Subtype.ext
    have hcoeστ : ((σ τ u : K) : X →₀ k) = ofMulAction k (Equiv.Perm X) X τ w := rfl
    change w - ((σ τ u : K) : X →₀ k) = _
    rw [hcoeστ]
    simpa using ofMulAction_swap_sub_eq (k := k) w a b
  have hdab_mem : (⟨_, hdiff_mem a b⟩ : K) ∈ U.toSubmodule := by
    have hscaled : (w a - w b) • (⟨_, hdiff_mem a b⟩ : K) ∈ U.toSubmodule := by
      rw [← hdiff_ab]; exact hsub_mem
    have hne : w a - w b ≠ 0 := sub_ne_zero.mpr hab
    have := U.toSubmodule.smul_mem (w a - w b)⁻¹ hscaled
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  -- every coordinate difference lies in `map K.subtype U.toSubmodule`.
  have hrange : ∀ c d : X, Finsupp.single c (1 : k) - Finsupp.single d 1 ∈
      Submodule.map K.subtype U.toSubmodule := by
    intro c d
    by_cases hcd : c = d
    · subst hcd; simp
    · obtain ⟨g, hga, hgb⟩ := exists_perm_pair_eq hab' hcd
      refine ⟨σ g (⟨_, hdiff_mem a b⟩ : K), U.apply_mem_toSubmodule g hdab_mem, ?_⟩
      change ((σ g (⟨_, hdiff_mem a b⟩ : K) : K) : X →₀ k) = _
      have hcoe : ((σ g (⟨_, hdiff_mem a b⟩ : K) : K) : X →₀ k)
          = ofMulAction k (Equiv.Perm X) X g (Finsupp.single a (1 : k) - Finsupp.single b 1) := rfl
      rw [hcoe, map_sub, ofMulAction_single, ofMulAction_single, Equiv.Perm.smul_def,
        Equiv.Perm.smul_def, hga, hgb]
  -- hence `map K.subtype U.toSubmodule = K`.
  have hmapK : Submodule.map K.subtype U.toSubmodule = K := by
    apply le_antisymm
    · exact Submodule.map_subtype_le K U.toSubmodule
    · refine le_trans (augmentation_ker_le_span_diff (k := k) (X := X)) ?_
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact hrange p.1 p.2
  -- so `U.toSubmodule = ⊤`, hence `U = ⊤`.
  have hUtop : U.toSubmodule = ⊤ := by
    apply Submodule.map_injective_of_injective (Submodule.subtype_injective K)
    rw [hmapK, Submodule.map_subtype_top]
  apply Subrepresentation.toSubmodule_injective
  simpa using hUtop

end Representation
