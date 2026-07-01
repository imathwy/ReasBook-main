import Mathlib
import stacks_project.Chap10.Definition_10_104_1
import stacks_project.Chap10.Lemma_10_5_3
import stacks_project.Chap10.Lemma_10_72_3
import stacks_project.Chap10.Lemma_10_72_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}

/-- Helper for Lemma 10.104.8: a linear equivalence preserves the set of regular-sequence lengths
in a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- Transport each regular sequence across the equivalence and reverse the argument.
  ext n
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.104.8: ideal depth is invariant under a linear equivalence of finite
modules. -/
private theorem idealDepth_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- The branch `I • M = M` is preserved by the equivalence, and otherwise the same
  -- regular-sequence lengths compute the depth on both sides.
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_linearEquiv (R := R) (M := M) (N := N) I e]

/-- Helper for Lemma 10.104.8: a linear equivalence preserves module depth for finite modules. -/
private theorem moduleDepth_eq_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := by
  -- Specialize ideal-depth invariance to the maximal ideal of the local ring.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv (R := R) (M := M) (N := N) (IsLocalRing.maximalIdeal R) e

/-- Helper for Lemma 10.104.8: a finite subsingleton module has depth `⊤`. -/
private theorem moduleDepth_eq_top_of_subsingleton (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M] :
    moduleDepth R M = ⊤ := by
  -- For a zero module, `𝔪 • M = M`, so the depth definition lands in the top branch.
  have htopbot : (⊤ : Submodule R M) = ⊥ := by
    ext x
    simp [Subsingleton.elim x 0]
  have hsmul_bot : IsLocalRing.maximalIdeal R • (⊥ : Submodule R M) = ⊥ := by
    ext x
    simp
  have hsmul : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    rw [htopbot, hsmul_bot]
  change Ideal.depth (IsLocalRing.maximalIdeal R) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal R) M hsmul

/-- Helper for Lemma 10.104.8: a Cohen-Macaulay local ring is nontrivial. -/
private theorem nontrivial_of_cohenMacaulay_self (hCM : Module.CohenMacaulay R R) : Nontrivial R := by
  by_contra hR
  letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
  have hsupp : Module.supportDim R R = ⊥ :=
    Module.supportDim_eq_bot_of_subsingleton (R := R) (M := R)
  have hdepth : Module.supportDim R R = .some (moduleDepth R R) := hCM.supportDim_eq_moduleDepth
  simpa [hsupp] using hdepth

/-- Helper for Lemma 10.104.8: a nonzero finite module has depth at most the ambient Krull
dimension. -/
private theorem moduleDepth_le_ringKrullDim_of_nontrivial {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] {d : ℕ} (hdim : ringKrullDim R = d) :
    moduleDepth R M ≤ d := by
  -- Combine the standard depth-support inequality with the support-dimension upper bound.
  have hdepth :
      WithBot.some (moduleDepth R M : ℕ∞) ≤ Module.supportDim R M :=
    depth_le_supportDim (R := R) (M := M)
  have hsupp : Module.supportDim R M ≤ ringKrullDim R :=
    Module.supportDim_le_ringKrullDim (R := R) (M := M)
  have hle : WithBot.some (moduleDepth R M : ℕ∞) ≤ d := by
    exact le_trans hdepth (by simpa [hdim] using hsupp)
  exact WithBot.coe_le_coe.mp hle

/-- Helper for Lemma 10.104.8: the self-module of a Cohen-Macaulay local ring has depth equal to
the Krull dimension. -/
private theorem moduleDepth_self_eq_ringKrullDim {d : ℕ}
    (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R R = d := by
  -- Rewrite the Cohen-Macaulay self-module equality in the ring-dimension normalization.
  have hdepth : WithBot.some (moduleDepth R R : ℕ∞) = d := by
    simpa [Module.supportDim_self_eq_ringKrullDim, hdim] using hCM.supportDim_eq_moduleDepth.symm
  exact WithBot.coe_eq_coe.mp hdepth

/-- Helper for Lemma 10.104.8: the numerical endgame behind the depth trichotomy is an elementary
fact about natural numbers. -/
private theorem strict_gt_or_both_eq_dim_of_ge_min_succ_nat {a b d : ℕ}
    (hmin : min d (b + 1) ≤ a) (ha : a ≤ d) (hb : b ≤ d) :
    a > b ∨ (a = d ∧ b = d) := by
  -- Separate the quotient depth according to whether it already reaches the ambient dimension.
  rcases lt_or_eq_of_le hb with hb_lt | hb_eq
  · left
    have hsucc : b + 1 ≤ d := Nat.succ_le_of_lt hb_lt
    have hba : b + 1 ≤ a := by
      calc
        b + 1 = min d (b + 1) := (Nat.min_eq_right hsucc).symm
        _ ≤ a := hmin
    exact lt_of_lt_of_le (Nat.lt_succ_self b) hba
  · right
    have hd_le : d ≤ a := by
      simpa [hb_eq] using hmin
    exact ⟨le_antisymm ha hd_le, hb_eq⟩

/-- Helper for Lemma 10.104.8: a finite free module with `n + 1` generators has depth equal to
the ambient Cohen-Macaulay dimension. -/
private theorem moduleDepth_piFinSucc_eq_ringKrullDim {d : ℕ} (n : ℕ)
    (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R (Fin n.succ → R) = d := by
  have hRdepth : moduleDepth R R = d := moduleDepth_self_eq_ringKrullDim (R := R) hCM hdim
  haveI : Nontrivial R := nontrivial_of_cohenMacaulay_self (R := R) hCM
  induction n with
  | zero =>
      -- `Fin 1 → R` is linearly equivalent to `R` itself.
      simpa [hRdepth] using
        (moduleDepth_eq_of_linearEquiv (R := R)
          (M := Fin 1 → R) (N := R) (LinearEquiv.funUnique (Fin 1) R R))
  | succ n ih =>
      let T : ShortComplex (ModuleCat R) :=
        ModuleCat.shortComplexOfCompEqZero
          (LinearMap.inl R R (Fin n.succ → R))
          (LinearMap.snd R R (Fin n.succ → R))
          (by ext x <;> rfl)
      have hT : T.ShortExact :=
        ModuleCat.shortComplex_shortExact T
          Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective
      -- The split exact sequence `0 → R → R × R^n → R^n → 0` forces the middle depth up to `d`.
      have hmid_ge : moduleDepth R (R × (Fin n.succ → R)) ≥ d := by
        have hmiddle := moduleDepth_middle_ge_min (R := R) (S := T) hT
        simpa [T, hRdepth, ih] using hmiddle
      -- The general support-dimension estimate gives the complementary upper bound.
      have hmid_le : moduleDepth R (R × (Fin n.succ → R)) ≤ d :=
        moduleDepth_le_ringKrullDim_of_nontrivial (R := R)
          (M := R × (Fin n.succ → R)) hdim
      have hmid : moduleDepth R (R × (Fin n.succ → R)) = d := le_antisymm hmid_le hmid_ge
      -- Transport the product calculation back to the standard `Fin`-indexed model.
      calc
        moduleDepth R (Fin n.succ.succ → R)
            = moduleDepth R (R × (Fin n.succ → R)) := by
              symm
              exact moduleDepth_eq_of_linearEquiv (R := R)
                (M := R × (Fin n.succ → R)) (N := Fin n.succ.succ → R)
                (Fin.consLinearEquiv R (fun _ : Fin n.succ.succ => R))
        _ = d := hmid

/-- Helper for Lemma 10.104.8: every nonzero finite free finite module over a Cohen-Macaulay local
ring has depth equal to the ambient Krull dimension. -/
private theorem moduleDepth_eq_ringKrullDim_of_nontrivial_finite_free {d : ℕ} {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P] [Nontrivial P]
    (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R P = d := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex R P) R P := Module.Free.chooseBasis R P
  let ι := Module.Free.ChooseBasisIndex R P
  letI : Finite ι := Module.Finite.finite_basis b
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let eBasis : (ι → R) ≃ₗ[R] P := b.equivFun.symm
  let eFin : (Fin (Fintype.card ι) → R) ≃ₗ[R] (ι → R) :=
    LinearEquiv.funCongrLeft R R (Fintype.equivFin ι)
  have hι_nonempty : Nonempty ι := by
    by_contra hι
    letI : IsEmpty ι := not_nonempty_iff.mp hι
    have hsub : Subsingleton P := by
      refine ⟨fun x y ↦ ?_⟩
      have : eBasis.symm x = eBasis.symm y := Subsingleton.elim _ _
      exact eBasis.symm.injective this
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  have hcard_ne_zero : Fintype.card ι ≠ 0 := Nat.ne_of_gt (Fintype.card_pos_iff.mpr hι_nonempty)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard_ne_zero
  -- Choose finite coordinates for the free module and invoke the `Fin`-indexed computation.
  calc
    moduleDepth R P = moduleDepth R (ι → R) := by
      symm
      exact moduleDepth_eq_of_linearEquiv (R := R) (M := ι → R) (N := P) eBasis
    _ = moduleDepth R (Fin (Fintype.card ι) → R) := by
      symm
      exact moduleDepth_eq_of_linearEquiv (R := R)
        (M := Fin (Fintype.card ι) → R) (N := ι → R) eFin
    _ = d := by
      have hfin : moduleDepth R (Fin (Fintype.card ι) → R) = d := by
        rw [hn]
        exact moduleDepth_piFinSucc_eq_ringKrullDim (R := R) (d := d) n hCM hdim
      exact hfin

/-
Domain-style sampling:
* primary domain: module depth in short exact sequences over Noetherian local Cohen-Macaulay rings;
* sampled owner declarations:
  `moduleDepth`,
  `Module.CohenMacaulay`,
  `Module.Free`,
  `Module.Finite`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min`;
* best owner abstraction: the short exact complex `S` with `hS : S.ShortExact`; the finite free
  middle term is expressed intrinsically by `[Module.Free R S.X₂]` and
  `[Module.Finite R S.X₂]`;
* source/core/bridge triage:
  this theorem remains `source-facing`, because it records the special trichotomy for an exact
  sequence whose middle term is finite free over a Cohen-Macaulay local ring;
  the exact-sequence data itself is `core/canonical`, carried by `hS : S.ShortExact`;
  any coordinate identification of `S.X₂` with a finite product of copies of `R` is only the
  `bridge/view`, obtained internally from `Module.Free.chooseBasis R S.X₂`;
* primitive data: `hS`, the Cohen-Macaulay owner hypothesis `hCM : Module.CohenMacaulay R R`, the
  dimension equality `hdim`, and the intrinsic finite-free owner data on `S.X₂`;
* derived API: `S.X₃` is finite because it is a quotient of the finite middle term, and then `S.X₁`
  is finite by the canonical exact-sequence owner theorem `Module.Finite.of_exact_of_finitePresentation`;
  the depth comparisons belong to the existing owner lemmas from Lemma `10.72.6`, while any basis
  choice and transfer of depth across the resulting linear equivalence are proof-level derived data.
-/

-- Proof sketch: if `S.X₃ = 0`, this is the first alternative. Otherwise `S.X₂` is nonzero because
-- `hS.moduleCat_surjective_g` is onto. Choose a basis of the finite free module `S.X₂`, whose
-- finite index type is derived from `[Module.Finite R S.X₂]`, and use the induced linear
-- equivalence with a finite product of copies of `R` to identify `moduleDepth R S.X₂` with `d`
-- from `hCM` and `hdim`. Then apply the canonical short-exact depth inequalities from
-- Lemma `10.72.6` to compare `moduleDepth R S.X₁` and `moduleDepth R S.X₃`, obtaining either a
-- strict increase or equality at the top value `d`.
/-- Lemma 10.104.8: let `R` be a Noetherian local Cohen-Macaulay ring of dimension `d`, and let
`0 → K → P → M → 0` be a short exact sequence of `R`-modules with `P` finite free. In the
chapter's canonical owner language, this is a short exact complex `S` whose middle term `S.X₂`
carries `[Module.Free R S.X₂]` and `[Module.Finite R S.X₂]`; the endpoint finiteness needed for
`moduleDepth` is derived internally from `hS`. Then either `M = 0`, or `depth(K) > depth(M)`, or
`depth(K) = depth(M) = d`. -/
theorem moduleDepth_kernel_trichotomy_of_exact_free_over_cohenMacaulayLocalRing
    {d : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hS : S.ShortExact) [Module.Free R S.X₂] [Module.Finite R S.X₂] :
    letI : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom hS.moduleCat_surjective_g
    letI : Module.Finite R S.X₁ := by
      letI : Module.FinitePresentation R S.X₃ := Module.finitePresentation_of_finite R S.X₃
      exact Module.Finite.of_exact_of_finitePresentation S.f.hom S.g.hom
        hS.moduleCat_injective_f hS.moduleCat_surjective_g
        ((moduleCat_exact_iff_function_exact S).mp hS.exact)
    Subsingleton S.X₃ ∨ moduleDepth R S.X₁ > moduleDepth R S.X₃ ∨
      (moduleDepth R S.X₁ = d ∧ moduleDepth R S.X₃ = d) := by
  classical
  letI : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom hS.moduleCat_surjective_g
  letI : Module.Finite R S.X₁ := by
    letI : Module.FinitePresentation R S.X₃ := Module.finitePresentation_of_finite R S.X₃
    exact Module.Finite.of_exact_of_finitePresentation S.f.hom S.g.hom
      hS.moduleCat_injective_f hS.moduleCat_surjective_g
      ((moduleCat_exact_iff_function_exact S).mp hS.exact)
  by_cases hX₃ : Subsingleton S.X₃
  · -- If the quotient vanishes, the first alternative is exactly the claim.
    exact Or.inl hX₃
  letI : Nontrivial S.X₃ := not_subsingleton_iff_nontrivial.mp hX₃
  by_cases hX₁ : Subsingleton S.X₁
  · -- If the kernel vanishes while the quotient is nonzero, its depth is `⊤`, hence strictly
    -- larger than the finite quotient depth.
    have hdepth₁ : moduleDepth R S.X₁ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₁
    have hdepth₃_le : moduleDepth R S.X₃ ≤ d :=
      moduleDepth_le_ringKrullDim_of_nontrivial (R := R) (M := S.X₃) hdim
    right
    left
    rw [hdepth₁]
    exact lt_top_iff_ne_top.mpr <|
      ne_top_of_le_ne_top (show (d : ℕ∞) ≠ ⊤ by simp) hdepth₃_le
  letI : Nontrivial S.X₁ := not_subsingleton_iff_nontrivial.mp hX₁
  letI : Nontrivial S.X₂ := Function.Surjective.nontrivial hS.moduleCat_surjective_g
  -- Compute the finite free middle term's depth from the Cohen-Macaulay hypothesis on `R`.
  have hdepth₂ : moduleDepth R S.X₂ = d :=
    moduleDepth_eq_ringKrullDim_of_nontrivial_finite_free (R := R) (P := S.X₂) hCM hdim
  -- The left-hand depth lemma is the promised special case of Lemma `10.72.6`.
  have hleft : min (d : ℕ∞) (moduleDepth R S.X₃ + 1) ≤ moduleDepth R S.X₁ := by
    have hleft' := moduleDepth_left_ge_min (R := R) (S := S) hS
    simpa [hdepth₂] using hleft'
  -- Both nonzero endpoint depths are finite and bounded by the ambient dimension.
  have hdepth₁_le : moduleDepth R S.X₁ ≤ d :=
    moduleDepth_le_ringKrullDim_of_nontrivial (R := R) (M := S.X₁) hdim
  have hdepth₃_le : moduleDepth R S.X₃ ≤ d :=
    moduleDepth_le_ringKrullDim_of_nontrivial (R := R) (M := S.X₃) hdim
  have hdepth₁_ne_top : moduleDepth R S.X₁ ≠ ⊤ :=
    ne_top_of_le_ne_top (show (d : ℕ∞) ≠ ⊤ by simp) hdepth₁_le
  have hdepth₃_ne_top : moduleDepth R S.X₃ ≠ ⊤ :=
    ne_top_of_le_ne_top (show (d : ℕ∞) ≠ ⊤ by simp) hdepth₃_le
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hdepth₁_ne_top
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hdepth₃_ne_top
  have hmin_nat : min d (b + 1) ≤ a := by
    exact WithTop.coe_le_coe.mp (by simpa [ha, hb] using hleft)
  have ha_le : a ≤ d := by
    exact WithTop.coe_le_coe.mp (by simpa [ha] using hdepth₁_le)
  have hb_le : b ≤ d := by
    exact WithTop.coe_le_coe.mp (by simpa [hb] using hdepth₃_le)
  -- The remaining trichotomy is pure arithmetic on the finite depth values.
  rcases strict_gt_or_both_eq_dim_of_ge_min_succ_nat hmin_nat ha_le hb_le with hgt | ⟨ha_eq, hb_eq⟩
  · right
    left
    change moduleDepth R S.X₃ < moduleDepth R S.X₁
    rw [← hb, ← ha]
    exact WithTop.coe_lt_coe.mpr hgt
  · right
    right
    refine ⟨?_, ?_⟩
    · calc
        moduleDepth R S.X₁ = (a : ℕ∞) := ha.symm
        _ = d := by exact_mod_cast ha_eq
    · calc
        moduleDepth R S.X₃ = (b : ℕ∞) := hb.symm
        _ = d := by exact_mod_cast hb_eq

end

end ShortExact
end ShortComplex
end CategoryTheory
