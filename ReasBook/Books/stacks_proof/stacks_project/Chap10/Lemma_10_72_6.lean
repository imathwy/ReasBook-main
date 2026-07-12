import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap10.Lemma_10_71_6
import StacksProject_2024.Chap10.Lemma_10_72_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₃]

/-- In a short exact sequence of finite modules, the middle term is finite. -/
instance finite_X₂ (hS : S.ShortExact) : Module.Finite R S.X₂ :=
  Module.Finite.of_exact
    ((moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₃]

open CategoryTheory.Abelian.Ext
open IsLocalRing
open scoped ENat

/- Domain-style sampling:
* primary domain: local commutative algebra of module depth in short exact sequences of finite
  modules, with the proof route passing through the canonical covariant long exact `Ext` sequence;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `Module.Finite.of_exact`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.Abelian.Ext.covariantSequence_exact`;
* best owner abstraction: `moduleDepth` is the chapter owner surface for local depth, while
  `S : ShortComplex (ModuleCat R)` with `hS : S.ShortExact` is the canonical owner for the short
  exact sequence data;
* source/core/bridge triage: this file is `source-facing`. No upstream theorem already packages
  the depth-lemma inequalities themselves, so the refinement should keep these three inequalities
  as the public owner statements rather than introducing a parallel wrapper or a fake recall;
* primitive vs derived split: the primitive data are just the short exact sequence `S` and the
  chapter owner `moduleDepth` on its three terms. The comparisons below are derived theorems from
  Lemma `10.72.5` and the recalled long exact `Ext` owner of Lemma `10.71.6`, so no extra public
  data/package structure belongs here. In particular, finite generation of `S.X₂` is itself a
  derived owner instance `hS.finite_X₂`, while any zero-endpoint case splits needed to use
  Lemma `10.72.5`
  belong in the proof rather than in the public theorem hypotheses.
-/

/-- Helper for Lemma 10.72.6: a linear equivalence preserves the set of regular-sequence lengths
with entries in a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {M N : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- Transport each regular sequence across the equivalence and then reverse the argument.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.72.6: depth is invariant under a linear equivalence of finite modules. -/
private theorem idealDepth_eq_of_linearEquiv {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- The `IM = M` branch is preserved by the equivalence, and otherwise the same regular-sequence
  -- lengths compute the depth on both sides.
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

/-- Helper for Lemma 10.72.6: isomorphic finite `R`-modules have the same depth. -/
private theorem moduleDepth_eq_of_moduleIso {M N : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Finite R N] (e : M ≅ N) :
    moduleDepth R M = moduleDepth R N := by
  -- Forget the module isomorphism to a linear equivalence and reuse depth invariance.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv (R := R) (M := M) (N := N) (maximalIdeal R) e.toLinearEquiv

/-- Helper for Lemma 10.72.6: a finite subsingleton module has infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton (M : ModuleCat.{u} R) [Module.Finite R M]
    [Subsingleton M] :
    moduleDepth R M = ⊤ := by
  -- For a zero module, `𝔪 • M = M`, so the depth definition lands in the `⊤` branch.
  have htopbot : (⊤ : Submodule R M) = ⊥ := by
    ext x
    simp [Subsingleton.elim x 0]
  have hsmul_bot : maximalIdeal R • (⊥ : Submodule R M) = ⊥ := by
    ext x
    simp
  have hsmul : maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    rw [htopbot, hsmul_bot]
  change Ideal.depth (maximalIdeal R) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M hsmul

section ExtTransport

variable [Module.Finite R S.X₂]
variable [Nontrivial S.X₁] [Nontrivial S.X₂] [Nontrivial S.X₃]

/-- Helper for Lemma 10.72.6: if the residue-field `Ext^n` groups of the two endpoints vanish,
then the middle `Ext^n` group also vanishes. -/
private lemma residueFieldExt_vanish_middle_of_end_vanish (hS : S.ShortExact) {n : ℕ}
    (hleft : ¬ residueFieldExtNonzero R S.X₁ n)
    (hright : ¬ residueFieldExtNonzero R S.X₃ n) :
    ¬ residueFieldExtNonzero R S.X₂ n := by
  rintro ⟨e, he⟩
  by_cases hg : e.comp (mk₀ S.g) (add_zero n) = 0
  · -- Exactness at `Ext^n(k, S.X₂)` then lifts `e` to the left endpoint.
    obtain ⟨e₁, he₁⟩ := covariant_sequence_exact₂ (ModuleCat.of R (ResidueField R)) hS e hg
    have he₁_ne : e₁ ≠ 0 := by
      intro he₁_zero
      apply he
      calc
        e = e₁.comp (mk₀ S.f) (add_zero n) := he₁.symm
        _ = 0 := by simp [he₁_zero]
    exact hleft ⟨e₁, he₁_ne⟩
  · -- Otherwise the image of `e` in the right endpoint is already a nonzero class.
    exact hright ⟨e.comp (mk₀ S.g) (add_zero n), hg⟩

/-- Helper for Lemma 10.72.6: vanishing in the middle degree and in the next left degree forces
vanishing on the right. -/
private lemma residueFieldExt_vanish_right_of_middle_vanish_of_left_succ_vanish (hS : S.ShortExact)
    {n : ℕ} (hmiddle : ¬ residueFieldExtNonzero R S.X₂ n)
    (hleft_succ : ¬ residueFieldExtNonzero R S.X₁ (n + 1)) :
    ¬ residueFieldExtNonzero R S.X₃ n := by
  rintro ⟨e, he⟩
  by_cases hδ : e.comp hS.extClass rfl = 0
  · -- Exactness at `Ext^n(k, S.X₃)` lifts a zero boundary class back to the middle term.
    obtain ⟨e₂, he₂⟩ :=
      covariant_sequence_exact₃ (ModuleCat.of R (ResidueField R)) hS e rfl hδ
    have he₂_ne : e₂ ≠ 0 := by
      intro he₂_zero
      apply he
      calc
        e = e₂.comp (mk₀ S.g) (add_zero n) := he₂.symm
        _ = 0 := by simp [he₂_zero]
    exact hmiddle ⟨e₂, he₂_ne⟩
  · -- A nonzero boundary produces the forbidden left-side class in degree `n + 1`.
    exact hleft_succ ⟨e.comp hS.extClass rfl, hδ⟩

/-- Helper for Lemma 10.72.6: at degree `0`, vanishing in the middle forces vanishing on the
left because `Hom(k, -)` preserves monomorphisms. -/
private lemma residueFieldExt_vanish_left_zero_of_middle_vanish (hS : S.ShortExact)
    (hmiddle : ¬ residueFieldExtNonzero R S.X₂ 0) :
    ¬ residueFieldExtNonzero R S.X₁ 0 := by
  let _ : Mono S.f := hS.mono_f
  rintro ⟨e, he⟩
  have himage_ne : e.comp (mk₀ S.f) (add_zero 0) ≠ 0 := by
    intro hzero
    apply he
    have himage_eq :
        ((mk₀ S.f).postcomp (ModuleCat.of R (ResidueField R)) (add_zero 0)) e =
          ((mk₀ S.f).postcomp (ModuleCat.of R (ResidueField R)) (add_zero 0)) 0 := by
      simpa using hzero
    exact (postcomp_mk₀_injective_of_mono (ModuleCat.of R (ResidueField R)) S.f) himage_eq
  -- Injectivity of the degree-zero map sends a nonzero left class to a nonzero middle class.
  exact hmiddle ⟨e.comp (mk₀ S.f) (add_zero 0), himage_ne⟩

/-- Helper for Lemma 10.72.6: vanishing in the middle degree `n + 1` and on the right in degree
`n` forces vanishing on the left in degree `n + 1`. -/
private lemma residueFieldExt_vanish_left_succ_of_middle_vanish_of_right_vanish (hS : S.ShortExact)
    {n : ℕ} (hmiddle_succ : ¬ residueFieldExtNonzero R S.X₂ (n + 1))
    (hright : ¬ residueFieldExtNonzero R S.X₃ n) :
    ¬ residueFieldExtNonzero R S.X₁ (n + 1) := by
  rintro ⟨e, he⟩
  by_cases hf : e.comp (mk₀ S.f) (add_zero (n + 1)) = 0
  · -- Exactness at `Ext^(n+1)(k, S.X₁)` lifts a zero image to a right-side class.
    obtain ⟨e₃, he₃⟩ :=
      covariant_sequence_exact₁ (ModuleCat.of R (ResidueField R)) hS e hf (n₀ := n) rfl
    have he₃_ne : e₃ ≠ 0 := by
      intro he₃_zero
      apply he
      calc
        e = e₃.comp hS.extClass rfl := he₃.symm
        _ = 0 := by simp [he₃_zero]
    exact hright ⟨e₃, he₃_ne⟩
  · -- Otherwise the image of `e` in the middle term is already a forbidden nonzero class.
    exact hmiddle_succ ⟨e.comp (mk₀ S.f) (add_zero (n + 1)), hf⟩

end ExtTransport

-- Proof sketch: first dispose of the degenerate cases where `S.X₁ = 0` or `S.X₃ = 0`, in which
-- the short exact sequence identifies `S.X₂` with one endpoint and the inequality is immediate.
-- In the nonzero case, identify each depth with the least degree of a nonvanishing residue-field
-- `Ext` group using Lemma `10.72.5`, apply the covariant long exact `Ext` sequence from
-- Lemma `10.71.6` to the short exact sequence `S`, and compare the first nonvanishing degrees.
/-- Lemma 10.72.6 (1): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the middle module is at least the minimum of the depths of the two end modules. -/
@[stacks 00LX]
theorem moduleDepth_middle_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₂ ≥ min (moduleDepth R S.X₁) (moduleDepth R S.X₃) := by
  letI : Module.Finite R S.X₂ := hS.finite_X₂
  by_cases hX₁ : Subsingleton S.X₁
  · -- If the left term vanishes, short exactness identifies the middle term with the right term.
    let _ : IsIso S.g := (ShortExact.isIso_g_iff hS).2 (ModuleCat.isZero_of_subsingleton S.X₁)
    have hdepth₁ : moduleDepth R S.X₁ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₁
    have hdepth₂₃ : moduleDepth R S.X₂ = moduleDepth R S.X₃ :=
      moduleDepth_eq_of_moduleIso (R := R) (asIso S.g)
    simpa [hdepth₁, hdepth₂₃]
  by_cases hX₃ : Subsingleton S.X₃
  · -- If the right term vanishes, short exactness identifies the middle term with the left term.
    let _ : IsIso S.f := (ShortExact.isIso_f_iff hS).2 (ModuleCat.isZero_of_subsingleton S.X₃)
    have hdepth₃ : moduleDepth R S.X₃ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₃
    have hdepth₁₂ : moduleDepth R S.X₁ = moduleDepth R S.X₂ :=
      moduleDepth_eq_of_moduleIso (R := R) (asIso S.f)
    simpa [hdepth₃, hdepth₁₂]
  -- In the nondegenerate case, compare the first nonvanishing residue-field `Ext` degrees.
  letI : Nontrivial S.X₁ := not_subsingleton_iff_nontrivial.mp hX₁
  letI : Nontrivial S.X₃ := not_subsingleton_iff_nontrivial.mp hX₃
  letI : Nontrivial S.X₂ := Function.Injective.nontrivial hS.moduleCat_injective_f
  let i₁ := firstNonzeroResidueFieldExtIndex R S.X₁
  let i₂ := firstNonzeroResidueFieldExtIndex R S.X₂
  let i₃ := firstNonzeroResidueFieldExtIndex R S.X₃
  have hdepth₁ : moduleDepth R S.X₁ = (i₁ : WithTop ℕ) := by
    simpa [i₁] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₁)
  have hdepth₂ : moduleDepth R S.X₂ = (i₂ : WithTop ℕ) := by
    simpa [i₂] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₂)
  have hdepth₃ : moduleDepth R S.X₃ = (i₃ : WithTop ℕ) := by
    simpa [i₃] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₃)
  have hprofile₁ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₁) (n := i₁) hdepth₁
  have hprofile₂ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₂) (n := i₂) hdepth₂
  have hprofile₃ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₃) (n := i₃) hdepth₃
  have hnat : min i₁ i₃ ≤ i₂ := by
    by_contra hlt
    have hi₂_lt_min : i₂ < min i₁ i₃ := lt_of_not_ge hlt
    have hi₂_lt_i₁ : i₂ < i₁ := lt_of_lt_of_le hi₂_lt_min (Nat.min_le_left _ _)
    have hi₂_lt_i₃ : i₂ < i₃ := lt_of_lt_of_le hi₂_lt_min (Nat.min_le_right _ _)
    have hvanish₂ :
        ¬ residueFieldExtNonzero R S.X₂ i₂ :=
      residueFieldExt_vanish_middle_of_end_vanish (R := R) (S := S) hS
        (hprofile₁.2 i₂ hi₂_lt_i₁)
        (hprofile₃.2 i₂ hi₂_lt_i₃)
    exact hvanish₂ hprofile₂.1
  -- The index comparison is exactly the desired depth inequality after rewriting.
  rw [hdepth₁, hdepth₂, hdepth₃]
  have hcastcases : ((i₁ : WithTop ℕ) ≤ (i₂ : WithTop ℕ)) ∨
      ((i₃ : WithTop ℕ) ≤ (i₂ : WithTop ℕ)) := by
    rcases min_le_iff.mp hnat with hi₁_le_i₂ | hi₃_le_i₂
    · left
      exact_mod_cast hi₁_le_i₂
    · right
      exact_mod_cast hi₃_le_i₂
  change min (i₁ : WithTop ℕ) (i₃ : WithTop ℕ) ≤ (i₂ : WithTop ℕ)
  rw [min_le_iff]
  exact hcastcases

-- Proof sketch: as above, handle the zero-endpoint cases internally using the isomorphisms forced
-- by short exactness. Otherwise use Lemma `10.72.5` to rewrite depths as first nonvanishing
-- residue-field `Ext` degrees, then analyze the long exact `Ext` sequence of Lemma `10.71.6` for
-- `S` to show that the first nonvanishing degree of `S.X₃` is bounded below by the minimum of the
-- corresponding degrees for `S.X₂` and `S.X₁ - 1`.
/-- Lemma 10.72.6 (2): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the quotient module is at least the minimum of the depth of the middle module and one
less than the depth of the submodule. -/
@[stacks 00LX]
theorem moduleDepth_right_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₃ ≥ min (moduleDepth R S.X₂) (moduleDepth R S.X₁ - 1) := by
  letI : Module.Finite R S.X₂ := hS.finite_X₂
  by_cases hX₁ : Subsingleton S.X₁
  · -- If the left term vanishes, `g` is an isomorphism and the estimate becomes equality.
    let _ : IsIso S.g := (ShortExact.isIso_g_iff hS).2 (ModuleCat.isZero_of_subsingleton S.X₁)
    have hdepth₁ : moduleDepth R S.X₁ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₁
    have hdepth₂₃ : moduleDepth R S.X₂ = moduleDepth R S.X₃ :=
      moduleDepth_eq_of_moduleIso (R := R) (asIso S.g)
    simpa [hdepth₁, hdepth₂₃]
  by_cases hX₃ : Subsingleton S.X₃
  · -- If the quotient vanishes, its depth is `⊤`, so the inequality is automatic.
    have hdepth₃ : moduleDepth R S.X₃ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₃
    simpa [hdepth₃]
  -- In the nondegenerate case, use exactness to compare the first nonvanishing `Ext` indices.
  letI : Nontrivial S.X₁ := not_subsingleton_iff_nontrivial.mp hX₁
  letI : Nontrivial S.X₃ := not_subsingleton_iff_nontrivial.mp hX₃
  letI : Nontrivial S.X₂ := Function.Injective.nontrivial hS.moduleCat_injective_f
  let i₁ := firstNonzeroResidueFieldExtIndex R S.X₁
  let i₂ := firstNonzeroResidueFieldExtIndex R S.X₂
  let i₃ := firstNonzeroResidueFieldExtIndex R S.X₃
  have hdepth₁ : moduleDepth R S.X₁ = (i₁ : WithTop ℕ) := by
    simpa [i₁] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₁)
  have hdepth₂ : moduleDepth R S.X₂ = (i₂ : WithTop ℕ) := by
    simpa [i₂] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₂)
  have hdepth₃ : moduleDepth R S.X₃ = (i₃ : WithTop ℕ) := by
    simpa [i₃] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₃)
  have hprofile₁ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₁) (n := i₁) hdepth₁
  have hprofile₂ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₂) (n := i₂) hdepth₂
  have hprofile₃ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₃) (n := i₃) hdepth₃
  have hcases_nat : i₂ ≤ i₃ ∨ i₁ ≤ i₃ + 1 := by
    by_contra hnot
    have hi₃_lt_i₂ : i₃ < i₂ := lt_of_not_ge (not_or.mp hnot).1
    have hi₃_succ_lt_i₁ : i₃ + 1 < i₁ := lt_of_not_ge (not_or.mp hnot).2
    have hvanish₃ :
        ¬ residueFieldExtNonzero R S.X₃ i₃ :=
      residueFieldExt_vanish_right_of_middle_vanish_of_left_succ_vanish
        (R := R) (S := S) hS
        (hprofile₂.2 i₃ hi₃_lt_i₂)
        (hprofile₁.2 (i₃ + 1) hi₃_succ_lt_i₁)
    exact hvanish₃ hprofile₃.1
  -- Once the depths are rewritten to indices, the proved nat inequality is the claim.
  rw [hdepth₁, hdepth₂, hdepth₃]
  have hcastcases : ((i₂ : WithTop ℕ) ≤ (i₃ : WithTop ℕ)) ∨
      ((i₁ : WithTop ℕ) ≤ (i₃ : WithTop ℕ) + 1) := by
    rcases hcases_nat with hi₂_le_i₃ | hi₁_le_i₃_succ
    · left
      exact_mod_cast hi₂_le_i₃
    · right
      exact_mod_cast hi₁_le_i₃_succ
  change min (i₂ : WithTop ℕ) ((i₁ : WithTop ℕ) - 1) ≤ (i₃ : WithTop ℕ)
  rw [min_le_iff]
  have hcastcases' : ((i₂ : WithTop ℕ) ≤ (i₃ : WithTop ℕ)) ∨
      (((i₁ : WithTop ℕ) - 1) ≤ (i₃ : WithTop ℕ)) := by
    rcases hcastcases with hi₂_le_i₃ | hi₁_le_i₃_succ
    · exact Or.inl hi₂_le_i₃
    · exact Or.inr <| (tsub_le_iff_right).2 hi₁_le_i₃_succ
  exact hcastcases'

-- Proof sketch: rewrite the three depths via Lemma `10.72.5` after the same internal zero-case
-- reductions, apply the long exact covariant `Ext` sequence from Lemma `10.71.6`, and compare the
-- first nonvanishing degrees to bound the depth of `S.X₁` below by the minimum of the depth of
-- `S.X₂` and the shifted depth of `S.X₃`.
/-- Lemma 10.72.6 (3): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the submodule is at least the minimum of the depth of the middle module and one more
than the depth of the quotient module. -/
@[stacks 00LX]
theorem moduleDepth_left_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₁ ≥ min (moduleDepth R S.X₂) (moduleDepth R S.X₃ + 1) := by
  letI : Module.Finite R S.X₂ := hS.finite_X₂
  by_cases hX₁ : Subsingleton S.X₁
  · -- If the submodule vanishes, its depth is `⊤`, so the inequality is automatic.
    have hdepth₁ : moduleDepth R S.X₁ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₁
    simpa [hdepth₁]
  by_cases hX₃ : Subsingleton S.X₃
  · -- If the quotient vanishes, `f` is an isomorphism and the inequality becomes equality.
    let _ : IsIso S.f := (ShortExact.isIso_f_iff hS).2 (ModuleCat.isZero_of_subsingleton S.X₃)
    have hdepth₃ : moduleDepth R S.X₃ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₃
    have hdepth₁₂ : moduleDepth R S.X₁ = moduleDepth R S.X₂ :=
      moduleDepth_eq_of_moduleIso (R := R) (asIso S.f)
    simpa [hdepth₃, hdepth₁₂]
  -- In the nondegenerate case, exactness bounds the first nonzero left index from below.
  letI : Nontrivial S.X₁ := not_subsingleton_iff_nontrivial.mp hX₁
  letI : Nontrivial S.X₃ := not_subsingleton_iff_nontrivial.mp hX₃
  letI : Nontrivial S.X₂ := Function.Injective.nontrivial hS.moduleCat_injective_f
  let i₁ := firstNonzeroResidueFieldExtIndex R S.X₁
  let i₂ := firstNonzeroResidueFieldExtIndex R S.X₂
  let i₃ := firstNonzeroResidueFieldExtIndex R S.X₃
  have hdepth₁ : moduleDepth R S.X₁ = (i₁ : WithTop ℕ) := by
    simpa [i₁] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₁)
  have hdepth₂ : moduleDepth R S.X₂ = (i₂ : WithTop ℕ) := by
    simpa [i₂] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₂)
  have hdepth₃ : moduleDepth R S.X₃ = (i₃ : WithTop ℕ) := by
    simpa [i₃] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₃)
  have hprofile₁ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₁) (n := i₁) hdepth₁
  have hprofile₂ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₂) (n := i₂) hdepth₂
  have hprofile₃ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₃) (n := i₃) hdepth₃
  have hcases_nat : i₂ ≤ i₁ ∨ i₃ + 1 ≤ i₁ := by
    by_contra hnot
    have hi₁_lt_i₂ : i₁ < i₂ := lt_of_not_ge (not_or.mp hnot).1
    have hi₁_lt_i₃_succ : i₁ < i₃ + 1 := lt_of_not_ge (not_or.mp hnot).2
    by_cases hi₁_zero : i₁ = 0
    · have hzero_lt_i₂ : 0 < i₂ := by
        simpa [hi₁_zero] using hi₁_lt_i₂
      have hvanish₁ :
          ¬ residueFieldExtNonzero R S.X₁ 0 :=
        residueFieldExt_vanish_left_zero_of_middle_vanish (R := R) (S := S) hS
          (hprofile₂.2 0 hzero_lt_i₂)
      have hnonzero₁ : residueFieldExtNonzero R S.X₁ 0 := by
        simpa [hi₁_zero] using hprofile₁.1
      exact hvanish₁ hnonzero₁
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hi₁_zero
      have hn_succ_lt_i₂ : n + 1 < i₂ := by
        simpa [hn] using hi₁_lt_i₂
      have hn_succ_lt_i₃_succ : n + 1 < i₃ + 1 := by
        simpa [hn] using hi₁_lt_i₃_succ
      have hn_lt_i₃ : n < i₃ := Nat.lt_of_succ_lt_succ hn_succ_lt_i₃_succ
      have hvanish₁ :
          ¬ residueFieldExtNonzero R S.X₁ (n + 1) :=
        residueFieldExt_vanish_left_succ_of_middle_vanish_of_right_vanish
          (R := R) (S := S) hS
          (hprofile₂.2 (n + 1) hn_succ_lt_i₂)
          (hprofile₃.2 n hn_lt_i₃)
      have hnonzero₁ : residueFieldExtNonzero R S.X₁ (n + 1) := by
        simpa [hn] using hprofile₁.1
      exact hvanish₁ hnonzero₁
  -- Rewriting the depths reduces the claim to the natural-number inequality above.
  rw [hdepth₁, hdepth₂, hdepth₃]
  have hcastcases : ((i₂ : WithTop ℕ) ≤ (i₁ : WithTop ℕ)) ∨
      ((i₃ : WithTop ℕ) + 1 ≤ (i₁ : WithTop ℕ)) := by
    rcases hcases_nat with hi₂_le_i₁ | hi₃_succ_le_i₁
    · left
      exact_mod_cast hi₂_le_i₁
    · right
      exact_mod_cast hi₃_succ_le_i₁
  change min (i₂ : WithTop ℕ) ((i₃ : WithTop ℕ) + 1) ≤ (i₁ : WithTop ℕ)
  rw [min_le_iff]
  exact hcastcases

end

end ShortExact
end ShortComplex
end CategoryTheory
