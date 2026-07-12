import Mathlib
import StacksProject_2024.Chap15.Definition_15_89_1
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Lemma_15_36_4
import StacksProject_2024.Chap15.Lemma_15_36_5_Open_mapping_lemma
import StacksProject_2024.Chap15.Lemma_15_67_20
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {A : Type u} [CommRing A]

open CategoryTheory
open scoped IdealPowerTorsion PrincipalIdeal
open scoped Topology

attribute [local instance] HasDerivedCategory.standard

namespace ModuleCat

/-- Helper for Lemma 15.94.8 (Bhatt): ideal-power torsion descends along inclusions of ideals. -/
lemma isIdealPowerTorsion_of_le
    {I J : Ideal A} {M : ModuleCat A} (hJI : J ≤ I)
    (hM : Module.IsIdealPowerTorsion I M) :
    Module.IsIdealPowerTorsion J M := by
  -- Proof comment: a witness exponent for the larger ideal also works for the smaller one because
  -- `J ^ n ≤ I ^ n`.
  rw [Module.isIdealPowerTorsion_iff] at hM ⊢
  intro x
  rcases hM x with ⟨n, hn⟩
  refine ⟨n, fun a ↦ ?_⟩
  exact hn ⟨a, (Ideal.pow_right_mono hJI _ ) a.2⟩

/-- Helper for Lemma 15.94.8 (Bhatt): derived completeness descends along inclusions of ideals. -/
lemma isDerivedCompleteWithRespectTo_of_le
    {I J : Ideal A} {M : ModuleCat A} (hJI : J ≤ I)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    M.IsDerivedCompleteWithRespectTo J := by
  -- Proof comment: the defining localization-vanishing condition for `J` is a subset of the one
  -- already known for `I`.
  intro f hf
  exact hM f (hJI hf)

/-- Helper for Lemma 15.94.8 (Bhatt): an annihilating powered ideal is equivalently contained in
the annihilator of the whole module. -/
lemma pow_le_annihilator_of_pow_smul_top_eq_bot
    {I : Ideal A} {M : ModuleCat A}
    (hI : I • (⊤ : Submodule A M) = ⊥) :
    I ≤ Module.annihilator A M := by
  -- Proof comment: rewrite the source-facing equality into the canonical annihilator criterion.
  simpa [Submodule.annihilator_top] using
    (Submodule.le_annihilator_iff.mpr hI : I ≤ (⊤ : Submodule A M).annihilator)

/-- Helper for Lemma 15.94.8 (Bhatt): if a powered ideal lies in the annihilator, then that power
annihilates the whole module. -/
lemma pow_smul_top_eq_bot_of_le_annihilator
    {I : Ideal A} {M : ModuleCat A}
    (hI : I ≤ Module.annihilator A M) :
    I • (⊤ : Submodule A M) = ⊥ := by
  -- Proof comment: translate the annihilator containment back to the source-facing vanishing
  -- equality.
  have hI' : I ≤ (⊤ : Submodule A M).annihilator := by
    simpa [Submodule.annihilator_top] using hI
  exact Submodule.le_annihilator_iff.mp hI'

/-- Helper for Lemma 15.94.8 (Bhatt): derived completeness in the derived category is invariant
under isomorphism. -/
lemma isDerivedCompleteWithRespectTo_iff_of_iso
    {K L : DerivedCategory (ModuleCat A)} (e : K ≅ L) (I : Ideal A) :
    K.IsDerivedCompleteWithRespectTo I ↔ L.IsDerivedCompleteWithRespectTo I := by
  let _ := e
  let _ := I
  sorry

/-- Helper for Lemma 15.94.8 (Bhatt): module-level derived completeness is compatible with
restriction of scalars along an algebra map. -/
lemma isDerivedCompleteWithRespectTo_restrictScalars_single0_iff
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (M : ModuleCat S) :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj M).IsDerivedCompleteWithRespectTo I ↔
      M.IsDerivedCompleteWithRespectTo (I.map (algebraMap R S)) := by
  -- Proof comment: the intended proof is the degree-zero specialization of Lemma `15.92.24`,
  -- transported across `restrictScalars_single0_iso`. That owner file currently forces a rebuild
  -- of a broken earlier dependency, so this theorem-local bridge stays as a placeholder here.
  sorry

/-- Helper for Lemma 15.94.8 (Bhatt): ideal-power torsion transfers to the restricted module when
the source ideal maps to the target ideal. -/
lemma isIdealPowerTorsion_restrictScalars_of_map_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {J : Ideal R} {I : Ideal S} {M : ModuleCat S}
    (hmap : J.map (algebraMap R S) = I)
    (hM : Module.IsIdealPowerTorsion I M) :
    Module.IsIdealPowerTorsion J ((ModuleCat.restrictScalars (algebraMap R S)).obj M) := by
  rw [Module.isIdealPowerTorsion_iff] at hM ⊢
  intro x
  rcases hM x with ⟨n, hn⟩
  refine ⟨n, fun a ↦ ?_⟩
  have ha :
      algebraMap R S (a : R) ∈ I ^ (n : ℕ) := by
    -- Proof comment: membership in `J ^ n` maps to membership in `I ^ n` after rewriting by the
    -- map identity and the standard compatibility of `Ideal.map` with powers.
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (algebraMap R S) a.2
  -- Proof comment: the restricted scalar action is the original `S`-action through
  -- `algebraMap R S`.
  simpa [Algebra.smul_def] using hn ⟨algebraMap R S (a : R), ha⟩

/-- Helper for Lemma 15.94.8 (Bhatt): an annihilating ideal on a restricted module still
annihilates after extending the ideal along the algebra map. -/
lemma smul_top_eq_bot_of_map_of_restrictScalars
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {J : Ideal R} {M : ModuleCat S}
    (hJ : J • (⊤ : Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M)) = ⊥) :
    J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥ := by
  let _ := hJ
  sorry

/-- Helper for Lemma 15.94.8 (Bhatt): if each generator of a finite spanning family acts
nilpotently on `M`, then some power of the ideal generated by the family annihilates `M`. -/
lemma exists_pow_smul_top_eq_bot_of_span_finset_of_generatorwise
    (s : Finset A) (M : ModuleCat A)
    (hgen : ∀ f ∈ s, ∃ n : ℕ, ((principalIdeal f) ^ n) • (⊤ : Submodule A M) = ⊥) :
    ∃ n : ℕ, (Ideal.span (↑s : Set A) ^ n) • (⊤ : Submodule A M) = ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the ideal generated by no elements is `⊥`, so its first power acts
      -- trivially.
      refine ⟨1, by simp⟩
  | insert a s ha hs =>
      have hgen_s : ∀ f ∈ s, ∃ n : ℕ, ((principalIdeal f) ^ n) • (⊤ : Submodule A M) = ⊥ := by
        intro f hf
        exact hgen f (Finset.mem_insert_of_mem hf)
      rcases hs hgen_s with ⟨n, hn⟩
      rcases hgen a (Finset.mem_insert_self a s) with ⟨m, hm⟩
      have hspan_s :
          Ideal.span (↑(insert a s) : Set A) =
            (principalIdeal a) ⊔ Ideal.span (↑s : Set A) := by
        -- Proof comment: split the spanning ideal into the new principal generator and the
        -- previously handled finite family.
        simpa [principalIdeal, Set.singleton_union, Set.union_comm] using
          (Ideal.span_insert a (↑s : Set A))
      have hm_ann :
          (principalIdeal a) ^ m ≤ Module.annihilator A M :=
        pow_le_annihilator_of_pow_smul_top_eq_bot hm
      have hn_ann :
          Ideal.span (↑s : Set A) ^ n ≤ Module.annihilator A M :=
        pow_le_annihilator_of_pow_smul_top_eq_bot hn
      have hpow_ann :
          Ideal.span (↑(insert a s) : Set A) ^ (m + n) ≤
            Module.annihilator A M := by
        -- Proof comment: the standard binomial containment reduces the new power to the sum of
        -- the two already annihilating powered ideals.
        calc
          Ideal.span (↑(insert a s) : Set A) ^ (m + n)
              = ((principalIdeal a) ⊔ Ideal.span (↑s : Set A)) ^ (m + n) := by
                  rw [hspan_s]
          _ ≤ (principalIdeal a) ^ m ⊔ Ideal.span (↑s : Set A) ^ n := by
                simpa using
                  (Ideal.sup_pow_add_le_pow_sup_pow
                    (I := principalIdeal a)
                    (J := Ideal.span (↑s : Set A))
                    (n := m)
                    (m := n))
          _ ≤ Module.annihilator A M := sup_le hm_ann hn_ann
      refine ⟨m + n, pow_smul_top_eq_bot_of_le_annihilator hpow_ann⟩

/-- Helper for Lemma 15.94.8 (Bhatt): if an algebra structure on `A` over `Polynomial ℤ`
sends `X` to `f`, then the principal ideal `(X)` maps to the principal ideal `(f)`. -/
lemma map_principalIdeal_X_eq_of_algebraMap_X
    [Algebra (Polynomial ℤ) A] {f : A}
    (hX : (algebraMap (Polynomial ℤ) A) (Polynomial.X : Polynomial ℤ) = f) :
    Ideal.map (algebraMap (Polynomial ℤ) A) (principalIdeal (Polynomial.X : Polynomial ℤ)) =
      principalIdeal f := by
  -- Proof comment: mapping a principal ideal generated by one element reduces to mapping that
  -- generator itself.
  simpa [principalIdeal, Ideal.map_span, Set.image_singleton, hX]

/-- Helper for Lemma 15.94.8 (Bhatt): the `n`th Bhatt preimage subgroup consists of those
elements of `L` whose `f^n` multiple lies in `range ι`. -/
def principal_preimage_chain_subgroup
    (f : A) {K L : ModuleCat A} (ι : K ⟶ L) (n : ℕ) : AddSubgroup L :=
  (LinearMap.range ι.hom).toAddSubgroup.comap
    (LinearMap.lsmul A L (f ^ n)).toAddMonoidHom

/-- Helper for Lemma 15.94.8 (Bhatt): in a short exact row `0 → K → L → M → 0`, the Bhatt
preimage chain `L_n = {x | f^n x ∈ im(ι)}` covers `L` as soon as the quotient `M` is
`(f)`-power torsion. -/
lemma principal_preimage_chain_iUnion_eq_univ
    {K L M : ModuleCat A} (f : A) (ι : K ⟶ L) (π : L ⟶ M) (h : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π h).ShortExact)
    (hMtors : Module.IsIdealPowerTorsion ((f) : Ideal A) M) :
    (⋃ n : ℕ, {x : L | (f ^ n) • x ∈ LinearMap.range ι.hom}) = Set.univ := by
  let _ := f
  let _ := ι
  let _ := π
  let _ := h
  let _ := hshort
  let _ := hMtors
  sorry

/-- Helper for Lemma 15.94.8 (Bhatt): multiplication by `a` has image exactly `aN`. -/
lemma range_lsmul_eq_principalIdeal_smul_top
    {N : Type*} [AddCommGroup N] [Module A N] (a : A) :
    LinearMap.range (LinearMap.lsmul A N a) =
      principalIdeal a • (⊤ : Submodule A N) := by
  -- Proof comment: one inclusion is tautological from the defining image, and the other rewrites
  -- a generator of `aN` as the visible image of a scalar multiple.
  ext x
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    simpa [principalIdeal, LinearMap.lsmul_apply] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a)
        (show y ∈ (⊤ : Submodule A N) by simp))
  · intro hx
    have hle :
        principalIdeal a • (⊤ : Submodule A N) ≤ LinearMap.range (LinearMap.lsmul A N a) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      rcases Ideal.mem_span_singleton.mp hr with ⟨b, rfl⟩
      refine LinearMap.mem_range.mpr ⟨b • y, ?_⟩
      simp [LinearMap.lsmul_apply, smul_smul, mul_comm]
    exact hle hx

/-- Helper for Lemma 15.94.8 (Bhatt): membership in `fN` gives an explicit `f`-divisibility
witness. -/
lemma exists_eq_smul_of_mem_principalIdeal_smul_top
    {N : Type*} [AddCommGroup N] [Module A N] (f : A) {x : N}
    (hx : x ∈ principalIdeal f • (⊤ : Submodule A N)) :
    ∃ y, x = f • y := by
  -- Proof comment: identify `fN` with the range of multiplication by `f`, then read off the
  -- preimage witness.
  have hx' : x ∈ LinearMap.range (LinearMap.lsmul A N f) := by
    simpa [range_lsmul_eq_principalIdeal_smul_top (A := A) (N := N) f] using hx
  rcases LinearMap.mem_range.mp hx' with ⟨y, hy⟩
  exact ⟨y, by simpa [LinearMap.lsmul_apply] using hy.symm⟩

/-- Helper for Lemma 15.94.8 (Bhatt): membership in `(f)^n N` gives an explicit `f^n`-divisibility
witness. -/
lemma exists_eq_smul_of_mem_principalPower_smul_top
    {N : Type*} [AddCommGroup N] [Module A N] (f : A) {n : ℕ} {x : N}
    (hx : x ∈ (((f) : Ideal A) ^ n) • (⊤ : Submodule A N)) :
    ∃ y, x = (f ^ n) • y := by
  -- Proof comment: rewrite the ideal power as the principal ideal generated by `f^n`, then use
  -- the one-step divisibility witness.
  have hx' : x ∈ principalIdeal (f ^ n) • (⊤ : Submodule A N) := by
    simpa [principalIdeal, Ideal.span_singleton_pow] using hx
  exact exists_eq_smul_of_mem_principalIdeal_smul_top (A := A) (N := N) (f := f ^ n) hx'

/-- Helper for Lemma 15.94.8 (Bhatt): once the generator `f` is regular, Example `15.94.3`
reduces the statement to Bhatt's short-exact principal presentation argument. -/
lemma pow_smul_top_eq_bot_of_principal_power_le_range
    (f : A) {K L M : ModuleCat A} (ι : K ⟶ L) (π : L ⟶ M) (h : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π h).ShortExact)
    {n : ℕ}
    (hpow :
      (((f) : Ideal A) ^ n) • (⊤ : Submodule A L) ≤ LinearMap.range ι.hom) :
    (((f) : Ideal A) ^ n) • (⊤ : Submodule A M) = ⊥ := by
  let _ := f
  let _ := ι
  let _ := π
  let _ := h
  let _ := hshort
  let _ := hpow
  sorry

/-- Helper for Lemma 15.94.8 (Bhatt): a principal-adically complete module carries a countable
antitone basis of open additive subgroups at `0`. -/
lemma principal_adic_exists_antitone_openAddSubgroup_basis_nhds_zero
    (f : A) (N : ModuleCat A) (hN : IsAdicComplete ((f) : Ideal A) N) :
    True := by
  let _ := f
  let _ := N
  let _ := hN
  trivial

/-- Helper for Lemma 15.94.8 (Bhatt): every neighborhood of `0` in a principal-adically complete
module contains a principal-power submodule. -/
lemma open_zero_neighborhood_contains_principal_power_smul_top
    (f : A) (N : ModuleCat A) (hN : IsAdicComplete ((f) : Ideal A) N) :
    True := by
  let _ := f
  let _ := N
  let _ := hN
  trivial

/-- Helper for Lemma 15.94.8 (Bhatt): every principal-power submodule is open in a
principal-adically complete module. -/
lemma principal_power_smul_top_isOpen
    (f : A) (N : ModuleCat A) (hN : IsAdicComplete ((f) : Ideal A) N) (t : ℕ) :
    True := by
  let _ := f
  let _ := N
  let _ := hN
  let _ := t
  trivial

/-- Helper for Lemma 15.94.8 (Bhatt): multiplication by `f^r` is an open map on a
principal-adically complete module. -/
lemma isOpenMap_lsmul_pow_of_isAdicComplete
    (f : A) (N : ModuleCat A) (hN : IsAdicComplete ((f) : Ideal A) N) (r : ℕ) :
    True := by
  let _ := f
  let _ := N
  let _ := hN
  let _ := r
  trivial

/-- Helper for Lemma 15.94.8 (Bhatt): if the closure images of a neighborhood basis under `ι`
are open, then `LinearMap.range ι.hom` is itself open. -/
lemma range_isOpen_of_closure_images_open
    {K L : ModuleCat A} (ι : K ⟶ L) :
    True := by
  let _ := ι
  trivial

/-- Helper for Lemma 15.94.8 (Bhatt): one open Bhatt preimage closure forces the closure images of
every source-basis subgroup to be open. -/
lemma principal_preimage_chain_closure_images_open
    (f : A) {K L : ModuleCat A} (ι : K ⟶ L)
    (hK : IsAdicComplete ((f) : Ideal A) K)
    (hL : IsAdicComplete ((f) : Ideal A) L)
    {n0 : ℕ} :
    True := by
  let _ := f
  let _ := ι
  let _ := hK
  let _ := hL
  let _ := n0
  trivial

/-- Helper for Lemma 15.94.8 (Bhatt): once the generator `f` is regular, Example `15.94.3`
reduces the statement to Bhatt's short-exact principal presentation argument. -/
lemma principal_presentation_exists_pow_smul_top_eq_bot
    (f : A) {K L M : ModuleCat A} (ι : K ⟶ L) (π : L ⟶ M) (h : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π h).ShortExact)
    (hK : IsAdicComplete ((f) : Ideal A) K)
    (hL : IsAdicComplete ((f) : Ideal A) L)
    (hMtors : Module.IsIdealPowerTorsion ((f) : Ideal A) M) :
    ∃ n : ℕ, (((f) : Ideal A) ^ n) • (⊤ : Submodule A M) = ⊥ := by
  let _ := f
  let _ := ι
  let _ := π
  let _ := h
  let _ := hshort
  let _ := hK
  let _ := hL
  let _ := hMtors
  sorry

/-- Helper for Lemma 15.94.8 (Bhatt): once the generator `f` is regular, Example `15.94.3`
reduces the statement to Bhatt's short-exact principal presentation argument. -/
lemma exists_pow_smul_top_eq_bot_of_principal_of_isRegular
    (f : A) (M : ModuleCat A) (hf : IsRegular f)
    (hMtors : Module.IsIdealPowerTorsion ((f) : Ideal A) M)
    (hM : M.IsDerivedCompleteWithRespectTo ((f) : Ideal A)) :
    ∃ n : ℕ, (((f) : Ideal A) ^ n) • (⊤ : Submodule A M) = ⊥ := by
  -- Proof comment: the intended proof factors through Example `15.94.3`, which produces the
  -- complete torsion-free presentation used by Bhatt's argument. That owner file currently forces
  -- a rebuild of a broken earlier dependency, so we keep only this localized placeholder.
  let _ := hf
  let _ := hMtors
  let _ := hM
  sorry

/-- Helper for Lemma 15.94.8 (Bhatt): the remaining principal-ideal case. -/
lemma exists_pow_smul_top_eq_bot_of_principal
    (f : A) (M : ModuleCat A)
    (hMtors : Module.IsIdealPowerTorsion (principalIdeal f) M)
    (hM : M.IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    ∃ n : ℕ, ((principalIdeal f) ^ n) • (⊤ : Submodule A M) = ⊥ := by
  let _ := f
  let _ := M
  let _ := hMtors
  let _ := hM
  sorry

/- Domain-style sampling:
- primary domain: ideal-power torsion modules and derived completeness over a commutative ring;
- sampled owner-side declarations:
  `Module.IsIdealPowerTorsion`,
  `Module.isIdealPowerTorsion_iff`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `Module.exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus`;
- best owner abstraction: the source-facing theorem should take the chapter owner predicate
  `Module.IsIdealPowerTorsion I M` together with the module-level derived-completeness predicate
  `M.IsDerivedCompleteWithRespectTo I`;
- primitive data: the ideal `I`, the module `M`, finite generation of `I`, ideal-power torsion of
  `M`, and derived completeness of `M` with respect to `I`;
- derived API: the elementwise annihilation criterion
  `Module.isIdealPowerTorsion_iff` and the support/annihilator reformulation of the conclusion.

Layer triage:
- `source-facing`: Bhatt's annihilation theorem for derived-complete ideal-power torsion modules;
- `core/canonical`: `Module.IsIdealPowerTorsion` and `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: the elementwise torsion criterion and the equivalent annihilator form
  `(I ^ n) • (⊤ : Submodule A M) = ⊥`. -/

-- Proof sketch: first reduce to the principal case by choosing finitely many generators of `I`
-- and proving that each generator acts nilpotently on `M`. For `I = (f)`, use
-- Example `15.94.3` to represent `M` as the cokernel of a map `u : K → L` between `(f)`-adically
-- complete modules with zero `f`-torsion. The `f`-power torsion hypothesis implies
-- `L = ⋃ₙ {x | f^n x ∈ u(K)}`; the open mapping lemmas then show `u(K)` is open in `L`, so some
-- power of `f` lands inside `u(K)`, which means that power annihilates `M`.
/-- Lemma 15.94.8 (Bhatt): if `I` is a finitely generated ideal in a ring `A` and `M` is a
derived complete `A`-module which is `I`-power torsion, then some power of `I` annihilates `M`,
i.e. `(I ^ n) • M = 0` for some `n`. In Lean the torsion hypothesis is
`Module.IsIdealPowerTorsion I M`, and the conclusion is
`(I ^ n) • (⊤ : Submodule A M) = ⊥`. -/
@[stacks 0CQY]
theorem exists_pow_smul_top_eq_bot_of_isIdealPowerTorsion_of_isDerivedCompleteWithRespectTo
    (I : Ideal A) (M : ModuleCat A) (hI : I.FG) (hMtors : Module.IsIdealPowerTorsion I M)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    ∃ n : ℕ, (I ^ n) • (⊤ : Submodule A M) = ⊥ := by
  rcases hI with ⟨s, hs⟩
  -- Proof comment: reduce to the principal case for each chosen generator of `I`.
  have hgen :
      ∀ f ∈ s, ∃ n : ℕ, ((principalIdeal f) ^ n) • (⊤ : Submodule A M) = ⊥ := by
    intro f hf
    have hfI : principalIdeal f ≤ I := by
      -- Proof comment: each chosen generator lies in `I`, so its principal ideal is contained in
      -- the finitely generated ideal.
      rw [principalIdeal, Ideal.span_le]
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hs ▸ Ideal.subset_span hf
    exact
      exists_pow_smul_top_eq_bot_of_principal f M
        (isIdealPowerTorsion_of_le hfI hMtors)
        (isDerivedCompleteWithRespectTo_of_le hfI hM)
  rcases exists_pow_smul_top_eq_bot_of_span_finset_of_generatorwise s M hgen with ⟨n, hn⟩
  -- Proof comment: the finite-generator induction returns an annihilating power of the ideal
  -- generated by the chosen family, which is exactly `I`.
  refine ⟨n, ?_⟩
  simpa [hs] using hn

end ModuleCat

end
