import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Valuation.ValuationRing
import StacksProject_2024.Chap10.Lemma_10_5_3
import StacksProject_2024.Chap10.Lemma_10_90_3
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap15.Lemma_15_125_1
import StacksProject_2024.Chap15.Lemma_15_125_2_Generalized_valuation_rings
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: finitely presented module decompositions over generalized valuation rings;
- sampled owner declarations:
  `PreValuationRing`,
  `PreValuationRing.iff_ideal_total`,
  `principalIdeal`;
- best owner abstraction: this item remains `source-facing`, with the ambient generalized
  valuation-ring hypothesis carried directly by the canonical owner `PreValuationRing R`; the
  cyclic quotient summands should use the chapter owner `principalIdeal` rather than restating
  `Ideal.span ({f} : Set R)`. The bridge from the ideal-order formulation to this owner is
  `PreValuationRing.iff_ideal_total`; the stronger PID structure theorem
  `Module.equiv_free_prod_directSum` is only a downstream specialization and would change the
  theorem's semantics by introducing a free part, so the decomposition here should stay on the
  canonical `LinearEquiv`/`DirectSum` surface instead of collapsing to that later view or
  introducing a local package;
- primitive data vs. derived API:
  primitive data is the ambient ring `R` together with the finitely presented `R`-module `M`;
  derived API is the finite index `n`, the family `f : Fin n → R`, and the resulting linear
  equivalence from `M` to the direct sum of the corresponding principal quotient modules.

Source/core/bridge triage:
- `source-facing`: the existence of a finite cyclic-quotient decomposition for `M`;
- `core/canonical`: `PreValuationRing`, `principalIdeal`, and `LinearEquiv`;
- `bridge/view`: `PreValuationRing.iff_ideal_total`, relating the source's ideal-order language to
  the canonical owner `PreValuationRing`.
-/

section

variable {R : Type u} [CommRing R] [PreValuationRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-- Helper for Lemma 15.125.3: a subsingleton module is the empty direct sum of principal
quotients. -/
lemma exists_linearEquiv_directSum_principal_quotients_of_subsingleton_module
    {R₀ : Type u} [CommRing R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀] [Subsingleton M₀] :
    ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty (M₀ ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) := by
  -- The source's empty decomposition is exactly the unique map between subsingleton modules.
  refine ⟨0, Fin.elim0, ?_⟩
  exact ⟨LinearEquiv.ofSubsingleton _ _⟩

/-- Helper for Lemma 15.125.3: over a subsingleton ring, every module is linearly equivalent to
the empty direct sum of principal quotients. -/
lemma exists_linearEquiv_directSum_principal_quotients_of_subsingleton
    {R₀ : Type u} [CommRing R₀] [Subsingleton R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀] :
    ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty (M₀ ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) := by
  letI : Subsingleton M₀ := Module.subsingleton R₀ M₀
  -- First collapse the module to a subsingleton, then reuse the empty-sum helper.
  exact exists_linearEquiv_directSum_principal_quotients_of_subsingleton_module
    (R₀ := R₀) (M₀ := M₀)

/-- Helper for Lemma 15.125.3: a nontrivial generalized valuation ring is local and Bézout. -/
lemma generalized_valuation_ring_isLocalRing_and_isBezout
    {R₀ : Type u} [CommRing R₀] [PreValuationRing R₀] [Nontrivial R₀] :
    IsLocalRing R₀ ∧ IsBezout R₀ := by
  -- First translate the generalized valuation-ring hypothesis to totality of ideals, then use the
  -- chapter API that totality implies the local Bézout condition.
  have hTotal : @Std.Total (Ideal R₀) (· ≤ ·) := PreValuationRing.iff_ideal_total.mp inferInstance
  exact ⟨inferInstance, isBezout_of_ideal_total hTotal⟩

/-- Helper for Lemma 15.125.3: ideals in a nontrivial generalized valuation ring are totally
ordered by inclusion. -/
lemma generalized_valuation_ring_ideal_total
    {R₀ : Type u} [CommRing R₀] [PreValuationRing R₀] [Nontrivial R₀] :
    @Std.Total (Ideal R₀) (· ≤ ·) := by
  -- The same TFAE also gives the total-order formulation, which is the main ring-theoretic
  -- invariant used in the inductive splitting argument.
  exact PreValuationRing.iff_ideal_total.mp inferInstance

/-- Helper for Lemma 15.125.3: quotienting a finite-dimensional vector space by the span of a
nonzero vector strictly lowers the dimension. -/
lemma finrank_quotient_span_singleton_lt_of_nonzero
    {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (v : V) (hv : v ≠ 0) :
    Module.finrank k (V ⧸ Submodule.span k ({v} : Set V)) < Module.finrank k V := by
  let W : Submodule k V := Submodule.span k ({v} : Set V)
  let toSpan : k →ₗ[k] W :=
    LinearMap.codRestrict W (LinearMap.toSpanSingleton k V v) (fun r ↦ by
      -- The singleton-span map lands in the cyclic span generated by `v`.
      rw [LinearMap.toSpanSingleton_apply, Submodule.mem_span_singleton]
      exact ⟨r, rfl⟩)
  have htoSpan_bijective : Function.Bijective toSpan := by
    constructor
    · intro a b hab
      -- Equality in the span forces the underlying scalar coefficients to agree because `v ≠ 0`.
      have hab' : a • v = b • v := congrArg Subtype.val hab
      have hsub : (a - b) • v = 0 := by
        rw [sub_smul, hab', sub_self]
      rcases smul_eq_zero.mp hsub with hab0 | hv0
      · exact sub_eq_zero.mp hab0
      · exact (hv hv0).elim
    · intro y
      -- Every element of the singleton span is some scalar multiple of `v`.
      rcases Submodule.mem_span_singleton.mp y.2 with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      simpa [toSpan, LinearMap.toSpanSingleton_apply] using ha
  let eSpan : k ≃ₗ[k] W := LinearEquiv.ofBijective toSpan htoSpan_bijective
  have hW_finrank : Module.finrank k W = 1 := by
    -- The span of one nonzero vector is linearly equivalent to the base field itself.
    simpa using (LinearEquiv.finrank_eq eSpan).symm
  have hquot :
      Module.finrank k (V ⧸ W) + Module.finrank k W = Module.finrank k V := by
    -- Quotient finrank plus subspace finrank recovers the ambient finrank.
    simpa [W] using Submodule.finrank_quotient_add_finrank W
  have hquot' : Module.finrank k (V ⧸ W) + 1 = Module.finrank k V := by
    -- The previous identity simplifies because the singleton span is one-dimensional.
    simpa [hW_finrank] using hquot
  -- Replacing the span by its one-dimensional description gives the strict inequality.
  have hlt : Module.finrank k (V ⧸ W) < Module.finrank k (V ⧸ W) + 1 := Nat.lt_succ_self _
  rwa [hquot'] at hlt

section LocalResidueHelpers

variable [IsLocalRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R
local notation "κ" => IsLocalRing.ResidueField R
local notation "Mbar" => M ⧸ (𝔪 • (⊤ : Submodule R M))

local instance : Module κ Mbar := inferInstanceAs (Module (R ⧸ 𝔪) Mbar)
local instance : SMulCommClass R κ Mbar := inferInstanceAs (SMulCommClass R (R ⧸ 𝔪) Mbar)
local instance : IsScalarTower R κ Mbar := inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) Mbar)
local instance : Module.Finite κ Mbar := inferInstanceAs (Module.Finite (R ⧸ 𝔪) Mbar)

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: lifts of a residue-field basis generate the whole module. -/
lemma basis_lifts_span_top [Module.Finite R M]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) κ Mbar) (x : Fin (n + 1) → M)
    (hx : ∀ i, Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) (x i) = b i) :
    Submodule.span R (Set.range x) = ⊤ := by
  classical
  let s : Finset M := Finset.univ.image x
  have hs : (s : Set M) = Set.range x := by
    -- Replace the finite image of `Fin (n + 1)` by the corresponding range set.
    ext y
    simp [s]
  have hquot :
      Submodule.span R ((Submodule.mkQ (𝔪 • (⊤ : Submodule R M))) '' (s : Set M)) = ⊤ := by
    -- First rewrite the quotient images of the finite lift set as the range of the lifted basis.
    rw [hs]
    have himage :
        ((Submodule.mkQ (𝔪 • (⊤ : Submodule R M))) '' Set.range x : Set Mbar) =
          Set.range (fun i : Fin (n + 1) ↦ Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) (x i)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
    rw [himage]
    have hcomp :
        (fun i : Fin (n + 1) ↦ Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) (x i)) = b := by
      funext i
      exact hx i
    -- Then forget from the residue field back to `R`; the basis still spans the quotient module.
    rw [hcomp, ← Submodule.restrictScalars_span R κ Ideal.Quotient.mk_surjective,
      Submodule.restrictScalars_eq_top_iff]
    exact b.span_eq
  have hmaxJac₀ : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) :=
    IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)
  have hmaxJac : IsLocalRing.maximalIdeal R ≤ Ring.jacobson R := by
    -- In a local ring the maximal ideal lies in the Jacobson radical.
    rw [← Ideal.jacobson_bot]
    exact hmaxJac₀
  -- Nakayama upgrades generation modulo `𝔪` to generation upstairs.
  simpa [hs] using
    (span_eq_top_of_quotient_span_eq_top_of_le_ring_jacobson (I := 𝔪) (s := s) hquot hmaxJac)

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: a nonzero residue class cannot be represented by an element of
`maximalIdeal R • ⊤`. -/
lemma lift_not_mem_maximalIdeal_smul_of_ne_zero_residue
    {x : M} (hx : Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x ≠ 0) :
    x ∉ 𝔪 • (⊤ : Submodule R M) := by
  -- Any element of `𝔪 • ⊤` maps to zero in the quotient by definition.
  intro hxmem
  exact hx (by simpa using hxmem)

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: the image of a cyclic span in the residue quotient is the span of
its residue class. -/
lemma map_mkQ_span_singleton_eq_residue_span_singleton (x : M) :
    Submodule.map (Submodule.mkQ (𝔪 • (⊤ : Submodule R M))) (R ∙ x) =
      (Submodule.span κ ({Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x} : Set Mbar)).restrictScalars
        R := by
  -- First identify the image of the cyclic span with the span of the image singleton.
  calc
    Submodule.map (Submodule.mkQ (𝔪 • (⊤ : Submodule R M))) (R ∙ x) =
        Submodule.span R ({Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x} : Set Mbar) := by
          simpa [Submodule.map_span, Set.image_singleton]
    -- Then rewrite that `R`-span as the restricted scalar view of the `κ`-span.
    _ =
        (Submodule.span κ ({Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x} : Set Mbar)).restrictScalars
          R := by
            rw [← Submodule.restrictScalars_span R κ Ideal.Quotient.mk_surjective]

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: quotienting by a cyclic span carries `maximalIdeal R • ⊤` to the
corresponding residue submodule of the quotient. -/
lemma map_mkQ_maximalIdeal_smul_top_eq_maximalIdeal_smul_top_quotient (x : M) :
    Submodule.map (Submodule.mkQ (R ∙ x)) (𝔪 • (⊤ : Submodule R M)) =
      𝔪 • (⊤ : Submodule R (M ⧸ (R ∙ x))) := by
  -- Mapping a scalar multiple commutes with taking the image, and the quotient map has full range.
  simp [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: the two quotient orders used in the residue-step transport define
the same quotient submodule. -/
lemma maximalIdeal_smul_top_sup_span_singleton_eq_span_singleton_sup_maximalIdeal_smul_top
    (x : M) :
    (𝔪 • (⊤ : Submodule R M)) ⊔ (R ∙ x) = (R ∙ x) ⊔ (𝔪 • (⊤ : Submodule R M)) := by
  -- The transport only swaps the order of the two summands inside the join.
  exact sup_comm _ _

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: quotienting by `R ∙ x` and then reducing modulo `maximalIdeal R`
matches quotienting the residue module by the span of the residue class of `x`, viewed over `R`
via restricted scalars. -/
noncomputable def residue_quotient_linearEquiv_quotient_residue_span_singleton (x : M) :
    ((M ⧸ (R ∙ x)) ⧸ (𝔪 • (⊤ : Submodule R (M ⧸ (R ∙ x))))) ≃ₗ[R]
      (Mbar ⧸
        (Submodule.span κ ({Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x} : Set Mbar)).restrictScalars
          R) :=
  -- The transport follows the canonical quotient-of-quotient route from the source proof:
  -- first rewrite the visible quotient submodule as an image under `mkQ`, collapse to the quotient
  -- by the join, swap the join order, and then expand back out on the residue side.
  (Submodule.quotEquivOfEq
      (𝔪 • (⊤ : Submodule R (M ⧸ (R ∙ x))))
      (Submodule.map (Submodule.mkQ (R ∙ x)) (𝔪 • (⊤ : Submodule R M)))
      (map_mkQ_maximalIdeal_smul_top_eq_maximalIdeal_smul_top_quotient
        (R := R) (M := M) x).symm) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup
      (R ∙ x) (𝔪 • (⊤ : Submodule R M))) ≪≫ₗ
    (Submodule.quotEquivOfEq
      ((R ∙ x) ⊔ (𝔪 • (⊤ : Submodule R M)))
      ((𝔪 • (⊤ : Submodule R M)) ⊔ (R ∙ x))
      (maximalIdeal_smul_top_sup_span_singleton_eq_span_singleton_sup_maximalIdeal_smul_top
        (R := R) (M := M) x).symm) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup
      (𝔪 • (⊤ : Submodule R M)) (R ∙ x)).symm ≪≫ₗ
    (Submodule.quotEquivOfEq
      (Submodule.map (Submodule.mkQ (𝔪 • (⊤ : Submodule R M))) (R ∙ x))
      (((Submodule.span κ ({Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x} : Set Mbar)) :
        Submodule κ Mbar).restrictScalars R)
      (map_mkQ_span_singleton_eq_residue_span_singleton (R := R) (M := M) x))

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: the recursive residue quotient has the same residue-field
dimension as quotienting the residue module by the span of the chosen residue class. -/
lemma residue_quotient_finrank_eq_quotient_residue_span_singleton
    [Module.Finite κ Mbar] (x : M) :
    Module.finrank κ (((M ⧸ (R ∙ x)) ⧸ (𝔪 • (⊤ : Submodule R (M ⧸ (R ∙ x)))))) =
      Module.finrank κ
        (Mbar ⧸ Submodule.span κ ({Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x} : Set Mbar)) := by
  let eR := residue_quotient_linearEquiv_quotient_residue_span_singleton (R := R) (M := M) x
  let eκ :
      (((M ⧸ (R ∙ x)) ⧸ (𝔪 • (⊤ : Submodule R (M ⧸ (R ∙ x)))))) ≃ₗ[κ]
        (Mbar ⧸ Submodule.span κ ({Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x} : Set Mbar)) :=
    { toFun := eR
      invFun := eR.symm
      left_inv := eR.left_inv
      right_inv := eR.right_inv
      map_add' := eR.map_add
      map_smul' := fun c y ↦ by
        -- Route correction: reuse the existing `R`-linear transport and upgrade scalar
        -- compatibility by writing every residue-field scalar as the class of a ring element.
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        simpa using eR.map_smul r y }
  -- Finite-dimensionality is preserved across the resulting `κ`-linear equivalence.
  simpa using LinearEquiv.finrank_eq eκ

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: quotienting by the cyclic span of a nonzero residue lift strictly
lowers the residue-field dimension. -/
lemma residue_finrank_lt_of_nonzero_lift [Nontrivial R] [Module.Finite R M]
    {x : M} (hx : Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x ≠ 0) :
    Module.finrank κ (((M ⧸ (R ∙ x)) ⧸ (𝔪 • (⊤ : Submodule R (M ⧸ (R ∙ x)))))) <
      Module.finrank κ Mbar := by
  letI : Module.Finite R Mbar := Module.Finite.quotient R (𝔪 • (⊤ : Submodule R M))
  letI : Module.Finite κ Mbar := Module.Finite.of_restrictScalars_finite R κ Mbar
  -- First rewrite the recursive quotient as the quotient of `Mbar` by the span of the chosen
  -- residue class.
  rw [residue_quotient_finrank_eq_quotient_residue_span_singleton (R := R) (M := M) x]
  -- Then apply the standard strict-dimension drop for quotienting by a nonzero singleton span.
  exact finrank_quotient_span_singleton_lt_of_nonzero
    (k := κ) (V := Mbar) (Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x) hx

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: if the residue quotient `M / 𝔪M` is subsingleton, then Nakayama
forces `M` itself to be subsingleton. -/
lemma subsingleton_of_subsingleton_maximalIdeal_smul_quotient [Module.Finite R M]
    (hsub : Subsingleton (M ⧸ (𝔪 • (⊤ : Submodule R M)))) :
    Subsingleton M := by
  letI : Subsingleton (M ⧸ (𝔪 • (⊤ : Submodule R M))) := hsub
  have htop : 𝔪 • (⊤ : Submodule R M) = ⊤ := by
    -- Every element has zero residue class, so every element already lies in `𝔪 • ⊤`.
    apply top_unique
    intro x hx
    have hxzero : Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x = 0 := Subsingleton.elim _ _
    simpa using hxzero
  have hmaxJac₀ : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) :=
    IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)
  have hmaxJac : IsLocalRing.maximalIdeal R ≤ Ring.jacobson R := by
    -- In a local ring the maximal ideal lies in the Jacobson radical.
    rw [← Ideal.jacobson_bot]
    exact hmaxJac₀
  -- Apply the Nakayama owner already imported to the equality `𝔪 • ⊤ = ⊤`.
  exact
    subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
      (I := 𝔪) (M := M) htop hmaxJac

end LocalResidueHelpers

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: once a finite family spans `M`, the module annihilator is the
intersection of the annihilators of the cyclic spans of the chosen generators. -/
lemma module_annihilator_eq_iInf_annihilator_of_span_eq_top
    {n : ℕ} (x : Fin n → M) (hx : Submodule.span R (Set.range x) = ⊤) :
    Module.annihilator R M = ⨅ i, Submodule.annihilator (R ∙ x i) := by
  classical
  refine le_antisymm ?_ ?_
  · intro r hr
    -- A scalar annihilating all of `M` annihilates each chosen cyclic summand in particular.
    rw [Ideal.mem_iInf]
    intro i
    simpa [Submodule.mem_annihilator_span_singleton] using (Module.mem_annihilator.mp hr (x i))
  · intro r hr
    -- Conversely, the cyclic annihilator data extends from the generators to all of `M`.
    rw [Ideal.mem_iInf] at hr
    rw [Module.mem_annihilator]
    intro m
    have hm : m ∈ Submodule.span R (Set.range x) := by
      simp [hx]
    refine Submodule.span_induction (p := fun z _ ↦ r • z = 0) ?_ ?_ ?_ ?_ hm
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      simpa [Submodule.mem_annihilator_span_singleton] using (hr i)
    · simp
    · intro a b _ _ ha hb
      rw [smul_add, ha, hb, add_zero]
    · intro a b _ hb
      calc
        r • (a • b) = (r * a) • b := by rw [smul_smul]
        _ = (a * r) • b := by rw [mul_comm]
        _ = a • (r • b) := by rw [smul_smul]
        _ = 0 := by rw [hb, smul_zero]

/-- Helper for Lemma 15.125.3: if one term in a finite infimum is below all the others, then it
is the infimum. -/
lemma iInf_eq_of_le {α : Type*} [CompleteLattice α]
    {n : ℕ} (f : Fin n → α) (i₀ : Fin n) (hmin : ∀ i, f i₀ ≤ f i) :
    (⨅ i, f i) = f i₀ := by
  refine le_antisymm ?_ ?_
  · -- The infimum always lies below each individual term.
    exact iInf_le f i₀
  · -- The chosen minimal term is below the whole family, hence below the infimum.
    exact le_iInf hmin

/-- Helper for Lemma 15.125.3: a finite nonempty family in a total preorder has a term below all
the others. -/
lemma exists_le_all_fin_succ_of_total
    {α : Type*} [Preorder α] (hTotal : @Std.Total α (· ≤ ·)) :
    ∀ {n : ℕ} (f : Fin (n + 1) → α), ∃ i₀ : Fin (n + 1), ∀ i, f i₀ ≤ f i
  | 0, f => ⟨0, fun i ↦ by
      -- In the singleton index type every entry is the distinguished one.
      fin_cases i
      exact le_rfl⟩
  | n + 1, f => by
      -- Compare a minimal term from the initial segment with the final term.
      obtain ⟨i₀, hi₀⟩ :=
        exists_le_all_fin_succ_of_total hTotal (fun i : Fin (n + 1) ↦ f i.castSucc)
      rcases hTotal.total (f i₀.castSucc) (f (Fin.last (n + 1))) with hmin | hlast
      · refine ⟨i₀.castSucc, ?_⟩
        intro i
        -- If the chosen term also lies below the last entry, then it is minimal in the full
        -- family.
        cases i using Fin.lastCases with
        | last =>
            simpa using hmin
        | cast j =>
            simpa using hi₀ j
      · refine ⟨Fin.last (n + 1), ?_⟩
        intro i
        -- Otherwise the last entry lies below the candidate, and hence below every initial entry.
        cases i using Fin.lastCases with
        | last =>
            exact le_rfl
        | cast j =>
            exact le_trans hlast (hi₀ j)

omit [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: among finitely many cyclic annihilators, one is minimal. -/
lemma exists_minimal_cyclic_annihilator_index
    {n : ℕ} [Nontrivial R] (x : Fin (n + 1) → M) :
    ∃ i₀ : Fin (n + 1), ∀ i,
      Submodule.annihilator (R ∙ x i₀) ≤ Submodule.annihilator (R ∙ x i) := by
  -- The selector step reduces first to choosing a minimal ideal in the total order on ideals.
  simpa using
    (exists_le_all_fin_succ_of_total
      (α := Ideal R)
      (hTotal := generalized_valuation_ring_ideal_total (R₀ := R))
      (fun i ↦ Submodule.annihilator (R ∙ x i)))

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: if a spanning family has one cyclic annihilator below all the
others, then that cyclic annihilator already equals the module annihilator. -/
lemma module_annihilator_eq_of_span_eq_top_of_minimal_cyclic_annihilator
    {n : ℕ} (x : Fin (n + 1) → M) (hx : Submodule.span R (Set.range x) = ⊤)
    (i₀ : Fin (n + 1))
    (hmin : ∀ i, Submodule.annihilator (R ∙ x i₀) ≤ Submodule.annihilator (R ∙ x i)) :
    Module.annihilator R M = Submodule.annihilator (R ∙ x i₀) := by
  -- First rewrite the module annihilator as the infimum over the cyclic annihilators of a
  -- spanning family.
  calc
    Module.annihilator R M = ⨅ i, Submodule.annihilator (R ∙ x i) :=
      module_annihilator_eq_iInf_annihilator_of_span_eq_top (R := R) (M := M) x hx
    -- Then collapse that finite infimum to the chosen minimal term.
    _ = Submodule.annihilator (R ∙ x i₀) := iInf_eq_of_le _ _ hmin

section LocalResidueHelpers

variable [IsLocalRing R] [Nontrivial R] [Module.Finite R M]

local notation "𝔪" => IsLocalRing.maximalIdeal R
local notation "κ" => IsLocalRing.ResidueField R
local notation "Mbar" => M ⧸ (𝔪 • (⊤ : Submodule R M))

local instance : Module κ Mbar := inferInstanceAs (Module (R ⧸ 𝔪) Mbar)
local instance : SMulCommClass R κ Mbar := inferInstanceAs (SMulCommClass R (R ⧸ 𝔪) Mbar)
local instance : IsScalarTower R κ Mbar := inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) Mbar)

omit [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: among the vectors of a residue-field basis, one has the property
that every lift already has the module annihilator. -/
lemma exists_basis_index_with_module_annihilator_for_all_lifts
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) κ Mbar) :
    ∃ i₀ : Fin (n + 1), ∀ z : M,
      Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) z = b i₀ →
        Module.annihilator R M = Submodule.annihilator (R ∙ z) := by
  classical
  by_contra h
  push Not at h
  choose z hzlift hzbad using h
  have hspan : Submodule.span R (Set.range z) = ⊤ := by
    -- The chosen bad lifts still project to a basis, so they generate `M`.
    exact basis_lifts_span_top (R := R) (M := M) b z hzlift
  obtain ⟨i₀, hi₀⟩ := exists_minimal_cyclic_annihilator_index (R := R) (M := M) z
  have hcollapse :
      Module.annihilator R M = Submodule.annihilator (R ∙ z i₀) := by
    -- The minimal cyclic annihilator in that spanning family must equal the module annihilator.
    exact
      module_annihilator_eq_of_span_eq_top_of_minimal_cyclic_annihilator
        (R := R) (M := M) z hspan i₀ hi₀
  -- The selected index was declared bad, contradicting the annihilator collapse above.
  exact hzbad i₀ hcollapse

end LocalResidueHelpers

omit [PreValuationRing R] in
/-- Helper for Lemma 15.125.3: failure of `f ∣ g` forces the opposite divisibility with a factor
in the maximal ideal. -/
lemma exists_factor_mem_maximalIdeal_of_not_dvd [IsLocalRing R] [IsBezout R]
    {f g : R} (hfg : ¬ f ∣ g) :
    ∃ h : R, h ∈ IsLocalRing.maximalIdeal R ∧ f = h * g := by
  have hnot_le : ¬ Ideal.span ({g} : Set R) ≤ Ideal.span ({f} : Set R) := by
    intro hspan
    apply hfg
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp <|
      hspan (Ideal.subset_span (by simp : g ∈ ({g} : Set R)))
    exact ⟨a, by simpa [mul_comm] using ha.symm⟩
  rcases (ideal_total_of_isLocalRing_isBezout (R := R)).total
      (Ideal.span ({f} : Set R)) (Ideal.span ({g} : Set R)) with hspan | hspan
  · -- Totality of principal ideals gives the opposite divisibility once `f ∤ g` is excluded.
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp <|
      hspan (Ideal.subset_span (by simp : f ∈ ({f} : Set R)))
    refine ⟨h, ?_, hh.symm⟩
    by_contra hhmax
    have hunit : IsUnit h := IsLocalRing.notMem_maximalIdeal.mp hhmax
    rcases hunit with ⟨u, rfl⟩
    apply hfg
    refine ⟨↑u⁻¹, ?_⟩
    calc
      g = ↑u⁻¹ * (↑u * g) := by simp
      _ = ↑u⁻¹ * f := by rw [hh]
      _ = f * ↑u⁻¹ := by ac_rfl
  · exact (hnot_le hspan).elim

section LocalResidueReplacement

variable [IsLocalRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R

omit [PreValuationRing R] [Module.FinitePresentation R M] in
/-- Helper for Lemma 15.125.3: subtracting a maximal-ideal multiple does not change the residue
class modulo `maximalIdeal R • ⊤`. -/
lemma mkQ_sub_smul_eq_of_mem_maximalIdeal
    {x z : M} {h : R} (hh : h ∈ 𝔪) :
    Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) (x - h • z) =
      Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x := by
  -- The replacement step only changes `x` by an element of `𝔪 • ⊤`, so its residue class is
  -- unchanged.
  apply (Submodule.Quotient.eq (𝔪 • (⊤ : Submodule R M))).2
  -- Rewrite the quotient equality as membership of the correction term in `𝔪 • ⊤`.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Submodule.smul_mem_smul
      (show -h ∈ 𝔪 by simpa using Submodule.neg_mem 𝔪 hh)
      (by simp : z ∈ (⊤ : Submodule R M)))

/-
The next three lemmas isolate the source-faithful replacement step: first the raw algebraic
computation, then the nondivisible zero conclusion, and finally the hard principal-pure inclusion.
-/
omit [PreValuationRing R] [Module.FinitePresentation R M] [IsLocalRing R] in
/-- Helper for Lemma 15.125.3: the selector replacement step kills the corrected lift after
factoring the scalar through the maximal ideal. -/
lemma smul_sub_eq_zero_of_eq_mul_smul
    {a r h : R} {x z : M} (hr : r = h * a) (hax : a • x = r • z) :
    a • (x - h • z) = 0 := by
  -- Expand the corrected lift and rewrite the second term using the chosen factorization.
  calc
    a • (x - h • z) = a • x - a • (h • z) := by rw [smul_sub]
    _ = r • z - a • (h • z) := by rw [hax]
    _ = r • z - (h * a) • z := by rw [smul_smul, mul_comm]
    _ = r • z - r • z := by rw [hr]
    _ = 0 := sub_self _

omit [PreValuationRing R] [Module.FinitePresentation R M] [IsLocalRing R] in
/-- Helper for Lemma 15.125.3: if a residue-equivalent lift has the module annihilator, then a
nondivisible relation `a • x = r • z` forces `a • x = 0`. -/
lemma smul_eq_zero_of_not_dvd_of_lift_annihilator_eq_module_annihilator [IsLocalRing R] [IsBezout R]
    {x : M}
    (hxann : ∀ z : M,
      Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) z =
        Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x →
          Module.annihilator R M = Submodule.annihilator (R ∙ z))
    {a r : R} {z : M} (hax : a • x = r • z) (hr : ¬ r ∣ a) :
    a • x = 0 := by
  obtain ⟨h, hh𝔪, hr_eq⟩ :=
    exists_factor_mem_maximalIdeal_of_not_dvd (R := R) (f := r) (g := a) hr
  let y : M := x - h • z
  have hy_residue :
      Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) y =
        Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x := by
    -- The correction term is in `𝔪 • ⊤`, so the residue class is unchanged.
    simpa [y] using
      mkQ_sub_smul_eq_of_mem_maximalIdeal (R := R) (M := M) (x := x) (z := z) hh𝔪
  have hy_ann :
      Module.annihilator R M = Submodule.annihilator (R ∙ y) := hxann y hy_residue
  have ha_mem : a ∈ Module.annihilator R M := by
    -- The corrected lift is annihilated by `a`, so `a` lies in the cyclic annihilator and hence
    -- in the module annihilator.
    rw [hy_ann]
    exact
      (Submodule.mem_annihilator_span_singleton y a).2
        (smul_sub_eq_zero_of_eq_mul_smul (a := a) (r := r) (h := h) hr_eq hax)
  -- Once `a` annihilates all of `M`, it annihilates the original lift `x`.
  exact Module.mem_annihilator.mp ha_mem x

omit [PreValuationRing R] [Module.FinitePresentation R M] [IsLocalRing R] in
/-- Helper for Lemma 15.125.3: the only nontrivial inclusion for principal-purity of a cyclic
span follows from the replacement argument. -/
lemma span_singleton_inf_principalIdeal_smul_top_le_principalIdeal_smul_span_singleton
    [IsLocalRing R] [IsBezout R]
    {x : M}
    (hxann : ∀ z : M,
      Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) z =
        Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x →
          Module.annihilator R M = Submodule.annihilator (R ∙ z)) :
    ∀ r : R,
      ((R ∙ x) ⊓ principalIdeal r • (⊤ : Submodule R M) : Submodule R M) ≤
        principalIdeal r • (R ∙ x)
  := by
  intro r u hu
  rw [Submodule.mem_inf] at hu
  rcases Submodule.mem_span_singleton.mp hu.1 with ⟨a, rfl⟩
  rw [Submodule.ideal_span_singleton_smul] at hu ⊢
  rcases (Submodule.mem_smul_pointwise_iff_exists (a • x) r (⊤ : Submodule R M)).1 hu.2 with
    ⟨z, -, hz⟩
  by_cases hdiv : r ∣ a
  · rcases hdiv with ⟨b, rfl⟩
    refine (Submodule.mem_smul_pointwise_iff_exists ((r * b) • x) r (R ∙ x)).2 ?_
    refine ⟨b • x, ?_, ?_⟩
    · exact (R ∙ x).smul_mem b (Submodule.subset_span (by simp))
    · simp [smul_smul]
  · refine (Submodule.mem_smul_pointwise_iff_exists (a • x) r (R ∙ x)).2 ?_
    refine ⟨0, by simp, ?_⟩
    -- In the nondivisible branch the replacement contradiction shows the element is zero.
    simpa [smul_zero] using
      smul_eq_zero_of_not_dvd_of_lift_annihilator_eq_module_annihilator
        (R := R) (M := M) hxann (a := a) (r := r) (z := z) hz.symm hdiv |>.symm

omit [PreValuationRing R] [Module.FinitePresentation R M] [IsLocalRing R] in
/-- Helper for Lemma 15.125.3: the cyclic span of the selected lift is principal-pure. -/
lemma span_singleton_subtype_isPrincipalPure_of_lift_annihilator_eq_module_annihilator
    [IsLocalRing R] [IsBezout R]
    {x : M}
    (hxann : ∀ z : M,
      Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) z =
        Submodule.mkQ (𝔪 • (⊤ : Submodule R M)) x →
          Module.annihilator R M = Submodule.annihilator (R ∙ z)) :
    LinearMap.IsPrincipalPure ((R ∙ x).subtype) := by
  intro r
  rw [Submodule.range_subtype]
  apply le_antisymm
  · intro u hu
    rw [Submodule.ideal_span_singleton_smul] at hu
    rcases (Submodule.mem_smul_pointwise_iff_exists u r (R ∙ x)).1 hu with ⟨y, hy, rfl⟩
    rw [Submodule.mem_inf]
    constructor
    · exact (R ∙ x).smul_mem r hy
    · rw [Submodule.ideal_span_singleton_smul]
      exact (Submodule.mem_smul_pointwise_iff_exists (r • y) r (⊤ : Submodule R M)).2
        ⟨y, Submodule.mem_top, rfl⟩
  · -- Route correction: close principal-purity by proving only the hard reverse inclusion.
    exact
      span_singleton_inf_principalIdeal_smul_top_le_principalIdeal_smul_span_singleton
        (R := R) (M := M) hxann r

end LocalResidueReplacement

/-- Helper for Lemma 15.125.3: quotienting a finitely presented module by a cyclic span preserves
finite presentation. -/
lemma quotient_span_singleton_finitePresentation
    {R₀ : Type u} [Ring R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    [Module.FinitePresentation R₀ M₀] (x : M₀) :
    Module.FinitePresentation R₀ (M₀ ⧸ (R₀ ∙ x)) := by
  letI : Module.Finite R₀ (R₀ ∙ x) := Module.Finite.of_fg (Submodule.fg_span_singleton x)
  -- Use the canonical short exact quotient row `0 → R ∙ x → M → M / (R ∙ x) → 0`.
  exact
    Module.finitePresentation_of_surjective_of_exact
      ((R₀ ∙ x).subtype)
      (Submodule.mkQ (R₀ ∙ x))
      (Submodule.mkQ_surjective (R₀ ∙ x))
      (LinearMap.exact_iff.2 (by
        rw [Submodule.range_subtype, Submodule.ker_mkQ]))

/-- Helper for Lemma 15.125.3: the kernel of the quotient map by a cyclic span is that cyclic
span. -/
lemma ker_mkQ_span_singleton_eq
    {R₀ : Type u} [Ring R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    (x : M₀) :
    LinearMap.ker (Submodule.mkQ (R₀ ∙ x)) = R₀ ∙ x := by
  -- The canonical quotient row identifies the kernel of `mkQ` with the submodule we quotient by.
  simpa using (Submodule.ker_mkQ (R₀ ∙ x))

/-- Helper for Lemma 15.125.3: subtracting the chosen section from a point leaves a vector in the
cyclic kernel. -/
lemma sub_section_mem_span_singleton_of_mkQ_section
    {R₀ : Type u} [Ring R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    (x : M₀) (σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀)
    (hσ : (Submodule.mkQ (R₀ ∙ x)).comp σ = LinearMap.id)
    (z : M₀) :
    z - σ (Submodule.mkQ (R₀ ∙ x) z) ∈ R₀ ∙ x := by
  have hσ_apply :
      Submodule.mkQ (R₀ ∙ x) (σ (Submodule.mkQ (R₀ ∙ x) z)) =
        Submodule.mkQ (R₀ ∙ x) z := by
    -- Evaluate the section identity at the residue class of `z`.
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀ ⧸ (R₀ ∙ x) ↦
        f (Submodule.mkQ (R₀ ∙ x) z)) hσ
  have hzker :
      Submodule.mkQ (R₀ ∙ x) (z - σ (Submodule.mkQ (R₀ ∙ x) z)) = 0 := by
    -- The correction term is exactly the difference of two representatives of the same quotient
    -- class.
    calc
      Submodule.mkQ (R₀ ∙ x) (z - σ (Submodule.mkQ (R₀ ∙ x) z)) =
          Submodule.mkQ (R₀ ∙ x) z -
            Submodule.mkQ (R₀ ∙ x) (σ (Submodule.mkQ (R₀ ∙ x) z)) := by
              rw [LinearMap.map_sub]
      _ = 0 := by rw [hσ_apply, sub_self]
  -- Rewrite vanishing in the quotient as membership in the cyclic span.
  have hmem :
      z - σ (Submodule.mkQ (R₀ ∙ x) z) ∈ LinearMap.ker (Submodule.mkQ (R₀ ∙ x)) :=
    (LinearMap.mem_ker).2 hzker
  simpa [ker_mkQ_span_singleton_eq (R₀ := R₀) (M₀ := M₀) x] using hmem

/-- Helper for Lemma 15.125.3: the backward map records the corrected cyclic part together with
the quotient coordinate. -/
noncomputable def module_prod_backward_of_mkQ_section
    {R₀ : Type u} [Ring R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    (x : M₀) (σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀)
    (hσ : (Submodule.mkQ (R₀ ∙ x)).comp σ = LinearMap.id) :
    M₀ →ₗ[R₀] ((R₀ ∙ x) × (M₀ ⧸ (R₀ ∙ x))) :=
  LinearMap.prod
    (LinearMap.codRestrict (R₀ ∙ x)
      (LinearMap.id - σ.comp (Submodule.mkQ (R₀ ∙ x)))
      (sub_section_mem_span_singleton_of_mkQ_section
        (R₀ := R₀) (M₀ := M₀) x σ hσ))
    (Submodule.mkQ (R₀ ∙ x))

/-- Helper for Lemma 15.125.3: the forward map adds the cyclic component back to the chosen
section of the quotient coordinate. -/
noncomputable def module_prod_forward_of_mkQ_section
    {R₀ : Type u} [Ring R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    (x : M₀) (σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀) :
    ((R₀ ∙ x) × (M₀ ⧸ (R₀ ∙ x))) →ₗ[R₀] M₀ :=
  LinearMap.coprod (R₀ ∙ x).subtype σ

/-- Helper for Lemma 15.125.3: correcting a point and then adding back its section recovers the
original point. -/
theorem module_prod_forward_comp_backward_of_mkQ_section
    {R₀ : Type u} [Ring R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    (x : M₀) (σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀)
    (hσ : (Submodule.mkQ (R₀ ∙ x)).comp σ = LinearMap.id) :
    (module_prod_forward_of_mkQ_section (R₀ := R₀) (M₀ := M₀) x σ).comp
        (module_prod_backward_of_mkQ_section (R₀ := R₀) (M₀ := M₀) x σ hσ) =
      LinearMap.id := by
  apply DFunLike.ext
  intro z
  -- The corrected cyclic part and the chosen section term recombine to `z`.
  simp [module_prod_forward_of_mkQ_section, module_prod_backward_of_mkQ_section,
    sub_eq_add_neg, add_assoc]

/-- Helper for Lemma 15.125.3: decomposing a split pair and then correcting it returns the
original cyclic and quotient coordinates. -/
theorem module_prod_backward_comp_forward_of_mkQ_section
    {R₀ : Type u} [Ring R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    (x : M₀) (σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀)
    (hσ : (Submodule.mkQ (R₀ ∙ x)).comp σ = LinearMap.id) :
    (module_prod_backward_of_mkQ_section (R₀ := R₀) (M₀ := M₀) x σ hσ).comp
        (module_prod_forward_of_mkQ_section (R₀ := R₀) (M₀ := M₀) x σ) =
      LinearMap.id := by
  apply DFunLike.ext
  intro p
  -- Compare the cyclic and quotient coordinates separately.
  apply Prod.ext
  · apply Subtype.ext
    change
      ((module_prod_backward_of_mkQ_section (R₀ := R₀) (M₀ := M₀) x σ hσ)
        ((module_prod_forward_of_mkQ_section (R₀ := R₀) (M₀ := M₀) x σ) p)).1.1 =
        p.1.1
    have hpker : Submodule.mkQ (R₀ ∙ x) p.1.1 = 0 := by
      -- Elements of the cyclic summand vanish in the quotient.
      simpa using p.1.2
    have hσ_apply :
        Submodule.mkQ (R₀ ∙ x) (σ p.2) = p.2 := by
      -- Evaluate the section identity at the quotient coordinate of `p`.
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀ ⧸ (R₀ ∙ x) ↦ f p.2) hσ
    have hsum :
        Submodule.mkQ (R₀ ∙ x) (p.1.1 + σ p.2) = p.2 := by
      -- The quotient forgets the cyclic coordinate and remembers the chosen section coordinate.
      rw [LinearMap.map_add, hpker, hσ_apply, zero_add]
    -- After rewriting the quotient coordinate, the remaining term is `p.1.1 + σ p.2 - σ p.2`.
    change p.1.1 + σ p.2 - σ (Submodule.mkQ (R₀ ∙ x) (p.1.1 + σ p.2)) = p.1.1
    rw [hsum]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · change
      Submodule.mkQ (R₀ ∙ x) p.1.1 + Submodule.mkQ (R₀ ∙ x) (σ p.2) = p.2
    have hpker : Submodule.mkQ (R₀ ∙ x) p.1.1 = 0 := by
      -- The cyclic coordinate is killed by the quotient map.
      simpa using p.1.2
    have hσ_apply :
        Submodule.mkQ (R₀ ∙ x) (σ p.2) = p.2 := by
      -- The section recovers the prescribed quotient coordinate.
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀ ⧸ (R₀ ∙ x) ↦ f p.2) hσ
    -- The quotient kills the cyclic coordinate and keeps the section coordinate.
    rw [hpker, hσ_apply, zero_add]

/-- Helper for Lemma 15.125.3: a section of the quotient map `M → M / (R ∙ x)` splits `M` as the
product of the cyclic span and the quotient. -/
noncomputable def module_linearEquiv_prod_span_singleton_quotient_of_mkQ_section
    {R₀ : Type u} [Ring R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    (x : M₀) (σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀)
    (hσ : (Submodule.mkQ (R₀ ∙ x)).comp σ = LinearMap.id) :
    M₀ ≃ₗ[R₀] ((R₀ ∙ x) × (M₀ ⧸ (R₀ ∙ x))) :=
  -- Package the explicit forward/backward split maps into a linear equivalence.
  LinearEquiv.ofLinear
    (module_prod_backward_of_mkQ_section (R₀ := R₀) (M₀ := M₀) x σ hσ)
    (module_prod_forward_of_mkQ_section (R₀ := R₀) (M₀ := M₀) x σ)
    (module_prod_backward_comp_forward_of_mkQ_section
      (R₀ := R₀) (M₀ := M₀) x σ hσ)
    (module_prod_forward_comp_backward_of_mkQ_section
      (R₀ := R₀) (M₀ := M₀) x σ hσ)

/-- Helper for Lemma 15.125.3: a finitely presented cyclic submodule over a Bézout ring is a
principal quotient. -/
lemma cyclic_factor_linearEquiv_principal_quotient_of_finitePresentation
    {R₀ : Type u} [CommRing R₀] [IsBezout R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    (x : M₀) [Module.FinitePresentation R₀ (R₀ ∙ x)] :
    ∃ f : R₀, Nonempty ((R₀ ∙ x) ≃ₗ[R₀] R₀ ⧸ principalIdeal f) := by
  let hmem : ∀ r : R₀, LinearMap.toSpanSingleton R₀ M₀ x r ∈ R₀ ∙ x := fun r ↦ by
    -- The codomain restriction records that the singleton-span map really lands in the cyclic
    -- submodule generated by `x`.
    rw [LinearMap.toSpanSingleton_apply, Submodule.mem_span_singleton]
    exact ⟨r, rfl⟩
  let toSpan : R₀ →ₗ[R₀] R₀ ∙ x :=
    LinearMap.codRestrict (R₀ ∙ x) (LinearMap.toSpanSingleton R₀ M₀ x) hmem
  have hsurj : Function.Surjective toSpan := by
    -- Every vector in the cyclic span is, by definition, the image of some scalar.
    intro y
    rcases Submodule.mem_span_singleton.mp y.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa [toSpan, hmem, LinearMap.toSpanSingleton_apply] using ha
  have hfg : toSpan.ker.FG := Module.FinitePresentation.fg_ker toSpan hsurj
  letI : toSpan.ker.IsPrincipal := IsBezout.isPrincipal_of_FG toSpan.ker hfg
  obtain ⟨f, hf⟩ := Submodule.IsPrincipal.principal toSpan.ker
  refine ⟨f, ?_⟩
  let eQuot := LinearMap.quotKerEquivOfSurjective toSpan hsurj
  have hker : toSpan.ker = (principalIdeal f : Submodule R₀ R₀) := by
    -- The Bézout hypothesis turns the kernel ideal of the cyclic presentation into a principal
    -- ideal generated by one scalar.
    simpa [principalIdeal] using hf
  let eIdeal := Submodule.quotEquivOfEq toSpan.ker (principalIdeal f) hker
  exact ⟨eQuot.symm.trans eIdeal⟩

/-- Helper for Lemma 15.125.3: separating the distinguished summand rewrites a product with the
remaining direct sum as a single direct sum indexed by `Option`. -/
noncomputable def directSum_fin_succ_linearEquiv
    {R₀ : Type u} [Semiring R₀] {n : ℕ}
    {α : Option (Fin n) → Type*} [∀ o, AddCommMonoid (α o)] [∀ o, Module R₀ (α o)] :
    (α none × ⨁ i : Fin n, α (some i)) ≃ₗ[R₀] ⨁ o : Option (Fin n), α o :=
  -- The direct-sum API already splits off the `none` summand as a product.
  (@DirectSum.lequivProdDirectSum R₀ _ _ α _ _).symm

/-- Helper for Lemma 15.125.3: if the quotient by a cyclic span already decomposes as a finite
direct sum of principal quotients and the cyclic inclusion is principal-pure, then the quotient
map admits a linear section. -/
lemma quotient_mkQ_has_section_of_principalPure_of_directSum_principal_quotients
    {R₀ : Type u} [CommRing R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    {x : M₀}
    (hpure : LinearMap.IsPrincipalPure ((R₀ ∙ x).subtype))
    (hdecomp : ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty ((M₀ ⧸ (R₀ ∙ x)) ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i))) :
    ∃ σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀,
      (Submodule.mkQ (R₀ ∙ x)).comp σ = LinearMap.id := by
  classical
  obtain ⟨n, f, ⟨e⟩⟩ := hdecomp
  let S : CategoryTheory.ShortComplex (ModuleCat.{v} R₀) :=
    CategoryTheory.ShortComplex.moduleCatMk
      ((R₀ ∙ x).subtype)
      (Submodule.mkQ (R₀ ∙ x))
      <| by
        -- This is the standard quotient row.
        ext z
        simpa using z.2
  have hS : S.ShortExact := by
    -- The quotient row is short exact with the usual `subtype`/`mkQ` witnesses.
    refine ModuleCat.shortComplex_shortExact S ?_ ?_ ?_
    · simpa using LinearMap.exact_subtype_mkQ (R₀ ∙ x)
    · exact Submodule.injective_subtype (R₀ ∙ x)
    · simpa using Submodule.mkQ_surjective (R₀ ∙ x)
  have hPureS : LinearMap.IsPrincipalPure S.f.hom := by
    -- The short complex uses exactly the given principal-pure cyclic inclusion.
    simpa [S] using hpure
  obtain ⟨τ, hτ⟩ :=
    surjective_compRight_directSum_of_principal_quotients
      (R := R₀) f hS hPureS e.symm.toLinearMap
  let σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀ := τ.comp e.toLinearMap
  -- Apply surjectivity to the identity of the quotient to obtain the desired section.
  refine ⟨σ, ?_⟩
  have hτ' : S.g.hom.comp τ = e.symm.toLinearMap := by
    simpa [LinearMap.compRight_apply] using hτ
  apply LinearMap.ext
  intro z
  have hz := congrArg (fun φ : (⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) →ₗ[R₀] S.X₃ ↦
      φ (e z)) hτ'
  simpa [S, σ, LinearMap.comp_assoc] using hz.trans (e.symm_apply_apply z)

/-- Helper for Lemma 15.125.3: once the quotient row by a cyclic span splits and both factors
already have principal-quotient decompositions, the ambient module inherits such a decomposition
by reassembling the split product and reindexing by `Fin (n + 1)`. -/
lemma exists_linearEquiv_directSum_principal_quotients_of_mkQ_section
    {R₀ : Type u} [CommRing R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    {x : M₀}
    (σ : (M₀ ⧸ (R₀ ∙ x)) →ₗ[R₀] M₀)
    (hσ : (Submodule.mkQ (R₀ ∙ x)).comp σ = LinearMap.id)
    (hcyc : ∃ g : R₀, Nonempty ((R₀ ∙ x) ≃ₗ[R₀] R₀ ⧸ principalIdeal g))
    (hquot : ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty ((M₀ ⧸ (R₀ ∙ x)) ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i))) :
    ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty (M₀ ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) := by
  obtain ⟨g, ⟨ecyc⟩⟩ := hcyc
  obtain ⟨n, f, ⟨equot⟩⟩ := hquot
  let α : Option (Fin n) → Type _ := fun o ↦
    R₀ ⧸ principalIdeal (Option.elim o g f)
  let eSplit :
      M₀ ≃ₗ[R₀] ((R₀ ∙ x) × (M₀ ⧸ (R₀ ∙ x))) :=
    module_linearEquiv_prod_span_singleton_quotient_of_mkQ_section
      (R₀ := R₀) (M₀ := M₀) x σ hσ
  let eFactors :
      ((R₀ ∙ x) × (M₀ ⧸ (R₀ ∙ x))) ≃ₗ[R₀] (α none × ⨁ i : Fin n, α (some i)) :=
    -- Replace the two split factors by their known principal-quotient presentations.
    LinearEquiv.prodCongr ecyc equot
  let eDirect :
      (α none × ⨁ i : Fin n, α (some i)) ≃ₗ[R₀] ⨁ o : Option (Fin n), α o :=
    -- The source proof next rewrites the product as a direct sum with one distinguished index.
    directSum_fin_succ_linearEquiv (R₀ := R₀) (n := n) (α := α)
  let eReindex :
      (⨁ o : Option (Fin n), α o) ≃ₗ[R₀] ⨁ i : Fin (n + 1), α (finSuccEquiv n i) := by
    -- Finally reindex `Option (Fin n)` by the standard `Fin (n + 1)` equivalence.
    simpa using
      (DirectSum.lequivCongrLeft R₀ ((finSuccEquiv n).symm) :
        (⨁ o : Option (Fin n), α o) ≃ₗ[R₀]
          ⨁ i : Fin (n + 1), α (((finSuccEquiv n).symm).symm i))
  refine ⟨n + 1, fun i ↦ Option.elim (finSuccEquiv n i) g f, ?_⟩
  -- Compose the split equivalence with the factor presentations and the final reindexing.
  exact ⟨eSplit.trans (eFactors.trans (eDirect.trans eReindex))⟩

section LocalBezoutInduction

variable {R₀ : Type u} [CommRing R₀] [Nontrivial R₀] [IsLocalRing R₀] [IsBezout R₀]

local notation "𝔪" => IsLocalRing.maximalIdeal R₀
local notation "κ" => IsLocalRing.ResidueField R₀

local instance residue_quotient_module
    {P : Type v} [AddCommGroup P] [Module R₀ P] :
    Module κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) :=
  inferInstanceAs (Module (R₀ ⧸ 𝔪) (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))))

local instance residue_quotient_smulCommClass
    {P : Type v} [AddCommGroup P] [Module R₀ P] :
    SMulCommClass R₀ κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) :=
  inferInstanceAs (SMulCommClass R₀ (R₀ ⧸ 𝔪) (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))))

local instance residue_quotient_isScalarTower
    {P : Type v} [AddCommGroup P] [Module R₀ P] :
    IsScalarTower R₀ κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) :=
  inferInstanceAs (IsScalarTower R₀ (R₀ ⧸ 𝔪) (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))))

omit [Nontrivial R₀] [IsBezout R₀] in
/-- Helper for Lemma 15.125.3: residue-space dimension `0` forces the module itself to be
subsingleton, hence an empty direct sum of principal quotients. -/
lemma exists_linearEquiv_directSum_principal_quotients_of_local_bezout_base_of_residue_finrank_zero
    {P : Type v} [AddCommGroup P] [Module R₀ P] [Module.FinitePresentation R₀ P]
    (hfin :
      Module.finrank κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) = 0) :
    ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty (P ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) := by
  letI : Module.Finite R₀ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) :=
    Module.Finite.quotient R₀ (𝔪 • (⊤ : Submodule R₀ P))
  letI : Module.Finite κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) :=
    Module.Finite.of_restrictScalars_finite R₀ κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P)))
  have hsubbar : Subsingleton (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) := by
    -- Zero residue-space dimension is equivalent to the quotient being subsingleton.
    exact (Module.finrank_eq_zero_iff_of_free κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P)))).mp hfin
  have hsub : Subsingleton P :=
    subsingleton_of_subsingleton_maximalIdeal_smul_quotient
      (R := R₀) (M := P) hsubbar
  -- Once Nakayama collapses the module, the source base case is the empty direct sum.
  letI : Subsingleton P := hsub
  exact
    exists_linearEquiv_directSum_principal_quotients_of_subsingleton_module
      (R₀ := R₀) (M₀ := P)

omit [Nontrivial R₀] in
/-- Helper for Lemma 15.125.3: once the cyclic lift has module annihilator and the quotient by its
span already decomposes, principal-purity splits off that cyclic factor and reassembles the full
module decomposition. -/
lemma exists_linearEquiv_directSum_principal_quotients_step_of_residue_lift
    {P : Type v} [AddCommGroup P] [Module R₀ P] [Module.FinitePresentation R₀ P]
    (x : P)
    (_hx : Submodule.mkQ (𝔪 • (⊤ : Submodule R₀ P)) x ≠ 0)
    (hxann : ∀ z : P,
      Submodule.mkQ (𝔪 • (⊤ : Submodule R₀ P)) z =
          Submodule.mkQ (𝔪 • (⊤ : Submodule R₀ P)) x →
        Module.annihilator R₀ P = Submodule.annihilator (R₀ ∙ z))
    (hquot : ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty ((P ⧸ (R₀ ∙ x)) ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i))) :
    ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty (P ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) := by
  have hpure : LinearMap.IsPrincipalPure ((R₀ ∙ x).subtype) := by
    -- The annihilator selector from the source proof is exactly the principal-purity hypothesis.
    exact
      span_singleton_subtype_isPrincipalPure_of_lift_annihilator_eq_module_annihilator
        (R := R₀) (M := P) hxann
  obtain ⟨σ, hσ⟩ :=
    quotient_mkQ_has_section_of_principalPure_of_directSum_principal_quotients
      (R₀ := R₀) (M₀ := P) (x := x) hpure hquot
  letI : Module.FinitePresentation R₀ (R₀ ∙ x) :=
    Module.finitePresentation_of_split_exact
      ((R₀ ∙ x).subtype)
      (Submodule.mkQ (R₀ ∙ x))
      σ
      hσ
      (Submodule.injective_subtype (R₀ ∙ x))
      (LinearMap.exact_subtype_mkQ (R₀ ∙ x))
  obtain ⟨g, hg⟩ :=
    cyclic_factor_linearEquiv_principal_quotient_of_finitePresentation
      (R₀ := R₀) (x := x)
  -- The split quotient row now matches the previously built reassembly lemma.
  exact
    exists_linearEquiv_directSum_principal_quotients_of_mkQ_section
      (R₀ := R₀) (M₀ := P) (x := x) σ hσ ⟨g, hg⟩ hquot

omit [Nontrivial R₀] [IsBezout R₀] in
/-- Helper for Lemma 15.125.3: the strong-induction hypothesis can be specialized directly to any
smaller residue-space dimension. -/
lemma exists_linearEquiv_directSum_principal_quotients_of_local_bezout_of_residue_finrank_lt
    {n : ℕ}
    (ih :
      ∀ k < n, ∀ {Q : Type v} [AddCommGroup Q] [Module R₀ Q] [Module.FinitePresentation R₀ Q],
        Module.finrank κ (Q ⧸ (𝔪 • (⊤ : Submodule R₀ Q))) = k →
          ∃ (m : ℕ) (f : Fin m → R₀),
            Nonempty (Q ≃ₗ[R₀] ⨁ i : Fin m, R₀ ⧸ principalIdeal (f i)))
    {Q : Type v} [AddCommGroup Q] [Module R₀ Q] [Module.FinitePresentation R₀ Q]
    (hfinlt : Module.finrank κ (Q ⧸ (𝔪 • (⊤ : Submodule R₀ Q))) < n) :
    ∃ (m : ℕ) (f : Fin m → R₀),
      Nonempty (Q ≃ₗ[R₀] ⨁ i : Fin m, R₀ ⧸ principalIdeal (f i)) := by
  -- Specialize the strong-induction hypothesis at the actual residue-space dimension of `Q`.
  exact ih _ hfinlt rfl

/-- Helper for Lemma 15.125.3: the positive `m + 1` branch of the residue-dimension induction
chooses a distinguished residue basis vector, recurses on the quotient by one lift, and then
reassembles the cyclic factor. -/
lemma exists_linearEquiv_directSum_principal_quotients_positive_branch_of_residue_finrank_succ
    {P : Type v} [AddCommGroup P] [Module R₀ P] [Module.FinitePresentation R₀ P]
    (m : ℕ)
    (hfin :
      Module.finrank κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) = m + 1)
    (hrec :
      ∀ {Q : Type v} [AddCommGroup Q] [Module R₀ Q] [Module.FinitePresentation R₀ Q],
        Module.finrank κ (Q ⧸ (𝔪 • (⊤ : Submodule R₀ Q))) < m + 1 →
          ∃ (n : ℕ) (f : Fin n → R₀),
            Nonempty (Q ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i))) :
    ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty (P ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) := by
  let Pbar : Type v := P ⧸ (𝔪 • (⊤ : Submodule R₀ P))
  letI : Module.Finite R₀ Pbar := Module.Finite.quotient R₀ (𝔪 • (⊤ : Submodule R₀ P))
  letI : Module.Finite κ Pbar := Module.Finite.of_restrictScalars_finite R₀ κ Pbar
  letI : PreValuationRing R₀ :=
    PreValuationRing.iff_ideal_total.mpr (ideal_total_of_isLocalRing_isBezout (R := R₀))
  let b : Module.Basis (Fin (m + 1)) κ Pbar := Module.finBasisOfFinrankEq κ Pbar hfin
  obtain ⟨i₀, hi₀⟩ :=
    exists_basis_index_with_module_annihilator_for_all_lifts
      (R := R₀) (M := P) b
  obtain ⟨x, hxlift⟩ :=
    Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R₀ P)) (b i₀)
  have hx :
      Submodule.mkQ (𝔪 • (⊤ : Submodule R₀ P)) x ≠ 0 := by
    -- A basis vector in the residue module is nonzero, so any chosen lift has nonzero residue.
    simpa [hxlift] using b.ne_zero i₀
  have hxann : ∀ z : P,
      Submodule.mkQ (𝔪 • (⊤ : Submodule R₀ P)) z =
          Submodule.mkQ (𝔪 • (⊤ : Submodule R₀ P)) x →
        Module.annihilator R₀ P = Submodule.annihilator (R₀ ∙ z) := by
    intro z hz
    -- The selector property obtained from the chosen basis index applies to every lift of `b i₀`.
    exact hi₀ z (hz.trans hxlift)
  letI : Module.FinitePresentation R₀ (P ⧸ (R₀ ∙ x)) :=
    quotient_span_singleton_finitePresentation (R₀ := R₀) (M₀ := P) x
  have hlt :
      Module.finrank κ
          ((P ⧸ (R₀ ∙ x)) ⧸ (𝔪 • (⊤ : Submodule R₀ (P ⧸ (R₀ ∙ x))))) <
        m + 1 := by
    -- Quotienting by the span of a lift of a nonzero residue class strictly lowers residue
    -- dimension.
    simpa [hfin] using residue_finrank_lt_of_nonzero_lift (R := R₀) (M := P) hx
  have hquot :
      ∃ (n : ℕ) (f : Fin n → R₀),
        Nonempty ((P ⧸ (R₀ ∙ x)) ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) :=
    hrec (Q := P ⧸ (R₀ ∙ x)) hlt
  -- Route correction: the source proof's whole successor step is now isolated in one lemma,
  -- leaving the outer strong induction to dispatch only between `0` and `m + 1`.
  exact
    exists_linearEquiv_directSum_principal_quotients_step_of_residue_lift
      (R₀ := R₀) (P := P) x hx hxann hquot

/-- Helper for Lemma 15.125.3: strong induction on the residue-field dimension gives the full
decomposition theorem for arbitrary finitely presented modules over a local Bézout ring. -/
lemma exists_linearEquiv_directSum_principal_quotients_of_local_bezout_aux
    (n : ℕ) :
    ∀ {P : Type v} [AddCommGroup P] [Module R₀ P] [Module.FinitePresentation R₀ P],
      Module.finrank κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) = n →
        ∃ (m : ℕ) (f : Fin m → R₀),
          Nonempty (P ≃ₗ[R₀] ⨁ i : Fin m, R₀ ⧸ principalIdeal (f i)) := by
  -- Route correction: package the strong induction in a separate auxiliary so the induction
  -- motive still quantifies over arbitrary finitely presented modules.
  let haux :
      ∀ n : ℕ, ∀ {P : Type v} [AddCommGroup P] [Module R₀ P] [Module.FinitePresentation R₀ P],
        Module.finrank κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) = n →
          ∃ (m : ℕ) (f : Fin m → R₀),
            Nonempty (P ≃ₗ[R₀] ⨁ i : Fin m, R₀ ⧸ principalIdeal (f i)) := by
    intro n
    refine Nat.strong_induction_on n
      (motive := fun n =>
        ∀ {P : Type v} [AddCommGroup P] [Module R₀ P] [Module.FinitePresentation R₀ P],
          Module.finrank κ (P ⧸ (𝔪 • (⊤ : Submodule R₀ P))) = n →
            ∃ (m : ℕ) (f : Fin m → R₀),
              Nonempty (P ≃ₗ[R₀] ⨁ i : Fin m, R₀ ⧸ principalIdeal (f i))) ?_
    intro n ih P _ _ _ hfin
    by_cases hzero : n = 0
    · subst n
      -- The base case is exactly the zero-dimensional residue-space case from the source proof.
      exact
        exists_linearEquiv_directSum_principal_quotients_of_local_bezout_base_of_residue_finrank_zero
          (R₀ := R₀) (P := P) hfin
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hrec :
          ∀ {Q : Type v} [AddCommGroup Q] [Module R₀ Q] [Module.FinitePresentation R₀ Q],
            Module.finrank κ (Q ⧸ (𝔪 • (⊤ : Submodule R₀ Q))) < m + 1 →
              ∃ (n : ℕ) (f : Fin n → R₀),
                Nonempty (Q ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) := by
        intro Q _ _ _ hlt
        -- Package the strong-induction hypothesis so the recursive quotient call no longer needs
        -- to manipulate the Nat index explicitly.
        exact
          exists_linearEquiv_directSum_principal_quotients_of_local_bezout_of_residue_finrank_lt
            (R₀ := R₀) (n := m + 1) (ih := ih) (Q := Q) hlt
      -- The positive branch now follows the source proof verbatim: pick a distinguished residue
      -- basis vector, recurse on the quotient by a lift, and split off the cyclic factor.
      exact
        exists_linearEquiv_directSum_principal_quotients_positive_branch_of_residue_finrank_succ
          (R₀ := R₀) (P := P) m hfin hrec
  exact haux n

end LocalBezoutInduction

/-- Helper for Lemma 15.125.3: over a nontrivial local Bézout ring, every finitely presented
module decomposes as a finite direct sum of principal quotient modules. -/
lemma exists_linearEquiv_directSum_principal_quotients_of_local_bezout
    {R₀ : Type u} [CommRing R₀] [Nontrivial R₀] [IsLocalRing R₀] [IsBezout R₀]
    {N : Type v} [AddCommGroup N] [Module R₀ N] [Module.FinitePresentation R₀ N] :
    ∃ (n : ℕ) (f : Fin n → R₀),
      Nonempty (N ≃ₗ[R₀] ⨁ i : Fin n, R₀ ⧸ principalIdeal (f i)) := by
  letI : Module (IsLocalRing.ResidueField R₀)
      (N ⧸ (IsLocalRing.maximalIdeal R₀ • (⊤ : Submodule R₀ N))) :=
    inferInstanceAs
      (Module (R₀ ⧸ IsLocalRing.maximalIdeal R₀)
        (N ⧸ (IsLocalRing.maximalIdeal R₀ • (⊤ : Submodule R₀ N))))
  -- Route correction: the recursive parameter must quantify over arbitrary finitely presented
  -- modules so that the induction hypothesis can be applied to `N ⧸ (R₀ ∙ x)`.
  exact
    exists_linearEquiv_directSum_principal_quotients_of_local_bezout_aux
      (R₀ := R₀)
      (n := Module.finrank (IsLocalRing.ResidueField R₀)
        (N ⧸ (IsLocalRing.maximalIdeal R₀ • (⊤ : Submodule R₀ N))))
      (P := N)
      rfl

-- Proof sketch: if `R` is subsingleton, then every `R`-module is subsingleton, so one may take
-- `n = 0` and the unique linear equivalence to the empty direct sum. Otherwise, argue by induction
-- on the dimension of `M / maximalIdeal R • ⊤` over the residue field of the local ring coming
-- from `PreValuationRing R`. Choose a lift whose annihilator is the annihilator of `M`, split off
-- the corresponding cyclic summand using the principal-pure lifting criterion of
-- Lemma `15.125.1`, and conclude that the resulting annihilator ideal is principal because `M` is
-- finitely presented.
/-- Lemma 15.125.3: if `R` is a generalized valuation ring in the canonical sense
`PreValuationRing R`, then every finitely presented `R`-module is linearly isomorphic to a finite
direct sum of principal quotient modules `R ⧸ (fᵢ)`. -/
theorem finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients :
    ∃ (n : ℕ) (f : Fin n → R),
      Nonempty (M ≃ₗ[R] ⨁ i : Fin n, R ⧸ principalIdeal (f i)) := by
  classical
  by_cases hR : Subsingleton R
  · letI : Subsingleton R := hR
    -- The degenerate ring case is the empty decomposition proved above.
    exact exists_linearEquiv_directSum_principal_quotients_of_subsingleton (R₀ := R) (M₀ := M)
  · letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
    let hlocalBezout :=
      generalized_valuation_ring_isLocalRing_and_isBezout (R₀ := R)
    letI : IsLocalRing R := hlocalBezout.1
    letI : IsBezout R := hlocalBezout.2
    -- With the generalized valuation-ring structure installed as local Bézout data, the theorem
    -- reduces to the source-faithful local induction helper.
    exact
      exists_linearEquiv_directSum_principal_quotients_of_local_bezout
        (R₀ := R) (N := M)

end
