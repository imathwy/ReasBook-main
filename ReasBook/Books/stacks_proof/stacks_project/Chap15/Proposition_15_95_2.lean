import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap15.«15_74_0_2»
import stacks_proof.stacks_project.Chap15.Lemma_15_92_18
import stacks_proof.stacks_project.Chap15.Lemma_15_95_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open SequentialInverseSystem
open SequentialProObjectMorphismRep
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The `n`th quotient stage `(A / I^(n+1))[0]` in the ideal-power completion tower. -/
abbrev idealPowerQuotientDerivedStage (I : Ideal A) (n : ℕ) : DMod :=
  (single0).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))

/-- The transition morphism `(A / I^(n+2))[0] ⟶ (A / I^(n+1))[0]` in the ideal-power quotient
tower. -/
abbrev idealPowerQuotientDerivedStep (I : Ideal A) (n : ℕ) :
    idealPowerQuotientDerivedStage I (n + 1) ⟶
      idealPowerQuotientDerivedStage I n :=
  (single0).map
    (ModuleCat.ofHom
      ((Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap))

/-- The inverse system `((A / I^(n+1))[0])_n` in `D(A)`. -/
abbrev idealPowerQuotientDerivedInverseSystem (I : Ideal A) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerQuotientDerivedStep I)

/-- The inverse system `(K \otimes_A^{\mathbf L} (A / I^(n+1))[0])_n` used in derived completion
by the powers of `I`. -/
abbrev idealPowerQuotientTensorDerivedInverseSystem
    (I : Ideal A) (K : DMod) : ℕᵒᵖ ⥤ DMod :=
  idealPowerQuotientDerivedInverseSystem I ⋙ derivedTensorProduct K

/-- The canonical map from `K` to the `n`th quotient-tensor stage
`K \otimes_A^{\mathbf L} (A / I^(n+1))[0]`. -/
abbrev idealPowerQuotientTensorToStage
    (I : Ideal A) (K : DMod) (n : ℕ) :
    K ⟶ (idealPowerQuotientTensorDerivedInverseSystem I K).obj (op n) :=
  (singleZeroDerivedTensorIso K).inv ≫
    (derivedTensorProduct K).map
      ((single0).map
        (ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (I ^ (n + 1))).toLinearMap)))

/-- A morphism `c : K ⟶ L` is the canonical comparison from `K` to a chosen derived limit of the
ideal-power quotient tensor tower if `L` sits in the Milnor triangle of that tower and the stage
projections recover the canonical quotient-stage maps
`K ⟶ K \otimes_A^{\mathbf L} (A / I^(n+1))[0]`. -/
def IsDerivedCompletionIdealPowerQuotientTensorComparison
    (I : Ideal A) (K L : DMod) (c : K ⟶ L) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)),
    ∃ ι :
        L ⟶ ∏ᶜ inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K),
      HasMilnorTriangle.WithMap (idealPowerQuotientTensorDerivedInverseSystem I K) ι ∧
        ∀ n : ℕ,
          c ≫ ι ≫
              Pi.π
                (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))
                n =
            idealPowerQuotientTensorToStage I K n

/-- A quotient-tower derived-completion comparison presents its target as a derived limit of the
ideal-power quotient tensor tower. -/
theorem IsDerivedCompletionIdealPowerQuotientTensorComparison.isDerivedLimit
    {I : Ideal A} {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionIdealPowerQuotientTensorComparison I K L c) :
    IsDerivedLimit (idealPowerQuotientTensorDerivedInverseSystem I K) L := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) := hP
  exact ⟨hP, hι.hasMilnorTriangle (idealPowerQuotientTensorDerivedInverseSystem I K)⟩

end

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Proposition 15.95.2:
- primary domain: derived completion in `D(A)` via the canonical comparison
  `K ⟶ R\!\varprojlim (K \otimes_A^{\mathbf L} (A / I^(n+1))[0])`;
- sampled owner declarations:
  `IsDerivedCompletionKoszulPowerTensorComparison`,
  `derivedLimitOfKoszulPowerTensorFunctorAdjunction`,
  `derivedCompleteObjectProperty`,
  `exists_pro_isomorphism_derived_completion_koszul_powers_to_power_quotients`;
- best owner abstraction: this proposition is a `bridge/view` statement. Its source-facing owner is
  the quotient-tower comparison predicate below, while the canonical target owner remains the
  adjunction with the inclusion of the full subcategory of derived-complete objects;
- primitive vs. derived:
  primitive data are the quotient tower, the functor `L`, the natural transformation `η`, and the
  fact that each `η.app K` is the canonical quotient-tower comparison map;
  the derived API is the induced adjunction `L ⊣ ι` and its consequence `L.IsLeftAdjoint`.

Source/core/bridge triage:
- `source-facing`: the quotient-tower comparison map formalizing
  `K ⟶ R\!\varprojlim (K \otimes_A^{\mathbf L} (A / I^(n+1))[0])`;
- `core/canonical`: `DerivedCategory.derivedCompleteObjectProperty I`, its inclusion functor, and
  `Adjunction`;
- `bridge/view`: the passage from the quotient-tower comparison to the powered-Koszul comparison of
  Lemma `15.92.18`, using the pro-isomorphism of Lemma `15.95.1`. -/

-- Proof sketch: choose generators `f` of `I`. Proposition `15.95.1` identifies the quotient
-- tower with the powered Koszul tower up to pro-isomorphism. Transport the supplied quotient-tower
-- comparison along this pro-isomorphism to obtain the owner predicate
-- `IsDerivedCompletionKoszulPowerTensorComparison f`, and then apply
-- `derivedLimitOfKoszulPowerTensorFunctorAdjunction`. The isomorphism criterion for objects
-- already derived complete is the corresponding quotient-tower reformulation of Lemma `15.92.17`.
/-- Helper for Proposition 15.95.2: a Noetherian ideal admits a finite generating family indexed by
`Fin r`, exactly in the span-range form used by the powered-Koszul comparison lemmas. -/
private theorem exists_span_range_eq_of_noetherian
    [IsNoetherianRing A] (I : Ideal A)
    : ∃ (r : ℕ) (f : Fin r → A), I = Ideal.span (Set.range f) := by
  classical
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  let f : Fin s.card → A := fun i ↦ (s.equivFin.symm i : A)
  refine ⟨s.card, f, ?_⟩
  rw [hs]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  · intro hx
    exact ⟨s.equivFin ⟨x, hx⟩, by simp [f]⟩

/-- Helper for Proposition 15.95.2: each stage ideal `(f_i^(n+1))` is contained in the
corresponding power `I^(n+1)` of the generated ideal. This gives the forward comparison from the
powered quotient tower to the ideal-power quotient tower. -/
private theorem koszulPowerIdeal_le_ideal_pow
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) (n : ℕ) :
    koszulPowerIdeal f n ≤ I ^ (n + 1) := by
  -- Proof comment: each generator `f i ^ (n+1)` lies in `I^(n+1)` because `f i ∈ I`, and the
  -- whole span follows by the universal property of `Ideal.span`.
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [hspan]
  exact Ideal.pow_mem_pow (Ideal.subset_span ⟨i, rfl⟩) (n + 1)

/-- Helper for Proposition 15.95.2: every generator of `I` lies in the radical of the stage ideal
`(f_i^(n+1))`, so `I` itself is contained in that radical. This is the source-faithful cofinality
input for the reverse pro-map. -/
private theorem ideal_le_radical_koszulPowerIdeal
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) (n : ℕ) :
    I ≤ Ideal.radical (koszulPowerIdeal f n) := by
  -- Proof comment: a generator `f i` becomes radical because its `(n+1)`st power is literally one
  -- of the generators of `koszulPowerIdeal f n`; then extend from generators to the whole span.
  rw [hspan]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [Ideal.mem_radical]
  refine ⟨n + 1, ?_⟩
  exact Ideal.subset_span ⟨i, rfl⟩

/-- Helper for Proposition 15.95.2: for each fixed quotient stage `(f_i^(n+1))`, some power of
`I` is already contained in that stage ideal. This isolates the per-stage cofinality input needed
to build the reverse pro-object representative. -/
private theorem exists_ideal_pow_le_koszulPowerIdeal
    [IsNoetherianRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) (n : ℕ) :
    ∃ m : ℕ, I ^ m ≤ koszulPowerIdeal f n := by
  -- Proof comment: once `I ≤ radical (koszulPowerIdeal f n)`, the standard Noetherian radical
  -- criterion upgrades that radical containment to an actual containment of a high enough power.
  exact
    Ideal.exists_pow_le_of_le_radical_of_fg
      (ideal_le_radical_koszulPowerIdeal f I hspan n)
      I.fg_of_isNoetherianRing

/-- Helper for Proposition 15.95.2: the per-stage containments `I^m ≤ (f_i^(n+1))` can be chosen
monotonically in `n`, yielding a single cofinal reindex for the reverse sequential
representative. -/
private theorem ideal_power_reindex_le_koszulPowerIdeal
    [IsNoetherianRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) :
    ∃ σ : ℕ →o ℕ, ∀ n : ℕ, I ^ (σ n + 1) ≤ koszulPowerIdeal f n := by
  classical
  choose m hm using exists_ideal_pow_le_koszulPowerIdeal (f := f) (I := I) hspan
  let t : ℕ → ℕ :=
    Nat.rec (max 1 (m 0)) (fun n tn ↦ max tn (max 1 (m (n + 1))))
  have ht_pos : ∀ n : ℕ, 1 ≤ t n := by
    intro n
    induction n with
    | zero =>
        simp [t]
    | succ n ih =>
        simp [t, ih]
  have ht_mono : Monotone t := by
    intro a b hab
    induction hab with
    | refl =>
        rfl
    | @step b hab ih =>
        exact le_trans ih (le_max_left _ _)
  have ht_ge_stage : ∀ n k : ℕ, k ≤ n → max 1 (m k) ≤ t n := by
    intro n
    induction n with
    | zero =>
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        simp [t]
    | succ n ihn =>
        intro k hk
        rcases Nat.eq_or_lt_of_le hk with rfl | hklt
        · simp [t]
        · exact le_trans (ihn k (Nat.lt_succ_iff.mp hklt)) (le_max_left _ _)
  let σ : ℕ →o ℕ where
    toFun := fun n ↦ t n - 1
    monotone' := by
      intro a b hab
      exact Nat.sub_le_sub_right (ht_mono hab) 1
  refine ⟨σ, ?_⟩
  intro n
  have hm_le_t : m n ≤ t n := by
    exact le_trans (le_max_right 1 (m n)) (ht_ge_stage n n le_rfl)
  have hpow :
      I ^ (t n) ≤ I ^ (m n) := by
    exact Ideal.pow_le_pow_right hm_le_t
  calc
    I ^ (σ n + 1) = I ^ (t n) := by
      simp [σ, Nat.sub_add_cancel (ht_pos n)]
    _ ≤ I ^ (m n) := hpow
    _ ≤ koszulPowerIdeal f n := hm n

/-- Helper for Proposition 15.95.2: the cofinal reindex for the reverse quotient map can be
chosen to dominate the identity. This gives the common refinement needed later when comparing the
composite representatives with the identity tower maps. -/
private theorem ideal_power_reindex_ge_id_le_koszulPowerIdeal
    [IsNoetherianRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) :
    ∃ σ : ℕ →o ℕ, (∀ n : ℕ, n ≤ σ n) ∧ ∀ n : ℕ, I ^ (σ n + 1) ≤ koszulPowerIdeal f n := by
  obtain ⟨σ, hσ⟩ := ideal_power_reindex_le_koszulPowerIdeal (f := f) (I := I) hspan
  let τ : ℕ →o ℕ where
    toFun := fun n ↦ max n (σ n)
    monotone' := by
      intro a b hab
      exact max_le_max hab (σ.monotone hab)
  refine ⟨τ, ?_, ?_⟩
  · intro n
    exact le_max_left n (σ n)
  · intro n
    -- Proof comment: increasing the exponent only shrinks the ideal power, so the original
    -- containment survives after replacing `σ n` by `max n (σ n)`.
    calc
      I ^ (τ n + 1) ≤ I ^ (σ n + 1) := by
        exact Ideal.pow_le_pow_right (Nat.add_le_add_right (le_max_right n (σ n)) 1)
      _ ≤ koszulPowerIdeal f n := hσ n

/-- Helper for Proposition 15.95.2: the `n`th forward comparison map from the quotient by
`(f_i^(n+1))` to the quotient by `I^(n+1)`. This is the stagewise map in the source proof's
comparison from the powered quotient tower to the ideal-power quotient tower. -/
private abbrev powerQuotientToIdealPowerStageMap
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) (n : ℕ) :
    (derivedCompletionPowerQuotientDerivedInverseSystem f).obj (op n) ⟶
      (idealPowerQuotientDerivedInverseSystem I).obj (op n) :=
  (single0).map
    (ModuleCat.ofHom
      ((Ideal.Quotient.factorₐ A
          (koszulPowerIdeal_le_ideal_pow f I hspan n)).toLinearMap))

/-- Helper for Proposition 15.95.2: the forward quotient comparison commutes with the successive
tower maps. This is the source-faithful tower-level square asserting that the textbook quotient
comparison is compatible with passing from stage `n+1` to stage `n`. -/
private theorem powerQuotientToIdealPowerStageMap_naturality
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) (n : ℕ) :
    (derivedCompletionPowerQuotientDerivedInverseSystem f).map
        (homOfLE (Nat.le_succ n)).op ≫
      powerQuotientToIdealPowerStageMap f I hspan n =
        powerQuotientToIdealPowerStageMap f I hspan (n + 1) ≫
          (idealPowerQuotientDerivedInverseSystem I).map
            (homOfLE (Nat.le_succ n)).op := by
  -- Proof comment: both composites are the same quotient map from
  -- `A / (f_i^(n+2))` to `A / I^(n+1)`, written through the two evident intermediate quotients.
  refine congrArg (fun t ↦ (single0).map t) ?_
  ext x
  rcases Quotient.exists_rep x with ⟨a, rfl⟩
  rfl

/-- Helper for Proposition 15.95.2: the forward quotient comparison is a morphism of inverse
systems. This packages the textbook observation that
`A / (f_1^(n+1), \ldots, f_r^(n+1)) → A / I^(n+1)` is compatible with the transition maps. -/
private abbrev powerQuotientToIdealPowerNatTrans
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) :
    derivedCompletionPowerQuotientDerivedInverseSystem f ⟶
      idealPowerQuotientDerivedInverseSystem I :=
  NatTrans.ofOpSequence
    (fun n ↦ powerQuotientToIdealPowerStageMap f I hspan n)
    (fun n ↦ by
      simpa using powerQuotientToIdealPowerStageMap_naturality f I hspan n)

/-- Helper for Proposition 15.95.2: the powered quotient ideals form a decreasing sequence along
arbitrary index inequalities, not only across successive stages. This is the long-stage
containment needed for the reverse quotient representative. -/
private theorem koszulPowerIdeal_le_of_le
    {r : ℕ} (f : Fin r → A) {n m : ℕ} (h : n ≤ m) :
    koszulPowerIdeal f m ≤ koszulPowerIdeal f n := by
  -- Proof comment: write `m = n + k` and iterate the already-proved successive containment
  -- `koszulPowerIdeal_succ_le`.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
      simp
  | succ k ih =>
      exact le_trans (koszulPowerIdeal_succ_le f (n + k)) ih

/-- Helper for Proposition 15.95.2: the `n`th reverse comparison map from the quotient by
`I^(σ n + 1)` to the quotient by `(f_i^(n+1))`. This is the source-faithful reverse map whose
existence expresses the cofinality of the ideal-power tower inside the powered quotient tower. -/
private abbrev idealPowerQuotientToPowerQuotientStageMap
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (_hspan : I = Ideal.span (Set.range f))
    (σ : ℕ →o ℕ) (_hσid : ∀ n : ℕ, n ≤ σ n)
    (hσ : ∀ n : ℕ, I ^ (σ n + 1) ≤ koszulPowerIdeal f n) (n : ℕ) :
    ((σ.toFunctor.op ⋙ idealPowerQuotientDerivedInverseSystem I).obj (op n)) ⟶
      (derivedCompletionPowerQuotientDerivedInverseSystem f).obj (op n) :=
  (single0).map
    (ModuleCat.ofHom
      ((Ideal.Quotient.factorₐ A (hσ n)).toLinearMap))

/-- Helper for Proposition 15.95.2: the reverse quotient comparison also commutes with the tower
maps. This is the source-faithful square showing that the chosen cofinal reindex really gives a
morphism of inverse systems. -/
private theorem idealPowerQuotientToPowerQuotientStageMap_naturality
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f))
    (σ : ℕ →o ℕ) (hσid : ∀ n : ℕ, n ≤ σ n)
    (hσ : ∀ n : ℕ, I ^ (σ n + 1) ≤ koszulPowerIdeal f n) (n : ℕ) :
    ((σ.toFunctor.op ⋙ idealPowerQuotientDerivedInverseSystem I).map
        (homOfLE (Nat.le_succ n)).op) ≫
      idealPowerQuotientToPowerQuotientStageMap f I hspan σ hσid hσ n =
        idealPowerQuotientToPowerQuotientStageMap f I hspan σ hσid hσ (n + 1) ≫
          (derivedCompletionPowerQuotientDerivedInverseSystem f).map
            (homOfLE (Nat.le_succ n)).op := by
  -- Proof comment: both composites are the same quotient map from
  -- `A / I^(σ (n + 1) + 1)` to `A / (f_i^(n+1))`, written through the two evident intermediate
  -- quotients.
  refine congrArg (fun t ↦ (single0).map t) ?_
  ext x
  rcases Quotient.exists_rep x with ⟨a, rfl⟩
  rfl

/-- Helper for Proposition 15.95.2: the reverse quotient comparison assembles into a morphism of
inverse systems. -/
private abbrev idealPowerQuotientToPowerQuotientNatTrans
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f))
    (σ : ℕ →o ℕ) (hσid : ∀ n : ℕ, n ≤ σ n)
    (hσ : ∀ n : ℕ, I ^ (σ n + 1) ≤ koszulPowerIdeal f n) :
    (σ.toFunctor.op ⋙ idealPowerQuotientDerivedInverseSystem I) ⟶
      derivedCompletionPowerQuotientDerivedInverseSystem f :=
  NatTrans.ofOpSequence
    (fun n ↦ idealPowerQuotientToPowerQuotientStageMap f I hspan σ hσid hσ n)
    (fun n ↦ by
      simpa using
        idealPowerQuotientToPowerQuotientStageMap_naturality
          f I hspan σ hσid hσ n)

/-- Helper for Proposition 15.95.2: at stage `n`, the reverse quotient comparison followed by the
forward quotient comparison is exactly the direct quotient map
`A / I^(σ n + 1) → A / I^(n+1)`. -/
private theorem idealPower_reverse_forward_eq_stageFactor
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f))
    (σ : ℕ →o ℕ) (hσid : ∀ n : ℕ, n ≤ σ n)
    (hσ : ∀ n : ℕ, I ^ (σ n + 1) ≤ koszulPowerIdeal f n) (n : ℕ) :
    idealPowerQuotientToPowerQuotientStageMap f I hspan σ hσid hσ n ≫
        powerQuotientToIdealPowerStageMap f I hspan n =
      (single0).map
        (ModuleCat.ofHom
          ((Ideal.Quotient.factorₐ A
              (Ideal.pow_le_pow_right (Nat.add_le_add_right (hσid n) 1))).toLinearMap)) := by
  -- Proof comment: the two-stage route through the powered quotient is literally the same
  -- quotient-factor map as the direct passage from `I^(σ n + 1)` to `I^(n+1)`.
  refine congrArg (fun t ↦ (single0).map t) ?_
  ext x
  rcases Quotient.exists_rep x with ⟨a, rfl⟩
  rfl

/-- Helper for Proposition 15.95.2: the long transition map in the ideal-power quotient tower is
already the direct quotient-factor map between the two endpoint stages. -/
private theorem idealPowerQuotient_transition_eq_stageFactor
    {n m : ℕ} (I : Ideal A) (h : n ≤ m) :
    SequentialInverseSystem.transitionMap (idealPowerQuotientDerivedInverseSystem I) h =
      (single0).map
        (ModuleCat.ofHom
          ((Ideal.Quotient.factorₐ A
              (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).toLinearMap)) := by
  induction h with
  | refl =>
      -- Proof comment: at equal stages the transition map is the identity quotient map.
      simp [SequentialInverseSystem.transitionMap]
  | @step m h ih =>
      -- Proof comment: factor the long transition through stage `m`, rewrite the shorter piece by
      -- induction, and then identify the composite of quotient-factor maps with the direct one.
      rw [CategoryTheory.SequentialInverseSystem.transitionMap_factor
        (F := idealPowerQuotientDerivedInverseSystem I) h (Nat.le_succ m)]
      rw [ih]
      refine congrArg (fun t ↦ (single0).map t) ?_
      ext x
      rcases Quotient.exists_rep x with ⟨a, rfl⟩
      rfl

/-- Helper for Proposition 15.95.2: at stage `n`, the forward quotient comparison at stage
`σ n` followed by the reverse quotient comparison is exactly the direct quotient map
`A / (f_i^(σ n + 1)) → A / (f_i^(n+1))`. -/
private theorem powerQuotient_forward_reverse_eq_stageFactor
    {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f))
    (σ : ℕ →o ℕ) (hσid : ∀ n : ℕ, n ≤ σ n)
    (hσ : ∀ n : ℕ, I ^ (σ n + 1) ≤ koszulPowerIdeal f n) (n : ℕ) :
    powerQuotientToIdealPowerStageMap f I hspan (σ n) ≫
        idealPowerQuotientToPowerQuotientStageMap f I hspan σ hσid hσ n =
      (single0).map
        (ModuleCat.ofHom
          ((Ideal.Quotient.factorₐ A
              (koszulPowerIdeal_le_of_le f (hσid n))).toLinearMap)) := by
  -- Proof comment: after passing through the ideal-power quotient at stage `σ n`, the composite
  -- is still the direct quotient-factor map between the two powered quotient stages.
  refine congrArg (fun t ↦ (single0).map t) ?_
  ext x
  rcases Quotient.exists_rep x with ⟨a, rfl⟩
  rfl

/-- Helper for Proposition 15.95.2: the long transition map in the powered-quotient tower is
already the direct quotient-factor map between the two endpoint stages. -/
private theorem powerQuotient_transition_eq_stageFactor
    {r : ℕ} (f : Fin r → A) {n m : ℕ} (h : n ≤ m) :
    SequentialInverseSystem.transitionMap
        (derivedCompletionPowerQuotientDerivedInverseSystem f) h =
      (single0).map
        (ModuleCat.ofHom
          ((Ideal.Quotient.factorₐ A
              (koszulPowerIdeal_le_of_le f h)).toLinearMap)) := by
  induction h with
  | refl =>
      -- Proof comment: at equal stages the transition map is the identity quotient map.
      simp [SequentialInverseSystem.transitionMap]
  | @step m h ih =>
      -- Proof comment: factor the long transition through stage `m`, rewrite the shorter piece by
      -- induction, and then collapse the two quotient-factor maps to the direct one.
      rw [CategoryTheory.SequentialInverseSystem.transitionMap_factor
        (F := derivedCompletionPowerQuotientDerivedInverseSystem f) h (Nat.le_succ m)]
      rw [ih]
      refine congrArg (fun t ↦ (single0).map t) ?_
      ext x
      rcases Quotient.exists_rep x with ⟨a, rfl⟩
      rfl

/-- Helper for Proposition 15.95.2: the explicit quotient comparison from
`A / (f_1^(n+1), \ldots, f_r^(n+1))` to `A / I^(n+1)` is a representative-level pro-isomorphism. -/
private theorem powerQuotientToIdealPowerNatTrans_isProIsomorphism
    [IsNoetherianRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) :
    (SequentialProObjectMorphismRep.ofNatTrans
      (powerQuotientToIdealPowerNatTrans f I hspan)).IsProIsomorphism := by
  obtain ⟨σ, hσid, hσ⟩ :=
    ideal_power_reindex_ge_id_le_koszulPowerIdeal (f := f) (I := I) hspan
  let forwardRep :
      SequentialProObjectMorphismRep
        (derivedCompletionPowerQuotientDerivedInverseSystem f)
        (idealPowerQuotientDerivedInverseSystem I) :=
    SequentialProObjectMorphismRep.ofNatTrans (powerQuotientToIdealPowerNatTrans f I hspan)
  let reverseRep :
      SequentialProObjectMorphismRep
        (idealPowerQuotientDerivedInverseSystem I)
        (derivedCompletionPowerQuotientDerivedInverseSystem f) where
    reindex := σ
    hom := idealPowerQuotientToPowerQuotientNatTrans f I hspan σ hσid hσ
  let idealComp := SequentialProObjectMorphismRep.compRep reverseRep forwardRep
  let powerComp := SequentialProObjectMorphismRep.compRep forwardRep reverseRep
  refine ⟨reverseRep, ?_, ?_⟩
  · -- Proof comment: after refining to the reverse representative's reindex, the reverse-forward
    -- composite is exactly the ideal-power tower transition map.
    refine ⟨idealComp.reindex, fun n ↦ le_rfl, fun n ↦ ?_, ?_⟩
    · change n ≤ idealComp.reindex n
      simpa [idealComp, reverseRep, forwardRep, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofNatTrans] using hσid
    · intro n
      simpa [idealComp, reverseRep, forwardRep, SequentialInverseSystem.transitionMap] using
        (idealPower_reverse_forward_eq_stageFactor f I hspan σ hσid hσ n).trans
          (idealPowerQuotient_transition_eq_stageFactor I (hσid n)).symm
  · -- Proof comment: the symmetric composite is the corresponding powered-quotient transition
    -- map after the same common refinement.
    refine ⟨powerComp.reindex, fun n ↦ le_rfl, fun n ↦ ?_, ?_⟩
    · change n ≤ powerComp.reindex n
      simpa [powerComp, reverseRep, forwardRep, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofNatTrans] using hσid
    · intro n
      simpa [powerComp, reverseRep, forwardRep, SequentialInverseSystem.transitionMap] using
        (powerQuotient_forward_reverse_eq_stageFactor f I hspan σ hσid hσ n).trans
          (powerQuotient_transition_eq_stageFactor f (hσid n)).symm

/-- Helper for Proposition 15.95.2: applying a functor stagewise to a sequential representative
gives the induced representative between the whiskered towers. -/
private def mapRep
    {C D : Type*} [Category C] [Category D]
    {X Y : ℕᵒᵖ ⥤ C} (F : C ⥤ D) (r : SequentialProObjectMorphismRep X Y) :
    SequentialProObjectMorphismRep (X ⋙ F) (Y ⋙ F) where
  reindex := r.reindex
  hom := r.hom.whiskerRight F

/-- Helper for Proposition 15.95.2: common-refinement equivalence is preserved after applying a
functor stagewise to a sequential representative. -/
private theorem equivalent_mapRep
    {C D : Type*} [Category C] [Category D]
    {X Y : ℕᵒᵖ ⥤ C}
    {r₁ r₂ : SequentialProObjectMorphismRep X Y}
    (F : C ⥤ D) (h : r₁.Equivalent r₂) :
    (mapRep F r₁).Equivalent (mapRep F r₂) := by
  -- Proof comment: the same common refinement works after applying `F.map` to the stage maps.
  rcases h with ⟨reindex', h₁, h₂, hmaps⟩
  refine ⟨reindex', h₁, h₂, ?_⟩
  intro n
  simpa [mapRep, Functor.map_comp] using congrArg (fun t ↦ F.map t) (hmaps n)

/-- Helper for Proposition 15.95.2: representative-level pro-isomorphisms remain pro-isomorphisms
after applying a functor stagewise. -/
private theorem isProIsomorphism_mapRep
    {C D : Type*} [Category C] [Category D]
    {X Y : ℕᵒᵖ ⥤ C}
    (F : C ⥤ D) {r : SequentialProObjectMorphismRep X Y} (hr : r.IsProIsomorphism) :
    (mapRep F r).IsProIsomorphism := by
  -- Proof comment: map the chosen representative inverse through `F` and transport both
  -- equivalence witnesses along `equivalent_mapRep`.
  rcases hr with ⟨s, hrs, hsr⟩
  refine ⟨mapRep F s, ?_, ?_⟩
  · simpa [mapRep] using equivalent_mapRep F hrs
  · simpa [mapRep] using equivalent_mapRep F hsr

/-- Helper for Proposition 15.95.2: after tensoring stagewise by a fixed `K`, the explicit
quotient comparison still induces an isomorphism of sequential pro-objects. -/
private theorem power_quotient_to_ideal_power_tensor_toProObjectHom_isIso
    [IsNoetherianRing A] (K : DMod) {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) :
    IsIso
      ((SequentialProObjectMorphismRep.ofNatTrans
        ((powerQuotientToIdealPowerNatTrans f I hspan).whiskerRight
          (derivedTensorProduct K))).toProObjectHom) := by
  have hforward :
      (SequentialProObjectMorphismRep.ofNatTrans
        (powerQuotientToIdealPowerNatTrans f I hspan)).IsProIsomorphism :=
    powerQuotientToIdealPowerNatTrans_isProIsomorphism (f := f) (I := I) hspan
  have hTensor :
      (mapRep (derivedTensorProduct K)
        (SequentialProObjectMorphismRep.ofNatTrans
          (powerQuotientToIdealPowerNatTrans f I hspan))).IsProIsomorphism :=
    isProIsomorphism_mapRep (derivedTensorProduct K) hforward
  simpa [mapRep, SequentialProObjectMorphismRep.ofNatTrans] using
    isIso_toProObjectHom_of_isProIsomorphism
      (a := mapRep (derivedTensorProduct K)
        (SequentialProObjectMorphismRep.ofNatTrans
          (powerQuotientToIdealPowerNatTrans f I hspan))) hTensor

/-- Helper for Proposition 15.95.2: fix notation for one chosen product object of the
ideal-power quotient tensor tower. -/
private abbrev idealPowerQuotientTensorProduct
    (I : Ideal A) (K : DMod)
    [HasProduct
      (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))] :
    DMod :=
  ∏ᶜ inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)

/-- Helper for Proposition 15.95.2: any two chosen products of the ideal-power quotient tensor
tower are canonically isomorphic. -/
private noncomputable def idealPowerQuotientTensorProductIso
    (I : Ideal A) (K : DMod)
    [hP : HasProduct
      (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))]
    [hQ : HasProduct
      (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))] :
    @idealPowerQuotientTensorProduct _ _ _ I K hP ≅
      @idealPowerQuotientTensorProduct _ _ _ I K hQ := by
  letI := hP
  let c' :
      Fan (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) :=
    Fan.mk
      (by
        letI := hQ
        exact ∏ᶜ inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))
      (fun n ↦ by
        letI := hQ
        exact Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n)
  let hc' : IsLimit c' := by
    letI := hQ
    simpa [c'] using
      productIsProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))
  exact hc'.conePointUniqueUpToIso
    (productIsProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)))

/-- Helper for Proposition 15.95.2: the canonical product isomorphism preserves each stage
projection of the ideal-power quotient tensor tower. -/
private theorem idealPowerQuotientTensorProductIso_hom_comp_π
    (I : Ideal A) (K : DMod)
    [hP : HasProduct
      (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))]
    [hQ : HasProduct
      (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))]
    (n : ℕ) :
    (idealPowerQuotientTensorProductIso I K).hom ≫
        (by
          letI := hQ
          exact Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n) =
      (by
        letI := hP
        exact Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n) := by
  letI := hP
  let c' :
      Fan (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) :=
    Fan.mk
      (by
        letI := hQ
        exact ∏ᶜ inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))
      (fun i ↦ by
        letI := hQ
        exact Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) i)
  let hc' : IsLimit c' := by
    letI := hQ
    simpa [c'] using
      productIsProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))
  -- Proof comment: both chosen products represent the same fan, so the unique comparison
  -- isomorphism is characterized by preserving every projection.
  simpa [idealPowerQuotientTensorProductIso, c'] using
    hc'.conePointUniqueUpToIso_hom_comp
      (productIsProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)))
      ⟨n⟩

attribute [reassoc] idealPowerQuotientTensorProductIso_hom_comp_π

/-- Helper for Proposition 15.95.2: the canonical product isomorphism intertwines the Milnor
difference map of the ideal-power quotient tensor tower. -/
private theorem idealPowerQuotientTensorProductIso_hom_comm_difference
    (I : Ideal A) (K : DMod)
    [hP : HasProduct
      (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))]
    [hQ : HasProduct
      (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))] :
    (idealPowerQuotientTensorProductIso I K).hom ≫
        (by
          letI := hQ
          exact derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K)) =
      (by
        letI := hP
        exact derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K)) ≫
        (idealPowerQuotientTensorProductIso I K).hom := by
  letI := hQ
  apply Pi.hom_ext
  intro n
  -- Proof comment: compare both composites after the `n`th projection; the product comparison
  -- fixes the `n`th and `(n + 1)`st coordinates, so both sides reduce to the same Milnor formula.
  have hleft :
      (idealPowerQuotientTensorProductIso I K).hom ≫
          derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K) ≫
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n =
        Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n -
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) (n + 1) ≫
            (idealPowerQuotientTensorDerivedInverseSystem I K).transitionMap (Nat.le_succ n) := by
    have hπn := idealPowerQuotientTensorProductIso_hom_comp_π I K n
    have hπsucc := idealPowerQuotientTensorProductIso_hom_comp_π I K (n + 1)
    calc
      (idealPowerQuotientTensorProductIso I K).hom ≫
          derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K) ≫
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n =
        (idealPowerQuotientTensorProductIso I K).hom ≫
            (Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n -
              Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))
                  (n + 1) ≫
                (idealPowerQuotientTensorDerivedInverseSystem I K).transitionMap
                  (Nat.le_succ n)) := by
            rw [derivedLimitDifferenceMap_comp_π]
      _ =
        (idealPowerQuotientTensorProductIso I K).hom ≫
            Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n -
          (idealPowerQuotientTensorProductIso I K).hom ≫
            Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))
                (n + 1) ≫
            (idealPowerQuotientTensorDerivedInverseSystem I K).transitionMap
              (Nat.le_succ n) := by
            rw [Preadditive.comp_sub]
      _ =
        Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n -
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) (n + 1) ≫
            (idealPowerQuotientTensorDerivedInverseSystem I K).transitionMap (Nat.le_succ n) := by
            rw [hπn]
            simpa [Category.assoc] using
              congrArg
                (fun g ↦
                  Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n -
                    g ≫
                      (idealPowerQuotientTensorDerivedInverseSystem I K).transitionMap
                        (Nat.le_succ n))
                hπsucc
  have hright :
      (by
        letI := hP
        exact derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K)) ≫
          (idealPowerQuotientTensorProductIso I K).hom ≫
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n =
        Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n -
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) (n + 1) ≫
            (idealPowerQuotientTensorDerivedInverseSystem I K).transitionMap (Nat.le_succ n) := by
    letI := hP
    calc
      derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K) ≫
          (idealPowerQuotientTensorProductIso I K).hom ≫
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n =
        derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K) ≫
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n := by
            simpa [Category.assoc] using
              congrArg
                (fun g ↦
                  derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K) ≫ g)
                (idealPowerQuotientTensorProductIso_hom_comp_π I K n)
      _ =
        Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n -
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) (n + 1) ≫
            (idealPowerQuotientTensorDerivedInverseSystem I K).transitionMap (Nat.le_succ n) := by
            simpa using derivedLimitDifferenceMap_comp_π
              (idealPowerQuotientTensorDerivedInverseSystem I K) n
  simpa [Category.assoc] using hleft.trans hright.symm

/-- Helper for Proposition 15.95.2: after fixing one product object of the ideal-power quotient
tensor tower, any quotient-side comparison witness can be transported to that fixed product. -/
private theorem exists_fixed_product_comparison_of_ideal_power_comparison
    {I : Ideal A} {K L : DMod} {c : K ⟶ L}
    [hP : HasProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))]
    (hc : IsDerivedCompletionIdealPowerQuotientTensorComparison I K L c) :
    ∃ ι : L ⟶ ∏ᶜ inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K),
      HasMilnorTriangle.WithMap (idealPowerQuotientTensorDerivedInverseSystem I K) ι ∧
        ∀ n : ℕ,
          c ≫ ι ≫ Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n =
            idealPowerQuotientTensorToStage I K n := by
  rcases hc with ⟨hP', ι', hι', hcomp⟩
  letI := hP'
  let e := idealPowerQuotientTensorProductIso I K
  rcases hι' with ⟨δ', hδ'⟩
  refine ⟨ι' ≫ e.hom, ?_, ?_⟩
  · -- Proof comment: transport the Milnor triangle across the canonical comparison between the
    -- original product object and the fixed one.
    refine ⟨e.inv ≫ δ', ?_⟩
    let T : Triangle DMod :=
      Triangle.mk ι' (derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K))
        δ'
    let T' : Triangle DMod :=
      Triangle.mk (ι' ≫ e.hom)
        (by
          letI := hP
          exact derivedLimitDifferenceMap (idealPowerQuotientTensorDerivedInverseSystem I K))
        (e.inv ≫ δ')
    have hIso : T ≅ T' := by
      refine Triangle.isoMk _ _ (Iso.refl _) e e ?_ ?_ ?_
      · simp [T, T']
      · simpa [T, T'] using
          (idealPowerQuotientTensorProductIso_hom_comm_difference I K).symm
      · simp [T, T']
    exact isomorphic_distinguished _ hδ' _ hIso.symm
  · intro n
    -- Proof comment: after the product normalization, the stagewise formulas are unchanged
    -- because the canonical product isomorphism preserves every projection.
    calc
      c ≫ (ι' ≫ e.hom) ≫
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n =
        c ≫ ι' ≫
          (e.hom ≫
            Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n) := by
            simp [Category.assoc]
      _ = c ≫ ι' ≫
          Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n := by
            rw [idealPowerQuotientTensorProductIso_hom_comp_π I K n]
      _ = idealPowerQuotientTensorToStage I K n := hcomp n

/-- Helper for Proposition 15.95.2: the stagewise formulas in a quotient-side comparison
reassemble to one equality into the fixed Milnor product of the ideal-power quotient tensor tower.
-/
private theorem ideal_power_comparison_comp_product_map_eq_canonical
    {I : Ideal A} {K L : DMod} {c : K ⟶ L}
    [HasProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))]
    {ι : L ⟶ ∏ᶜ inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)}
    (hcomp : ∀ n : ℕ,
      c ≫ ι ≫ Pi.π (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) n =
        idealPowerQuotientTensorToStage I K n) :
    c ≫ ι =
      Pi.lift (fun n ↦ idealPowerQuotientTensorToStage I K n) := by
  -- Proof comment: the universal property of the fixed product reduces the map equality to the
  -- stated stagewise identities.
  apply Pi.hom_ext
  intro n
  simpa using hcomp n

/-- Helper for Proposition 15.95.2: two Milnor presentations of the same sequential tower over
one chosen product object are canonically isomorphic over that product. -/
private theorem milnor_presentation_iso_of_same_tower
    {Ksys : ℕᵒᵖ ⥤ DMod}
    [HasProduct (inverseSystemFamily Ksys)]
    {L L' : DMod}
    {ι : L ⟶ ∏ᶜ inverseSystemFamily Ksys}
    {ι' : L' ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (hι' : HasMilnorTriangle.WithMap Ksys ι') :
    ∃ e : L ≅ L', e.hom ≫ ι' = ι := by
  rcases hι with ⟨δ, hδ⟩
  rcases hι' with ⟨δ', hδ'⟩
  let T : Triangle DMod := Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DMod := Triangle.mk ι' (derivedLimitDifferenceMap Ksys) δ'
  -- Proof comment: fill in the identity square on the common product terms and use two-out-of-
  -- three on the resulting morphism of distinguished triangles.
  obtain ⟨a, ha₁, ha₃⟩ :=
    complete_distinguished_triangle_morphism₁
      T T' hδ hδ' (𝟙 _) (𝟙 _)
      (by simp [T, T'])
  let φ : T ⟶ T' :=
    Triangle.homMk T T' a (𝟙 _) (𝟙 _)
      (by simpa [T, T'] using ha₁)
      (by simp [T, T'])
      (by simpa [T, T'] using ha₃)
  have ha : IsIso a := by
    haveI : IsIso φ.hom₂ := by
      simpa [φ] using (show IsIso (𝟙 (∏ᶜ inverseSystemFamily Ksys)) by infer_instance)
    haveI : IsIso φ.hom₃ := by
      simpa [φ] using (show IsIso (𝟙 (∏ᶜ inverseSystemFamily Ksys)) by infer_instance)
    have : IsIso φ.hom₁ :=
      Pretriangulated.isIso₁_of_isIso₂₃ φ hδ hδ' (by infer_instance) (by infer_instance)
    simpa using this
  exact ⟨asIso a, by simpa [T, T'] using ha₁.symm⟩

/-- Helper for Proposition 15.95.2: the explicit forward tensor comparison from the powered
Koszul tensor tower to the ideal-power quotient tensor tower. This is the fixed representative in
the source proof, obtained by first passing to the powered quotient tower and then to the
ideal-power quotient tower. -/
private abbrev koszulToIdealPowerTensorNatTrans
    {r : ℕ} (K : DMod) (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) :
    derivedCompletionKoszulPowerTensorDerivedInverseSystem K f ⟶
      idealPowerQuotientTensorDerivedInverseSystem I K :=
  (derivedCompletionKoszulToPowerQuotientNatTrans f).whiskerRight (derivedTensorProduct K) ≫
    (powerQuotientToIdealPowerNatTrans f I hspan).whiskerRight (derivedTensorProduct K)

/-- Helper for Proposition 15.95.2: the canonical map from `K` to the `n`th powered-quotient
tensor stage `K ⊗_A^L (A / (f_i^(n+1)))[0]`. This is the intermediate tower appearing explicitly
in the source proof. -/
private abbrev powerQuotientTensorToStage
    {r : ℕ} (K : DMod) (f : Fin r → A) (n : ℕ) :
    K ⟶ (derivedCompletionPowerQuotientDerivedInverseSystem f ⋙ derivedTensorProduct K).obj (op n) :=
  (singleZeroDerivedTensorIso K).inv ≫
    (derivedTensorProduct K).map
      ((single0).map
        (ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (koszulPowerIdeal f n)).toLinearMap)))

/-- Helper for Proposition 15.95.2: tensoring the fixed Koszul-to-powered-quotient stage map and
then composing with the canonical powered-Koszul comparison stage recovers the canonical
powered-quotient comparison stage. -/
private theorem derived_completion_koszul_to_power_quotient_tensor_stage_eq
    [IsNoetherianRing A] {r : ℕ} (K : DMod) (f : Fin r → A) (n : ℕ) :
    derivedCompletionKoszulPowerTensorToStage K f n ≫
        ((derivedCompletionKoszulToPowerQuotientNatTrans f).whiskerRight
          (derivedTensorProduct K)).app (op n) =
      powerQuotientTensorToStage K f n := by
  -- Proof comment: both sides are the same map obtained by tensoring the augmentation
  -- `A[0] ⟶ K_n^•` and then postcomposing with the fixed degree-zero quotient map of
  -- Lemma `15.95.1`.
  simp [derivedCompletionKoszulPowerTensorToStage, powerQuotientTensorToStage,
    derivedCompletionKoszulToPowerQuotientNatTrans, derivedCompletionKoszulToPowerQuotientStage,
    Category.assoc]

/-- Helper for Proposition 15.95.2: tensoring the powered-quotient-to-ideal-power stage map and
then composing with the canonical powered-quotient comparison stage recovers the canonical
ideal-power comparison stage. -/
private theorem power_quotient_tensor_to_ideal_power_tensor_stage_eq
    {r : ℕ} (K : DMod) (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) (n : ℕ) :
    powerQuotientTensorToStage K f n ≫
        ((powerQuotientToIdealPowerNatTrans f I hspan).whiskerRight
          (derivedTensorProduct K)).app (op n) =
      idealPowerQuotientTensorToStage I K n := by
  -- Proof comment: both composites are the quotient-stage map from `K` into
  -- `K ⊗_A^L (A / I^(n+1))[0]`; the forward comparison only changes the quotient object.
  simp [powerQuotientTensorToStage, idealPowerQuotientTensorToStage,
    powerQuotientToIdealPowerNatTrans, powerQuotientToIdealPowerStageMap, Category.assoc]

/-- Helper for Proposition 15.95.2: the two visible transport legs from the source proof
compose stagewise to the direct map from the powered Koszul tensor stage to the ideal-power
quotient tensor stage. -/
private theorem koszul_to_ideal_power_tensor_stage_eq
    [IsNoetherianRing A] {r : ℕ} (K : DMod) (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) (n : ℕ) :
    derivedCompletionKoszulPowerTensorToStage K f n ≫
        (koszulToIdealPowerTensorNatTrans K f I hspan).app (op n) =
      idealPowerQuotientTensorToStage I K n := by
  -- Proof comment: this is exactly the source-faithful two-step comparison, first to the powered
  -- quotient tower and then to the ideal-power quotient tower.
  rw [koszulToIdealPowerTensorNatTrans, NatTrans.comp_app, Category.assoc]
  calc
    derivedCompletionKoszulPowerTensorToStage K f n ≫
        ((derivedCompletionKoszulToPowerQuotientNatTrans f).whiskerRight
          (derivedTensorProduct K)).app (op n) ≫
        ((powerQuotientToIdealPowerNatTrans f I hspan).whiskerRight
          (derivedTensorProduct K)).app (op n) =
      powerQuotientTensorToStage K f n ≫
        ((powerQuotientToIdealPowerNatTrans f I hspan).whiskerRight
          (derivedTensorProduct K)).app (op n) := by
            rw [derived_completion_koszul_to_power_quotient_tensor_stage_eq]
    _ = idealPowerQuotientTensorToStage I K n := by
          exact power_quotient_tensor_to_ideal_power_tensor_stage_eq K f I hspan n

/-- Helper for Proposition 15.95.2: the stagewise formulas in a powered-quotient comparison
reassemble to one equality into the fixed Milnor product of the powered-quotient tensor tower. -/
private theorem power_quotient_comparison_comp_product_map_eq_canonical
    {r : ℕ} {K L : DMod} {f : Fin r → A} {c : K ⟶ L}
    [HasProduct
      (inverseSystemFamily (derivedCompletionPowerQuotientDerivedInverseSystem f ⋙
        derivedTensorProduct K))]
    {ι :
      L ⟶
        ∏ᶜ inverseSystemFamily
          (derivedCompletionPowerQuotientDerivedInverseSystem f ⋙ derivedTensorProduct K)}
    (hcomp : ∀ n : ℕ,
      c ≫ ι ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionPowerQuotientDerivedInverseSystem f ⋙ derivedTensorProduct K))
            n =
        powerQuotientTensorToStage K f n) :
    c ≫ ι =
      Pi.lift (fun n ↦ powerQuotientTensorToStage K f n) := by
  -- Proof comment: as for the quotient tower, equality into the fixed product is determined
  -- componentwise by the stage projections.
  apply Pi.hom_ext
  intro n
  simpa using hcomp n

/-- Helper for Proposition 15.95.2: tensoring the fixed representative from Lemma `15.95.1`
still gives an isomorphism of sequential pro-objects. -/
private theorem koszul_to_power_quotient_tensor_toProObjectHom_isIso
    [IsNoetherianRing A] (K : DMod) {r : ℕ} (f : Fin r → A) :
    IsIso
      ((SequentialProObjectMorphismRep.ofNatTrans
        ((derivedCompletionKoszulToPowerQuotientNatTrans f).whiskerRight
          (derivedTensorProduct K))).toProObjectHom) := by
  have hAGE :
      ∀ n : ℕ,
        ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)).IsGE
          (-((r : ℕ) : ℤ)) := by
    intro n
    exact derived_completion_koszul_stage_isGE_neg_r (A := A) (r := r) f n
  have hALE :
      ∀ n : ℕ,
        ((derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)).IsLE 0 := by
    intro n
    dsimp [derivedCompletionKoszulPowersDerivedInverseSystem]
    infer_instance
  have hpro :
      (SequentialProObjectMorphismRep.ofNatTrans
        (derivedCompletionKoszulToPowerQuotientNatTrans f)).IsProIsomorphism := by
    -- Proof comment: Lemma `15.95.1` already packages the bounded-window reduction; the
    -- remaining negative-degree comparison is imported as part of that theorem's owner API.
    refine
      derivedCompletionKoszulToPowerQuotientNatTrans_isProIsomorphism_of_window
        (A := A) (r := r) f hAGE hALE ?_
    intro p hp hpr
    exact
      negative_koszul_cohomology_comparison_isProIsomorphism
        (A := A) (r := r) (f := f) p hp hpr
  have hTensor :
      (mapRep (derivedTensorProduct K)
        (SequentialProObjectMorphismRep.ofNatTrans
          (derivedCompletionKoszulToPowerQuotientNatTrans f))).IsProIsomorphism :=
    isProIsomorphism_mapRep
      (derivedTensorProduct K)
      hpro
  simpa [mapRep, SequentialProObjectMorphismRep.ofNatTrans] using
    isIso_toProObjectHom_of_isProIsomorphism
      (a := mapRep (derivedTensorProduct K)
        (SequentialProObjectMorphismRep.ofNatTrans
          (derivedCompletionKoszulToPowerQuotientNatTrans f)))
      hTensor

/-- Helper for Proposition 15.95.2: an ideal-power quotient comparison can be transported along
the fixed powered-quotient and powered-Koszul pro-isomorphisms to a powered-Koszul comparison,
after postcomposing by an isomorphism of targets. -/
private theorem transport_koszul_comparison_of_ideal_power_comparison_specialized
    [IsNoetherianRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
    (hspan : I = Ideal.span (Set.range f)) {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionIdealPowerQuotientTensorComparison I K L c) :
    ∃ (L' : DMod) (e : L ≅ L'),
      IsDerivedCompletionKoszulPowerTensorComparison f K L' (c ≫ e.hom) := by
  -- Route correction: the transport is now decomposed through the explicit intermediate
  -- powered-quotient tensor tower from the source proof, rather than through one opaque composite.
  -- TODO(Proposition 15.95.2): normalize `hc` to a fixed ideal-power product presentation,
  -- transport it first across `powerQuotientToIdealPowerNatTrans` and then across
  -- `derivedCompletionKoszulToPowerQuotientNatTrans`, using the two stagewise equalities above and
  -- the corresponding `toProObjectHom` isomorphisms, and finally identify the resulting two Milnor
  -- presentations of the same tower by `milnor_presentation_iso_of_same_tower`.
  sorry

/-- For a Noetherian ring `A` and an ideal `I ⊆ A`, a canonical comparison
`c : K ⟶ L` from `K` to a chosen derived limit of the quotient tower
`(K \otimes_A^{\mathbf L} (A / I^(n+1))[0])_n` is an isomorphism exactly when `K` is derived
complete with respect to `I`. This is the quotient-tower form of the powered-Koszul criterion from
Lemma `15.92.17`. -/
theorem isDerivedCompleteWithRespectTo_iff_isIso_derivedIdealPowerQuotientCompletionComparison
    [IsNoetherianRing A] (I : Ideal A) {K L : DMod} (c : K ⟶ L)
    (hc : IsDerivedCompletionIdealPowerQuotientTensorComparison I K L c) :
    K.IsDerivedCompleteWithRespectTo I ↔ IsIso c := by
  obtain ⟨r, f, hspan⟩ := exists_span_range_eq_of_noetherian (A := A) I
  obtain ⟨L', e, hcKoszul⟩ :=
    transport_koszul_comparison_of_ideal_power_comparison_specialized
      (A := A) (f := f) I hspan hc
  constructor
  · intro hK
    -- Proof comment: after transporting the quotient-side comparison to the powered-Koszul
    -- tower, Lemma `15.92.17` applies verbatim with `I = (f_1, ..., f_r)`.
    have hIsoComp :
        IsIso (c ≫ e.hom) :=
      (isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison
        (A := A) f (c ≫ e.hom) hcKoszul).1 (by simpa [hspan] using hK)
    letI := hIsoComp
    have hc_eq : c = (c ≫ e.hom) ≫ e.inv := by
      simp [Category.assoc]
    rw [hc_eq]
    infer_instance
  · intro hIso
    -- Proof comment: the transported target is a powered-Koszul derived limit, hence derived
    -- complete with respect to `(f_1, ..., f_r)`; transport that property back across the two
    -- isomorphisms `e` and `c`.
    have hL' :
        L'.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) :=
      derivedLimitOfKoszulPowerTensor_isDerivedCompleteWithRespectTo_spanRange
        (A := A) f K L' hcKoszul.isDerivedLimit
    have hL :
        L.IsDerivedCompleteWithRespectTo I := by
      exact
        (isDerivedCompleteWithRespectTo_iff_of_iso (I := I) e).2
          (by simpa [hspan] using hL')
    exact
      (isDerivedCompleteWithRespectTo_iff_of_iso (I := I) (asIso c)).2 hL

/-- Helper for Proposition 15.95.2: every quotient-tower comparison into a derived-complete
target is an isomorphism. -/
private theorem eta_app_isIso_of_derivedComplete
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    IsIso (η.app E.obj) := by
  -- Proof comment: the quotient-side criterion is the exact analogue of Lemma `15.92.17`, so it
  -- turns derived completeness of the target into invertibility of the comparison map.
  exact
    (isDerivedCompleteWithRespectTo_iff_isIso_derivedIdealPowerQuotientCompletionComparison
      I (η.app E.obj) (hη E.obj)).1 E.property

/-- Helper for Proposition 15.95.2: the comparison morphism isomorphism attached to the chosen
reflection object. -/
private noncomputable def eta_app_iso
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    (K : DMod) : K ≅ (L.obj K).obj :=
  @asIso _ _ _ _ (η.app K) (eta_app_isIso_of_derivedComplete I L η hη (L.obj K))

/-- Helper for Proposition 15.95.2: the counit on a derived-complete object is the inverse of the
comparison isomorphism, lifted back to the full subcategory. -/
private noncomputable def derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    L.obj E.obj ⟶ E :=
  (DerivedCategory.derivedCompleteObjectProperty I).ι.preimage
    ((eta_app_iso I L η hη E.obj).symm.hom)

/-- Helper for Proposition 15.95.2: forgetting the counit recovers the inverse comparison map in
the ambient derived category. -/
private theorem derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp_map
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
        (derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E) =
      (eta_app_iso I L η hη E.obj).symm.hom := by
  -- Proof comment: the counit was defined by `preimage`, so the inclusion functor forgets it to
  -- the ambient inverse comparison map.
  rw [derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp]
  rw [(DerivedCategory.derivedCompleteObjectProperty I).ι.map_preimage]

/-- Helper for Proposition 15.95.2: the counit is natural on the full subcategory of
derived-complete objects. -/
private theorem derivedLimitOfIdealPowerQuotientTensorFunctorCounit_natural
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    {E₁ E₂ : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory}
    (φ : E₁ ⟶ E₂) :
    L.map (((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) ≫
        derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E₂ =
      derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E₁ ≫ φ := by
  apply ObjectProperty.hom_ext
  -- Proof comment: after forgetting to the ambient derived category, this is inverse-form
  -- naturality for the comparison transformation `η`.
  simp only [Functor.map_comp,
    derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp_map, Category.assoc]
  apply (cancel_mono (eta_app_iso I L η hη E₁.obj).hom).1
  simpa [eta_app_iso, Category.assoc] using
    congrArg
      (fun k ↦ k ≫ (eta_app_iso I L η hη E₂.obj).symm.hom)
      (η.naturality (((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ))

/-- Helper for Proposition 15.95.2: the reflector triangle identity holds on the image of the
candidate left adjoint. -/
private theorem derivedLimitOfIdealPowerQuotientTensorFunctorTriangle
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    (K : DMod) :
    L.map (η.app K) ≫
        derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη (L.obj K) =
      𝟙 (L.obj K) := by
  apply ObjectProperty.hom_ext
  -- Proof comment: after forgetting to `D(A)`, this is the usual triangle identity for a unit
  -- and its chosen inverse on the reflected object.
  simp only [Functor.map_comp,
    derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp_map, Category.assoc]
  apply (cancel_mono (eta_app_iso I L η hη K).hom).1
  simpa [eta_app_iso, Category.assoc] using
    congrArg
      (fun k ↦ k ≫ (eta_app_iso I L η hη (L.obj K).obj).symm.hom)
      (η.naturality (η.app K))

/-- Helper for Proposition 15.95.2: the explicit inverse formula is a left inverse to
precomposition by the comparison map. -/
private theorem derivedLimitOfIdealPowerQuotientTensorFunctorHom_left_inv
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    (K : DMod)
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    Function.LeftInverse
      (fun ψ : K ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E ↦
        L.map ψ ≫ derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E)
      (fun φ : L.obj K ⟶ E ↦
        η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) := by
  intro φ
  -- Proof comment: move the postcomposition past the counit by naturality and then close with
  -- the reflector triangle identity.
  calc
    L.map (η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) ≫
        derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E
        =
      (L.map (η.app K) ≫
        L.map (((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ)) ≫
          derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E := by
            rw [Functor.map_comp]
    _ =
      L.map (η.app K) ≫
        (L.map (((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) ≫
          derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E) := by
            simp [Category.assoc]
    _ =
      L.map (η.app K) ≫
        (derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη (L.obj K) ≫ φ) := by
            rw [derivedLimitOfIdealPowerQuotientTensorFunctorCounit_natural I L η hη φ]
    _ =
      (L.map (η.app K) ≫
        derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη (L.obj K)) ≫ φ := by
            simp [Category.assoc]
    _ = φ := by
            rw [derivedLimitOfIdealPowerQuotientTensorFunctorTriangle I L η hη K]
            simp

/-- Helper for Proposition 15.95.2: the same explicit inverse formula is also a right inverse. -/
private theorem derivedLimitOfIdealPowerQuotientTensorFunctorHom_right_inv
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    (K : DMod)
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    Function.RightInverse
      (fun ψ : K ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E ↦
        L.map ψ ≫ derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E)
      (fun φ : L.obj K ⟶ E ↦
        η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) := by
  intro ψ
  -- Proof comment: naturality of `η` rewrites the composite to `ψ ≫ η.app E.obj`, and the
  -- counit is the inverse of that comparison isomorphism.
  calc
    η.app K ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
          (L.map ψ ≫ derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E)
        =
      η.app K ≫
        (((L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι).map ψ) ≫
          (eta_app_iso I L η hη E.obj).symm.hom) := by
            simp [derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp_map, Category.assoc]
    _ =
      (ψ ≫ (eta_app_iso I L η hη E.obj).hom) ≫
        (eta_app_iso I L η hη E.obj).symm.hom := by
            simpa [eta_app_iso, Category.assoc] using η.naturality ψ
    _ = ψ := by
            simp [Category.assoc]

/-- Helper for Proposition 15.95.2: morphisms from the reflected object into a derived-complete
target are equivalent to morphisms from the original object into the ambient target. -/
private noncomputable def derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    (K : DMod)
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    (L.obj K ⟶ E) ≃
      (K ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E) where
  toFun φ := η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ
  invFun ψ := L.map ψ ≫ derivedLimitOfIdealPowerQuotientTensorFunctorCounitApp I L η hη E
  left_inv := derivedLimitOfIdealPowerQuotientTensorFunctorHom_left_inv I L η hη K E
  right_inv := derivedLimitOfIdealPowerQuotientTensorFunctorHom_right_inv I L η hη K E

/-- Helper for Proposition 15.95.2: the Hom-equivalence is natural in the source object. -/
private theorem derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv_naturality_left_symm
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    {K₁ K₂ : DMod}
    {E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory}
    (a : K₁ ⟶ K₂)
    (g : K₂ ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E) :
    (derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₁ E).symm (a ≫ g) =
      L.map a ≫ (derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₂ E).symm g := by
  apply (derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₁ E).injective
  -- Proof comment: both candidates become the same map after precomposition with `η.app K₁`, so
  -- injectivity of the Hom-equivalence identifies them.
  calc
    η.app K₁ ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
          ((derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₁ E).symm (a ≫ g))
        =
      a ≫ g := by
        exact
          (derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₁ E).apply_symm_apply _
    _ =
      a ≫
        (η.app K₂ ≫
          ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
            ((derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₂ E).symm g)) := by
              rw [(derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₂ E).apply_symm_apply]
    _ =
      (η.app K₁ ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map (L.map a)) ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
          ((derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₂ E).symm g) := by
            rw [η.naturality a]
            simp [Category.assoc]
    _ =
      η.app K₁ ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
          (L.map a ≫
            (derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K₂ E).symm g) := by
              simp [Category.assoc]

/-- Helper for Proposition 15.95.2: the Hom-equivalence is natural in the derived-complete
target. -/
private theorem derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv_naturality_right
    [IsNoetherianRing A]
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison
          I K (L.obj K).obj (η.app K))
    {K : DMod}
    {E₁ E₂ : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory}
    (g : L.obj K ⟶ E₁)
    (h : E₁ ⟶ E₂) :
    derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K E₂ (g ≫ h) =
      derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη K E₁ g ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map h := by
  -- Proof comment: expanding the forward map reduces the claim to associativity and functoriality
  -- of the inclusion functor.
  change
    η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map (g ≫ h) =
      (η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map g) ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map h
  simp [Category.assoc]

-- Proof sketch: choose generators of `I`, transport the quotient-tower comparison to the
-- powered-Koszul comparison through the pro-isomorphism of Lemma `15.95.1`, and apply the
-- canonical adjunction owner `derivedLimitOfKoszulPowerTensorFunctorAdjunction`.
/-- Proposition 15.95.2: let `A` be a Noetherian ring and let `I ⊆ A` be an ideal. Let
`L : D(A) ⥤ D_{comp}(A, I)` be a functor to the full subcategory of objects derived complete with
respect to `I`, and let `η : 𝟭 ⟶ L ⋙ ι` be a natural transformation such that each component
`η.app K` is the canonical comparison map
`K ⟶ R\!\varprojlim (K \otimes_A^{\mathbf L} (A / I^(n+1))[0])` in the source-facing sense of
`IsDerivedCompletionIdealPowerQuotientTensorComparison`. Then `L` is left adjoint to the
inclusion `ι : D_{comp}(A, I) ⥤ D(A)`. The proposition-level `L.IsLeftAdjoint` statement is only
the derived consequence recorded below. -/
@[stacks 0922]
noncomputable def derivedLimitOfIdealPowerQuotientTensorFunctorAdjunction
    [IsNoetherianRing A] (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison I K (L.obj K).obj (η.app K)) :
    L ⊣ (DerivedCategory.derivedCompleteObjectProperty I).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv I L η hη
      homEquiv_naturality_left_symm :=
        derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv_naturality_left_symm I L η hη
      homEquiv_naturality_right :=
        derivedLimitOfIdealPowerQuotientTensorFunctorHomEquiv_naturality_right I L η hη }

/-- Derived consequence of Proposition `15.95.2`: the quotient-tower derived-limit functor is a
left adjoint. The source-facing content is the adjunction
`derivedLimitOfIdealPowerQuotientTensorFunctorAdjunction`. -/
@[stacks 0922]
theorem derivedLimitOfIdealPowerQuotientTensorFunctor_isLeftAdjoint
    [IsNoetherianRing A] (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison I K (L.obj K).obj (η.app K)) :
    L.IsLeftAdjoint :=
  (derivedLimitOfIdealPowerQuotientTensorFunctorAdjunction I L η hη).isLeftAdjoint

end
