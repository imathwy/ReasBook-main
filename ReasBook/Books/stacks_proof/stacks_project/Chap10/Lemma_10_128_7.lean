import stacks_proof.stacks_project.Chap10.Lemma_10_127_13
import stacks_proof.stacks_project.Chap10.Lemma_10_128_3
import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Remark_10_75_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.FinitePresentation S M]

/- Domain-style sampling for the approximation-based flatness criterion:
- primary domain: flatness of a finitely presented module over an essentially finitely presented
  local map, detected from a quotient-flatness hypothesis and a `Tor₁` vanishing hypothesis;
- sampled owner declarations of the same kind:
  `RingHom.EssFinitePresentation`,
  `DirectedLocalEssFinitePresentationModuleApproximation`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `Tor₁[R](M, N)`;
- best owner abstraction: the source-facing theorem here still concludes in the canonical owner
  `Module.Flat`, and its homological hypothesis should reuse the chapter owner notation
  `Tor₁[R](M, R ⧸ I)` rather than a raw derived-functor term;
- primitive data: the local map `R → S`, the essentially finitely presented hypothesis, the
  finitely presented `S`-module `M`, the proper ideal `I`, the vanishing of `Tor₁^R(M, R / I)`,
  and flatness of `M / IM` over `R / I`;
- derived API: flatness of `M` over `R`.

Source/core/bridge triage:
- `source-facing`: Lemma 10.128.7 itself;
- `core/canonical`: `Module.Flat`, `RingHom.EssFinitePresentation`, and the chapter owner notation
  `Tor₁[R](M, N)`;
- `bridge/view`: the directed approximation owner
  `DirectedLocalEssFinitePresentationModuleApproximation` and the stagewise descent/ascent lemmas
  `10.127.13`, `10.128.3`, `10.99.12`, and `10.99.10`, which belong to the proof route rather
  than to the public statement.
-/

-- Proof sketch: use Lemma `10.127.13` to approximate the local map `R → S` and the finitely
-- presented `S`-module `M` by finite type stage data. Descend flatness of `M / IM` to a stage via
-- Lemma `10.128.3`, then use finite generation of the stage `Tor₁` module together with the
-- vanishing of `Tor₁^R(M, R / I)` and the surjectivity-up-to-localization statement from
-- Lemma `10.99.12` to force stagewise vanishing of `Tor₁`. Finally apply the variant of the local
-- criterion from Lemma `10.99.10` at that stage and pass back to the limit.
omit [Module R M] [IsScalarTower R S M] in
/-- Helper for Chap10 Lemma 10 128 7: the algebra-map essential finite-presentation hypothesis
supplies the directed local approximation of the map and module. -/
private theorem nonemptyModuleApproximation_of_algebraMapEssFinitePresentation
    (hess : (algebraMap R S).EssFinitePresentation) :
    Nonempty
      (DirectedLocalEssFinitePresentationModuleApproximation.{u, v, u, v, max u v}
        (algebraMap R S) M) := by
  -- Proof comment: specialize Lemma `10.127.13` to the ambient algebra map; later proof steps
  -- should work stagewise inside this approximation.
  exact exists_localEssFinitePresentationModuleApproximation (f := algebraMap R S) (M := M) hess

/-- Helper for Chap10 Lemma 10 128 7: the stage ideal induced by an ideal on the limit source
ring is the comap along the source-stage-to-limit map. -/
private noncomputable abbrev stageIdeal
    (A : DirectedLocalEssFinitePresentationModuleApproximation
      (algebraMap R S) M)
    (I : Ideal R) (i : A.Λ) : Ideal (A.RStage i) :=
  Ideal.comap
    (DirectedLocalEssFinitePresentationModuleApproximation.source_stage_to_limit_hom A i) I

/-- Helper for Chap10 Lemma 10 128 7: membership in the stage ideal is membership after
mapping to the limit source ring. -/
private theorem mem_stageIdeal_iff
    (A : DirectedLocalEssFinitePresentationModuleApproximation
      (algebraMap R S) M)
    (I : Ideal R) (i : A.Λ) (r : A.RStage i) :
    r ∈ stageIdeal (R := R) (S := S) (M := M) A I i ↔
      DirectedLocalEssFinitePresentationModuleApproximation.source_stage_to_limit_hom A i r ∈ I := by
  -- Proof comment: unfold the chosen normal form for the stage ideal exactly once.
  rfl

/-- Helper for Chap10 Lemma 10 128 7: a stage ideal is top exactly when the limit ideal is top. -/
private theorem stageIdeal_eq_top_iff
    (A : DirectedLocalEssFinitePresentationModuleApproximation
      (algebraMap R S) M)
    (I : Ideal R) (i : A.Λ) :
    stageIdeal (R := R) (S := S) (M := M) A I i = ⊤ ↔ I = ⊤ := by
  constructor
  · intro htop
    -- Proof comment: topness at a stage puts the image of `1` in the limit ideal, hence the
    -- limit ideal is top.
    apply (Ideal.eq_top_iff_one I).mpr
    have hone_stage : (1 : A.RStage i) ∈
        stageIdeal (R := R) (S := S) (M := M) A I i := by
      rw [htop]
      exact Submodule.mem_top
    simpa using (mem_stageIdeal_iff (R := R) (S := S) (M := M) A I i 1).mp hone_stage
  · intro htop
    -- Proof comment: if the limit ideal is top, its comap to any stage is top.
    rw [htop]
    simp [stageIdeal]

/-- Helper for Chap10 Lemma 10 128 7: the stage ideal above a proper limit ideal is proper. -/
private theorem stageIdeal_ne_top
    (A : DirectedLocalEssFinitePresentationModuleApproximation
      (algebraMap R S) M)
    (I : Ideal R) (hI : I ≠ ⊤) (i : A.Λ) :
    stageIdeal (R := R) (S := S) (M := M) A I i ≠ ⊤ := by
  -- Proof comment: properness now follows from the stage/top criterion, avoiding repeated
  -- unfolding of the comap normal form in later stage arguments.
  intro htop
  exact hI ((stageIdeal_eq_top_iff (R := R) (S := S) (M := M) A I i).mp htop)

omit [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 128 7: vanishing of the public quotient `Tor₁` owner makes the
canonical ideal-multiplication tensor map injective. -/
private theorem idealTensorMul_injective_of_torOneQuotient_vanishing
    (J : Ideal R) (hTor : IsZero (Tor₁[R](M, R ⧸ J))) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype)) := by
  let μ : J ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype)
  have hKerSubsingleton : Subsingleton (LinearMap.ker μ) := by
    let eKernel :=
      tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := R) (M := M) J
    -- Proof comment: Remark `10.75.9` identifies the public `Tor₁` term with the kernel of
    -- multiplication by the ideal, so `IsZero` gives a subsingleton kernel.
    exact
      (eKernel.toEquiv.subsingleton_congr).mp
        ((ModuleCat.isZero_iff_subsingleton).1 hTor)
  have hker : LinearMap.ker μ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    -- Proof comment: a subsingleton kernel contains only the zero element.
    have hz' : (⟨z, hz⟩ : LinearMap.ker μ) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val hz'
  -- Proof comment: injectivity of a linear map is equivalent to having zero kernel.
  exact (LinearMap.ker_eq_bot.mp hker)

/-- Helper for Chap10 Lemma 10 128 7: a proper ideal in the source of a local homomorphism maps
inside the maximal ideal of the target. -/
private theorem map_ideal_le_maximalIdeal_of_ne_top
    (I : Ideal R) (hI : I ≠ ⊤) :
    Ideal.map (algebraMap R S) I ≤ IsLocalRing.maximalIdeal S := by
  -- Proof comment: proper ideals in a local source lie in the source maximal ideal, and a local
  -- homomorphism maps the source maximal ideal into the target maximal ideal.
  exact
    (Ideal.map_mono (IsLocalRing.le_maximalIdeal (R := R) hI)).trans
      (IsLocalRing.map_maximalIdeal_le (algebraMap R S))

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 7: quotient flatness trivializes the image of a finite
relation after reducing both coefficients and vectors modulo `I`. -/
private theorem quotient_relation_isTrivial_of_flat_mod_ideal
    (I : Ideal R) (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    {l : ℕ} {f : Fin l → R} {x : Fin l → M}
    (hrel : ∑ i, f i • x i = 0) :
    Module.IsTrivialRelation (fun i : Fin l => Ideal.Quotient.mk I (f i))
      (fun i => (Submodule.Quotient.mk (x i) : M ⧸ (I • ⊤ : Submodule R M))) := by
  -- Proof comment: apply the flatness equational criterion over `R / I` to the image of the
  -- original relation in the quotient module.
  apply (Module.Flat.iff_forall_isTrivialRelation.mp hflat)
  have hq : Submodule.mkQ (I • ⊤ : Submodule R M) (∑ i, f i • x i) = 0 := by
    rw [hrel]
    exact map_zero _
  calc
    ∑ i, (Ideal.Quotient.mk I (f i)) •
        (Submodule.Quotient.mk (x i) : M ⧸ (I • ⊤ : Submodule R M)) =
        ∑ i, (Submodule.Quotient.mk (f i • x i) : M ⧸ (I • ⊤ : Submodule R M)) := by
      simp [Module.Quotient.mk_smul_mk]
    _ = Submodule.mkQ (I • ⊤ : Submodule R M) (∑ i, f i • x i) := by
      rw [map_sum]
      rfl
    _ = 0 := hq

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 7: a quotient-trivialized finite relation admits lifted
representatives whose coefficient sums vanish modulo `I`. -/
private theorem quotientRelation_liftedWitnesses_exists
    (I : Ideal R) (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    {l : ℕ} {f : Fin l → R} {x : Fin l → M}
    (hrel : ∑ i, f i • x i = 0) :
    ∃ (k : ℕ) (a : Fin l → Fin k → R) (y : Fin k → M),
      (∀ i,
        (Submodule.Quotient.mk (x i) : M ⧸ (I • ⊤ : Submodule R M)) =
          ∑ j, (Ideal.Quotient.mk I (a i j)) •
            (Submodule.Quotient.mk (y j) : M ⧸ (I • ⊤ : Submodule R M))) ∧
      ∀ j, Ideal.Quotient.mk I (∑ i, f i * a i j) = 0 := by
  classical
  obtain ⟨k, aq, yq, hxq, hfq⟩ :=
    quotient_relation_isTrivial_of_flat_mod_ideal (R := R) (M := M) I hflat hrel
  -- Proof comment: choose representatives for all quotient coefficients and quotient vectors.
  have ha_surj : ∀ i j, ∃ r : R, Ideal.Quotient.mk I r = aq i j := by
    intro i j
    exact Ideal.Quotient.mk_surjective (aq i j)
  choose a ha using ha_surj
  have hy_surj : ∀ j, ∃ m : M, Submodule.Quotient.mk m = yq j := by
    intro j
    exact Submodule.Quotient.mk_surjective (p := (I • ⊤ : Submodule R M)) (yq j)
  choose y hy using hy_surj
  refine ⟨k, a, y, ?_, ?_⟩
  · intro i
    -- Proof comment: replacing the quotient witnesses by their representatives preserves the
    -- displayed quotient decomposition.
    calc
      (Submodule.Quotient.mk (x i) : M ⧸ (I • ⊤ : Submodule R M)) = ∑ j, aq i j • yq j :=
        hxq i
      _ = ∑ j, (Ideal.Quotient.mk I (a i j)) •
            (Submodule.Quotient.mk (y j) : M ⧸ (I • ⊤ : Submodule R M)) := by
          simp [ha, hy]
  · intro j
    -- Proof comment: the coefficient identity in `R / I` is exactly the quotient of the lifted
    -- coefficient sum.
    simpa [map_sum, map_mul, ha] using hfq j

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 7: every element of `I • M` is hit by the canonical
ideal-multiplication tensor map `I ⊗ M → M`. -/
private theorem exists_idealTensorMul_preimage_of_mem_smul_top
    (I : Ideal R) {x : M} (hx : x ∈ (I • ⊤ : Submodule R M)) :
    ∃ z : I ⊗[R] M,
      TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) z = x := by
  classical
  have hx' : x ∈ I • Submodule.span R (Set.range fun m : M => m) := by
    simpa using hx
  rw [Submodule.mem_ideal_smul_span_iff_exists_sum I (fun m : M => m) x] at hx'
  obtain ⟨a, ha, hxsum⟩ := hx'
  let z : I ⊗[R] M := a.sum fun m r =>
    if h : r ∈ I then (⟨r, h⟩ : I) ⊗ₜ[R] m else 0
  refine ⟨z, ?_⟩
  -- Proof comment: represent the `I • M` element by a finite supported sum and lift each
  -- coefficient into the ideal tensor factor.
  calc
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) z =
        a.sum (fun m r => if h : r ∈ I then r • m else 0) := by
      dsimp [z]
      unfold Finsupp.sum
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases h : a m ∈ I <;> simp [h]
    _ = a.sum (fun m r => r • m) := by
      apply Finsupp.sum_congr
      intro m hm
      have hmI : a m ∈ I := ha m
      simp [hmI]
    _ = x := hxsum

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 7: the quotient witnesses split the original relation into
the coefficient part and the residual `I • M` part. -/
private theorem sum_relation_residual_identity
    {l k : ℕ} (f : Fin l → R) (a : Fin l → Fin k → R)
    (x : Fin l → M) (y : Fin k → M) :
    (∑ j, (∑ i, f i * a i j) • y j) +
      ∑ i, f i • (x i - ∑ j, a i j • y j) = ∑ i, f i • x i := by
  -- Proof comment: commute the finite sums in the coefficient part, then cancel the residual
  -- expansion against the original vectors.
  have hcoef :
      (∑ j, (∑ i, f i * a i j) • y j) = ∑ i, f i • ∑ j, a i j • y j := by
    calc
      (∑ j, (∑ i, f i * a i j) • y j) =
          ∑ j, ∑ i, (f i * a i j) • y j := by
        simp [Finset.sum_smul]
      _ = ∑ i, ∑ j, (f i * a i j) • y j := by
        rw [Finset.sum_comm]
      _ = ∑ i, f i • ∑ j, a i j • y j := by
        simp [Finset.smul_sum, mul_smul]
  rw [hcoef]
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 7: after quotient-flatness lifts the relation, the residual
data form a zero tensor in `I ⊗ M` under the Tor-injectivity hypothesis. -/
private theorem residualTensorRelation_zero_of_liftedWitnesses
    (I : Ideal R)
    {l k : ℕ} {f : Fin l → R} {x : Fin l → M}
    (a : Fin l → Fin k → R) (y : Fin k → M)
    (hrel : ∑ i, f i • x i = 0)
    (hcoef_mem : ∀ j, ∑ i, f i * a i j ∈ I)
    (hx_residual_mem : ∀ i, x i - ∑ j, a i j • y j ∈ (I • ⊤ : Submodule R M))
    (hmul_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype))) :
    ∃ z : Fin l → I ⊗[R] M,
      (∀ i,
        TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) (z i) =
          x i - ∑ j, a i j • y j) ∧
      (∑ j, (⟨∑ i, f i * a i j, hcoef_mem j⟩ : I) ⊗ₜ[R] y j) +
        ∑ i, f i • z i = 0 := by
  let μ : I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  have hres_tensor :
      ∀ i, ∃ z : I ⊗[R] M, μ z = x i - ∑ j, a i j • y j := by
    intro i
    exact exists_idealTensorMul_preimage_of_mem_smul_top (R := R) (M := M) I
      (hx_residual_mem i)
  choose z hz using hres_tensor
  refine ⟨z, hz, ?_⟩
  -- Proof comment: map the residual tensor relation to `M`; the image is exactly the original
  -- relation, hence zero, and Tor-injectivity reflects this zero back to `I ⊗ M`.
  apply hmul_inj
  calc
    μ ((∑ j, (⟨∑ i, f i * a i j, hcoef_mem j⟩ : I) ⊗ₜ[R] y j) +
        ∑ i, f i • z i) =
        (∑ j, ∑ i, (f i * a i j) • y j) +
          ∑ i, f i • (x i - ∑ j, a i j • y j) := by
      simp [μ, hz]
    _ = (∑ j, (∑ i, f i * a i j) • y j) +
          ∑ i, f i • (x i - ∑ j, a i j • y j) := by
      simp [Finset.sum_smul]
    _ = ∑ i, f i • x i := sum_relation_residual_identity (R := R) (M := M) f a x y
    _ = 0 := hrel

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 7: a trivial vanishing certificate for a finite ideal-tensor
family turns compatible linear-combination data into a trivial module relation. -/
private theorem isTrivialRelation_of_linearCombination_vanishesTrivially
    (I : Ideal R) {τ : Type u} [Fintype τ]
    {p : τ → I} {q : τ → M}
    {l : ℕ} {f : Fin l → R} {x : Fin l → M}
    (γ : Fin l → τ → R)
    (hx : ∀ i, x i = ∑ t, γ i t • q t)
    (hp : ∀ t, ∑ i, f i * γ i t = (p t : R))
    (hvanish : TensorProduct.VanishesTrivially R p q) :
    Module.IsTrivialRelation f x := by
  classical
  -- Proof comment: unfold the tensor-vanishing certificate and reuse its common right-hand
  -- generators as the witnesses for the original relation.
  rw [Module.isTrivialRelation_iff_vanishesTrivially]
  obtain ⟨k, b, w, hq, hpzero⟩ := hvanish
  refine
    TensorProduct.VanishesTrivially.of_fintype
      (κ := Fin k) (fun i m => ∑ t, γ i t * b t m) w ?_ ?_
  · intro i
    -- Proof comment: substitute the trivial-vanishing decompositions of the right factors and
    -- commute the two finite sums.
    calc
      x i = ∑ t, γ i t • q t := hx i
      _ = ∑ t, γ i t • ∑ m, b t m • w m := by
        simp [hq]
      _ = ∑ m, (∑ t, γ i t * b t m) • w m := by
        simpa [Finset.sum_smul, Finset.smul_sum, mul_smul] using
          (Finset.sum_comm :
            (∑ t, ∑ m, (γ i t * b t m) • w m) =
              ∑ m, ∑ t, (γ i t * b t m) • w m)
  · intro m
    -- Proof comment: the coefficient condition is the value in `R` of the ideal-valued zero
    -- supplied by the tensor-vanishing certificate.
    have hval : ∑ t, b t m * (p t : R) = 0 := by
      simpa using congrArg Subtype.val (hpzero m)
    have hsum :
        ∑ i, (∑ t, γ i t * b t m) • f i =
          ∑ t, b t m * (∑ i, f i * γ i t) := by
      simp_rw [smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    calc
      ∑ i, (∑ t, γ i t * b t m) • f i =
          ∑ t, b t m * (∑ i, f i * γ i t) := hsum
      _ = ∑ t, b t m * (p t : R) := by
        simp [hp]
      _ = 0 := hval

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
  [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 128 7: a trivial finite relation remains trivial after
transporting coefficients along an algebra map and vectors along a compatible linear map. -/
private theorem isTrivialRelation_map_of_isTrivialRelation
    {A : Type*} {B : Type*} {N : Type*} {P : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    (φ : N →ₗ[A] P) {l : ℕ} {fA : Fin l → A} {xA : Fin l → N}
    {f : Fin l → B} {x : Fin l → P}
    (hf : ∀ i, algebraMap A B (fA i) = f i)
    (hx : ∀ i, φ (xA i) = x i)
    (htriv : Module.IsTrivialRelation fA xA) :
    Module.IsTrivialRelation f x := by
  obtain ⟨k, a, y, hy, hcoef⟩ := htriv
  refine ⟨k, fun i j => algebraMap A B (a i j), fun j => φ (y j), ?_, ?_⟩
  · intro i
    -- Proof comment: map the stage witness decomposition through `φ` and rewrite the
    -- restricted scalar action as scalar multiplication by the image coefficient.
    calc
      x i = φ (xA i) := (hx i).symm
      _ = φ (∑ j, a i j • y j) := by
        rw [hy i]
      _ = ∑ j, algebraMap A B (a i j) • φ (y j) := by
        simp [map_sum, map_smul]
  · intro j
    -- Proof comment: coefficient vanishing is preserved by the algebra map after replacing the
    -- transported coefficients by their prescribed limit values.
    calc
      ∑ i, f i * algebraMap A B (a i j) =
          ∑ i, algebraMap A B (fA i) * algebraMap A B (a i j) := by
        simp [hf]
      _ = algebraMap A B (∑ i, fA i * a i j) := by
        simp [map_sum, map_mul]
      _ = 0 := by
        rw [hcoef j]
        exact map_zero _

/-- Helper for Chap10 Lemma 10 128 7: the quotient-flatness and quotient-`Tor₁` hypotheses
trivialize each finite relation in `M`. -/
private theorem relation_isTrivial_of_essFinitePresentation_localCriterion
    (hess : (algebraMap R S).EssFinitePresentation)
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    {l : ℕ} {f : Fin l → R} {x : Fin l → M}
    (hrel : ∑ i, f i • x i = 0) :
    Module.IsTrivialRelation f x := by
  classical
  obtain ⟨A⟩ :=
    nonemptyModuleApproximation_of_algebraMapEssFinitePresentation
      (R := R) (S := S) (M := M) hess
  have hstageIdealProper :
      ∀ i : A.Λ, stageIdeal (R := R) (S := S) (M := M) A I i ≠ ⊤ :=
    fun i ↦ stageIdeal_ne_top (R := R) (S := S) (M := M) A I hI i
  have hmapI :
      Ideal.map (algebraMap R S) I ≤ IsLocalRing.maximalIdeal S :=
    map_ideal_le_maximalIdeal_of_ne_top (R := R) (S := S) I hI
  -- Route correction: the previous residual-tensor route asked for a finite
  -- `VanishesTrivially` certificate from a zero tensor in `I ⊗ M`. That normal form is too
  -- strong without a generation or restricted tensor-injectivity hypothesis. The remaining source
  -- proof should instead descend this finite relation to a stage of `A`, move to a later stage
  -- where quotient flatness and quotient `Tor₁` vanish for `stageIdeal A I _`, apply the
  -- Noetherian local criterion there, and transport the resulting trivial relation back to `M`.
  -- The target-maximal containment (`hmapI`) is now separated from the still-missing
  -- approximation step.
  -- TODO: implement the stagewise local-criterion route using `hstageIdealProper`, the
  -- limit-level hypotheses above, quotient-flat descent, eventual stage `Tor₁` vanishing, and
  -- final-base-change transport of
  -- `Module.IsTrivialRelation`.
  sorry

/-- Lemma 10.128.7: let `R → S` be a local homomorphism of local rings, let `I ≠ R` be an ideal of
`R`, and let `M` be an `S`-module. If `S` is essentially of finite presentation over `R`, `M` is
of finite presentation over `S`, `Tor₁^R(M, R / I)` vanishes, and `M / IM` is flat over `R / I`,
then `M` is flat over `R`. -/
@[stacks 0471]
theorem flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal_of_essFinitePresentation
    (hess : (algebraMap R S).EssFinitePresentation)
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat R M := by
  -- Proof comment: reduce flatness to the equational criterion; the remaining source-proof work
  -- is isolated in the relation-level helper above.
  refine Module.Flat.of_forall_isTrivialRelation ?_
  intro l f x hrel
  exact
    relation_isTrivial_of_essFinitePresentation_localCriterion
      (R := R) (S := S) (M := M) hess I hI hTor hflat hrel

end
