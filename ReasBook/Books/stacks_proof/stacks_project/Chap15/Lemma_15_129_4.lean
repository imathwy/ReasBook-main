import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Module.Projective
import Mathlib.Order.Disjoint
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.TensorProduct.Free
import StacksProject_2024.Chap10.Lemma_10_19_1
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_75_7
import StacksProject_2024.Chap10.Theorem_10_85_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable [IsNoetherianRing (R ⧸ Ring.jacobson R)]

/- Domain triage:
- primary domain: projective modules, cyclic submodules, and complemented direct summands;
  `exists_free_directSummand_submodule_containing`, `IsComplemented`, and the canonical finiteness
  API for cyclic spans;
- sampled maximal-local owner declaration: `MaximalSpectrum R`, the chapter-project owner for
  hypotheses indexed by maximal ideals and their canonical localizations;
- source-facing layer: perturb `s` by an element of `M` so that the cyclic submodule it generates
  becomes a free direct summand;
- core/canonical layer: the chapter owner abstraction is
  `Module.HasFiniteFreeComplementSummandProperty R P`, while the cyclic submodule `R ∙ (s + m)` is
  the canonical source-facing object produced in this perturbation step;
- bridge/view: the present theorem is the source-facing bridge feeding that owner-level story.
  Because the underlying submodule is canonically fixed as `R ∙ (s + m)`, the direct-summand datum
  is best expressed by `IsComplemented (R ∙ (s + m))` rather than by a separate complemented-owner
  witness plus an equality back to the cyclic span. Freeness is an ordinary property of that fixed
  submodule and finiteness is already a derived instance.

Primitive data are the perturbation `m : M` and the resulting cyclic submodule `R ∙ (s + m)`.
Complementedness and freeness are derived properties of that fixed cyclic span, and finiteness is
already supplied canonically because cyclic spans are finitely generated, so none of them should
remain bundled inside a separate existential owner witness in the public API. -/

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: an element whose evaluation under some linear form is a unit spans
a free complemented direct summand. -/
lemma cyclicSpan_free_directSummand_of_exists_unit_linearForm
    (x : P) (hx : ∃ φ : P →ₗ[R] R, IsUnit (φ x)) :
    IsComplemented (R ∙ x) ∧ Module.Free R (R ∙ x) := by
  rcases hx with ⟨φ, hunit⟩
  let u : Rˣ := hunit.unit
  let φ₁ : P →ₗ[R] R := (↑u⁻¹ : R) • φ
  let proj : P →ₗ[R] P := φ₁.smulRight x
  -- Rescale the linear form so that the chosen generator is sent to `1`.
  have hu_spec : (u : R) = φ x := by
    simpa [u] using hunit.unit_spec
  have hφ₁x : φ₁ x = 1 := by
    change (↑u⁻¹ : R) * φ x = 1
    rw [← hu_spec]
    exact Units.inv_mul u
  have hproj_mem : ∀ y : P, proj y ∈ R ∙ x := by
    intro y
    rw [Submodule.mem_span_singleton]
    refine ⟨φ₁ y, ?_⟩
    simp [proj, LinearMap.smulRight_apply]
  let projSpan : P →ₗ[R] R ∙ x := LinearMap.codRestrict (R ∙ x) proj hproj_mem
  -- The projector acts as the identity on the cyclic span because `φ₁ x = 1`.
  have hprojSpan_id : ∀ y : R ∙ x, projSpan y = y := by
    intro y
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
    apply Subtype.ext
    calc
      ((projSpan y : R ∙ x) : P) = proj y := rfl
      _ = φ₁ y • x := by rfl
      _ = φ₁ (a • x) • x := by rw [ha.symm]
      _ = (a * φ₁ x) • x := by
        simp [smul_eq_mul, mul_smul]
      _ = a • x := by simp [hφ₁x]
      _ = y := by simpa using ha
  -- The identity-on-span projector gives a complement by the standard projection lemma.
  have hcompl : IsComplemented (R ∙ x) := by
    exact ⟨LinearMap.ker projSpan, LinearMap.isCompl_of_proj hprojSpan_id⟩
  have htoSpan_mem : ∀ r : R, LinearMap.toSpanSingleton R P x r ∈ R ∙ x := by
    intro r
    rw [LinearMap.toSpanSingleton_apply, Submodule.mem_span_singleton]
    exact ⟨r, rfl⟩
  let toSpan : R →ₗ[R] R ∙ x :=
    LinearMap.codRestrict (R ∙ x) (LinearMap.toSpanSingleton R P x) htoSpan_mem
  -- The span map is injective because the normalized linear form recovers the scalar, and it is
  -- surjective because every element of a singleton span is a scalar multiple of the generator.
  have htoSpan_bijective : Function.Bijective toSpan := by
    constructor
    · intro a b hab
      have hab' : (a : R) • x = (b : R) • x := by
        exact congrArg Subtype.val hab
      have hφ := congrArg φ₁ hab'
      simpa [smul_eq_mul, hφ₁x] using hφ
    · intro y
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
      refine ⟨a, ?_⟩
      apply Subtype.ext
      simpa [toSpan, LinearMap.toSpanSingleton_apply] using ha
  let eSpan : R ≃ₗ[R] R ∙ x := LinearEquiv.ofBijective toSpan htoSpan_bijective
  refine ⟨hcompl, ?_⟩
  exact Module.Free.of_equiv eSpan

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: an evaluation equal to `1` is the normalized special case of the
unit-valued criterion for splitting off the cyclic span. -/
lemma cyclicSpan_free_directSummand_of_exists_linearForm_eval_one
    (x : P) (hx : ∃ φ : P →ₗ[R] R, φ x = 1) :
    IsComplemented (R ∙ x) ∧ Module.Free R (R ∙ x) := by
  rcases hx with ⟨φ, hφ⟩
  -- Convert the exact evaluation `1` into the unit-valued hypothesis used by the splitting lemma.
  apply cyclicSpan_free_directSummand_of_exists_unit_linearForm
  refine ⟨φ, ?_⟩
  simpa [hφ] using (isUnit_one : IsUnit (1 : R))

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: a quotient-valued linear form sending `s + m` to `1` modulo the
Jacobson radical lifts to an `R`-linear form whose value on `s + m` is a unit. -/
lemma exists_unit_linearForm_of_eval_one_mod_jacobson
    (M : Submodule R P) (s : P)
    (hquot : ∃ m : M, ∃ φbar : P →ₗ[R] (R ⧸ Ring.jacobson R), φbar (s + m) = 1) :
    ∃ m : M, ∃ φ : P →ₗ[R] R, IsUnit (φ (s + m)) := by
  rcases hquot with ⟨m, φbar, hφbar⟩
  let π : R →ₗ[R] (R ⧸ Ring.jacobson R) := (Ideal.Quotient.mkₐ R (Ring.jacobson R)).toLinearMap
  obtain ⟨φ, hlift⟩ :=
    Module.projective_lifting_property π φbar (Ideal.Quotient.mkₐ_surjective R (Ring.jacobson R))
  have hπeval : Ideal.Quotient.mk (Ring.jacobson R) (φ (s + m)) = 1 := by
    -- Evaluate the lifted equality at the chosen perturbation.
    have hcomp :=
      congrArg (fun ψ : P →ₗ[R] (R ⧸ Ring.jacobson R) => ψ (s + m)) hlift
    simpa [π] using hcomp.trans hφbar
  have hmem : φ (s + m) - 1 ∈ Ring.jacobson R := by
    -- The difference from `1` dies in the quotient, hence lies in the Jacobson radical.
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hπeval, map_one]
    simp
  have hunit :
      IsUnit (1 + (φ (s + m) - 1)) := by
    -- Apply the Jacobson-radical unit criterion to the difference from `1`.
    exact
      (ideal_le_ring_jacobson_iff_isUnit_one_add (R := R) (I := Ring.jacobson R)).mp le_rfl
        (φ (s + m) - 1) hmem
  refine ⟨m, φ, ?_⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hunit

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: if `x` generates `P ⧸ M`, then that quotient is a finite
`R`-module. -/
lemma finite_quotient_of_span_singleton_sup_eq_top
    (M : Submodule R P) (x : P) (hspan : R ∙ x + M = ⊤) :
    Module.Finite R (P ⧸ M) := by
  let qx : P ⧸ M := M.mkQ x
  let f : R →ₗ[R] P ⧸ M := (LinearMap.id : R →ₗ[R] R).smulRight qx
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective M y
    -- Rewrite a class in `P ⧸ M` using the chosen generator `x` modulo `M`.
    have hp : p ∈ R ∙ x + M := by
      simpa [hspan] using (show p ∈ (⊤ : Submodule R P) from trivial)
    rcases Submodule.mem_sup.mp hp with ⟨u, hu, m, hm, rfl⟩
    rcases Submodule.mem_span_singleton.mp hu with ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    -- The quotient kills the `M`-part, so only the scalar multiple of `x` remains.
    simp [f, qx, hm]
  exact Module.Finite.of_surjective f hsurj

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: the source kernel
`M ∩ ⋂ i, ker (Φ i)` has finite quotient over a Noetherian ring because `P` maps into
`(P ⧸ M) × R^n` with exactly that kernel. This is the first finite-control step in the Stacks
argument once the source proof has reduced to the Noetherian case. -/
lemma finite_quotient_of_intersection_kernel
    [IsNoetherianRing R]
    (M : Submodule R P) (x : P) {n : ℕ} (Φ : Fin n → P →ₗ[R] R)
    (hspan : R ∙ x + M = ⊤) :
    Module.Finite R (P ⧸ (M ⊓ ⨅ i, LinearMap.ker (Φ i))) := by
  letI : Module.Finite R (P ⧸ M) :=
    finite_quotient_of_span_singleton_sup_eq_top (R := R) (P := P) M x hspan
  let f : P →ₗ[R] (P ⧸ M) × (Fin n → R) :=
    (M.mkQ).prod (LinearMap.pi Φ)
  have hker :
      LinearMap.ker f = M ⊓ ⨅ i, LinearMap.ker (Φ i) := by
    -- Proof comment: the product map vanishes exactly when the quotient coordinate is zero and
    -- every scalar-valued coordinate is zero.
    ext p
    constructor
    · intro hp
      have hp₀ : f p = 0 := by
        simpa [LinearMap.mem_ker] using hp
      refine ⟨?_, ?_⟩
      · exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Prod.fst hp₀)
      · change p ∈ ⨅ i, LinearMap.ker (Φ i)
        rw [Submodule.mem_iInf]
        intro i
        have hpi : ((LinearMap.pi Φ) p) i = 0 := by
          simpa [f] using congrArg (fun y : (P ⧸ M) × (Fin n → R) ↦ y.2 i) hp₀
        simpa [LinearMap.pi_apply, LinearMap.mem_ker] using hpi
    · rintro ⟨hpM, hpΦ⟩
      change f p = 0
      have hpΦ' : ∀ i : Fin n, p ∈ LinearMap.ker (Φ i) := by
        simpa [Submodule.mem_iInf] using hpΦ
      apply Prod.ext
      · exact (Submodule.Quotient.mk_eq_zero _).mpr hpM
      · ext i
        simpa [LinearMap.mem_ker] using hpΦ' i
  letI : Module.Finite R ((P ⧸ M) × (Fin n → R)) := by infer_instance
  letI : Module.Finite R f.range :=
    Module.Finite.of_injective f.range.subtype (Submodule.injective_subtype f.range)
  have hfiniteKerQuot : Module.Finite R (P ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  -- Proof comment: transport finiteness of the concrete range back across
  -- `P / ker(f) ≃ range(f)`, then rewrite the kernel description.
  exact hker ▸ hfiniteKerQuot

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: over a field, a vector outside the span of `x` can be separated
from `x` by a linear form which vanishes on `x` and sends that vector to `1`. -/
lemma exists_linearForm_zero_eq_one_of_not_mem_span_singleton
    {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (x t : V) (ht : t ∉ Submodule.span k ({x} : Set V)) :
    ∃ ℓ : V →ₗ[k] k, ℓ x = 0 ∧ ℓ t = 1 := by
  classical
  let q : V →ₗ[k] V ⧸ Submodule.span k ({x} : Set V) := Submodule.mkQ _
  have hqt : q t ≠ 0 := by
    -- The quotient class of `t` is nonzero exactly because `t` does not lie in the span of `x`.
    intro hzero
    apply ht
    exact (Submodule.Quotient.mk_eq_zero _).mp hzero
  let b : Module.Basis (Module.Free.ChooseBasisIndex k (V ⧸ Submodule.span k ({x} : Set V)))
      k (V ⧸ Submodule.span k ({x} : Set V)) := Module.Free.chooseBasis k _
  have hcoeff : ∃ i, (b.repr (q t)) i ≠ 0 := by
    -- Some coordinate of the nonzero quotient class must be nonzero in a basis expansion.
    by_contra hnone
    apply hqt
    apply b.repr.injective
    ext i
    by_contra hi
    exact hnone ⟨i, by simpa using hi⟩
  rcases hcoeff with ⟨i, hi⟩
  let c : k := ((b.repr (q t)) i)⁻¹
  let ℓbar : (V ⧸ Submodule.span k ({x} : Set V)) →ₗ[k] k := c • b.coord i
  refine ⟨ℓbar.comp q, ?_, ?_⟩
  · -- The quotient kills `x`, so the lifted functional vanishes on `x`.
    have hxq : q x = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (by simp))
    simp [q, hxq]
  · -- Rescaling the `i`-th coordinate makes the value on `t` equal to `1`.
    change c * (b.repr (q t)) i = 1
    simp [c, hi]

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: once a finite family of evaluations generates the unit ideal,
their `R`-linear combination is a single linear form evaluating to `1`. -/
lemma exists_linearForm_eval_one_of_span_range_eq_top
    {n : ℕ} (Φ : Fin n → P →ₗ[R] R) (x : P)
    (hspan : Ideal.span (Set.range fun i : Fin n ↦ Φ i x) = ⊤) :
    ∃ φ : P →ₗ[R] R, φ x = 1 := by
  have hsurj :
      Function.Surjective (Fintype.linearCombination R (fun i : Fin n ↦ Φ i x)) := by
    simpa using
      (span_range_eq_top_iff_surjective_fintypeLinearCombination R
        (fun i : Fin n ↦ Φ i x)).1 hspan
  rcases hsurj 1 with ⟨a, ha⟩
  refine ⟨∑ i, a i • Φ i, ?_⟩
  -- Evaluate the combined form at `x` and read off the prescribed linear combination.
  simpa [Fintype.linearCombination_apply, mul_comm, mul_left_comm, mul_assoc] using ha

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: over a local ring, finite generation of the maximal-ideal quotient
already lifts to finite generation of the whole module by Nakayama. -/
lemma moduleFinite_of_finite_quotient_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A]
    {Q : Type v} [AddCommGroup Q] [Module A Q]
    [Module.Projective A Q]
    [Module.Finite (A ⧸ IsLocalRing.maximalIdeal A)
      (Q ⧸ ((IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Q)))] :
    Module.Finite A Q := by
  -- TODO: identify `Q / 𝔪Q` with `(A ⧸ 𝔪) ⊗[A] Q`, transport the free basis of the local
  -- projective module `Q` across `Algebra.TensorProduct.basis`, and conclude that the common basis
  -- index is finite because the closed fiber is finite over `A ⧸ 𝔪`.
  sorry

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: for a local ring, non-finiteness persists after passing to the
closed fiber modulo the maximal ideal. -/
lemma not_moduleFinite_closed_fiber_of_not_moduleFinite
    {A : Type u} [CommRing A] [IsLocalRing A]
    {Q : Type v} [AddCommGroup Q] [Module A Q]
    [Module.Projective A Q]
    (hQ : ¬ Module.Finite A Q) :
    ¬ Module.Finite (A ⧸ IsLocalRing.maximalIdeal A)
      (Q ⧸ ((IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Q))) := by
  intro hclosed
  letI : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A)
      (Q ⧸ ((IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Q))) := hclosed
  exact hQ (moduleFinite_of_finite_quotient_maximalIdeal (A := A) (Q := Q))

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: quotienting a surjective exact pair by `I • ⊤` preserves
exactness. -/
lemma quotientMapByIdeal_exact
    {A : Type u} [CommRing A]
    {N P Q : Type v}
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q]
    (I : Ideal A) (f : N →ₗ[A] P) (g : P →ₗ[A] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A P)) y
    have hxI : g x ∈ I • (⊤ : Submodule A Q) := by
      simpa [LinearMap.quotientMapByIdeal] using
        (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A Q))).mp hy
    have hxLift :
        ∃ y' : P, y' ∈ I • (⊤ : Submodule A P) ∧ g y' = g x := by
      -- Lift the quotient-side `I • ⊤` witness back through surjectivity of `g`.
      refine
        Submodule.smul_induction_on hxI
          (fun a ha z _ ↦ ?_)
          (fun y z hy hz ↦ ?_)
      · obtain ⟨y', rfl⟩ := hg z
        refine ⟨a • y', ?_, by simp⟩
        exact Submodule.smul_mem_smul ha (by simp)
      · rcases hy with ⟨y', hy', rfl⟩
        rcases hz with ⟨z', hz', rfl⟩
        exact ⟨y' + z', Submodule.add_mem _ hy' hz', by simp⟩
    rcases hxLift with ⟨y', hy'I, hy'g⟩
    have hxy : g (x - y') = 0 := by
      simp [hy'g]
    rcases (hExact (x - y')).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule A N)).mkQ n, ?_⟩
    have hy'zero : ((I • (⊤ : Submodule A P)).mkQ y' : P ⧸ I • (⊤ : Submodule A P)) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hy'I
    calc
      (f.quotientMapByIdeal I) ((I • (⊤ : Submodule A N)).mkQ n)
          = (I • (⊤ : Submodule A P)).mkQ (f n) := by
              simp [LinearMap.quotientMapByIdeal]
      _ = (I • (⊤ : Submodule A P)).mkQ (x - y') := by rw [hn]
      _ = (I • (⊤ : Submodule A P)).mkQ x := by
            rw [map_sub, hy'zero, sub_zero]
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A N)) x
    change ((I • (⊤ : Submodule A Q)).mkQ (g (f x))) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    have hgf : g (f x) = 0 := by
      simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
    rw [hgf]
    exact Submodule.zero_mem _

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: quotienting a surjective linear map by `I • ⊤` preserves
surjectivity. -/
lemma quotientMapByIdeal_surjective
    {A : Type u} [CommRing A]
    {M N : Type v}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Surjective (f.quotientMapByIdeal I) := by
  intro y
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A N)) y
  obtain ⟨m, rfl⟩ := hf n
  -- The quotient map induced by `f` sends the chosen representative to the required class.
  refine ⟨Submodule.Quotient.mk m, ?_⟩
  simp [LinearMap.quotientMapByIdeal]

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: if a quotient module is finite over `A`, then it is also finite
over the quotient ring `A ⧸ I`. -/
lemma moduleFinite_quotientByIdeal_of_moduleFinite
    {A : Type u} [CommRing A]
    {I : Ideal A}
    {Q : Type v} [AddCommGroup Q] [Module A Q]
    (hQ : Module.Finite A Q) :
    Module.Finite (A ⧸ I) (Q ⧸ (I • (⊤ : Submodule A Q))) := by
  letI : Module.Finite A (Q ⧸ (I • (⊤ : Submodule A Q))) := by infer_instance
  exact Module.Finite.of_restrictScalars_finite A (A ⧸ I) (Q ⧸ (I • (⊤ : Submodule A Q)))

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: any submodule contained in a cyclic span is finite, since that span
is generated by one element. -/
lemma moduleFinite_of_le_span_singleton
    {A : Type u} [CommRing A]
    {Q : Type v} [AddCommGroup Q] [Module A Q]
    [IsNoetherianRing A]
    (L : Submodule A Q) (x : Q) (hL : L ≤ A ∙ x) :
    Module.Finite A L := by
  have hspanfg : (A ∙ x).FG := Submodule.fg_span_singleton x
  exact Module.Finite.of_fg (Submodule.FG.of_le hspanfg hL)

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: the realized evaluation ideal attached to a perturbation `m` and a
finite family of quotient-valued linear forms is the ideal generated by their evaluations on
`s + m`. -/
def realized_evalIdeal
    (M : Submodule R P) (s : P) {n : ℕ} (m : M)
    (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R)) :
    Ideal (R ⧸ Ring.jacobson R) :=
  Ideal.span (Set.range fun i : Fin n ↦ Φ i (s + m))

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: once a realized evaluation ideal is the unit ideal, the finite
family collapses to a single quotient-valued linear form sending `s + m` to `1`. -/
lemma exists_linearForm_eval_one_of_realized_evalIdeal_eq_top
    (M : Submodule R P) (s : P) {n : ℕ} (m : M)
    (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R))
    (htop : realized_evalIdeal (R := R) (P := P) M s m Φ = ⊤) :
    ∃ φbar : P →ₗ[R] (R ⧸ Ring.jacobson R), φbar (s + m) = 1 := by
  let S := R ⧸ Ring.jacobson R
  have hsurj :
      Function.Surjective (Fintype.linearCombination S (fun i : Fin n ↦ Φ i (s + m))) := by
    simpa [S, realized_evalIdeal] using
      (span_range_eq_top_iff_surjective_fintypeLinearCombination S
        (fun i : Fin n ↦ Φ i (s + m))).1 htop
  rcases hsurj 1 with ⟨a, ha⟩
  refine ⟨∑ i, a i • Φ i, ?_⟩
  -- Evaluate the chosen quotient-linear combination at `s + m` and read off the coefficient sum.
  simpa [Fintype.linearCombination_apply, S, mul_comm, mul_left_comm, mul_assoc] using ha

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: if two perturbations have the same values under every member of a
finite quotient-valued family, then they define the same realized evaluation ideal. -/
lemma realized_evalIdeal_eq_of_pointwise_eq
    (M : Submodule R P) (s : P) {n : ℕ} {m m' : M}
    (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R))
    (hΦ : ∀ i : Fin n, Φ i (s + m) = Φ i (s + m')) :
    realized_evalIdeal (R := R) (P := P) M s m Φ =
      realized_evalIdeal (R := R) (P := P) M s m' Φ := by
  -- Both realized ideals are spans of the same generators after rewriting the evaluations
  -- pointwise along `hΦ`.
  unfold realized_evalIdeal
  refine le_antisymm ?_ ?_
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    simpa [hΦ i] using
      (Ideal.subset_span ⟨i, rfl⟩ :
        Φ i (s + m') ∈ Ideal.span (Set.range fun i : Fin n ↦ Φ i (s + m')))
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    simpa [hΦ i] using
      (Ideal.subset_span ⟨i, rfl⟩ :
        Φ i (s + m) ∈ Ideal.span (Set.range fun i : Fin n ↦ Φ i (s + m)))

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: adding an element of the lifted common kernel to the perturbation
does not change the induced realized evaluation ideal. -/
lemma realized_evalIdeal_eq_of_add_mem_lifted_common_kernel
    (M : Submodule R P) (s : P) {n : ℕ} (m : M)
    (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R))
    (φ : Fin n → P →ₗ[R] R)
    (hφ : ∀ i : Fin n,
      ((Ideal.Quotient.mkₐ R (Ring.jacobson R)).toLinearMap.comp (φ i)) = Φ i)
    {k : P} (hk : k ∈ M ⊓ ⨅ i, LinearMap.ker (φ i)) :
    realized_evalIdeal (R := R) (P := P) M s m Φ =
      realized_evalIdeal (R := R) (P := P) M s
        (⟨(m : P) + k, M.add_mem m.2 hk.1⟩ : M) Φ := by
  apply realized_evalIdeal_eq_of_pointwise_eq
  intro i
  have hkφ : φ i k = 0 := by
    have hk' : ∀ j : Fin n, φ j k = 0 := by
      simpa [Submodule.mem_iInf, LinearMap.mem_ker] using hk.2
    exact hk' i
  -- Rewrite the perturbed evaluation through the chosen lifts and kill the common-kernel term.
  calc
    Φ i (s + m) =
      ((Ideal.Quotient.mkₐ R (Ring.jacobson R)).toLinearMap.comp (φ i)) (s + m) := by
        rw [← hφ i]
    _ =
      ((Ideal.Quotient.mkₐ R (Ring.jacobson R)).toLinearMap.comp (φ i)) ((s + m : P) + k) := by
        simp [LinearMap.comp_apply, map_add, hkφ]
    _ = Φ i ((s + m : P) + k) := by
        rw [hφ i]
    _ = Φ i (s + (⟨(m : P) + k, M.add_mem m.2 hk.1⟩ : M)) := by
        simp [add_assoc]

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: adjoining one more quotient-valued linear form whose value on the
new perturbation escapes a containing ideal forces a strict enlargement of the realized evaluation
ideal, provided the old realized ideal is unchanged by the perturbation. -/
lemma exists_strictly_larger_realized_evalIdeal_of_new_eval_not_mem
    (M : Submodule R P) (s : P) {n : ℕ} (m : M)
    (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R))
    {q : Ideal (R ⧸ Ring.jacobson R)}
    (hcontained : realized_evalIdeal (R := R) (P := P) M s m Φ ≤ q)
    (m' : M)
    (hold :
      realized_evalIdeal (R := R) (P := P) M s m Φ =
        realized_evalIdeal (R := R) (P := P) M s m' Φ)
    (ψ : P →ₗ[R] (R ⧸ Ring.jacobson R))
    (houtside : ψ (s + m') ∉ q) :
    ∃ Ψ : Fin (n + 1) → P →ₗ[R] (R ⧸ Ring.jacobson R),
      realized_evalIdeal (R := R) (P := P) M s m Φ <
        realized_evalIdeal (R := R) (P := P) M s m' Ψ := by
  let Ψ : Fin (n + 1) → P →ₗ[R] (R ⧸ Ring.jacobson R) := Fin.lastCases ψ Φ
  have hle_old :
      realized_evalIdeal (R := R) (P := P) M s m' Φ ≤
        realized_evalIdeal (R := R) (P := P) M s m' Ψ := by
    -- The old family sits inside the enlarged family by `Fin.castSucc`, now evaluated at the same
    -- perturbation `m'`.
    unfold realized_evalIdeal
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨Fin.castSucc i, by simp [Ψ]⟩
  have hle :
      realized_evalIdeal (R := R) (P := P) M s m Φ ≤
        realized_evalIdeal (R := R) (P := P) M s m' Ψ := by
    -- Transport the old ideal to the new perturbation before adjoining the extra generator.
    calc
      realized_evalIdeal (R := R) (P := P) M s m Φ =
          realized_evalIdeal (R := R) (P := P) M s m' Φ := hold
      _ ≤ realized_evalIdeal (R := R) (P := P) M s m' Ψ := hle_old
  have hnotle :
      ¬ realized_evalIdeal (R := R) (P := P) M s m' Ψ ≤ q := by
    intro hnew
    apply houtside
    -- The freshly adjoined evaluation lies in the enlarged realized ideal by construction.
    exact hnew <| by
      unfold realized_evalIdeal
      exact Ideal.subset_span ⟨Fin.last n, by simp [Ψ]⟩
  refine ⟨Ψ, lt_of_le_of_ne hle ?_⟩
  intro heq
  have hnew_contained :
      realized_evalIdeal (R := R) (P := P) M s m' Ψ ≤ q := by
    simpa [heq] using hcontained
  exact hnotle hnew_contained

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: the empty family realizes the zero ideal, so the set of realized
evaluation ideals is nonempty before the Noetherian maximal-choice step. -/
lemma realized_evalIdeal_empty_eq_bot
    (M : Submodule R P) (s : P) (m : M) :
    realized_evalIdeal (R := R) (P := P) M s m (n := 0) (fun i ↦ Fin.elim0 i) = ⊥ := by
  -- With no evaluations, the spanning set is empty, hence the generated ideal is zero.
  simp [realized_evalIdeal]

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: any proper realized evaluation ideal is contained in some maximal
ideal of the Jacobson quotient. -/
lemma exists_maximalIdeal_over_proper_realized_evalIdeal
    (M : Submodule R P) (s : P) {n : ℕ} (m : M)
    (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R))
    (hproper : realized_evalIdeal (R := R) (P := P) M s m Φ ≠ ⊤) :
    ∃ q : Ideal (R ⧸ Ring.jacobson R),
      q.IsMaximal ∧ realized_evalIdeal (R := R) (P := P) M s m Φ ≤ q := by
  -- A proper ideal is contained in a maximal ideal by the standard commutative-algebra lemma.
  obtain ⟨q, hqmax, hle⟩ :=
    Ideal.exists_le_maximal
      (realized_evalIdeal (R := R) (P := P) M s m Φ) hproper
  exact ⟨q, hqmax, hle⟩

omit [Module.Projective R P] in
/-- Helper for Lemma 15.129.4: over the Noetherian quotient `R ⧸ Ring.jacobson R`, one can choose
a realized evaluation ideal which is maximal among all realized evaluation ideals. -/
lemma exists_maximal_realized_evalIdeal
    (M : Submodule R P) (s : P) :
    ∃ n : ℕ, ∃ m : M, ∃ Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R),
      ∀ {n' : ℕ} {m' : M} {Ψ : Fin n' → P →ₗ[R] (R ⧸ Ring.jacobson R)},
        realized_evalIdeal (R := R) (P := P) M s m Φ ≤
        realized_evalIdeal (R := R) (P := P) M s m' Ψ →
        realized_evalIdeal (R := R) (P := P) M s m' Ψ =
          realized_evalIdeal (R := R) (P := P) M s m Φ := by
  classical
  let S := R ⧸ Ring.jacobson R
  let realizedSet : Set (Ideal S) :=
    { I | ∃ n : ℕ, ∃ m : M, ∃ Φ : Fin n → P →ₗ[R] S,
        realized_evalIdeal (R := R) (P := P) M s m Φ = I }
  have hnonempty : realizedSet.Nonempty := by
    -- The empty family realizes the zero ideal, so the candidate set is inhabited.
    refine ⟨⊥, ?_⟩
    refine ⟨0, (0 : M), fun i ↦ Fin.elim0 i, ?_⟩
    simpa [S] using realized_evalIdeal_empty_eq_bot (R := R) (P := P) M s (0 : M)
  have hwf : WellFounded ((· > ·) : Ideal S → Ideal S → Prop) := by
    -- Noetherianity of `S` makes strict inclusion on ideals well founded.
    simpa [S] using
      (isNoetherian_iff (R := S) (M := S)).mp inferInstance
  obtain ⟨I, hIrealized, hImax⟩ := hwf.has_min realizedSet hnonempty
  rcases hIrealized with ⟨n, m, Φ, rfl⟩
  refine ⟨n, m, Φ, ?_⟩
  intro n' m' Ψ hle
  have hrealized' :
      realized_evalIdeal (R := R) (P := P) M s m' Ψ ∈ realizedSet := by
    exact ⟨n', m', Ψ, rfl⟩
  -- Minimality for `>` means that no larger realized ideal exists above the chosen one.
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact False.elim (hImax _ hrealized' hlt)
  · simpa using heq.symm

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: a finite family of quotient-valued linear forms can be lifted to a
family of `R`-valued linear forms because `P` is projective. -/
lemma exists_lift_family_of_quotient_linearForms
    {n : ℕ} (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R)) :
    ∃ φ : Fin n → P →ₗ[R] R,
      ∀ i : Fin n,
        ((Ideal.Quotient.mkₐ R (Ring.jacobson R)).toLinearMap.comp (φ i)) = Φ i := by
  classical
  let π : R →ₗ[R] (R ⧸ Ring.jacobson R) := (Ideal.Quotient.mkₐ R (Ring.jacobson R)).toLinearMap
  -- Lift each member of the finite family separately through the quotient map.
  choose φ hφ using fun i : Fin n ↦
    Module.projective_lifting_property π (Φ i)
      (Ideal.Quotient.mkₐ_surjective R (Ring.jacobson R))
  exact ⟨φ, hφ⟩

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: if `P ⧸ K` is finite, then after localizing at a maximal ideal,
the localized copy of `K` inside `P_p` cannot be finite unless `P_p` is finite as well. -/
lemma localized_common_kernel_not_finite_at_lieover
    (p : MaximalSpectrum R) {K : Submodule R P}
    (hfiniteQuot : Module.Finite R (P ⧸ K))
    (hPp :
      ¬ Module.Finite (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P)) :
    ¬ Module.Finite (Localization.AtPrime p.asIdeal)
      ((Submodule.localized (p := p.asIdeal.primeCompl) K :
          Submodule (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal P))) := by
  intro hKp
  let A := Localization.AtPrime p.asIdeal
  let U := p.asIdeal.primeCompl
  letI :
      Module.Finite A
        ((Submodule.localized (p := U) K :
          Submodule A (LocalizedModule.AtPrime p.asIdeal P))) := hKp
  have hquot :
      Module.Finite A
        (LocalizedModule.AtPrime p.asIdeal P ⧸
          (Submodule.localized (p := U) K :
            Submodule A (LocalizedModule.AtPrime p.asIdeal P))) := by
    letI : Module.Finite A (LocalizedModule.AtPrime p.asIdeal (P ⧸ K)) := by
      infer_instance
    -- Localizing the finite quotient `P ⧸ K` identifies with quotienting the localized module by
    -- the localized copy of `K`.
    exact Module.Finite.equiv (localizedQuotientEquiv U K).symm
  letI :
      Module.Finite A
        (LocalizedModule.AtPrime p.asIdeal P ⧸
          (Submodule.localized (p := U) K :
            Submodule A (LocalizedModule.AtPrime p.asIdeal P))) := hquot
  have hExact :
      Function.Exact
        ((Submodule.localized (p := U) K :
          Submodule A (LocalizedModule.AtPrime p.asIdeal P)).subtype)
        ((Submodule.localized (p := U) K :
          Submodule A (LocalizedModule.AtPrime p.asIdeal P)).mkQ) := by
    -- The localized submodule sits in the standard exact sequence
    -- `0 → K_p → P_p → P_p / K_p → 0`.
    simpa using
      (LinearMap.exact_subtype_mkQ
        (Submodule.localized (p := U) K :
          Submodule A (LocalizedModule.AtPrime p.asIdeal P)))
  have hfiniteP :
      Module.Finite A (LocalizedModule.AtPrime p.asIdeal P) :=
    Module.Finite.of_exact hExact
      ((Submodule.localized (p := U) K :
        Submodule A (LocalizedModule.AtPrime p.asIdeal P)).mkQ_surjective)
  exact hPp hfiniteP

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: an element of a localized submodule admits a global numerator after
clearing one localization denominator. -/
lemma exists_smul_eq_mkLinearMap_of_localized_submodule_element
    (p : MaximalSpectrum R) (K : Submodule R P)
    (kp : Submodule.localized (p := p.asIdeal.primeCompl) K) :
    ∃ k : K, ∃ u : p.asIdeal.primeCompl,
      (u : R) • kp.1 =
        LocalizedModule.mkLinearMap p.asIdeal.primeCompl P k := by
  have hkp : kp.1 ∈ Submodule.localized (p := p.asIdeal.primeCompl) K := kp.2
  -- Proof comment: membership in the localized submodule already packages a numerator together
  -- with one denominator.
  rw [Submodule.mem_localized'] at hkp
  rcases hkp with ⟨k, hkK, u, hu⟩
  refine ⟨⟨k, hkK⟩, u, ?_⟩
  -- Proof comment: rewrite the localization equality `mk'(k, u) = kp` as the cleared
  -- denominator identity in the localized ambient module.
  exact
    (IsLocalizedModule.mk'_eq_iff
      (f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl P)).mp hu |>.symm

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.4: once the local argument produces a quotient-valued separator,
projectivity lifts it back to a separator valued in `R ⧸ Ring.jacobson R`. -/
lemma exists_separator_of_quotient_separator
    {K : Submodule R P} (x : P) {q : Ideal (R ⧸ Ring.jacobson R)}
    (hsepq : ∃ k : P, k ∈ K ∧
      ∃ ψq : P →ₗ[R] ((R ⧸ Ring.jacobson R) ⧸ q), ψq (x + k) ≠ 0) :
    ∃ k : P, k ∈ K ∧
      ∃ ψ : P →ₗ[R] (R ⧸ Ring.jacobson R), ψ (x + k) ∉ q := by
  let S := R ⧸ Ring.jacobson R
  rcases hsepq with ⟨k, hkK, ψq, hψq⟩
  let π : S →ₗ[R] (S ⧸ q) := (Ideal.Quotient.mkₐ S q).toLinearMap.restrictScalars R
  obtain ⟨ψ, hψ⟩ :=
    Module.projective_lifting_property π ψq <| by
      simpa [π, S] using (Ideal.Quotient.mkₐ_surjective S q)
  refine ⟨k, hkK, ψ, ?_⟩
  intro hmem
  have hπeval : Ideal.Quotient.mk q (ψ (x + k)) = ψq (x + k) := by
    -- Evaluate the lifted equality at the chosen perturbation.
    have hcomp := congrArg (fun f : P →ₗ[R] (S ⧸ q) => f (x + k)) hψ
    simpa [π, S] using hcomp
  apply hψq
  calc
    ψq (x + k) = Ideal.Quotient.mk q (ψ (x + k)) := hπeval.symm
    _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-- Helper for Lemma 15.129.4: package the remaining local closed-fiber argument directly at the
exact separator interface needed to enlarge the realized evaluation ideal. -/
lemma closed_fiber_common_kernel_separator_data
    (M : Submodule R P) (s : P)
    (hP : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P))
    {n : ℕ} (m : M)
    (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R))
    (φ : Fin n → P →ₗ[R] R)
    (hφ : ∀ i : Fin n,
      ((Ideal.Quotient.mkₐ R (Ring.jacobson R)).toLinearMap.comp (φ i)) = Φ i)
    {q : Ideal (R ⧸ Ring.jacobson R)} (hqmax : q.IsMaximal)
    (hcontained : realized_evalIdeal (R := R) (P := P) M s m Φ ≤ q)
    (hfiniteQuot :
      Module.Finite R (P ⧸ (M ⊓ ⨅ i, LinearMap.ker (φ i)))) :
    ∃ k : P, k ∈ M ⊓ ⨅ i, LinearMap.ker (φ i) ∧
      ∃ ψ : P →ₗ[R] (R ⧸ Ring.jacobson R), ψ ((s + m) + k) ∉ q := by
  -- TODO: localize at the maximal ideal lying over `q`, pass to the closed fiber of the localized
  -- exact sequence, use non-finiteness of the localized projective module to find a separator over
  -- the field quotient, then clear one denominator and invoke
  -- `exists_separator_of_quotient_separator`.
  sorry

/-- Helper for Lemma 15.129.4: if a realized evaluation ideal is contained in a maximal ideal of
`R ⧸ Ring.jacobson R`, the source proof constructs a strictly larger realized evaluation ideal by a
new perturbation lying in the current common kernel. -/
lemma exists_strictly_larger_realized_evalIdeal
    (M : Submodule R P) (s : P)
    (hP : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P))
    (hspan : R ∙ s + M = ⊤)
    {n : ℕ} (m : M) (Φ : Fin n → P →ₗ[R] (R ⧸ Ring.jacobson R))
    {q : Ideal (R ⧸ Ring.jacobson R)} (hqmax : q.IsMaximal)
    (hcontained : realized_evalIdeal (R := R) (P := P) M s m Φ ≤ q) :
    ∃ n' : ℕ, ∃ m' : M, ∃ Ψ : Fin n' → P →ₗ[R] (R ⧸ Ring.jacobson R),
      realized_evalIdeal (R := R) (P := P) M s m Φ <
        realized_evalIdeal (R := R) (P := P) M s m' Ψ := by
  let x : P := s + m
  obtain ⟨φ, hφ⟩ := exists_lift_family_of_quotient_linearForms (R := R) (P := P) Φ
  let K : Submodule R P := M ⊓ ⨅ i, LinearMap.ker (φ i)
  -- Route correction: the enlargement step has to pass through lifts of the quotient-valued
  -- family before applying the finite-quotient kernel control from the source proof.
  have hxspan : R ∙ x + M = ⊤ := by
    -- Replacing `s` by `s + m` does not change the cyclic span modulo `M` because `m ∈ M`.
    refine top_unique ?_
    rw [← hspan]
    refine sup_le ?_ le_sup_right
    refine (Submodule.span_singleton_le_iff_mem s (R ∙ x + M)).2 ?_
    dsimp [x]
    refine Submodule.mem_sup.mpr ?_
    refine ⟨s + m, ?_, -(m : P), ?_, ?_⟩
    · exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
    · simpa using M.neg_mem m.2
    · simp
  have hfiniteQuot : Module.Finite R (P ⧸ K) := by
    -- TODO: after the Jacobson-quotient reduction, replace this with the Noetherian version of
    -- `finite_quotient_of_intersection_kernel` on the reduced module `P / J P`; the current
    -- original-ring statement is not available without an explicit Noetherian bridge.
    sorry
  suffices hseparator :
      ∃ k : P, k ∈ K ∧
        ∃ ψ : P →ₗ[R] (R ⧸ Ring.jacobson R), ψ (x + k) ∉ q by
    rcases hseparator with ⟨k, hkK, ψ, hψ⟩
    let m' : M := ⟨(m : P) + k, M.add_mem m.2 hkK.1⟩
    have hold :
        realized_evalIdeal (R := R) (P := P) M s m Φ =
          realized_evalIdeal (R := R) (P := P) M s m' Φ := by
      -- A perturbation by an element of the lifted common kernel preserves all old evaluations.
      simpa [m'] using
        realized_evalIdeal_eq_of_add_mem_lifted_common_kernel
          (R := R) (P := P) M s m Φ φ hφ hkK
    have houtside : ψ (s + m') ∉ q := by
      -- The local separator is already phrased on `x + k`, and `m'` was defined to realize that
      -- perturbation globally.
      simpa [x, m', add_assoc] using hψ
    obtain ⟨Ψ, hlt⟩ :=
      exists_strictly_larger_realized_evalIdeal_of_new_eval_not_mem
        (R := R) (P := P) M s m Φ hcontained m' hold ψ houtside
    exact ⟨n + 1, m', Ψ, hlt⟩
  -- The remaining source-faithful gap is exactly the local closed-fiber separator packaged in the
  -- dedicated helper above.
  simpa [x, K] using
    closed_fiber_common_kernel_separator_data
      (R := R) (P := P) M s hP m Φ φ hφ hqmax hcontained hfiniteQuot

/-- Helper for Lemma 15.129.4: after reducing modulo the Jacobson radical, the remaining source
argument is a Noetherian descent on realized vanishing loci `Z(s + m, Φ)`. -/
lemma exists_linearForm_eval_one_mod_jacobson_of_isNoetherianRing
    (M : Submodule R P) (s : P)
    (hP : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P))
    (hspan : R ∙ s + M = ⊤) :
    ∃ m : M, ∃ φbar : P →ₗ[R] (R ⧸ Ring.jacobson R), φbar (s + m) = 1 := by
  -- Route correction: the source proof works directly with realized evaluation ideals in
  -- `R ⧸ Ring.jacobson R`, so the global invariant should be chosen before the local enlargement.
  obtain ⟨n, m, Φ, hmax⟩ := exists_maximal_realized_evalIdeal (R := R) (P := P) M s
  by_cases htop :
      realized_evalIdeal (R := R) (P := P) M s m Φ = ⊤
  · -- If the maximal realized ideal is already the unit ideal, collapse the finite family to one
    -- linear form with value `1`.
    exact ⟨m,
      exists_linearForm_eval_one_of_realized_evalIdeal_eq_top (R := R) (P := P) M s m Φ htop⟩
  · -- Otherwise a maximal ideal above it exists, and the missing source-faithful step is to
    -- enlarge the realized ideal strictly inside that maximal point.
    obtain ⟨q, hqmax, hcontained⟩ :=
      exists_maximalIdeal_over_proper_realized_evalIdeal (R := R) (P := P) M s m Φ htop
    obtain ⟨n', m', Ψ, hlt⟩ :=
      exists_strictly_larger_realized_evalIdeal
        (R := R) (P := P) M s hP hspan m Φ hqmax hcontained
    have heq :
        realized_evalIdeal (R := R) (P := P) M s m' Ψ =
          realized_evalIdeal (R := R) (P := P) M s m Φ :=
      hmax hlt.le
    exact (hlt.ne heq.symm).elim

-- Proof sketch: reduce modulo the Jacobson radical and work over the Noetherian quotient `R ⧸
-- Ring.jacobson R`, where a Noetherian-induction argument on closed subsets of `Spec R` produces a
-- perturbation `s + m` together with a splitting `P →ₗ[R] R`. That splitting identifies the cyclic
-- span of `s + m` with a free direct summand of `P`.
/-- Lemma 15.129.4: if `R ⧸ Ring.jacobson R` is Noetherian, `P` is a projective `R`-module whose
localizations at maximal ideals are not finitely generated, and `s` together with the submodule
`M` generates `P`, then there exists a perturbation `m : M` such that the cyclic submodule
generated by `s + m` is itself a free direct summand of `P`, expressed directly by the properties
`IsComplemented (R ∙ (s + m))` and `Module.Free R (R ∙ (s + m))`; its finiteness is the canonical
cyclic-span finiteness consequence and need not be carried as extra data. -/
@[stacks 0GVI]
theorem exists_perturbation_with_cyclicSpan_free_directSummand
    (M : Submodule R P) (s : P)
    (hP : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P))
    (hspan : R ∙ s + M = ⊤) :
    ∃ m : M, IsComplemented (R ∙ (s + m)) ∧ Module.Free R (R ∙ (s + m)) := by
  -- Route correction: the proved closing layer is isolated, so the remaining blocker is exactly
  -- the Jacobson-quotient perturbation theorem from the source proof.
  have hquot : ∃ m : M, ∃ φbar : P →ₗ[R] (R ⧸ Ring.jacobson R), φbar (s + m) = 1 :=
    exists_linearForm_eval_one_mod_jacobson_of_isNoetherianRing M s hP hspan
  have hunit : ∃ m : M, ∃ φ : P →ₗ[R] R, IsUnit (φ (s + m)) :=
    exists_unit_linearForm_of_eval_one_mod_jacobson M s hquot
  rcases hunit with ⟨m, φ, hφ⟩
  refine ⟨m, ?_⟩
  -- The remaining step is the already-verified splitting criterion for a unit-valued linear form.
  exact cyclicSpan_free_directSummand_of_exists_unit_linearForm (x := s + m) ⟨φ, hφ⟩

end
