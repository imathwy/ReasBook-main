import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Pointwise

/-
Domain triage:
* primary domain: module length and finite-length principal quotients in dimension-one local
  domains;
* sampled owner API: `Module.length`, `QuotSMulTop`,
  `isFiniteLength_quotient_span_singleton`, and `Ring.KrullDimLE.eq_bot_or_eq_top`;
* core/canonical owners: `QuotSMulTop x M` for the quotient module and
  `IsFiniteLength R (R ⧸ Ideal.span ({x} : Set R))` for the principal quotient;
* layer split: `QuotSMulTop x M` and the finite-length owner theorem for `R / xR` are primitive,
  while the Stacks inequality is the derived source-facing API.
-/

section

variable {R : Type u} {K : Type v}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Ring.KrullDimLE 1 R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

-- Proof sketch: if `x = 0`, then `QuotSMulTop x M = M`, while in a local domain of Krull
-- dimension at most `1` the zero-dimensional case is a field and the one-dimensional case makes
-- the right-hand side trivially `⊤`; so the inequality is immediate. If `x` is a unit then
-- `QuotSMulTop x M` vanishes. Otherwise `x` lies in the maximal ideal, and the canonical theorem
-- `isFiniteLength_quotient_span_singleton` gives finite length for `R / xR`. For a finite
-- submodule
-- `M ⊆ K^r`, clear denominators to compare `M` with `R^r`, use the filtration by powers of `x`,
-- and compute the asymptotic length growth inside `R^r`. For general `M`, choose a finite
-- submodule whose quotient modulo `x` has any prescribed finite-length subquotient and reduce to
-- the finite case.
/-
Canonical background: in the present dimension-one local-domain setting, the principal
quotient `R / xR` has finite length. This is exactly the owner theorem
`isFiniteLength_quotient_span_singleton`.
-/
recall isFiniteLength_quotient_span_singleton

omit [IsLocalRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 10.119.9: if `R` is not a field, then `R` has infinite length as an
`R`-module. -/
lemma length_ring_eq_top_of_not_isField (hR : ¬ IsField R) :
    Module.length R R = ⊤ := by
  -- A finite-length domain is Artinian, hence a field; this contradicts `hR`.
  by_contra hlen
  have hfinite : IsFiniteLength R R := Module.length_ne_top_iff.mp hlen
  have hart : IsArtinian R R := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2
  let _ : IsArtinianRing R := hart
  haveI : Ring.KrullDimLE 0 R := (isArtinianRing_iff_krullDimLE_zero).mp ‹IsArtinianRing R›
  exact hR Ring.KrullDimLE.isField_of_isDomain

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 10.119.9: the quotient of a finite free module by `x` is the corresponding
product of `R / (x)`, so its length is the rank times `length_R (R / xR)`. -/
lemma length_quotSMulTop_pi_free {x : R} (s : ℕ) :
    Module.length R (QuotSMulTop x (Fin s → R)) =
      s * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
  -- Rewrite the quotient of the product coordinatewise, then sum the coordinate lengths.
  let p : Fin s → Submodule R R := fun _ => x • (⊤ : Submodule R R)
  have hquot :
      ((Fin s → R) ⧸ Submodule.pi Set.univ p) ≃ₗ[R] (∀ i : Fin s, R ⧸ p i) :=
    Submodule.quotientPi p
  have hsmul :
      (x • (⊤ : Submodule R (Fin s → R))) = Submodule.pi Set.univ p := by
    ext f
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, p]
    constructor
    · intro hf
      rw [Submodule.mem_smul_pointwise_iff_exists] at hf
      rcases hf with ⟨g, -, rfl⟩
      intro i
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨g i, Submodule.mem_top, rfl⟩
    · intro hf
      rw [Submodule.mem_smul_pointwise_iff_exists]
      choose g hg using fun i => (Submodule.mem_smul_pointwise_iff_exists (m := f i) (a := x)
        (S := (⊤ : Submodule R R))).mp (hf i)
      refine ⟨g, Submodule.mem_top, ?_⟩
      ext i
      exact (hg i).2
  rw [LinearEquiv.length_eq (Submodule.quotEquivOfEq _ _ hsmul ≪≫ₗ hquot), Module.length_pi_of_fintype]
  have hsum :
      (∑ i : Fin s, Module.length R (R ⧸ p i)) =
        s • Module.length R (R ⧸ x • (⊤ : Submodule R R)) := by
    change Finset.univ.sum (fun _ : Fin s => Module.length R (R ⧸ x • (⊤ : Submodule R R))) =
      s • Module.length R (R ⧸ x • (⊤ : Submodule R R))
    rw [Finset.sum_const, Finset.card_univ]
    simpa using congrArg (fun n : ℕ => n • Module.length R (R ⧸ x • (⊤ : Submodule R R)))
      (Fintype.card_fin s)
  have hspan :
      Module.length R (R ⧸ x • (⊤ : Submodule R R)) =
        Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
    simpa [Submodule.ideal_span_singleton_smul] using
      (LinearEquiv.length_eq
        (Submodule.quotEquivOfEq (x • (⊤ : Submodule R R)) (Ideal.span ({x} : Set R))
          (by simpa using (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R R)).symm)) : _)
  rw [hspan] at hsum
  simpa [nsmul_eq_mul] using hsum

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 10.119.9: if `R` is a field, then the ambient module `K^{\oplus r}` has
length `r` over `R`. -/
lemma length_pi_fractionRing_eq_rank_of_isField {r : ℕ} (hfield : IsField R) :
    Module.length R (Fin r → K) = r := by
  -- Surjectivity of `R → K` lets us compute the length over `R` via the ambient `K`-vector-space
  -- structure.
  have hsurj : Function.Surjective (algebraMap R K) :=
    (IsFractionRing.surjective_iff_isField (R := R) (K := K)).mpr hfield
  calc
    Module.length R (Fin r → K) = Module.length K (Fin r → K) := by
      simpa using
        (Module.length_eq_of_surjective (S := R) (R := K) (M := Fin r → K) hsurj)
    _ = r := by
      simpa using (Module.length_eq_finrank K (Fin r → K))

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsFractionRing R K] in
/-- Helper for Lemma 10.119.9: any finite set of classes in `QuotSMulTop x M` already comes from
some finite submodule of `M`. -/
lemma finite_set_liftable_along_quotSMulTop_map
    {r : ℕ} (M : Submodule R (Fin r → K)) {x : R} (t : Finset (QuotSMulTop x M)) :
    ∃ M0 : Submodule R (Fin r → K), ∃ h : M0 ≤ M, Module.Finite R M0 ∧
      ∀ y ∈ t, ∃ z : QuotSMulTop x M0, QuotSMulTop.map x (Submodule.inclusion h) z = y := by
  classical
  -- Choose one representative in `M` for each class in the finite set.
  let rep : {y // y ∈ t} → M :=
    fun u ↦ Classical.choose (Submodule.Quotient.mk_surjective (x • (⊤ : Submodule R M)) u.1)
  have hrep :
      ∀ u : {y // y ∈ t},
        (Submodule.Quotient.mk (rep u) : QuotSMulTop x M) = u.1 := by
    intro u
    exact Classical.choose_spec
      (Submodule.Quotient.mk_surjective (x • (⊤ : Submodule R M)) u.1)
  let M0 : Submodule R (Fin r → K) :=
    Submodule.span R (Set.range fun u : {y // y ∈ t} ↦ ((rep u : M) : Fin r → K))
  have hM0 : M0 ≤ M := by
    -- The spanning generators already lie in `M`, so the whole span does as well.
    refine Submodule.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨u, rfl⟩
    exact (rep u).property
  refine ⟨M0, hM0, ?_, ?_⟩
  · -- A span of finitely many generators is a finite module.
    exact Module.Finite.of_fg <| by
      simpa [M0] using
        (Submodule.fg_span (R := R)
          (Set.finite_range fun u : {y // y ∈ t} ↦ ((rep u : M) : Fin r → K)))
  · intro y hy
    let u : {y // y ∈ t} := ⟨y, hy⟩
    -- Use the chosen representative of `y` as a class in the finite span `M0`.
    refine ⟨Submodule.Quotient.mk ⟨((rep u : M) : Fin r → K), ?_⟩, ?_⟩
    · exact Submodule.subset_span ⟨u, rfl⟩
    · -- The quotient functor sends that chosen representative back to the original class.
      rw [QuotSMulTop.map_apply_mk]
      have hincl :
          (Submodule.inclusion hM0)
              ⟨((rep u : M) : Fin r → K), Submodule.subset_span ⟨u, rfl⟩⟩ = rep u := by
        ext
        rfl
      rw [hincl]
      simpa [u] using hrep u

omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 10.119.9: multiplying a lattice in `K^s` by a nonzero scalar does not change
the length of the quotient modulo `x`. -/
lemma length_quotSMulTop_smul_eq
    {s : ℕ} {L : Submodule R (Fin s → K)} {x a : R} (ha : a ≠ 0) :
    Module.length R (QuotSMulTop x ((a • L : Submodule R (Fin s → K)))) =
      Module.length R (QuotSMulTop x L) := by
  let aK : K := algebraMap R K a
  have haK : aK ≠ 0 := by
    intro haK0
    exact ha ((IsFractionRing.injective R K) <| by simpa [aK] using haK0)
  let eK : (Fin s → K) ≃ₗ[K] (Fin s → K) :=
    LinearEquiv.smulOfNeZero (K := K) (M := Fin s → K) aK haK
  let eR : (Fin s → K) ≃ₗ[R] (Fin s → K) := eK.restrictScalars R
  have hmap : L.map eR.toLinearMap = a • L := by
    -- The transport equivalence is multiplication by `a`, so its image is the pointwise scalar
    -- multiple of `L`.
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz, rfl⟩
      rw [Submodule.mem_smul_pointwise_iff_exists]
      refine ⟨z, hz, ?_⟩
      ext i
      simp [eR, eK, aK, Algebra.smul_def]
    · intro hy
      rw [Submodule.mem_smul_pointwise_iff_exists] at hy
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      ext i
      simp [eR, eK, aK, Algebra.smul_def]
  -- Apply the quotient functor to the scalar-multiplication equivalence on the ambient space.
  have hlen :
      Module.length R (QuotSMulTop x L) =
        Module.length R (QuotSMulTop x (L.map eR.toLinearMap)) := by
    simpa using
      (LinearEquiv.length_eq
        (QuotSMulTop.congr x (Submodule.equivMapOfInjective eR.toLinearMap eR.injective L)) :
          Module.length R (QuotSMulTop x L) =
            Module.length R (QuotSMulTop x (L.map eR.toLinearMap)))
  rw [hmap] at hlen
  exact hlen.symm

/-- Helper for Lemma 10.119.9: the coordinatewise algebra-map inclusion embeds `R^s` into `K^s`.
-/
abbrev fractionFieldPiInclusion (s : ℕ) : (Fin s → R) →ₗ[R] (Fin s → K) :=
  LinearMap.piMap fun _ : Fin s => Algebra.linearMap R K

omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 10.119.9: a finite lattice in `K^s` can be cleared into the coordinate image
of an actual `R^s`-submodule after multiplying by one nonzero scalar. -/
lemma exists_nonzero_scalar_map_pi_eq_smul_of_finite
    {s : ℕ} (L : Submodule R (Fin s → K)) (hLfinite : Module.Finite R L) :
    ∃ a : R, a ≠ 0 ∧ ∃ N : Submodule R (Fin s → R),
      N.map (fractionFieldPiInclusion (R := R) (K := K) s) = a • L := by
  classical
  rw [Module.Finite.iff_fg] at hLfinite
  rcases hLfinite with ⟨t, ht⟩
  let g : t → Fin s → K := fun i ↦ (i : Fin s → K)
  let coords : t × Fin s → K := fun ij ↦ g ij.1 ij.2
  obtain ⟨a', ha'⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors R) coords
  let a : R := a'
  have ha : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a'.property
  have hcoords :
      ∀ i : t, ∀ j : Fin s, ∃ r : R, algebraMap R K r = a • g i j := by
    intro i j
    exact ha' (i, j)
  choose w hw using hcoords
  let v : t → Fin s → R := fun i j ↦ w i j
  let N : Submodule R (Fin s → R) := Submodule.span R (Set.range v)
  have hv :
      ∀ i : t,
        fractionFieldPiInclusion (R := R) (K := K) s (v i) = a • (i : Fin s → K) := by
    intro i
    ext j
    exact hw i j
  have hspanL : Submodule.span R (Set.range g) = L := by
    -- Rewrite the finite generator family as a ranged map from the finite set `t`.
    simpa [g, Set.image_eq_range] using ht
  have hmapRange :
      fractionFieldPiInclusion (R := R) (K := K) s '' Set.range v =
        Set.range fun i : t ↦ a • (i : Fin s → K) := by
    ext y
    constructor
    · rintro ⟨i, ⟨j, rfl⟩, hy⟩
      refine ⟨j, ?_⟩
      exact (hv j).symm.trans hy
    · rintro ⟨i, rfl⟩
      refine ⟨v i, ⟨i, rfl⟩, hv i⟩
  have hscaled :
      Submodule.span R (Set.range fun i : t ↦ a • (i : Fin s → K)) = a • L := by
    calc
      Submodule.span R (Set.range fun i : t ↦ a • (i : Fin s → K)) =
          Submodule.span R (a • Set.range g) := by
            rw [Set.smul_set_range]
      _ = a • Submodule.span R (Set.range g) := by
            rw [Submodule.smul_span]
      _ = a • L := by rw [hspanL]
  refine ⟨a, ha, N, ?_⟩
  -- The image of the cleared generators is exactly the scalar multiple `a • L`.
  calc
    N.map (fractionFieldPiInclusion (R := R) (K := K) s) =
        Submodule.span R (fractionFieldPiInclusion (R := R) (K := K) s '' Set.range v) := by
          change
            Submodule.map (fractionFieldPiInclusion (R := R) (K := K) s)
              (Submodule.span R (Set.range v)) =
              Submodule.span R
                (fractionFieldPiInclusion (R := R) (K := K) s '' Set.range v)
          rw [Submodule.map_span]
    _ = Submodule.span R (Set.range fun i : t ↦ a • (i : Fin s → K)) := by
          rw [hmapRange]
    _ = a • L := hscaled

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsFractionRing R K] in
/-- Helper for Lemma 10.119.9: once the source finite-case estimate is known for finite
submodules of `K^{\oplus r}`, the general case follows by lifting a finite strict chain in
`M / xM` to a finite submodule of `M`. -/
lemma length_quotSMulTop_le_of_finite_case
    {r : ℕ} (M : Submodule R (Fin r → K)) {x : R}
    (hfinite_case :
      ∀ M0 : Submodule R (Fin r → K), M0 ≤ M → Module.Finite R M0 →
        Module.length R (QuotSMulTop x M0) ≤
          r * Module.length R (R ⧸ Ideal.span ({x} : Set R))) :
    Module.length R (QuotSMulTop x M) ≤
      r * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
  classical
  -- Control the module length through arbitrary finite strict chains in the quotient lattice.
  rw [Module.length_eq_height]
  apply Order.height_le
  intro p hp_last
  let witness : Fin p.length → QuotSMulTop x M :=
    fun i ↦ Classical.choose
      (SetLike.exists_of_lt (show p (Fin.castSucc i) < p i.succ from p.step i))
  have hwitness_mem_upper :
      ∀ i : Fin p.length, witness i ∈ p i.succ := by
    intro i
    exact (Classical.choose_spec
      (SetLike.exists_of_lt (show p (Fin.castSucc i) < p i.succ from p.step i))).1
  have hwitness_not_mem_lower :
      ∀ i : Fin p.length, witness i ∉ p (Fin.castSucc i) := by
    intro i
    exact (Classical.choose_spec
      (SetLike.exists_of_lt (show p (Fin.castSucc i) < p i.succ from p.step i))).2
  let t : Finset (QuotSMulTop x M) := Finset.univ.image witness
  have hwitness_mem_t : ∀ i : Fin p.length, witness i ∈ t := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨M0, hM0, hM0finite, hlift⟩ :=
    finite_set_liftable_along_quotSMulTop_map (R := R) (K := K) M t
  let f : QuotSMulTop x M0 →ₗ[R] QuotSMulTop x M :=
    QuotSMulTop.map x (Submodule.inclusion hM0)
  let lift : Fin p.length → QuotSMulTop x M0 :=
    fun i ↦ Classical.choose (hlift (witness i) (hwitness_mem_t i))
  have hlift_spec : ∀ i : Fin p.length, f (lift i) = witness i := by
    intro i
    exact Classical.choose_spec (hlift (witness i) (hwitness_mem_t i))
  let q : LTSeries (Submodule R (QuotSMulTop x M0)) := {
    length := p.length
    toFun := fun i ↦ Submodule.comap f (p i)
    step := by
      intro i
      -- Pull back the strict step in `p` using the chosen lift of a witness outside the lower
      -- term of the chain.
      change Submodule.comap f (p (Fin.castSucc i)) < Submodule.comap f (p i.succ)
      apply lt_of_le_of_ne
      · exact Submodule.comap_mono (le_of_lt (show p (Fin.castSucc i) < p i.succ from p.step i))
      · intro hEq
        have hlift_upper : lift i ∈ Submodule.comap f (p i.succ) := by
          simpa [Submodule.mem_comap, hlift_spec i] using hwitness_mem_upper i
        have hlift_lower : lift i ∈ Submodule.comap f (p (Fin.castSucc i)) := by
          simpa [hEq] using hlift_upper
        exact hwitness_not_mem_lower i <| by
          simpa [Submodule.mem_comap, hlift_spec i] using hlift_lower }
  have hq_length :
      (q.length : ℕ∞) ≤ Module.length R (QuotSMulTop x M0) := by
    -- The pulled-back chain has the same length and ends at the top submodule of the finite
    -- quotient, so its length is bounded by the height of that top element.
    calc
      (q.length : ℕ∞) ≤ Order.height q.last := Order.length_le_height_last (p := q)
      _ = Order.height (Submodule.comap f p.last) := by
        rfl
      _ = Order.height (⊤ : Submodule R (QuotSMulTop x M0)) := by
        rw [hp_last]
        simp
      _ = Module.length R (QuotSMulTop x M0) := by
        simpa [Module.length_eq_height]
  have hp_length :
      (p.length : ℕ∞) ≤ Module.length R (QuotSMulTop x M0) := by
    simpa [q] using hq_length
  exact le_trans hp_length (hfinite_case M0 hM0 hM0finite)

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 9: the coordinatewise fraction-field inclusion localizes the
finite product `R^s` at the nonzero divisors of `R`. -/
lemma isLocalizedModule_fractionFieldPiInclusion (s : ℕ) :
    IsLocalizedModule (nonZeroDivisors R) (fractionFieldPiInclusion (R := R) (K := K) s) := by
  -- Compare the product with finitely supported functions, where localization is already
  -- available coordinatewise.
  rw [← show
      ((Finsupp.linearEquivFunOnFinite R K (Fin s)).toLinearMap ∘ₗ
        Finsupp.mapRange.linearMap (Algebra.linearMap R K) ∘ₗ
        (Finsupp.linearEquivFunOnFinite R R (Fin s)).symm.toLinearMap) =
        fractionFieldPiInclusion (R := R) (K := K) s by
    ext x i
    rfl]
  infer_instance

omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 9: full fraction-field span of a submodule of `R^s`
contains a nonzero scalar multiple of the standard lattice. -/
lemma exists_nonzero_smul_top_le_of_full_fraction_span
    {s : ℕ} (N : Submodule R (Fin s → R))
    (hspan :
      Submodule.span K
        (((N.map (fractionFieldPiInclusion (R := R) (K := K) s)) :
          Submodule R (Fin s → K)) : Set (Fin s → K)) = ⊤) :
    ∃ a : R, a ≠ 0 ∧ a • (⊤ : Submodule R (Fin s → R)) ≤ N := by
  classical
  let ι := fractionFieldPiInclusion (R := R) (K := K) s
  let S : Set (Fin s → K) := ((N.map ι : Submodule R (Fin s → K)) : Set (Fin s → K))
  obtain ⟨bset, hb_subset, hb_span, hb_li⟩ := exists_linearIndependent K S
  have hb_top : Submodule.span K (bset : Set (Fin s → K)) = ⊤ := by
    -- Extract a basis from the spanning subset of the localized lattice.
    calc
      Submodule.span K (bset : Set (Fin s → K)) = Submodule.span K S := hb_span
      _ = ⊤ := by simpa [S, ι] using hspan
  haveI : Fintype bset := Set.Finite.fintype hb_li.finite
  let b : Module.Basis bset K (Fin s → K) :=
    Module.Basis.mk hb_li (by
      rw [← hb_top]
      exact Submodule.span_mono fun y hy ↦ ⟨⟨y, hy⟩, rfl⟩)
  let coeff : Fin s × bset → K :=
    fun p ↦ b.repr (ι (Pi.single p.1 (1 : R))) p.2
  obtain ⟨a', ha'⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors R) coeff
  let a : R := a'
  have ha : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a'.property
  let numerator : Fin s × bset → R := fun p ↦ Classical.choose (ha' p)
  have hnumerator :
      ∀ p : Fin s × bset, algebraMap R K (numerator p) = a • coeff p := by
    intro p
    exact Classical.choose_spec (ha' p)
  let preimage : bset → N := fun j ↦
    ⟨Classical.choose (show (j : Fin s → K) ∈ N.map ι from hb_subset j.property),
      (Classical.choose_spec
        (show (j : Fin s → K) ∈ N.map ι from hb_subset j.property)).1⟩
  have hpreimage : ∀ j : bset, ι (preimage j : Fin s → R) = (j : Fin s → K) := by
    intro j
    exact (Classical.choose_spec
      (show (j : Fin s → K) ∈ N.map ι from hb_subset j.property)).2
  have hι_injective : Function.Injective ι := by
    intro y z hyz
    ext i
    exact IsFractionRing.injective R K (congrFun hyz i)
  have hstd_mem : ∀ i : Fin s, a • (Pi.single i (1 : R) : Fin s → R) ∈ N := by
    intro i
    let evec : Fin s → R := Pi.single i (1 : R)
    let v : Fin s → R :=
      ∑ j : bset, numerator (i, j) • (preimage j : Fin s → R)
    have hv_mem : v ∈ N := by
      -- The cleared basis expansion is an `R`-linear combination of elements of `N`.
      dsimp [v]
      exact Submodule.sum_mem N fun j _ ↦
        Submodule.smul_mem N (numerator (i, j)) (preimage j).property
    have hbasis_sum :
        (∑ j : bset, b.repr (ι evec) j • (j : Fin s → K)) =
          ι evec := by
      simpa [b, Module.Basis.mk_apply] using b.sum_repr (ι evec)
    have hv_image : ι v = a • ι evec := by
      -- Map the cleared `R`-linear combination to `K^s` and compare with the basis expansion.
      calc
        ι v =
            ∑ j : bset, ι (numerator (i, j) • (preimage j : Fin s → R)) := by
              simp [v, map_sum]
        _ = ∑ j : bset, (algebraMap R K (numerator (i, j))) • (j : Fin s → K) := by
              simp [hpreimage, ι]
        _ = ∑ j : bset, (a • coeff (i, j)) • (j : Fin s → K) := by
              simp [hnumerator]
        _ = a • ∑ j : bset, b.repr (ι evec) j • (j : Fin s → K) := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _
              dsimp [coeff, evec]
              rw [smul_assoc]
        _ = a • ι evec := by
              rw [hbasis_sum]
    have hv_eq : v = a • evec := by
      apply hι_injective
      simpa [ι] using hv_image
    simpa [hv_eq] using hv_mem
  refine ⟨a, ha, ?_⟩
  -- Once every standard basis vector has a cleared multiple in `N`, every vector does.
  intro y hy
  rw [Submodule.mem_smul_pointwise_iff_exists] at hy
  rcases hy with ⟨z, -, rfl⟩
  have hz :
      a • z = ∑ i : Fin s, z i • (a • (Pi.single i (1 : R) : Fin s → R)) := by
    -- Reconstruct the vector coordinatewise from the standard basis after scaling.
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro j _ hji
      have hsingle : (Pi.single j (1 : R) : Fin s → R) i = 0 :=
        Pi.single_eq_of_ne (M := fun _ : Fin s ↦ R) (i := j) (i' := i) (Ne.symm hji) (1 : R)
      simpa [Pi.smul_apply, hsingle]
    · simp
  rw [hz]
  exact Submodule.sum_mem N fun i _ ↦ Submodule.smul_mem N (z i) (hstd_mem i)

/-- Helper for Chap10 Lemma 10 119 9: a submodule of `R^s` containing a nonzero scalar
multiple of the whole lattice has finite-length quotient. -/
lemma isFiniteLength_quotient_pi_of_nonzero_smul_top_le
    {s : ℕ} {N : Submodule R (Fin s → R)} {a : R} (ha : a ≠ 0)
    (haN : a • (⊤ : Submodule R (Fin s → R)) ≤ N) :
    IsFiniteLength R ((Fin s → R) ⧸ N) := by
  -- The quotient by `N` is a quotient of the finite-length module `(R^s)/(aR^s)`.
  let q : QuotSMulTop a (Fin s → R) →ₗ[R] (Fin s → R) ⧸ N :=
    Submodule.mapQ (a • (⊤ : Submodule R (Fin s → R))) N LinearMap.id (by
      simpa using haN)
  have hq_surj : Function.Surjective q := by
    intro y
    rcases Submodule.mkQ_surjective N y with ⟨z, rfl⟩
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hbase :
      Module.length R (R ⧸ Ideal.span ({a} : Set R)) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr ha))
  have hfree_len : Module.length R (QuotSMulTop a (Fin s → R)) ≠ ⊤ := by
    rw [length_quotSMulTop_pi_free (R := R) (x := a) s]
    exact WithTop.mul_ne_top (ENat.coe_ne_top s) hbase
  exact IsFiniteLength.of_surjective (Module.length_ne_top_iff.mp hfree_len) hq_surj

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 9: the length of a module splits into the length of the
kernel and the range of any linear map. -/
lemma length_eq_add_length_range
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Module.length R M = Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) := by
  -- Replace `f` by its surjective codomain restriction to the range.
  let fr : M →ₗ[R] LinearMap.range f :=
    f.codRestrict (LinearMap.range f) fun x ↦ ⟨x, rfl⟩
  have hfr_surj : Function.Surjective fr := by
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hker : LinearMap.ker fr = LinearMap.ker f := by
    ext x
    simp [fr]
  have hexact : Function.Exact (LinearMap.ker f).subtype fr := by
    rw [← hker]
    exact LinearMap.exact_subtype_ker_map fr
  exact Module.length_eq_add_of_exact (LinearMap.ker f).subtype fr Subtype.val_injective
    hfr_surj hexact

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 9: on a finite-length module, the kernel and cokernel of
multiplication by a scalar have the same length. -/
lemma length_ker_lsmul_eq_length_quotSMulTop_of_finiteLength
    {Q : Type*} [AddCommGroup Q] [Module R Q] (hQ : IsFiniteLength R Q) (x : R) :
    Module.length R (LinearMap.ker (LinearMap.lsmul R Q x)) =
      Module.length R (QuotSMulTop x Q) := by
  let l : Q →ₗ[R] Q := LinearMap.lsmul R Q x
  have hlength_range :
      Module.length R Q =
        Module.length R (LinearMap.ker l) + Module.length R (LinearMap.range l) :=
    length_eq_add_length_range (R := R) l
  have hlength_quot :
      Module.length R Q =
        Module.length R (LinearMap.range l) + Module.length R (QuotSMulTop x Q) := by
    have hrange : LinearMap.range l = x • (⊤ : Submodule R Q) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact Submodule.smul_mem_pointwise_smul z x ⊤ trivial
      · intro hy
        rw [Submodule.mem_smul_pointwise_iff_exists] at hy
        rcases hy with ⟨z, -, rfl⟩
        exact ⟨z, rfl⟩
    let q : Q →ₗ[R] QuotSMulTop x Q := (x • (⊤ : Submodule R Q)).mkQ
    have hexact : Function.Exact (LinearMap.range l).subtype q := by
      rw [hrange]
      -- The range of multiplication is exactly the kernel of the quotient map.
      intro y
      constructor
      · intro hy
        refine ⟨⟨y, ?_⟩, rfl⟩
        exact (Submodule.Quotient.mk_eq_zero (x • (⊤ : Submodule R Q))).mp hy
      · rintro ⟨z, hz⟩
        rw [← hz]
        exact (Submodule.Quotient.mk_eq_zero (x • (⊤ : Submodule R Q))).mpr z.property
    exact Module.length_eq_add_of_exact (LinearMap.range l).subtype q Subtype.val_injective
      (Submodule.mkQ_surjective _) hexact
  have hrange_finite : Module.length R (LinearMap.range l) ≠ ⊤ := by
    exact Module.length_ne_top_iff.mpr
      (IsFiniteLength.of_injective (f := (LinearMap.range l).subtype) hQ
        Subtype.val_injective)
  apply WithTop.add_right_cancel hrange_finite
  calc
    Module.length R (LinearMap.ker l) + Module.length R (LinearMap.range l) =
        Module.length R Q := hlength_range.symm
    _ = Module.length R (LinearMap.range l) + Module.length R (QuotSMulTop x Q) :=
        hlength_quot
    _ = Module.length R (QuotSMulTop x Q) + Module.length R (LinearMap.range l) := by
        rw [add_comm]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Chap10 Lemma 10 119 9: a submodule with finite-length cokernel has the same
modulo-`x` length as the ambient module when multiplication by `x` is regular on the ambient
module. -/
lemma length_quotSMulTop_eq_of_submodule_finite_quotient
    {F : Type*} [AddCommGroup F] [Module R F] (N : Submodule R F) {x : R}
    (hxF : IsSMulRegular F x) (hQ : IsFiniteLength R (F ⧸ N)) :
    Module.length R (QuotSMulTop x N) = Module.length R (QuotSMulTop x F) := by
  classical
  let Q : Type _ := F ⧸ N
  let i : N →ₗ[R] F := N.subtype
  let q : F →ₗ[R] Q := N.mkQ
  let lN : N →ₗ[R] N := LinearMap.lsmul R N x
  let lF : F →ₗ[R] F := LinearMap.lsmul R F x
  let lQ : Q →ₗ[R] Q := LinearMap.lsmul R Q x
  let πN : N →ₗ[R] QuotSMulTop x N := (x • (⊤ : Submodule R N)).mkQ
  let πF : F →ₗ[R] QuotSMulTop x F := (x • (⊤ : Submodule R F)).mkQ
  let α : QuotSMulTop x N →ₗ[R] QuotSMulTop x F := QuotSMulTop.map x i
  let β : QuotSMulTop x F →ₗ[R] QuotSMulTop x Q := QuotSMulTop.map x q
  have hexact : Function.Exact i q := by
    simpa [i, q] using LinearMap.exact_subtype_mkQ N
  have hq_surj : Function.Surjective q := by
    simpa [q] using Submodule.mkQ_surjective N
  have hi_inj : Function.Injective i := by
    simpa [i] using N.injective_subtype
  have h₁ : i.comp lN = lF.comp i := by
    ext n
    rfl
  have h₂ : q.comp lF = lQ.comp q := by
    ext y
    rfl
  have hπN : Function.Exact lN πN := by
    simpa [lN, πN] using LinearMap.exact_smul_id_smul_top_mkQ N x
  have hπF : Function.Exact lF πF := by
    simpa [lF, πF] using LinearMap.exact_smul_id_smul_top_mkQ F x
  let δ : LinearMap.ker lQ →ₗ[R] QuotSMulTop x N :=
    SnakeLemma.δ' lN lF lQ i q hexact i q hexact h₁ h₂ (LinearMap.ker lQ).subtype
      (LinearMap.exact_subtype_ker_map lQ) πN hπN hq_surj hi_inj
  have hαπ : α.comp πN = πF.comp i := by
    simpa [α, πN, πF, i] using QuotSMulTop.map_comp_mkQ x i
  have hδ_left : Function.Exact δ α := by
    -- The snake lemma identifies the kernel of the modulo map with the connecting image.
    simpa [δ, α] using
      SnakeLemma.exact_δ'_left lN lF lQ i q hexact i q hexact h₁ h₂
        (LinearMap.ker lQ).subtype (LinearMap.exact_subtype_ker_map lQ) πN hπN
        πF hπF hq_surj hi_inj α hαπ
        (Submodule.mkQ_surjective (x • (⊤ : Submodule R N)))
  let Fker : LinearMap.ker lF →ₗ[R] LinearMap.ker lQ :=
    (q.comp (LinearMap.ker lF).subtype).codRestrict (LinearMap.ker lQ) (by
      intro y
      calc
        lQ (q y.1) = q (lF y.1) := by
          exact (congrArg (fun f : F →ₗ[R] Q => f y.1) h₂).symm
        _ = 0 := by rw [y.property, map_zero])
  have hFker : q.comp (LinearMap.ker lF).subtype = (LinearMap.ker lQ).subtype.comp Fker := by
    ext y
    rfl
  have hδ_right : Function.Exact Fker δ := by
    simpa [δ, Fker] using
      SnakeLemma.exact_δ'_right lN lF lQ i q hexact i q hexact h₁ h₂
        (LinearMap.ker lF).subtype (LinearMap.exact_subtype_ker_map lF)
        (LinearMap.ker lQ).subtype (LinearMap.exact_subtype_ker_map lQ) πN hπN
        hq_surj hi_inj Fker hFker Subtype.val_injective
  have hδ_inj : Function.Injective δ := by
    -- Regularity on `F` kills the previous kernel term in the snake exact sequence.
    rw [injective_iff_map_eq_zero]
    intro z hz
    rcases (hδ_right z).mp hz with ⟨y, hy⟩
    have hy0 : y = 0 := by
      ext
      exact hxF.right_eq_zero_of_smul (by simpa [lF] using y.property)
    rw [hy0] at hy
    simpa using hy.symm
  have hαβ : Function.Exact α β := by
    simpa [α, β, i, q] using QuotSMulTop.map_exact x hexact hq_surj
  have hβ_surj : Function.Surjective β := by
    simpa [β, q] using QuotSMulTop.map_surjective x hq_surj
  have hlen_kerα :
      Module.length R (LinearMap.ker α) = Module.length R (LinearMap.ker lQ) := by
    calc
      Module.length R (LinearMap.ker α) = Module.length R (LinearMap.range δ) := by
        exact LinearEquiv.length_eq (LinearEquiv.ofEq _ _ hδ_left.linearMap_ker_eq)
      _ = Module.length R (LinearMap.ker lQ) := by
        exact (LinearEquiv.length_eq (LinearEquiv.ofInjective δ hδ_inj)).symm
  have hlen₁ :
      Module.length R (QuotSMulTop x N) =
        Module.length R (LinearMap.ker lQ) + Module.length R (LinearMap.range α) := by
    rw [length_eq_add_length_range (R := R) α, hlen_kerα]
  have hlen₂ :
      Module.length R (QuotSMulTop x F) =
        Module.length R (LinearMap.range α) + Module.length R (QuotSMulTop x Q) := by
    have hkerβ : LinearMap.ker β = LinearMap.range α := hαβ.linearMap_ker_eq
    calc
      Module.length R (QuotSMulTop x F) =
          Module.length R (LinearMap.ker β) + Module.length R (QuotSMulTop x Q) := by
        exact Module.length_eq_add_of_exact (LinearMap.ker β).subtype β
          Subtype.val_injective hβ_surj (LinearMap.exact_subtype_ker_map β)
      _ = Module.length R (LinearMap.range α) + Module.length R (QuotSMulTop x Q) := by
        rw [LinearEquiv.length_eq (LinearEquiv.ofEq _ _ hkerβ)]
  have hKQ :
      Module.length R (LinearMap.ker lQ) = Module.length R (QuotSMulTop x Q) :=
    length_ker_lsmul_eq_length_quotSMulTop_of_finiteLength (R := R) hQ x
  rw [hlen₁, hlen₂, hKQ]
  rw [add_comm]

/-- Helper for Lemma 10.119.9: the remaining finite case is exactly the source denominator-
clearing lattice comparison for finite submodules of `K^{\oplus r}`. -/
lemma length_quotSMulTop_le_rank_mul_length_quotient_of_lattice
    {s : ℕ} (N : Submodule R (Fin s → R))
    (hspan :
      Submodule.span K
        (((N.map (fractionFieldPiInclusion (R := R) (K := K) s)) :
          Submodule R (Fin s → K)) : Set (Fin s → K)) = ⊤)
    {x : R} (hx : x ≠ 0) :
    Module.length R
      (QuotSMulTop x (N.map (fractionFieldPiInclusion (R := R) (K := K) s))) ≤
      s * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
  let ι := fractionFieldPiInclusion (R := R) (K := K) s
  have hι_inj : Function.Injective ι := by
    intro y z hyz
    ext i
    exact IsFractionRing.injective R K (congrFun hyz i)
  have hmap_len :
      Module.length R (QuotSMulTop x (N.map ι)) =
        Module.length R (QuotSMulTop x N) := by
    -- Move from the coordinate image back to the original lattice using injectivity of the
    -- fraction-field inclusion.
    exact
      (LinearEquiv.length_eq
        (QuotSMulTop.congr x (Submodule.equivMapOfInjective ι hι_inj N))).symm
  obtain ⟨a, ha, haN⟩ :=
    exists_nonzero_smul_top_le_of_full_fraction_span (R := R) (K := K) N hspan
  have hQ : IsFiniteLength R ((Fin s → R) ⧸ N) :=
    isFiniteLength_quotient_pi_of_nonzero_smul_top_le (R := R) (ha := ha) haN
  have hxF : IsSMulRegular (Fin s → R) x :=
    IsSMulRegular.of_ne_zero hx
  have hlen_lattice :
      Module.length R (QuotSMulTop x N) =
        Module.length R (QuotSMulTop x (Fin s → R)) :=
    length_quotSMulTop_eq_of_submodule_finite_quotient (R := R) N hxF hQ
  -- The finite-cokernel comparison reduces the lattice to the free module, whose quotient length
  -- is computed coordinatewise.
  calc
    Module.length R (QuotSMulTop x (N.map ι)) =
        Module.length R (QuotSMulTop x N) := hmap_len
    _ = Module.length R (QuotSMulTop x (Fin s → R)) := hlen_lattice
    _ = s * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
      exact length_quotSMulTop_pi_free (R := R) (x := x) s
    _ ≤ s * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := le_rfl

omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 10.119.9: after denominator clearing, the `K`-span is still the whole
ambient `K^s`. -/
lemma span_map_pi_eq_top_of_smul_full_span
    {s : ℕ} {L : Submodule R (Fin s → K)} {a : R} (ha : a ≠ 0)
    {N : Submodule R (Fin s → R)}
    (hNmap : N.map (fractionFieldPiInclusion (R := R) (K := K) s) = a • L)
    (hspan : Submodule.span K (L : Set (Fin s → K)) = ⊤) :
    Submodule.span K
      (((N.map (fractionFieldPiInclusion (R := R) (K := K) s)) :
        Submodule R (Fin s → K)) : Set (Fin s → K)) = ⊤ := by
  let aK : K := algebraMap R K a
  have haK : aK ≠ 0 := by
    intro haK
    exact ha ((IsFractionRing.injective R K) <| by simpa [aK] using haK)
  let e : (Fin s → K) ≃ₗ[K] (Fin s → K) :=
    LinearEquiv.smulOfNeZero (K := K) (M := Fin s → K) aK haK
  have himage :
      e '' (L : Set (Fin s → K)) =
        (((a • L : Submodule R (Fin s → K)) : Submodule R (Fin s → K)) : Set (Fin s → K)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change e z ∈ (a • L : Submodule R (Fin s → K))
      rw [Submodule.mem_smul_pointwise_iff_exists]
      refine ⟨z, hz, ?_⟩
      ext i
      simp [e, aK, Algebra.smul_def]
    · intro hy
      change y ∈ (a • L : Submodule R (Fin s → K)) at hy
      rw [Submodule.mem_smul_pointwise_iff_exists] at hy
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      ext i
      simp [e, aK, Algebra.smul_def]
  -- Transport the spanning equality across the nonzero scalar automorphism.
  calc
    Submodule.span K
        (((N.map (fractionFieldPiInclusion (R := R) (K := K) s)) :
          Submodule R (Fin s → K)) : Set (Fin s → K)) =
        Submodule.span K ((((a • L : Submodule R (Fin s → K)) :
          Submodule R (Fin s → K)) : Set (Fin s → K))) := by
          rw [hNmap]
    _ = Submodule.span K (e '' (L : Set (Fin s → K))) := by rw [himage]
    _ = (Submodule.span K (L : Set (Fin s → K))).map e.toLinearMap := by
          symm
          exact Submodule.map_span e.toLinearMap (L : Set (Fin s → K))
    _ = ⊤ := by
          rw [hspan, Submodule.map_top]
          exact LinearMap.range_eq_top.2 e.surjective

/-- Helper for Lemma 10.119.9: the remaining finite case is exactly the source denominator-
clearing lattice comparison for finite submodules of `K^{\oplus r}`. -/
lemma length_quotSMulTop_le_rank_mul_length_quotient_of_finite_full_span
    {s : ℕ} (L : Submodule R (Fin s → K)) (hLfinite : Module.Finite R L)
    (hspan : Submodule.span K (L : Set (Fin s → K)) = ⊤)
    {x : R} (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x L) ≤
      s * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
  let ι := fractionFieldPiInclusion (R := R) (K := K) s
  obtain ⟨a, ha, N, hNmap⟩ :=
    exists_nonzero_scalar_map_pi_eq_smul_of_finite (R := R) (K := K) L hLfinite
  have hquot :
      Module.length R (QuotSMulTop x L) =
        Module.length R (QuotSMulTop x (N.map ι)) := by
    -- First scale `L` into the coordinate image, then rewrite by the cleared-denominator model.
    calc
      Module.length R (QuotSMulTop x L) =
          Module.length R (QuotSMulTop x (a • L : Submodule R (Fin s → K))) := by
            symm
            exact length_quotSMulTop_smul_eq (R := R) (K := K) (L := L) (x := x) (a := a) ha
      _ = Module.length R (QuotSMulTop x (N.map ι)) := by
            rw [hNmap]
  have hspanN :
      Submodule.span K (((N.map ι : Submodule R (Fin s → K)) : Set (Fin s → K))) = ⊤ :=
    span_map_pi_eq_top_of_smul_full_span (R := R) (K := K) ha hNmap hspan
  -- Route correction: the old blocker lived in the embedded standard lattice. The remaining
  -- source-faithful blocker is now only the actual `R^s` lattice estimate after denominator
  -- clearing.
  calc
    Module.length R (QuotSMulTop x L) =
        Module.length R (QuotSMulTop x (N.map ι)) := hquot
    _ ≤ s * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
      exact length_quotSMulTop_le_rank_mul_length_quotient_of_lattice
        (R := R) (K := K) N hspanN hx

/-- Helper for Lemma 10.119.9: the finite case reduces to the full-span coordinate model obtained
by shrinking to the `K`-span of `M0`. -/
lemma length_quotSMulTop_le_finrank_mul_length_quotient_span_singleton_of_finite
    {r : ℕ} (M0 : Submodule R (Fin r → K)) {x : R}
    (hM0finite : Module.Finite R M0) (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x M0) ≤
      r * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
  let W : Submodule K (Fin r → K) := Submodule.span K (M0 : Set (Fin r → K))
  let s : ℕ := Module.finrank K W
  have hM0W : M0 ≤ W.restrictScalars R := by
    -- The chosen `K`-span contains the original finite `R`-submodule.
    intro m hm
    exact Submodule.subset_span hm
  let e : W ≃ₗ[K] (Fin s → K) := LinearEquiv.ofFinrankEq W (Fin s → K) (by simp [s])
  let f : M0 →ₗ[R] (Fin s → K) :=
    (e.restrictScalars R).toLinearMap.comp (Submodule.inclusion hM0W)
  have hf : Function.Injective f := by
    intro m₁ m₂ hm
    -- Both maps in the coordinate transport are injective, so equality in the image comes from
    -- equality in the original finite submodule.
    ext x
    exact congrFun (congrArg Subtype.val ((e.restrictScalars R).injective hm)) x
  have hspan_inW : Submodule.span K (Set.range (Submodule.inclusion hM0W)) = ⊤ := by
    -- The inclusion of `M0` into its `K`-span generates that span over `K`.
    simpa [W] using
      (Submodule.span_range_inclusion_eq_top (R := R) (S := K) (p := M0) (q := W)
        hM0W (by simpa [W] using (le_rfl : W ≤ Submodule.span K (M0 : Set (Fin r → K)))))
  have hspan_range_f : Submodule.span K (Set.range f) = ⊤ := by
    -- Transport the generating family in `W` through the chosen coordinates.
    have himage : Set.range f = e '' Set.range (Submodule.inclusion hM0W) := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        refine ⟨Submodule.inclusion hM0W m, ⟨m, rfl⟩, rfl⟩
      · rintro ⟨y', ⟨m, rfl⟩, rfl⟩
        exact ⟨m, rfl⟩
    rw [himage, Submodule.span_image_linearEquiv]
    simpa [hspan_inW]
  have hquot :
      Module.length R (QuotSMulTop x M0) =
        Module.length R (QuotSMulTop x (LinearMap.range f)) := by
    -- Replacing `M0` by its coordinate image preserves the quotient length.
    simpa using
      (LinearEquiv.length_eq (QuotSMulTop.congr x (LinearEquiv.ofInjective f hf)) :
        Module.length R (QuotSMulTop x M0) =
          Module.length R (QuotSMulTop x (LinearMap.range f)))
  have hsle : s ≤ r := by
    -- Shrinking to the `K`-span cannot increase the ambient `K`-dimension.
    simpa [s] using (Submodule.finrank_le W)
  calc
    Module.length R (QuotSMulTop x M0) =
        Module.length R (QuotSMulTop x (LinearMap.range f)) := hquot
    _ ≤ s * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
      -- The only remaining source-faithful work is the finite full-span lattice estimate.
      apply length_quotSMulTop_le_rank_mul_length_quotient_of_finite_full_span
        (R := R) (K := K) (L := LinearMap.range f) (hLfinite := inferInstance)
        (hx := hx)
      -- The coordinate image still spans the whole ambient `K^s`.
      change Submodule.span K (Set.range f) = ⊤
      exact hspan_range_f
    _ ≤ r * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
      gcongr

/-- Chap10 Lemma 10 119 9: if `R` is a local Noetherian domain of Krull dimension at most
`1`, `M` is an `R`-submodule of `K^{\oplus r}`, then
`length_R (QuotSMulTop x M) ≤ r * length_R(R / xR)`. -/
-- Proof sketch: reduce first to the finite case by approximating a finite-length subquotient of
-- `QuotSMulTop x M` with the image of a finite submodule of `M`, then compare with `R^r` after
-- clearing denominators and use additivity of module length together with finite length of `R/xR`.
@[stacks 00PE]
theorem length_quotSMulTop_le_finrank_mul_length_quotient_span_singleton
    {r : ℕ} (M : Submodule R (Fin r → K)) {x : R} :
    Module.length R (QuotSMulTop x M) ≤
      r * Module.length R (R ⧸ Ideal.span {x}) := by
  by_cases hx : x = 0
  · -- If `x = 0`, the quotient is just `M`, so the only nontrivial work is hidden in the
    -- ambient dimension-one local-domain dichotomy.
    subst hx
    -- Rewrite the quotient by `0` as the original module before splitting into the field and
    -- nonfield branches.
    have hquot :
        Module.length R (QuotSMulTop (0 : R) M) = Module.length R M := by
      simpa [QuotSMulTop] using
        (LinearEquiv.length_eq
          (((0 : R) • (⊤ : Submodule R M)).quotEquivOfEqBot (by simp)) : _)
    rw [hquot]
    by_cases hr : r = 0
    · -- Rank zero forces the ambient module, and hence `M`, to be trivial.
      subst hr
      simp
    · by_cases hfield : IsField R
      · -- In the field case, compare with the ambient `K`-vector space and compute its length.
        letI : Field R := hfield.toField
        have hsub :
            Module.length R M ≤ Module.length R (Fin r → K) :=
          Module.length_le_of_injective M.subtype Subtype.val_injective
        have hquotient_zero :
            Module.length R (R ⧸ Ideal.span ({(0 : R)} : Set R)) = 1 := by
          have hbot : Ideal.span ({(0 : R)} : Set R) = ⊥ := by simp
          rw [hbot]
          simpa using
            (LinearEquiv.length_eq ((AlgEquiv.quotientBot R R).toLinearEquiv) :
              Module.length R (R ⧸ (⊥ : Ideal R)) = Module.length R R)
        have hrhs : r * Module.length R (R ⧸ Ideal.span ({(0 : R)} : Set R)) = r := by
          rw [hquotient_zero]
          simp
        calc
          Module.length R M ≤ Module.length R (Fin r → K) := hsub
          _ = r := length_pi_fractionRing_eq_rank_of_isField (R := R) (K := K) hfield
          _ = r * Module.length R (R ⧸ Ideal.span ({(0 : R)} : Set R)) := hrhs.symm
      · -- In the nonfield case, `length_R R = ⊤`, so the right-hand side is automatically `⊤`.
        have hquotient_zero :
            Module.length R (R ⧸ Ideal.span ({(0 : R)} : Set R)) = Module.length R R := by
          have hbot : Ideal.span ({(0 : R)} : Set R) = ⊥ := by simp
          rw [hbot]
          simpa using
            (LinearEquiv.length_eq ((AlgEquiv.quotientBot R R).toLinearEquiv) :
              Module.length R (R ⧸ (⊥ : Ideal R)) = Module.length R R)
        have htop : r * Module.length R R = ⊤ := by
          simp [length_ring_eq_top_of_not_isField (R := R) hfield, hr]
        calc
          Module.length R M ≤ ⊤ := le_top
          _ = r * Module.length R R := htop.symm
          _ = r * Module.length R (R ⧸ Ideal.span ({(0 : R)} : Set R)) := by
            rw [← hquotient_zero]
  · by_cases hunit : IsUnit x
    · -- If `x` is a unit then `x • ⊤ = ⊤`, so the quotient vanishes.
      have hspan : Ideal.span ({x} : Set R) = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
      have hsmul : x • (⊤ : Submodule R M) = ⊤ := by
        rw [← Submodule.ideal_span_singleton_smul, hspan, Submodule.top_smul]
      simpa [QuotSMulTop, hsmul]
    · -- TODO: Source-faithful remaining route.
      -- Route correction: the arbitrary-`M` reduction is now proved separately, so this branch
      -- only has to invoke the source finite-case estimate for finite submodules.
      refine length_quotSMulTop_le_of_finite_case (R := R) (K := K) (M := M) ?_
      intro M0 hM0 hM0finite
      -- The remaining source-faithful work is the finite denominator-clearing comparison.
      exact length_quotSMulTop_le_finrank_mul_length_quotient_span_singleton_of_finite
        (R := R) (K := K) M0 hM0finite hx

end
