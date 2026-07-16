import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped FrobeniusSubfield
open KaehlerDifferential

universe u v w

section PBasis

variable (p : ℕ) (k : Type u) (K : Type v)
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/- Domain triage:
- primary domain: `p`-bases of characteristic-`p` field extensions and their characterization via
  the universal derivation `D k K`;
- sampled owner declarations:
  `PIndependent`,
  `IsPBasis`,
  `Module.Basis.mk`,
  `Module.Basis.span_eq`,
  `D k K`;
- best owner abstraction: the source-facing owners are the chapter declarations `PIndependent` and
  `IsPBasis`, while any actual `Module.Basis` witness is derived data supplied canonically by
  `Module.Basis.mk`;
- primitive data: `p`-independence and generation over `pPowerCompositum p k K`;
- derived API: the differential criteria and existence statements below.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma `15.46.2`;
- `core/canonical`: `PIndependent`, `IsPBasis`, `Module.Basis.mk`, and `D k K`;
- `bridge/view`: the textbook basis wording is expressed directly through the owner `IsPBasis`,
  rather than through any parallel local restatement or existential `Module.Basis` wrapper.
-/

/-- Helper for Lemma 15.46.2: the universal derivation satisfies the usual power rule. -/
lemma derivation_pow_formula (a : K) (n : ℕ) :
    D k K (a ^ n) = ((n • a ^ (n - 1) : K)) • D k K a := by
  -- Follow the source route: differentiate powers by repeated Leibniz and keep the coefficient in
  -- the field so the characteristic-`p` vanishing becomes a scalar computation.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      cases n with
      | zero =>
          simp
      | succ m =>
          calc
            D k K (a ^ (Nat.succ (Nat.succ m))) = D k K (a ^ (Nat.succ m) * a) := by
              simp [pow_succ]
            _ = a ^ (Nat.succ m) • D k K a + a • D k K (a ^ (Nat.succ m)) := by
              simpa [add_comm] using (D k K).leibniz a (a ^ (Nat.succ m))
            _ = a ^ (Nat.succ m) • D k K a + a • (((Nat.succ m • a ^ m : K)) • D k K a) := by
              simpa using
                congrArg (fun z ↦ a ^ (Nat.succ m) • D k K a + a • z) ih
            _ = a ^ (Nat.succ m) • D k K a + (a * ((Nat.succ m • a ^ m : K))) • D k K a := by
              simp [smul_smul, mul_comm]
            _ = (a ^ (Nat.succ m) + a * ((Nat.succ m • a ^ m : K))) • D k K a := by
              rw [← add_smul]
            _ = (((Nat.succ (Nat.succ m)) • a ^ (Nat.succ m) : K)) • D k K a := by
              congr 1
              rw [nsmul_eq_mul, nsmul_eq_mul]
              simp [pow_succ, Nat.cast_add]
              ring_nf

omit [Fact p.Prime] in
/-- Helper for Lemma 15.46.2: the universal derivation kills `p`th powers in characteristic `p`. -/
lemma derivation_eq_zero_of_pth_power (a : K) :
    D k K (a ^ p) = 0 := by
  -- The power rule turns the derivative into multiplication by `p`, which vanishes in
  -- characteristic `p`.
  rw [derivation_pow_formula (k := k) (K := K) (a := a) (n := p)]
  have hp0 : ((p • a ^ (p - 1) : K)) = 0 := by
    rw [nsmul_eq_mul]
    simp
  simpa [hp0]

/-- Helper for Lemma 15.46.2: the kernel of a derivation is closed under inversion. -/
lemma derivation_inv_eq_zero_of_eq_zero (a : K) (ha : D k K a = 0) :
    D k K a⁻¹ = 0 := by
  -- Differentiate `a * a⁻¹ = 1`; after the source element is already in the kernel, the inverse
  -- term is forced to vanish as well.
  by_cases ha0 : a = 0
  · simp [ha0]
  · have hmul : D k K (a * a⁻¹) = a • D k K a⁻¹ + a⁻¹ • D k K a := by
      simpa [add_comm] using (D k K).leibniz a⁻¹ a
    have hone : D k K (a * a⁻¹) = 0 := by
      simp [ha0]
    have hsmul : a • D k K a⁻¹ = 0 := by
      calc
        a • D k K a⁻¹ = D k K (a * a⁻¹) := by
          simpa [ha] using hmul.symm
        _ = 0 := hone
    rcases smul_eq_zero.mp hsmul with ha' | hinv
    · exact False.elim (ha0 ha')
    · exact hinv

/-- Helper for Lemma 15.46.2: every element of `k(K^p)` has zero Kähler differential over `k`
after being viewed inside `K`. -/
lemma derivation_eq_zero_of_mem_pPowerCompositum (a : K) (ha : a ∈ pPowerCompositum p k K) :
    D k K a = 0 := by
  -- Follow the source proof literally: `k(K^p)` is generated from `k` and the `p`th powers, and
  -- the universal derivation kills both generators while preserving the field operations.
  refine IntermediateField.adjoin_induction (F := k) (s := (K^[p] : Set K))
      (p := fun x _ ↦ D k K x = 0) ?_ ?_ ?_ ?_ ?_
      (show a ∈ IntermediateField.adjoin k (K^[p] : Set K) from ha)
  · -- Route correction: the previous attempt stalled on the generator step; the power rule above
    -- now supplies the missing source-faithful `d(b^p) = 0` calculation.
    intro x hx
    rcases hx with ⟨b, rfl⟩
    change D k K (b ^ p) = 0
    exact derivation_eq_zero_of_pth_power (p := p) (k := k) (K := K) b
  · intro x
    simpa using (D k K).map_algebraMap x
  · intro x y _ _ hx hy
    simpa [hx, hy] using (D k K).map_add x y
  · intro x _ hx
    simpa using derivation_inv_eq_zero_of_eq_zero (k := k) (K := K) x hx
  · intro x y _ _ hx hy
    simpa [hx, hy] using (D k K).leibniz x y

/-- Helper for Lemma 15.46.2: if `da` already lies in the span generated by the chosen
differentials, then so does `d(a⁻¹)`. -/
lemma differential_inv_mem_span (x : ι → K) {a : K}
    (ha : D k K a ∈ Submodule.span K (Set.range (D k K ∘ x))) :
    D k K a⁻¹ ∈ Submodule.span K (Set.range (D k K ∘ x)) := by
  -- Differentiate `a * a⁻¹ = 1` and solve for `d(a⁻¹)`; the resulting scalar multiple of `da`
  -- stays inside the same `K`-submodule.
  by_cases ha0 : a = 0
  · simp [ha0]
  · have hsum : a • D k K a⁻¹ + a⁻¹ • D k K a = 0 := by
      calc
        a • D k K a⁻¹ + a⁻¹ • D k K a = D k K (a * a⁻¹) := by
          simpa [add_comm] using (D k K).leibniz a⁻¹ a
        _ = 0 := by
          simp [ha0]
    have hmul : a • D k K a⁻¹ = -(a⁻¹ • D k K a) := by
      exact eq_neg_of_add_eq_zero_left hsum
    have hinv :
        D k K a⁻¹ = -((a⁻¹ * a⁻¹ : K)) • D k K a := by
      have hmul' := congrArg (fun z ↦ a⁻¹ • z) hmul
      simpa [smul_smul, ha0, mul_assoc, mul_comm, mul_left_comm] using hmul'
    rw [hinv]
    exact Submodule.smul_mem _ _ ha

/-- Helper for Lemma 15.46.2: adjoining elements to `k(K^p)` does not create new differentials
outside the span generated by the differentials of the chosen generators. -/
lemma differential_mem_span_of_mem_adjoin (x : ι → K) {a : K}
    (ha : a ∈ IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x)) :
    D k K a ∈ Submodule.span K (Set.range (D k K ∘ x)) := by
  -- Package the source proof as a single adjoin induction over `k(K^p)` and the generators `x i`.
  let P : ∀ z ∈ IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x), Prop :=
    fun z _ ↦ D k K z ∈ Submodule.span K (Set.range (D k K ∘ x))
  refine IntermediateField.adjoin_induction
      (F := pPowerCompositum p k K) (s := Set.range x) (p := P) ?_ ?_ ?_ ?_ ?_ ha
  · intro z hz
    rcases hz with ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · intro z
    -- Elements already in `k(K^p)` have zero differential, hence lie in every span.
    change D k K (z : K) ∈ Submodule.span K (Set.range (D k K ∘ x))
    rw [derivation_eq_zero_of_mem_pPowerCompositum (p := p) (k := k) (K := K) (a := (z : K))
      z.property]
    exact Submodule.zero_mem _
  · intro z w _ _ hz hw
    -- The span is closed under addition, so differentiating sums stays inside it.
    change D k K (z + w) ∈ Submodule.span K (Set.range (D k K ∘ x))
    simpa using Submodule.add_mem _ hz hw
  · intro z _ hz
    -- Inversion preserves span-membership by the standard derivative-of-inverse identity.
    change D k K z⁻¹ ∈ Submodule.span K (Set.range (D k K ∘ x))
    exact differential_inv_mem_span (k := k) (K := K) (x := x) hz
  · intro z w _ _ hz hw
    -- Leibniz expresses `d(zw)` as a sum of scalar multiples of `dz` and `dw`.
    change D k K (z * w) ∈ Submodule.span K (Set.range (D k K ∘ x))
    simpa using
      Submodule.add_mem _ (Submodule.smul_mem _ z hw) (Submodule.smul_mem _ w hz)

/-- Helper for Lemma 15.46.2: if a family generates `K` over `k(K^p)`, then its differentials
span `Ω[K⁄k]`. -/
lemma span_differentials_of_adjoin_eq_top (x : ι → K)
    (hx : IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x) = ⊤) :
    Submodule.span K (Set.range (D k K ∘ x)) = ⊤ := by
  -- Rewrite the top target through the universal derivation, then place each generator `da`
  -- into the smaller span using the adjoin-closure helper proved above.
  refine top_unique ?_
  rw [← KaehlerDifferential.span_range_derivation k K]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x) := by
    rw [hx]
    simp
  exact differential_mem_span_of_mem_adjoin (p := p) (k := k) (K := K) (x := x) ha

/-- Helper for Lemma 15.46.2: if `K / L` is simultaneously separable and every `p`th power of an
element of `K` already lies in `L`, then `L = K`. -/
lemma top_of_isSeparableOver_of_frobeniusSubfield_le
    (L : IntermediateField k K) [Algebra.IsSeparable L K] (hpow : (K^[p]) ≤ L.toSubfield) :
    L = ⊤ := by
  -- Route correction: the closing step is not another differential argument. It is the standard
  -- fact that a separable extension with all `p`th powers already in the base is trivial.
  letI : IsPurelyInseparable L K := by
    rw [isPurelyInseparable_iff_pow_mem L p]
    intro x
    have hxpow : x ^ p ∈ (K^[p] : Set K) := by
      change x ^ p ∈ (_root_.frobenius K p).fieldRange
      exact ⟨x, rfl⟩
    have hxL : x ^ p ∈ (L : Set K) := hpow hxpow
    refine ⟨1, ?_⟩
    simpa using (show x ^ p ∈ (algebraMap L K).range from ⟨⟨x ^ p, hxL⟩, rfl⟩)
  -- Purely inseparable plus separable forces surjectivity of the structure map `L → K`.
  refine top_unique ?_
  intro x hx
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable L K x
  rw [← hy]
  exact y.property

/-- Helper for Lemma 15.46.2: if the relative Kähler differentials over an intermediate field
are trivial and that field already contains `K^[p]`, then the intermediate field is all of `K`. -/
lemma eq_top_of_subsingleton_kaehler_of_frobeniusSubfield_le
    (L : IntermediateField k K) [hΩ : Subsingleton Ω[K⁄L]]
    (hpow : (K^[p]) ≤ L.toSubfield) :
    L = ⊤ := by
  -- Convert vanishing of `Ω[K⁄L]` into formal unramifiedness, hence separability, and then apply
  -- the purely inseparable-versus-separable collapse proved just above.
  -- TODO: mathlib only exposes the field-theoretic bridge
  -- `Algebra.FormallyUnramified.isSeparable` under an `EssFiniteType` hypothesis, so the missing
  -- source-faithful step here is a finite-type-free lemma showing that vanishing Kähler
  -- differentials over a field extension imply separability.
  sorry

/-- Helper for Lemma 15.46.2: a linearly independent differential family extends to a basis of
`Ω[K⁄k]` whose vectors still lie in the image of the universal derivation. -/
lemma exists_basis_extension_in_differential_range (x : ι → K)
    (hx : LinearIndependent K (D k K ∘ x)) :
    ∃ s : Set Ω[K⁄k],
      Set.range (D k K ∘ x) ⊆ s ∧
      s ⊆ Set.range (D k K) ∧
      Nonempty (Module.Basis s K Ω[K⁄k]) := by
  -- Extend the independent set `range (D ∘ x)` inside the ambient generating set `range D`.
  let hs : LinearIndepOn K id (Set.range (D k K ∘ x)) := hx.linearIndepOn_id
  let hst : Set.range (D k K ∘ x) ⊆ Set.range (D k K) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, rfl⟩
  -- The universal derivation already spans the whole Kähler differential module.
  let ht : ⊤ ≤ Submodule.span K (Set.range (D k K)) := by
    rw [KaehlerDifferential.span_range_derivation k K]
  refine ⟨hs.extend hst, ?_, ?_, ?_⟩
  · -- The chosen extension contains the original differentials.
    simpa [hs, hst, ht] using
      ((Module.Basis.range_extendLe hs hst ht).symm ▸ Module.Basis.subset_extendLe hs hst ht)
  · -- By construction, the extension never leaves the image of `D`.
    simpa [hs, hst, ht] using
      ((Module.Basis.range_extendLe hs hst ht).symm ▸ Module.Basis.extendLe_subset hs hst ht)
  · -- `extendLe` itself provides the required basis on the enlarged set.
    exact ⟨Module.Basis.extendLe hs hst ht⟩

/-- Helper for Lemma 15.46.2: from a linearly independent differential family, one can choose a
`k`-derivation detecting a prescribed `dx_i` and killing the other `dx_j`. -/
lemma exists_dual_derivation_of_linearIndependent_differentials
    (x : ι → K) (hx : LinearIndependent K (D k K ∘ x)) (i : ι) :
    ∃ θ : Derivation k K K, θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0 := by
  classical
  -- Route correction: keep the source basis-extension step concrete so the coordinate functional
  -- can be evaluated directly on the chosen `dx_i`.
  let hs : LinearIndepOn K id (Set.range (D k K ∘ x)) := hx.linearIndepOn_id
  let hst : Set.range (D k K ∘ x) ⊆ Set.range (D k K) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨x j, rfl⟩
  let ht : ⊤ ≤ Submodule.span K (Set.range (D k K)) := by
    rw [KaehlerDifferential.span_range_derivation k K]
  let b : Module.Basis (↑(hs.extend hst)) K Ω[K⁄k] := Module.Basis.extendLe hs hst ht
  have hsubset : Set.range (D k K ∘ x) ⊆ ↑(hs.extend hst) := by
    -- The extendLe basis contains the original differential family among its indices.
    simpa [hs, hst, ht] using
      ((Module.Basis.range_extendLe hs hst ht).symm ▸ Module.Basis.subset_extendLe hs hst ht)
  let ei : ↑(hs.extend hst) := ⟨D k K (x i), hsubset ⟨i, rfl⟩⟩
  let coord : Ω[K⁄k] →ₗ[K] K := (Finsupp.lapply ei).comp b.repr.toLinearMap
  let θ : Derivation k K K := (LinearMap.compDer coord) (D k K)
  have hb_apply (u : ↑(hs.extend hst)) : b u = u := by
    -- The concrete `extendLe` basis is indexed by the enlarged set itself.
    simpa [b] using congrArg (fun f ↦ f u) (Module.Basis.coe_extendLe hs hst ht)
  have hcoord (u : ↑(hs.extend hst)) : coord (u : Ω[K⁄k]) = if u = ei then 1 else 0 := by
    -- Coordinate evaluation on the concrete basis is the expected Kronecker delta.
    calc
      coord (u : Ω[K⁄k]) =
          (Finsupp.lapply (R := K) (M := K) ei) (b.repr (b u)) := by
        simp [coord, hb_apply]
      _ = (Finsupp.lapply (R := K) (M := K) ei) (Finsupp.single u (1 : K)) := by
        rw [Module.Basis.repr_self]
      _ = if u = ei then 1 else 0 := by
        simp [Finsupp.lapply, Finsupp.single_apply]
  refine ⟨θ, ?_, ?_⟩
  · -- The coordinate indexed by `dx_i` reads off coefficient `1` on `dx_i`.
    let ej : ↑(hs.extend hst) := ⟨D k K (x i), hsubset ⟨i, rfl⟩⟩
    calc
      θ (x i) = coord (D k K (x i)) := by
        rfl
      _ = if ej = ei then 1 else 0 := by
        simpa [ej] using hcoord ej
      _ = 1 := by
        simp [ei, ej]
  · intro j hji
    let ej : ↑(hs.extend hst) := ⟨D k K (x j), hsubset ⟨j, rfl⟩⟩
    have hDx_inj : Function.Injective (D k K ∘ x) := hx.injective
    -- Translate equality of basis indices back to equality of the original family indices.
    calc
      θ (x j) = coord (D k K (x j)) := by
        rfl
      _ = if ej = ei then 1 else 0 := by
        simpa [ej] using hcoord ej
      _ = 0 := by
        have hej : ej ≠ ei := by
          intro hEq
          apply hji
          apply hDx_inj
          exact congrArg Subtype.val hEq
        simp [hej]

/-- Helper for Lemma 15.46.2: a family of derivations dual to the chosen elements forces the
corresponding differentials to be linearly independent. -/
lemma linearIndependent_differentials_of_dual_derivations (x : ι → K)
    (hdual : ∀ i, ∃ θ : Derivation k K K, θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0) :
    LinearIndependent K (D k K ∘ x) := by
  classical
  choose θ hθ_self hθ_other using hdual
  -- Lift each detecting derivation across the universal derivation to obtain dual linear forms on
  -- `Ω[K⁄k]`, then apply the standard dual-basis criterion for linear independence.
  refine LinearIndependent.of_pairwise_dual_eq_zero_one (v := D k K ∘ x)
      (f := fun i ↦ (θ i).liftKaehlerDifferential) ?_ ?_
  · intro i j hij
    -- Off the distinguished index, the chosen derivation kills the corresponding generator.
    simpa [Function.comp_apply, Derivation.liftKaehlerDifferential_comp_D,
      hθ_other i j hij.symm] using hθ_other i j hij.symm
  · intro i
    -- On the distinguished generator, the chosen derivation evaluates to `1`.
    simpa [Function.comp_apply, Derivation.liftKaehlerDifferential_comp_D,
      hθ_self i] using hθ_self i

/-- Helper for Lemma 15.46.2: the total exponent weight of a `p`-restricted monomial exponent. -/
abbrev pMonomialWeight (e : ι →₀ Fin p) : ℕ :=
  e.support.sum fun i ↦ (e i : ℕ)

/-- Helper for Lemma 15.46.2: lower the exponent at `i` by one in the source minimal-weight
argument. -/
noncomputable abbrev lowerAt (i : ι) (e : ι →₀ Fin p) : ι →₀ Fin p :=
  e - Finsupp.single i 1

/-- Helper for Lemma 15.46.2: lowering at a different index leaves the exponent unchanged. -/
lemma lowerAt_apply_of_ne (i j : ι) (hji : j ≠ i) (e : ι →₀ Fin p) :
    lowerAt (p := p) i e j = e j := by
  -- Away from `i`, the lowering term is the zero single coefficient.
  simp [lowerAt, hji]

/-- Helper for Lemma 15.46.2: lowering records subtraction of `1` at the chosen exponent. -/
lemma lowerAt_apply_self (i : ι) (e : ι →₀ Fin p) :
    lowerAt (p := p) i e i = e i - 1 := by
  -- At the distinguished index, `lowerAt` is literally subtraction by the basis vector.
  simp [lowerAt]

/-- Helper for Lemma 15.46.2: if the chosen exponent is nonzero, lowering it decreases its
natural-value by exactly `1`. -/
lemma lowerAt_apply_self_val_add_one_of_ne_zero (i : ι) {e : ι →₀ Fin p} (hi : e i ≠ 0) :
    ((lowerAt (p := p) i e i : Fin p) : ℕ) + 1 = (e i : ℕ) := by
  -- On the distinguished coordinate there is no wrap-around, so the `Fin` subtraction agrees with
  -- ordinary subtraction on natural values.
  have hp : Nat.Prime p := Fact.out
  have hi_pos : 0 < (e i : ℕ) := by
    exact Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
  have hi_lt : (e i : ℕ) < p := (e i).2
  rw [lowerAt_apply_self, Fin.val_sub]
  change (p - (1 % p) + (e i : ℕ)) % p + 1 = (e i : ℕ)
  rw [Nat.mod_eq_of_lt hp.one_lt]
  have hge : p ≤ p - 1 + (e i : ℕ) := by
    omega
  rw [Nat.mod_eq_sub_mod hge]
  have hsub : p - 1 + (e i : ℕ) - p = (e i : ℕ) - 1 := by
    omega
  rw [hsub, Nat.mod_eq_of_lt]
  · omega
  · omega

/-- Helper for Lemma 15.46.2: lowering a positive exponent drops the total `p`-restricted
monomial weight by exactly `1`. -/
lemma pMonomialWeight_lowerAt_of_ne_zero (i : ι) {e : ι →₀ Fin p} (hi : e i ≠ 0) :
    pMonomialWeight (p := p) (lowerAt (p := p) i e) + 1 = pMonomialWeight (p := p) e := by
  classical
  -- Isolate the distinguished exponent from the support sum; all other coordinates are unchanged
  -- by `lowerAt`, while the `i`-coordinate loses exactly one.
  have hi_mem : i ∈ e.support := Finsupp.mem_support_iff.mpr hi
  have hsupport :
      (lowerAt (p := p) i e).support.erase i = e.support.erase i := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [lowerAt_apply_of_ne (p := p) i j hji e, hji]
  have hsum_off :
      ((lowerAt (p := p) i e).support.erase i).sum
          (fun j ↦ (lowerAt (p := p) i e j : ℕ)) =
        (e.support.erase i).sum fun j ↦ (e j : ℕ) := by
    rw [hsupport]
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact congrArg (fun a : Fin p ↦ (a : ℕ))
      (lowerAt_apply_of_ne (p := p) i j (Finset.mem_erase.mp hj).1 e)
  have he_split :
      pMonomialWeight (p := p) e =
        (e.support.erase i).sum (fun j ↦ (e j : ℕ)) + (e i : ℕ) := by
    -- Since `i` lies in the original support, split off that single term from the weight sum.
    unfold pMonomialWeight
    simpa [add_comm] using
      (Finset.sum_erase_add (s := e.support) (f := fun j ↦ (e j : ℕ)) hi_mem).symm
  have hlower_split :
      pMonomialWeight (p := p) (lowerAt (p := p) i e) =
        ((lowerAt (p := p) i e).support.erase i).sum
            (fun j ↦ (lowerAt (p := p) i e j : ℕ)) +
          (lowerAt (p := p) i e i : ℕ) := by
    -- Either `i` remains in the lowered support, or its contribution is already zero.
    unfold pMonomialWeight
    by_cases hli : i ∈ (lowerAt (p := p) i e).support
    · simpa [add_comm] using
        (Finset.sum_erase_add
          (s := (lowerAt (p := p) i e).support)
          (f := fun j ↦ (lowerAt (p := p) i e j : ℕ)) hli).symm
    · have hli_zero : lowerAt (p := p) i e i = 0 := by
        by_contra hne
        exact hli (Finsupp.mem_support_iff.mpr hne)
      have herase :
          (lowerAt (p := p) i e).support.erase i = (lowerAt (p := p) i e).support := by
        ext j
        simp [hli]
      rw [herase]
      simp [hli_zero]
  calc
    pMonomialWeight (p := p) (lowerAt (p := p) i e) + 1 =
        ((lowerAt (p := p) i e).support.erase i).sum
            (fun j ↦ (lowerAt (p := p) i e j : ℕ)) +
          ((lowerAt (p := p) i e i : ℕ) + 1) := by
      rw [hlower_split]
      omega
    _ = (e.support.erase i).sum (fun j ↦ (e j : ℕ)) + (e i : ℕ) := by
      rw [hsum_off, lowerAt_apply_self_val_add_one_of_ne_zero (p := p) (i := i) hi]
    _ = pMonomialWeight (p := p) e := by
      rw [he_split]

/-- Helper for Lemma 15.46.2: lowering is injective on exponents with positive `i`-coordinate. -/
lemma lowerAt_injective_on_pos (i : ι) {e e' : ι →₀ Fin p}
    (_he : e i ≠ 0) (_he' : e' i ≠ 0)
    (h : lowerAt (p := p) i e = lowerAt (p := p) i e') :
    e = e' := by
  -- Add back the same basis vector on both sides to recover the original exponents.
  calc
    e = lowerAt (p := p) i e + Finsupp.single i 1 := by
      simpa [lowerAt] using (sub_add_cancel e (Finsupp.single i 1)).symm
    _ = lowerAt (p := p) i e' + Finsupp.single i 1 := by
      rw [h]
    _ = e' := by
      simpa [lowerAt] using (sub_add_cancel e' (Finsupp.single i 1))

/-- Helper for Lemma 15.46.2: a derivation kills a finite product when it kills every factor. -/
lemma derivation_prod_eq_zero_of_forall (θ : Derivation k K K) (s : Finset ι) (f : ι → K)
    (hzero : ∀ j ∈ s, θ (f j) = 0) :
    θ (s.prod f) = 0 := by
  classical
  -- Run the source product rule one factor at a time; every Leibniz term vanishes because each
  -- individual factor already lies in the kernel of the derivation.
  revert hzero
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih hzero
    have ha0 : θ (f a) = 0 := hzero a (Finset.mem_insert_self a s)
    have hs0 : ∀ j ∈ s, θ (f j) = 0 := by
      intro j hj
      exact hzero j (Finset.mem_insert_of_mem hj)
    calc
      θ ((insert a s).prod f) = θ (f a * s.prod f) := by
        rw [Finset.prod_insert ha]
      _ = f a • θ (s.prod f) + s.prod f • θ (f a) := by
        simpa using θ.leibniz (f a) (s.prod f)
      _ = 0 := by
        simp [ih hs0, ha0]

/-- Helper for Lemma 15.46.2: a `K`-valued derivation satisfies the usual power rule. -/
lemma scalar_derivation_pow_formula (θ : Derivation k K K) (a : K) (n : ℕ) :
    θ (a ^ n) = ((n • a ^ (n - 1) : K)) * θ a := by
  -- This is the scalar-valued version of the usual Leibniz induction, kept separate from the
  -- universal-derivation formula because the codomain here is `K`.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      cases n with
      | zero =>
          simp
      | succ m =>
          calc
            θ (a ^ (Nat.succ (Nat.succ m))) = θ (a ^ (Nat.succ m) * a) := by
              simp [pow_succ]
            _ = a ^ (Nat.succ m) * θ a + a * θ (a ^ (Nat.succ m)) := by
              simpa [smul_eq_mul, add_comm, mul_comm, mul_left_comm] using
                θ.leibniz a (a ^ (Nat.succ m))
            _ = a ^ (Nat.succ m) * θ a + a * (((Nat.succ m • a ^ m : K)) * θ a) := by
              simpa using congrArg (fun z ↦ a ^ (Nat.succ m) * θ a + a * z) ih
            _ = a ^ (Nat.succ m) * θ a + (a * ((Nat.succ m • a ^ m : K))) * θ a := by
              rw [← mul_assoc]
            _ = (a ^ (Nat.succ m) + a * ((Nat.succ m • a ^ m : K))) * θ a := by
              rw [← add_mul]
            _ = (((Nat.succ (Nat.succ m)) • a ^ (Nat.succ m) : K)) * θ a := by
              congr 1
              rw [nsmul_eq_mul, nsmul_eq_mul]
              simp [pow_succ, Nat.cast_add]
              ring_nf

/-- Helper for Lemma 15.46.2: if the distinguished exponent vanishes, a dual derivation kills the
corresponding `p`-restricted monomial. -/
lemma dual_derivation_apply_pMonomial_eq_zero_of_eq_zero (x : ι → K) (i : ι)
    (θ : Derivation k K K) (hθ_other : ∀ j, j ≠ i → θ (x j) = 0) {e : ι →₀ Fin p}
    (hi : e i = 0) :
    θ (pMonomial p x e) = 0 := by
  classical
  -- When the `i`-exponent is already zero, every support factor lies away from `i`, so the dual
  -- derivation annihilates each powered factor and hence the whole product.
  unfold pMonomial
  refine derivation_prod_eq_zero_of_forall (k := k) (K := K) θ e.support
    (fun j ↦ x j ^ (e j : ℕ)) ?_
  intro j hj
  have hji : j ≠ i := by
    intro hji
    subst hji
    exact (Finsupp.mem_support_iff.mp hj) hi
  calc
    θ (x j ^ (e j : ℕ)) = (((e j : ℕ) • x j ^ ((e j : ℕ) - 1) : K)) * θ (x j) := by
      simpa using
        scalar_derivation_pow_formula (k := k) (K := K) θ (x j) (e j : ℕ)
    _ = 0 := by
      simp [hθ_other j hji]

/-- Helper for Lemma 15.46.2: splitting a `p`-restricted monomial at an index with positive
exponent isolates the distinguished power factor. -/
lemma pMonomial_eq_prod_erase_mul_pow [DecidableEq ι] (x : ι → K) (i : ι) {e : ι →₀ Fin p}
    (hi : e i ≠ 0) :
    pMonomial p x e =
      (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) * x i ^ (e i : ℕ) := by
  classical
  -- Split the support product at `i`; positivity of the exponent is exactly what puts `i` into the
  -- support.
  have hi_mem : i ∈ e.support := Finsupp.mem_support_iff.mpr hi
  unfold pMonomial
  simpa [mul_comm] using
    (Finset.prod_erase_mul (s := e.support) (f := fun j ↦ x j ^ (e j : ℕ)) hi_mem).symm

/-- Helper for Lemma 15.46.2: lowering a positive exponent rewrites the corresponding monomial by
dropping one copy of the distinguished generator. -/
lemma pMonomial_lowerAt_eq_prod_erase_mul_pow_pred [DecidableEq ι] (x : ι → K) (i : ι)
    {e : ι →₀ Fin p} (hi : e i ≠ 0) :
    pMonomial p x (lowerAt (p := p) i e) =
      (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) * x i ^ ((e i : ℕ) - 1) := by
  classical
  -- Follow the source lowering route: compare the lowered support with `e.support.erase i`, then
  -- split according to whether the lowered exponent at `i` is still positive.
  let e' := lowerAt (p := p) i e
  have hsupport :
      e'.support.erase i = e.support.erase i := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [e', lowerAt_apply_of_ne (p := p) i j hji e, hji]
  have hpred :
      (e' i : ℕ) = (e i : ℕ) - 1 := by
    have hstep := lowerAt_apply_self_val_add_one_of_ne_zero (p := p) (i := i) hi
    have hpred' : Nat.pred (e i : ℕ) = (e' i : ℕ) := by
      rw [← hstep, Nat.pred_succ]
    simpa [Nat.pred_eq_sub_one] using hpred'.symm
  by_cases hmem : i ∈ e'.support
  · have hmem' : e' i ≠ 0 := Finsupp.mem_support_iff.mp hmem
    rw [pMonomial_eq_prod_erase_mul_pow (p := p) (x := x) (i := i) (e := e') (hi := hmem'),
      hsupport]
    congr 1
    · refine Finset.prod_congr rfl ?_
      intro j hj
      rw [lowerAt_apply_of_ne (p := p) i j (Finset.mem_erase.mp hj).1 e]
    · simp [hpred]
  · have hself_zero : e' i = 0 := by
      by_contra hne
      exact hmem (Finsupp.mem_support_iff.mpr hne)
    have herase : e'.support.erase i = e'.support := by
      ext j
      simp [hmem]
    have hprod :
        pMonomial p x e' = (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) := by
      unfold pMonomial
      rw [← herase, hsupport]
      refine Finset.prod_congr rfl ?_
      intro j hj
      rw [lowerAt_apply_of_ne (p := p) i j (Finset.mem_erase.mp hj).1 e]
    have hpow_zero : ((e i : ℕ) - 1) = 0 := by
      have hself_zero_nat : (e' i : ℕ) = 0 := by simp [hself_zero]
      omega
    calc
      pMonomial p x e' = (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) := hprod
      _ = (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) * x i ^ ((e i : ℕ) - 1) := by
        simp [hpow_zero]

/-- Helper for Lemma 15.46.2: a positive exponent monomial is one copy of the distinguished
generator times the lowered monomial. -/
lemma pMonomial_mul_lowerAt_factor (x : ι → K) (i : ι) {e : ι →₀ Fin p}
    (hi : e i ≠ 0) :
    x i * pMonomial p x (lowerAt (p := p) i e) = pMonomial p x e := by
  classical
  -- Rewrite both monomials by splitting off the distinguished index, then compare the remaining
  -- powers using the positive-exponent predecessor identity.
  rw [pMonomial_lowerAt_eq_prod_erase_mul_pow_pred (p := p) (x := x) (i := i) (e := e)
      (hi := hi),
    pMonomial_eq_prod_erase_mul_pow (p := p) (x := x) (i := i) (e := e) (hi := hi)]
  have hi_pos : 0 < (e i : ℕ) := Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
  calc
    x i * ((e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) * x i ^ ((e i : ℕ) - 1)) =
        (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) *
          (x i ^ 1 * x i ^ ((e i : ℕ) - 1)) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ = (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) *
          x i ^ (1 + ((e i : ℕ) - 1)) := by
      rw [← pow_add]
    _ = (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ)) * x i ^ (e i : ℕ) := by
      congr 2
      omega

/-- Helper for Lemma 15.46.2: differentiating a `p`-restricted monomial at a dual derivation lowers
the distinguished exponent by one and multiplies by that exponent. -/
lemma dual_derivation_apply_pMonomial_of_ne_zero (x : ι → K) (i : ι)
    (θ : Derivation k K K) (hθ_self : θ (x i) = 1)
    (hθ_other : ∀ j, j ≠ i → θ (x j) = 0) {e : ι →₀ Fin p}
    (hi : e i ≠ 0) :
    θ (pMonomial p x e) = ((e i : K)) * pMonomial p x (lowerAt (p := p) i e) := by
  classical
  -- Split the source monomial at `i`, kill the off-`i` product, and rewrite the remaining power
  -- derivative back into the lowered monomial from the source argument.
  let offProd := (e.support.erase i).prod (fun j ↦ x j ^ (e j : ℕ))
  have hoff_zero : θ offProd = 0 := by
    refine derivation_prod_eq_zero_of_forall (k := k) (K := K) θ (e.support.erase i)
      (fun j ↦ x j ^ (e j : ℕ)) ?_
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    calc
      θ (x j ^ (e j : ℕ)) = (((e j : ℕ) • x j ^ ((e j : ℕ) - 1) : K)) * θ (x j) := by
        simpa using scalar_derivation_pow_formula (k := k) (K := K) θ (x j) (e j : ℕ)
      _ = 0 := by
        simp [hθ_other j hji]
  calc
    θ (pMonomial p x e) = θ (offProd * x i ^ (e i : ℕ)) := by
      have hsplit := pMonomial_eq_prod_erase_mul_pow (p := p) (x := x) (i := i) (e := e)
        (hi := hi)
      simpa [offProd] using congrArg θ hsplit
    _ = offProd * θ (x i ^ (e i : ℕ)) + x i ^ (e i : ℕ) * θ offProd := by
      simpa [offProd, smul_eq_mul, add_comm, mul_comm, mul_left_comm] using
        θ.leibniz offProd (x i ^ (e i : ℕ))
    _ = offProd * θ (x i ^ (e i : ℕ)) := by simp [hoff_zero]
    _ = offProd * ((((e i : ℕ) • x i ^ ((e i : ℕ) - 1) : K)) * θ (x i)) := by
      rw [scalar_derivation_pow_formula (k := k) (K := K) θ (x i) (e i : ℕ)]
    _ = ((e i : K)) * (offProd * x i ^ ((e i : ℕ) - 1)) := by
      simp [hθ_self, nsmul_eq_mul, offProd, mul_assoc, mul_comm, mul_left_comm]
    _ = ((e i : K)) * pMonomial p x (lowerAt (p := p) i e) := by
      rw [← pMonomial_lowerAt_eq_prod_erase_mul_pow_pred (p := p) (x := x) (i := i) (e := e)
        (hi := hi)]

/-- Helper for Lemma 15.46.2: derivations dual to the chosen generators force
`p`-independence. -/
lemma pIndependent_of_dual_derivations (x : ι → K)
    (hdual : ∀ i, ∃ θ : Derivation k K K, θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0) :
    PIndependent p k K x := by
  -- Route correction: the missing source-faithful step is the minimal-total-weight contradiction on
  -- a nontrivial `p`-restricted monomial relation after differentiating with one of the dual
  -- derivations. The new helpers `pMonomialWeight` and `lowerAt_injective_on_pos` isolate the
  -- exponent bookkeeping, and the zero-exponent differential case is now packaged separately, so
  -- the remaining blocker is the positive-exponent lowering step in the minimal-weight argument.
  -- TODO: choose a minimal-support relation over `pPowerCompositum p k K`, use
  -- `derivation_eq_zero_of_mem_pPowerCompositum` to kill the coefficients, and apply the
  -- monomial-lowering rewrite for the chosen derivation to contradict minimality.
  sorry

/-- Helper for Lemma 15.46.2: the canonical map on Kähler differentials kills `D k K a` once
`a` already lies in the intermediate field. -/
lemma kaehler_map_D_eq_zero_of_mem_intermediate (L : IntermediateField k K) {a : K}
    (ha : a ∈ L) :
    KaehlerDifferential.map k L K K (D k K a) = 0 := by
  -- The owner formula `map_D` rewrites the source differential to the relative one over `L`,
  -- where universal derivations vanish on elements coming from the base field.
  let aL : L := ⟨a, ha⟩
  rw [KaehlerDifferential.map_D]
  simpa [aL] using (D L K).map_algebraMap aL

/-- Helper for Lemma 15.46.2: if the differentials of `x` span `Ω[K⁄k]`, then the relative
Kähler differentials over `L = adjoin(k(K^p), x)` are trivial. -/
lemma subsingleton_kaehler_of_span_differentials_eq_top_over_adjoin (x : ι → K)
    (hspan : Submodule.span K (Set.range (D k K ∘ x)) = ⊤) :
    Subsingleton Ω[K⁄(IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x))] := by
  let L : IntermediateField (pPowerCompositum p k K) K :=
    IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x)
  let Lk : IntermediateField k K := L.restrictScalars k
  let φ : Ω[K⁄k] →ₗ[K] Ω[K⁄Lk] := KaehlerDifferential.map k Lk K K
  have hspan_ker : Submodule.span K (Set.range (D k K ∘ x)) ≤ LinearMap.ker φ := by
    -- Each generator differential `D k K (x i)` already dies in the relative module over `L`.
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change φ (D k K (x i)) = 0
    exact kaehler_map_D_eq_zero_of_mem_intermediate
      (k := k) (K := K) (L := Lk) (a := x i)
      (by
        simpa [Lk] using
          (IntermediateField.subset_adjoin
            (F := pPowerCompositum p k K) (S := Set.range x) (by exact ⟨i, rfl⟩)))
  have htop_ker : (⊤ : Submodule K Ω[K⁄k]) ≤ LinearMap.ker φ := by
    simpa [hspan] using hspan_ker
  have hφ_zero : φ = 0 := by
    -- Once the span is all of `Ω[K⁄k]`, the canonical map vanishes identically.
    apply LinearMap.ext
    intro ω
    have hω : ω ∈ LinearMap.ker φ := by
      exact htop_ker (show ω ∈ (⊤ : Submodule K Ω[K⁄k]) from by trivial)
    exact LinearMap.mem_ker.mp hω
  have hsub : Subsingleton Ω[K⁄Lk] := by
    refine ⟨fun y z ↦ ?_⟩
    -- Surjectivity of the canonical map then forces every target vector to be zero.
    obtain ⟨y', rfl⟩ := KaehlerDifferential.map_surjective k Lk K y
    obtain ⟨z', rfl⟩ := KaehlerDifferential.map_surjective k Lk K z
    simp [φ, hφ_zero]
  simpa [Lk] using hsub

/-- Helper for Lemma 15.46.2: if the differentials of a `p`-independent family already span
`Ω[K⁄k]`, then the family generates `K` over `k(K^p)`. -/
lemma adjoin_eq_top_of_span_differentials_eq_top (x : ι → K) (hx : PIndependent p k K x)
    (hspan : Submodule.span K (Set.range (D k K ∘ x)) = ⊤) :
    IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x) = ⊤ := by
  -- Route correction: the previous enlargement/maximality route was the wrong abstraction here.
  -- The source-faithful bridge is the canonical map `Ω[K⁄k] → Ω[K⁄L]` for
  -- `L := IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x)`, which kills each
  -- generator differential `D k K (x i)` because `x i ∈ L`; surjectivity then makes `Ω[K⁄L]`
  -- subsingleton, and the new helper
  -- `eq_top_of_subsingleton_kaehler_of_frobeniusSubfield_le` finishes.
  -- TODO: after the finite-type-free collapse lemma above is available, combine it with the
  -- newly proved subsingleton statement for `Ω[K⁄L]` to conclude that the adjoin is all of `K`.
  sorry

/-- Helper for Lemma 15.46.2: a `p`-independent family can be enlarged so that the resulting
family of differentials is both linearly independent and spanning in `Ω[K⁄k]`. -/
lemma exists_extension_with_basis_differentials (x : ι → K) (hx : PIndependent p k K x) :
    ∃ (ι' : Type (max v w)) (y : ι' → K) (e : ι ↪ ι'),
      (∀ i, y (e i) = x i) ∧
        LinearIndependent K (D k K ∘ y) ∧
          Submodule.span K (Set.range (D k K ∘ y)) = ⊤ := by
  -- Route correction: the remaining source-faithful step is to enlarge `x` inside `Ω[K⁄k]`,
  -- convert the enlarged differential family back to a `p`-independent family via the reverse
  -- differential criterion, and then use the adjoin-converse to upgrade spanning to generation.
  -- TODO: first prove `LinearIndependent K (D k K ∘ x)` from `hx`, then apply
  -- `exists_basis_extension_in_differential_range`; choose preimages in `K` for the basis vectors
  -- inside `Set.range (D k K)`, and finally combine
  -- `pIndependent_of_dual_derivations` with
  -- `adjoin_eq_top_of_span_differentials_eq_top` to show the enlarged family is a `p`-basis.
  sorry

/-- Helper for Lemma 15.46.2: a `p`-independent family extends to a `p`-basis. -/
lemma exists_isPBasis_extension_aux (x : ι → K) (hx : PIndependent p k K x) :
    ∃ (ι' : Type (max v w)) (y : ι' → K) (e : ι ↪ ι'),
      (∀ i, y (e i) = x i) ∧ IsPBasis p k K y := by
  -- Follow the strengthened extension route: first enlarge `x` so that the resulting differentials
  -- form a basis of `Ω[K⁄k]`, then turn those two differential properties back into the two
  -- clauses of `IsPBasis`.
  obtain ⟨ι', y, e, he, hyLin, hySpan⟩ :=
    exists_extension_with_basis_differentials (p := p) (k := k) (K := K) x hx
  have hyDual : ∀ i, ∃ θ : Derivation k K K, θ (y i) = 1 ∧
      ∀ j, j ≠ i → θ (y j) = 0 := by
    intro i
    exact exists_dual_derivation_of_linearIndependent_differentials
      (k := k) (K := K) y hyLin i
  have hyP : PIndependent p k K y := by
    -- The reverse differential criterion upgrades the enlarged linearly independent family to
    -- `p`-independence.
    exact pIndependent_of_dual_derivations (p := p) (k := k) (K := K) y hyDual
  have hyTop : IntermediateField.adjoin (pPowerCompositum p k K) (Set.range y) = ⊤ := by
    -- Once the enlarged differential family spans all differentials, the converse adjoin lemma
    -- upgrades that spanning statement to generation of `K`.
    exact adjoin_eq_top_of_span_differentials_eq_top (p := p) (k := k) (K := K) y hyP hySpan
  exact ⟨ι', y, e, he, ⟨hyP, hyTop⟩⟩

/-- Helper for Lemma 15.46.2: the differentials attached to a `p`-basis are linearly independent. -/
lemma linearIndependent_differentials_of_isPBasis (x : ι → K) (hx : IsPBasis p k K x) :
    LinearIndependent K (D k K ∘ x) := by
  -- Use the strengthened extension helper on the `p`-independent part of the basis and then
  -- restrict the resulting independent differential family back along the embedding.
  obtain ⟨ι', y, e, he, hyLin, -⟩ :=
    exists_extension_with_basis_differentials (p := p) (k := k) (K := K) x hx.1
  have hcomp : (D k K ∘ x) = (D k K ∘ y) ∘ e := by
    -- The embedding records that the enlarged family extends the original one pointwise.
    funext i
    simp [Function.comp_apply, he i]
  rw [hcomp]
  exact hyLin.comp e e.injective
-- Proof sketch: identify `k`-derivations of `K` with `K`-linear maps out of `Ω[K⁄k]`, then use
-- the standard characteristic-`p` argument that `p`-restricted monomial relations are detected by
-- derivations.
/-- Lemma 15.46.2 (1): a family in a characteristic-`p` field extension is `p`-independent over
`k` if and only if its differentials are `K`-linearly independent in `Ω[K⁄k]`. -/
theorem pIndependent_iff_linearIndependent_differentials (x : ι → K) :
    PIndependent p k K x ↔
      LinearIndependent K (D k K ∘ x) := by
  -- Route correction: the source proof first constructs dual derivations from the independent
  -- differentials, then uses them to rule out nontrivial `p`-monomial relations.
  constructor
  · intro hx
    -- Extend the given `p`-independent family to a `p`-basis and then restrict the linear
    -- independence of the larger differential family back along the embedding.
    obtain ⟨ι', y, e, he, hy⟩ :=
      exists_isPBasis_extension_aux (p := p) (k := k) (K := K) x hx
    have hyLin : LinearIndependent K (D k K ∘ y) :=
      linearIndependent_differentials_of_isPBasis (p := p) (k := k) (K := K) y hy
    have hcomp : (D k K ∘ x) = (D k K ∘ y) ∘ e := by
      funext i
      simp [Function.comp_apply, he i]
    rw [hcomp]
    exact hyLin.comp e e.injective
  · intro hlin
    -- The basis-extension argument above already manufactures dual derivations for the family.
    have hdual : ∀ i, ∃ θ : Derivation k K K, θ (x i) = 1 ∧
        ∀ j, j ≠ i → θ (x j) = 0 := by
      intro i
      exact exists_dual_derivation_of_linearIndependent_differentials
        (k := k) (K := K) x hlin i
    exact pIndependent_of_dual_derivations (p := p) (k := k) (K := K) x hdual

-- Proof sketch: apply Zorn's lemma to enlarge a `p`-independent family to a maximal one, then
-- show that maximal `p`-independent families generate `K` over `k(K^p)`.
/-- Lemma 15.46.2 (2): every `p`-independent family in `K` extends to a `p`-basis of `K` over
`k`. -/
theorem exists_isPBasis_extension (x : ι → K) (hx : PIndependent p k K x) :
    ∃ (ι' : Type (max v w)) (y : ι' → K) (e : ι ↪ ι'),
      (∀ i, y (e i) = x i) ∧ IsPBasis p k K y := by
  -- Delegate to the source-faithful maximality construction isolated above.
  exact exists_isPBasis_extension_aux (p := p) (k := k) (K := K) x hx

-- Proof sketch: start from the empty `p`-independent family and apply the extension statement.
/-- Lemma 15.46.2 (3): the field `K` admits a `p`-basis over `k`. -/
theorem exists_isPBasis :
    ∃ (ι : Type v) (x : ι → K), IsPBasis p k K x := by
  let x : ULift.{v, 0} Empty → K := fun i ↦ nomatch i.down
  have hlin : LinearIndependent K (D k K ∘ x) := linearIndependent_empty_type
  have hx : PIndependent p k K x :=
    (pIndependent_iff_linearIndependent_differentials (p := p) (k := k) (K := K) x).2 hlin
  obtain ⟨ι', y, e, -, hy⟩ :=
    exists_isPBasis_extension (p := p) (k := k) (K := K) x hx
  exact ⟨ι', y, hy⟩

-- Proof sketch: combine the first equivalence with the spanning criterion for `Ω[K⁄k]`; a
-- `p`-basis gives a linearly independent spanning family of differentials, and conversely such a
-- family is a maximal `p`-independent family.
/-- Lemma 15.46.2 (4): a family is a `p`-basis of `K` over `k` if and only if its differentials
are `K`-linearly independent and span `Ω[K⁄k]`. -/
theorem isPBasis_iff_differentials_formBasis (x : ι → K) :
    IsPBasis p k K x ↔
      LinearIndependent K (D k K ∘ x) ∧
        Submodule.span K (Set.range (D k K ∘ x)) = ⊤ := by
  constructor
  · intro hx
    rcases hx with ⟨hx_indep, hx_top⟩
    refine ⟨(pIndependent_iff_linearIndependent_differentials
      (p := p) (k := k) (K := K) x).1 hx_indep, ?_⟩
    exact span_differentials_of_adjoin_eq_top (p := p) (k := k) (K := K) x hx_top
  · rintro ⟨hlin, hspan⟩
    have hx : PIndependent p k K x :=
      (pIndependent_iff_linearIndependent_differentials
        (p := p) (k := k) (K := K) x).2 hlin
    refine ⟨hx, ?_⟩
    exact adjoin_eq_top_of_span_differentials_eq_top (p := p) (k := k) (K := K) x hx hspan

end PBasis
