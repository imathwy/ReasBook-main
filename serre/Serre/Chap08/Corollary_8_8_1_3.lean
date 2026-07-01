import Serre.Chap08.Proposition_8_8_1_1
import Serre.Chap08.Remark_8_8_1_2
import Serre.Chap02.Theorem_2_2_3_5
import Serre.Chap02.Proposition_2_2_2_1
import Serre.Chap06.Corollary_6_6_5_3
import Serre.Chap06.Proposition_6_6_5_1
import Serre.Chap06.Exercise_6_6_5_6
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.LinearAlgebra.TensorPower.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Representation

noncomputable section

open scoped BigOperators MonoidAlgebra TensorProduct Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

local instance finiteGroupFintypeCorollary8813 : Fintype G := Fintype.ofFinite G

/- Source/core/bridge triage:
* `source-facing`: Serre's divisibility statement for an irreducible complex representation and an
  abelian normal subgroup `A`.
* `core/canonical`: the Chapter 6 owner theorem `finrank_dvd_center_index`.
* `bridge/view`: the descended quotient representation `Representation.ofQuotient ρ ρ.ker`,
  together with the Chapter 8 induction/isotypy alternative and the scalar-action-to-centrality
  bridge used to pass from isotypy on `A` to centrality in `G ⧸ ρ.ker`.

Sampled owner declarations in this domain:
* `Representation.ofQuotient`
* `exists_proper_overgroup_irreducible_induced_or_restriction_isotypic`
* `restriction_isotypic_iff_exists_character_of_commutative_subgroup`
* `quotient_mk_mem_center_of_exists_smul_id`
* `finrank_dvd_center_index`

Primitive data versus derived API:
the primitive source data are only `A`, its normal commutative structure, and the irreducible
representation `ρ`. The descended quotient representation `Representation.ofQuotient ρ ρ.ker`,
the induction branch from Proposition `8-8.1-1`, the scalar-action criterion from Remark
`8-8.1-2`, and the centrality statement in the kernel quotient are all derived bridge data, so
this file should expose only the divisibility theorem and reuse those owners directly rather than
introducing an intermediate subgroup-image wrapper.

Proof sketch: apply
`exists_proper_overgroup_irreducible_induced_or_restriction_isotypic`. In the induced case, use
induction on the order of `G` and multiplicativity of subgroup indices to pass divisibility from a
proper overgroup `H` to `G`. In the isotypic case,
`restriction_isotypic_iff_exists_character_of_commutative_subgroup` yields a linear character
`χ : A →* ℂˣ` whose scalar action makes every element of `A` act on `V` by a homothety, so
`quotient_mk_mem_center_of_exists_smul_id` places the image of `A` inside the center of
`G ⧸ ρ.ker`; then `finrank_dvd_center_index` applied to `Representation.ofQuotient ρ ρ.ker` gives
the divisibility, and `Subgroup.index_map_dvd` transfers it back to `A.index`. -/
/-- Helper for Corollary 8-8.1-3: the `q`-indexed translate in an induced decomposition is
linearly equivalent to the explicit `q.out`-translate of `W`. -/
lemma leftQuotientSubmodule_out_local
    {H : Subgroup G} (ρ : Representation ℂ G V)
    (W : Subrepresentation (ρ.comp H.subtype)) (q : G ⧸ H) :
    ρ.leftQuotientSubmodule H W q = W.toSubmodule.map (ρ q.out) := by
  -- Replace the quotient class `q` by its chosen representative so the owner definition unfolds.
  simpa [Quotient.out_eq q] using (ρ.leftQuotientSubmodule_mk H W q.out)

/-- Helper for Corollary 8-8.1-3: the `q`-indexed translate in an induced decomposition is
linearly equivalent to the original inducing subspace `W`. -/
noncomputable def leftQuotientSubmoduleEquiv_local
    {H : Subgroup G} (ρ : Representation ℂ G V)
    (W : Subrepresentation (ρ.comp H.subtype)) (q : G ⧸ H) :
    W.toSubmodule ≃ₗ[ℂ] ρ.leftQuotientSubmodule H W q :=
  let e : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  (e.submoduleMap W.toSubmodule).trans
    (LinearEquiv.ofEq _ _ (leftQuotientSubmodule_out_local (ρ := ρ) W q).symm)

/-- Helper for Corollary 8-8.1-3: an induced representation has degree equal to the subgroup
index times the degree of the inducing subrepresentation. -/
lemma finrank_eq_index_mul_finrank_of_isInducedFromSubrepresentation
    {H : Subgroup G} (ρ : Representation ℂ G V)
    [FiniteDimensional ℂ V]
    (W : Subrepresentation (ρ.comp H.subtype))
    (hInduced : ρ.IsInducedFromSubrepresentation H W) :
    Module.finrank ℂ V = H.index * Module.finrank ℂ W.toSubmodule := by
  classical
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule H W) := by
    -- Unpack the Chapter `3` owner predicate into the internal direct-sum family it controls.
    simpa [Representation.IsInducedFromSubrepresentation] using hInduced
  letI := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule H W) hInternal
  letI : ∀ q : G ⧸ H, Module.Free ℂ (ρ.leftQuotientSubmodule H W q) :=
    fun q ↦ Module.Free.of_divisionRing ℂ _
  let e := (DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule H W)).symm
  -- Compare `V` with the external direct sum of its coset components and then replace each
  -- component by the original inducing subspace via the transport equivalence.
  calc
    Module.finrank ℂ V = Module.finrank ℂ (DirectSum (G ⧸ H) fun q ↦ ρ.leftQuotientSubmodule H W q) := by
      exact e.finrank_eq.symm
    _ = ∑ q : G ⧸ H, Module.finrank ℂ (ρ.leftQuotientSubmodule H W q) := by
      exact Module.finrank_directSum (R := ℂ) (M := fun q ↦ ρ.leftQuotientSubmodule H W q)
    _ = ∑ _q : G ⧸ H, Module.finrank ℂ W.toSubmodule := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      simpa using (leftQuotientSubmoduleEquiv_local (ρ := ρ) W q).finrank_eq.symm
    _ = H.index * Module.finrank ℂ W.toSubmodule := by
      simp [Subgroup.index_eq_card]

/-- Helper for Corollary 8-8.1-3: divisibility inside a proper overgroup lifts to divisibility by
the ambient index when the ambient representation is induced from that overgroup. -/
lemma subgroup_index_eq_subgroupOf_index_mul_index_local
    {A H : Subgroup G} (hAH : A ≤ H) :
    A.index = (A.subgroupOf H).index * H.index := by
  -- Rewrite the ambient subgroup index through the intermediate overgroup `H`.
  simpa [Subgroup.relIndex] using (Subgroup.relIndex_mul_index hAH).symm

/-- Helper for Corollary 8-8.1-3: divisibility inside a proper overgroup lifts to divisibility by
the ambient index when the ambient representation is induced from that overgroup. -/
lemma dvd_index_of_induced_from_overgroup
    {A H : Subgroup G} (ρ : Representation ℂ G V)
    [FiniteDimensional ℂ V]
    (hAH : A ≤ H)
    (W : Subrepresentation (ρ.comp H.subtype))
    (hInduced : ρ.IsInducedFromSubrepresentation H W)
    (hWdiv : Module.finrank ℂ W.toSubmodule ∣ (A.subgroupOf H).index) :
    Module.finrank ℂ V ∣ A.index := by
  rcases hWdiv with ⟨d, hd⟩
  -- Rewrite the ambient degree by Serre's induced-dimension formula and the subgroup-index
  -- factorization `A.index = (A : H) * H.index`.
  refine ⟨d, ?_⟩
  calc
    A.index = (A.subgroupOf H).index * H.index := by
      exact subgroup_index_eq_subgroupOf_index_mul_index_local hAH
    _ = (Module.finrank ℂ W.toSubmodule * d) * H.index := by rw [hd]
    _ = H.index * Module.finrank ℂ W.toSubmodule * d := by ac_rfl
    _ = Module.finrank ℂ V * d := by
      rw [finrank_eq_index_mul_finrank_of_isInducedFromSubrepresentation (ρ := ρ) W hInduced]

/-- Helper for Corollary 8-8.1-3: if `ρ s` is a scalar endomorphism, then the image of `s` in the
quotient by `ρ.ker` is central. -/
lemma quotient_mk_mem_center_of_exists_smul_id_local
    (ρ : Representation ℂ G V) (s : G)
    (hsmul : ∃ z : ℂ, ρ s = z • 1) :
    (QuotientGroup.mk s : G ⧸ ρ.ker) ∈ Subgroup.center (G ⧸ ρ.ker) := by
  rw [Subgroup.mem_center_iff]
  intro q
  refine Quotient.inductionOn q ?_
  intro g
  -- Compare the operators of `g * s` and `s * g`; their equality is exactly the kernel
  -- criterion for centrality in the quotient.
  change (QuotientGroup.mk (g * s) : G ⧸ ρ.ker) = QuotientGroup.mk (s * g)
  rw [QuotientGroup.eq_iff_div_mem, MonoidHom.div_mem_ker_iff ρ]
  rcases hsmul with ⟨z, hz⟩
  calc
    ρ (g * s) = ρ g * ρ s := by rw [ρ.map_mul]
    _ = ρ g * (z • 1) := by rw [hz]
    _ = z • ρ g := by simp
    _ = (z • 1) * ρ g := by simp
    _ = ρ s * ρ g := by rw [hz]
    _ = ρ (s * g) := by rw [ρ.map_mul]

/-- Helper for Corollary 8-8.1-3: quotienting by a normal subgroup that acts trivially preserves
irreducibility because the quotient representation has the same invariant subspaces. -/
lemma isIrreducible_of_ofQuotient_of_isTrivial_local
    (ρ : Representation ℂ G V) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (ρ.comp S.subtype)] [ρ.IsIrreducible] :
    Representation.IsIrreducible (ρ.ofQuotient S) := by
  letI : Nontrivial (Subrepresentation (ρ.ofQuotient S)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  -- Any nonzero quotient-stable subspace is already a nonzero `ρ`-subrepresentation, hence it
  -- must be all of `V`.
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W.apply_mem_toSubmodule (g : G ⧸ S) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Corollary 8-8.1-3: the action of the center on an irreducible complex
representation is given by a multiplicative scalar character. -/
lemma center_scalar_action_hom_local
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ∃ μ : Subgroup.center G →* ℂ, ∀ s : Subgroup.center G,
      ρ (s : G) = μ s • (1 : Module.End ℂ V) := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Module (MonoidAlgebra ℂ G) V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule (MonoidAlgebra ℂ G) V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) V
  let exists_smul_id_of_mem_center :
      ∀ s : G, s ∈ Submonoid.center G → ∃ z : ℂ, ρ s = z • (1 : Module.End ℂ V) :=
    fun s hs ↦ by
      -- Schur's lemma identifies every central intertwiner with a scalar homothety.
      obtain ⟨z, hz⟩ := intertwiningMap_eq_smul_id (ρ := ρ)
        (Representation.IntertwiningMap.centralMul ρ s hs)
      refine ⟨z, ?_⟩
      simpa using congrArg Representation.IntertwiningMap.toLinearMap hz
  let scalar : Subgroup.center G → ℂ := fun s ↦
    Classical.choose <| exists_smul_id_of_mem_center (s : G)
      (show (s : G) ∈ Submonoid.center G from by
        simpa [Subgroup.center_toSubmonoid] using s.2)
  have hscalar (s : Subgroup.center G) :
      ρ (s : G) = scalar s • (1 : Module.End ℂ V) := by
    -- Each central element acts by the chosen scalar extracted from Schur's lemma.
    simpa [scalar] using
      (Classical.choose_spec <| exists_smul_id_of_mem_center (s : G)
        (show (s : G) ∈ Submonoid.center G from by
          simpa [Subgroup.center_toSubmonoid] using s.2))
  have hsmul_injective : Function.Injective fun z : ℂ ↦ z • (1 : Module.End ℂ V) := by
    -- A scalar multiple of the identity is determined by its value on any nonzero vector.
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro z w hzw
    have hvw : z • v = w • v := by
      simpa using congrArg (fun f : Module.End ℂ V ↦ f v) hzw
    have hsub : (z - w) • v = 0 := by
      rw [sub_smul, hvw, sub_self]
    rcases smul_eq_zero.mp hsub with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact (hv hzero).elim
  refine ⟨{
    toFun := scalar
    map_one' := by
      -- The identity element acts as the identity operator, so its scalar is `1`.
      apply hsmul_injective
      calc
        scalar 1 • (1 : Module.End ℂ V) = ρ (1 : G) := (hscalar 1).symm
        _ = (1 : ℂ) • (1 : Module.End ℂ V) := by simp
    map_mul' := by
      intro s t
      -- Multiplicativity follows by comparing `ρ (s * t)` with `ρ s * ρ t`.
      apply hsmul_injective
      calc
        scalar (s * t) • (1 : Module.End ℂ V) = ρ (s * t : G) := (hscalar (s * t)).symm
        _ = ρ (s : G) * ρ (t : G) := by simp
        _ = (scalar s * scalar t) • (1 : Module.End ℂ V) := by
            rw [hscalar s, hscalar t]
            calc
              (scalar s • (1 : Module.End ℂ V)) * (scalar t • (1 : Module.End ℂ V))
                  = scalar s • ((1 : Module.End ℂ V) * (scalar t • (1 : Module.End ℂ V))) := by
                      rw [smul_mul_assoc]
              _ = scalar s • (scalar t • (1 : Module.End ℂ V)) := by simp
              _ = (scalar s * scalar t) • (1 : Module.End ℂ V) := by rw [smul_smul]
  }, hscalar⟩

/-- Helper for Corollary 8-8.1-3: if every positive power of `n` divides the corresponding power
of `a` up to a fixed nonzero factor `c`, then `n` already divides `a`. -/
lemma dvd_of_forall_succ_pow_dvd_center_card_mul_pow_local
    {n c a : ℕ} (hc : 0 < c)
    (h : ∀ m : ℕ, n ^ (m + 1) ∣ c * a ^ (m + 1)) :
    n ∣ a := by
  by_cases hn : n = 0
  · -- If `n = 0`, the first divisibility relation forces `a = 0`.
    subst hn
    have hzero := h 0
    rw [pow_one, zero_dvd_iff] at hzero
    have ha0 : a = 0 := by
      rw [pow_one, mul_eq_zero] at hzero
      exact Or.resolve_left hzero hc.ne'
    simp [ha0]
  by_cases ha : a = 0
  · -- If `a = 0`, divisibility is immediate.
    subst ha
    exact dvd_zero n
  -- Compare prime factor valuations with the special choice `m = v_p(c)`.
  refine Nat.factorization_le_iff_dvd hn ha |>.mp ?_
  intro p
  by_cases hp : Nat.Prime p
  · let m := c.factorization p
    have hdiv := h m
    have hfac :=
      Nat.factorization_le_iff_dvd (pow_ne_zero (m + 1) hn)
        (mul_ne_zero hc.ne' (pow_ne_zero (m + 1) ha)) |>.mpr hdiv
    have hfac' := hfac p
    have hfac'' : (m + 1) * n.factorization p ≤ m + (m + 1) * a.factorization p := by
      simpa [Nat.factorization_mul hc.ne' (pow_ne_zero (m + 1) ha), Nat.factorization_pow,
        Finsupp.smul_apply, Pi.smul_apply, m] using hfac'
    refine le_of_not_gt ?_
    intro hlt
    have hsucc : a.factorization p + 1 ≤ n.factorization p := Nat.succ_le_of_lt hlt
    have hpow :
        (m + 1) * (a.factorization p + 1) ≤ m + (m + 1) * a.factorization p := by
      exact le_trans (Nat.mul_le_mul_left (m + 1) hsucc) hfac''
    have hpow' :
        (m + 1) * a.factorization p + (m + 1) ≤ (m + 1) * a.factorization p + m := by
      simpa [Nat.mul_add, add_comm, add_left_comm, add_assoc] using hpow
    have hm : m + 1 ≤ m := by
      exact add_le_add_iff_left ((m + 1) * a.factorization p) |>.mp hpow'
    exact (Nat.not_succ_le_self m) hm
  · simpa [Nat.factorization_eq_zero_of_not_prime n hp,
      Nat.factorization_eq_zero_of_not_prime a hp]

/-- Helper for Corollary 8-8.1-3: the inverse character of a finite-dimensional representation is
a class function. -/
lemma inverse_character_mem_classFunctionSubmodule_local [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    (fun s : G ↦ ρ.character s⁻¹) ∈ classFunctionSubmodule ℂ G := by
  -- Conjugate elements have conjugate inverses, so the inverse character stays constant on
  -- conjugacy classes.
  rw [mem_classFunctionSubmodule_iff]
  refine ⟨?_⟩
  intro a b hab
  rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, hg⟩
  calc
    ρ.character a⁻¹ = ρ.character (g * a⁻¹ * g⁻¹) := by
      exact (ρ.char_conj a⁻¹ g).symm
    _ = ρ.character b⁻¹ := by
      -- Rewrite the conjugate of `a⁻¹` as `b⁻¹`.
      have hinv : g * a⁻¹ * g⁻¹ = b⁻¹ := by
        rw [← hg]
        simp [mul_assoc]
      simp [hinv]

/-- Helper for Corollary 8-8.1-3: the self-pairing of an irreducible character is the group
order. -/
lemma character_self_pairing_sum_eq_card_local [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] [Invertible (Nat.card G : ℂ)] :
    ∑ s : G, ρ.character s⁻¹ * ρ.character s = Nat.card G := by
  -- Orthogonality identifies the normalized character pairing with the self-intertwining rank.
  have hpair := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  have hpair' : (Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s⁻¹ * ρ.character s = 1 := by
    simpa [mul_comm, IsIrreducible.finrank_intertwiningMap_self ρ] using hpair
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  -- Clear the normalized factor to recover the unscaled sum.
  field_simp [hcard] at hpair'
  simpa using hpair'

/-- Helper for Corollary 8-8.1-3: if `(m : ℂ) / n` is integral over `ℤ`, then `n` divides `m`.
-/
lemma nat_dvd_of_isIntegral_natCast_div_local {m n : ℕ} (hn : n ≠ 0)
    (h : IsIntegral ℤ ((m : ℂ) / n)) :
    n ∣ m := by
  let q : ℚ := m / n
  have hq : IsIntegral ℤ q := by
    -- Descend integrality from `ℂ` to the rational scalar itself.
    have hqC : IsIntegral ℤ (q : ℂ) := by
      simpa [q] using h
    exact IsIntegral.ratCast_iff.mp hqC
  obtain ⟨z, hz : q = z⟩ := hq.exists_int_iff_exists_rat |>.mp ⟨q, rfl⟩
  have hden : q.den = 1 := by
    -- Once the rational is an integer, its denominator is `1`.
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m n hn).mp <| by
    simpa [q] using hden

/-- Helper for Corollary 8-8.1-3: an irreducible complex representation has degree dividing the
group order. -/
lemma finrank_dvd_card_local (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Module.finrank ℂ V ∣ Nat.card G := by
  classical
  -- Install the finite-dimensional and simple-module instances needed by the Chapter 6 API.
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  have hfinrank_ne_zero : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt Module.finrank_pos
  letI : NeZero (Module.finrank ℂ V : ℂ) := ⟨hfinrank_ne_zero⟩
  have hcard_ne_zero : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne_zero
  let f : classFunctionSubmodule ℂ G :=
    ⟨fun s ↦ ρ.character s⁻¹, inverse_character_mem_classFunctionSubmodule_local (ρ := ρ)⟩
  let u : Subalgebra.center ℂ (ℂ[G]) :=
    ⟨Finsupp.equivFunOnFinite.symm (f : G → ℂ), mem_center_of_classFunction ℂ f⟩
  have hu : ∀ s : G, ((u : ℂ[G]) s) = ρ.character s⁻¹ := by
    -- The coefficients of the packaged central element are exactly the inverse character values.
    intro s
    simp [u, f]
  have hcoeff : ∀ s : G, IsIntegral ℤ ((u : ℂ[G]) s) := by
    -- Proposition `6-6.5-1` gives algebraic integrality of each inverse character coefficient.
    intro s
    rw [hu s]
    exact char_isIntegral_of_isOfFinOrder ρ (isOfFinOrder_of_finite s⁻¹)
  have hsum : ∑ s : G, ρ.character s⁻¹ * ρ.character s = Nat.card G := by
    -- This is the standard orthogonality step from the Chapter 6 source proof.
    exact character_self_pairing_sum_eq_card_local (ρ := ρ)
  have hint :
      IsIntegral ℤ ((Nat.card G : ℂ) / Module.finrank ℂ V) := by
    have hint_raw := isIntegral_finrank_inv_sum_coeff_mul_character (ρ := ρ) u hcoeff
    have hsum' :
        (Module.finrank ℂ V : ℂ)⁻¹ * ∑ s : G, (u : ℂ[G]) s * ρ.character s =
          (Nat.card G : ℂ) / Module.finrank ℂ V := by
      -- Rewrite the Chapter 6 integrality statement using the explicit coefficients of `u` and
      -- the character self-pairing identity.
      calc
        (Module.finrank ℂ V : ℂ)⁻¹ * ∑ s : G, (u : ℂ[G]) s * ρ.character s
            = (Module.finrank ℂ V : ℂ)⁻¹ * ∑ s : G, ρ.character s⁻¹ * ρ.character s := by
                simp [hu]
        _ = (Module.finrank ℂ V : ℂ)⁻¹ * Nat.card G := by
              rw [hsum]
        _ = (Nat.card G : ℂ) / Module.finrank ℂ V := by
              simp [div_eq_mul_inv, mul_comm]
    rw [hsum'] at hint_raw
    exact hint_raw
  -- A rational algebraic integer is an integer, so the denominator `dim V` divides `|G|`.
  exact nat_dvd_of_isIntegral_natCast_div_local
    (n := Module.finrank ℂ V) (m := Nat.card G) (Nat.ne_of_gt Module.finrank_pos) hint

/-- Helper for Corollary 8-8.1-3: the external tensor product of two representations is the
canonical tensor-product representation after precomposing with the product projections. -/
abbrev externalTensorRep_local
    {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂]
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    (σ : Representation ℂ G₁ V₁) (τ : Representation ℂ G₂ V₂) :
    Representation ℂ (G₁ × G₂) (TensorProduct ℂ V₁ V₂) :=
  Representation.tprod (σ.comp (MonoidHom.fst G₁ G₂)) (τ.comp (MonoidHom.snd G₁ G₂))

/-- Helper for Corollary 8-8.1-3: precomposing an irreducible representation with a group
equivalence preserves irreducibility. -/
lemma isIrreducible_comp_of_mulEquiv_local
    {G₁ : Type*} [Group G₁] {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    (e : G ≃* G₁) (σ : Representation ℂ G₁ V₁) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  -- Transport subrepresentations along the group equivalence and reuse simplicity of `σ`.
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W.apply_mem_toSubmodule (e.symm g) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Corollary 8-8.1-3: a representation equivalence transports subrepresentations by
mapping along the underlying linear equivalence. -/
noncomputable def subrepresentationOrderIso_local
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} (e : σ.Equiv τ) :
    Subrepresentation σ ≃o Subrepresentation τ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- Mapping an invariant subspace through an intertwining equivalence preserves invariance.
        refine ⟨σ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- The inverse equivalence transports invariance back in the same way.
        refine ⟨τ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv U := by
    -- Mapping to `τ` and back to `σ` recovers the original invariant subspace.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simp at hy
      exact hy
    · intro hx
      change x ∈
        Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv U := by
    -- The same computation shows that transport to `σ` and back is inverse on `τ`.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simp at hy
      exact hy
    · intro hx
      change x ∈
        Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  map_rel_iff' := by
    intro U U'
    constructor
    · intro h x hx
      -- Inclusion after transport implies inclusion before transport because `e` is injective.
      have hx' : e x ∈ U.toSubmodule.map e.toLinearMap := ⟨x, hx, rfl⟩
      rcases h hx' with ⟨y, hy, hxy⟩
      have : y = x := by
        apply e.toLinearEquiv.injective
        simpa [hxy]
      simpa [this] using hy
    · intro h x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for Corollary 8-8.1-3: equivalent representations have isomorphic subrepresentation
lattices, so irreducibility transfers across the equivalence. -/
lemma isIrreducible_of_nonempty_equiv_local
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W}
    [σ.IsIrreducible] (h : Nonempty (σ.Equiv τ)) :
    Representation.IsIrreducible τ := by
  rcases h with ⟨e⟩
  -- Transport the simple subrepresentation lattice of `σ` across the equivalence.
  exact (subrepresentationOrderIso_local e).isSimpleOrder_iff.mp inferInstance

/-- Helper for Corollary 8-8.1-3: replace a finite-dimensional representation by a small finite
model while shrinking the group universe to level `0`. -/
noncomputable def finiteModelRep_local [Module.Finite ℂ V] (ρ : Representation ℂ G V) :
    Representation ℂ (Shrink.{0} G) (FGModuleRepr.ofFinite ℂ V) where
  toFun g :=
    (FGModuleRepr.ofFiniteEquiv ℂ V).symm.toLinearMap.comp
      ((ρ (Shrink.mulEquiv g)).comp (FGModuleRepr.ofFiniteEquiv ℂ V).toLinearMap)
  map_one' := by
    -- The transported action is conjugation by the chosen finite-model equivalence.
    ext x
    simp
  map_mul' g h := by
    -- Conjugation preserves multiplication, so this is still a representation action.
    ext x
    simp [LinearMap.comp_apply]

/-- Helper for Corollary 8-8.1-3: the small finite model is equivalent to the original
representation precomposed with the shrink equivalence. -/
noncomputable def finiteModelRepEquivComp_local [Module.Finite ℂ V] (ρ : Representation ℂ G V) :
    (finiteModelRep_local ρ).Equiv
      (ρ.comp (Shrink.mulEquiv : Shrink.{0} G ≃* G).toMonoidHom) :=
  Representation.Equiv.mk (FGModuleRepr.ofFiniteEquiv ℂ V) (fun g => by
    -- The finite-model equivalence intertwines the transported action by construction.
    ext x
    simp [finiteModelRep_local, LinearMap.comp_apply])

/-- Helper for Corollary 8-8.1-3: shrinking both factors of a product group is equivalent to
shrinking the product itself. -/
noncomputable def prodShrinkMulEquiv_local
    {H : Type*} [Group H] [Finite H] :
    (Shrink.{0} G × Shrink.{0} H) ≃* Shrink.{0} (G × H) :=
  (MulEquiv.prodCongr (Shrink.mulEquiv : Shrink.{0} G ≃* G)
      (Shrink.mulEquiv : Shrink.{0} H ≃* H)).trans
    (Shrink.mulEquiv : Shrink.{0} (G × H) ≃* (G × H)).symm

/-- Helper for Corollary 8-8.1-3: the tensor product of the two small finite models is a small
finite model for the tensor-product space. -/
noncomputable def finiteModelTensorEquiv_local
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W] [Module.Finite ℂ (TensorProduct ℂ V W)] :
    (TensorProduct ℂ (FGModuleRepr.ofFinite ℂ V) (FGModuleRepr.ofFinite ℂ W)) ≃ₗ[ℂ]
      FGModuleRepr.ofFinite ℂ (TensorProduct ℂ V W) :=
  (TensorProduct.congr (FGModuleRepr.ofFiniteEquiv ℂ V) (FGModuleRepr.ofFiniteEquiv ℂ W)).trans
    (FGModuleRepr.ofFiniteEquiv ℂ (TensorProduct ℂ V W)).symm

/-- Helper for Corollary 8-8.1-3: after identifying the shrunk product group and the finite-model
tensor space, the external tensor of the finite models matches the finite model of the external
tensor product. -/
noncomputable def finiteModelExternalTensorEquiv_local
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W] [Module.Finite ℂ (TensorProduct ℂ V W)]
    (σ : Representation ℂ G V) (τ : Representation ℂ H W) :
    Representation.Equiv
      ((externalTensorRep_local (finiteModelRep_local σ) (finiteModelRep_local τ)).comp
        ((prodShrinkMulEquiv_local (G := G) (H := H)).symm.toMonoidHom))
      (finiteModelRep_local (externalTensorRep_local σ τ)) :=
  Representation.Equiv.mk (finiteModelTensorEquiv_local (V := V) (W := W)) (fun g => by
    -- Identify the two coordinates extracted from the shrunk product with the original pair.
    have hfst :
        Shrink.mulEquiv ((prodShrinkMulEquiv_local (G := G) (H := H)).symm g).1 =
          (Shrink.mulEquiv g).1 :=
      congrArg Prod.fst <|
        (MulEquiv.prodCongr (Shrink.mulEquiv : Shrink.{0} G ≃* G)
          (Shrink.mulEquiv : Shrink.{0} H ≃* H)).apply_symm_apply (Shrink.mulEquiv g)
    have hsnd :
        Shrink.mulEquiv ((prodShrinkMulEquiv_local (G := G) (H := H)).symm g).2 =
          (Shrink.mulEquiv g).2 :=
      congrArg Prod.snd <|
        (MulEquiv.prodCongr (Shrink.mulEquiv : Shrink.{0} G ≃* G)
          (Shrink.mulEquiv : Shrink.{0} H ≃* H)).apply_symm_apply (Shrink.mulEquiv g)
    ext x y
    simp [finiteModelTensorEquiv_local, finiteModelRep_local, externalTensorRep_local,
      LinearMap.comp_apply, TensorProduct.map_tmul, hfst, hsnd])

/-- Helper for Corollary 8-8.1-3: the small finite model of an irreducible representation remains
irreducible. -/
lemma finiteModelRep_isIrreducible_local [FiniteDimensional ℂ V] [Module.Finite ℂ V]
    (σ : Representation ℂ G V) [σ.IsIrreducible] :
    Representation.IsIrreducible (finiteModelRep_local σ) := by
  letI :
      Representation.IsIrreducible
        (σ.comp (Shrink.mulEquiv : Shrink.{0} G ≃* G).toMonoidHom) :=
    isIrreducible_comp_of_mulEquiv_local (e := (Shrink.mulEquiv : Shrink.{0} G ≃* G)) σ
  -- First shrink the group, then transport the action to the finite-model carrier.
  exact isIrreducible_of_nonempty_equiv_local ⟨(finiteModelRepEquivComp_local σ).symm⟩

/-- Helper for Corollary 8-8.1-3: the character of the local external tensor product is the
pointwise product of the two factor characters. -/
lemma external_tensor_character_apply_local
    {G₁ : Type*} [Group G₁] [Finite G₁]
    {G₂ : Type*} [Group G₂] [Finite G₂]
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂]
    (σ : Representation ℂ G₁ V₁) (τ : Representation ℂ G₂ V₂) (g : G₁ × G₂) :
    (externalTensorRep_local σ τ).character g = σ.character g.1 * τ.character g.2 := by
  -- Expand the tensor-product character owner and then read off the two coordinate projections.
  simpa [externalTensorRep_local, Representation.character] using
    congrFun
      (Representation.char_tensor
        (ρ := σ.comp (MonoidHom.fst G₁ G₂))
        (σ := τ.comp (MonoidHom.snd G₁ G₂)))
      g

/-- Helper for Corollary 8-8.1-3: the normalized pairing `⟪φ, ψ⟫` is the explicit
`Nat.card`-normalized sum over the group. -/
lemma groupFunctionPairingOverField_eq_nat_card_inv_sum_local
    {H : Type*} [Group H] [Finite H] (φ ψ : H → ℂ) :
    ⟪φ, ψ⟫ = (Nat.card H : ℂ)⁻¹ * ∑ h : H, φ h⁻¹ * ψ h := by
  -- Unfold the owner definition in the same `Nat.card` language as the explicit product sum.
  simp [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card]

/-- Helper for Corollary 8-8.1-3: the inverse cardinal factor of a product group splits as the
product of the inverse cardinal factors of the two coordinates. -/
lemma prod_card_inv_eq_mul_card_inv_local
    {G₁ : Type*} [Group G₁] [Finite G₁]
    {G₂ : Type*} [Group G₂] [Finite G₂] :
    ((Nat.card (G₁ × G₂) : ℂ)⁻¹ : ℂ) =
      (Nat.card G₁ : ℂ)⁻¹ * (Nat.card G₂ : ℂ)⁻¹ := by
  -- Rewrite the product-group cardinality and then normalize the scalar factor in `ℂ`.
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_prod, Nat.cast_mul]
  ring

/-- Helper for Corollary 8-8.1-3: the explicit self-pairing sum over a product group factors into
the product of the two coordinate sums. -/
lemma external_tensor_self_pairing_sum_eq_mul_local
    {G₁ : Type*} [Group G₁] [Finite G₁]
    {G₂ : Type*} [Group G₂] [Finite G₂]
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂]
    (σ : Representation ℂ G₁ V₁) (τ : Representation ℂ G₂ V₂) :
    ∑ g : G₁ × G₂, (externalTensorRep_local σ τ).character g⁻¹ *
        (externalTensorRep_local σ τ).character g
      =
        (∑ g₁ : G₁, σ.character g₁⁻¹ * σ.character g₁) *
          (∑ g₂ : G₂, τ.character g₂⁻¹ * τ.character g₂) := by
  -- Rewrite the product-group sum as an iterated sum and separate the two coordinates.
  rw [Fintype.sum_prod_type]
  calc
    ∑ g₁ : G₁, ∑ g₂ : G₂,
        (externalTensorRep_local σ τ).character (g₁, g₂)⁻¹ *
          (externalTensorRep_local σ τ).character (g₁, g₂)
      =
        ∑ g₁ : G₁, ∑ g₂ : G₂,
          (σ.character g₁⁻¹ * σ.character g₁) *
            (τ.character g₂⁻¹ * τ.character g₂) := by
          refine Finset.sum_congr rfl fun g₁ _ ↦ ?_
          refine Finset.sum_congr rfl fun g₂ _ ↦ ?_
          have hInv :
              (externalTensorRep_local σ τ).character (g₁, g₂)⁻¹ =
                σ.character g₁⁻¹ * τ.character g₂⁻¹ := by
            simpa [Prod.fst_inv, Prod.snd_inv] using
              external_tensor_character_apply_local (σ := σ) (τ := τ) ((g₁, g₂)⁻¹)
          have hVal :
              (externalTensorRep_local σ τ).character (g₁, g₂) =
                σ.character g₁ * τ.character g₂ := by
            simpa using external_tensor_character_apply_local (σ := σ) (τ := τ) (g₁, g₂)
          rw [hInv, hVal]
          ring
    _ =
        ∑ g₁ : G₁,
          (σ.character g₁⁻¹ * σ.character g₁) *
            ∑ g₂ : G₂, τ.character g₂⁻¹ * τ.character g₂ := by
          refine Finset.sum_congr rfl fun g₁ _ ↦ ?_
          rw [Finset.mul_sum]
    _ =
        (∑ g₁ : G₁, σ.character g₁⁻¹ * σ.character g₁) *
          (∑ g₂ : G₂, τ.character g₂⁻¹ * τ.character g₂) := by
          rw [Finset.sum_mul]

/-- Helper for Corollary 8-8.1-3: the self-pairing of an external tensor product factors as the
product of the self-pairings of the two factors. -/
lemma external_tensor_self_pairing_eq_mul_local
    {G₁ : Type*} [Group G₁] [Finite G₁]
    {G₂ : Type*} [Group G₂] [Finite G₂]
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    (σ : Representation ℂ G₁ V₁) (τ : Representation ℂ G₂ V₂)
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] :
    ⟪(externalTensorRep_local σ τ).character, (externalTensorRep_local σ τ).character⟫ =
      ⟪σ.character, σ.character⟫ * ⟪τ.character, τ.character⟫ := by
  -- Route correction: work directly with the defining sum for `⟪_, _⟫` so the product-group
  -- indexing stays explicit and the sum factorization is a plain `Fintype.sum_prod_type` step.
  rw [groupFunctionPairingOverField_eq_nat_card_inv_sum_local]
  rw [groupFunctionPairingOverField_eq_nat_card_inv_sum_local]
  rw [groupFunctionPairingOverField_eq_nat_card_inv_sum_local]
  -- Replace the product-group `Finset.univ` owner by the canonical product owner used in the
  -- explicit sum factorization lemma.
  have huniv_prod :
      (@Finset.univ (G₁ × G₂) (finiteGroupFintypeCorollary8813 (G := G₁ × G₂))) =
        @Finset.univ (G₁ × G₂) (instFintypeProd G₁ G₂) := by
    ext g
    simp
  have hsum :
      ((@Finset.univ (G₁ × G₂) (finiteGroupFintypeCorollary8813 (G := G₁ × G₂))).sum
        fun g ↦ (externalTensorRep_local σ τ).character g⁻¹ *
          (externalTensorRep_local σ τ).character g)
        =
          (∑ g₁ : G₁, σ.character g₁⁻¹ * σ.character g₁) *
            (∑ g₂ : G₂, τ.character g₂⁻¹ * τ.character g₂) := by
    simpa [huniv_prod] using external_tensor_self_pairing_sum_eq_mul_local (σ := σ) (τ := τ)
  have hscaled :
      (Nat.card (G₁ × G₂) : ℂ)⁻¹ *
          ((@Finset.univ (G₁ × G₂) (finiteGroupFintypeCorollary8813 (G := G₁ × G₂))).sum
            fun h ↦ (externalTensorRep_local σ τ).character h⁻¹ *
              (externalTensorRep_local σ τ).character h)
        =
          (Nat.card (G₁ × G₂) : ℂ)⁻¹ *
            ((∑ g₁ : G₁, σ.character g₁⁻¹ * σ.character g₁) *
              (∑ g₂ : G₂, τ.character g₂⁻¹ * τ.character g₂)) := by
    exact congrArg (fun z : ℂ ↦ (Nat.card (G₁ × G₂) : ℂ)⁻¹ * z) hsum
  exact hscaled.trans <| by
    -- Split the product cardinality scalar so the result becomes exactly the product
    -- of the two factor pairings.
    rw [prod_card_inv_eq_mul_card_inv_local]
    ring

/-- Helper for Corollary 8-8.1-3: after moving both factors to the same finite-model owner, the
external tensor product is irreducible. -/
lemma finiteModelExternalTensor_isIrreducible_local
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W] [Module.Finite ℂ (TensorProduct ℂ V W)]
    (σ : Representation ℂ G V) (τ : Representation ℂ H W)
    [σ.IsIrreducible] [τ.IsIrreducible] :
    Representation.IsIrreducible
      ((externalTensorRep_local (finiteModelRep_local σ) (finiteModelRep_local τ)).comp
        ((prodShrinkMulEquiv_local (G := G) (H := H)).symm.toMonoidHom)) := by
  have hσirr : Representation.IsIrreducible (finiteModelRep_local σ) :=
    finiteModelRep_isIrreducible_local (σ := σ)
  have hτirr : Representation.IsIrreducible (finiteModelRep_local τ) :=
    finiteModelRep_isIrreducible_local (σ := τ)
  letI : Representation.IsIrreducible (finiteModelRep_local σ) := hσirr
  letI : Representation.IsIrreducible (finiteModelRep_local τ) := hτirr
  have hpair :
      ⟪(externalTensorRep_local (finiteModelRep_local σ) (finiteModelRep_local τ)).character,
        (externalTensorRep_local (finiteModelRep_local σ) (finiteModelRep_local τ)).character⟫
        = (1 : ℂ) := by
    -- On the finite models, the Chapter 2 character criterion applies directly.
    rw [external_tensor_self_pairing_eq_mul_local]
    rw [self_pairing_eq_one_of_isIrreducible_via_fdrep (ρ := finiteModelRep_local σ)]
    rw [self_pairing_eq_one_of_isIrreducible_via_fdrep (ρ := finiteModelRep_local τ)]
    norm_num
  letI :
      Representation.IsIrreducible
        (externalTensorRep_local (finiteModelRep_local σ) (finiteModelRep_local τ)) :=
    (self_character_pairing_eq_one_iff_isIrreducible
      (ρ := externalTensorRep_local (finiteModelRep_local σ) (finiteModelRep_local τ))).mp hpair
  -- Precomposing with the product-shrink equivalence only changes the group coordinates.
  exact isIrreducible_comp_of_mulEquiv_local
    (e := (prodShrinkMulEquiv_local (G := G) (H := H)).symm)
    (externalTensorRep_local (finiteModelRep_local σ) (finiteModelRep_local τ))

/-- Helper for Corollary 8-8.1-3: the external tensor product of irreducible representations of
finite groups is irreducible. -/
lemma isIrreducible_external_tensor_local
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G V) (τ : Representation ℂ H W)
    [σ.IsIrreducible] [τ.IsIrreducible] :
    Representation.IsIrreducible (externalTensorRep_local σ τ) := by
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite σ
  letI : Module.Finite ℂ V := inferInstance
  letI : Module.Finite ℂ W := inferInstance
  letI : Module.Finite ℂ (TensorProduct ℂ V W) := inferInstance
  -- Route correction: move to same-universe finite models, prove irreducibility there by the
  -- character pairing criterion, and then transport back to the original external tensor product.
  letI :
      Representation.IsIrreducible
        ((externalTensorRep_local (finiteModelRep_local σ) (finiteModelRep_local τ)).comp
          ((prodShrinkMulEquiv_local (G := G) (H := H)).symm.toMonoidHom)) :=
    finiteModelExternalTensor_isIrreducible_local (σ := σ) (τ := τ)
  letI : Representation.IsIrreducible (finiteModelRep_local (externalTensorRep_local σ τ)) :=
    isIrreducible_of_nonempty_equiv_local
      ⟨finiteModelExternalTensorEquiv_local (σ := σ) (τ := τ)⟩
  letI :
      Representation.IsIrreducible
        ((externalTensorRep_local σ τ).comp
          (Shrink.mulEquiv : Shrink.{0} (G × H) ≃* (G × H)).toMonoidHom) :=
    isIrreducible_of_nonempty_equiv_local
      ⟨finiteModelRepEquivComp_local (ρ := externalTensorRep_local σ τ)⟩
  have hUnshrink :
      Representation.IsIrreducible
        (((externalTensorRep_local σ τ).comp
            (Shrink.mulEquiv : Shrink.{0} (G × H) ≃* (G × H)).toMonoidHom).comp
          ((Shrink.mulEquiv : Shrink.{0} (G × H) ≃* (G × H)).symm.toMonoidHom)) :=
    isIrreducible_comp_of_mulEquiv_local
      (e := (Shrink.mulEquiv : Shrink.{0} (G × H) ≃* (G × H)).symm)
      ((externalTensorRep_local σ τ).comp
        (Shrink.mulEquiv : Shrink.{0} (G × H) ≃* (G × H)).toMonoidHom)
  -- Unshrink the product group to recover the original external tensor representation.
  convert hUnshrink using 1
  ext g x y
  simp

/-- Helper for Corollary 8-8.1-3: a `1`-tuple of group elements is canonically the same as a
single group element. -/
def finOneMulEquiv_local : (Fin 1 → G) ≃* G where
  toFun := fun f ↦ f 0
  invFun := fun g _ ↦ g
  left_inv := by
    intro f
    funext i
    fin_cases i
    rfl
  right_inv := by
    intro g
    rfl
  map_mul' := by
    intro f h
    rfl

/-- Helper for Corollary 8-8.1-3: splitting a tuple of length `n + m` into its first `n`
coordinates and its last `m` coordinates is a group equivalence. -/
def finAppendMulEquiv_local (n m : ℕ) : (Fin (n + m) → G) ≃* (Fin n → G) × (Fin m → G) where
  toEquiv := (Fin.appendEquiv n m).symm
  map_mul' := by
    intro f h
    ext i <;> rfl

/-- Helper for Corollary 8-8.1-3: the `n`-fold tensor-power representation acts coordinatewise on
the `n`-fold tensor power. -/
def tensorPowerRep_local (ρ : Representation ℂ G V) (n : ℕ) :
    Representation ℂ (Fin n → G) (TensorPower ℂ n V) where
  toFun g := PiTensorProduct.map (fun i ↦ ρ (g i))
  map_one' := by
    -- Coordinatewise identity maps induce the identity on the full tensor product.
    simpa using (PiTensorProduct.map_one (R := ℂ) (s := fun _ : Fin n ↦ V))
  map_mul' g h := by
    -- Coordinatewise multiplication of endomorphisms transports through `PiTensorProduct.map`.
    simpa using
      (PiTensorProduct.map_mul (R := ℂ) (s := fun _ : Fin n ↦ V)
        (f₁ := fun i ↦ ρ (g i)) (f₂ := fun i ↦ ρ (h i)))

/-- Helper for Corollary 8-8.1-3: the one-fold tensor power is the original representation after
identifying `Fin 1 → G` with `G`. -/
noncomputable def tensorPowerRepOneEquiv_local (ρ : Representation ℂ G V) :
    (tensorPowerRep_local ρ 1).Equiv (ρ.comp (finOneMulEquiv_local (G := G)).toMonoidHom) :=
  Representation.Equiv.mk
    (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 ↦ V) 0)
    (fun g ↦ by
      -- On pure tensors, the singleton tensor product action is the original action.
      ext f
      simp [tensorPowerRep_local, finOneMulEquiv_local,
        PiTensorProduct.subsingletonEquiv_apply_tprod])

/-- Helper for Corollary 8-8.1-3: splitting a tuple into its first `n` coordinates and final
coordinate and then appending them again recovers the original tuple. -/
lemma fin_append_castAdd_last_local {α : Type*} (n : ℕ) (f : Fin (n + 1) → α) :
    Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun _ : Fin 1 ↦ f (Fin.last n)) = f := by
  -- This is the exact `Fin.append` reconstruction used when splitting off the last tensor factor.
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := by
    simpa using (Fin.natAdd_last (n := n) (m := 0))
  calc
    Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun _ : Fin 1 ↦ f (Fin.last n))
        =
          Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i))
            (fun i : Fin 1 ↦ f (Fin.natAdd n i)) := by
              congr 1
              funext i
              fin_cases i
              simpa using congrArg f hlast.symm
    _ = f := Fin.append_castAdd_natAdd (f := f)

/-- Helper for Corollary 8-8.1-3: the inverse of `TensorPower.mulEquiv` on a pure tensor splits
off the last tensor coordinate. -/
lemma tensorPower_mulEquiv_symm_tprod_split_last_local (n : ℕ) (f : Fin (n + 1) → V) :
    (TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)).symm
      (PiTensorProduct.tprod ℂ f)
      =
        (PiTensorProduct.tprod ℂ (fun i : Fin n ↦ f (Fin.castAdd 1 i))) ⊗ₜ[ℂ]
          (PiTensorProduct.tprod ℂ (fun i : Fin 1 ↦ f (Fin.natAdd n i))) := by
  -- Apply the forward equivalence so the goal becomes the standard tensor multiplication rule.
  apply (TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)).injective
  calc
    TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)
        ((TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)).symm
          (PiTensorProduct.tprod ℂ f))
        = PiTensorProduct.tprod ℂ f := by
            rw [LinearEquiv.apply_symm_apply]
    _ =
        PiTensorProduct.tprod ℂ
          (Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun i : Fin 1 ↦ f (Fin.natAdd n i))) := by
            congr 1
            exact (Fin.append_castAdd_natAdd (f := f)).symm
    _ =
        TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)
          ((PiTensorProduct.tprod ℂ (fun i : Fin n ↦ f (Fin.castAdd 1 i))) ⊗ₜ[ℂ]
            (PiTensorProduct.tprod ℂ (fun i : Fin 1 ↦ f (Fin.natAdd n i)))) := by
              symm
              simpa [TensorPower.gMul_def] using
                (TensorPower.tprod_mul_tprod (R := ℂ)
                  (fun i : Fin n ↦ f (Fin.castAdd 1 i))
                  (fun i : Fin 1 ↦ f (Fin.natAdd n i)))

/-- Helper for Corollary 8-8.1-3: after splitting off the last tensor factor, the successor
tensor-power action matches the split external tensor action. -/
lemma tensorPowerRepSucc_apply_tprod_local (ρ : Representation ℂ G V) (n : ℕ)
    (g : Fin (n + 1) → G) (f : Fin (n + 1) → V) :
    TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)
      (((((externalTensorRep_local (tensorPowerRep_local ρ n) (tensorPowerRep_local ρ 1)).comp
          (finAppendMulEquiv_local (G := G) n 1).toMonoidHom) g)
        ((TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)).symm
          ((PiTensorProduct.tprod ℂ) f))))
      = PiTensorProduct.tprod ℂ (fun i ↦ ρ (g i) (f i)) := by
  -- Route correction: first isolate the `mulEquiv.symm` reindexing, then evaluate the split action.
  rw [tensorPower_mulEquiv_symm_tprod_split_last_local]
  let f₁ : Fin n → V := fun i ↦ f (Fin.castAdd 1 i)
  let f₂ : Fin 1 → V := fun i ↦ f (Fin.natAdd n i)
  let gf₁ : Fin n → V := fun i ↦ ρ (g (Fin.castAdd 1 i)) (f (Fin.castAdd 1 i))
  let gf₂ : Fin 1 → V := fun i ↦ ρ (g (Fin.natAdd n i)) (f (Fin.natAdd n i))
  have hsplit :
      (((externalTensorRep_local (tensorPowerRep_local ρ n) (tensorPowerRep_local ρ 1)).comp
          (finAppendMulEquiv_local (G := G) n 1).toMonoidHom) g)
        ((PiTensorProduct.tprod ℂ f₁) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ f₂))
      =
        (PiTensorProduct.tprod ℂ gf₁) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ gf₂) := by
    simp [f₁, f₂, gf₁, gf₂, externalTensorRep_local, Representation.tprod,
      tensorPowerRep_local, finAppendMulEquiv_local]
  rw [hsplit]
  -- Recombine the two pure tensors using the tensor-power multiplication rule.
  calc
    TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)
        ((PiTensorProduct.tprod ℂ gf₁) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ gf₂))
        = PiTensorProduct.tprod ℂ (Fin.append gf₁ gf₂) := by
              simpa [TensorPower.gMul_def] using
                (TensorPower.tprod_mul_tprod (R := ℂ) gf₁ gf₂)
    _ = PiTensorProduct.tprod ℂ (fun i ↦ ρ (g i) (f i)) := by
          congr 1
          simpa [f₁, f₂, gf₁, gf₂] using
            (Fin.append_castAdd_natAdd (f := fun i : Fin (n + 1) ↦ ρ (g i) (f i)))

/-- Helper for Corollary 8-8.1-3: after splitting off the last tensor factor, the successor tensor
power is equivalent to the external tensor of the shorter power and the one-fold power. -/
noncomputable def tensorPowerRepSuccEquiv_local (ρ : Representation ℂ G V) (n : ℕ) :
    (tensorPowerRep_local ρ (n + 1)).Equiv
      ((externalTensorRep_local (tensorPowerRep_local ρ n) (tensorPowerRep_local ρ 1)).comp
        (finAppendMulEquiv_local (G := G) n 1).toMonoidHom) :=
  Representation.Equiv.mk
    (TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)).symm
    (fun g ↦ by
      -- The two actions agree on pure tensors after the standard split-recombine rewrite.
      ext f
      apply (TensorPower.mulEquiv (R := ℂ) (M := V) (n := n) (m := 1)).injective
      simpa [eq_comm, tensorPowerRep_local, PiTensorProduct.map_tprod] using
        tensorPowerRepSucc_apply_tprod_local (ρ := ρ) (n := n) g f)

/-- Helper for Corollary 8-8.1-3: every positive tensor power of an irreducible representation is
irreducible. -/
lemma tensor_power_rep_is_irreducible_local
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (n : ℕ) :
    Representation.IsIrreducible (tensorPowerRep_local ρ (n + 1)) := by
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : FiniteDimensional ℂ (TensorPower ℂ 1 V) :=
    FiniteDimensional.of_injective
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 ↦ V) 0).toLinearMap
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 ↦ V) 0).injective
  have hOne : Representation.IsIrreducible (tensorPowerRep_local ρ 1) := by
    letI : Representation.IsIrreducible
        (ρ.comp (finOneMulEquiv_local (G := G)).toMonoidHom) :=
      isIrreducible_comp_of_mulEquiv_local (G := Fin 1 → G)
        (e := finOneMulEquiv_local (G := G)) ρ
    exact isIrreducible_of_nonempty_equiv_local
      ⟨(tensorPowerRepOneEquiv_local (ρ := ρ)).symm⟩
  induction n with
  | zero =>
      exact hOne
  | succ n ih =>
      letI : Representation.IsIrreducible (tensorPowerRep_local ρ (n + 1)) := ih
      letI : Representation.IsIrreducible (tensorPowerRep_local ρ 1) := hOne
      letI : Representation.IsIrreducible
          (externalTensorRep_local (tensorPowerRep_local ρ (n + 1)) (tensorPowerRep_local ρ 1)) :=
        isIrreducible_external_tensor_local
          (σ := tensorPowerRep_local ρ (n + 1)) (τ := tensorPowerRep_local ρ 1)
      letI : Representation.IsIrreducible
          ((externalTensorRep_local (tensorPowerRep_local ρ (n + 1)) (tensorPowerRep_local ρ 1)).comp
            (finAppendMulEquiv_local (G := G) (n + 1) 1).toMonoidHom) :=
        isIrreducible_comp_of_mulEquiv_local (G := Fin (n + 2) → G)
          (e := finAppendMulEquiv_local (G := G) (n + 1) 1)
          (externalTensorRep_local (tensorPowerRep_local ρ (n + 1)) (tensorPowerRep_local ρ 1))
      -- The successor tensor power is equivalent to the split external tensor.
      exact isIrreducible_of_nonempty_equiv_local
        ⟨(tensorPowerRepSuccEquiv_local (ρ := ρ) (n := n + 1)).symm⟩

/-- Helper for Corollary 8-8.1-3: the degree of the positive tensor power is the corresponding
power of the original degree. -/
lemma tensor_power_finrank_local [FiniteDimensional ℂ V] (n : ℕ) :
    Module.finrank ℂ (TensorPower ℂ (n + 1) V) = Module.finrank ℂ V ^ (n + 1) := by
  induction n with
  | zero =>
      -- A one-fold tensor product is the original space.
      rw [pow_one]
      exact (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 ↦ V) 0).finrank_eq
  | succ n ih =>
      -- Split off the last factor and use multiplicativity of finite dimension.
      calc
        Module.finrank ℂ (TensorPower ℂ ((n + 1) + 1) V)
            = Module.finrank ℂ (TensorProduct ℂ (TensorPower ℂ (n + 1) V) (TensorPower ℂ 1 V)) := by
                simpa [Nat.add_comm] using
                  (TensorPower.mulEquiv (R := ℂ) (M := V) (n := n + 1) (m := 1)).symm.finrank_eq
        _ = Module.finrank ℂ (TensorPower ℂ (n + 1) V) * Module.finrank ℂ (TensorPower ℂ 1 V) := by
              simpa using
                (Module.finrank_tensorProduct (R := ℂ) (S := ℂ)
                  (M := TensorPower ℂ (n + 1) V) (M' := TensorPower ℂ 1 V))
        _ = Module.finrank ℂ V ^ (n + 1) * Module.finrank ℂ V := by
              rw [ih]
              rw [(PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 ↦ V) 0).finrank_eq]
        _ = Module.finrank ℂ V ^ ((n + 1) + 1) := by
              simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Corollary 8-8.1-3: the center subgroup is commutative in its own right, so
coordinatewise products of central tuples are available. -/
noncomputable instance centerCommGroup_local : CommGroup (Subgroup.center G) :=
  Group.commGroupOfCenterEqTop (Subgroup.center_eq_top (G := Subgroup.center G))

/-- Helper for Corollary 8-8.1-3: forgetting the central subtype on each coordinate embeds
central tuples into the full tuple group. -/
def centerTupleEmbedding_local (n : ℕ) :
    (Fin (n + 1) → Subgroup.center G) →* (Fin (n + 1) → G) where
  toFun z i := z i
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- Helper for Corollary 8-8.1-3: multiplying the entries of a central tuple defines a homomorphism
back to the center. -/
def centerTupleProd_local (n : ℕ) : (Fin (n + 1) → Subgroup.center G) →* Subgroup.center G where
  toFun z := ∏ i, z i
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simpa using
      (Finset.prod_mul_distrib : (∏ i, x i * y i) = (∏ i, x i) * ∏ i, y i)

/-- Helper for Corollary 8-8.1-3: Serre's product-one central subgroup inside the tuple group is
the image of the kernel of the coordinatewise product map. -/
def productOneCenterSubgroup_local (n : ℕ) : Subgroup (Fin (n + 1) → G) :=
  ((centerTupleProd_local (G := G) n).ker).map (centerTupleEmbedding_local (G := G) n)

/-- Helper for Corollary 8-8.1-3: forgetting the central subtype coordinatewise is injective. -/
lemma centerTupleEmbedding_injective_local (n : ℕ) :
    Function.Injective (centerTupleEmbedding_local (G := G) n) := by
  intro x y h
  ext i
  exact congrFun h i

/-- Helper for Corollary 8-8.1-3: the image of the coordinate-forgetful map is exactly the tuple
subgroup whose coordinates all lie in the center. -/
lemma centerTupleEmbedding_range_local (n : ℕ) :
    (centerTupleEmbedding_local (G := G) n).range =
      Subgroup.pi Set.univ (fun _ : Fin (n + 1) ↦ Subgroup.center G) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    intro i _
    exact (x i).2
  · intro hz
    refine ⟨fun i ↦ ⟨z i, hz i (by simp)⟩, ?_⟩
    rfl

/-- Helper for Corollary 8-8.1-3: the coordinatewise product map on central tuples is surjective. -/
lemma centerTupleProd_surjective_local (n : ℕ) :
    Function.Surjective (centerTupleProd_local (G := G) n) := by
  intro z
  refine ⟨fun i ↦ if i = Fin.last n then z else 1, ?_⟩
  change ∏ i : Fin (n + 1), (if i = Fin.last n then z else 1) = z
  rw [Fin.prod_univ_castSucc]
  simp

/-- Helper for Corollary 8-8.1-3: the product-one central subgroup has the index in Serre's
quotient-order computation. -/
lemma product_one_center_subgroup_index_local (n : ℕ) :
    (productOneCenterSubgroup_local (G := G) n).index =
      Nat.card (Subgroup.center G) * (Subgroup.center G).index ^ (n + 1) := by
  have hker : (centerTupleProd_local (G := G) n).ker.index = Nat.card (Subgroup.center G) := by
    rw [Subgroup.index_ker]
    have hrange : (centerTupleProd_local (G := G) n).range = ⊤ := by
      ext z
      constructor
      · intro _
        simp
      · intro _
        rcases centerTupleProd_surjective_local (G := G) n z with ⟨x, rfl⟩
        exact ⟨x, rfl⟩
    simpa [hrange]
  have hrange :
      (centerTupleEmbedding_local (G := G) n).range.index =
        (Subgroup.center G).index ^ (n + 1) := by
    rw [centerTupleEmbedding_range_local, Subgroup.index_pi]
    simp
  calc
    (productOneCenterSubgroup_local (G := G) n).index
        = (centerTupleProd_local (G := G) n).ker.index *
            (centerTupleEmbedding_local (G := G) n).range.index := by
              simpa [productOneCenterSubgroup_local] using
                (Subgroup.index_map_of_injective (H := (centerTupleProd_local (G := G) n).ker)
                  (f := centerTupleEmbedding_local (G := G) n)
                  (hf := centerTupleEmbedding_injective_local (G := G) n))
    _ = Nat.card (Subgroup.center G) * (Subgroup.center G).index ^ (n + 1) := by
          rw [hker, hrange]

/-- Helper for Corollary 8-8.1-3: a central tuple acts on the tensor power by the product of the
corresponding scalar character values. -/
lemma tensorPowerRep_center_tuple_action_local (ρ : Representation ℂ G V)
    (μ : Subgroup.center G →* ℂ)
    (hμ : ∀ s : Subgroup.center G, ρ (s : G) = μ s • (1 : Module.End ℂ V))
    (n : ℕ) (z : Fin (n + 1) → Subgroup.center G) :
    tensorPowerRep_local ρ (n + 1) (centerTupleEmbedding_local (G := G) n z) =
      (∏ i, μ (z i)) • (1 : Module.End ℂ (TensorPower ℂ (n + 1) V)) := by
  -- On pure tensors, each central coordinate contributes its scalar and multilinearity collects them.
  ext f
  have haction :
      PiTensorProduct.tprod ℂ (fun i : Fin (n + 1) ↦ μ (z i) • f i) =
        (∏ i, μ (z i)) • PiTensorProduct.tprod ℂ f := by
    exact
      (PiTensorProduct.tprod ℂ :
        MultilinearMap ℂ (fun _ : Fin (n + 1) ↦ V) (TensorPower ℂ (n + 1) V)).map_smul_univ
          (fun i ↦ μ (z i)) f
  calc
    tensorPowerRep_local ρ (n + 1) (centerTupleEmbedding_local (G := G) n z)
        (PiTensorProduct.tprod ℂ f)
        = PiTensorProduct.tprod ℂ (fun i ↦ ρ ((z i : Subgroup.center G) : G) (f i)) := by
            simp [tensorPowerRep_local, centerTupleEmbedding_local]
    _ = PiTensorProduct.tprod ℂ (fun i ↦ μ (z i) • f i) := by
          congr 1
          funext i
          simpa [hμ (z i)]
    _ = (∏ i, μ (z i)) • PiTensorProduct.tprod ℂ f := haction

/-- Helper for Corollary 8-8.1-3: the product-one central subgroup acts trivially on the positive
tensor-power representation. -/
lemma tensor_power_rep_product_one_center_is_trivial_local (ρ : Representation ℂ G V)
    (μ : Subgroup.center G →* ℂ)
    (hμ : ∀ s : Subgroup.center G, ρ (s : G) = μ s • (1 : Module.End ℂ V))
    (n : ℕ) :
    Representation.IsTrivial
      ((tensorPowerRep_local ρ (n + 1)).comp (productOneCenterSubgroup_local (G := G) n).subtype) := by
  refine ⟨?_⟩
  intro g
  rcases g.2 with ⟨z, hz, hz'⟩
  have hg : (g : Fin (n + 1) → G) = centerTupleEmbedding_local (G := G) n z := hz'.symm
  have hprod : ∏ i, μ (z i) = 1 := by
    simpa [centerTupleProd_local] using congrArg μ hz
  -- Route correction: first convert the action into the scalar product from the previous helper.
  calc
    ((tensorPowerRep_local ρ (n + 1)).comp (productOneCenterSubgroup_local (G := G) n).subtype) g
        = tensorPowerRep_local ρ (n + 1) (centerTupleEmbedding_local (G := G) n z) := by
            simpa [hg]
    _ = (∏ i, μ (z i)) • (1 : Module.End ℂ (TensorPower ℂ (n + 1) V)) :=
          tensorPowerRep_center_tuple_action_local (ρ := ρ) (μ := μ) hμ n z
    _ = LinearMap.id := by
          rw [hprod, one_smul]
          rfl

/-- Helper for Corollary 8-8.1-3: the tensor-power quotient construction yields the divisibility
family needed to extract the center-index divisibility. -/
lemma tensor_power_quotient_finrank_pow_dvd_center_card_mul_index_pow_local
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (m : ℕ) :
    Module.finrank ℂ V ^ (m + 1) ∣
      Nat.card (Subgroup.center G) * (Subgroup.center G).index ^ (m + 1) := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  obtain ⟨μ, hμ⟩ := center_scalar_action_hom_local (ρ := ρ)
  let H := productOneCenterSubgroup_local (G := G) m
  let σ := tensorPowerRep_local ρ (m + 1)
  letI : Representation.IsIrreducible σ := tensor_power_rep_is_irreducible_local (ρ := ρ) m
  letI : Representation.IsTrivial (σ.comp H.subtype) :=
    tensor_power_rep_product_one_center_is_trivial_local (ρ := ρ) (μ := μ) hμ m
  have hHcenter : H ≤ Subgroup.center (Fin (m + 1) → G) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    ext i
    rcases hg with ⟨z, hz, rfl⟩
    exact Subgroup.mem_center_iff.mp (z i).2 (h i)
  letI : H.Normal := ⟨fun a ha b ↦ by
    have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp (hHcenter ha) b
    simpa [Subgroup.mem_carrier, mul_assoc, hcomm] using ha⟩
  let τ := σ.ofQuotient H
  letI : Representation.IsIrreducible τ :=
    isIrreducible_of_ofQuotient_of_isTrivial_local σ H
  have hdiv : Module.finrank ℂ (TensorPower ℂ (m + 1) V) ∣ H.index := by
    -- The descended quotient representation is irreducible, so the order-divisibility owner applies.
    simpa [H, τ, Subgroup.index_eq_card] using finrank_dvd_card_local τ
  -- Rewrite the tensor-power degree and quotient order into Serre's final arithmetic form.
  simpa [H, tensor_power_finrank_local, product_one_center_subgroup_index_local] using hdiv

/-- Helper for Corollary 8-8.1-3: an irreducible representation has degree dividing the index of
the center. -/
lemma finrank_dvd_center_index_local
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Module.finrank ℂ V ∣ (Subgroup.center G).index := by
  -- The tensor-power quotient divisibility family is already in the exact shape needed by the
  -- arithmetic extractor proved earlier in the file.
  have hc : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
  exact dvd_of_forall_succ_pow_dvd_center_card_mul_pow_local hc
    (tensor_power_quotient_finrank_pow_dvd_center_card_mul_index_pow_local (ρ := ρ))

/-- Helper for Corollary 8-8.1-3: if the restriction to the abelian normal subgroup `A` is
isotypic, then the image of `A` in the quotient by `ρ.ker` lies in the center. -/
lemma quotient_image_le_center_of_restriction_isotypic
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ρ : Representation ℂ G V)
    (hIsotypic :
      let ρA : Representation ℂ A V := ρ.comp A.subtype
      letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra ℂ A) V) :
    A.map (QuotientGroup.mk' ρ.ker) ≤ Subgroup.center (G ⧸ ρ.ker) := by
  -- Remark `8-8.1-2` turns isotypy into scalar action by a single character of `A`.
  obtain ⟨χ, hχ⟩ :=
    (restriction_isotypic_iff_exists_character_of_commutative_subgroup
      (ρ := ρ) (A := A)).mp hIsotypic
  intro q hq
  rcases Subgroup.mem_map.mp hq with ⟨a, ha, rfl⟩
  -- A scalar action on `a` implies that its quotient image is central.
  exact quotient_mk_mem_center_of_exists_smul_id_local ρ a ⟨χ ⟨a, ha⟩, hχ ⟨a, ha⟩⟩

/-- Helper for Corollary 8-8.1-3: prove the divisibility statement by induction on the order of
the ambient finite group. -/
theorem finrank_dvd_index_of_normal_commutative_subgroup_aux
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] :
    Module.finrank ℂ V ∣ A.index := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  -- Split by Proposition `8-8.1-1` into the induced branch and the isotypic restriction branch.
  rcases
      exists_proper_overgroup_irreducible_induced_or_restriction_isotypic
        ρ A with
    ⟨H, hAH, hHtop, W, hWirr, hInduced⟩ | hIsotypic
  · letI : W.toRepresentation.IsIrreducible := hWirr
    letI : FiniteDimensional ℂ W.toSubmodule :=
      IsIrreducible.finiteDimensional_of_finite W.toRepresentation
    -- Recurse on the proper overgroup `H`, then lift divisibility through the induced-dimension
    -- formula from the previous helper.
    have hWdiv : Module.finrank ℂ W.toSubmodule ∣ (A.subgroupOf H).index := by
      exact
        finrank_dvd_index_of_normal_commutative_subgroup_aux
          (A := A.subgroupOf H) (ρ := W.toRepresentation)
    exact dvd_index_of_induced_from_overgroup (ρ := ρ) hAH W hInduced hWdiv
  · letI : Representation.IsTrivial (ρ.comp ρ.ker.subtype) := by
      constructor
      intro g
      ext v
      simpa using LinearMap.congr_fun g.property v
    let σ : Representation ℂ (G ⧸ ρ.ker) V := ρ.ofQuotient ρ.ker
    letI : σ.IsIrreducible := isIrreducible_of_ofQuotient_of_isTrivial_local ρ ρ.ker
    -- Route correction: descend to the faithful quotient first, place the image of `A` in the
    -- quotient center, and then apply the center-index divisibility theorem there.
    have hcenter :
        A.map (QuotientGroup.mk' ρ.ker) ≤ Subgroup.center (G ⧸ ρ.ker) :=
      quotient_image_le_center_of_restriction_isotypic (A := A) ρ hIsotypic
    have hdiv_center :
        Module.finrank ℂ V ∣ (Subgroup.center (G ⧸ ρ.ker)).index := by
      simpa [σ] using finrank_dvd_center_index_local σ
    have hcenter_dvd :
        (Subgroup.center (G ⧸ ρ.ker)).index ∣ (A.map (QuotientGroup.mk' ρ.ker)).index :=
      Subgroup.index_dvd_of_le hcenter
    have himage_dvd :
        (A.map (QuotientGroup.mk' ρ.ker)).index ∣ A.index :=
      Subgroup.index_map_dvd (H := A) (f := QuotientGroup.mk' ρ.ker)
        (QuotientGroup.mk'_surjective ρ.ker)
    exact dvd_trans hdiv_center (dvd_trans hcenter_dvd himage_dvd)
termination_by Nat.card G
decreasing_by
  rw [← H.index_mul_card]
  exact
    lt_mul_of_one_lt_left Nat.card_pos
      (Subgroup.one_lt_index_of_ne_top hHtop.ne)

/-- Corollary 8-8.1-3: if `A` is an abelian normal subgroup of the finite group `G`, then the
degree of each irreducible complex representation `ρ` of `G` divides the index of `A` in `G`.
Finite-dimensionality is automatic in this setting and is derived internally from
`ρ.IsIrreducible`. -/
theorem finrank_dvd_index_of_normal_commutative_subgroup
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] :
    Module.finrank ℂ V ∣ A.index := by
  -- The public statement is a thin wrapper around the induction theorem above.
  exact finrank_dvd_index_of_normal_commutative_subgroup_aux (A := A) ρ

end

end

end Representation
