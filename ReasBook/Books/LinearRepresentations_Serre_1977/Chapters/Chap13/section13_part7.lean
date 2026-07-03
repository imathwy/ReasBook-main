import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_13_13_1_17 (from Chap13) -/
open Matrix
open Matrix.GeneralLinearGroup
open scoped MonoidAlgebra
open scoped Pointwise
open scoped Representation
open Representation

noncomputable section

open Polynomial

section Exercise137

variable (p : ℕ) [Fact p.Prime]

section

variable (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))))

local notation "GPrime" =>
  Multiplicative (ZMod (p ^ 2)) ⋊[φ] Multiplicative (ZMod p)

/-- Helper for Exercise 13-13.1-17: powers of `Multiplicative.ofAdd 1` record repeated addition in
`ZMod (p^2)`. -/
private theorem ofAdd_one_pow (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) ^ n =
      Multiplicative.ofAdd ((n : ℕ) : ZMod (p ^ 2)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [pow_succ, ih]

/-- Helper for Exercise 13-13.1-17: the remaining Sylow-side blocker is to transport an arbitrary
Sylow `p`-subgroup of `GL₃(𝔽_p)` to the upper-unitriangular Heisenberg model and prove that every
element has `p`-th power equal to `1`. -/
private theorem sylowGL3_pow_p_eq_one (hp2 : p ≠ 2)
    (P : Sylow p (GL (Fin 3) (ZMod p))) (x : P) :
    x ^ p = 1 := by
  let Gmat : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    (((x : P) : GL (Fin 3) (ZMod p)) : Matrix _ _ _)
  let A : Matrix (Fin 3) (Fin 3) (ZMod p) := Gmat - 1
  have hp : Nat.Prime p := Fact.out
  obtain ⟨n, hn⟩ := P.isPGroup' x
  have hA_nilpotent : IsNilpotent A := by
    -- Route correction: work directly with the `p`-power torsion of `x`; in characteristic `p`,
    -- the relation `x^(p^n) = 1` forces `x - 1` to be nilpotent.
    refine ⟨p ^ n, ?_⟩
    obtain ⟨r, hr⟩ :=
      Commute.exists_add_pow_prime_pow_eq hp ((Commute.one_right Gmat).neg_right) n
    let f : P → Matrix (Fin 3) (Fin 3) (ZMod p) :=
      fun h => (((h : P) : GL (Fin 3) (ZMod p)) : Matrix _ _ _)
    have hgpow : Gmat ^ p ^ n = 1 := by
      simpa [f, Gmat] using congrArg f hn
    have hneg : (-(1 : Matrix (Fin 3) (Fin 3) (ZMod p))) ^ p ^ n = -1 := by
      have hodd : Odd (p ^ n) := (Nat.Prime.odd_of_ne_two hp hp2).pow
      simpa using hodd.neg_one_pow (α := Matrix (Fin 3) (Fin 3) (ZMod p))
    rw [show A = Gmat + -1 by simp [A, Gmat, sub_eq_add_neg]]
    rw [hr, hgpow, hneg]
    simp
  have hA3 : A ^ 3 = 0 := by
    -- A nilpotent endomorphism on a `3`-dimensional space has characteristic polynomial `X^3`,
    -- so Cayley-Hamilton forces the third power to vanish.
    have hA_toLin_nilpotent : IsNilpotent A.toLin' :=
      (Matrix.isNilpotent_toLin'_iff A).2 hA_nilpotent
    have hchar : LinearMap.charpoly A.toLin' = X ^ 3 := by
      simpa [Module.finrank_fintype_fun_eq_card] using
        (IsNilpotent.charpoly_eq_X_pow_finrank (R := ZMod p) (M := Fin 3 → ZMod p)
          hA_toLin_nilpotent)
    have hpowLin : A.toLin' ^ 3 = 0 := by
      simpa [hchar, aeval_X_pow] using (LinearMap.aeval_self_charpoly A.toLin')
    apply Matrix.toLin'.injective
    simpa [Matrix.toLin'_pow] using hpowLin
  have hp_gt_two : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hAp : A ^ p = 0 := by
    exact pow_eq_zero_of_le (by omega) hA3
  have hgpow : Gmat ^ p = 1 := by
    -- Apply the prime-power binomial identity once more to `1 + (x - 1)`; the nilpotent part
    -- dies because `A ^ p = 0`.
    obtain ⟨r, hr⟩ := Commute.exists_add_pow_prime_pow_eq hp (Commute.one_left A) 1
    have hsum : Gmat = 1 + A := by
      simp [A, Gmat]
    rw [hsum]
    simpa [pow_one, hAp] using hr
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simpa [Gmat] using congrFun (congrFun hgpow i) j

/-- Helper for Exercise 13-13.1-17: in the semidirect product `(Z / p²Z) ⋊ (Z / pZ)`, the obvious
generator from the `Z / p²Z` factor still has nontrivial `p`-th power. -/
private theorem semidirect_inl_one_pow_p_ne_one :
    ((SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) : GPrime) ^ p) ≠
      1 := by
  have hp : Nat.Prime p := Fact.out
  have hp_lt : p < p ^ 2 := by
    nlinarith [hp.two_le]
  have hp_cast_ne_zero : ((p : ℕ) : ZMod (p ^ 2)) ≠ 0 := by
    intro hzero
    rw [ZMod.natCast_eq_zero_iff] at hzero
    exact (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt) hzero
  intro hpow
  have hinl :
      SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd ((p : ℕ) : ZMod (p ^ 2))) = 1 := by
    -- Compute the `p`-th power through the inclusion of the normal factor.
    calc
      SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd ((p : ℕ) : ZMod (p ^ 2)))
          = ((SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) :
                GPrime) ^ p) := by
              symm
              calc
                ((SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) :
                    GPrime) ^ p)
                    = SemidirectProduct.inl (φ := φ)
                        ((Multiplicative.ofAdd (1 : ZMod (p ^ 2))) ^ p) := by
                            exact
                              ((SemidirectProduct.inl (φ := φ)).map_pow
                                (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) p).symm
                _ = SemidirectProduct.inl (φ := φ)
                      (Multiplicative.ofAdd ((p : ℕ) : ZMod (p ^ 2))) := by
                            rw [ofAdd_one_pow (p := p) p]
      _ = 1 := hpow
  have hzero : ((p : ℕ) : ZMod (p ^ 2)) = 0 := by
    exact (ofAdd_eq_one).1 (SemidirectProduct.inl_injective (by simpa using hinl))
  exact hp_cast_ne_zero hzero

-- Proof sketch: a Sylow `p`-subgroup of `GL₃(𝔽_p)` is the upper-unitriangular Heisenberg group of
-- exponent `p`, whereas a nonabelian semidirect product `Z / p² Z ⋊ Z / p Z` contains an element
-- of order `p²`; compare element orders to rule out a group isomorphism.
/-- Exercise 13-13.1-17 (1): for an odd prime `p`, a Sylow `p`-subgroup of `GL₃(𝔽_p)` is not
isomorphic to a nonabelian semidirect product of `Z / p Z` with `Z / p² Z`. -/
theorem sylowGL3_not_isomorphic_to_nonabelian_zmod_semidirectProduct
    (hp2 : p ≠ 2)
    (P : Sylow p (GL (Fin 3) (ZMod p)))
    (hφ : ¬ IsMulCommutative GPrime) :
    ¬ Nonempty (P ≃* GPrime) := by
  intro hIso
  rcases hIso with ⟨e⟩
  let y : GPrime :=
    SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd (1 : ZMod (p ^ 2)))
  let x : P := e.symm y
  -- The Sylow subgroup is transported to the explicit Heisenberg model, so every element has
  -- `p`-th power equal to `1`.
  have hx : x ^ p = 1 := sylowGL3_pow_p_eq_one (p := p) hp2 P x
  -- Applying the supposed isomorphism would force the semidirect-product witness to have trivial
  -- `p`-th power, contradicting the explicit computation in the normal `Z / p²Z` factor.
  have hy : y ^ p = 1 := by
    simpa [x, y] using congrArg e hx
  exact semidirect_inl_one_pow_p_ne_one (p := p) (φ := φ) hy

end

-- Proof sketch: classify the irreducible rational representations of the Heisenberg Sylow
-- `p`-subgroup, identify the corresponding simple components by their character fields, and apply
-- Artin-Wedderburn to `ℚ[G]`.
/-- Helper for Exercise 13-13.1-17: the common rational Artin-Wedderburn target shared by the
Heisenberg and semidirect models. -/
private abbrev RationalPacketTarget :=
  ℚ × (Fin (p + 1) → CyclotomicField p ℚ) ×
    Matrix (Fin p) (Fin p) (CyclotomicField p ℚ)

/-- Helper for Exercise 13-13.1-17: the common rational Artin-Wedderburn target has total
`ℚ`-dimension `p^3`. -/
private theorem rational_target_finrank_p_cubed :
    Module.finrank ℚ (RationalPacketTarget (p := p)) =
      p ^ 3 := by
  -- The cyclotomic field `ℚ(p)` has degree `φ(p) = p - 1` for prime `p`.
  have hcyclo : Module.finrank ℚ (CyclotomicField p ℚ) = p - 1 := by
    letI : NeZero (p : ℚ) := ⟨by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
    letI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
      CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)
    simpa [Nat.totient_prime (Fact.out : Nat.Prime p)] using
      IsCyclotomicExtension.Rat.finrank p (CyclotomicField p ℚ)
  -- Add the dimensions of the trivial factor, the `p + 1` cyclotomic field factors, and the
  -- `p × p` matrix algebra over that same cyclotomic field.
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, Module.finrank_pi_fintype,
    Module.finrank_matrix]
  simp [hcyclo]
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  have hcalc : (1 + ((p + 1) * (p - 1) + p * p * (p - 1)) : ℤ) = p ^ 3 := by
    ring
  exact_mod_cast hcalc

/-- Helper for Exercise 13-13.1-17: once a rational packet map kills a complete complex family
after scalar extension, the packet map is injective over `ℚ`. -/
private theorem rational_packet_map_injective_of_complex_family
    {G : Type} [Group G] [Finite G]
    {A : Type} [Ring A] [Algebra ℚ A]
    {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of ((π i).ρ)))
    (Φ : ℚ[G] →ₐ[ℚ] A)
    (hΦ_family :
      ∀ z : ℚ[G], Φ z = 0 →
        familyEndAlgHom (π := π)
          (MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) z) = 0) :
    Function.Injective Φ := by
  intro x y hxy
  let z : ℚ[G] := x - y
  -- Pass to the difference so the packet map and the complete complex family both see a zero
  -- element.
  have hz_packet : Φ z = 0 := by
    simp [z, map_sub, hxy]
  have hfamily_zero :
      familyEndAlgHom (π := π)
          (MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) z) = 0 :=
    hΦ_family z hz_packet
  -- The complete-family injectivity theorem over `ℂ` needs the finite group order to be
  -- invertible, which is automatic in characteristic zero.
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have hinj_complex :
      Function.Injective (familyEndAlgHom (π := π)) :=
    familyEndAlgHom_injective_of_complete_family
      (π := π) hπ_pairwise hπ_complete
  have hmap_zero :
      MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) z = 0 := by
    exact hinj_complex hfamily_zero
  have hz_zero : z = 0 := by
    -- Descend the complex zero equality coefficientwise through the injective scalar map
    -- `ℚ → ℂ`.
    ext g
    have hg0 := congrArg (fun w : ℂ[G] ↦ w g) hmap_zero
    change algebraMap ℚ ℂ (z g) = 0 at hg0
    exact RingHom.injective (algebraMap ℚ ℂ) (by simpa using hg0)
  exact sub_eq_zero.mp (by simpa [z] using hz_zero)

/-- Helper for Exercise 13-13.1-17: equal `ℚ`-dimensions upgrade an injective algebra map to an
algebra equivalence. -/
private theorem algEquiv_of_injective_algHom_of_finrank_eq
    {A B : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (Φ : A →ₐ[ℚ] B)
    (hdim : Module.finrank ℚ A = Module.finrank ℚ B)
    (hΦ : Function.Injective Φ) :
    Nonempty (A ≃ₐ[ℚ] B) := by
  -- Compare source and target dimensions on the underlying linear map.
  have hsurj : Function.Surjective Φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦ
  exact ⟨AlgEquiv.ofBijective Φ ⟨hΦ, hsurj⟩⟩

/-- Helper for Exercise 13-13.1-17: an algebra equivalence identifies Jacobson radicals by
comap. This packages the membership-level transport from `JenningsObstruction` as an ideal
equality. -/
private theorem jacobson_comap_eq_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) :
    Ideal.comap (e : A →+* B) (Ring.jacobson B) = Ring.jacobson A := by
  ext x
  -- Read comap membership through the already-proved Jacobson-membership transport.
  rw [Ideal.mem_comap]
  exact (mem_jacobson_iff_of_algEquiv (p := p) e (x := x)).symm

/-- Helper for Exercise 13-13.1-17: an algebra equivalence identifies Jacobson radicals by
map. This is the ideal-level rewrite needed before passing to Jennings quotients. -/
private theorem jacobson_map_eq_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) :
    Ideal.map (e : A →+* B) (Ring.jacobson A) = Ring.jacobson B := by
  -- Compare after comapping along the surjective equivalence.
  apply (Ideal.comap_injective_of_surjective (f := (e : A →+* B)) e.surjective)
  rw [Ideal.comap_map_of_bijective (f := (e : A →+* B)) e.bijective]
  symm
  exact jacobson_comap_eq_of_algEquiv (p := p) e

/-- Helper for Exercise 13-13.1-17: an algebra equivalence transports products of two-sided
ideals exactly. This keeps the later Jennings-layer rewrites at the ideal level instead of
expanding quotient representatives. -/
private theorem ideal_map_mul_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (I J : Ideal A) :
    Ideal.map (e : A →+* B) (I * J) =
      Ideal.map (e : A →+* B) I * Ideal.map (e : A →+* B) J := by
  apply le_antisymm
  · -- Forward inclusion is immediate from the product generators in `I * J`.
    rw [Ideal.map_le_iff_le_comap, Ideal.mul_le]
    intro r hr s hs
    rw [Ideal.mem_comap]
    simpa [map_mul] using
      (Ideal.mul_mem_mul
        (Ideal.mem_map_of_mem (e : A →+* B) hr)
        (Ideal.mem_map_of_mem (e : A →+* B) hs) :
        e r * e s ∈
          Ideal.map (e : A →+* B) I * Ideal.map (e : A →+* B) J)
  · -- For the reverse inclusion, pull both factors back through surjectivity of `e`.
    rw [Ideal.mul_le]
    intro y hy z hz
    rcases
        (Ideal.mem_map_iff_of_surjective (f := (e : A →+* B)) e.surjective).1 hy with
      ⟨r, hr, rfl⟩
    rcases
        (Ideal.mem_map_iff_of_surjective (f := (e : A →+* B)) e.surjective).1 hz with
      ⟨s, hs, rfl⟩
    simpa [map_mul] using
      (Ideal.mem_map_of_mem
        (e : A →+* B)
        (Ideal.mul_mem_mul hr hs) :
        e (r * s) ∈ Ideal.map (e : A →+* B) (I * J))

/-- Helper for Exercise 13-13.1-17: an algebra equivalence transports powers of the Jacobson
radical exactly. This closes the ideal-power rewrite step in the planned Jennings obstruction. -/
private theorem jacobson_pow_map_eq_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) :
    Ideal.map (e : A →+* B) (Ring.jacobson A ^ n) = Ring.jacobson B ^ n := by
  have hmul :
      ∀ I J : Ideal A,
        Ideal.map (e : A →+* B) (I * J) =
          Ideal.map (e : A →+* B) I * Ideal.map (e : A →+* B) J :=
    ideal_map_mul_of_algEquiv (p := p) e
  have hjac :
      Ideal.map (e : A →+* B) (Ring.jacobson A) = Ring.jacobson B :=
    jacobson_map_eq_of_algEquiv (p := p) e
  induction n with
  | zero =>
      -- Both zeroth powers are the top ideal.
      change Ideal.map (e : A →+* B) (1 : Ideal A) = (1 : Ideal B)
      simpa [Ideal.one_eq_top] using (Ideal.map_top (e : A →+* B))
  | succ n ih =>
      -- Rewrite one Jacobson power by `I^(n+1) = I * I^n` and transport both factors.
      rw [(Ring.jacobson A).pow_succ, (Ring.jacobson B).pow_succ, hmul, hjac, ih]

/-- Helper for Exercise 13-13.1-17: the same algebra equivalence also identifies Jacobson
powers by comap. This is the form needed to compare quotient kernels. -/
private theorem jacobson_pow_comap_eq_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) :
    Ideal.comap (e : A →+* B) (Ring.jacobson B ^ n) = Ring.jacobson A ^ n := by
  calc
    Ideal.comap (e : A →+* B) (Ring.jacobson B ^ n)
        = Ideal.comap (e : A →+* B)
            (Ideal.map (e : A →+* B) (Ring.jacobson A ^ n)) := by
              rw [jacobson_pow_map_eq_of_algEquiv (p := p) e n]
    _ = Ring.jacobson A ^ n := by
          rw [Ideal.comap_map_of_bijective (f := (e : A →+* B)) e.bijective]

/-- Helper for Exercise 13-13.1-17: vanishing of a Jacobson-power class is preserved by an
algebra equivalence. This isolates the quotient-kernel part of the Jennings obstruction from the
still-open compatibility with the `p`-th-power map. -/
private theorem jacobson_pow_quotient_zero_iff_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) (x : A) :
    Ideal.Quotient.mk (Ring.jacobson B ^ n) (e x) = 0 ↔
      Ideal.Quotient.mk (Ring.jacobson A ^ n) x = 0 := by
  -- Convert both quotient equalities to ideal membership and then rewrite by comap.
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  rw [← jacobson_pow_comap_eq_of_algEquiv (p := p) e n, Ideal.mem_comap]
  simpa

/-- Helper for Exercise 13-13.1-17: the algebra equivalence itself respects the Jacobson-power
quotient kernels, so it induces the canonical map on the `n`-th Jennings layer. -/
private theorem jacobson_pow_le_linear_comap_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) :
    Ring.jacobson A ^ n ≤
      Submodule.comap e.toRingHom.toSemilinearMap (Ring.jacobson B ^ n) := by
  -- Read the target submodule membership as ideal membership and rewrite it by the already-closed
  -- Jacobson-power comap theorem.
  intro x hx
  have hx' : x ∈ Ideal.comap (e : A →+* B) (Ring.jacobson B ^ n) := by
    rw [jacobson_pow_comap_eq_of_algEquiv (p := p) e n]
    exact hx
  simpa [Submodule.mem_comap, Ideal.mem_comap] using hx'

/-- Helper for Exercise 13-13.1-17: an algebra equivalence induces a linear map on the quotient by
the `n`-th Jacobson power. This is the concrete `Submodule.mapQ` owner needed for the Jennings
obstruction. -/
private noncomputable def jacobson_pow_quotient_map_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) :
    A ⧸ Ring.jacobson A ^ n →ₛₗ[e.toRingHom] B ⧸ Ring.jacobson B ^ n :=
  (Ring.jacobson A ^ n).mapQ (Ring.jacobson B ^ n) e.toRingHom.toSemilinearMap
    (jacobson_pow_le_linear_comap_of_algEquiv (p := p) e n)

/-- Helper for Exercise 13-13.1-17: the induced quotient map sends the class of `x` to the class
of `e x`. This keeps the later Jennings comparison on representatives completely explicit. -/
private theorem jacobson_pow_quotient_map_of_algEquiv_mk
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) (x : A) :
    jacobson_pow_quotient_map_of_algEquiv (p := p) e n
        (Ideal.Quotient.mk (Ring.jacobson A ^ n) x) =
      Ideal.Quotient.mk (Ring.jacobson B ^ n) (e x) := by
  -- Unfold the quotient map once and evaluate it on a class representative.
  simpa [jacobson_pow_quotient_map_of_algEquiv] using
    (Submodule.mapQ_apply
      (p := Ring.jacobson A ^ n)
      (q := Ring.jacobson B ^ n)
      (f := e.toRingHom.toSemilinearMap)
      (h := jacobson_pow_le_linear_comap_of_algEquiv (p := p) e n)
      x)

/-- Helper for Exercise 13-13.1-17: zero classes are preserved by the induced quotient map on
Jacobson powers. This is the quotient-level zero/nonzero transport needed before comparing the
Jennings `p`-th-power layer. -/
private theorem jacobson_pow_quotient_map_eq_zero_iff_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) (x : A) :
    jacobson_pow_quotient_map_of_algEquiv (p := p) e n
        (Ideal.Quotient.mk (Ring.jacobson A ^ n) x) = 0 ↔
      Ideal.Quotient.mk (Ring.jacobson A ^ n) x = 0 := by
  -- Reduce to the representative formula and then read zero through the earlier quotient-kernel
  -- transport theorem.
  rw [jacobson_pow_quotient_map_of_algEquiv_mk (p := p) e n x]
  exact jacobson_pow_quotient_zero_iff_of_algEquiv (p := p) e n x

/-- Helper for Exercise 13-13.1-17: the quotient map commutes with taking the representative
`p`-th power before passing to `J^(p+1)`. This is the stabilized quotient-level frontier of the
Jennings obstruction. -/
private theorem jacobson_pth_power_quotient_map_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (x : A) :
    jacobson_pow_quotient_map_of_algEquiv (p := p) e (p + 1)
        (Ideal.Quotient.mk (Ring.jacobson A ^ (p + 1)) (x ^ p)) =
      Ideal.Quotient.mk (Ring.jacobson B ^ (p + 1)) (e x ^ p) := by
  -- The quotient map is defined on representatives, and the algebra equivalence carries `x^p`
  -- to `(e x)^p`.
  rw [jacobson_pow_quotient_map_of_algEquiv_mk (p := p) e (p + 1) (x ^ p)]
  simp [map_pow]

/-- Helper for Exercise 13-13.1-17: every Sylow `p`-subgroup of `GL₃(𝔽_p)` is isomorphic to the
canonical upper-unitriangular model. -/
private theorem sylowGL3_mulEquiv_upperUnitriangularSubgroup
    (P : Sylow p (GL (Fin 3) (ZMod p))) :
    Nonempty (P ≃* upperUnitriangularSubgroup (ZMod p) 3) := by
  -- Use the chapter-8 canonical Sylow owner and Sylow conjugacy to freeze the source group.
  rcases upperUnitriangularSubgroup_isSylow (k := ZMod p) (n := 3) (p := p) with ⟨Q, hQ⟩
  exact ⟨(P.equiv Q).trans (MulEquiv.subgroupCongr hQ)⟩

/-- Helper for Exercise 13-13.1-17: a multiplicative equivalence of groups transports to an
algebra equivalence of their group algebras over any coefficient semiring. -/
private theorem groupAlgebra_equiv_of_mulEquiv
    {k G H : Type*} [CommSemiring k] [Group G] [Group H] (e : G ≃* H) :
    Nonempty (k[G] ≃ₐ[k] k[H]) := by
  -- The monoid-algebra domain congruence is the canonical transport owner.
  exact ⟨MonoidAlgebra.domCongr k k e⟩

/-- Helper for Exercise 13-13.1-17: finite group algebras have dimension equal to the group
cardinality. -/
private theorem groupAlgebra_finrank_eq_natCard
    {k G : Type*} [Field k] [Group G] [Finite G] :
    Module.finrank k k[G] = Nat.card G := by
  let _ : Fintype G := Fintype.ofFinite G
  -- Rewrite the group algebra as a finitely supported function space on the group basis.
  rw [Nat.card_eq_fintype_card]
  change Module.finrank k (G →₀ k) = Fintype.card G
  exact Module.finrank_finsupp_self (R := k) (ι := G)

/-- Helper for Exercise 13-13.1-17: in characteristic `p`, the basis element `[g] - 1` has
`p`-th power `[g^p] - 1`. -/
private theorem monoidAlgebra_of_sub_one_pow_p
    {G : Type*} [Group G] (g : G) :
    ((MonoidAlgebra.of (ZMod p) G g : (ZMod p)[G]) - 1) ^ p =
      MonoidAlgebra.of (ZMod p) G (g ^ p) - 1 := by
  let x : (ZMod p)[G] := MonoidAlgebra.of (ZMod p) G g
  have hp : Nat.Prime p := Fact.out
  have hpow : (x + -(1 : (ZMod p)[G])) ^ p = x ^ p + (-(1 : (ZMod p)[G])) ^ p := by
    obtain ⟨r, hr⟩ := (Commute.one_right x).neg_right.exists_add_pow_prime_eq hp
    have hpzero : ((p : ℕ) : (ZMod p)[G]) = 0 := by
      have hpzero' : ((p : ℕ) : ZMod p) = 0 := by
        simpa using (CharP.cast_eq_zero (R := ZMod p) (p := p))
      calc
        ((p : ℕ) : (ZMod p)[G]) =
            MonoidAlgebra.singleOneRingHom (R := ZMod p) (M := G) ((p : ℕ) : ZMod p) := rfl
        _ = MonoidAlgebra.singleOneRingHom (R := ZMod p) (M := G) 0 := by rw [hpzero']
        _ = 0 := by
              change MonoidAlgebra.single (1 : G) (0 : ZMod p) = 0
              exact Finsupp.single_zero _
    rw [hr, hpzero]
    simp
  have hxpow : x ^ p = MonoidAlgebra.of (ZMod p) G (g ^ p) := by
    simpa [x] using ((MonoidAlgebra.of (ZMod p) G).map_pow g p).symm
  -- The characteristic-`p` Frobenius identity turns `[g] - 1` into `[g^p] - 1`.
  calc
    ((MonoidAlgebra.of (ZMod p) G g : (ZMod p)[G]) - 1) ^ p
        = (x + -(1 : (ZMod p)[G])) ^ p := by simp [x, sub_eq_add_neg]
    _ = x ^ p + (-(1 : (ZMod p)[G])) ^ p := hpow
    _ = MonoidAlgebra.of (ZMod p) G (g ^ p) - 1 := by
          rw [hxpow]
          have hnegpow : (-(1 : (ZMod p)[G])) ^ p = -(1 : (ZMod p)[G]) := by
            have hnegcoeff : ((-1 : ZMod p) ^ p) = (-1 : ZMod p) := by
              by_cases hp2 : p = 2
              · subst hp2
                simp
              · have hpodd : Odd p := Nat.Prime.odd_of_ne_two hp hp2
                simpa using hpodd.neg_one_pow (α := ZMod p)
            have hsingle : (-(1 : (ZMod p)[G])) = MonoidAlgebra.single 1 (-1 : ZMod p) := by
              ext h
              by_cases hh : h = 1
              · subst hh
                simp [MonoidAlgebra.one_def]
              · simp [MonoidAlgebra.one_def, hh]
            rw [hsingle, MonoidAlgebra.single_pow]
            simpa [hnegcoeff]
          rw [hnegpow]
          simp [sub_eq_add_neg]

/-- Helper for Exercise 13-13.1-17: the canonical upper-unitriangular model has order `p^3`. -/
private theorem upperUnitriangularSubgroup_card_p_cubed :
    Nat.card (upperUnitriangularSubgroup (ZMod p) 3) = p ^ 3 := by
  rcases upperUnitriangularSubgroup_isSylow (k := ZMod p) (n := 3) (p := p) with ⟨P, hP⟩
  rw [← hP, P.card_eq_multiplicity]
  have hcard :
      Nat.card (GL (Fin 3) (ZMod p)) = p ^ 3 * ((p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rw [Matrix.card_GL_field (n := 3) (𝔽 := ZMod p), Fin.prod_univ_three, ZMod.card]
    have hp_cube_sub_p :
        p ^ 3 - p = p * (p ^ 2 - 1) := by
      simp [pow_succ, Nat.mul_assoc, Nat.mul_sub_left_distrib]
    have hp_cube_sub_p_sq :
        p ^ 3 - p ^ 2 = p ^ 2 * (p - 1) := by
      simp [pow_succ, Nat.mul_assoc, Nat.mul_sub_left_distrib]
    -- The three `GL₃` factors are `(p^3 - 1)`, `p (p^2 - 1)`, and `p^2 (p - 1)`.
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, Nat.one_mod, pow_one,
      Nat.mod_succ]
    rw [hp_cube_sub_p, hp_cube_sub_p_sq]
    ring
  have hp : Nat.Prime p := Fact.out
  have hcoprime_p_minus_one : Nat.Coprime p (p - 1) := by
    refine hp.coprime_iff_not_dvd.2 ?_
    exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos (by decide))
  have hcoprime_p_sq_minus_one : Nat.Coprime p (p ^ 2 - 1) := by
    refine hp.coprime_iff_not_dvd.2 ?_
    intro hdiv
    have hp2 : p ∣ p ^ 2 := by
      simp [pow_two]
    have hp_dvd_one : p ∣ 1 := by
      have hsub : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub hp2 hdiv
      have hcalc : 1 + (p ^ 2 - 1) = p ^ 2 := by
        have hp2pos : 0 < p ^ 2 := by
          have hp0 : 0 < p := hp.pos
          positivity
        simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one, Nat.add_comm] using
          Nat.succ_pred_eq_of_pos hp2pos
      exact (Nat.eq_sub_of_add_eq hcalc).symm ▸ hsub
    exact hp.not_dvd_one hp_dvd_one
  have hcoprime_p_cube_minus_one : Nat.Coprime p (p ^ 3 - 1) := by
    refine hp.coprime_iff_not_dvd.2 ?_
    intro hdiv
    have hp3 : p ∣ p ^ 3 := by
      exact dvd_pow_self p (show 3 ≠ 0 by decide)
    have hp_dvd_one : p ∣ 1 := by
      have hsub : p ∣ p ^ 3 - (p ^ 3 - 1) := Nat.dvd_sub hp3 hdiv
      have hcalc : 1 + (p ^ 3 - 1) = p ^ 3 := by
        have hp3pos : 0 < p ^ 3 := by
          have hp0 : 0 < p := hp.pos
          positivity
        simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one, Nat.add_comm] using
          Nat.succ_pred_eq_of_pos hp3pos
      exact (Nat.eq_sub_of_add_eq hcalc).symm ▸ hsub
    exact hp.not_dvd_one hp_dvd_one
  have hcoprime : Nat.Coprime p ((p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)) := by
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right hcoprime_p_minus_one hcoprime_p_sq_minus_one)
      hcoprime_p_cube_minus_one
  have hm0 : ((p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)) ≠ 0 := by
    intro hmz
    have : Nat.Coprime p 0 := by
      simpa [hmz] using hcoprime
    exact hp.ne_one <| by simpa [Nat.coprime_zero_right] using this
  have hfactorization :
      (Nat.card (GL (Fin 3) (ZMod p))).factorization p = 3 := by
    rw [hcard]
    have hmul := Nat.factorization_mul (a := p ^ 3)
        (b := (p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)) (pow_ne_zero _ hp.ne_zero) hm0
    have hfactorization_m : (((p - 1) * (p ^ 2 - 1) * (p ^ 3 - 1)).factorization p) = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdiv
      exact (hp.coprime_iff_not_dvd.mp hcoprime) hdiv
    rw [hmul]
    simp [hp.factorization_pow, hfactorization_m]
  rw [hfactorization]

/-- Helper for Exercise 13-13.1-17: the upper-unitriangular group algebra has `ℚ`-dimension
`p^3`. -/
private theorem upperUnitriangularSubgroup_groupAlgebra_finrank_p_cubed :
    Module.finrank ℚ ℚ[upperUnitriangularSubgroup (ZMod p) 3] = p ^ 3 := by
  -- Combine the general group-algebra dimension formula with the explicit order of the canonical
  -- Heisenberg model.
  rw [groupAlgebra_finrank_eq_natCard (k := ℚ) (G := upperUnitriangularSubgroup (ZMod p) 3),
    upperUnitriangularSubgroup_card_p_cubed (p := p)]

/-- Helper for Exercise 13-13.1-17: the canonical Heisenberg model has exponent `p`. -/
private theorem upperUnitriangularSubgroup_pow_p_eq_one
    (hp2 : p ≠ 2) (x : upperUnitriangularSubgroup (ZMod p) 3) :
    x ^ p = 1 := by
  rcases upperUnitriangularSubgroup_isSylow (k := ZMod p) (n := 3) (p := p) with ⟨P, hP⟩
  let e : upperUnitriangularSubgroup (ZMod p) 3 ≃* P := MulEquiv.subgroupCongr hP.symm
  have hxP : (e x) ^ p = 1 := sylowGL3_pow_p_eq_one (p := p) hp2 P (e x)
  -- Transport the exponent-`p` relation back from the chosen Sylow owner.
  exact e.injective (by simpa using hxP)

/-- Helper for Exercise 13-13.1-17: on the Heisenberg model, every augmentation generator
`[g] - 1` has zero `p`-th power over `𝔽_p`. -/
private theorem upperUnitriangularSubgroup_of_sub_one_pow_p_eq_zero
    (hp2 : p ≠ 2) (g : upperUnitriangularSubgroup (ZMod p) 3) :
    ((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
        (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ^ p = 0 := by
  -- Rewrite the `p`-th power in the group algebra, then use the exponent-`p` calculation.
  rw [monoidAlgebra_of_sub_one_pow_p (p := p) (G := upperUnitriangularSubgroup (ZMod p) 3) g,
    upperUnitriangularSubgroup_pow_p_eq_one (p := p) hp2 g]
  ext h
  by_cases hh : h = 1
  · subst hh
    simp [MonoidAlgebra.of, MonoidAlgebra.one_def]
  · simp [MonoidAlgebra.of, MonoidAlgebra.one_def, hh]

/-- Helper for Exercise 13-13.1-17: the canonical Heisenberg model carries the usual augmentation
map to `𝔽_p`. -/
private def upperUnitriangularSubgroup_augmentation :
    (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3] →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3)
    (1 : upperUnitriangularSubgroup (ZMod p) 3 →* ZMod p)

/-- Helper for Exercise 13-13.1-17: the Heisenberg augmentation map is surjective. -/
private theorem upperUnitriangularSubgroup_augmentation_surjective :
    Function.Surjective (upperUnitriangularSubgroup_augmentation (p := p)) := by
  intro z
  refine ⟨algebraMap (ZMod p) ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) z, ?_⟩
  -- The augmentation sends scalar coefficients to the same scalar in `𝔽_p`.
  simp [upperUnitriangularSubgroup_augmentation]

/-- Helper for Exercise 13-13.1-17: each Heisenberg augmentation generator `[g] - 1` lies in the
kernel of the augmentation map. -/
private theorem upperUnitriangularSubgroup_of_sub_one_mem_augmentationKernel
    (g : upperUnitriangularSubgroup (ZMod p) 3) :
    ((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
        (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ∈
      RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom := by
  -- The augmentation sends both `[g]` and `1` to `1`, so their difference is killed.
  rw [RingHom.mem_ker]
  simp [upperUnitriangularSubgroup_augmentation]

/-- Helper for Exercise 13-13.1-17: the Heisenberg augmentation kernel is exactly the span of the
standard generators `[g] - 1`. -/
private theorem upperUnitriangularSubgroup_augmentationKernel_eq_span_sub_one :
    RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom =
      Ideal.span
        (Set.range fun g : upperUnitriangularSubgroup (ZMod p) 3 =>
          (MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
              (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) := by
  -- The generic augmentation-kernel owner already identifies finite-group kernels with the span of
  -- the differences `[g] - 1`.
  simpa [upperUnitriangularSubgroup_augmentation] using
    (monoidAlgebra_augmentationKernel_eq_span_sub_one
      (p := p) (G := upperUnitriangularSubgroup (ZMod p) 3))

/-- Helper for Exercise 13-13.1-17: the Heisenberg augmentation kernel is maximal because the
quotient is the field `𝔽_p`. -/
private theorem upperUnitriangularSubgroup_augmentationKernel_isMaximal :
    (RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom).IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective
    (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom
    (upperUnitriangularSubgroup_augmentation_surjective (p := p))

/-- Helper for Exercise 13-13.1-17: the ring Jacobson radical is always contained in the maximal
Heisenberg augmentation kernel. -/
private theorem upperUnitriangularSubgroup_jacobson_le_augmentationKernel :
    Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) ≤
      RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom := by
  letI :
      (RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom).IsMaximal :=
    upperUnitriangularSubgroup_augmentationKernel_isMaximal (p := p)
  -- The Jacobson radical is contained in every maximal ideal, in particular in the augmentation
  -- kernel.
  exact Ring.jacobson_le_of_isMaximal _

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's generator-level Jacobson lemma upgrades the concrete
Heisenberg augmentation kernel to a subideal of the Jacobson radical. -/
private theorem upperUnitriangularSubgroup_augmentationKernel_le_jacobson :
    RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom ≤
      Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) := by
  have hspan :
      Ideal.span
          (Set.range fun g : upperUnitriangularSubgroup (ZMod p) 3 =>
            (MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
                (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ≤
        Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    have hP :
        IsPGroup p (upperUnitriangularSubgroup (ZMod p) 3) :=
      IsPGroup.of_card (upperUnitriangularSubgroup_card_p_cubed (p := p))
    -- Each standard augmentation generator already lies in the Jacobson radical.
    simpa using
      p_group_generator_sub_one_mem_jacobson
        (p := p) (G := upperUnitriangularSubgroup (ZMod p) 3) hP g
  -- Rewrite the augmentation kernel by the span of the standard generators and apply the new
  -- generator-level Jacobson owner.
  rw [upperUnitriangularSubgroup_augmentationKernel_eq_span_sub_one (p := p)]
  exact hspan

/-- Helper for Exercise 13-13.1-17: on the canonical Heisenberg model, the Jacobson radical is
exactly the augmentation kernel. -/
private theorem upperUnitriangularSubgroup_jacobson_eq_augmentationKernel :
    Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) =
      RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom := by
  -- The easy maximal-ideal inclusion and the new generator-level inclusion meet in the middle.
  exact le_antisymm
    (upperUnitriangularSubgroup_jacobson_le_augmentationKernel (p := p))
    (upperUnitriangularSubgroup_augmentationKernel_le_jacobson (p := p))

/-- Helper for Exercise 13-13.1-17: once LinearRepresentations_Serre_1977's packet comparison map on the canonical
upper-unitriangular model is injective, finite-dimensionality upgrades it to the desired
Artin-Wedderburn equivalence. -/
private theorem upperUnitriangularSubgroup_rational_packet_data
    (hp2 : p ≠ 2) :
    ∃ Φ :
      ℚ[upperUnitriangularSubgroup (ZMod p) 3] →ₐ[ℚ]
        RationalPacketTarget (p := p),
      Function.Injective Φ := by
  -- Route correction: the remaining source-faithful work is now exactly LinearRepresentations_Serre_1977's explicit packet
  -- map on the Heisenberg model and the proof that its kernel vanishes.
  -- TODO: construct the `p + 1` linear rational packets from the abelianization together with the
  -- single degree-`p` Schrödinger packet, then prove that zero packet data kills the complete
  -- complex Heisenberg family so `rational_packet_map_injective_of_complex_family` applies.
  sorry

/-- Helper for Exercise 13-13.1-17: the source-faithful rational Artin-Wedderburn owner on the
canonical upper-unitriangular Heisenberg model. -/
private theorem upperUnitriangularSubgroup_rational_groupAlgebra_decomposition
    (hp2 : p ≠ 2) :
    Nonempty
      (ℚ[upperUnitriangularSubgroup (ZMod p) 3] ≃ₐ[ℚ]
        RationalPacketTarget (p := p)) := by
  rcases upperUnitriangularSubgroup_rational_packet_data (p := p) hp2 with ⟨Φ, hΦ⟩
  have hdim :
      Module.finrank ℚ ℚ[upperUnitriangularSubgroup (ZMod p) 3] =
        Module.finrank ℚ (RationalPacketTarget (p := p)) := by
    rw [upperUnitriangularSubgroup_groupAlgebra_finrank_p_cubed (p := p),
      rational_target_finrank_p_cubed (p := p)]
  -- Once the packet map is injective, the common `p^3` dimension forces bijectivity.
  exact algEquiv_of_injective_algHom_of_finrank_eq Φ hdim hΦ

/-- Exercise 13-13.1-17 (2): source part (b) for the Sylow `p`-subgroup `G ≤ GL₃(𝔽_p)`. Its
rational group algebra is the product of `ℚ`, `p + 1` copies of `ℚ(p) = CyclotomicField p ℚ`,
and the matrix algebra `M_p(ℚ(p))`, assuming `p` is odd. -/
theorem sylowGL3_rational_groupAlgebra_decomposition
    (hp2 : p ≠ 2)
    (P : Sylow p (GL (Fin 3) (ZMod p))) :
    Nonempty
      (ℚ[P] ≃ₐ[ℚ]
        RationalPacketTarget (p := p)) := by
  rcases sylowGL3_mulEquiv_upperUnitriangularSubgroup (p := p) P with ⟨eP⟩
  rcases groupAlgebra_equiv_of_mulEquiv (k := ℚ) eP with ⟨eAlg⟩
  rcases upperUnitriangularSubgroup_rational_groupAlgebra_decomposition
      (p := p) hp2 with ⟨eU⟩
  -- Compose the arbitrary-Sylow transport with the canonical Heisenberg-model decomposition.
  exact ⟨eAlg.trans eU⟩

section

variable (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))))

local notation "GPrime" =>
  Multiplicative (ZMod (p ^ 2)) ⋊[φ] Multiplicative (ZMod p)

/-- Helper for Exercise 13-13.1-17: the integer `p + 1` is coprime to `p²`, so it defines the
standard unit in `Z / p² Z`. -/
private theorem standard_nonabelian_zmodP2_unit_coprime :
    Nat.Coprime (p + 1) (p ^ 2) := by
  -- Consecutive integers are coprime, and coprimeness survives taking powers on the second slot.
  have hcoprime : Nat.Coprime (p + 1) p := by
    rw [Nat.coprime_self_add_left]
    exact Nat.coprime_one_left p
  exact hcoprime.pow_right 2

/-- Helper for Exercise 13-13.1-17: the unit `1 + p` in `Z / p² Z` is the owner of LinearRepresentations_Serre_1977's
standard semidirect action. -/
private def standard_nonabelian_zmodP2_unit : (ZMod (p ^ 2))ˣ :=
  ZMod.unitOfCoprime (p + 1) (standard_nonabelian_zmodP2_unit_coprime (p := p))

/-- Helper for Exercise 13-13.1-17: powers of `Multiplicative.ofAdd 1` in `Z / p Z` recover the
corresponding natural-number classes. -/
private theorem ofAdd_one_pow_mod_p (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod p)) ^ n =
      Multiplicative.ofAdd ((n : ℕ) : ZMod p) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [pow_succ, ih]

/-- Helper for Exercise 13-13.1-17: the semidirect action is already determined by the image of
the additive generator `1 ∈ Z / p Z`. -/
private theorem semidirect_action_trivial_of_generator_eq_one
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod p)) = 1) :
    φ = 1 := by
  ext x y
  -- Every element of `Multiplicative (ZMod p)` is a power of the class of `1`.
  have hxpow :
      (Multiplicative.ofAdd (1 : ZMod p)) ^ x.val =
        Multiplicative.ofAdd x := by
    simpa [ZMod.natCast_val] using (ofAdd_one_pow_mod_p (p := p) x.val)
  calc
    φ (Multiplicative.ofAdd x) y
        = φ ((Multiplicative.ofAdd (1 : ZMod p)) ^ x.val) y := by
            rw [← hxpow]
    _ = ((φ (Multiplicative.ofAdd (1 : ZMod p))) ^ x.val) y := by
          rw [map_pow]
    _ = y := by
          simp [hgen]

/-- Helper for Exercise 13-13.1-17: if the `Z / p Z`-action is trivial, the semidirect product is
just the direct product of two abelian factors. -/
private theorem semidirectProduct_isMulCommutative_of_action_trivial
    (htriv : φ = 1) :
    IsMulCommutative GPrime := by
  refine IsMulCommutative.of_comm ?_
  intro a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  ext <;> simp [htriv, mul_comm, mul_assoc]

/-- Helper for Exercise 13-13.1-17: the acting generator has `p`-th power equal to `1` because
the source `Z / p Z` has exponent `p`. -/
private theorem semidirect_action_generator_pow_p :
    (φ (Multiplicative.ofAdd (1 : ZMod p))) ^ p = 1 := by
  have hsrc : (Multiplicative.ofAdd (1 : ZMod p)) ^ p = 1 := by
    rw [ofAdd_one_pow_mod_p (p := p) p, ZMod.natCast_self]
    rfl
  simpa using congrArg φ hsrc

/-- Helper for Exercise 13-13.1-17: noncommutativity forces the `Z / p Z`-generator to act
nontrivially. -/
private theorem semidirect_action_generator_ne_one_of_noncommutative
    (hφ : ¬ IsMulCommutative GPrime) :
    φ (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 := by
  intro hgen
  apply hφ
  exact semidirectProduct_isMulCommutative_of_action_trivial
    (p := p) (φ := φ) (semidirect_action_trivial_of_generator_eq_one (p := p) (φ := φ) hgen)

/-- Helper for Exercise 13-13.1-17: in the nonabelian case, the acting generator has exact order
`p` inside `Aut(Z / p² Z)`. -/
private theorem semidirect_action_generator_orderOf_eq_p
    (hφ : ¬ IsMulCommutative GPrime) :
    orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) = p := by
  -- The previous two lemmas reduce the order computation to the prime-order criterion.
  exact orderOf_eq_prime
    (semidirect_action_generator_pow_p (p := p) (φ := φ))
    (semidirect_action_generator_ne_one_of_noncommutative (p := p) (φ := φ) hφ)

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's standard unit has order dividing `p`, so the
`Z / p Z`-parameter really factors through the `1 + p` action modulo `p²`. -/
private theorem standard_nonabelian_zmodP2_unit_pow_p :
    (standard_nonabelian_zmodP2_unit (p := p)) ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  unfold standard_nonabelian_zmodP2_unit
  rw [ZMod.coe_unitOfCoprime, Nat.cast_add, Nat.cast_one, add_comm]
  have hp : Nat.Prime p := Fact.out
  -- Expand `(1 + p)^p` in characteristic `p`; every nontrivial term is divisible by `p²`.
  obtain ⟨r, hr0⟩ :=
    exists_add_pow_prime_pow_eq hp (1 : ZMod (p ^ 2)) (p : ZMod (p ^ 2)) 1
  have hr :
      ((1 + (p : ZMod (p ^ 2))) ^ p) =
        1 + (p : ZMod (p ^ 2)) ^ p + (p : ZMod (p ^ 2)) * 1 * (p : ZMod (p ^ 2)) * r := by
    simpa [pow_one] using hr0
  rw [hr]
  have hppow : ((p : ZMod (p ^ 2)) ^ p) = 0 := by
    exact ZMod.natCast_pow_eq_zero_of_le p (show 2 ≤ p by exact hp.two_le)
  have hp2 : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by
    exact ZMod.natCast_pow_eq_zero_of_le p (show 2 ≤ 2 by decide)
  rw [hppow]
  ring_nf
  simp [hp2]

/-- Helper for Exercise 13-13.1-17: the standard unit `1 + p` is nontrivial modulo `p²`. -/
private theorem standard_nonabelian_zmodP2_unit_ne_one :
    standard_nonabelian_zmodP2_unit (p := p) ≠ 1 := by
  intro hunit
  -- Compare underlying residue classes and isolate the surviving class of `p`.
  apply_fun Units.val at hunit
  unfold standard_nonabelian_zmodP2_unit at hunit
  rw [ZMod.coe_unitOfCoprime, Nat.cast_add, Nat.cast_one] at hunit
  have hp : Nat.Prime p := Fact.out
  have hp_lt : p < p ^ 2 := by
    nlinarith [hp.two_le]
  have hp_cast_ne_zero : ((p : ℕ) : ZMod (p ^ 2)) ≠ 0 := by
    intro hzero
    rw [ZMod.natCast_eq_zero_iff] at hzero
    exact (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt) hzero
  have hp_zero : ((p : ℕ) : ZMod (p ^ 2)) = 0 := by
    have hsub := congrArg (fun x : ZMod (p ^ 2) => x - 1) hunit
    simpa using hsub
  exact hp_cast_ne_zero hp_zero

/-- Helper for Exercise 13-13.1-17: the standard unit `1 + p` has exact order `p`. -/
private theorem standard_nonabelian_zmodP2_unit_order :
    orderOf (standard_nonabelian_zmodP2_unit (p := p)) = p := by
  -- The previous two lemmas put `1 + p` in the unique nontrivial `p`-torsion class.
  exact orderOf_eq_prime
    (standard_nonabelian_zmodP2_unit_pow_p (p := p))
    (standard_nonabelian_zmodP2_unit_ne_one (p := p))

/-- Helper for Exercise 13-13.1-17: the unit group of `Z / p² Z` is cyclic for every prime `p`.
The odd-prime case uses the general prime-power theorem, and `p = 2` reduces to `ZMod 4`. -/
private theorem zmodP2_units_isCyclic :
    IsCyclic (ZMod (p ^ 2))ˣ := by
  by_cases hp2 : p = 2
  · subst hp2
    simpa using ZMod.isCyclic_units_four
  · exact ZMod.isCyclic_units_of_prime_pow p (Fact.out) hp2 2

/-- Helper for Exercise 13-13.1-17: every order-`p` unit in `(Z / p² Z)ˣ` lies in the subgroup
generated by LinearRepresentations_Serre_1977's standard unit `1 + p`. -/
private theorem order_p_unit_mem_standard_zpowers
    (u : (ZMod (p ^ 2))ˣ) (hu_pow : u ^ p = 1) (_hu_ne : u ≠ 1) :
    u ∈ Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) := by
  letI : IsCyclic (ZMod (p ^ 2))ˣ := zmodP2_units_isCyclic (p := p)
  let K : Subgroup ((ZMod (p ^ 2))ˣ) :=
    (powMonoidHom p : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
  have hu_mem : u ∈ K := by
    -- The kernel of the `p`-th-power map is exactly the `p`-torsion layer.
    change u ^ p = 1
    exact hu_pow
  have hs_le : Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) ≤ K := by
    -- The standard unit also lies in that `p`-torsion layer.
    rw [Subgroup.zpowers_le]
    change (standard_nonabelian_zmodP2_unit (p := p)) ^ p = 1
    exact standard_nonabelian_zmodP2_unit_pow_p (p := p)
  have hK_card : Nat.card K = p := by
    -- In the cyclic unit group of cardinal `p (p - 1)`, the `p`-power kernel has cardinal `p`.
    rw [show Nat.card K =
        Nat.card ↥((powMonoidHom p : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker) by
        rfl]
    rw [IsCyclic.card_powMonoidHom_ker ((ZMod (p ^ 2))ˣ) p]
    have hcard_units : Nat.card ((ZMod (p ^ 2))ˣ) = p * (p - 1) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      simpa [pow_succ] using
        Nat.totient_prime_pow (Fact.out) (show 0 < 2 by decide)
    rw [hcard_units, Nat.gcd_comm]
    exact Nat.gcd_eq_left (dvd_mul_right p (p - 1))
  have hz_card :
      Nat.card (Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p))) = p := by
    -- The subgroup generated by `1 + p` has the same cardinality `p`.
    rw [Nat.card_zpowers, standard_nonabelian_zmodP2_unit_order (p := p)]
  have htop_card :
      Nat.card
          ((Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p))).subgroupOf K) =
        Nat.card K := by
    rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hs_le).toEquiv), hz_card, hK_card]
  have htop :
      (Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p))).subgroupOf K = ⊤ := by
    exact (Subgroup.card_eq_iff_eq_top _).mp htop_card
  have hEq : Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) = K := by
    -- Equal cardinality upgrades the inclusion to equality of subgroups.
    exact le_antisymm hs_le (Subgroup.subgroupOf_eq_top.mp htop)
  have hu_mem' : u ∈ Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) := by
    rw [hEq]
    exact hu_mem
  exact hu_mem'

/-- Helper for Exercise 13-13.1-17: the chosen order-`p` unit kills `p` inside the lifted additive
presentation of `Z / p Z`. -/
private theorem standard_nonabelian_zmodP2_unit_zmultiples_zero :
    zmultiplesHom (Additive ((ZMod (p ^ 2))ˣ))
        (Additive.ofMul (standard_nonabelian_zmodP2_unit (p := p))) p =
      0 := by
  -- `ZMod.lift` only needs the generator to have `p`-th power equal to `1`.
  change (standard_nonabelian_zmodP2_unit (p := p)) ^ p = 1
  simpa using standard_nonabelian_zmodP2_unit_pow_p (p := p)

/-- Helper for Exercise 13-13.1-17: the `Z / p Z`-parameter maps to powers of the standard
`1 + p` unit in `(Z / p² Z)ˣ`. -/
private def standard_nonabelian_zmodP2_units_hom :
    Multiplicative (ZMod p) →* (ZMod (p ^ 2))ˣ :=
  AddMonoidHom.toMultiplicativeLeft <|
    ZMod.lift p
      ⟨zmultiplesHom (Additive ((ZMod (p ^ 2))ˣ))
          (Additive.ofMul (standard_nonabelian_zmodP2_unit (p := p))),
        standard_nonabelian_zmodP2_unit_zmultiples_zero (p := p)⟩

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's standard `Z/p² ⋊ Z/p` model is governed by the
`1 + p` automorphism of `Z / p² Z`. -/
private def standard_nonabelian_zmodP2_action :
    Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))) :=
  ((MulAutMultiplicative (ZMod (p ^ 2))).symm.toMonoidHom).comp <|
    ((ZMod.AddAutEquivUnits (p ^ 2)).symm.toMonoidHom).comp <|
      standard_nonabelian_zmodP2_units_hom (p := p)

local notation "StandardGPrime" =>
  Multiplicative (ZMod (p ^ 2)) ⋊[standard_nonabelian_zmodP2_action (p := p)] Multiplicative
    (ZMod p)

/-- Helper for Exercise 13-13.1-17: the distinguished `Z / p² Z` generator in LinearRepresentations_Serre_1977's standard
semidirect model. -/
private def standard_nonabelian_semidirect_inl_one : StandardGPrime :=
  SemidirectProduct.inl (φ := standard_nonabelian_zmodP2_action (p := p))
    (Multiplicative.ofAdd (1 : ZMod (p ^ 2)))

/-- Helper for Exercise 13-13.1-17: the canonical standard semidirect model is finite because its
underlying type is equivalent to a finite product. -/
private instance standard_nonabelian_zmod_semidirectProduct_finite : Finite StandardGPrime :=
  Finite.of_equiv
    (Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod p))
    (SemidirectProduct.equivProd
      (N := Multiplicative (ZMod (p ^ 2)))
      (G := Multiplicative (ZMod p))
      (φ := standard_nonabelian_zmodP2_action (p := p))).symm

/-- Helper for Exercise 13-13.1-17: the canonical standard semidirect model has order `p^3`. -/
private theorem standard_nonabelian_zmod_semidirectProduct_card_p_cubed :
    Nat.card StandardGPrime = p ^ 3 := by
  -- Forget the multiplication and count the underlying product type.
  rw [SemidirectProduct.card]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (p ^ 2)) ≃ ZMod (p ^ 2))]
  rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p)]
  rw [Nat.card_eq_fintype_card, ZMod.card]
  ring

/-- Helper for Exercise 13-13.1-17: the standard semidirect-model group algebra has `ℚ`-dimension
`p^3`. -/
private theorem standard_nonabelian_zmod_semidirectProduct_groupAlgebra_finrank_p_cubed :
    Module.finrank ℚ ℚ[StandardGPrime] = p ^ 3 := by
  -- The semidirect product has the expected order `p^2 * p`.
  rw [groupAlgebra_finrank_eq_natCard (k := ℚ) (G := StandardGPrime),
    standard_nonabelian_zmod_semidirectProduct_card_p_cubed (p := p)]

/-- Helper for Exercise 13-13.1-17: in the canonical standard semidirect model, the `Z / p² Z`
generator still has nontrivial `p`-th power. -/
private theorem standard_nonabelian_semidirect_inl_one_pow_p_ne_one :
    (standard_nonabelian_semidirect_inl_one (p := p)) ^ p ≠ 1 := by
  simpa [standard_nonabelian_semidirect_inl_one] using
    semidirect_inl_one_pow_p_ne_one (p := p) (φ := standard_nonabelian_zmodP2_action (p := p))

/-- Helper for Exercise 13-13.1-17: the semidirect Jennings obstruction reads off the coefficient
of the surviving basis element `a^p`. -/
private def standard_nonabelian_semidirect_pth_power_coefficient :
    (ZMod p)[StandardGPrime] →ₗ[ZMod p] ZMod p where
  toFun z := z ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p)
  map_add' x y := by
    rfl
  map_smul' c z := by
    rfl

/-- Helper for Exercise 13-13.1-17: the coefficient detector already evaluates to `1` on LinearRepresentations_Serre_1977's
distinguished source-side class `([a] - 1)^p`. -/
private theorem standard_nonabelian_semidirect_pth_power_coefficient_yRaw_pow_p :
    standard_nonabelian_semidirect_pth_power_coefficient (p := p)
      (((MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) ^
        p) = 1 := by
  rw [monoidAlgebra_of_sub_one_pow_p (p := p) (G := StandardGPrime)
    (standard_nonabelian_semidirect_inl_one (p := p))]
  have hpow_ne :
      (standard_nonabelian_semidirect_inl_one (p := p)) ^ p ≠ 1 :=
    standard_nonabelian_semidirect_inl_one_pow_p_ne_one (p := p)
  -- Evaluate the surviving basis vector `[(a^p)] - 1` at `a^p`; the scalar part vanishes because
  -- `a^p ≠ 1`.
  unfold standard_nonabelian_semidirect_pth_power_coefficient
  have hone_coeff :
      (1 : (ZMod p)[StandardGPrime])
        ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) = 0 := by
    simp [MonoidAlgebra.one_def, hpow_ne]
  simpa [sub_eq_add_neg, hone_coeff] using
    (show (MonoidAlgebra.of (ZMod p) StandardGPrime
        ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p))
      ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) = 1 by
        simp [MonoidAlgebra.of_apply])

/-- Helper for Exercise 13-13.1-17: on the standard semidirect model, the augmentation generator
coming from the `Z / p² Z` factor has nonzero `p`-th power over `𝔽_p`. -/
private theorem standard_nonabelian_semidirect_inl_sub_one_pow_p_ne_zero :
    ((MonoidAlgebra.of (ZMod p) StandardGPrime
        (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) ^ p ≠
      0 := by
  intro hzero
  -- Route correction: package the surviving `a^p` coefficient as a linear functional so the later
  -- graded-quotient detector can reuse the same calculation instead of redoing it ad hoc.
  have hcoeff :
      standard_nonabelian_semidirect_pth_power_coefficient (p := p)
        (((MonoidAlgebra.of (ZMod p) StandardGPrime
            (standard_nonabelian_semidirect_inl_one (p := p)) :
              (ZMod p)[StandardGPrime]) - 1) ^ p) =
        standard_nonabelian_semidirect_pth_power_coefficient (p := p) 0 := by
    exact congrArg (standard_nonabelian_semidirect_pth_power_coefficient (p := p)) hzero
  rw [standard_nonabelian_semidirect_pth_power_coefficient_yRaw_pow_p (p := p)] at hcoeff
  simpa [standard_nonabelian_semidirect_pth_power_coefficient] using hcoeff

/-- Helper for Exercise 13-13.1-17: the distinguished semidirect `Z / p² Z` generator has
trivial `p²`-th power. -/
private theorem standard_nonabelian_semidirect_inl_one_pow_p_sq_eq_one :
    (standard_nonabelian_semidirect_inl_one (p := p)) ^ (p ^ 2) = 1 := by
  -- Compute the full `p²`-power in the normal cyclic factor.
  calc
    (standard_nonabelian_semidirect_inl_one (p := p)) ^ (p ^ 2)
        = (SemidirectProduct.inl
            (φ := standard_nonabelian_zmodP2_action (p := p))
            (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) : StandardGPrime) ^ (p ^ 2) := by
              rfl
    _ = SemidirectProduct.inl
          (φ := standard_nonabelian_zmodP2_action (p := p))
          ((Multiplicative.ofAdd (1 : ZMod (p ^ 2))) ^ (p ^ 2)) := by
            exact
              ((SemidirectProduct.inl
                (φ := standard_nonabelian_zmodP2_action (p := p))).map_pow
                (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) (p ^ 2)).symm
    _ = SemidirectProduct.inl
          (φ := standard_nonabelian_zmodP2_action (p := p))
          (Multiplicative.ofAdd (((p ^ 2 : ℕ) : ZMod (p ^ 2)))) := by
            rw [ofAdd_one_pow (p := p) (p ^ 2)]
    _ = 1 := by
          rw [ZMod.natCast_self]
          rfl

/-- Helper for Exercise 13-13.1-17: the distinguished semidirect augmentation generator is
nilpotent of order at most `p²`. -/
private theorem standard_nonabelian_semidirect_inl_sub_one_isNilpotent :
    IsNilpotent
      ((MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) := by
  refine ⟨p ^ 2, ?_⟩
  -- Apply the characteristic-`p` formula twice and then use the `p²`-torsion of the source
  -- generator.
  calc
    (((MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) ^
          (p ^ 2))
        = ((((MonoidAlgebra.of (ZMod p) StandardGPrime
                (standard_nonabelian_semidirect_inl_one (p := p)) :
                  (ZMod p)[StandardGPrime]) - 1) ^ p) ^ p) := by
              simpa [pow_two] using
                (pow_mul
                  ((MonoidAlgebra.of (ZMod p) StandardGPrime
                      (standard_nonabelian_semidirect_inl_one (p := p)) :
                        (ZMod p)[StandardGPrime]) - 1) p p)
    _ = ((MonoidAlgebra.of (ZMod p) StandardGPrime
            ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) :
              (ZMod p)[StandardGPrime]) - 1) ^ p := by
          rw [monoidAlgebra_of_sub_one_pow_p (p := p) (G := StandardGPrime)
            (standard_nonabelian_semidirect_inl_one (p := p))]
    _ = MonoidAlgebra.of (ZMod p) StandardGPrime
          (((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) ^ p) - 1 := by
            rw [monoidAlgebra_of_sub_one_pow_p (p := p) (G := StandardGPrime)
              ((standard_nonabelian_semidirect_inl_one (p := p)) ^ p)]
    _ = 0 := by
          have hpow :
              (((standard_nonabelian_semidirect_inl_one (p := p)) ^ p) ^ p) = 1 := by
            simpa [pow_mul, pow_two, mul_comm] using
              standard_nonabelian_semidirect_inl_one_pow_p_sq_eq_one (p := p)
          rw [hpow]
          ext g
          by_cases hg : g = 1
          · subst hg
            simp [MonoidAlgebra.of, MonoidAlgebra.one_def]
          · simp [MonoidAlgebra.of, MonoidAlgebra.one_def, hg]

/-- Helper for Exercise 13-13.1-17: the canonical standard semidirect model carries the usual
augmentation map to `𝔽_p`. -/
private def standard_nonabelian_semidirect_augmentation :
    (ZMod p)[StandardGPrime] →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) StandardGPrime (1 : StandardGPrime →* ZMod p)

/-- Helper for Exercise 13-13.1-17: the standard semidirect augmentation map is surjective. -/
private theorem standard_nonabelian_semidirect_augmentation_surjective :
    Function.Surjective (standard_nonabelian_semidirect_augmentation (p := p)) := by
  intro z
  refine ⟨algebraMap (ZMod p) ((ZMod p)[StandardGPrime]) z, ?_⟩
  -- The augmentation sends scalar coefficients to the same scalar in `𝔽_p`.
  simp [standard_nonabelian_semidirect_augmentation]

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's distinguished semidirect augmentation generator
belongs to the augmentation kernel. -/
private theorem standard_nonabelian_semidirect_inl_sub_one_mem_augmentationKernel :
    let yRaw : (ZMod p)[StandardGPrime] :=
      (MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1
    yRaw ∈ RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom := by
  -- The augmentation again sends `[a]` and `1` to the same scalar `1`.
  rw [RingHom.mem_ker]
  simp [standard_nonabelian_semidirect_augmentation]

/-- Helper for Exercise 13-13.1-17: the standard semidirect augmentation kernel is exactly the
span of the standard generators `[g] - 1`. -/
private theorem standard_nonabelian_semidirect_augmentationKernel_eq_span_sub_one :
    RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom =
      Ideal.span
        (Set.range fun g : StandardGPrime =>
          (MonoidAlgebra.of (ZMod p) StandardGPrime g : (ZMod p)[StandardGPrime]) - 1) := by
  -- The same finite-group augmentation owner applies unchanged to the standard semidirect model.
  simpa [standard_nonabelian_semidirect_augmentation] using
    (monoidAlgebra_augmentationKernel_eq_span_sub_one (p := p) (G := StandardGPrime))

/-- Helper for Exercise 13-13.1-17: the standard semidirect augmentation kernel is maximal because
the quotient is the field `𝔽_p`. -/
private theorem standard_nonabelian_semidirect_augmentationKernel_isMaximal :
    (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom).IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective
    (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom
    (standard_nonabelian_semidirect_augmentation_surjective (p := p))

/-- Helper for Exercise 13-13.1-17: the ring Jacobson radical is always contained in the maximal
standard semidirect augmentation kernel. -/
private theorem standard_nonabelian_semidirect_jacobson_le_augmentationKernel :
    Ring.jacobson ((ZMod p)[StandardGPrime]) ≤
      RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom := by
  letI :
      (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom).IsMaximal :=
    standard_nonabelian_semidirect_augmentationKernel_isMaximal (p := p)
  -- The Jacobson radical sits inside every maximal ideal, so it sits inside the augmentation
  -- kernel of the standard model.
  exact Ring.jacobson_le_of_isMaximal _

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's generator-level Jacobson lemma upgrades the concrete
standard semidirect augmentation kernel to a subideal of the Jacobson radical. -/
private theorem standard_nonabelian_semidirect_augmentationKernel_le_jacobson :
    RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom ≤
      Ring.jacobson ((ZMod p)[StandardGPrime]) := by
  have hspan :
      Ideal.span
          (Set.range fun g : StandardGPrime =>
            (MonoidAlgebra.of (ZMod p) StandardGPrime g : (ZMod p)[StandardGPrime]) - 1) ≤
        Ring.jacobson ((ZMod p)[StandardGPrime]) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    have hP : IsPGroup p StandardGPrime :=
      IsPGroup.of_card (standard_nonabelian_zmod_semidirectProduct_card_p_cubed (p := p))
    -- The standard semidirect generators are still augmentation generators of a `p`-group group
    -- algebra, so the same Jacobson owner applies.
    simpa using
      p_group_generator_sub_one_mem_jacobson
        (p := p) (G := StandardGPrime) hP g
  -- Rewrite the augmentation kernel by the span of the standard generators and apply the new
  -- generator-level Jacobson owner.
  rw [standard_nonabelian_semidirect_augmentationKernel_eq_span_sub_one (p := p)]
  exact hspan

/-- Helper for Exercise 13-13.1-17: on the canonical standard semidirect model, the Jacobson
radical is exactly the augmentation kernel. -/
private theorem standard_nonabelian_semidirect_jacobson_eq_augmentationKernel :
    Ring.jacobson ((ZMod p)[StandardGPrime]) =
      RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom := by
  -- The easy maximal-ideal inclusion and the new generator-level inclusion meet in the middle.
  exact le_antisymm
    (standard_nonabelian_semidirect_jacobson_le_augmentationKernel (p := p))
    (standard_nonabelian_semidirect_augmentationKernel_le_jacobson (p := p))

/-- Helper for Exercise 13-13.1-17: every nonabelian semidirect product
`(Z / p² Z) ⋊ (Z / p Z)` is multiplicatively equivalent to LinearRepresentations_Serre_1977's standard action model. -/
private theorem nonabelian_zmod_semidirectProduct_mulEquiv_standard_action
    (hφ : ¬ IsMulCommutative GPrime) :
    Nonempty (GPrime ≃* StandardGPrime) := by
  -- Route correction: separate the canonical semidirect normalization from the later packet
  -- classification so the remaining blocker is only the standard-model representation theory.
  let toUnits : MulAut (Multiplicative (ZMod (p ^ 2))) →* (ZMod (p ^ 2))ˣ :=
    (ZMod.AddAutEquivUnits (p ^ 2)).toMonoidHom.comp
      (MulAutMultiplicative (ZMod (p ^ 2))).toMonoidHom
  have htoUnits_inj : Function.Injective fun f => toUnits f := by
    intro a b hab
    apply (MulAutMultiplicative (ZMod (p ^ 2))).injective
    apply (ZMod.AddAutEquivUnits (p ^ 2)).injective
    exact hab
  let uφ : (ZMod (p ^ 2))ˣ := toUnits (φ (Multiplicative.ofAdd (1 : ZMod p)))
  have hgenerator_ne_one :
      φ (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 :=
    semidirect_action_generator_ne_one_of_noncommutative (p := p) (φ := φ) hφ
  have hgenerator_order :
      orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) = p :=
    semidirect_action_generator_orderOf_eq_p (p := p) (φ := φ) hφ
  have huφ_pow : uφ ^ p = 1 := by
    -- Transport the order-`p` relation from the acting automorphism to the unit picture.
    unfold uφ
    simpa [MonoidHom.map_pow] using
      congrArg toUnits (semidirect_action_generator_pow_p (p := p) (φ := φ))
  have huφ_ne : uφ ≠ 1 := by
    -- Nontriviality is preserved because the automorphism-to-unit conversion is injective.
    intro huφ_one
    apply hgenerator_ne_one
    apply htoUnits_inj
    simpa [uφ] using huφ_one
  have huφ_order : orderOf uφ = p := by
    -- The same injective conversion preserves the exact order `p`.
    unfold uφ
    rw [orderOf_injective toUnits htoUnits_inj]
    exact hgenerator_order
  have huφ_mem :
      uφ ∈ Subgroup.zpowers (standard_nonabelian_zmodP2_unit (p := p)) := by
    -- The acting generator already lands in the unique order-`p` subgroup generated by `1 + p`.
    exact order_p_unit_mem_standard_zpowers (p := p) uφ huφ_pow huφ_ne
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huφ_mem
  let g : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  let s : (ZMod (p ^ 2))ˣ := standard_nonabelian_zmodP2_unit (p := p)
  have hg_zpowers : ∀ x : Multiplicative (ZMod p), x ∈ Subgroup.zpowers g := by
    -- The quotient factor has prime cardinality `p`, so any nontrivial element generates it.
    have htop : Subgroup.zpowers g = ⊤ := by
      apply zpowers_eq_top_of_prime_card (p := p)
      · simpa using (ZMod.card p)
      · intro hg_one
        have : (1 : ZMod p) = 0 := (ofAdd_eq_one).mp hg_one
        exact zero_ne_one this.symm
    intro x
    simpa [g, htop]
  have hg_pow : g ^ p = 1 := by
    -- The additive generator of `Z / p Z` has exact exponent `p`.
    dsimp [g]
    rw [ofAdd_one_pow_mod_p (p := p) p, ZMod.natCast_self]
    rfl
  have hg_ne : g ≠ 1 := by
    -- The class of `1` modulo `p` is still nonzero.
    intro hg_one
    have : (1 : ZMod p) = 0 := (ofAdd_eq_one).mp hg_one
    exact zero_ne_one this.symm
  have hg_order : orderOf g = p := by
    -- Prime-order criterion on the additive generator.
    exact orderOf_eq_prime hg_pow hg_ne
  have hs_on_generator :
      standard_nonabelian_zmodP2_units_hom (p := p) g = s := by
    -- Unfold the additive lift once: the generator `1` is sent to LinearRepresentations_Serre_1977's standard unit `1 + p`.
    dsimp [g, s, standard_nonabelian_zmodP2_units_hom]
    simpa using
      congrArg Additive.toMul
        (ZMod.lift_coe
          (n := p)
          (f := ⟨zmultiplesHom (Additive ((ZMod (p ^ 2))ˣ))
            (Additive.ofMul (standard_nonabelian_zmodP2_unit (p := p))),
            standard_nonabelian_zmodP2_unit_zmultiples_zero (p := p)⟩)
          (1 : ℤ))
  have hgk_image :
      standard_nonabelian_zmodP2_units_hom (p := p) (g ^ k) = uφ := by
    -- The standard model sends `g ^ k` to the prescribed order-`p` unit `uφ`.
    calc
      standard_nonabelian_zmodP2_units_hom (p := p) (g ^ k)
          = (standard_nonabelian_zmodP2_units_hom (p := p) g) ^ k := by
              rw [map_zpow]
      _ = s ^ k := by rw [hs_on_generator]
      _ = uφ := hk
  have hgk_ne : g ^ k ≠ 1 := by
    -- Otherwise its image under the standard unit-valued hom would be trivial, contradicting `uφ ≠ 1`.
    intro hgk_one
    apply huφ_ne
    rw [← hgk_image, hgk_one]
    simp
  have hgk_zpowers : ∀ x : Multiplicative (ZMod p), x ∈ Subgroup.zpowers (g ^ k) := by
    -- A nontrivial element in a group of prime cardinality is again a generator.
    have htop : Subgroup.zpowers (g ^ k) = ⊤ := by
      apply zpowers_eq_top_of_prime_card (p := p)
      · simpa using (ZMod.card p)
      · exact hgk_ne
    intro x
    simpa [htop]
  have hgk_order : orderOf (g ^ k) = p := by
    -- Since `g ^ k` lies in the cyclic group generated by `g`, its order divides `p`; nontriviality
    -- rules out the divisor `1`.
    have hdvd : orderOf (g ^ k) ∣ p := by
      have hdvd' : orderOf (g ^ k) ∣ orderOf g :=
        orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
      rwa [hg_order] at hdvd'
    rcases (Nat.dvd_prime (Fact.out)).1 hdvd with h_one | h_p
    · exfalso
      exact hgk_ne ((orderOf_eq_one_iff.mp h_one) : g ^ k = 1)
    · exact h_p
  let β : Multiplicative (ZMod p) ≃* Multiplicative (ZMod p) :=
    mulEquivOfOrderOfEq hg_zpowers hgk_zpowers (hg_order.trans hgk_order.symm)
  have hβ_generator : β g = g ^ k := by
    -- The cyclic-group equivalence is defined by sending the chosen generator to `g ^ k`.
    simpa [β] using
      (mulEquivOfOrderOfEq_apply_gen hg_zpowers hgk_zpowers (hg_order.trans hgk_order.symm))
  have h_units :
      (standard_nonabelian_zmodP2_units_hom (p := p)).comp β.toMonoidHom = toUnits.comp φ := by
    -- Both unit-valued homomorphisms are determined by the generator `g`.
    exact
      (MonoidHom.eq_iff_eq_on_generator hg_zpowers _ _).2 <|
        calc
          ((standard_nonabelian_zmodP2_units_hom (p := p)).comp β.toMonoidHom) g
              = standard_nonabelian_zmodP2_units_hom (p := p) (β g) := rfl
          _ = standard_nonabelian_zmodP2_units_hom (p := p) (g ^ k) := by rw [hβ_generator]
          _ = uφ := hgk_image
          _ = toUnits (φ g) := by rfl
          _ = (toUnits.comp φ) g := rfl
  have h_action :
      ((standard_nonabelian_zmodP2_action (p := p)).comp β.toMonoidHom) = φ := by
    -- Apply the injective automorphism-to-unit conversion pointwise.
    refine MonoidHom.ext ?_
    intro x
    apply htoUnits_inj
    have hx := congrArg (fun f : Multiplicative (ZMod p) →* (ZMod (p ^ 2))ˣ => f x) h_units
    calc
      toUnits (((standard_nonabelian_zmodP2_action (p := p)).comp β.toMonoidHom) x)
          = (standard_nonabelian_zmodP2_units_hom (p := p)) (β x) := by
              ext
              change ((standard_nonabelian_zmodP2_units_hom (p := p)) (β x) : ZMod (p ^ 2)) •
                  (1 : ZMod (p ^ 2)) =
                ↑((standard_nonabelian_zmodP2_units_hom (p := p)) (β x))
              simp
      _ = toUnits (φ x) := hx
  refine ⟨SemidirectProduct.congr (MulEquiv.refl _) β ?_⟩
  intro x
  -- The semidirect-product compatibility is exactly the action equality established above.
  have hx := congrArg
    (fun f : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))) => f x) h_action
  simpa using hx.symm

/-- Helper for Exercise 13-13.1-17: once LinearRepresentations_Serre_1977's packet comparison map on the canonical standard
semidirect model is injective, finite-dimensionality upgrades it to the desired
Artin-Wedderburn equivalence. -/
private theorem standard_nonabelian_zmod_semidirectProduct_rational_packet_data
    (hp2 : p ≠ 2) :
    ∃ Φ :
      ℚ[StandardGPrime] →ₐ[ℚ] RationalPacketTarget (p := p),
      Function.Injective Φ := by
  -- Route correction: the semidirect normalization is complete, so the only remaining source
  -- step is the explicit packet map built from the normal cyclic subgroup of order `p²`.
  -- TODO: assemble the `p + 1` linear packets and the single degree-`p` monomial packet for the
  -- standard `1 + p` action, then prove that zero packet data kills the complete complex
  -- semidirect family so `rational_packet_map_injective_of_complex_family` applies.
  sorry

/-- Helper for Exercise 13-13.1-17: the source-faithful rational Artin-Wedderburn owner on the
canonical nonabelian semidirect model. -/
private theorem standard_nonabelian_zmod_semidirectProduct_rational_groupAlgebra_decomposition
    (hp2 : p ≠ 2) :
    Nonempty
      (ℚ[StandardGPrime] ≃ₐ[ℚ] RationalPacketTarget (p := p)) := by
  rcases standard_nonabelian_zmod_semidirectProduct_rational_packet_data
      (p := p) hp2 with ⟨Φ, hΦ⟩
  have hdim :
      Module.finrank ℚ ℚ[StandardGPrime] =
        Module.finrank ℚ (RationalPacketTarget (p := p)) := by
    rw [standard_nonabelian_zmod_semidirectProduct_groupAlgebra_finrank_p_cubed (p := p),
      rational_target_finrank_p_cubed (p := p)]
  -- The standard-model packet map has the same source and target dimension `p^3`, so injectivity
  -- already implies bijectivity.
  exact algEquiv_of_injective_algHom_of_finrank_eq Φ hdim hΦ

/-- Helper for Exercise 13-13.1-17: on the canonical Heisenberg model, every Jacobson-radical
element has trivial class in LinearRepresentations_Serre_1977's Jennings quotient `J^p / J^(p+1)`. -/
private theorem upperUnitriangularSubgroup_generator_pth_power_mem_augmentation_pow_succ
    (hp2 : p ≠ 2)
    (g : upperUnitriangularSubgroup (ZMod p) 3) :
    (((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
        (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ^ p) ∈
      (RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom) ^ (p + 1) := by
  -- The source-side Heisenberg generator already has zero `p`-th power, so its class vanishes in
  -- every later augmentation quotient.
  have hpow :
      (((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
          (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ^ p) = 0 :=
    upperUnitriangularSubgroup_of_sub_one_pow_p_eq_zero (p := p) hp2 g
  rw [hpow]
  exact Ideal.zero_mem _

/-- Helper for Exercise 13-13.1-17: on the canonical Heisenberg model, every Jacobson-radical
element has trivial class in LinearRepresentations_Serre_1977's Jennings quotient `J^p / J^(p+1)`. -/
private theorem upperUnitriangularSubgroup_generator_pth_power_class_zero
    (hp2 : p ≠ 2)
    (g : upperUnitriangularSubgroup (ZMod p) 3) :
    Ideal.Quotient.mk
        (Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) ^ (p + 1))
        ((((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
            (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ^ p)) =
      0 := by
  -- Route correction: record the source-side generator calculation directly as augmentation-power
  -- membership, since that is the invariant later transported through Jennings quotients.
  have hmem_aug :
      (((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
          (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ^ p) ∈
        (RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom) ^ (p + 1) :=
    upperUnitriangularSubgroup_generator_pth_power_mem_augmentation_pow_succ
      (p := p) hp2 g
  have hmem_jac :
      (((MonoidAlgebra.of (ZMod p) (upperUnitriangularSubgroup (ZMod p) 3) g :
          (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) - 1) ^ p) ∈
        Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) ^ (p + 1) := by
    -- Rewrite the closed augmentation estimate once to the actual Jacobson filtration.
    simpa [upperUnitriangularSubgroup_jacobson_eq_augmentationKernel (p := p)] using hmem_aug
  exact Ideal.Quotient.eq_zero_iff_mem.2 hmem_jac

/-- Helper for Exercise 13-13.1-17: on the canonical Heisenberg model, every Jacobson-radical
element has trivial class in LinearRepresentations_Serre_1977's Jennings quotient `J^p / J^(p+1)`. -/
private theorem upperUnitriangularSubgroup_augmentation_pth_power_mem_pow_succ
    (hp2 : p ≠ 2)
    (x : (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3])
    (hx : x ∈ RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom) :
    x ^ p ∈
      (RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom) ^ (p + 1) := by
  -- Route correction: the remaining modular Heisenberg step is exactly LinearRepresentations_Serre_1977's augmentation
  -- filtration estimate in the quotient by `I^(p + 1)`, not another Jacobson-radical rewrite.
  -- TODO: write `x` modulo `I²` in terms of the two abelianization generators, note that the
  -- central commutator generator already lies in `I²`, and use Frobenius together with
  -- `upperUnitriangularSubgroup_of_sub_one_pow_p_eq_zero` to force `x ^ p` into `I^(p + 1)`.
  sorry

/-- Helper for Exercise 13-13.1-17: on the canonical Heisenberg model, every Jacobson-radical
element has trivial class in LinearRepresentations_Serre_1977's Jennings quotient `J^p / J^(p+1)`. -/
private theorem upperUnitriangularSubgroup_jacobson_pth_power_class_zero
    (hp2 : p ≠ 2)
    (x : Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3])) :
    Ideal.Quotient.mk
        (Ring.jacobson ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) ^ (p + 1))
        (((x : (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]) ^ p)) =
      0 := by
  let A := (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]
  have hx_aug :
      ((x : Ring.jacobson A) : A) ∈
        RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom := by
    -- Rewrite the radical once to the augmentation kernel and keep the remaining work in the
    -- source-side augmentation filtration.
    simpa [A, upperUnitriangularSubgroup_jacobson_eq_augmentationKernel (p := p)] using x.property
  have hx_pow_aug :
      (((x : Ring.jacobson A) : A) ^ p) ∈
        (RingHom.ker (upperUnitriangularSubgroup_augmentation (p := p)).toRingHom) ^ (p + 1) :=
    upperUnitriangularSubgroup_augmentation_pth_power_mem_pow_succ
      (p := p) hp2 ((x : Ring.jacobson A) : A) hx_aug
  have hx_pow_jac :
      (((x : Ring.jacobson A) : A) ^ p) ∈ Ring.jacobson A ^ (p + 1) := by
    -- The augmentation-kernel estimate is exactly the desired Jennings-layer membership after the
    -- already-closed Jacobson equals augmentation rewrite.
    simpa [A, upperUnitriangularSubgroup_jacobson_eq_augmentationKernel (p := p)] using hx_pow_aug
  exact Ideal.Quotient.eq_zero_iff_mem.2 hx_pow_jac

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's distinguished semidirect augmentation generator is
already a Jacobson-radical element on the canonical standard model. -/
private theorem standard_nonabelian_semidirect_inl_sub_one_mem_jacobson :
    let yRaw : (ZMod p)[StandardGPrime] :=
      (MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1
    yRaw ∈ Ring.jacobson ((ZMod p)[StandardGPrime]) := by
  -- Rewrite the Jacobson radical as the augmentation kernel and reuse the closed generator fact.
  rw [standard_nonabelian_semidirect_jacobson_eq_augmentationKernel (p := p)]
  simpa using standard_nonabelian_semidirect_inl_sub_one_mem_augmentationKernel (p := p)

/-- Helper for Exercise 13-13.1-17: the canonical semidirect model already provides a Jacobson
witness whose ambient `p`-th power is nonzero. -/
private theorem standard_nonabelian_semidirect_generator_pth_power_ne_zero :
    ∃ y : Ring.jacobson ((ZMod p)[StandardGPrime]),
      (((y : (ZMod p)[StandardGPrime]) ^ p)) ≠ 0 := by
  let yRaw : (ZMod p)[StandardGPrime] :=
    (MonoidAlgebra.of (ZMod p) StandardGPrime
        (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1
  have hy_mem : yRaw ∈ Ring.jacobson ((ZMod p)[StandardGPrime]) := by
    simpa [yRaw] using standard_nonabelian_semidirect_inl_sub_one_mem_jacobson (p := p)
  refine ⟨⟨yRaw, hy_mem⟩, ?_⟩
  -- The remaining obstruction is no longer raw nonvanishing but survival modulo `J^(p+1)`.
  simpa [yRaw] using standard_nonabelian_semidirect_inl_sub_one_pow_p_ne_zero (p := p)

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's distinguished semidirect augmentation generator
already lies in the `p`-th augmentation power, so it defines a genuine degree-`p` Jennings-layer
class. -/
private theorem standard_nonabelian_semidirect_generator_pth_power_mem_augmentation_pow :
    let yRaw : (ZMod p)[StandardGPrime] :=
      (MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1
    yRaw ^ p ∈
      (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom) ^ p := by
  let yRaw : (ZMod p)[StandardGPrime] :=
    (MonoidAlgebra.of (ZMod p) StandardGPrime
        (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1
  have hy_mem :
      yRaw ∈ RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom := by
    simpa [yRaw] using standard_nonabelian_semidirect_inl_sub_one_mem_augmentationKernel (p := p)
  -- The source-side witness is an augmentation generator, so its `p`-th power lies in `I^p`.
  simpa [yRaw] using
    (Ideal.pow_mem_pow hy_mem p :
      yRaw ^ p ∈
        (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom) ^ p)

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's source-side semidirect obstruction is detected by a
linear functional that kills `I^(p + 1)` but evaluates to `1` on the distinguished class
`([a] - 1)^p`. -/
private theorem standard_nonabelian_semidirect_pth_layer_detector :
    ∃ δ : (ZMod p)[StandardGPrime] →ₗ[ZMod p] ZMod p,
      (∀ z ∈
          (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom) ^
            (p + 1), δ z = 0) ∧
        δ (((MonoidAlgebra.of (ZMod p) StandardGPrime
            (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1) ^
          p) = 1 := by
  -- TODO: define the coefficient-at-`a^p` functional on the standard semidirect basis, prove that
  -- every element of `I^(p + 1)` has zero `a^p` coefficient, and evaluate the detector on
  -- `([a] - 1)^p` using `monoidAlgebra_of_sub_one_pow_p`.
  sorry

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's distinguished semidirect augmentation generator
survives in the Jennings quotient `J^p / J^(p+1)`. -/
private theorem standard_nonabelian_semidirect_generator_pow_p_not_mem_augmentation_pow_succ :
    let yRaw : (ZMod p)[StandardGPrime] :=
      (MonoidAlgebra.of (ZMod p) StandardGPrime
          (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1
    yRaw ^ p ∉
      (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom) ^ (p + 1) := by
  let yRaw : (ZMod p)[StandardGPrime] :=
    (MonoidAlgebra.of (ZMod p) StandardGPrime
        (standard_nonabelian_semidirect_inl_one (p := p)) : (ZMod p)[StandardGPrime]) - 1
  rcases standard_nonabelian_semidirect_pth_layer_detector (p := p) with ⟨δ, hδ_zero, hδ_y⟩
  -- Route correction: once the source-side detector is isolated, the Jennings obstruction is a
  -- one-line contradiction between `δ yRaw^p = 1` and the fact that `δ` kills `I^(p + 1)`.
  intro hy_mem
  have hzero : δ (yRaw ^ p) = 0 := hδ_zero (yRaw ^ p) hy_mem
  have hone : δ (yRaw ^ p) = 1 := by
    simpa [yRaw] using hδ_y
  exact one_ne_zero (hone.symm.trans hzero)

/-- Helper for Exercise 13-13.1-17: LinearRepresentations_Serre_1977's distinguished semidirect augmentation generator
survives in the Jennings quotient `J^p / J^(p+1)`. -/
private theorem standard_nonabelian_semidirect_generator_pth_power_class_nonzero :
    ∃ y : Ring.jacobson ((ZMod p)[StandardGPrime]),
      Ideal.Quotient.mk
          (Ring.jacobson ((ZMod p)[StandardGPrime]) ^ (p + 1))
          (((y : (ZMod p)[StandardGPrime]) ^ p)) ≠
        0 := by
  let B := (ZMod p)[StandardGPrime]
  let yRaw : B :=
    (MonoidAlgebra.of (ZMod p) StandardGPrime
        (standard_nonabelian_semidirect_inl_one (p := p)) : B) - 1
  have hy_mem : yRaw ∈ Ring.jacobson B := by
    -- Freeze the distinguished augmentation generator as the Jacobson witness.
    simpa [B, yRaw] using standard_nonabelian_semidirect_inl_sub_one_mem_jacobson (p := p)
  have hy_not_mem :
      yRaw ^ p ∉
        (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom) ^ (p + 1) := by
    simpa [B, yRaw] using
      standard_nonabelian_semidirect_generator_pow_p_not_mem_augmentation_pow_succ (p := p)
  refine ⟨⟨yRaw, hy_mem⟩, ?_⟩
  intro hy_zero
  have hy_mem_jac :
      (yRaw ^ p : B) ∈ Ring.jacobson B ^ (p + 1) :=
    Ideal.Quotient.eq_zero_iff_mem.1 hy_zero
  have hy_mem_aug :
      (yRaw ^ p : B) ∈
        (RingHom.ker (standard_nonabelian_semidirect_augmentation (p := p)).toRingHom) ^ (p + 1) := by
    -- Rewrite the Jacobson radical once to the augmentation kernel and read off the contradiction
    -- in the source-side filtration.
    simpa [B, standard_nonabelian_semidirect_jacobson_eq_augmentationKernel (p := p)] using hy_mem_jac
  exact hy_not_mem hy_mem_aug

/-- Helper for Exercise 13-13.1-17: the canonical Heisenberg and standard semidirect models have
nonisomorphic group algebras over `𝔽_p`. -/
private theorem canonical_models_modP_groupAlgebras_not_isomorphic
    (hp2 : p ≠ 2) :
    ¬ Nonempty
      ((ZMod p)[upperUnitriangularSubgroup (ZMod p) 3] ≃ₐ[ZMod p]
        (ZMod p)[StandardGPrime]) := by
  -- Route correction: compare one explicit augmentation/Jennings layer on the two canonical
  -- models, rather than trying to prove the modular obstruction directly for arbitrary transports.
  -- The raw `p`-th power computations are already closed:
  -- `upperUnitriangularSubgroup_of_sub_one_pow_p_eq_zero` kills each Heisenberg generator, while
  -- `standard_nonabelian_semidirect_inl_sub_one_pow_p_ne_zero` gives the surviving semidirect
  -- generator. The first transport step is now isolated in
  -- `jennings_pth_power_class_preserved_of_algEquiv`, which handles Jacobson-radical membership
  -- under an algebra equivalence. The ideal-power rewrite step is now closed by
  -- `jacobson_pow_map_eq_of_algEquiv`, and the quotient-level `Submodule.mapQ` owner is now
  -- explicit in `jacobson_pow_quotient_map_of_algEquiv` together with
  -- `jacobson_pth_power_quotient_map_of_algEquiv`. The remaining blocker is narrower: produce the
  -- source-faithful Heisenberg zero class and semidirect nonzero class in the actual Jennings
  -- quotient `J^p / J^(p+1)` so the new transport lemmas can contradict an algebra equivalence.
  intro hIso
  rcases hIso with ⟨e⟩
  let A := (ZMod p)[upperUnitriangularSubgroup (ZMod p) 3]
  let B := (ZMod p)[StandardGPrime]
  rcases standard_nonabelian_semidirect_generator_pth_power_class_nonzero (p := p) with
    ⟨y, hy_nonzero⟩
  have hx_mem :
      e.symm (y : B) ∈ Ring.jacobson A := by
    -- Pull the semidirect Jennings witness back through the hypothetical algebra equivalence.
    simpa [A, B] using
      (mem_jacobson_iff_of_algEquiv (p := p) e.symm (x := (y : B))).1 y.property
  let x : Ring.jacobson A := ⟨e.symm (y : B), hx_mem⟩
  have hx_zero :
      Ideal.Quotient.mk (Ring.jacobson A ^ (p + 1)) (((x : A) ^ p)) = 0 :=
    upperUnitriangularSubgroup_jacobson_pth_power_class_zero (p := p) hp2 x
  have htransport_zero :
      Ideal.Quotient.mk (Ring.jacobson B ^ (p + 1)) (((y : B) ^ p)) = 0 := by
    -- The quotient-level transport now turns the Heisenberg zero class into a zero class on the
    -- semidirect side.
    let f :=
      jacobson_pow_quotient_map_of_algEquiv (p := p) e (p + 1)
    have hmap_zero' :
        f (Ideal.Quotient.mk (Ring.jacobson A ^ (p + 1)) (((x : A) ^ p))) =
          f (0 : A ⧸ Ring.jacobson A ^ (p + 1)) := by
      exact congrArg f hx_zero
    have hmap_zero :
        f (Ideal.Quotient.mk (Ring.jacobson A ^ (p + 1)) (((x : A) ^ p))) = 0 := by
      have hfzero : f (0 : A ⧸ Ring.jacobson A ^ (p + 1)) = 0 := by
        change
          jacobson_pow_quotient_map_of_algEquiv (p := p) e (p + 1)
              (Ideal.Quotient.mk (Ring.jacobson A ^ (p + 1)) (0 : A)) =
            0
        rw [jacobson_pow_quotient_map_of_algEquiv_mk (p := p) e (p + 1) (0 : A)]
        simp
      exact hmap_zero'.trans hfzero
    calc
      Ideal.Quotient.mk (Ring.jacobson B ^ (p + 1)) (((y : B) ^ p))
          = f (Ideal.Quotient.mk (Ring.jacobson A ^ (p + 1)) (((x : A) ^ p))) := by
              symm
              calc
                f (Ideal.Quotient.mk (Ring.jacobson A ^ (p + 1)) (((x : A) ^ p)))
                    = Ideal.Quotient.mk (Ring.jacobson B ^ (p + 1)) (e ((x : A)) ^ p) := by
                        exact
                          jacobson_pth_power_quotient_map_of_algEquiv
                            (p := p) e (x := (x : A))
                _ = Ideal.Quotient.mk (Ring.jacobson B ^ (p + 1)) (((y : B) ^ p)) := by
                      simp [A, B, x]
      _ = 0 := hmap_zero
  exact hy_nonzero htransport_zero

-- Proof sketch: classify the irreducible rational representations of the nonabelian semidirect
-- product `G'`, compute their character fields, and apply Artin-Wedderburn to `ℚ[G']`.
/-- Exercise 13-13.1-17 (3): source part (b) for the nonabelian semidirect product
`G' = (Z / p² Z) ⋊ (Z / p Z)`. Its rational group algebra has the same Artin-Wedderburn shape as
that of the Sylow `p`-subgroup of `GL₃(𝔽_p)`, assuming `p` is odd. -/
theorem nonabelian_zmod_semidirectProduct_rational_groupAlgebra_decomposition
    (hp2 : p ≠ 2)
    (hφ : ¬ IsMulCommutative GPrime) :
    Nonempty
      (ℚ[GPrime] ≃ₐ[ℚ]
        RationalPacketTarget (p := p)) := by
  rcases nonabelian_zmod_semidirectProduct_mulEquiv_standard_action
      (p := p) (φ := φ) hφ with ⟨eStd⟩
  rcases groupAlgebra_equiv_of_mulEquiv (k := ℚ) eStd with ⟨eAlg⟩
  rcases standard_nonabelian_zmod_semidirectProduct_rational_groupAlgebra_decomposition
      (p := p) hp2 with ⟨eStdAlg⟩
  -- Normalize first to LinearRepresentations_Serre_1977's standard semidirect model, then apply the canonical decomposition.
  exact ⟨eAlg.trans eStdAlg⟩

-- Proof sketch: combine the two Artin-Wedderburn decompositions from parts (2) and (3) by
-- composing one algebra equivalence with the inverse of the other.
/-- Exercise 13-13.1-17 (4): source part (b). For odd `p`, the rational group algebras of the two
groups are isomorphic. -/
theorem sylowGL3_and_nonabelian_zmod_semidirectProduct_rational_groupAlgebras_isomorphic
    (hp2 : p ≠ 2)
    (P : Sylow p (GL (Fin 3) (ZMod p)))
    (hφ : ¬ IsMulCommutative GPrime) :
    Nonempty (ℚ[P] ≃ₐ[ℚ] ℚ[GPrime]) := by
  -- Compose the two decompositions through the common Artin-Wedderburn target from parts `(2)`
  -- and `(3)`.
  rcases sylowGL3_rational_groupAlgebra_decomposition (p := p) hp2 P with ⟨eP⟩
  rcases nonabelian_zmod_semidirectProduct_rational_groupAlgebra_decomposition
      (p := p) (φ := φ) hp2 hφ with ⟨eGPrime⟩
  exact ⟨eP.trans eGPrime.symm⟩

-- Proof sketch: compute invariants of the modular group algebras in characteristic `p`, such as
-- their Jacobson radicals or Loewy layers, and show these invariants differ for the two groups.
/-- Exercise 13-13.1-17 (5): source part (c). For odd `p`, the group algebras over `𝔽_p` of the
two groups are not isomorphic. -/
theorem sylowGL3_and_nonabelian_zmod_semidirectProduct_modP_groupAlgebras_not_isomorphic
    (hp2 : p ≠ 2)
    (P : Sylow p (GL (Fin 3) (ZMod p)))
    (hφ : ¬ IsMulCommutative GPrime) :
    ¬ Nonempty
      ((ZMod p)[P] ≃ₐ[ZMod p]
        (ZMod p)[GPrime]) := by
  rcases sylowGL3_mulEquiv_upperUnitriangularSubgroup (p := p) P with ⟨eP⟩
  rcases groupAlgebra_equiv_of_mulEquiv (k := ZMod p) eP with ⟨eAlgP⟩
  rcases nonabelian_zmod_semidirectProduct_mulEquiv_standard_action
      (p := p) (φ := φ) hφ with ⟨eStd⟩
  rcases groupAlgebra_equiv_of_mulEquiv (k := ZMod p) eStd with ⟨eAlgStd⟩
  -- Freeze both groups to LinearRepresentations_Serre_1977's canonical models, compare the distinguished modular layer
  -- there, and pull the contradiction back through the algebra transports.
  intro hIso
  rcases hIso with ⟨e⟩
  exact canonical_models_modP_groupAlgebras_not_isomorphic (p := p) hp2
    ⟨eAlgP.symm.trans e |>.trans eAlgStd⟩

end

end Exercise137

section Exercise138

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

open Subgroup.CyclicConjClasses

-- Proof sketch: Theorem `13-13.1-6` gives that the permutation characters `ℓ_C^G` induced from
-- cyclic subgroups span `ℚ⊗R[ℚ](G)`. Conjugate representatives yield the same character, so the
-- chosen family still spans. A direct maximal-support argument on subgroup cardinalities proves
-- linear independence, and `Module.Basis.mk` then packages the basis.
/-- Exercise 13-13.1-17 (6): if `C₁, …, C_d` represent the conjugacy classes of cyclic subgroups
of `G`, then the induced trivial rational characters `ℓ_{C_i}^G` form a basis of `ℚ ⊗R[ℚ](G)`. -/
theorem cyclicSubgroup_representative_induced_trivial_characters_form_basis
    (d : ℕ) (C : Fin d → Subgroup G)
    (hC_cyclic : ∀ i, IsCyclic (C i))
    (hC_pairwise :
      Pairwise fun i j : Fin d ↦
        ¬ (C i).IsConj (C j))
    (hC_surj :
      ∀ H : Subgroup G, IsCyclic H →
        ∃ i : Fin d, (C i).IsConj H) :
    ∃ b : Module.Basis (Fin d) ℚ (ℚ ⊗R[ℚ](G)),
      ∀ i, (b i : G → ℚ) = (ℓ_{C i}^G : G → ℚ) := by
  classical
  let η : Fin d → ℚ ⊗R[ℚ](G) := representativeCyclicPermutationCharacter (G := G) C
  refine ⟨Module.Basis.mk (v := η) ?_ ?_, ?_⟩
  · -- The representative-family characters are independent by the maximal-support argument above.
    simpa [η] using
      linearIndependent_representative_cyclic_permutation_characters
        (G := G) d C hC_cyclic hC_pairwise
  · -- The same family spans because every cyclic subgroup is conjugate to one chosen
    -- representative.
    simpa [η] using
      top_le_span_representative_cyclic_permutation_characters
        (G := G) d C hC_cyclic hC_surj
  · intro i
    -- `Module.Basis.mk` evaluates to the generating family.
    simp [η, representativeCyclicPermutationCharacter]

end Exercise138
