import Mathlib
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped Representation
open scoped MonoidalCategory

namespace Representation

/- Remark 16-16.1-9 (1) is a proof note rather than a new owner-level construction. The chapter's
canonical declaration for the conclusion is `Representation.cartanHom_injective`. Keeping a
separate local theorem with only `c = d ∘ e` and injectivity of `e` would be mathematically
incorrect, since the standard `cde` argument also uses the large-field hypotheses entering the
decomposition map. -/
recall cartanHom_injective

section

variable {p : ℕ}
variable {G : Type u}
variable [Fact p.Prime]

end

section

variable {p : ℕ}
variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

local notation "c" => cartanHom k G

/-- Helper for Remark 16-16.1-9: a `p ^ n`-section of the Cartan homomorphism sends every target
element to a preimage of its `p ^ n`-multiple. -/
private theorem cartan_p_power_range_of_section
    (n : ℕ)
    (c' : R₀[k](G) →+ P₀[k](G))
    (hc' : (c).comp c' = (p ^ n : ℕ) • AddMonoidHom.id _) :
    ∀ y : R₀[k](G), (p ^ n) • y ∈ (c).range := by
  intro y
  -- Evaluate the factorization identity at `y`.
  refine ⟨c' y, ?_⟩
  simpa using DFunLike.congr_fun hc' y

-- Proof sketch: because `R_k(G)` is a free abelian group, the statement that every multiple
-- `(p ^ n) • y` lies in `(cartanHom k G).range` extends from generators to an additive
-- factorization `c'`; conversely, evaluating such a factorization at `y` puts `(p ^ n) • y`
-- back in the Cartan range.
/-- The bridge used in Remark 16-16.1-9 (2): multiplication by `p ^ n` on `R_k(G)` lands in the
range of the Cartan homomorphism `c : P_k(G) → R_k(G)` if and only if it factors through `c` via
an additive homomorphism `c' : R_k(G) → P_k(G)` with `c ∘ c' = p ^ n`. -/
theorem cartanHom_p_power_surjective_iff_exists_p_power_section
    (n : ℕ) :
    (∀ y : R₀[k](G), (p ^ n) • y ∈ (c).range) ↔
      ∃ c' : R₀[k](G) →+ P₀[k](G),
        (c).comp c' = (p ^ n : ℕ) • AddMonoidHom.id _ := by
  constructor
  · intro hsurj
    classical
    let c'fun : R₀[k](G) → P₀[k](G) := fun y ↦ Classical.choose (hsurj y)
    have hc'fun : ∀ y : R₀[k](G), c (c'fun y) = (p ^ n) • y := by
      intro y
      exact Classical.choose_spec (hsurj y)
    let c' : R₀[k](G) →+ P₀[k](G) :=
      { toFun := c'fun
        map_zero' := by
          apply cartanHom_injective
          rw [hc'fun]
          simp
        map_add' := by
          intro y z
          apply cartanHom_injective
          change c (c'fun (y + z)) = c (c'fun y + c'fun z)
          rw [map_add, hc'fun, hc'fun, hc'fun]
          simp }
    refine ⟨c', ?_⟩
    refine AddMonoidHom.ext fun y ↦ ?_
    exact hc'fun y
  · rintro ⟨c', hc'⟩
    exact cartan_p_power_range_of_section n c' hc'

end

section

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p]
variable {G : Type u} [Group G]
variable [Fact p.Prime]

/-- Remark 16-16.1-9 (2): under the hypotheses of Theorem `16-16.1-5`, multiplication by `p ^ n`
on `R_k(G)` factors through the Cartan homomorphism. -/
theorem exists_p_power_section_of_card_eq
    (n m : ℕ) (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m) :
    by
      letI : Finite G := finite_of_card_eq_mul_of_coprime hcard hm
      exact ∃ c' : R₀[k](G) →+ P₀[k](G),
        (cartanHom k G).comp c' = (p ^ n : ℕ) • AddMonoidHom.id _ := by
  letI : Finite G := finite_of_card_eq_mul_of_coprime hcard hm
  exact (cartanHom_p_power_surjective_iff_exists_p_power_section n).1
    (cartanHom_surjective_on_p_part_multiples n m hcard hm)

end

section

variable {p : ℕ}
variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

local notation "c" => cartanHom k G

-- Proof sketch: evaluate `c ∘ c' = p^n` at `c x`; Corollary `16-16.1-6` makes `c` injective, so
-- cancelling `c` yields `c' (c x) = (p ^ n) • x` for every `x : P_k(G)`.
/-- Under Corollary 16-16.1-6, any `p ^ n`-section of the Cartan homomorphism acts on
`P_k(G)` as multiplication by `p ^ n`. -/
theorem p_power_section_comp_cartanHom_eq
    (n : ℕ)
    (c' : R₀[k](G) →+ P₀[k](G))
    (hc' : (c).comp c' = (p ^ n : ℕ) • AddMonoidHom.id _) :
    c'.comp (c) = (p ^ n : ℕ) • AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun x ↦ ?_
  apply cartanHom_injective
  simpa using DFunLike.congr_fun hc' ((c) x)

end

section

variable {p : ℕ}

/-- Helper for Remark 16-16.1-9: on `R₀[k](G)`, the quotient-owner `nsmul` from the Grothendieck
presentation agrees with the local `Nat.smul` coming from the ring owner. -/
private theorem finiteRepGrothendieck_nsmul_owner_normalization
    {k : Type u} [Field k]
    {G : Type u} [Group G]
    (N : ℕ) (x : R₀[k](G)) :
    (@nsmulAddMonoidHom (R₀[k](G))
      (QuotientAddGroup.Quotient.addCommGroup
        (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      N) x =
      (N : ℕ) • x := by
  have hmul :
      (@nsmulAddMonoidHom (R₀[k](G))
        (QuotientAddGroup.Quotient.addCommGroup
          (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        N) x =
        (N : R₀[k](G)) * x := by
    induction N with
    | zero =>
        simp [nsmulAddMonoidHom]
    | succ N ih =>
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        simpa [nsmulAddMonoidHom, succ_nsmul, add_comm, add_left_comm, add_assoc] using
          congrArg (fun z ↦ x + z) ih
  exact hmul.trans (nsmul_eq_mul N x).symm

/-- Helper for Remark 16-16.1-9: the concrete cyclic group `Multiplicative (ZMod (p ^ n))` is
itself a Sylow `p`-subgroup, so one can package a Sylow whose order is exactly `p ^ n`. -/
private theorem cyclic_p_group_has_sylow_of_card
    [Fact p.Prime] (n : ℕ) :
    ∃ P : Sylow p (Multiplicative (ZMod (p ^ n))),
      Nat.card (P : Subgroup (Multiplicative (ZMod (p ^ n)))) = p ^ n := by
  have htop_card : Nat.card (⊤ : Subgroup (Multiplicative (ZMod (p ^ n)))) = p ^ n := by
    -- The source example is the cyclic group of order exactly `p ^ n`.
    rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
    exact ZMod.card (p ^ n)
  have htop : IsPGroup p (⊤ : Subgroup (Multiplicative (ZMod (p ^ n)))) :=
    IsPGroup.of_card htop_card
  let P : Sylow p (Multiplicative (ZMod (p ^ n))) := htop.toSylow (by
    simpa using (Nat.Prime.not_dvd_one (Fact.out : Nat.Prime p)))
  refine ⟨P, ?_⟩
  -- The chosen Sylow is the whole cyclic `p`-group, so its order is still `p ^ n`.
  change Nat.card (⊤ : Subgroup (Multiplicative (ZMod (p ^ n)))) = p ^ n
  exact htop_card

/-- Helper for Remark 16-16.1-9: Exercise `16-16.1-12` on the concrete cyclic `p`-group
`Multiplicative (ZMod (p ^ n))` gives the obstruction at exponent `n - 1` on the same universe
surface as the current file. -/
private theorem cyclic_p_group_trivial_class_nonrange
    [Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (P : Sylow p (Multiplicative (ZMod (p ^ n))))
    (hcard : Nat.card (P : Subgroup (Multiplicative (ZMod (p ^ n)))) = p ^ n) :
    let y : R₀[ZMod p](Multiplicative (ZMod (p ^ n))) :=
      [𝟙_ (FDRep (ZMod p) (Multiplicative (ZMod (p ^ n))))]₀
    (Int.ofNat (p ^ (n - 1))) • y ∉
      (cartanHom (ZMod p) (Multiplicative (ZMod (p ^ n)))).range := by
  -- The exercise already gives the obstruction on this concrete cyclic `p`-group.
  dsimp
  exact
    trivial_class_p_pow_pred_not_in_cartan_range
      (k := ZMod p) (G := Multiplicative (ZMod (p ^ n))) P n hn hcard

/-- Helper for Remark 16-16.1-9: on the concrete cyclic `p`-group, the exercise obstruction is
unchanged when one rewrites the scalar from `Int.ofNat`-smul to the local `Nat.smul` surface. -/
private theorem trivial_class_nonrange_nat_smul
    [Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (P : Sylow p (Multiplicative (ZMod (p ^ n))))
    (hcard : Nat.card (P : Subgroup (Multiplicative (ZMod (p ^ n)))) = p ^ n) :
    let y : R₀[ZMod p](Multiplicative (ZMod (p ^ n))) :=
      [𝟙_ (FDRep (ZMod p) (Multiplicative (ZMod (p ^ n))))]₀
    (p ^ (n - 1)) • y ∉
      (cartanHom (ZMod p) (Multiplicative (ZMod (p ^ n)))).range := by
  dsimp
  intro hmem
  let y : R₀[ZMod p](Multiplicative (ZMod (p ^ n))) :=
    [𝟙_ (FDRep (ZMod p) (Multiplicative (ZMod (p ^ n))))]₀
  have hmem' :
      (Int.ofNat (p ^ (n - 1))) • y ∈
        (cartanHom (ZMod p) (Multiplicative (ZMod (p ^ n)))).range := by
    -- Rewrite the exercise theorem's quotient-owner scalar to the local `Nat.smul` surface.
    have hy_int :
        (Int.ofNat (p ^ (n - 1))) • y =
          (p ^ (n - 1) : ℕ) * y := by
      have hy_nat :
          (Int.ofNat (p ^ (n - 1))) • y =
            (p ^ (n - 1) : ℕ) • y := by
        simpa [Int.ofNat_eq_natCast, natCast_zsmul] using
          (finiteRepGrothendieck_nsmul_owner_normalization
            (k := ZMod p) (G := Multiplicative (ZMod (p ^ n))) (N := p ^ (n - 1)) y)
      calc
        (Int.ofNat (p ^ (n - 1))) • y = (p ^ (n - 1) : ℕ) • y := hy_nat
        _ = (p ^ (n - 1) : ℕ) * y := by
              exact nsmul_eq_mul (p ^ (n - 1)) y
    rcases hmem with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    calc
      (cartanHom (ZMod p) (Multiplicative (ZMod (p ^ n)))) u =
          (p ^ (n - 1) : ℕ) * y := by
            simpa [y] using hu
      _ = (Int.ofNat (p ^ (n - 1))) • y := hy_int.symm
  exact
    (trivial_class_p_pow_pred_not_in_cartan_range
      (k := ZMod p) (G := Multiplicative (ZMod (p ^ n))) P n hn hcard) hmem'

/-- Helper for Remark 16-16.1-9: Exercise `16-16.1-12` on the concrete cyclic `p`-group
`Multiplicative (ZMod (p ^ n))` gives the obstruction at exponent `n - 1` on the same universe
surface as the current file. -/
private theorem cyclic_p_group_optimality_witness
    [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    ∃ y : R₀[ZMod p](Multiplicative (ZMod (p ^ n))),
      (p ^ (n - 1)) • y ∉
        (cartanHom (ZMod p) (Multiplicative (ZMod (p ^ n)))).range := by
  obtain ⟨P, hcard⟩ := cyclic_p_group_has_sylow_of_card (p := p) n
  refine ⟨[𝟙_ (FDRep (ZMod p) (Multiplicative (ZMod (p ^ n))))]₀, ?_⟩
  -- The trivial class from Exercise `16-16.1-12` is already the required witness once the scalar
  -- is rewritten on the local `Nat.smul` surface.
  simpa using trivial_class_nonrange_nat_smul (p := p) n hn P hcard

/-- Helper for Remark 16-16.1-9: a counterexample for exponent `n - 1` yields one for every
smaller exponent after rescaling the witness class. -/
private theorem smaller_exponent_nonrange_of_pred_nonrange
    {k : Type u} [Field k]
    {G : Type u} [Group G] [Finite G]
    {n n' : ℕ}
    (hn' : n' < n)
    (t : R₀[k](G))
    (ht : (p ^ (n - 1)) • t ∉ (cartanHom k G).range) :
    let y : R₀[k](G) := (p ^ ((n - 1) - n')) • t
    (p ^ n') • y ∉ (cartanHom k G).range := by
  dsimp
  intro hy
  apply ht
  rcases hy with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hle : n' ≤ n - 1 := Nat.le_pred_of_lt hn'
  have hpow : p ^ n' * p ^ ((n - 1) - n') = p ^ (n - 1) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hle]
  -- Reassociate the two scalar factors into the original `p ^ (n - 1)` multiple.
  calc
    (cartanHom k G) x = (p ^ n') • ((p ^ ((n - 1) - n')) • t) := hx
    _ = (p ^ (n - 1)) • t := by
          rw [smul_smul, hpow]

-- Proof sketch: Exercise `16.3` supplies, for each smaller exponent `n' < n`, an example whose
-- group order has `p`-part `p ^ n` together with a class `y ∈ R_k(G)` such that `(p ^ n') • y`
-- does not lie in `(cartanHom k G).range`.
/-- Remark 16-16.1-9 (3): the exponent `n` in Theorem `16-16.1-5` is optimal: for every smaller
exponent `n' < n`, there is an example with `|G| = p^n m` and `(p, m) = 1` for which the theorem
fails with `p ^ n'` in place of `p ^ n`. -/
theorem cartanHom_p_part_exponent_best_possible
    (hp : Nat.Prime p) (n n' : ℕ) (hn' : n' < n) :
    by
      exact ∃ (k : Type) (_ : Field k) (_ : CharP k p)
        (G : Type) (_ : Group G) (m : ℕ)
        (hcard : Nat.card G = p ^ n * m) (hm : Nat.Coprime p m),
        by
          letI : Fact p.Prime := ⟨hp⟩
          letI : Finite G := finite_of_card_eq_mul_of_coprime hcard hm
          exact ∃ y : R₀[k](G), (p ^ n') • y ∉ (cartanHom k G).range := by
  letI : Fact p.Prime := ⟨hp⟩
  have hn : 0 < n := by
    exact Nat.pos_of_ne_zero (fun h0 => Nat.not_lt_zero _ (h0 ▸ hn'))
  obtain ⟨t, ht⟩ := cyclic_p_group_optimality_witness (p := p) n hn
  refine ⟨ZMod p, inferInstance, inferInstance, Multiplicative (ZMod (p ^ n)), inferInstance,
    1, ?_, Nat.coprime_one_right p, ?_⟩
  · -- The source example is the cyclic `p`-group of order exactly `p ^ n`.
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Nat.mul_one]
    exact ZMod.card (p ^ n)
  · refine ⟨(p ^ ((n - 1) - n')) • t, ?_⟩
    -- Route correction: descend from the sharp exponent `n - 1` witness using the closed
    -- rescaling lemma, instead of reintroducing a transported `ULift` witness.
    simpa using
      (smaller_exponent_nonrange_of_pred_nonrange
        (p := p) (k := ZMod p) (G := Multiplicative (ZMod (p ^ n)))
        (n := n) (n' := n') hn' t ht)

end

end Representation
