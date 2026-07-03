import Mathlib
import Serre.Chap10.Definition_10_10_1_2
import Serre.Chap11.Proposition_11_11_4_1
import Serre.Chap11.Theorem_11_11_2_2
import Serre.Chap11.Theorem_11_11_3_2

-- Declarations for this item will be appended below by the statement pipeline.

-- Primary domain: the prime spectrum of Serre's tensor character ring `A ⊗R(G)`, organized by
-- the canonical prime families `P0` and `Pm` and by the passage from an ordinary conjugacy class
-- to its `p`-regular component.
-- Sampled owner declarations in this domain:
-- * `pRegularComponent` and `pRegularComponent_conj` from Chapter `10`;
-- * `PRegularConjClass.ofSubtype`, `tensorCharacterRingZeroPrimeIdeal`, and
--   `tensorCharacterRingRegularPrime` from Proposition `11-11.4-1`;
-- * `tensor_character_ring_prime_ideal_classification` from Proposition `11-11.4-1`;
-- * `IsConnected.iUnion_of_reflTransGen` from mathlib's connectedness API.
-- Best owner abstraction: the Chapter `11` prime-spectrum owners `P0` and `Pm`, together with the
-- canonical connected-union theorem on families indexed by `ConjClasses G`.
-- Primitive data: the owners `P0`, `Pm`, `PRegularConjClass`, and the `p`-regular component map on
-- elements.
-- Derived API: the line `tensorCharacterRingPrimeSpectrumLine A c`, its intersection relation,
-- the auxiliary line-criterion theorem, and the main connectedness theorem.
-- Layer triage:
-- * source-facing: the line attached to a conjugacy class in `Spec (A ⊗ R(G))`;
-- * core/canonical: the prime owners `P0`, `Pm`, and `IsConnected.iUnion_of_reflTransGen`;
-- * bridge/view: `pRegularConjClassOfConjClass`, sending `c : ConjClasses G` to its
--   `p`-regular component in `PRegularConjClass G p`.

universe v

noncomputable section

open Representation
open scoped Representation

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]

local notation "SpecARG" =>
  PrimeSpectrum (A ⊗R(G))
local notation "P0" => tensorCharacterRingZeroPrimeIdeal
local notation "Pm" => fun {p : Nat.Primes}
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) ↦
      tensorCharacterRingRegularPrime (A := A) (G := G) p M

local instance (p : Nat.Primes) : Fact ((p : ℕ).Prime) := ⟨p.2⟩
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- The `p`-regular conjugacy class represented by the `p'`-component of an element. -/
private def pRegularConjClassOfElement (p : Nat.Primes) (x : G) : PRegularConjClass G p :=
  PRegularConjClass.ofSubtype p ⟨pRegularComponent p x, isPRegular_pRegularComponent x⟩

-- Proof sketch: if `x` and `y` are conjugate, then `pRegularComponent_conj` shows that their
-- `p'`-components are conjugate, so `PRegularConjClass.ofSubtype` yields the same owner element.
/-- Conjugate representatives define the same `p`-regular conjugacy class after passing to
`p'`-components. -/
private theorem pRegularConjClassOfElement_eq_of_isConj
    (p : Nat.Primes) {x y : G} (hxy : IsConj x y) :
    pRegularConjClassOfElement p x =
      pRegularConjClassOfElement p y := by
  -- Equality in the owner reduces to equality of the underlying conjugacy classes.
  apply Subtype.ext
  -- The `p'`-component construction is conjugation-equivariant.
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  rcases isConj_iff.mp hxy with ⟨t, rfl⟩
  exact isConj_iff.mpr ⟨t, by simp [pRegularComponent_conj]⟩

/-- The canonical `p`-regular conjugacy class attached to an ordinary conjugacy class by taking the
`p'`-component of any representative. -/
private def pRegularConjClassOfConjClass (p : Nat.Primes) :
    ConjClasses G → PRegularConjClass G p :=
  Quotient.lift
    (pRegularConjClassOfElement p)
    (fun _ _ hxy ↦ pRegularConjClassOfElement_eq_of_isConj p hxy)

-- Proof sketch: choose a representative of the `p`-regular class and use that a `p`-regular
-- element is equal to its own `p'`-component.
/-- The canonical `p`-regular conjugacy class attached to a `p`-regular conjugacy class is
itself. -/
@[simp] private theorem pRegularConjClassOfConjClass_coe
    (p : Nat.Primes) (c : PRegularConjClass G p) :
    pRegularConjClassOfConjClass p (c : ConjClasses G) = c := by
  -- Choose a representative of the underlying conjugacy class.
  apply Subtype.ext
  obtain ⟨x, hx⟩ := ConjClasses.mk_surjective (c : ConjClasses G)
  have hxreg : IsPRegular p x :=
    c.2 x (ConjClasses.mem_carrier_iff_mk_eq.mpr hx)
  -- For a `p`-regular representative, the `p'`-component is the element itself.
  rw [show (c : ConjClasses G) = ConjClasses.mk x by simp [hx]]
  change (pRegularConjClassOfElement p x : ConjClasses G) = ConjClasses.mk x
  simp [pRegularConjClassOfElement, pRegularComponent_eq_self_of_isPRegular hxreg]

/-- Helper for Proposition 11-11.4-4: any element lying in the carrier of the canonical
`p`-regular component of `c` determines the same `p`-regular conjugacy class. -/
private theorem pRegularConjClassOfConjClass_eq_of_mem_carrier
    (p : Nat.Primes) {c : ConjClasses G} {x : G}
    (hx : x ∈ (pRegularConjClassOfConjClass p c : ConjClasses G).carrier) :
    pRegularConjClassOfConjClass p (ConjClasses.mk x) =
      pRegularConjClassOfConjClass p c := by
  -- Passing back to the `p`-regular owner only depends on the conjugacy class represented by `x`.
  calc
    pRegularConjClassOfConjClass p (ConjClasses.mk x) =
        pRegularConjClassOfConjClass p
          ((pRegularConjClassOfConjClass p c : PRegularConjClass G p) : ConjClasses G) := by
            rw [ConjClasses.mem_carrier_iff_mk_eq.mp hx]
    _ = pRegularConjClassOfConjClass p c := by
          simpa using
            pRegularConjClassOfConjClass_coe p (pRegularConjClassOfConjClass p c)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsIntegralClosure A ℤ ℂ]

variable (A)

/-- The canonical line in `Spec (A ⊗ R(G))` attached to a conjugacy class `c`: it contains the
zero-residual prime `P₀,c` and, for each nonzero maximal ideal `M` of residual characteristic `p`,
the regular prime indexed by the `p`-regular component of `c` in the arithmetic setting where
`Pm` is defined. -/
def tensorCharacterRingPrimeSpectrumLine (c : ConjClasses G) : Set SpecARG :=
  ({P0 A c} : Set SpecARG) ∪ ⋃ (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p),
    ({Pm M (pRegularConjClassOfConjClass p c)} : Set SpecARG)

/-- Two canonical lines in `Spec (A ⊗ R(G))` meet if their intersection is nonempty. -/
def tensorCharacterRingPrimeSpectrumLineIntersects
    (c₁ c₂ : ConjClasses G) : Prop :=
  (tensorCharacterRingPrimeSpectrumLine A c₁ ∩
    tensorCharacterRingPrimeSpectrumLine A c₂).Nonempty

variable {A}

/-- Helper for Proposition 11-11.4-4: every nonzero prime of the arithmetic coefficient ring is
one of the residual-characteristic maximal ideals indexing Serre's regular branch. -/
private theorem nonzero_primeSpectrum_eq_residual_maximal_local
    (q : PrimeSpectrum A) (hq : q.asIdeal ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
      M.1.asIdeal = q.asIdeal := by
  -- A nonzero prime becomes maximal once every nonzero quotient of `A` is finite.
  letI : q.asIdeal.IsMaximal :=
    Ring.HasFiniteQuotients.maximalOfPrime hq
  have hfiniteQuot : Finite (A ⧸ q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient hq
  letI : Finite (A ⧸ q.asIdeal) := hfiniteQuot
  -- The residue field is finite, so its characteristic is an actual prime number.
  have hfiniteResidue : Finite q.asIdeal.ResidueField := by
    exact Finite.of_surjective
      (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal).surjective
  letI : Finite q.asIdeal.ResidueField := hfiniteResidue
  let p : Nat.Primes :=
    ⟨ringChar q.asIdeal.ResidueField, CharP.prime_ringChar q.asIdeal.ResidueField⟩
  let M : NonzeroResidualCharacteristicMaximalIdeal A p :=
    ⟨⟨q.asIdeal, inferInstance⟩, hq, by
      simpa [p] using
        (inferInstance : CharP q.asIdeal.ResidueField (ringChar q.asIdeal.ResidueField))⟩
  -- The packaged maximal ideal is definitionally the original prime ideal.
  exact ⟨p, M, rfl⟩

/-- Helper for Proposition 11-11.4-4: every rational prime occurs as the residual characteristic
of some nonzero maximal ideal of `A`. -/
private theorem exists_residualCharacteristicMaximalIdeal_of_prime
    (p : Nat.Primes) :
    Nonempty (NonzeroResidualCharacteristicMaximalIdeal A p) := by
  classical
  have hZA : Function.Injective (algebraMap ℤ A) := by
    intro m n hmn
    have hmn' := congrArg (algebraMap A ℂ) hmn
    rw [← IsScalarTower.algebraMap_apply ℤ A ℂ m,
      ← IsScalarTower.algebraMap_apply ℤ A ℂ n] at hmn'
    exact Int.cast_injective hmn'
  letI : Module.IsTorsionFree ℤ A :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 hZA
  haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ ℂ
  let P : Ideal ℤ := Ideal.span ({((p : ℕ) : ℤ)} : Set ℤ)
  have hPprime : P.IsPrime := by
    dsimp [P]
    infer_instance
  let Q : P.primesOver A := Classical.choice (Ideal.nonempty_primesOver (R := ℤ) (S := A) P)
  have hQmax : (Q : Ideal A).IsMaximal :=
    Ideal.isMaximal_of_mem_primesOver (p := P) Q.2
  have hp_memP : (((p : ℕ) : ℤ)) ∈ P := by
    exact Ideal.subset_span (by simp)
  have hp_memQ : (p : A) ∈ (Q : Ideal A) := by
    simpa using (Ideal.mem_of_liesOver (P := (Q : Ideal A)) P (((p : ℕ) : ℤ))).mp hp_memP
  have hQne : (Q : Ideal A) ≠ ⊥ := by
    intro hQbot
    have hpzeroA : (p : A) = 0 := by
      simpa [hQbot] using hp_memQ
    have hpzeroZ : (((p : ℕ) : ℤ)) = 0 := by
      apply hZA
      simpa using hpzeroA
    have hpzeroNat : (p : ℕ) = 0 := by
      exact_mod_cast hpzeroZ
    exact Nat.Prime.ne_zero p.2 hpzeroNat
  have hp0 : (p : A ⧸ (Q : Ideal A)) = 0 := by
    change Ideal.Quotient.mk (Q : Ideal A) (p : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp_memQ
  letI : CharP (A ⧸ (Q : Ideal A)) p := by
    exact
      ringChar.of_eq
        (CharP.ringChar_of_prime_eq_zero
          (R := A ⧸ (Q : Ideal A)) (Fact.out : Nat.Prime (p : ℕ)) hp0)
  letI : CharP (Q : Ideal A).ResidueField p :=
    charP_of_injective_algebraMap
      (Ideal.injective_algebraMap_quotient_residueField (Q : Ideal A)) p
  -- The chosen prime over `(p)` gives the required residual-characteristic maximal ideal.
  let M : NonzeroResidualCharacteristicMaximalIdeal A p :=
    ⟨⟨(Q : Ideal A), hQmax⟩, hQne, inferInstance⟩
  exact ⟨M⟩

-- Proof sketch: `P₀,c` belongs to the first singleton appearing in the defining union for the
-- line attached to `c`.
/-- The zero-residual prime `P₀,c` lies on the canonical line indexed by `c`. -/
@[simp] private theorem mem_tensorCharacterRingPrimeSpectrumLine_zero
    (c : ConjClasses G) :
    P0 A c ∈ tensorCharacterRingPrimeSpectrumLine A c := by
  -- The defining union contains `P₀,c` as its distinguished singleton summand.
  left
  simp

-- Proof sketch: `P_{M,c}` appears as the singleton indexed by `(p, M)` in the double union
-- defining the line attached to the ordinary conjugacy class `c`.
/-- Each regular prime indexed by the `p`-regular component of `c` lies on the canonical line
attached to `c`. -/
@[simp] private theorem mem_tensorCharacterRingPrimeSpectrumLine_regular
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    Pm M (pRegularConjClassOfConjClass p c) ∈ tensorCharacterRingPrimeSpectrumLine A c := by
  -- The defining double union contains the regular prime indexed by `(p, M)`.
  right
  refine Set.mem_iUnion.mpr ⟨p, ?_⟩
  refine Set.mem_iUnion.mpr ⟨M, ?_⟩
  simp

-- Proof sketch: Proposition `11-11.4-1` classifies every prime of `A ⊗ R(G)` as either a
-- zero-residual prime `P₀,c` or a regular prime `P_{M,c}`, and the previous two lemmas place
-- each such prime on the corresponding line.
/-- The canonical lines indexed by ordinary conjugacy classes cover the whole prime spectrum. -/
private theorem iUnion_tensorCharacterRingPrimeSpectrumLine_eq_univ :
    (⋃ c : ConjClasses G, tensorCharacterRingPrimeSpectrumLine A c) =
      (Set.univ : Set SpecARG) := by
  ext P
  constructor
  · intro _
    simp
  · intro _
    -- Classify the prime and place it on the corresponding canonical line.
    rcases tensor_character_ring_prime_ideal_classification P with hP0 | hPm
    · rcases hP0 with ⟨c, rfl⟩
      exact Set.mem_iUnion.mpr ⟨c, mem_tensorCharacterRingPrimeSpectrumLine_zero (A := A) c⟩
    · rcases hPm with ⟨p, M, c, rfl⟩
      refine Set.mem_iUnion.mpr ⟨(c : ConjClasses G), ?_⟩
      simpa [pRegularConjClassOfConjClass_coe] using
        mem_tensorCharacterRingPrimeSpectrumLine_regular (A := A) p M (c : ConjClasses G)

-- Proof sketch: Proposition `11-11.4-1` gives the canonical cover of `Spec(A ⊗ R(G))` by the
-- lines attached to ordinary conjugacy classes. If each such line is connected and every line can
-- be joined to the unit-class line through a finite chain of nonempty intersections, then the
-- standard connected-union theorem applies to this canonical line decomposition.
/-- Auxiliary connectedness criterion: if every canonical line in the prime spectrum of Serre's
tensor character ring `A ⊗ R(G)` is connected and every such line is linked to the unit-class line
by a finite chain of nonempty intersections, then `Spec (A ⊗ R(G))` is connected. -/
theorem tensorCharacterRingPrimeSpectrum_connected_of_lineCriterion
    (hconnected :
      ∀ c : ConjClasses G, IsConnected (tensorCharacterRingPrimeSpectrumLine A c))
    (hchain :
      ∀ c : ConjClasses G,
        Relation.ReflTransGen (tensorCharacterRingPrimeSpectrumLineIntersects A) c
          (1 : ConjClasses G)) :
    ConnectedSpace SpecARG := by
  letI : Nonempty (ConjClasses G) := ⟨1⟩
  have hsymm :
      Symmetric
        (tensorCharacterRingPrimeSpectrumLineIntersects A : ConjClasses G → ConjClasses G → Prop) :=
    by
    intro c₁ c₂ h
    simpa [tensorCharacterRingPrimeSpectrumLineIntersects, Set.inter_comm] using h
  have hlines :
      IsConnected (⋃ c : ConjClasses G, tensorCharacterRingPrimeSpectrumLine A c) :=
    IsConnected.iUnion_of_reflTransGen hconnected fun c₁ c₂ ↦
      (hchain c₁).trans <| (Relation.ReflTransGen.symmetric hsymm) (hchain c₂)
  have hcover :
      (⋃ c : ConjClasses G, tensorCharacterRingPrimeSpectrumLine A c) = Set.univ :=
    iUnion_tensorCharacterRingPrimeSpectrumLine_eq_univ
  rw [connectedSpace_iff_univ]
  exact hcover ▸ hlines

/-- Helper for Proposition 11-11.4-4: if two conjugacy classes have the same `p`-regular
component, then the corresponding canonical lines meet in the regular prime indexed by any fixed
maximal ideal `M` of residual characteristic `p`. -/
private theorem tensorCharacterRingPrimeSpectrumLineIntersects_of_pregular_eq
    {p : Nat.Primes} (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {c₁ c₂ : ConjClasses G}
    (hreg :
      pRegularConjClassOfConjClass p c₁ =
        pRegularConjClassOfConjClass p c₂) :
    tensorCharacterRingPrimeSpectrumLineIntersects A c₁ c₂ := by
  -- The shared regular prime sits in both singleton summands of the two defining unions.
  refine ⟨Pm M (pRegularConjClassOfConjClass p c₁), ?_, ?_⟩
  · exact mem_tensorCharacterRingPrimeSpectrumLine_regular (A := A) p M c₁
  · simpa [hreg] using mem_tensorCharacterRingPrimeSpectrumLine_regular (A := A) p M c₂

/-- Helper for Proposition 11-11.4-4: stripping one prime-power component from the order of an
element strictly lowers its order unless the element is already the identity. -/
private theorem orderOf_pRegularComponent_lt_of_prime_dvd_orderOf
    (p : Nat.Primes) (x : G) (hpdvd : (p : ℕ) ∣ orderOf x) :
    orderOf (pRegularComponent p x) < orderOf x := by
  have hdecomp :=
    p_component_decomposition_exists (p := (p : ℕ)) x (isOfFinOrder_of_finite x)
  have hdvd :
      orderOf (pRegularComponent p x) ∣ orderOf x := by
    exact orderOf_dvd_of_mem_zpowers hdecomp.right_mem_zpowers
  have hpnot :
      ¬ (p : ℕ) ∣ orderOf (pRegularComponent p x) := by
    exact
      (isPRegular_iff_not_dvd_orderOf (p := (p : ℕ)) (pRegularComponent p x)).mp
        (isPRegular_pRegularComponent x)
  have hne :
      orderOf (pRegularComponent p x) ≠ orderOf x := by
    intro hEq
    exact hpnot <| hEq.symm ▸ hpdvd
  have hpos : 0 < orderOf x := orderOf_pos x
  have hle : orderOf (pRegularComponent p x) ≤ orderOf x :=
    Nat.le_of_dvd hpos hdvd
  exact lt_of_le_of_ne hle hne

/-- Helper for Proposition 11-11.4-4: every canonical line can be joined to the unit-class line
by repeatedly replacing a conjugacy class with a suitable `p`-regular component. -/
private theorem tensorCharacterRingPrimeSpectrumLine_chain_to_one
    (c : ConjClasses G) :
    Relation.ReflTransGen (tensorCharacterRingPrimeSpectrumLineIntersects A) c
      (1 : ConjClasses G) := by
  classical
  obtain ⟨x, hx⟩ := ConjClasses.mk_surjective c
  have hchain :
      ∀ n : ℕ, ∀ y : G, orderOf y = n →
        Relation.ReflTransGen (tensorCharacterRingPrimeSpectrumLineIntersects A)
          (ConjClasses.mk y) (1 : ConjClasses G) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro m ihm y hy
    by_cases hm1 : m = 1
    · -- Order `1` means the representative is the identity, so the chain is trivial.
      have hyone : y = 1 := orderOf_eq_one_iff.mp (hy.trans hm1)
      simpa [hyone] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen (tensorCharacterRingPrimeSpectrumLineIntersects A)
            (1 : ConjClasses G) (1 : ConjClasses G))
    · -- Route correction: peel off one prime divisor of the order, then append the induction
      -- chain from the resulting `p`-regular component.
      have hmpos : 0 < m := hy.symm ▸ orderOf_pos y
      have hmne0 : m ≠ 0 := Nat.ne_of_gt hmpos
      obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hm1
      let pp : Nat.Primes := ⟨p, hpprime⟩
      let M : NonzeroResidualCharacteristicMaximalIdeal A pp :=
        Classical.choice (exists_residualCharacteristicMaximalIdeal_of_prime (A := A) pp)
      let y' : G := pRegularComponent pp y
      have hreg_eq :
          pRegularConjClassOfConjClass pp (ConjClasses.mk y) =
            pRegularConjClassOfConjClass pp (ConjClasses.mk y') := by
        -- The stripped element represents exactly the `p`-regular class attached to `y`.
        have hy'mk :
            (pRegularConjClassOfElement pp y : ConjClasses G) = ConjClasses.mk y' := by
          simp [pRegularConjClassOfElement, y']
        calc
          pRegularConjClassOfConjClass pp (ConjClasses.mk y) = pRegularConjClassOfElement pp y := rfl
          _ = pRegularConjClassOfConjClass pp (ConjClasses.mk y') := by
            rw [← hy'mk]
            exact
              (pRegularConjClassOfConjClass_coe pp (pRegularConjClassOfElement pp y)).symm
      have hstep :
          tensorCharacterRingPrimeSpectrumLineIntersects A (ConjClasses.mk y)
            (ConjClasses.mk y') := by
        exact
          tensorCharacterRingPrimeSpectrumLineIntersects_of_pregular_eq
            (A := A) (M := M) hreg_eq
      have hy'lt : orderOf y' < m := by
        simpa [y', hy] using
          orderOf_pRegularComponent_lt_of_prime_dvd_orderOf
            (p := pp) y (by simpa [hy] using hpdvd)
      have hy'chain :
          Relation.ReflTransGen (tensorCharacterRingPrimeSpectrumLineIntersects A)
            (ConjClasses.mk y') (1 : ConjClasses G) :=
        ihm (orderOf y') hy'lt y' rfl
      exact Relation.ReflTransGen.head hstep hy'chain
  simpa [hx] using hchain (orderOf x) x rfl

/-- Helper for Proposition 11-11.4-4: every associated `p`-elementary subgroup attached to the
`p`-regular component of `c` contains an element of the original conjugacy class `c`. -/
private theorem associatedPElementarySubgroup_nonempty_inter_carrier
    (p : Nat.Primes) {c : ConjClasses G} {x : G}
    (hx : x ∈ (pRegularConjClassOfConjClass p c : ConjClasses G).carrier)
    (P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G))) :
    ((associatedPElementarySubgroup (p : ℕ) x P : Set G) ∩ c.carrier).Nonempty := by
  classical
  obtain ⟨y, hyc⟩ := ConjClasses.mk_surjective c
  have hxmk :
      ConjClasses.mk x = ConjClasses.mk (pRegularComponent p y) := by
    calc
      ConjClasses.mk x = (pRegularConjClassOfConjClass p c : ConjClasses G) :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx
      _ = (pRegularConjClassOfConjClass p (ConjClasses.mk y) : ConjClasses G) := by
        rw [hyc]
      _ = (pRegularConjClassOfElement p y : ConjClasses G) := rfl
      _ = ConjClasses.mk (pRegularComponent p y) := by
        simp [pRegularConjClassOfElement]
  obtain ⟨g, hg⟩ :=
    isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hxmk)
  let y' : G := g⁻¹ * y * g
  have hy'c : y' ∈ c.carrier := by
    -- Conjugating the chosen representative of `c` stays inside the same conjugacy class.
    refine ConjClasses.mem_carrier_iff_mk_eq.mpr ?_
    calc
      ConjClasses.mk y' = ConjClasses.mk y := by
        refine ConjClasses.mk_eq_mk_iff_isConj.mpr ?_
        exact isConj_iff.mpr ⟨g, by simp [y', mul_assoc]⟩
      _ = c := hyc
  have hy'reg : pRegularComponent p y' = x := by
    -- Choose the conjugate representative whose `p'`-component is exactly the fixed regular
    -- element `x`.
    calc
      pRegularComponent p y' = g⁻¹ * pRegularComponent p y * g := by
        simpa [y'] using pRegularComponent_conj (p := (p : ℕ)) y g⁻¹
      _ = x := by
        rw [← hg]
        simp [mul_assoc]
  let u : G := pUnipotentComponent p y'
  have hu_mem_centralizer : u ∈ Subgroup.centralizer ({x} : Set G) := by
    -- In the `p`-component decomposition of `y'`, the `p`-unipotent and `p'`-regular factors
    -- commute.
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [u, hy'reg] using
      (p_component_decomposition_exists (p := (p : ℕ)) y' (isOfFinOrder_of_finite y')).commute.eq
  rcases
      (p_component_decomposition_exists (p := (p : ℕ)) y' (isOfFinOrder_of_finite y')).isPElement
    with ⟨k, hk⟩
  have hu_pgroup : IsPGroup (p : ℕ) (Subgroup.zpowers u) := by
    exact IsPGroup.of_card ((Nat.card_zpowers u).trans hk)
  have hu_zpowers_le_centralizer :
      Subgroup.zpowers u ≤ Subgroup.centralizer ({x} : Set G) := by
    exact Subgroup.zpowers_le.mpr hu_mem_centralizer
  have hu_pgroup_centralizer :
      IsPGroup (p : ℕ) ((Subgroup.zpowers u).subgroupOf (Subgroup.centralizer ({x} : Set G))) := by
    exact hu_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hu_zpowers_le_centralizer).symm
  obtain ⟨Q, hQ⟩ := hu_pgroup_centralizer.exists_le_sylow
  have hu_mem_Q :
      ⟨u, hu_mem_centralizer⟩ ∈ (Q : Subgroup (Subgroup.centralizer ({x} : Set G))) := by
    apply hQ
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers u)
  have hu_mem_assoc_Q :
      u ∈ Subgroup.map (Subgroup.centralizer ({x} : Set G)).subtype
        (Q : Subgroup (Subgroup.centralizer ({x} : Set G))) := by
    exact Subgroup.mem_map.mpr ⟨⟨u, hu_mem_centralizer⟩, hu_mem_Q, rfl⟩
  have hy'_eq : y' = x * u := by
    -- Rewrite `y'` using its `p`-component decomposition, then commute the two factors.
    calc
      y' = u * pRegularComponent p y' := by
        simpa [u] using
          (p_component_decomposition_exists (p := (p : ℕ)) y' (isOfFinOrder_of_finite y')).eq_mul
      _ = x * u := by
        simpa [u, hy'reg] using
          (p_component_decomposition_exists (p := (p : ℕ)) y' (isOfFinOrder_of_finite y')).commute.eq
  have hy'_mem_assoc_Q : y' ∈ associatedPElementarySubgroup (p : ℕ) x Q := by
    -- The representative `y' = x * u` lies in the associated subgroup once the `p`-part `u`
    -- is placed inside a Sylow subgroup of the centralizer.
    rw [hy'_eq, associatedPElementarySubgroup]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers x) hu_mem_assoc_Q
  obtain ⟨z, hz⟩ :=
    associatedPElementarySubgroup_conjugate_in_centralizer (p := (p : ℕ)) x Q P
  have hz_mem :
      (z : G) * y' * (z : G)⁻¹ ∈ associatedPElementarySubgroup (p : ℕ) x P := by
    have hz_map :
        MulAut.conj (z : G) y' ∈
          Subgroup.map (MulAut.conj (z : G)).toMonoidHom
            (associatedPElementarySubgroup (p : ℕ) x Q) := by
      exact Subgroup.mem_map.mpr ⟨y', hy'_mem_assoc_Q, rfl⟩
    have hz_eq :
        Subgroup.map (MulAut.conj (z : G)).toMonoidHom
            (associatedPElementarySubgroup (p : ℕ) x Q) =
          associatedPElementarySubgroup (p : ℕ) x P := by
      simpa using hz
    have hz_mem' :
        MulAut.conj (z : G) y' ∈ associatedPElementarySubgroup (p : ℕ) x P := by
      exact hz_eq ▸ hz_map
    simpa [MulAut.conj_apply, mul_assoc] using hz_mem'
  have hz_carrier : (z : G) * y' * (z : G)⁻¹ ∈ c.carrier := by
    -- Conjugating a point of `c` stays inside `c`.
    refine ConjClasses.mem_carrier_iff_mk_eq.mpr ?_
    calc
      ConjClasses.mk ((z : G) * y' * (z : G)⁻¹) = ConjClasses.mk y' := by
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨z⁻¹, by simp [mul_assoc]⟩)
      _ = c := ConjClasses.mem_carrier_iff_mk_eq.mp hy'c
  exact ⟨(z : G) * y' * (z : G)⁻¹, hz_mem, hz_carrier⟩

/-- Helper for Proposition 11-11.4-4: if a subgroup misses the conjugacy class `c`, then it
cannot contain any associated `p`-elementary subgroup coming from the `p`-regular component of
`c`. -/
private theorem not_hasAssociatedPElementarySubgroupInClass_of_disjoint_carrier_local
    (p : Nat.Primes) (H : Subgroup G) (c : ConjClasses G)
    (hdisj : ((H : Set G) ∩ c.carrier) = ∅) :
    ¬ HasAssociatedPElementarySubgroupInClass (pRegularConjClassOfConjClass p c) H := by
  intro hAssoc
  rcases hAssoc with ⟨x, hx, P, hP⟩
  rcases associatedPElementarySubgroup_nonempty_inter_carrier
      p hx P with ⟨y, hyAssoc, hyc⟩
  have hyH : y ∈ (H : Set G) := hP hyAssoc
  have : y ∈ ((H : Set G) ∩ c.carrier) := ⟨hyH, hyc⟩
  simpa [hdisj] using this

/-- Helper for Proposition 11-11.4-4: a subgroup-induction generator lies in the zero-residual
prime indexed by the class of `x` exactly when the induced class function vanishes at `x`. -/
private lemma induction_generator_mem_zero_prime_iff
    (H : Subgroup G) (x : G) (χ : R(H)) :
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
      (H.characterRingInduction χ)) ∈ (P0 A (ConjClasses.mk x)).asIdeal ↔
      ((H.characterRingInduction χ : R(G)) : G → ℂ) x = 0 := by
  -- Reduce kernel membership in `P₀,[x]` to ordinary evaluation of the induced class function.
  change (((tensorCharacterRingToSubalgebra A G)
      ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G)))
        (H.characterRingInduction χ)) :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ) x = 0 ↔ _
  simp [tensorCharacterRingToSubalgebra, Subgroup.characterRingInduction_apply]

/-- Helper for Proposition 11-11.4-4: if a subgroup misses the conjugacy class of `x`, then every
character induced from that subgroup vanishes at `x`. -/
private lemma induced_character_value_eq_zero_of_disjoint_carrier
    (H : Subgroup G) (x : G)
    (hdisj : ((H : Set G) ∩ (ConjClasses.mk x).carrier) = ∅) (χ : R(H)) :
    ((H.characterRingInduction χ : R(G)) : G → ℂ) x = 0 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype H := Fintype.ofFinite H
  -- Expand the induced character and show every summand is forced to vanish.
  rw [Subgroup.characterRingInduction_apply]
  change ((Nat.card H : ℂ)⁻¹) *
      (∑ s : G,
        if hsg : s⁻¹ * x * s ∈ H then
          χ ⟨s⁻¹ * x * s, hsg⟩
        else 0) = 0
  have hsum :
      (∑ s : G,
        if hsg : s⁻¹ * x * s ∈ H then
          χ ⟨s⁻¹ * x * s, hsg⟩
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s _
    by_cases hs : s⁻¹ * x * s ∈ H
    · -- A nonzero summand would exhibit an element of `H` inside the conjugacy class of `x`.
      have hsconj : s * (s⁻¹ * x * s) * s⁻¹ = x := by
        group
      have hcarrier : s⁻¹ * x * s ∈ (ConjClasses.mk x).carrier := by
        refine ConjClasses.mem_carrier_iff_mk_eq.mpr ?_
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.2 ⟨s, hsconj⟩)
      have hempty : False := by
        have hmem : s⁻¹ * x * s ∈ ((H : Set G) ∩ (ConjClasses.mk x).carrier) := ⟨hs, hcarrier⟩
        simp [hdisj] at hmem
      suffices χ ⟨s⁻¹ * x * s, hs⟩ = 0 by
        simpa [hs] using this
      exact False.elim hempty
    · simp [hs]
  rw [hsum, mul_zero]

/-- Helper for Proposition 11-11.4-4: when `x ∈ H`, the trivial induction generator has nonzero
value at `x`. -/
private lemma trivial_induced_value_ne_zero_of_mem_subgroup
    (H : Subgroup G) (x : G) (hx : x ∈ H) :
    ((H.characterRingInduction (1 : R(H)) : R(G)) : G → ℂ) x ≠ 0 := by
  -- For the trivial character, the identity element of `G` already contributes a nonzero summand.
  rw [Subgroup.characterRingInduction_apply, Subgroup.inducedClassFunction]
  have hcard_ne : Nat.card H ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  simpa [hcard_ne] using And.intro hcard_ne (show ∃ s : G, s⁻¹ * x * s ∈ H by
    refine ⟨1, ?_⟩
    simpa using hx)

/-- Helper for Proposition 11-11.4-4: a subgroup-induction ideal coming from a subgroup disjoint
from `c` is contained in the zero-residual prime `P₀,c`. -/
private theorem tensorCharacterRingInductionIdeal_le_zero_line_prime_of_disjoint_carrier
    (H : Subgroup G) (c : ConjClasses G)
    (hdisj : ((H : Set G) ∩ c.carrier) = ∅) :
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ (P0 A c).asIdeal := by
  -- Check the defining induction generators one by one after choosing a representative of `c`.
  rw [tensorCharacterRingInductionIdeal, Ideal.span_le]
  intro ξ hξ
  rcases hξ with ⟨χ, rfl⟩
  obtain ⟨x, hmk⟩ := ConjClasses.mk_surjective c
  have hdisj_x : ((H : Set G) ∩ (ConjClasses.mk x).carrier) = ∅ := by
    simpa [hmk] using hdisj
  have hmem_x :
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
        (H.characterRingInduction χ)) ∈ (P0 A (ConjClasses.mk x)).asIdeal :=
    (induction_generator_mem_zero_prime_iff (A := A) H x χ).2
      (induced_character_value_eq_zero_of_disjoint_carrier H x hdisj_x χ)
  simpa [hmk] using hmem_x

/-- Helper for Proposition 11-11.4-4: the subgroup-induction ideal `I_H` is contained in the
zero-residual prime `P₀,c` exactly when `H` misses the conjugacy class `c`. -/
private theorem subgroup_induction_ideal_le_zero_line_prime_iff_inter_eq_empty_local
    (H : Subgroup G) (c : ConjClasses G) :
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ (P0 A c).asIdeal ↔
      ((H : Set G) ∩ c.carrier) = ∅ := by
  constructor
  · intro hcontain
    -- If `I_H` lay in `P₀,c`, the trivial induction generator would vanish on every point of
    -- `H ∩ c`, contradicting the explicit nonvanishing witness.
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    intro x hx
    rcases hx with ⟨hxH, hxc⟩
    have hrange :
        Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction (1 : R(H))) ∈
          Set.range fun χ : R(H) ↦
            Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
              (H.characterRingInduction χ) := ⟨1, rfl⟩
    have hgen_mem :
        Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction (1 : R(H))) ∈
          tensorCharacterRingInductionIdeal (A := A) (G := G) H := by
      exact Ideal.subset_span hrange
    have hprime_mem :
        Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction (1 : R(H))) ∈
          (P0 A (ConjClasses.mk x)).asIdeal := by
      have hmem_c :
          Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
            (H.characterRingInduction (1 : R(H))) ∈ (P0 A c).asIdeal :=
        hcontain hgen_mem
      have hmk : ConjClasses.mk x = c := ConjClasses.mem_carrier_iff_mk_eq.mp hxc
      simpa [hmk] using hmem_c
    have hzero :=
      (induction_generator_mem_zero_prime_iff (A := A) H x (1 : R(H))).mp hprime_mem
    exact (trivial_induced_value_ne_zero_of_mem_subgroup H x hxH) hzero
  · intro hdisj
    -- The reverse implication is the already-verified disjoint-carrier containment lemma.
    exact
      tensorCharacterRingInductionIdeal_le_zero_line_prime_of_disjoint_carrier
        (A := A) H c hdisj

/-- Helper for Proposition 11-11.4-4: choose a representative of a conjugacy class. -/
private def fixedClassRepresentativeLocal (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective c)

/-- Helper for Proposition 11-11.4-4: the chosen representative maps back to the original
conjugacy class. -/
private theorem fixedClassRepresentativeLocal_mk (c : ConjClasses G) :
    ConjClasses.mk (fixedClassRepresentativeLocal c) = c :=
  Classical.choose_spec (ConjClasses.mk_surjective c)

/-- Helper for Proposition 11-11.4-4: evaluating the realized tensor character at the chosen
representative gives a concrete complex-valued ring hom on `A ⊗ R(G)`. -/
private def tensorCharacterRingValueAtConjClassComplex
    (c : ConjClasses G) :
    A ⊗R(G) →+* ℂ where
  toFun χ :=
    ((tensorCharacterRingToSubalgebra A G χ :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ) (fixedClassRepresentativeLocal c)
  map_one' := by
    simp [fixedClassRepresentativeLocal]
  map_mul' χ ψ := by
    simp [fixedClassRepresentativeLocal]
  map_zero' := by
    simp [fixedClassRepresentativeLocal]
  map_add' χ ψ := by
    simp [fixedClassRepresentativeLocal]

/-- Helper for Proposition 11-11.4-4: the fixed-class complex evaluation can be computed at any
representative of the same conjugacy class. -/
private theorem tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
    (c : ConjClasses G) (χ : A ⊗R(G)) {x : G} (hx : ConjClasses.mk x = c) :
    tensorCharacterRingValueAtConjClassComplex (A := A) c χ =
      ((tensorCharacterRingToSubalgebra A G χ :
          characterRingScalarExtensionSubalgebra A G) : G → ℂ) x := by
  let f : G → ℂ :=
    ((tensorCharacterRingToSubalgebra A G χ :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ)
  have hf :
      _root_.IsClassFunction f := by
    exact
      isClassFunction_of_mem_characterRingScalarExtension
        (show f ∈ characterRingScalarExtension A G from
          (tensorCharacterRingToSubalgebra A G χ).2)
  have hrepr :
      ConjClasses.mk (fixedClassRepresentativeLocal c) = ConjClasses.mk x := by
    rw [fixedClassRepresentativeLocal_mk, hx]
  -- Both evaluation points represent the same conjugacy class, so a class function takes the
  -- same value at them.
  exact hf.eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hrepr)

/-- Helper for Proposition 11-11.4-4: scalar tensors evaluate to the same scalar under the
fixed-class complex evaluation. -/
private theorem tensorCharacterRingValueAtConjClassComplex_algebraMap
    (c : ConjClasses G) (a : A) :
    tensorCharacterRingValueAtConjClassComplex (A := A) c
      ((algebraMap A (A ⊗R(G))) a) = algebraMap A ℂ a := by
  -- The tensor-character realization is an `A`-algebra map, so evaluating a scalar tensor gives
  -- the corresponding constant scalar function.
  simpa [tensorCharacterRingValueAtConjClassComplex, fixedClassRepresentativeLocal] using
    congrArg
      (fun f : characterRingScalarExtensionSubalgebra A G ↦
        ((f : G → ℂ) (fixedClassRepresentativeLocal c)))
      ((tensorCharacterRingToSubalgebra A G).commutes a)

/-- Helper for Proposition 11-11.4-4: the value of a virtual character at the chosen
representative of `c` lies in the arithmetic coefficient ring `A`. -/
private theorem characterRingValueAtConjClass_mem_range
    (c : ConjClasses G) (χ : R(G)) :
    (χ (fixedClassRepresentativeLocal c) : ℂ) ∈ Set.range (algebraMap A ℂ) := by
  -- Serre's arithmetic hypothesis says every character value is integral over `ℤ`, hence it
  -- already comes from the integral-closure ring `A`.
  exact
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).mp
      (Proposition_11_11_4_1.characterRing_value_isIntegral_local
        (G := G) χ (fixedClassRepresentativeLocal c))

/-- Helper for Proposition 11-11.4-4: evaluation on the chosen representative lifts from the
ordinary character ring `R(G)` to an `A`-valued algebra map. -/
private def characterRingValueAtConjClass
    (c : ConjClasses G) :
    R(G) →ₐ[ℤ] A where
  toFun χ := Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c χ)
  map_zero' := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    simpa using
      (Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c 0))
  map_one' := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    simpa using
      (Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c 1))
  map_add' χ ψ := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    have hχ :=
      Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c χ)
    have hψ :=
      Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c ψ)
    have hχψ :=
      Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c (χ + ψ))
    calc
      algebraMap A ℂ
          (Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c (χ + ψ)))
          = (χ + ψ) (fixedClassRepresentativeLocal c) := hχψ
      _ = χ (fixedClassRepresentativeLocal c) + ψ (fixedClassRepresentativeLocal c) := by
            simp
      _ = algebraMap A ℂ
            (Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c χ)) +
          algebraMap A ℂ
            (Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c ψ)) := by
            rw [hχ, hψ]
      _ = algebraMap A ℂ
            (Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c χ) +
              Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c ψ)) := by
            rw [map_add]
  map_mul' χ ψ := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    have hχ :=
      Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c χ)
    have hψ :=
      Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c ψ)
    have hχψ :=
      Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c (χ * ψ))
    calc
      algebraMap A ℂ
          (Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c (χ * ψ)))
          = (χ * ψ) (fixedClassRepresentativeLocal c) := hχψ
      _ = χ (fixedClassRepresentativeLocal c) * ψ (fixedClassRepresentativeLocal c) := by
            simp
      _ = algebraMap A ℂ
            (Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c χ)) *
          algebraMap A ℂ
            (Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c ψ)) := by
            rw [hχ, hψ]
      _ = algebraMap A ℂ
            (Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c χ) *
              Classical.choose (characterRingValueAtConjClass_mem_range (A := A) c ψ)) := by
            rw [map_mul]
  commutes' n := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    simpa using
      (Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) c (algebraMap ℤ (R(G)) n)))

/-- Helper for Proposition 11-11.4-4: after scalar extension to `ℂ`, the `A`-valued evaluation on
`R(G)` agrees with ordinary character evaluation at the chosen representative of `c`. -/
private theorem characterRingValueAtConjClass_algebraMap
    (c : ConjClasses G) (χ : R(G)) :
    algebraMap A ℂ (characterRingValueAtConjClass (A := A) c χ) =
      (χ (fixedClassRepresentativeLocal c) : ℂ) :=
  Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) c χ)

/-- Helper for Proposition 11-11.4-4: tensoring the scalar identity on `A` with fixed-class
evaluation on `R(G)` gives an `A`-valued evaluation map on `A ⊗ R(G)`. -/
private def tensorCharacterRingValueAtConjClass
    (c : ConjClasses G) :
    A ⊗R(G) →ₐ[ℤ] A :=
  Algebra.TensorProduct.productMap
    (AlgHom.id ℤ A)
    (characterRingValueAtConjClass (A := A) c)

/-- Helper for Proposition 11-11.4-4: the tensor-product evaluation sends a scalar tensor to the
same scalar in `A`. -/
private theorem tensorCharacterRingValueAtConjClass_algebraMap
    (c : ConjClasses G) (a : A) :
    tensorCharacterRingValueAtConjClass (A := A) c
      ((algebraMap A (A ⊗R(G))) a) = a := by
  -- The tensor-product evaluator uses the identity on the scalar factor.
  simp [tensorCharacterRingValueAtConjClass]

/-- Helper for Proposition 11-11.4-4: after applying `A → ℂ`, the `A`-valued tensor-product
evaluation becomes the corresponding complex evaluation at the chosen representative. -/
private theorem tensorCharacterRingValueAtConjClass_complex_eq
    (c : ConjClasses G) (χ : A ⊗R(G)) :
    algebraMap A ℂ (tensorCharacterRingValueAtConjClass (A := A) c χ) =
      tensorCharacterRingValueAtConjClassComplex (A := A) c χ := by
  let f : A ⊗R(G) →ₐ[A] ℂ :=
    { toRingHom := (algebraMap A ℂ).comp (tensorCharacterRingValueAtConjClass (A := A) c).toRingHom
      commutes' := by
        intro a
        exact congrArg (algebraMap A ℂ)
          (tensorCharacterRingValueAtConjClass_algebraMap (A := A) c a) }
  let g : A ⊗R(G) →ₐ[A] ℂ :=
    { toRingHom := tensorCharacterRingValueAtConjClassComplex (A := A) c
      commutes' := tensorCharacterRingValueAtConjClassComplex_algebraMap (A := A) c }
  have hright :
      (AlgHom.restrictScalars ℤ f).comp
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) =
        (AlgHom.restrictScalars ℤ g).comp
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) := by
    ext ψ
    -- On the character-ring factor, both tensor-product maps reduce to the same chosen
    -- evaluation at the fixed representative of `c`.
    simp [f, g, tensorCharacterRingValueAtConjClass, characterRingValueAtConjClass_algebraMap]
    simpa [tensorCharacterRingToSubalgebra] using
      (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
        (A := A) c
        ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) ψ)
        (fixedClassRepresentativeLocal_mk c)).symm
  have hfg : f = g := Algebra.TensorProduct.ext_ring hright
  exact congrArg (fun h : A ⊗R(G) →ₐ[A] ℂ ↦ h χ) hfg

/-- Helper for Proposition 11-11.4-4: any `|G|`-th root of unity in `ℂˣ` already comes from the
arithmetic coefficient ring `A`. -/
private theorem root_of_unity_mem_range_of_pow_card_eq_one
    (z : ℂˣ) (hz : z ^ Nat.card G = 1) :
    ((z : ℂ) ∈ Set.range (algebraMap A ℂ)) := by
  have hcard_pos : 0 < Nat.card G := by
    simpa [Nat.card_eq_fintype_card] using
      Fintype.card_pos_iff.mpr (show Nonempty G from ⟨1⟩)
  have hz_pow : ((z : ℂ) ^ Nat.card G) = 1 := by
    -- Coercing the unit equation to `ℂ` gives the source integrality relation.
    exact congrArg (fun u : ℂˣ ↦ (u : ℂ)) hz
  have hz_integral : IsIntegral ℤ (z : ℂ) := by
    -- A root of `X ^ |G| - 1` is integral over `ℤ`.
    refine IsIntegral.of_pow (n := Nat.card G) hcard_pos ?_
    simpa [hz_pow] using (isIntegral_one : IsIntegral ℤ (1 : ℂ))
  exact
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).mp
      hz_integral

/-- Helper for Proposition 11-11.4-4: the local `p`-regular owner map agrees with the canonical
owner map extracted in Proposition `11-11.4-1`. -/
private theorem pRegularConjClassOfConjClass_eq_owner
    (p : Nat.Primes) (c : ConjClasses G) :
    pRegularConjClassOfConjClass p c =
      Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p c := by
  -- Both owner maps are quotient lifts of the same `p'`-component construction, so it suffices
  -- to reduce to a concrete representative of the ordinary conjugacy class.
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  rfl

/-- Helper for Proposition 11-11.4-4: the local complex-valued fixed-class evaluation agrees with
the canonical fixed-class evaluation from Proposition `11-11.4-1`. -/
private theorem tensorCharacterRingValueAtConjClassComplex_eq_owner
    (c : ConjClasses G) :
    tensorCharacterRingValueAtConjClassComplex (A := A) c =
      Proposition_11_11_4_1.tensorCharacterRingValueAtConjClassComplex
        (A := A) (G := G) c := by
  -- Both complex-valued evaluators are the same ring hom after unfolding the duplicated local
  -- fixed-class representative choice.
  rfl

/-- Helper for Proposition 11-11.4-4: the local `A`-valued fixed-class evaluation agrees with the
canonical evaluation map extracted in Proposition `11-11.4-1`. -/
private theorem tensorCharacterRingValueAtConjClass_eq_owner
    (c : ConjClasses G) :
    tensorCharacterRingValueAtConjClass (A := A) c =
      Proposition_11_11_4_1.tensorCharacterRingValueAtConjClass
        (A := A) (G := G) c := by
  -- Compare the two `A`-valued evaluations after embedding into `ℂ`, where both sides become the
  -- already-identified complex fixed-class evaluator.
  exact AlgHom.ext fun χ ↦ by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    rw [tensorCharacterRingValueAtConjClass_complex_eq (A := A) c χ]
    rw [Proposition_11_11_4_1.tensorCharacterRingValueAtConjClass_complex_eq
      (A := A) (G := G) c χ]
    rw [tensorCharacterRingValueAtConjClassComplex_eq_owner (A := A) (G := G) c]

/-- Helper for Proposition 11-11.4-4: distinct ordinary conjugacy classes admit a tensor
character whose fixed-class evaluation vanishes on one class and is nonzero on the other. -/
private theorem zero_prime_separator_eval_of_ne
    (c₁ c₂ : ConjClasses G) (hc : c₁ ≠ c₂) :
    ∃ χ : A ⊗R(G),
      tensorCharacterRingValueAtConjClassComplex (A := A) c₂ χ = 0 ∧
        tensorCharacterRingValueAtConjClassComplex (A := A) c₁ χ ≠ 0 := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c₁
  rcases Representation.weighted_adamsOperator_conjClassIndicator_lifts_to_tensorCharacterRing
      A 1 (ConjClasses.mk x) (by
        -- Serre's Frobenius theorem uses exactly the `|G|`-th roots-of-unity hypothesis, which
        -- the integral-closure assumption provides.
        exact root_of_unity_mem_range_of_pow_card_eq_one (A := A) (G := G)) with ⟨χ, hχ⟩
  refine ⟨χ, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := ConjClasses.mk_surjective c₂
    have hxy : ConjClasses.mk y ≠ ConjClasses.mk x := by
      intro h
      exact hc (h.symm.trans hy)
    rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) c₂ χ hy]
    change (χ : G → ℂ) y = 0
    rw [hχ]
    have hyfin : IsOfFinOrder y := isOfFinOrder_of_finite y
    have hcard_ne : Nat.card G ≠ 0 := by
      exact Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
    have hindicator :
        (algebraMap A ℂ) ((ConjClasses.mk x).carrier.indicator 1 y : A) = 0 := by
      simp [Set.indicator, ConjClasses.mem_carrier_iff_mk_eq, hxy]
    simpa [Representation.adamsOperator, hyfin, ConjClasses.indicator, hcard_ne] using hindicator
  · rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (ConjClasses.mk x) χ rfl]
    change (χ : G → ℂ) x ≠ 0
    rw [hχ]
    have hxfin : IsOfFinOrder x := isOfFinOrder_of_finite x
    have hcard_ne : Nat.card G ≠ 0 := by
      exact Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
    have hindicator :
        (algebraMap A ℂ) (((ConjClasses.mk x).carrier.indicator 1 x : A)) ≠ 0 := by
      have hone : (algebraMap A ℂ) (1 : A) ≠ 0 := by
        exact_mod_cast one_ne_zero
      simpa [Set.indicator, ConjClasses.mem_carrier_iff_mk_eq] using hone
    simpa [Representation.adamsOperator, hxfin, ConjClasses.indicator, hcard_ne] using hindicator

/-- Helper for Proposition 11-11.4-4: the canonical regular prime indexed by `(p, M, c)` should
satisfy Serre's defining regular-prime predicate. -/
private theorem tensorCharacterRingRegularPrime_spec
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularConjClass G p) :
    Ideal.comap (algebraMap A (A ⊗R(G))) (Pm M c).asIdeal = M.1.asIdeal ∧
      ∀ H : Subgroup G,
        tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ (Pm M c).asIdeal ↔
          ¬ HasAssociatedPElementarySubgroupInClass c H := by
  -- The local regular-prime owner is exactly the canonical Proposition `11-11.4-1` regular prime
  -- attached to the underlying ordinary conjugacy class of `c`.
  simpa [tensorCharacterRingRegularPrime,
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class_coe] using
    (_root_.value_comap_isTensorCharacterRingRegularPrime
      (A := A) (G := G) p M (c : ConjClasses G))

/-- Helper for Proposition 11-11.4-4: the zero point on the line of `c` is the pullback of the
zero prime of `A` along the fixed-class `A`-valued evaluation map. -/
private theorem zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass
    (c : ConjClasses G) :
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
      ⟨(⊥ : Ideal A), inferInstance⟩ = P0 A c := by
  let Q : SpecARG :=
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
      ⟨(⊥ : Ideal A), inferInstance⟩
  have hQcomap :
      Ideal.comap (algebraMap A (A ⊗R(G))) Q.asIdeal = ⊥ := by
    ext a
    change tensorCharacterRingValueAtConjClass (A := A) c
        ((algebraMap A (A ⊗R(G))) a) ∈ (⊥ : Ideal A) ↔ a ∈ (⊥ : Ideal A)
    rw [tensorCharacterRingValueAtConjClass_algebraMap (A := A) c a]
  rcases tensor_character_ring_prime_ideal_classification (A := A) (G := G) Q with hzero | hreg
  · rcases hzero with ⟨c', hc'⟩
    have hcc' : c' = c := by
      by_contra hne
      obtain ⟨χ, hχc, hχc'⟩ := zero_prime_separator_eval_of_ne (A := A) c' c hne
      have hχQ : χ ∈ Q.asIdeal := by
        change tensorCharacterRingValueAtConjClass (A := A) c χ = 0
        apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
        rw [tensorCharacterRingValueAtConjClass_complex_eq (A := A) c χ, hχc]
        simp
      have hχP0 : χ ∈ (P0 A c').asIdeal := by
        simpa [Q, hc'.symm] using hχQ
      obtain ⟨x, hx⟩ := ConjClasses.mk_surjective c'
      have hχx :
          ((tensorCharacterRingToSubalgebra A G χ :
              characterRingScalarExtensionSubalgebra A G) : G → ℂ) x = 0 := by
        have hχP0x : χ ∈ (P0 A (ConjClasses.mk x)).asIdeal := by
          simpa [hx] using hχP0
        change (((tensorCharacterRingToSubalgebra A G) χ :
            characterRingScalarExtensionSubalgebra A G) : G → ℂ) x = 0 at hχP0x
        exact hχP0x
      have hχc'zero :
          tensorCharacterRingValueAtConjClassComplex (A := A) c' χ = 0 := by
        rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) c' χ hx]
        exact hχx
      exact hχc' hχc'zero
    calc
      Q = P0 A c' := hc'.symm
      _ = P0 A c := by simpa [hcc']
  · rcases hreg with ⟨p, M, d, hd⟩
    have hPmcomap :
        Ideal.comap (algebraMap A (A ⊗R(G))) (Pm M d).asIdeal = M.1.asIdeal :=
      (tensorCharacterRingRegularPrime_spec (A := A) (G := G) p M d).1
    have hMbot : M.1.asIdeal = ⊥ := by
      calc
        M.1.asIdeal = Ideal.comap (algebraMap A (A ⊗R(G))) (Pm M d).asIdeal := by
          symm
          exact hPmcomap
        _ = Ideal.comap (algebraMap A (A ⊗R(G))) Q.asIdeal := by
          simpa [hd]
        _ = ⊥ := hQcomap
    exact False.elim (M.2.1 hMbot)

/-- Helper for Proposition 11-11.4-4: the zero point `P₀,c` contracts to the zero ideal of `A`. -/
private theorem zero_line_point_comap_eq_bot_local
    (c : ConjClasses G) :
    Ideal.comap (algebraMap A (A ⊗R(G))) (P0 A c).asIdeal = ⊥ := by
  -- Rewrite `P₀,c` as the comap of the fixed-class evaluation at the bottom prime of `A`.
  rw [← zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass (A := A) c]
  ext a
  -- On scalar tensors, the fixed-class evaluation is literally the identity on `A`.
  change tensorCharacterRingValueAtConjClass (A := A) c
      ((algebraMap A (A ⊗R(G))) a) ∈ (⊥ : Ideal A) ↔ a ∈ (⊥ : Ideal A)
  rw [tensorCharacterRingValueAtConjClass_algebraMap (A := A) c a]

/-- Helper for Proposition 11-11.4-4: pulling back the maximal ideal `M` along the fixed-class
evaluation still lies over `M`. -/
private theorem value_comap_eq_residual_maximal_local
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    Ideal.comap (algebraMap A (A ⊗R(G)))
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
        ⟨M.1.asIdeal, inferInstance⟩).asIdeal = M.1.asIdeal := by
  -- Evaluate the contraction test on scalar tensors and use that the evaluation fixes scalars.
  ext a
  change tensorCharacterRingValueAtConjClass (A := A) c
      ((algebraMap A (A ⊗R(G))) a) ∈ M.1.asIdeal ↔ a ∈ M.1.asIdeal
  rw [tensorCharacterRingValueAtConjClass_algebraMap (A := A) c a]

/-- Helper for Proposition 11-11.4-4: the fixed-class evaluation pullback of `M` lands on the
regular branch of Serre's prime-spectrum classification, not on the zero branch. -/
private theorem value_comap_eq_some_regular_point
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    ∃ p' : Nat.Primes, ∃ M' : NonzeroResidualCharacteristicMaximalIdeal A p',
      ∃ d : PRegularConjClass G p',
        PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
          ⟨M.1.asIdeal, inferInstance⟩ = Pm M' d := by
  let Q : SpecARG :=
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
      ⟨M.1.asIdeal, inferInstance⟩
  rcases tensor_character_ring_prime_ideal_classification (A := A) (G := G) Q with hzero | hreg
  · rcases hzero with ⟨c', hc'⟩
    have hQbot : Ideal.comap (algebraMap A (A ⊗R(G))) Q.asIdeal = ⊥ := by
      -- The zero branch would force the contracted ideal to be zero, contradicting `M ≠ ⊥`.
      simpa [hc'] using zero_line_point_comap_eq_bot_local (A := A) c'
    have hMbot : M.1.asIdeal = ⊥ := by
      calc
        M.1.asIdeal =
            Ideal.comap (algebraMap A (A ⊗R(G))) Q.asIdeal := by
              symm
              exact value_comap_eq_residual_maximal_local (A := A) p M c
        _ = ⊥ := hQbot
    exact False.elim (M.2.1 hMbot)
  · rcases hreg with ⟨p', M', d, hd⟩
    exact ⟨p', M', d, hd.symm⟩

/-- Helper for Proposition 11-11.4-4: the fixed-class evaluation pullback of `M` is already a
regular prime over the same residual-characteristic maximal ideal `M`. -/
private theorem value_comap_eq_regular_point_over_same_maximal
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    ∃ d : PRegularConjClass G p,
      PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
        ⟨M.1.asIdeal, inferInstance⟩ = Pm M d := by
  rcases value_comap_eq_some_regular_point (A := A) p M c with ⟨p', M', d, hQeq⟩
  have hMideal : M'.1.asIdeal = M.1.asIdeal := by
    -- Compare the contraction of the regular branch representative with the already-computed
    -- contraction of the evaluation pullback.
    calc
      M'.1.asIdeal = Ideal.comap (algebraMap A (A ⊗R(G))) (Pm M' d).asIdeal := by
        symm
        exact (tensorCharacterRingRegularPrime_spec (A := A) (G := G) p' M' d).1
      _ = Ideal.comap (algebraMap A (A ⊗R(G)))
          (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
            ⟨M.1.asIdeal, inferInstance⟩).asIdeal := by
              simpa [hQeq]
      _ = M.1.asIdeal := value_comap_eq_residual_maximal_local (A := A) p M c
  have hMmax : M'.1 = M.1 := by
    -- Maximal ideals in `MaximalSpectrum A` are determined by their underlying ideals.
    exact MaximalSpectrum.ext hMideal
  have hp' : p' = p := by
    -- The residue field of the shared maximal ideal has a unique characteristic.
    have hp'ring : ringChar M'.1.asIdeal.ResidueField = p' := by
      letI : CharP M'.1.asIdeal.ResidueField p' := M'.2.2
      exact ringChar.eq M'.1.asIdeal.ResidueField p'
    have hpring : ringChar M'.1.asIdeal.ResidueField = p := by
      have hp0 : (p : A ⧸ M'.1.asIdeal) = 0 := by
        change Ideal.Quotient.mk M'.1.asIdeal (p : A) = 0
        rw [hMideal]
        have hp0M : (p : A ⧸ M.1.asIdeal) = 0 := by
          letI : CharP M.1.asIdeal.ResidueField p := M.2.2
          letI : CharP (A ⧸ M.1.asIdeal) p :=
            RingHom.charP
              (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
              M.1.asIdeal.injective_algebraMap_quotient_residueField p
          exact CharP.cast_eq_zero (R := A ⧸ M.1.asIdeal) p
        simpa using hp0M
      letI : CharP (A ⧸ M'.1.asIdeal) p :=
        ringChar.of_eq
          (CharP.ringChar_of_prime_eq_zero
            (R := A ⧸ M'.1.asIdeal) (Fact.out : Nat.Prime (p : ℕ)) hp0)
      letI : CharP M'.1.asIdeal.ResidueField p :=
        charP_of_injective_algebraMap
          M'.1.asIdeal.injective_algebraMap_quotient_residueField p
      exact ringChar.eq M'.1.asIdeal.ResidueField p
    apply Subtype.ext
    exact hp'ring.symm.trans hpring
  subst hp'
  have hM : M' = M := by
    -- After fixing the prime characteristic and the maximal ideal, only proof data remains.
    exact Subtype.ext hMmax
  subst hM
  exact ⟨d, hQeq⟩

/-- Helper for Proposition 11-11.4-4: evaluating an induction generator along the fixed-class map
just evaluates the induced virtual character at the chosen conjugacy class. -/
private theorem tensorCharacterRingValueAtConjClass_includeRight_characterRingInduction
    (c : ConjClasses G) (H : Subgroup G) (χ : R(H)) :
    tensorCharacterRingValueAtConjClass (A := A) c
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
        (H.characterRingInduction χ)) =
      characterRingValueAtConjClass (A := A) c (H.characterRingInduction χ) := by
  -- On pure tensors from the character-ring factor, the tensor-product evaluator is just its
  -- second component.
  simp [tensorCharacterRingValueAtConjClass]

/-- Helper for Proposition 11-11.4-4: a pure induction generator belongs to the evaluation
pullback prime over `M` exactly when its fixed-class evaluation lies in `M`. -/
private theorem induction_generator_mem_value_comap_iff_local
    (M : MaximalSpectrum A) (c : ConjClasses G) (H : Subgroup G) (χ : R(H)) :
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
      (H.characterRingInduction χ)) ∈
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
        ⟨M.asIdeal, inferInstance⟩).asIdeal ↔
        characterRingValueAtConjClass (A := A) c (H.characterRingInduction χ) ∈ M.asIdeal := by
  -- Membership in a comap is exactly membership of the evaluated image in the target prime ideal.
  change
    tensorCharacterRingValueAtConjClass (A := A) c
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction χ)) ∈ M.asIdeal ↔
      _
  rw [tensorCharacterRingValueAtConjClass_includeRight_characterRingInduction (A := A) c H χ]

/-- Helper for Proposition 11-11.4-4: the zero-residual point `P₀,c` always specializes to the
evaluation pullback prime over the maximal ideal `M`. -/
private theorem zero_line_point_specializes_value_comap_local
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    (P0 A c).asIdeal ≤
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
        ⟨M.1.asIdeal, inferInstance⟩).asIdeal := by
  -- Both primes are comaps of the same evaluation map, so specialization is just monotonicity of
  -- ideal comap along `⊥ ≤ M.1.asIdeal`.
  rw [← zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass (A := A) c]
  change
    Ideal.comap (tensorCharacterRingValueAtConjClass (A := A) c) (⊥ : Ideal A) ≤
      Ideal.comap (tensorCharacterRingValueAtConjClass (A := A) c) M.1.asIdeal
  exact Ideal.comap_mono bot_le

/-- Helper for Proposition 11-11.4-4: if a subgroup misses the conjugacy class `c`, then its
induction ideal already lies in the evaluation pullback prime over `M`. -/
private theorem tensorCharacterRingInductionIdeal_le_value_comap_of_disjoint_carrier
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (H : Subgroup G) (c : ConjClasses G)
    (hdisj : ((H : Set G) ∩ c.carrier) = ∅) :
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
        ⟨M.1.asIdeal, inferInstance⟩).asIdeal := by
  -- First place `I_H` in the zero-residual prime `P₀,c`, then specialize that zero point to the
  -- evaluation pullback over `M`.
  calc
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ (P0 A c).asIdeal :=
      tensorCharacterRingInductionIdeal_le_zero_line_prime_of_disjoint_carrier
        (A := A) H c hdisj
    _ ≤
        (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
          ⟨M.1.asIdeal, inferInstance⟩).asIdeal :=
      zero_line_point_specializes_value_comap_local (A := A) p M c

/-- Helper for Proposition 11-11.4-4: the evaluation pullback over `M` already satisfies Serre's
intrinsic regular-prime predicate for the canonical `p`-regular component of `c`. -/
private theorem value_comap_isTensorCharacterRingRegularPrime_local
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    IsTensorCharacterRingRegularPrime A G p M (pRegularConjClassOfConjClass p c)
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
        ⟨M.1.asIdeal, inferInstance⟩) := by
  -- Transport the canonical regular-prime criterion along the two owner-identification lemmas.
  simpa [tensorCharacterRingValueAtConjClass_eq_owner (A := A) (G := G) c,
    pRegularConjClassOfConjClass_eq_owner (G := G) p c] using
    (_root_.value_comap_isTensorCharacterRingRegularPrime
      (A := A) (G := G) p M c)

/-- Helper for Proposition 11-11.4-4: the evaluation pullback over `M` is the regular prime
indexed by the `p`-regular component of `c`. -/
private theorem regular_line_point_eq_comap_tensorCharacterRingValueAtConjClass
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
      ⟨M.1.asIdeal, inferInstance⟩ =
        Pm M (pRegularConjClassOfConjClass p c) := by
  -- The imported regular-branch identification already gives the desired point after rewriting
  -- the duplicated local evaluation map and local `p`-regular owner.
  simpa [tensorCharacterRingRegularPrime,
    tensorCharacterRingValueAtConjClass_eq_owner (A := A) (G := G) c,
    pRegularConjClassOfConjClass_eq_owner (G := G) p c] using
    (_root_.value_comap_eq_tensorCharacterRingRegularPrime
      (A := A) (G := G) p M c)

/-- Helper for Proposition 11-11.4-4: a subgroup-induction ideal coming from a subgroup disjoint
from `c` is contained in every regular prime on the canonical line of `c`. -/
private theorem tensorCharacterRingInductionIdeal_le_regular_line_prime_of_disjoint_carrier
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (H : Subgroup G) (c : ConjClasses G)
    (hdisj : ((H : Set G) ∩ c.carrier) = ∅) :
      tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤
      (Pm M (pRegularConjClassOfConjClass p c)).asIdeal := by
  -- The regular-prime owner criterion reduces containment to the absence of associated
  -- `p`-elementary subgroups from the relevant `p`-regular class.
  exact
    (tensorCharacterRingRegularPrime_spec (A := A) (G := G) p M
      (pRegularConjClassOfConjClass p c)).2 H |>.2
      (not_hasAssociatedPElementarySubgroupInClass_of_disjoint_carrier_local p H c hdisj)

/-- Helper for Proposition 11-11.4-4: every regular point on the canonical line specializes to the
zero-residual point `P₀,c` once the zero-branch ideal is shown to lie inside the corresponding
regular prime ideal. -/
private theorem regular_line_point_specializes_zero_prime_ideal
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    (P0 A c).asIdeal ≤ (Pm M (pRegularConjClassOfConjClass p c)).asIdeal := by
  -- Route correction: the old homeomorphism plan was too strong. The remaining algebraic task is
  -- only to show that the zero-residual kernel specializes to the matching regular prime.
  let Q : SpecARG :=
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) c)
      ⟨M.1.asIdeal, inferInstance⟩
  have hzero_le_Q : (P0 A c).asIdeal ≤ Q.asIdeal :=
    zero_line_point_specializes_value_comap_local (A := A) p M c
  have hQtarget :
      Q = Pm M (pRegularConjClassOfConjClass p c) := by
    simpa [Q] using
      regular_line_point_eq_comap_tensorCharacterRingValueAtConjClass
        (A := A) p M c
  -- Once the regular-class parameter is identified, the specialization is the formal comap
  -- monotonicity established above.
  calc
    (P0 A c).asIdeal ≤ Q.asIdeal := hzero_le_Q
    _ = (Pm M (pRegularConjClassOfConjClass p c)).asIdeal := by
      simpa [hQtarget]

/-- Helper for Proposition 11-11.4-4: every regular point on the canonical line lies in the
closure of the zero-residual point `P₀,c`. -/
private theorem regular_line_point_mem_closure_zero_prime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p) (c : ConjClasses G) :
    Pm M (pRegularConjClassOfConjClass p c) ∈ closure ({P0 A c} : Set SpecARG) := by
  -- In the Zariski topology, belonging to the closure of a singleton is exactly ideal inclusion.
  rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus]
  exact regular_line_point_specializes_zero_prime_ideal (A := A) p M c

/-- Helper for Proposition 11-11.4-4: the whole canonical line is contained in the closure of its
zero-residual point. -/
private theorem tensorCharacterRingPrimeSpectrumLine_subset_closure_zero
    (c : ConjClasses G) :
    tensorCharacterRingPrimeSpectrumLine A c ⊆ closure ({P0 A c} : Set SpecARG) := by
  intro P hP
  rcases hP with hP0 | hPreg
  · -- The distinguished zero point is in the closure of its own singleton.
    exact subset_closure hP0
  · -- Every regular singleton summand is reduced to the pointwise specialization lemma.
    rcases Set.mem_iUnion.mp hPreg with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨M, hM⟩
    have hEq : P = Pm M (pRegularConjClassOfConjClass p c) := by
      simpa using hM
    rw [hEq]
    exact regular_line_point_mem_closure_zero_prime (A := A) p M c

/-- Helper for Proposition 11-11.4-4: each canonical line is connected because it contains its
zero-residual point and stays inside the closure of that singleton. -/
private theorem tensorCharacterRingPrimeSpectrumLine_connected
    (c : ConjClasses G) :
    IsConnected (tensorCharacterRingPrimeSpectrumLine A c) := by
  -- Route correction: the source proof only needs the line to be the closure of its generic
  -- zero-residual point, not a full homeomorphism with `Spec A`.
  refine
    IsConnected.subset_closure isConnected_singleton
      (Set.singleton_subset_iff.mpr (mem_tensorCharacterRingPrimeSpectrumLine_zero (A := A) c))
      (tensorCharacterRingPrimeSpectrumLine_subset_closure_zero (A := A) c)

-- Proof sketch: use the canonical cover of `Spec (A ⊗ R(G))` by the lines indexed by conjugacy
-- classes. Each line is isomorphic to `Spec(A)`, hence connected, and stripping off one prime
-- power at a time from an element connects any line to the unit-class line through a finite chain
-- of nonempty intersections. Then apply the auxiliary line criterion above. This proposition is in
-- Serre's standing arithmetic setting on `A`; it is not intended as a statement for arbitrary
-- complex algebras.
/-- Proposition 11-11.4-4: in Serre's standing arithmetic setting on `A`, modeled here by an
integral-closure arithmetic subring of `ℂ` with finite quotients, the prime spectrum
`Spec (A ⊗ R(G))` is connected in the Zariski topology. This is not a statement for an arbitrary
complex algebra such as `ℚ`. -/
theorem tensorCharacterRingPrimeSpectrum_connected :
    ConnectedSpace SpecARG := by
  -- Route correction: the source proof must proceed through the canonical line cover, not by a
  -- direct topological shortcut on `Spec (A ⊗ R(G))`.
  exact
    tensorCharacterRingPrimeSpectrum_connected_of_lineCriterion (A := A)
      (tensorCharacterRingPrimeSpectrumLine_connected (A := A))
      (tensorCharacterRingPrimeSpectrumLine_chain_to_one (A := A))

end
