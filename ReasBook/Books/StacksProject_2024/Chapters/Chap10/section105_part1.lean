import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_105_1 (from Chap10) -/
noncomputable section

universe u

open Order Set

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace X`
- prime-spectrum/irreducible-closed bridge: `PrimeSpectrum.pointsEquivIrreducibleCloseds`
- ring-level owner: `IsCatenaryRing R`
- prime-spectrum owner equivalence: `isCatenaryRing_iff_catenarySpace_primeSpectrum`

Layer triage:
- `source-facing`: Definition 10.105.1 phrases catenarity through bounded prime chains and common
  lengths of maximal prime chains in intervals of `Spec R`
- `core/canonical`: the chapter owner is already `IsCatenaryRing R` from
  `Lemma_10_105_2`, together with its bridge to `CatenarySpace (PrimeSpectrum R)`
- `bridge/view`: `PrimeSpectrum.pointsEquivIrreducibleCloseds` transports the Chapter 5
  irreducible-closed catenary API to the prime-order formulation used in the source

Primitive data belongs to the owner abstraction `IsCatenaryRing R`; the interval-chain wording is
derived API and should stay as thin owner-derived companion theorems, not as a second public class
or a bundled replacement definition.
-/

/- Definition 10.105.1: the chapter owner for catenary commutative rings is
`IsCatenaryRing R`. -/
recall IsCatenaryRing

/- Companion recall: Lemma `10.105.2` identifies ring catenarity with catenarity of the prime
spectrum. -/
recall isCatenaryRing_iff_catenarySpace_primeSpectrum

namespace IsCatenaryRing

variable [IsCatenaryRing R]

/-- In a catenary ring, every interval `[p, q]` in `Spec R` has a uniform bound on the cardinality
of its finite prime chains. This is the source-facing bounded-chain clause of Definition 10.105.1,
derived from the Chapter 5 catenary owner on `Spec R`. -/
theorem primeChainsBounded (p q : PrimeSpectrum R) (hpq : p ≤ q) :
    ∃ n : ℕ, ∀ s : Set (Set.Icc p q), IsChain (· ≤ ·) s → s.Finite → s.encard ≤ n + 1 := by
  sorry

/-- In a catenary ring, any two maximal prime chains in a fixed interval `[p, q]` have the same
cardinality. This is the source-facing equal-length clause of Definition 10.105.1, derived from
the canonical owner `IsCatenaryRing R`. -/
theorem maximalPrimeChainsHaveSameLength
    (p q : PrimeSpectrum R) (hpq : p ≤ q)
    {s t : Set (Set.Icc p q)} (hs : IsMaxChain (· ≤ ·) s) (ht : IsMaxChain (· ≤ ·) t) :
    s.encard = t.encard := by
  sorry

end IsCatenaryRing

end

/-! ### Lemma_10_105_2 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace X`
- prime-spectrum owner: `PrimeSpectrum R`
- chapter source-facing bridge: `Definition_10_105_1` translates the source prime-chain wording to
  the Chapter 5 topological owner on `Spec R`

Layer triage:
- `source-facing`: the textbook condition that a commutative ring is catenary
- `core/canonical`: `CatenarySpace (PrimeSpectrum R)`
- `bridge/view`: the ring-level vocabulary alias `IsCatenaryRing R`

Primitive data is exactly the catenary-space structure on `Spec R`. The ring-level name is useful
high-reuse vocabulary downstream, but it should remain a thin alias to the canonical topological
owner rather than a one-field wrapper class that duplicates the same datum.
-/

/-- A commutative ring is catenary if its prime spectrum is catenary. This is a thin high-reuse
owner alias for the canonical topological owner on `Spec R`. -/
abbrev IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  CatenarySpace (PrimeSpectrum R)

/-- Lemma 10.105.2: a ring is catenary if and only if the topological space `Spec R` is
catenary. -/
theorem isCatenaryRing_iff_catenarySpace_primeSpectrum :
    IsCatenaryRing R ↔ CatenarySpace (PrimeSpectrum R) :=
  Iff.rfl

end

/-! ### Definition_10_105_3 (from Chap10) -/
universe u v

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace X`
- ring-level owner: `IsCatenaryRing A`
- bridge/view: `isCatenaryRing_iff_catenarySpace_primeSpectrum`

Layer triage:
- `source-facing`: Definition 10.105.3 introduces universal catenarity
- `core/canonical`: finite type algebras should be recorded as catenary rings via
  `IsCatenaryRing`
- `bridge/view`: catenary prime spectra are derived from the owner instance in
  `Lemma_10_105_2`

Primitive data belongs to the ring-level owner `IsCatenaryRing`; the `Spec` formulation is
derived API.
-/

/-- Definition 10.105.3: a Noetherian ring is universally catenary if every finite type
`R`-algebra is catenary. -/
class UniversallyCatenaryRing : Prop extends IsNoetherianRing R where
  catenary_of_finiteType {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    IsCatenaryRing A

/-- A universally catenary ring is catenary via the identity finite type algebra. -/
instance instIsCatenaryRingOfUniversallyCatenaryRing [UniversallyCatenaryRing.{u, u} R] :
    IsCatenaryRing R :=
  (inferInstance : UniversallyCatenaryRing R).catenary_of_finiteType

end

/-! ### Lemma_10_105_4 (from Chap10) -/
noncomputable section

open TopologicalSpace PrimeSpectrum

universe u v

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.105.4: an order isomorphism restricts to the corresponding closed
intervals. -/
private noncomputable def orderIso_interval {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (a b : α) : Set.Icc a b ≃o Set.Icc (e a) (e b) where
  toFun x := ⟨e x.1, e.monotone x.2.1, e.monotone x.2.2⟩
  invFun y := ⟨e.symm y.1, by
    simpa using e.symm.monotone y.2.1, by
    simpa using e.symm.monotone y.2.2⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_rel_iff' := by
    intro x y
    simpa using e.le_iff_le

/-- Helper for Lemma 10.105.4: the dual of an interval is order-isomorphic to the corresponding
reversed interval in the dual order. -/
private noncomputable def dual_orderIso_interval {α : Type*} [Preorder α]
    (a b : α) : (Set.Icc a b)ᵒᵈ ≃o Set.Icc (show αᵒᵈ from b) (show αᵒᵈ from a) where
  toFun x := by
    let x' : Set.Icc a b := show Set.Icc a b from x
    exact ⟨show αᵒᵈ from x'.1, x'.2.2, x'.2.1⟩
  invFun y := by
    exact show (Set.Icc a b)ᵒᵈ from ⟨show α from y.1, y.2.2, y.2.1⟩
  left_inv x := by
    ext
    rfl
  right_inv y := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Lemma 10.105.4: membership in the irreducible closed subset defined by a prime is
equivalent to specialization toward that prime. -/
private theorem mem_pointsEquivIrreducibleCloseds_iff_le (p q : PrimeSpectrum R) :
    p ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) ↔ q ≤ p := by
  -- Rewrite the irreducible closed subset attached to `q` as the closure of `{q}`.
  rw [show ((show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) =
      closure ({q} : Set (PrimeSpectrum R)) by rfl]
  rw [← specializes_iff_mem_closure, PrimeSpectrum.le_iff_specializes]

/-- Helper for Lemma 10.105.4: every prime below a disjoint prime is again disjoint from the
multiplicative set. -/
private theorem disjoint_of_le_comap {M : Submonoid R} {p q : PrimeSpectrum R}
    (hqM : Disjoint (M : Set R) q.asIdeal) (hpq : p ≤ q) :
    Disjoint (M : Set R) p.asIdeal := by
  -- Disjointness is inherited by smaller ideals.
  exact hqM.mono_right ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 hpq)

/-- Helper for Lemma 10.105.4: contraction along `R → Localization M` identifies prime intervals
in the localization with the corresponding ambient prime intervals. -/
private noncomputable def localization_prime_interval_order_iso (M : Submonoid R)
    (p q : PrimeSpectrum (Localization M)) :
    Set.Icc p q ≃o
      Set.Icc
        (PrimeSpectrum.comap (algebraMap R (Localization M)) p)
        (PrimeSpectrum.comap (algebraMap R (Localization M)) q) where
  toFun x := ⟨PrimeSpectrum.comap (algebraMap R (Localization M)) x.1,
    ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
      rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
      exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 x.2.1)),
    ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
      rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
      exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 x.2.2))⟩
  invFun y := by
    let hqM :
        Disjoint (M : Set R)
          (PrimeSpectrum.comap (algebraMap R (Localization M)) q).asIdeal := by
      have hq_ne_top : q.asIdeal ≠ ⊤ := q.2.1
      simpa [PrimeSpectrum.comap_asIdeal] using
        (IsLocalization.disjoint_comap_iff M (Localization M) q.asIdeal).2 hq_ne_top
    let hyM : Disjoint (M : Set R) y.1.asIdeal :=
      disjoint_of_le_comap (M := M) (p := y.1)
        (q := PrimeSpectrum.comap (algebraMap R (Localization M)) q) hqM y.2.2
    refine ⟨(primeSpectrum_localization_homeomorph M).symm ⟨y.1, hyM⟩, ?_, ?_⟩
    · -- Compare lower endpoints after extending ideals back to the localization.
      exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
        calc
          p.asIdeal = Ideal.map (algebraMap R (Localization M))
              (PrimeSpectrum.comap (algebraMap R (Localization M)) p).asIdeal := by
                rw [PrimeSpectrum.comap_asIdeal]
                exact (IsLocalization.map_comap M (Localization M) p.asIdeal).symm
          _ ≤ Ideal.map (algebraMap R (Localization M)) y.1.asIdeal := Ideal.map_mono y.2.1
          _ = ((primeSpectrum_localization_homeomorph M).symm ⟨y.1, hyM⟩).asIdeal := by
                symm
                simp [hyM, primeSpectrum_localization_homeomorph_symm_apply_asIdeal])
    · -- The same comparison on the upper endpoint keeps the inverse point inside the interval.
      exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
        calc
          ((primeSpectrum_localization_homeomorph M).symm ⟨y.1, hyM⟩).asIdeal =
              Ideal.map (algebraMap R (Localization M)) y.1.asIdeal := by
                simp [hyM, primeSpectrum_localization_homeomorph_symm_apply_asIdeal]
          _ ≤ Ideal.map (algebraMap R (Localization M))
              (PrimeSpectrum.comap (algebraMap R (Localization M)) q).asIdeal := Ideal.map_mono y.2.2
          _ = q.asIdeal := by
                rw [PrimeSpectrum.comap_asIdeal]
                exact IsLocalization.map_comap M (Localization M) q.asIdeal)
  left_inv x := by
    apply Subtype.ext
    let hxM :
        Disjoint (M : Set R)
          (PrimeSpectrum.comap (algebraMap R (Localization M)) x.1).asIdeal := by
      have hx_ne_top : x.1.asIdeal ≠ ⊤ := x.1.2.1
      simpa [PrimeSpectrum.comap_asIdeal] using
        (IsLocalization.disjoint_comap_iff M (Localization M) x.1.asIdeal).2 hx_ne_top
    have hSubtype :
        ⟨PrimeSpectrum.comap (algebraMap R (Localization M)) x.1, hxM⟩ =
          primeSpectrum_localization_homeomorph M x.1 := by
      apply Subtype.ext
      simp [primeSpectrum_localization_homeomorph_apply]
    -- Replace the subtype point by the forward localization homeomorphism and cancel.
    change (primeSpectrum_localization_homeomorph M).symm
        ⟨PrimeSpectrum.comap (algebraMap R (Localization M)) x.1, hxM⟩ = x.1
    rw [hSubtype]
    exact (primeSpectrum_localization_homeomorph M).symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    let hqM :
        Disjoint (M : Set R)
          (PrimeSpectrum.comap (algebraMap R (Localization M)) q).asIdeal := by
      have hq_ne_top : q.asIdeal ≠ ⊤ := q.2.1
      simpa [PrimeSpectrum.comap_asIdeal] using
        (IsLocalization.disjoint_comap_iff M (Localization M) q.asIdeal).2 hq_ne_top
    let hyM : Disjoint (M : Set R) y.1.asIdeal :=
      disjoint_of_le_comap (M := M) (p := y.1)
        (q := PrimeSpectrum.comap (algebraMap R (Localization M)) q) hqM y.2.2
    -- Apply the forward localization homeomorphism to the explicit inverse point.
    change PrimeSpectrum.comap (algebraMap R (Localization M))
        ((primeSpectrum_localization_homeomorph M).symm ⟨y.1, hyM⟩) = y.1
    exact congrArg Subtype.val
      ((primeSpectrum_localization_homeomorph M).apply_symm_apply ⟨y.1, hyM⟩)
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      -- Reflect interval order through extension of prime ideals.
      exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
        calc
          x.1.asIdeal = Ideal.map (algebraMap R (Localization M))
              (PrimeSpectrum.comap (algebraMap R (Localization M)) x.1).asIdeal := by
                rw [PrimeSpectrum.comap_asIdeal]
                exact (IsLocalization.map_comap M (Localization M) x.1.asIdeal).symm
          _ ≤ Ideal.map (algebraMap R (Localization M))
              (PrimeSpectrum.comap (algebraMap R (Localization M)) y.1).asIdeal := by
                exact Ideal.map_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 h)
          _ = y.1.asIdeal := by
                rw [PrimeSpectrum.comap_asIdeal]
                exact IsLocalization.map_comap M (Localization M) y.1.asIdeal)
    · intro h
      -- Monotonicity of ideal contraction gives the forward implication.
      exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
        change Ideal.comap (algebraMap R (Localization M)) x.1.asIdeal ≤
            Ideal.comap (algebraMap R (Localization M)) y.1.asIdeal
        exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 h))

/-- Helper for Lemma 10.105.4: codimension in the localization equals codimension in the ambient
spectrum between the contracted generic points. -/
private theorem localization_codim_transport (M : Submonoid R)
    {p q : PrimeSpectrum (Localization M)} (hpq : p ≤ q) :
    codimBetween
        (show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) q)
        (show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) p)
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).monotone hpq) =
      codimBetween
        (show IrreducibleCloseds (PrimeSpectrum R) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds R
            (PrimeSpectrum.comap (algebraMap R (Localization M)) q))
        (show IrreducibleCloseds (PrimeSpectrum R) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds R
            (PrimeSpectrum.comap (algebraMap R (Localization M)) p))
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone <| by
          exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
            rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
            exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 hpq))) := by
  let T : IrreducibleCloseds (PrimeSpectrum (Localization M)) :=
    show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) q
  let T' : IrreducibleCloseds (PrimeSpectrum (Localization M)) :=
    show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) p
  let U : IrreducibleCloseds (PrimeSpectrum R) :=
    show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R
        (PrimeSpectrum.comap (algebraMap R (Localization M)) q)
  let U' : IrreducibleCloseds (PrimeSpectrum R) :=
    show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R
        (PrimeSpectrum.comap (algebraMap R (Localization M)) p)
  let eLoc :=
    orderIso_interval
      (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm
      (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) p)
      (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) q)
  let eSrc :=
    orderIso_interval
      (PrimeSpectrum.pointsEquivIrreducibleCloseds R)
      (PrimeSpectrum.comap (algebraMap R (Localization M)) p)
      (PrimeSpectrum.comap (algebraMap R (Localization M)) q)
  -- Compare both codimensions through the Krull dimensions of the corresponding intervals.
  apply WithBot.coe_injective
  calc
    codimBetween T T' ((PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).monotone hpq) =
        Order.krullDim (Set.Icc T T') :=
      codimBetween_eq_krullDim _
    _ = Order.krullDim ((Set.Icc T T')ᵒᵈ) := by
      exact (Order.krullDim_orderDual (α := Set.Icc T T')).symm
    _ =
        Order.krullDim
          (Set.Icc
            (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T')
            (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T)) :=
      Order.krullDim_eq_of_orderIso (dual_orderIso_interval T T')
    _ =
        Order.krullDim
          (Set.Icc
            ((PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm
              (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) p))
            ((PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm
              (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) q))) :=
      by
        exact Order.krullDim_eq_of_orderIso eLoc
    _ = Order.krullDim (Set.Icc p q) := by
      rw [(PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm_apply_apply p]
      rw [(PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm_apply_apply q]
    _ =
        Order.krullDim
          (Set.Icc
            (PrimeSpectrum.comap (algebraMap R (Localization M)) p)
            (PrimeSpectrum.comap (algebraMap R (Localization M)) q)) :=
      Order.krullDim_eq_of_orderIso (localization_prime_interval_order_iso M p q)
    _ =
        Order.krullDim
          (Set.Icc
            (show (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from U')
            (show (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from U)) :=
      by simpa [U, U'] using Order.krullDim_eq_of_orderIso eSrc
    _ = Order.krullDim ((Set.Icc U U')ᵒᵈ) :=
      Order.krullDim_eq_of_orderIso (dual_orderIso_interval U U').symm
    _ = Order.krullDim (Set.Icc U U') :=
      Order.krullDim_orderDual
    _ = codimBetween U U' ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone <| by
          exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
            rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
            exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 hpq))) :=
      (codimBetween_eq_krullDim _).symm

/-- Helper for Lemma 10.105.4: ring equivalences preserve catenarity. -/
private theorem isCatenaryRing_of_ringEquiv {A : Type v} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [IsCatenaryRing A] :
    IsCatenaryRing B := by
  -- Transport the catenary-space structure across the induced homeomorphism on spectra.
  simpa [IsCatenaryRing] using
    (PrimeSpectrum.homeomorphOfRingEquiv e).catenarySpace

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)`
- ring owner: `IsCatenaryRing R`
- universal owner: `UniversallyCatenaryRing R`
- layer here: `bridge/view`, since this item records localization stability of the existing owners

Primitive data already belongs to the owner abstractions from `Lemma_10_105_2` and
`Definition_10_105_3`; this file should only expose the localization instances.
-/

/-- Lemma 10.105.4 (1): any localization of a catenary ring is catenary. -/
-- Proof sketch: identify `Spec(Localization M)` with the subspace of `Spec(R)` consisting of
-- primes disjoint from `M`; catenarity is preserved under this localization subspace
-- identification.
instance localization_isCatenaryRing (M : Submonoid R) [IsCatenaryRing R] :
    IsCatenaryRing (Localization M) := by
  rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
  rw [catenarySpace_iff_finite_codimBetween_and_codimBetween_additive]
  refine ⟨?_, ?_⟩
  · intro T T' hTT'
    let p : PrimeSpectrum (Localization M) :=
      (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm
        (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T')
    let q : PrimeSpectrum (Localization M) :=
      (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm
        (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T)
    let U : IrreducibleCloseds (PrimeSpectrum R) :=
      show IrreducibleCloseds (PrimeSpectrum R) from
        PrimeSpectrum.pointsEquivIrreducibleCloseds R
          (PrimeSpectrum.comap (algebraMap R (Localization M)) q)
    let U' : IrreducibleCloseds (PrimeSpectrum R) :=
      show IrreducibleCloseds (PrimeSpectrum R) from
        PrimeSpectrum.pointsEquivIrreducibleCloseds R
          (PrimeSpectrum.comap (algebraMap R (Localization M)) p)
    have hpq : p ≤ q := by
      -- Translate the interval of irreducible closed subsets back to a prime interval.
      exact (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm.monotone
        (show (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T') ≤
            (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T) by
          exact hTT')
    have hUU' : U ≤ U' := by
      exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone <| by
        exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
          rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
          exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 hpq))
    have hT :
        (show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) q) = T := by
      simpa [q] using
        (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).apply_symm_apply
          (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T)
    have hT' :
        (show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) p) = T' := by
      simpa [p] using
        (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).apply_symm_apply
          (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T')
    have hcodim :
        codimBetween T T' hTT' = codimBetween U U' hUU' := by
      simpa [p, q, U, U', hT, hT', hUU'] using
        localization_codim_transport (R := R) M hpq
    -- Transport the ambient finite codimension statement back through the interval comparison.
    have hfinite : codimBetween U U' hUU' < ⊤ :=
      CatenarySpace.finite_codimBetween hUU'
    simpa [hcodim] using hfinite
  · intro T T' T'' hTT' hT'T''
    let p : PrimeSpectrum (Localization M) :=
      (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm
        (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T'')
    let q : PrimeSpectrum (Localization M) :=
      (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm
        (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T')
    let r : PrimeSpectrum (Localization M) :=
      (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm
        (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T)
    let U : IrreducibleCloseds (PrimeSpectrum R) :=
      show IrreducibleCloseds (PrimeSpectrum R) from
        PrimeSpectrum.pointsEquivIrreducibleCloseds R
          (PrimeSpectrum.comap (algebraMap R (Localization M)) r)
    let U' : IrreducibleCloseds (PrimeSpectrum R) :=
      show IrreducibleCloseds (PrimeSpectrum R) from
        PrimeSpectrum.pointsEquivIrreducibleCloseds R
          (PrimeSpectrum.comap (algebraMap R (Localization M)) q)
    let U'' : IrreducibleCloseds (PrimeSpectrum R) :=
      show IrreducibleCloseds (PrimeSpectrum R) from
        PrimeSpectrum.pointsEquivIrreducibleCloseds R
          (PrimeSpectrum.comap (algebraMap R (Localization M)) p)
    have hpq : p ≤ q := by
      exact (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm.monotone
        (show (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T'') ≤
            (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T') by
          exact hT'T'')
    have hqr : q ≤ r := by
      exact (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).symm.monotone
        (show (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T') ≤
            (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T) by
          exact hTT')
    have hpr : p ≤ r := hpq.trans hqr
    have hUU' : U ≤ U' := by
      exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone <| by
        exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
          rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
          exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 hqr))
    have hU'U'' : U' ≤ U'' := by
      exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone <| by
        exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <| by
          rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
          exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 hpq))
    have hUU'' : U ≤ U'' := hUU'.trans hU'U''
    have hT :
        (show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) r) = T := by
      simpa [r] using
        (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).apply_symm_apply
          (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T)
    have hT' :
        (show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) q) = T' := by
      simpa [q] using
        (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).apply_symm_apply
          (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T')
    have hT'' :
        (show IrreducibleCloseds (PrimeSpectrum (Localization M)) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M) p) = T'' := by
      simpa [p] using
        (PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization M)).apply_symm_apply
          (show (IrreducibleCloseds (PrimeSpectrum (Localization M)))ᵒᵈ from T'')
    have hcodim01 :
        codimBetween T T' hTT' = codimBetween U U' hUU' := by
      simpa [q, r, U, U', hT, hT', hUU'] using
        localization_codim_transport (R := R) M hqr
    have hcodim12 :
        codimBetween T' T'' hT'T'' = codimBetween U' U'' hU'U'' := by
      simpa [p, q, U', U'', hT', hT'', hU'U''] using
        localization_codim_transport (R := R) M hpq
    have hcodim02 :
        codimBetween T T'' (hTT'.trans hT'T'') = codimBetween U U'' hUU'' := by
      simpa [p, r, U, U'', hT, hT'', hUU''] using
        localization_codim_transport (R := R) M hpr
    -- Use additivity in the ambient spectrum after transporting all three codimensions.
    have hadd :
        codimBetween U U'' hUU'' =
          codimBetween U U' hUU' + codimBetween U' U'' hU'U'' :=
      CatenarySpace.codimBetween_additive hUU' hU'U''
    simpa [hcodim01, hcodim12, hcodim02] using hadd

/-- Helper for Lemma 10.105.4: a finite-type witness subalgebra inside an essentially finite type
algebra over a universally catenary ring is catenary. -/
private theorem essFiniteType_witness_carrier_isCatenary {A : Type v}
    [CommRing A] [Algebra R A] [UniversallyCatenaryRing.{u, v} R]
    {S₀ : Subalgebra R A} [Algebra.FiniteType R S₀] : IsCatenaryRing S₀ := by
  -- Route correction: apply universal catenarity to the witness carrier `S₀`, not to a bundled
  -- subalgebra term whose universe metadata obscures the intended `Type v` argument.
  let A₀ : Type v := S₀
  change IsCatenaryRing A₀
  exact (inferInstance : UniversallyCatenaryRing R).catenary_of_finiteType

/-- Helper for Lemma 10.105.4: the localization witness for an essentially finite type algebra
produces a canonical ring equivalence from the witness localization to the target algebra. -/
private noncomputable def essFiniteType_witness_localization_equiv {A : Type v}
    [CommRing A] [Algebra R A] {S₀ : Subalgebra R A} (M₀ : Submonoid S₀)
    [IsLocalization M₀ A] : Localization M₀ ≃+* A :=
  (IsLocalization.algEquiv M₀ (Localization M₀) A).toRingEquiv

/-- Helper for Lemma 10.105.4: essentially finite type algebras over a universally catenary ring
are catenary. -/
private theorem isCatenaryRing_of_essFiniteType {A : Type v}
    [CommRing A] [Algebra R A] [UniversallyCatenaryRing.{u, v} R]
    [Algebra.EssFiniteType R A] : IsCatenaryRing A := by
  obtain ⟨S₀, M₀, hft, hloc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra (R := R) (S := A)).1 inferInstance
  letI : Algebra.FiniteType R S₀ := hft
  letI : IsLocalization M₀ A := hloc
  -- First make the finite-type witness ring catenary by universal catenarity of the base.
  letI : IsCatenaryRing S₀ := essFiniteType_witness_carrier_isCatenary (R := R) (S₀ := S₀)
  -- Then localize the witness ring and transport that catenary structure back to `A`.
  letI : IsCatenaryRing (Localization M₀) := localization_isCatenaryRing (R := S₀) M₀
  exact isCatenaryRing_of_ringEquiv
    (essFiniteType_witness_localization_equiv (R := R) (A := A) (S₀ := S₀) M₀)

/-- Lemma 10.105.4 (2): any localization of a Noetherian universally catenary ring is
universally catenary. -/
-- Proof sketch: if `A` is a finite type algebra over `Localization M`, then `A` is a localization
-- of some finite type `R`-algebra. Apply universal catenarity over `R` to that finite type
-- algebra, then use the first localization statement.
instance localization_universallyCatenaryRing (M : Submonoid R)
    [UniversallyCatenaryRing.{u, v} R] : UniversallyCatenaryRing.{u, v} (Localization M) := by
  refine ⟨?_⟩
  intro A _ _ _
  -- Compose the localization witness `R → Localization M` with the current finite-type algebra
  -- over `Localization M` to recover an essentially finite type `R`-algebra.
  letI : Algebra R A :=
    (RingHom.comp (algebraMap (Localization M) A) (algebraMap R (Localization M))).toAlgebra
  letI : IsScalarTower R (Localization M) A := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.EssFiniteType R (Localization M) :=
    Algebra.EssFiniteType.of_isLocalization (S := Localization M) M
  letI : Algebra.EssFiniteType (Localization M) A := inferInstance
  letI : Algebra.EssFiniteType R A :=
    Algebra.EssFiniteType.comp (R := R) (S := Localization M) (T := A)
  -- The previous helper closes the catenary claim exactly in the shape required by the class.
  exact isCatenaryRing_of_essFiniteType (R := R) (A := A)

end

/-! ### Lemma_10_105_5 (from Chap10) -/
universe u v

section

variable (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-
Domain-style sampling in the universal-catenarity API:
- catenary ring owner: `IsCatenaryRing R`
- universally catenary owner: `UniversallyCatenaryRing R`
- essentially finite type owner: `Algebra.EssFiniteType R S`, with canonical witness API
  `Algebra.EssFiniteType.subalgebra`, `Algebra.EssFiniteType.submonoid`, and
  `Algebra.EssFiniteType.isLocalization`
- localization stability: `localization_universallyCatenaryRing`

Layer triage:
- `source-facing`: Lemma 10.105.5 says essential finite type extensions of universally catenary
  rings are universally catenary
- `core/canonical`: `UniversallyCatenaryRing`
- `bridge/view`: `Algebra.EssFiniteType` presents `B` as a localization of the canonical finite
  type subalgebra `Algebra.EssFiniteType.subalgebra A B`

Primitive data belongs to the existing owners `UniversallyCatenaryRing` and
`Algebra.EssFiniteType`; this file should only provide the bridge theorem, not a second catenary
owner API. Since the source ring of an essentially finite type algebra is additional algebra data
not determined by the target ring `B`, Lean cannot expose this bridge as a global
`UniversallyCatenaryRing B` instance without a separate owner carrying that source data.
-/

/-- Helper for Lemma 10.105.5: a finite type algebra over a universally catenary ring is again
universally catenary. -/
theorem universallyCatenaryRing_of_finiteType {S : Type v} [CommRing S] [Algebra A S]
    [UniversallyCatenaryRing.{u, v} A] [Algebra.FiniteType A S] :
    UniversallyCatenaryRing.{v, v} S := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  refine { catenary_of_finiteType := ?_ }
  intro C _ _ _
  letI : Algebra A C := RingHom.toAlgebra ((algebraMap S C).comp (algebraMap A S))
  letI : IsScalarTower A S C := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  -- Compose the two finite type algebra structures back to the original base ring `A`.
  have hfinite : Algebra.FiniteType A C :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A S) inferInstance
  letI : Algebra.FiniteType A C := hfinite
  -- Universal catenarity of `A` now applies directly to the composed finite type algebra.
  exact (inferInstance : UniversallyCatenaryRing.{u, v} A).catenary_of_finiteType

/-- Helper for Lemma 10.105.5: universal catenarity transports across a ring equivalence. -/
theorem universallyCatenaryRing_of_ringEquiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S) [UniversallyCatenaryRing.{u, v} R] :
    UniversallyCatenaryRing.{v, v} S := by
  letI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  refine { catenary_of_finiteType := ?_ }
  intro T _ _ _
  letI : Algebra R S := RingHom.toAlgebra e.toRingHom
  letI : Algebra R T := RingHom.toAlgebra ((algebraMap S T).comp e.toRingHom)
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  -- Regard `S` and then `T` as algebras over `R` through the equivalence `e`.
  have hRS : Algebra.FiniteType R S := by
    let eAlg : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun x ↦ rfl
    exact Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType R R) eAlg
  have hRT : Algebra.FiniteType R T :=
    Algebra.FiniteType.trans hRS inferInstance
  letI : Algebra.FiniteType R T := hRT
  -- The target `T` is finite type over `R`, so universal catenarity descends from `R`.
  exact (inferInstance : UniversallyCatenaryRing.{u, v} R).catenary_of_finiteType

/-- Helper for Lemma 10.105.5: the canonical witness localization for an essentially finite type
`A`-algebra identifies with the algebra itself. -/
noncomputable def essFiniteType_witness_localization_ringEquiv [Algebra.EssFiniteType A B] :
    Localization (Algebra.EssFiniteType.submonoid A B) ≃+* B :=
  (IsLocalization.algEquiv (Algebra.EssFiniteType.submonoid A B)
    (Localization (Algebra.EssFiniteType.submonoid A B)) B).toRingEquiv

/-- Lemma 10.105.5: any `A`-algebra essentially of finite type over a universally catenary
ring `A` is universally catenary. -/
-- Proof sketch: let `B₀ := Algebra.EssFiniteType.subalgebra A B`; then `B₀` is a finite type
-- `A`-algebra, hence universally catenary by the finite-type case applied twice. The ambient ring
-- `B` is the localization of `B₀` at the canonical submonoid
-- `Algebra.EssFiniteType.submonoid A B`, so Lemma `10.105.4 (2)` gives the result.
theorem universallyCatenaryRing_of_essFiniteType [UniversallyCatenaryRing.{u, v} A]
    [Algebra.EssFiniteType A B] : UniversallyCatenaryRing.{v, v} B := by
  let B₀ := Algebra.EssFiniteType.subalgebra A B
  let M₀ := Algebra.EssFiniteType.submonoid A B
  -- First prove the finite type witness subalgebra is universally catenary.
  have hB₀ : UniversallyCatenaryRing.{v, v} B₀ := by
    exact universallyCatenaryRing_of_finiteType (A := A) (S := B₀)
  letI : UniversallyCatenaryRing.{v, v} B₀ := hB₀
  letI : UniversallyCatenaryRing.{v, v} (Localization M₀) := localization_universallyCatenaryRing M₀
  -- The source proof finishes by transporting the localization result along the canonical witness
  -- equivalence `Localization M₀ ≃+* B`.
  exact universallyCatenaryRing_of_ringEquiv
    (essFiniteType_witness_localization_ringEquiv (A := A) (B := B))

end

/-! ### Lemma_10_105_6 (from Chap10) -/
noncomputable section

open TopologicalSpace PrimeSpectrum IsLocalization.AtPrime

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)` from `Chap05/Definition_5_11_4`
- ring owner: `IsCatenaryRing R` from `Lemma_10_105_2`
- universal owner: `UniversallyCatenaryRing R` from `Definition_10_105_3`
- localization bridge: `localization_isCatenaryRing` and
  `localization_universallyCatenaryRing` from `Lemma_10_105_4`

Layer triage:
- `source-facing`: Lemma 10.105.6 records the prime-local and maximal-local TFAE criteria
- `core/canonical`: `IsCatenaryRing` and `UniversallyCatenaryRing`
- `bridge/view`: the localization predicates below are derived from the canonical owner instances

Primitive data already belongs to the upstream owner abstractions, so this file should only expose
the TFAE bridge and should not duplicate the catenary owner definitions locally.
-/

/-- Helper for Lemma 10.105.6: an order isomorphism restricts to the corresponding closed
intervals. -/
private noncomputable def orderIso_interval {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (a b : α) : Set.Icc a b ≃o Set.Icc (e a) (e b) where
  toFun x := ⟨e x.1, e.monotone x.2.1, e.monotone x.2.2⟩
  invFun y := ⟨e.symm y.1, by
    simpa using e.symm.monotone y.2.1, by
    simpa using e.symm.monotone y.2.2⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_rel_iff' := by
    intro x y
    simpa using e.le_iff_le

/-- Helper for Lemma 10.105.6: forgetting a subtype condition identifies the corresponding
interval in the subtype with the ambient interval. -/
private noncomputable def subtype_interval_orderIso {α : Type*} [Preorder α]
    {P : α → Prop} {a b : α} (ha : P a) (hb : P b)
    (hP : ∀ ⦃x : α⦄, a ≤ x → x ≤ b → P x) :
    Set.Icc (⟨a, ha⟩ : { x : α // P x }) ⟨b, hb⟩ ≃o Set.Icc a b where
  toFun x := ⟨x.1.1, x.2.1, x.2.2⟩
  invFun x := ⟨⟨x.1, hP x.2.1 x.2.2⟩, x.2.1, x.2.2⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Lemma 10.105.6: catenarity transports across ring equivalences. -/
private theorem isCatenaryRing_of_ringEquiv {A : Type v} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [IsCatenaryRing A] :
    IsCatenaryRing B := by
  -- Transport the catenary-space structure through the induced homeomorphism on spectra.
  simpa [IsCatenaryRing] using
    (PrimeSpectrum.homeomorphOfRingEquiv e).catenarySpace

/-- Helper for Lemma 10.105.6: irreducible closed subsets of `Spec(R_𝔭)` identify with ambient
irreducible closed subsets of `Spec R` containing `𝔭`. -/
private noncomputable def localizationAtPrimeIrreducibleClosedsSubtypeOrderIso
    (p : PrimeSpectrum R) :
    IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ≃o
      { Z : IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R)) } :=
  ((PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization.AtPrime p.asIdeal)).symm.trans
    (PrimeSpectrum.localizationAtPrimeIrreducibleCloseds p)).dual

/-- Helper for Lemma 10.105.6: the localization preimages of comparable irreducible closed sets
remain comparable. -/
private theorem localizationAtPrime_preimage_le (p : PrimeSpectrum R)
    {T T' : IrreducibleCloseds (PrimeSpectrum R)}
    (hpT : p ∈ (T : Set (PrimeSpectrum R)))
    (hpT' : p ∈ (T' : Set (PrimeSpectrum R)))
    (hTT' : T ≤ T') :
    (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T, hpT⟩ ≤
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T', hpT'⟩ := by
  -- Compare in the subtype first, then transport back through the order isomorphism.
  exact
    (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm.monotone hTT'

/-- Helper for Lemma 10.105.6: localizing at a point of the smaller irreducible closed set
preserves the codimension of the interval. -/
private theorem localizationAtPrime_codim_transport (p : PrimeSpectrum R)
    {T T' : IrreducibleCloseds (PrimeSpectrum R)}
    (hpT : p ∈ (T : Set (PrimeSpectrum R)))
    (hpT' : p ∈ (T' : Set (PrimeSpectrum R)))
    (hTT' : T ≤ T') :
    codimBetween
        ((localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T, hpT⟩)
        ((localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T', hpT'⟩)
        (localizationAtPrime_preimage_le (R := R) p hpT hpT' hTT') =
      codimBetween T T' hTT' := by
  let e := localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p
  let TU : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) := e.symm ⟨T, hpT⟩
  let T'U : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) := e.symm ⟨T', hpT'⟩
  let eSub :
      Set.Icc (⟨T, hpT⟩ : { Z : IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) }) ⟨T', hpT'⟩ ≃o
        Set.Icc T T' :=
    subtype_interval_orderIso
      (P := fun Z : IrreducibleCloseds (PrimeSpectrum R) ↦ p ∈ (Z : Set (PrimeSpectrum R)))
      (a := T) (b := T') hpT hpT' fun {_} hTZ _ ↦ hTZ hpT
  -- Compare both codimensions through the Krull dimensions of the corresponding intervals.
  apply WithBot.coe_injective
  have heTU :
      e TU =
        (⟨T, hpT⟩ : { Z : IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) }) := by
    simp [e, TU]
  have heT'U :
      e T'U =
        (⟨T', hpT'⟩ : { Z : IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) }) := by
    simp [e, T'U]
  calc
    codimBetween TU T'U (localizationAtPrime_preimage_le (R := R) p hpT hpT' hTT') =
        Order.krullDim (Set.Icc TU T'U) :=
      codimBetween_eq_krullDim _
    _ = Order.krullDim (Set.Icc (e TU) (e T'U)) :=
      Order.krullDim_eq_of_orderIso (orderIso_interval e TU T'U)
    _ =
        Order.krullDim
          (Set.Icc
            (⟨T, hpT⟩ : { Z : IrreducibleCloseds (PrimeSpectrum R) //
              p ∈ (Z : Set (PrimeSpectrum R)) })
            ⟨T', hpT'⟩) := by
      rw [heTU, heT'U]
    _ = Order.krullDim (Set.Icc T T') :=
      Order.krullDim_eq_of_orderIso eSub
    _ = codimBetween T T' hTT' :=
      (codimBetween_eq_krullDim _).symm

/-- Helper for Lemma 10.105.6: if every prime localization is catenary, then `R` is catenary. -/
private theorem isCatenaryRing_of_forall_prime_localizations
    (hlocal : ∀ p : PrimeSpectrum R, IsCatenaryRing (Localization.AtPrime p.asIdeal)) :
    IsCatenaryRing R := by
  rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
  rw [catenarySpace_iff_finite_codimBetween_and_codimBetween_additive]
  refine ⟨?_, ?_⟩
  · intro T T' hTT'
    -- Choose a point of the smaller irreducible closed set so both ends of the interval contain it.
    obtain ⟨p, hpT⟩ := T.isIrreducible.nonempty
    have hpT' : p ∈ (T' : Set (PrimeSpectrum R)) := hTT' hpT
    letI : IsCatenaryRing (Localization.AtPrime p.asIdeal) := hlocal p
    let TU : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T, hpT⟩
    let T'U : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T', hpT'⟩
    let hTUU : TU ≤ T'U :=
      localizationAtPrime_preimage_le (R := R) p hpT hpT' hTT'
    have hcodim :
        codimBetween TU T'U hTUU = codimBetween T T' hTT' := by
      simpa [TU, T'U, hTUU] using
        localizationAtPrime_codim_transport (R := R) p hpT hpT' hTT'
    -- Apply catenarity in the chosen prime localization and transport the codimension back.
    have hfinite : codimBetween TU T'U hTUU < ⊤ :=
      CatenarySpace.finite_codimBetween hTUU
    simpa [hcodim] using hfinite
  · intro T T' T'' hTT' hT'T''
    -- The same point of the smallest irreducible closed set lies in the whole interval.
    obtain ⟨p, hpT⟩ := T.isIrreducible.nonempty
    have hpT' : p ∈ (T' : Set (PrimeSpectrum R)) := hTT' hpT
    have hpT'' : p ∈ (T'' : Set (PrimeSpectrum R)) := hT'T'' hpT'
    letI : IsCatenaryRing (Localization.AtPrime p.asIdeal) := hlocal p
    let TU : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T, hpT⟩
    let T'U : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T', hpT'⟩
    let T''U : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T'', hpT''⟩
    let hTT'U : TU ≤ T'U :=
      localizationAtPrime_preimage_le (R := R) p hpT hpT' hTT'
    let hT'T''U : T'U ≤ T''U :=
      localizationAtPrime_preimage_le (R := R) p hpT' hpT'' hT'T''
    let hTT''U : TU ≤ T''U :=
      localizationAtPrime_preimage_le (R := R) p hpT hpT'' (hTT'.trans hT'T'')
    have hcodim01 :
        codimBetween TU T'U hTT'U = codimBetween T T' hTT' := by
      simpa [TU, T'U, hTT'U] using
        localizationAtPrime_codim_transport (R := R) p hpT hpT' hTT'
    have hcodim12 :
        codimBetween T'U T''U hT'T''U = codimBetween T' T'' hT'T'' := by
      simpa [T'U, T''U, hT'T''U] using
        localizationAtPrime_codim_transport (R := R) p hpT' hpT'' hT'T''
    have hcodim02 :
        codimBetween TU T''U hTT''U = codimBetween T T'' (hTT'.trans hT'T'') := by
      simpa [TU, T''U, hTT''U] using
        localizationAtPrime_codim_transport (R := R) p hpT hpT'' (hTT'.trans hT'T'')
    -- Additivity holds in the localization and therefore in the original interval.
    have hadd :
        codimBetween TU T''U hTT''U =
          codimBetween TU T'U hTT'U + codimBetween T'U T''U hT'T''U :=
      CatenarySpace.codimBetween_additive hTT'U hT'T''U
    simpa [hcodim01, hcodim12, hcodim02] using hadd

/-- Helper for Lemma 10.105.6: for `𝔭 ⊆ 𝔪`, this is the corresponding prime of `Spec(R_𝔪)`. -/
private noncomputable abbrev localization_prime_of_le_maximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum) :
    PrimeSpectrum (Localization.AtPrime m.asIdeal) :=
  (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime m.asIdeal) m.asIdeal).symm
    ⟨p, hpm⟩

/-- Helper for Lemma 10.105.6: the prime chosen in `Spec(R_𝔪)` contracts back to `𝔭`. -/
private theorem localization_prime_of_le_maximal_comap
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum) :
    PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal))
      (localization_prime_of_le_maximal (R := R) p m hpm) = p := by
  -- Unpack the prime-spectrum order isomorphism defining the point of `Spec(R_𝔪)`.
  change
    ((IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime m.asIdeal) m.asIdeal)
      (localization_prime_of_le_maximal (R := R) p m hpm)).1 = p
  simp [localization_prime_of_le_maximal]

/-- Helper for Lemma 10.105.6: the corresponding prime of `Spec(R_𝔪)` has contracted ideal
`𝔭.asIdeal`. -/
private theorem localization_prime_of_le_maximal_comap_asIdeal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum) :
    Ideal.comap (algebraMap R (Localization.AtPrime m.asIdeal))
      (localization_prime_of_le_maximal (R := R) p m hpm).asIdeal = p.asIdeal := by
  -- Pass from the prime-spectrum equality to the underlying ideal equality.
  simpa [PrimeSpectrum.comap_asIdeal] using
    congrArg PrimeSpectrum.asIdeal
      (localization_prime_of_le_maximal_comap (R := R) p m hpm)

/-- Helper for Lemma 10.105.6: the iterated localization `(R_𝔪)_𝔮` is a localization of `R` at
`𝔭` when `𝔮` is the prime of `Spec(R_𝔪)` corresponding to `𝔭 ⊆ 𝔪`. -/
private theorem isLocalizationAtPrime_of_le_maximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum) :
    IsLocalization.AtPrime
      (Localization.AtPrime (localization_prime_of_le_maximal (R := R) p m hpm).asIdeal)
      p.asIdeal := by
  -- Apply the standard iterated-localization theorem after identifying the contracted prime.
  simpa [localization_prime_of_le_maximal_comap_asIdeal (R := R) p m hpm] using
    (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := m.asIdeal.primeCompl)
      (T := Localization.AtPrime (localization_prime_of_le_maximal (R := R) p m hpm).asIdeal)
      (localization_prime_of_le_maximal (R := R) p m hpm).asIdeal)

/-- Helper for Lemma 10.105.6: catenarity descends from `R_𝔪` to `R_𝔭` whenever `𝔭 ⊆ 𝔪`. -/
private theorem isCatenaryRing_localizationAtPrime_of_le_maximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum)
    [IsCatenaryRing (Localization.AtPrime m.asIdeal)] :
    IsCatenaryRing (Localization.AtPrime p.asIdeal) := by
  let q := localization_prime_of_le_maximal (R := R) p m hpm
  -- Localize the maximal localization once more at the corresponding prime.
  letI : IsCatenaryRing (Localization.AtPrime q.asIdeal) :=
    localization_isCatenaryRing (R := Localization.AtPrime m.asIdeal) q.asIdeal.primeCompl
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal :=
    isLocalizationAtPrime_of_le_maximal (R := R) p m hpm
  let e : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).toRingEquiv
  -- Then transport the catenary structure back along the canonical ring equivalence.
  exact isCatenaryRing_of_ringEquiv e.symm

/-- Lemma 10.105.6 (1): for a commutative ring `R`, the following are equivalent: `R` is
catenary, every localization `R_𝔭` at a prime ideal is catenary, and every localization `R_𝔪`
at a maximal ideal is catenary. -/
-- Proof sketch: `(1) → (2)` is Lemma `10.105.4`. `(2) → (3)` is immediate because maximal ideals
-- are prime. For `(3) → (1)`, compare chains of prime ideals between `𝔭 ⊆ 𝔮` in `R` with the
-- corresponding chains in a localization `R_𝔪` for a maximal ideal `𝔪` containing `𝔮`.
theorem isCatenaryRing_localization_tfae :
    List.TFAE
      [ IsCatenaryRing R,
        ∀ p : PrimeSpectrum R, IsCatenaryRing (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R, IsCatenaryRing (Localization.AtPrime m.asIdeal) ] := by
  tfae_have 1 → 2 := by
    intro hR p
    letI : IsCatenaryRing R := hR
    -- The prime-local clause is exactly the localization stability from Lemma 10.105.4.
    exact localization_isCatenaryRing (R := R) p.asIdeal.primeCompl
  tfae_have 2 → 3 := by
    intro h p
    -- Maximal ideals are prime, so this is just specialization of the previous clause.
    exact h p.toPrimeSpectrum
  tfae_have 3 → 1 := by
    intro h
    -- Route correction: first recover every prime localization from a maximal localization, and
    -- only then invoke the already-proved prime-local criterion.
    refine isCatenaryRing_of_forall_prime_localizations (R := R) ?_
    intro p
    obtain ⟨mI, hmI, hpmI⟩ := Ideal.exists_le_maximal p.asIdeal p.2.1
    let m : MaximalSpectrum R := ⟨mI, hmI⟩
    have hpm : p ≤ m.toPrimeSpectrum := by
      simpa using hpmI
    letI : IsCatenaryRing (Localization.AtPrime m.asIdeal) := h m
    -- The chosen maximal ideal supplies the source-faithful bridge `R_𝔪 → R_𝔭`.
    exact isCatenaryRing_localizationAtPrime_of_le_maximal (R := R) p m hpm
  tfae_finish

section

variable [IsNoetherianRing R]

/-- Helper for Lemma 10.105.6: a finite-type witness subalgebra inside an essentially finite type
algebra over a universally catenary ring is catenary. -/
private theorem essFiniteType_witness_carrier_isCatenary {A : Type v}
    [CommRing A] [Algebra R A] [UniversallyCatenaryRing.{u, v} R]
    {S₀ : Subalgebra R A} [Algebra.FiniteType R S₀] : IsCatenaryRing S₀ := by
  -- Evaluate the universal catenarity owner on the finite-type witness carrier.
  let A₀ : Type v := S₀
  change IsCatenaryRing A₀
  exact (inferInstance : UniversallyCatenaryRing R).catenary_of_finiteType

/-- Helper for Lemma 10.105.6: the localization witness for an essentially finite type algebra
produces the canonical ring equivalence from the witness localization to the target algebra. -/
private noncomputable def essFiniteType_witness_localization_equiv {A : Type v}
    [CommRing A] [Algebra R A] {S₀ : Subalgebra R A} (M₀ : Submonoid S₀)
    [IsLocalization M₀ A] : Localization M₀ ≃+* A :=
  (IsLocalization.algEquiv M₀ (Localization M₀) A).toRingEquiv

/-- Helper for Lemma 10.105.6: essentially finite type algebras over a universally catenary ring
are catenary. -/
private theorem isCatenaryRing_of_essFiniteType {A : Type v}
    [CommRing A] [Algebra R A] [UniversallyCatenaryRing.{u, v} R]
    [Algebra.EssFiniteType R A] : IsCatenaryRing A := by
  obtain ⟨S₀, M₀, hft, hloc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra (R := R) (S := A)).1 inferInstance
  letI : Algebra.FiniteType R S₀ := hft
  letI : IsLocalization M₀ A := hloc
  -- First make the finite-type witness catenary, then localize and transport back to `A`.
  letI : IsCatenaryRing S₀ := essFiniteType_witness_carrier_isCatenary (R := R) (S₀ := S₀)
  letI : IsCatenaryRing (Localization M₀) := localization_isCatenaryRing (R := S₀) M₀
  exact isCatenaryRing_of_ringEquiv
    (essFiniteType_witness_localization_equiv (R := R) (A := A) (S₀ := S₀) M₀)

/-- Helper for Lemma 10.105.6: universal catenarity transports across a ring equivalence. -/
private theorem universallyCatenaryRing_of_ringEquiv {A : Type u} {B : Type u}
    [CommRing A] [CommRing B] (e : A ≃+* B) [UniversallyCatenaryRing.{u, v} A] :
    UniversallyCatenaryRing.{u, v} B := by
  letI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e
  refine { catenary_of_finiteType := ?_ }
  intro T _ _ _
  letI : Algebra A B := RingHom.toAlgebra e.toRingHom
  letI : Algebra A T := RingHom.toAlgebra ((algebraMap B T).comp e.toRingHom)
  letI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  -- Regard finite type `B`-algebras as finite type `A`-algebras through the equivalence.
  have hAB : Algebra.FiniteType A B := by
    let eAlg : A ≃ₐ[A] B := AlgEquiv.ofRingEquiv (f := e) fun x ↦ rfl
    exact Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType A A) eAlg
  have hAT : Algebra.FiniteType A T := Algebra.FiniteType.trans hAB inferInstance
  letI : Algebra.FiniteType A T := hAT
  -- Universal catenarity on `A` now applies directly to the transported algebra structure.
  exact (inferInstance : UniversallyCatenaryRing.{u, v} A).catenary_of_finiteType

/-- Helper for Lemma 10.105.6: universal catenarity descends from `R_𝔪` to `R_𝔭` whenever
`𝔭 ⊆ 𝔪`. -/
private theorem universallyCatenaryRing_localizationAtPrime_of_le_maximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum)
    [UniversallyCatenaryRing.{u, v} (Localization.AtPrime m.asIdeal)] :
    UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal) := by
  let q := localization_prime_of_le_maximal (R := R) p m hpm
  -- Localize the universally catenary maximal localization at the corresponding prime.
  letI : UniversallyCatenaryRing.{u, v} (Localization.AtPrime q.asIdeal) :=
    localization_universallyCatenaryRing (R := Localization.AtPrime m.asIdeal) q.asIdeal.primeCompl
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal :=
    isLocalizationAtPrime_of_le_maximal (R := R) p m hpm
  let e : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).toRingEquiv
  -- Transport the universal owner back across the canonical ring equivalence.
  exact universallyCatenaryRing_of_ringEquiv e.symm

/-- Helper for Lemma 10.105.6: localizing a finite-type `R`-algebra `A` at `q` is essentially
finite type over the contracted base localization `R_(q ∩ R)`. -/
private theorem localizationAtPrime_essFiniteType_of_finiteType_contraction {A : Type v}
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (q : PrimeSpectrum A) :
    Algebra.EssFiniteType
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R A) q).asIdeal)
      (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
  letI : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    inferInstance
  letI : Algebra.EssFiniteType R (Localization.AtPrime q.asIdeal) := by
    infer_instance
  -- First view `A_𝔮` as essentially finite type over `R`, then restrict scalars to `R_𝔭`.
  exact Algebra.EssFiniteType.of_comp R (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal)

/-- Helper for Lemma 10.105.6: if the contracted base localization `R_(q ∩ R)` is universally
catenary, then the target localization `A_𝔮` is catenary. -/
private theorem isCatenaryRing_localizationAtPrime_of_finiteType_contraction {A : Type v}
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (q : PrimeSpectrum A)
    [UniversallyCatenaryRing.{u, v}
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R A) q).asIdeal)] :
    IsCatenaryRing (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
  letI : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    inferInstance
  letI : Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) :=
    localizationAtPrime_essFiniteType_of_finiteType_contraction (R := R) (A := A) q
  -- Apply the essentially-finite-type catenary bridge over the contracted base localization.
  exact isCatenaryRing_of_essFiniteType
    (R := Localization.AtPrime p.asIdeal) (A := Localization.AtPrime q.asIdeal)

/-- Helper for Lemma 10.105.6: if every prime localization is universally catenary, then `R` is
universally catenary. -/
private theorem universallyCatenaryRing_of_forall_prime_localizations
    (hlocal : ∀ p : PrimeSpectrum R,
      UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal)) :
    UniversallyCatenaryRing.{u, v} R := by
  refine { catenary_of_finiteType := ?_ }
  intro A _ _ _
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hAq :
      ∀ q : PrimeSpectrum A, IsCatenaryRing (Localization.AtPrime q.asIdeal) := by
    intro q
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
    letI : UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal) := hlocal p
    -- The source proof localizes the finite-type algebra at `q` over the contracted base `p`.
    exact isCatenaryRing_localizationAtPrime_of_finiteType_contraction
      (R := R) (A := A) q
  -- Once every prime localization of `A` is catenary, the first TFAE recovers `A` itself.
  exact ((isCatenaryRing_localization_tfae (R := A)).out 1 0 rfl rfl).mp hAq

/-- Lemma 10.105.6 (2): for a Noetherian commutative ring `R`, the following are equivalent:
`R` is universally catenary, every localization `R_𝔭` at a prime ideal is universally catenary,
and every localization `R_𝔪` at a maximal ideal is universally catenary. -/
-- Proof sketch: `(1) → (2)` is Lemma `10.105.4`. `(2) → (3)` is immediate. For `(3) → (1)`,
-- let `R → A` be a finite type algebra. Localizing at a prime `𝔮` of `A` above `𝔭 ⊆ R`, choose a
-- maximal ideal `𝔪` of `R` containing `𝔭`; then `R_𝔭` is a localization of `R_𝔪`, so `A_𝔮` is
-- catenary, and the first TFAE gives catenarity of `A`.
theorem universallyCatenaryRing_localization_tfae :
    List.TFAE
      [ UniversallyCatenaryRing.{u, v} R,
        ∀ p : PrimeSpectrum R, UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R, UniversallyCatenaryRing.{u, v} (Localization.AtPrime m.asIdeal) ] := by
  tfae_have 1 → 2 := by
    intro hR p
    letI : UniversallyCatenaryRing.{u, v} R := hR
    -- The prime-local clause is exactly localization stability from Lemma 10.105.4.
    exact localization_universallyCatenaryRing (R := R) p.asIdeal.primeCompl
  tfae_have 2 → 3 := by
    intro h m
    -- Maximal ideals are prime, so this is immediate from the prime-local clause.
    exact h m.toPrimeSpectrum
  tfae_have 3 → 1 := by
    intro h
    -- Route correction: first descend from maximal localizations to all prime localizations, and
    -- then apply the prime-local universal criterion proved above.
    refine universallyCatenaryRing_of_forall_prime_localizations (R := R) ?_
    intro p
    obtain ⟨mI, hmI, hpmI⟩ := Ideal.exists_le_maximal p.asIdeal p.2.1
    let m : MaximalSpectrum R := ⟨mI, hmI⟩
    have hpm : p ≤ m.toPrimeSpectrum := by
      simpa using hpmI
    letI : UniversallyCatenaryRing.{u, v} (Localization.AtPrime m.asIdeal) := h m
    -- The maximal-local hypothesis provides the source-faithful bridge `R_𝔪 → R_𝔭`.
    exact universallyCatenaryRing_localizationAtPrime_of_le_maximal (R := R) p m hpm
  tfae_finish

end

end

/-! ### Lemma_10_105_7 (from Chap10) -/
noncomputable section

open PrimeSpectrum
open scoped PrimeSpectrum

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)` from `Chap05/Definition_5_11_4`
- ring owner: `IsCatenaryRing R` from `Lemma_10_105_2`
- universal owner: `UniversallyCatenaryRing R` from `Definition_10_105_3`
- layer here: `bridge/view`, since this item records quotient stability of the existing owners

Primitive data already belongs to the owner abstractions from `Lemma_10_105_2` and
`Definition_10_105_3`; this file should only expose the quotient instances.
-/

/-- Helper for Lemma 10.105.7: if `R` is catenary, then the closed zero locus `V(I)` in
`Spec R` is catenary. -/
private theorem zeroLocus_catenarySpace_of_catenaryRing [IsCatenaryRing R] :
    CatenarySpace (V((I : Set R))) := by
  -- Closed subspaces of a catenary prime spectrum remain catenary.
  simpa using (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).catenarySpace_subtype

/-- Lemma 10.105.7 (1): any quotient of a catenary ring is catenary. -/
-- Proof sketch: by Lemma 10.17.7, `Spec (R ⧸ I)` is homeomorphic to the closed subset `V(I)` of
-- `Spec R`; closed subspaces of catenary spaces are catenary, so the quotient ring is catenary.
instance quotient_catenaryRing [IsCatenaryRing R] : IsCatenaryRing (R ⧸ I) := by
  rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
  -- First put the catenary structure on the closed zero locus, then transport along the
  -- canonical homeomorphism `Spec (R ⧸ I) ≃ₜ V(I)`.
  letI : CatenarySpace (V((I : Set R))) := zeroLocus_catenarySpace_of_catenaryRing (I := I)
  simpa using (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm.catenarySpace

/-- Lemma 10.105.7 (2): any quotient of a Noetherian universally catenary ring is universally
catenary. -/
-- Proof sketch: the quotient `R ⧸ I` is a finite type `R`-algebra via the quotient map. Any
-- finite type algebra over `R ⧸ I` is also a finite type algebra over `R`, so the universal
-- catenarity hypothesis on `R` gives catenarity after composing the algebra structures.
instance quotient_universallyCatenaryRing [UniversallyCatenaryRing.{u, v} R] :
    UniversallyCatenaryRing.{u, v} (R ⧸ I) := by
  refine { catenary_of_finiteType := ?_ }
  intro A _ _ _
  let f : R →+* A := (algebraMap (R ⧸ I) A).comp (Ideal.Quotient.mk I)
  letI : Algebra R A := RingHom.toAlgebra f
  letI : IsScalarTower R (R ⧸ I) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  have hfinite : Algebra.FiniteType R A :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R (R ⧸ I)) inferInstance
  exact (inferInstance : UniversallyCatenaryRing R).catenary_of_finiteType

end
