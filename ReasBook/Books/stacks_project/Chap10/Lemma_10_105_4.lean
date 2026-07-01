import Mathlib
import stacks_project.Chap05.Lemma_5_11_5
import stacks_project.Chap05.Lemma_5_11_6
import stacks_project.Chap10.Lemma_10_17_5
import stacks_project.Chap10.Definition_10_105_3

-- Declarations for this item will be appended below by the statement pipeline.

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
