import Mathlib
import stacks_project.Chap05.Definition_5_20_1
import stacks_project.Chap05.Lemma_5_20_2
import stacks_project.Chap05.Lemma_5_20_4
import stacks_project.Chap10.Lemma_10_105_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open IsLocalRing Order PrimeSpectrum TopologicalSpace

/- Domain-style sampling in the catenary/dimension-function API:
- ring owner: `IsCatenaryRing A`
- topological owner: `IsDimensionFunction δ`
- bridge/view: the source function `p ↦ dim (A / p)` on `Spec A`, expressed here through
  `ringKrullDim (A ⧸ p.asIdeal)`

Layer triage:
- `source-facing`: Lemma 10.105.10 is the local Noetherian criterion for catenarity
- `core/canonical`: the owner abstractions are already `IsCatenaryRing` and `IsDimensionFunction`
- `bridge/view`: the quotient-dimension function is derived API and should stay scoped to the
  Noetherian-local setting of the theorem, rather than as a global owner declaration

Primitive data belongs to the existing owner abstractions. The quotient-dimension expression is
kept inline below because `ringKrullDim` is `WithBot`-valued in general, so truncating it with
`unbotD 0` is only source-faithful in the finite-dimensional local setting of this lemma.
-/

section

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 10.105.10: catenarity near the closed point globalizes to a dimension
function normalized to vanish at that closed point. -/
private theorem exists_dimensionFunction_vanishing_at_closedPoint
    [IsNoetherianRing A] [IsLocalRing A] [IsCatenaryRing A] :
    ∃ δ : PrimeSpectrum A → ℤ, IsDimensionFunction δ ∧ δ (closedPoint A) = 0 := by
  -- Start with the local existence theorem at the closed point.
  obtain ⟨U, hclosed_mem, δU, hδU⟩ :=
    exists_open_neighborhood_with_dimensionFunction (X := PrimeSpectrum A) (closedPoint A)
  have hU : U = ⊤ := (closedPoint_mem_iff U).mp hclosed_mem
  subst hU
  let δBase : PrimeSpectrum A → ℤ :=
    fun p ↦ δU ⟨p, by simp⟩
  -- Transport the dimension function from the top open subset back to the ambient spectrum.
  have hδBase : IsDimensionFunction δBase := by
    refine
      { strict_of_specializes := ?_
        eq_add_one_of_immediateSpecialization := ?_ }
    · intro x y hxy hxy_ne
      have hxyU : (⟨x, by simp⟩ : (⊤ : Opens (PrimeSpectrum A))) ⤳ ⟨y, by simp⟩ := by
        simpa using (subtype_specializes_iff (x := ⟨x, by simp⟩) (y := ⟨y, by simp⟩)).2 hxy
      have hxyU_ne : (⟨x, by simp⟩ : (⊤ : Opens (PrimeSpectrum A))) ≠ ⟨y, by simp⟩ := by
        intro h
        exact hxy_ne (Subtype.ext_iff.mp h)
      simpa [δBase] using hδU.strict_of_specializes hxyU hxyU_ne
    · intro x y hxy
      have hxyU :
          IsImmediateSpecialization
            (⟨x, by simp⟩ : (⊤ : Opens (PrimeSpectrum A))) ⟨y, by simp⟩ := by
        refine ⟨?_, ?_, ?_⟩
        · simpa using
            (subtype_specializes_iff (x := ⟨x, by simp⟩) (y := ⟨y, by simp⟩)).2 hxy.specializes
        · intro h
          exact hxy.ne (Subtype.ext_iff.mp h)
        · intro z hxz hzy
          have hxz' : x ⤳ (z : PrimeSpectrum A) := by
            simpa using
              (subtype_specializes_iff (x := ⟨x, by simp⟩) (y := z)).1 hxz
          have hzy' : (z : PrimeSpectrum A) ⤳ y := by
            simpa using
              (subtype_specializes_iff (x := z) (y := ⟨y, by simp⟩)).1 hzy
          rcases hxy.eq_or_eq hxz' hzy' with h | h
          · left
            exact Subtype.ext h
          · right
            exact Subtype.ext h
      simpa [δBase] using hδU.eq_add_one_of_immediateSpecialization hxyU
  let δ : PrimeSpectrum A → ℤ := fun p ↦ δBase p - δBase (closedPoint A)
  -- Normalize by subtracting the closed-point value.
  have hδ : IsDimensionFunction δ := by
    refine
      { strict_of_specializes := ?_
        eq_add_one_of_immediateSpecialization := ?_ }
    · intro x y hxy hxy_ne
      simpa [δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        hδBase.strict_of_specializes hxy hxy_ne
    · intro x y hxy
      have hstep := hδBase.eq_add_one_of_immediateSpecialization hxy
      dsimp [δ]
      omega
  refine ⟨δ, hδ, ?_⟩
  dsimp [δ]
  ring

/-- Helper for Lemma 10.105.10: in a local spectrum, the codimension from the closed point to a
prime is the coheight of that prime. -/
private theorem closedPoint_codim_eq_coheight [IsLocalRing A] (p : PrimeSpectrum A) :
    codimBetween (toIrreducibleCloseds (closedPoint A)) (toIrreducibleCloseds p)
      (specializes_closedPoint p).toIrreducibleCloseds_le =
      Order.coheight p := by
  let T : IrreducibleCloseds (PrimeSpectrum A) := toIrreducibleCloseds (closedPoint A)
  let T' : IrreducibleCloseds (PrimeSpectrum A) := toIrreducibleCloseds p
  let e : PrimeSpectrum A ≃o (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ :=
    PrimeSpectrum.pointsEquivIrreducibleCloseds A
  have eDual :
      (Set.Icc T T')ᵒᵈ ≃o
        Set.Icc (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T')
          (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T) := by
    refine
      { toFun := fun x ↦
          let x' : Set.Icc T T' := show Set.Icc T T' from x
          ⟨show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from x'.1, x'.2.2, x'.2.1⟩
        invFun := fun y ↦
          show (Set.Icc T T')ᵒᵈ from
            ⟨show IrreducibleCloseds (PrimeSpectrum A) from y.1, y.2.2, y.2.1⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }
    · intro x
      ext
      rfl
    · intro y
      ext
      rfl
    · intro x y
      rfl
  have hT : (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T) = e (closedPoint A) := by
    rfl
  have hT' : (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T') = e p := by
    rfl
  have eInterval :
      Set.Icc (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T')
          (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T) ≃o
        Set.Icc p (closedPoint A) := by
    refine
      { toFun := fun x ↦ ⟨e.symm x.1, ?_, ?_⟩
        invFun := fun y ↦ ⟨e y.1, ?_, ?_⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }
    · simpa [hT'] using e.symm.monotone x.2.1
    · simpa [hT] using e.symm.monotone x.2.2
    · simpa [hT'] using e.monotone y.2.1
    · simpa [hT] using e.monotone y.2.2
    · intro x
      ext
      simp [e]
    · intro y
      ext
      simp [e]
    · intro x y
      simpa using e.symm.le_iff_le
  -- Compute codimension as the Krull dimension of the corresponding interval, then transport it
  -- to the upper interval `Ici p` in the prime spectrum.
  apply WithBot.coe_injective
  calc
    (codimBetween T T' (specializes_closedPoint p).toIrreducibleCloseds_le : WithBot ℕ∞) =
        Order.krullDim (Set.Icc T T') := codimBetween_eq_krullDim _
    _ = Order.krullDim ((Set.Icc T T')ᵒᵈ) := by
      exact (Order.krullDim_orderDual (α := Set.Icc T T')).symm
    _ =
        Order.krullDim
          (Set.Icc (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T')
            (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T)) := by
          exact Order.krullDim_eq_of_orderIso eDual
    _ = Order.krullDim (Set.Icc p (closedPoint A)) := by
      exact Order.krullDim_eq_of_orderIso eInterval
    _ = Order.krullDim (Set.Ici p) := by
      rw [show (closedPoint A) = (⊤ : PrimeSpectrum A) by rfl, Set.Icc_top]
    _ = Order.coheight p := (Order.coheight_eq_krullDim_Ici p).symm

/-- Helper for Lemma 10.105.10: the Krull dimension of `A / p` agrees with the codimension from
the closed point to `p`. -/
private theorem prime_quotient_krullDimension_eq_closedPoint_codim
    [IsNoetherianRing A] [IsLocalRing A] (p : PrimeSpectrum A) :
    (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds (closedPoint A)) (toIrreducibleCloseds p)
          (specializes_closedPoint p).toIrreducibleCloseds_le) : ℤ) := by
  -- Rewrite the quotient Krull dimension as the coheight of `p`.
  have hquotient :
      ringKrullDim (A ⧸ p.asIdeal) = Order.coheight p := by
    rw [ringKrullDim_quotient]
    have hzero : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
      ext q
      change p.asIdeal ≤ q.asIdeal ↔ p ≤ q
      rfl
    rw [hzero]
    exact (Order.coheight_eq_krullDim_Ici p).symm
  -- After removing the `WithBot` wrapper, the remaining quantity is exactly the codimension.
  calc
    (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)
        = (((Order.coheight p : ℕ∞)).toNat : ℤ) := by
            rw [hquotient]
            simp [WithBot.unbotD_coe]
    _ =
        (ENat.toNat
          (codimBetween (toIrreducibleCloseds (closedPoint A)) (toIrreducibleCloseds p)
            (specializes_closedPoint p).toIrreducibleCloseds_le) : ℤ) := by
              rw [closedPoint_codim_eq_coheight (A := A) p]

/-- Helper for Lemma 10.105.10: a dimension function normalized to be zero at the closed point is
forced to be `p ↦ dim(A / p)`. -/
private theorem normalized_dimensionFunction_eq_primeQuotientKrullDimension
    [IsNoetherianRing A] [IsLocalRing A] {δ : PrimeSpectrum A → ℤ}
    (hδ : IsDimensionFunction δ) (hδ0 : δ (closedPoint A) = 0) :
    ∀ p : PrimeSpectrum A,
      δ p = (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) := by
  intro p
  -- Lemma 5.20.2 computes the normalized dimension function as codimension from the closed point.
  calc
    δ p = δ p - δ (closedPoint A) := by simpa [hδ0]
    _ =
        (ENat.toNat
          (codimBetween (toIrreducibleCloseds (closedPoint A)) (toIrreducibleCloseds p)
            (specializes_closedPoint p).toIrreducibleCloseds_le) : ℤ) := by
              simpa using
                hδ.sub_eq_codimBetween_pointClosure p (closedPoint A) (specializes_closedPoint p)
    _ = (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) := by
      symm
      exact prime_quotient_krullDimension_eq_closedPoint_codim (A := A) p

end

-- Proof sketch: for the forward implication, transport catenarity from prime-ideal intervals to the
-- specialization order on `Spec A` and use the local-ring codimension formula at the closed point to
-- identify the resulting dimension function with `p ↦ dim (A / p)`. For the reverse implication,
-- apply the dimension-function criterion for catenarity on the prime spectrum and translate back to
-- the ring-theoretic formulation.
/-- Lemma 10.105.10: for a Noetherian local ring, the ring is catenary if and only if the function
`p ↦ dim (A / p)` is a dimension function on `Spec A`. -/
theorem isCatenaryRing_iff_primeQuotientKrullDimension_isDimensionFunction
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsCatenaryRing A ↔
      IsDimensionFunction
        (fun p : PrimeSpectrum A ↦ (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) := by
  constructor
  · intro hcat
    letI : IsCatenaryRing A := hcat
    obtain ⟨δ, hδ, hδ0⟩ := exists_dimensionFunction_vanishing_at_closedPoint (A := A)
    -- Compare the normalized dimension function with the quotient-dimension function pointwise.
    have hfun :
        δ =
          (fun p : PrimeSpectrum A ↦
            (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) := by
      funext p
      exact normalized_dimensionFunction_eq_primeQuotientKrullDimension
        (A := A) hδ hδ0 p
    simpa [hfun] using hδ
  · intro hdim
    -- The reverse implication is exactly Lemma 5.20.2 on the prime spectrum.
    rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
    exact hdim.catenarySpace
