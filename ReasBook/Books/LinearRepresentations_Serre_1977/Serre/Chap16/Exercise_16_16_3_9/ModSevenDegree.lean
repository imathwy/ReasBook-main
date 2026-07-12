import Mathlib
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_9.DimensionTwoTransport
import LinearRepresentations_Serre_1977.Chap16.Remark_16_16_3_5
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.RepresentationTheory.SymmetricExterior

open scoped TensorProduct

noncomputable section

namespace Representation

/-- Helper for Exercise 16-16.3-9: the modulus `7` is prime, so `ZMod 7` carries its canonical
field structure. -/
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

section SpecialLinear

section ModSevenExample

variable {V : Type} [AddCommGroup V] [Module (ZMod 7) V]

local notation "G₇" => SpecialLinearGroup (ZMod 7) V
local notation "ρSL₇" =>
  Representation.ofDistribMulAction (ZMod 7) G₇ V

/-- Helper for Exercise 16-16.3-9: an isomorphism in `FDRep` preserves the underlying
dimension. -/
theorem fdRep_finrank_eq_of_iso
    {k : Type} [Field k] {G : Type} [Group G]
    (X Y : FDRep k G) (e : X ≅ Y) :
    Module.finrank k X = Module.finrank k Y := by
  -- Forgetting to the underlying vector spaces turns an isomorphism of representations into a
  -- linear equivalence, so the dimensions agree.
  simpa using (FDRep.isoToLinearEquiv e).finrank_eq

/-- Helper for Exercise 16-16.3-9: a representation equivalence induces an isomorphism of the
bundled finite-dimensional representation objects. -/
def equivToFDRepIso
    {k : Type} [Field k] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {W : Type} [AddCommGroup W] [Module k W] [Module.Finite k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : Representation.Equiv ρ σ) :
    FDRep.of ρ ≅ FDRep.of σ :=
  Action.mkIso e.toLinearEquiv.toFGModuleCatIso fun g ↦ by
    ext x
    exact LinearMap.congr_fun (e.isIntertwining' g) x

/-- Helper for Exercise 16-16.3-9: if a scalar extension of `T` is equivariantly identified with a
`ZMod 7`-representation, then both sides have the same dimension. -/
theorem finrank_eq_of_scalarExtension_equiv
    {k : Type} [Field k] [Algebra k (ZMod 7)]
    {G : Type} [Group G]
    (T : FDRep k G)
    {W : Type} [AddCommGroup W] [Module (ZMod 7) W] [FiniteDimensional (ZMod 7) W]
    {σ : Representation (ZMod 7) G W}
    (e : Representation.Equiv ((FDRep.scalarExtension (k := ZMod 7) T).ρ) σ) :
    Module.finrank k T = Module.finrank (ZMod 7) W := by
  have hBaseChange :
      Module.finrank k T =
        Module.finrank (ZMod 7) (FDRep.scalarExtension (k := ZMod 7) T) := by
    -- Scalar extension is ordinary base change of the underlying vector space.
    exact (Module.finrank_baseChange (R := ZMod 7) (S := k) (M' := T)).symm
  have hIso :
      FDRep.of ((FDRep.scalarExtension (k := ZMod 7) T).ρ) ≅ FDRep.of σ :=
    equivToFDRepIso e
  calc
    Module.finrank k T = Module.finrank (ZMod 7) (FDRep.scalarExtension (k := ZMod 7) T) :=
      hBaseChange
    _ = Module.finrank (ZMod 7) (FDRep.of σ) := by
      -- Repackage the intertwiner as an isomorphism in `FDRep`.
      simpa [FDRep.scalarExtension] using
        fdRep_finrank_eq_of_iso
          (FDRep.scalarExtension (k := ZMod 7) T) (FDRep.of σ) hIso
    _ = Module.finrank (ZMod 7) W := by
      rfl

/-- Helper for Exercise 16-16.3-9: an isomorphism from a reduction representation to `T` records
that the reduced lattice and `T` have the same dimension. -/
theorem reduction_finrank_eq_of_iso
    {A : Type} [CommRing A] [IsLocalRing A]
    {G : Type} [Group G]
    {E : Type} [AddCommGroup E] [Module (IsLocalRing.ResidueField A) E]
    [Module.Finite (IsLocalRing.ResidueField A) E]
    {ρ : Representation (IsLocalRing.ResidueField A) G E}
    (T : FDRep (IsLocalRing.ResidueField A) G)
    (e : FDRep.of ρ ≅ T) :
    Module.finrank (IsLocalRing.ResidueField A) E =
      Module.finrank (IsLocalRing.ResidueField A) T := by
  -- Again, forget to the underlying vector spaces and compare dimensions there.
  simpa using (FDRep.isoToLinearEquiv e).finrank_eq

/-- Helper for Exercise 16-16.3-9: if `V` has dimension `2` over `𝔽_7`, then `SL(V)` has order
`336`. -/
theorem special_linear_group_card_eq_336_of_finrank_eq_two
    [FiniteDimensional (ZMod 7) V]
    (hV : Module.finrank (ZMod 7) V = 2) :
    Nat.card G₇ = 336 := by
  let eSL := special_linear_group_matrix_equiv_of_finrank_eq_two (V := V) hV
  -- Transport the abstract special linear group to the standard matrix model.
  calc
    Nat.card G₇ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) := by
      exact Nat.card_congr eSL.toEquiv
    _ = 336 := by
      rw [Nat.card_eq_fintype_card]
      native_decide

/-- Helper for Exercise 16-16.3-9: for a two-dimensional `𝔽_7`-space, the order of `SL(V)` is
not divisible by `5`. -/
theorem five_not_dvd_special_linear_group_card_of_finrank_eq_two
    [FiniteDimensional (ZMod 7) V]
    (hV : Module.finrank (ZMod 7) V = 2) :
    ¬ 5 ∣ Nat.card G₇ := by
  -- Reduce to the explicit order computation and finish arithmetically.
  rw [special_linear_group_card_eq_336_of_finrank_eq_two hV]
  norm_num

/-- Helper for Exercise 16-16.3-9: over an algebraically closed characteristic-zero field, a
simple `G₇`-representation of degree `5` would contradict the Chapter `6` degree divisibility
theorem. -/
theorem simple_fdRep_degree_five_absurd_of_finrank_eq_two
    {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
    (X : FDRep K G₇) [CategoryTheory.Simple X]
    [FiniteDimensional (ZMod 7) V]
    (hV : Module.finrank (ZMod 7) V = 2)
    (hX : Module.finrank K X = 5) :
    False := by
  let eSL := special_linear_group_matrix_equiv_of_finrank_eq_two (V := V) hV
  letI : Finite G₇ :=
    Finite.of_equiv (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) eSL.symm.toEquiv
  letI : Representation.IsIrreducible X.ρ := by
    simpa using (FDRep.isIrreducible_of_simple X)
  -- Convert simplicity to irreducibility and apply the characteristic-zero divisibility theorem.
  have hdiv : Module.finrank K X ∣ Nat.card G₇ := by
    simpa using (finrank_dvd_card (ρ := X.ρ))
  have hfive : ¬ 5 ∣ Nat.card G₇ :=
    five_not_dvd_special_linear_group_card_of_finrank_eq_two (V := V) hV
  rw [hX] at hdiv
  exact hfive hdiv

/-- Helper for Exercise 16-16.3-9: the fourth tensor power of the standard two-dimensional
`𝔽₇`-space has dimension `16`. This is the ambient tensor-space size before passing to the
fourth symmetric quotient. -/
theorem standard_fourfold_tensor_power_finrank_eq_sixteen :
    Module.finrank (ZMod 7) (⨂[ZMod 7]^4 (Fin 2 → ZMod 7)) = 16 := by
  let b : Module.Basis (Fin 2) (ZMod 7) (Fin 2 → ZMod 7) :=
    Pi.basisFun (ZMod 7) (Fin 2)
  let bt : Module.Basis (Fin 4 → Fin 2) (ZMod 7) (⨂[ZMod 7]^4 (Fin 2 → ZMod 7)) :=
    Basis.piTensorProduct fun _ : Fin 4 => b
  -- The tensor-product basis is indexed by `4`-tuples of basis vectors, so the cardinality is
  -- `2 ^ 4 = 16`.
  calc
    Module.finrank (ZMod 7) (⨂[ZMod 7]^4 (Fin 2 → ZMod 7))
        = Fintype.card (Fin 4 → Fin 2) := Module.finrank_eq_card_basis bt
    _ = 16 := by native_decide

/-- Helper for Exercise 16-16.3-9: in the standard two-dimensional `𝔽₇`-space, the fourth
symmetric power is spanned by the five orbit-types of sorted `0/1` basis tuples. -/
theorem standard_sym4_finrank_le_five :
    Module.finrank (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 → ZMod 7)) ≤ 5 := by
  let SortedBitTuples := {f : Fin 4 → Fin 2 // Monotone f}
  let b : Module.Basis (Fin 2) (ZMod 7) (Fin 2 → ZMod 7) := Pi.basisFun (ZMod 7) (Fin 2)
  let bt : Module.Basis (Fin 4 → Fin 2) (ZMod 7) (⨂[ZMod 7]^4 (Fin 2 → ZMod 7)) :=
    Basis.piTensorProduct fun _ : Fin 4 => b
  let q : (⨂[ZMod 7]^4 (Fin 2 → ZMod 7)) →ₗ[ZMod 7] Sym[ZMod 7]^4 (Fin 2 → ZMod 7) :=
    SymmetricPower.mk (ZMod 7) (Fin 4) (Fin 2 → ZMod 7)
  let v : SortedBitTuples → Sym[ZMod 7]^4 (Fin 2 → ZMod 7) :=
    fun u ↦ ⨂ₛ[ZMod 7] i, b (u.1 i)
  have himage : q '' Set.range bt = Set.range (fun p : Fin 4 → Fin 2 => q (bt p)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨bt p, ⟨p, rfl⟩, rfl⟩
  have hspanBasis :
      Submodule.span (ZMod 7) (Set.range fun p : Fin 4 → Fin 2 => q (bt p)) = ⊤ := by
    -- The images of the tensor-product basis span because the quotient map is surjective.
    calc
      Submodule.span (ZMod 7) (Set.range fun p : Fin 4 → Fin 2 => q (bt p))
          = Submodule.span (ZMod 7) (q '' Set.range bt) := by
              rw [himage]
      _ = Submodule.map q (Submodule.span (ZMod 7) (Set.range bt)) := by
            rw [Submodule.span_image]
      _ = Submodule.map q ⊤ := by
            rw [bt.span_eq]
      _ = ⊤ := by
            rw [Submodule.map_top]
            exact LinearMap.range_eq_top.2 AddCon.mk'_surjective
  have hsubset :
      Set.range (fun p : Fin 4 → Fin 2 => q (bt p)) ⊆ Set.range v := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    refine ⟨⟨p ∘ Tuple.sort p, Tuple.monotone_sort p⟩, ?_⟩
    -- Sorting a basis tuple only permutes tensor factors, so its symmetric image is unchanged.
    simp [v, q, bt, Basis.piTensorProduct_apply, SymmetricPower.tprod, Function.comp]
    exact SymmetricPower.tprod_equiv (R := ZMod 7) (ι := Fin 4) (e := Tuple.sort p)
      (fun i => b (p i))
  have hspanSorted :
      Submodule.span (ZMod 7) (Set.range v) = ⊤ := by
    apply top_unique
    rw [← hspanBasis]
    exact Submodule.span_mono hsubset
  have hcard : Fintype.card SortedBitTuples = 5 := by
    decide
  -- A spanning family indexed by five sorted tuples forces the desired upper bound.
  exact le_trans (finrank_le_of_span_eq_top hspanSorted) (by simp [hcard])

/-- Helper for Exercise 16-16.3-9: in the standard two-dimensional `𝔽₇`-space, the fourth
symmetric power really has dimension `5`. -/
theorem standard_sym4_degree_eq_five :
    Module.finrank (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 → ZMod 7)) = 5 := by
  let ρstd :
      Representation (ZMod 7)
        (SpecialLinearGroup (ZMod 7) (Fin 2 → ZMod 7)) (Fin 2 → ZMod 7) :=
    Representation.ofDistribMulAction (ZMod 7)
      (SpecialLinearGroup (ZMod 7) (Fin 2 → ZMod 7)) (Fin 2 → ZMod 7)
  have hseries :=
    symmetricPowerCharacterSeries_eval_eq_det_inv
      (ρ := ρstd) (s := (1 : SpecialLinearGroup (ZMod 7) (Fin 2 → ZMod 7)))
  have hcoeff := congrArg (PowerSeries.coeff 4) hseries
  rw [show (ρstd 1) = (1 : (Fin 2 → ZMod 7) →ₗ[(ZMod 7)] (Fin 2 → ZMod 7)) by simp] at hcoeff
  have hreverse :
      ((((Polynomial.X : Polynomial (ZMod 7)) - 1) ^ 2).reverse : Polynomial (ZMod 7)) =
        (1 - Polynomial.X) ^ 2 := by
    -- Reverse the standard characteristic polynomial `(X - 1)^2` into the determinant form
    -- `(1 - X)^2`.
    rw [pow_two, Polynomial.reverse_mul_of_domain]
    · have hrewrite :
          ((Polynomial.X : Polynomial (ZMod 7)) - 1) = Polynomial.C (-1) + Polynomial.X := by
        simp [sub_eq_add_neg, add_comm]
      rw [hrewrite, Polynomial.reverse_C_add]
      have hrevX : (Polynomial.X : Polynomial (ZMod 7)).reverse = 1 := by
        calc
          (Polynomial.X : Polynomial (ZMod 7)).reverse =
              Polynomial.reverse (1 : Polynomial (ZMod 7)) := by
            simpa using (Polynomial.reverse_X_mul (1 : Polynomial (ZMod 7)))
          _ = 1 := by
            simpa using (Polynomial.reverse_C (1 : ZMod 7))
      rw [hrevX]
      norm_num [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simp [Representation.character, Representation.nthSymmetricPower, LinearMap.charpoly_one,
    hreverse, Module.finrank_fintype_fun_eq_card] at hcoeff
  have hinv : (((1 - PowerSeries.X : PowerSeries (ZMod 7)) ^ 2)⁻¹) =
      (PowerSeries.invOneSubPow (ZMod 7) 2).val := by
    -- Replace the inverse of `(1 - X)^2` by the closed-form power series with binomial
    -- coefficients.
    exact
      (PowerSeries.inv_eq_iff_mul_eq_one
        (k := ZMod 7)
        (φ := (PowerSeries.invOneSubPow (ZMod 7) 2).val)
        (ψ := (1 - PowerSeries.X : PowerSeries (ZMod 7)) ^ 2)
        (by simp)).2 <| by
          simpa [mul_comm] using
            (PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
              (S := ZMod 7) (d := 0) (e := 2))
  rw [hinv, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose] at hcoeff
  norm_num at hcoeff
  let n := Module.finrank (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 → ZMod 7))
  have hsymid :
      SymmetricPower.map 4
          (1 : (Fin 2 → ZMod 7) →ₗ[(ZMod 7)] (Fin 2 → ZMod 7)) = LinearMap.id := by
    change SymmetricPower.map 4
        (LinearMap.id : (Fin 2 → ZMod 7) →ₗ[(ZMod 7)] (Fin 2 → ZMod 7)) = LinearMap.id
    simpa using (SymmetricPower.map_id (n := 4) (k := ZMod 7) (V := Fin 2 → ZMod 7))
  have htrace :
      LinearMap.trace (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 → ZMod 7))
          (SymmetricPower.map 4
            (1 : (Fin 2 → ZMod 7) →ₗ[(ZMod 7)] (Fin 2 → ZMod 7))) = n := by
    rw [hsymid]
    simpa [n] using
      (LinearMap.trace_id (R := ZMod 7) (M := Sym[ZMod 7]^4 (Fin 2 → ZMod 7)) :
        LinearMap.trace (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 → ZMod 7))
        (LinearMap.id : Sym[ZMod 7]^4 (Fin 2 → ZMod 7) →ₗ[(ZMod 7)] Sym[ZMod 7]^4
          (Fin 2 → ZMod 7)) = Module.finrank (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 → ZMod 7)))
  rw [htrace] at hcoeff
  have hnmod : (n : ZMod 7) = 5 := by
    simpa [n] using hcoeff
  have hnle : n ≤ 5 := by
    simpa [n] using standard_sym4_finrank_le_five
  have hnlt : n < 7 := lt_of_le_of_lt hnle (by decide)
  have hnmod' : n % 7 = 5 := (ZMod.natCast_eq_natCast_iff' n 5 7).mp hnmod
  -- The upper bound `n ≤ 5` makes the congruence modulo `7` an actual equality of naturals.
  rw [Nat.mod_eq_of_lt hnlt] at hnmod'
  exact hnmod'

/-- Helper for Exercise 16-16.3-9: every two-dimensional `𝔽₇`-space has fourth symmetric power of
dimension `5`. -/
theorem sym4_degree_eq_five
    (hV : Module.finrank (ZMod 7) V = 2) :
    Module.finrank (ZMod 7) (Sym[ZMod 7]^4 V) = 5 := by
  letI : FiniteDimensional (ZMod 7) V := finiteDimensional_of_finrank_eq_two hV
  let eFin : Fin (Module.finrank (ZMod 7) V) ≃ Fin 2 := by
    simpa [hV] using (_root_.Equiv.refl (Fin 2))
  let b : Module.Basis (Fin 2) (ZMod 7) V := (Module.finBasis (ZMod 7) V).reindex eFin
  let e : V ≃ₗ[(ZMod 7)] (Fin 2 → ZMod 7) := b.equivFun
  let f := SymmetricPower.map 4 e.toLinearMap
  let g := SymmetricPower.map 4 e.symm.toLinearMap
  have hleft : g.comp f = LinearMap.id := by
    -- The symmetric-power map functor sends inverse linear equivalences to inverse endomorphisms.
    calc
      g.comp f = SymmetricPower.map 4 (e.symm.toLinearMap.comp e.toLinearMap) := by
        rw [← SymmetricPower.map_comp 4 e.toLinearMap e.symm.toLinearMap]
      _ = SymmetricPower.map 4 LinearMap.id := by
            congr
            ext x
            simp
      _ = LinearMap.id := SymmetricPower.map_id 4
  have hright : f.comp g = LinearMap.id := by
    calc
      f.comp g = SymmetricPower.map 4 (e.toLinearMap.comp e.symm.toLinearMap) := by
        rw [← SymmetricPower.map_comp 4 e.symm.toLinearMap e.toLinearMap]
      _ = SymmetricPower.map 4 LinearMap.id := by
            congr
            ext x
            simp
      _ = LinearMap.id := SymmetricPower.map_id 4
  let esym : Sym[ZMod 7]^4 V ≃ₗ[(ZMod 7)] Sym[ZMod 7]^4 (Fin 2 → ZMod 7) :=
    LinearEquiv.ofBijective f ⟨by
      intro x y hxy
      calc
        x = g (f x) := by
              symm
              exact LinearMap.congr_fun hleft x
        _ = g (f y) := by rw [hxy]
        _ = y := LinearMap.congr_fun hleft y,
      by
      intro y
      refine ⟨g y, ?_⟩
      exact LinearMap.congr_fun hright y⟩
  -- Transport the standard dimension computation back along the chosen basis equivalence.
  calc
    Module.finrank (ZMod 7) (Sym[ZMod 7]^4 V)
        = Module.finrank (ZMod 7) (Sym[ZMod 7]^4 (Fin 2 → ZMod 7)) := esym.finrank_eq
    _ = 5 := standard_sym4_degree_eq_five

end ModSevenExample

end SpecialLinear

end Representation
