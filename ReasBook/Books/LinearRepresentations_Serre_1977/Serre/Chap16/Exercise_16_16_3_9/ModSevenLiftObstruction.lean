import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_9.ModSevenDegree

open scoped TensorProduct

noncomputable section

namespace Representation

section SpecialLinear

section ModSevenExample

variable {V : Type} [AddCommGroup V] [Module (ZMod 7) V]

local notation "G₇" => SpecialLinearGroup (ZMod 7) V
local notation "ρSL₇" =>
  Representation.ofDistribMulAction (ZMod 7) G₇ V

-- Domain-style sampling for this example:
-- * primary domain: modular lifting obstructions for specific symmetric-power representations of
--   `SL₂` in characteristic `7`;
-- * relevant owner declarations inspected before refining:
--   `Representation.nthSymmetricPower`,
--   `FDRep.HasRPrimeLift`,
--   `FDRep.scalarExtension`,
--   `Representation.Equiv`;
-- * best owner abstraction for the source-facing target is the actual `𝔽_7`-representation
--   `nthSymmetricPower ρSL₇ 4`, while the Chapter `16` lift predicate lives on the residue-field
--   owner `FDRep.HasRPrimeLift`;
-- * primitive data: a residue-field representation `T` together with `FDRep.HasRPrimeLift T K`;
-- * derived API: comparing its scalar extension with `nthSymmetricPower ρSL₇ 4` by
--   `.Equiv` on the unbundled scalar-extension representation.
--
-- Layer triage:
-- * source-facing: the fourth symmetric-power representation of `SL(V)` over `𝔽_7`;
-- * core/canonical: `Representation.nthSymmetricPower` and `FDRep.HasRPrimeLift`;
-- * bridge/view: `FDRep.scalarExtension` and the comparison
--   `Nonempty (Representation.Equiv ((FDRep.scalarExtension T).ρ) (nthSymmetricPower ρSL₇ 4))`.

-- Proof sketch: for `p = 7` and `i = 4`, the representation `Sym⁴(V)` has dimension `5`; if the
-- corresponding object of `FDRep (ZMod 7) G₇` lifted to characteristic zero through a stable
-- lattice in a simple finite-dimensional ordinary representation, Serre's degree obstruction for
-- ordinary irreducible representations of `SL₂(𝔽₇)` would force
-- `5 ∣ |SL₂(𝔽₇)|`, which is false.
/-- Helper for Exercise 16-16.3-9: an `(R')`-lift whose reduction scalar-extends to the fourth
symmetric power already has reduction degree `5`. -/
theorem rPrimeLift_reduction_degree_eq_five_of_sym4_equiv
    (hV : Module.finrank (ZMod 7) V = 2)
    {A : Type} [CommRing A] [IsLocalRing A]
    {K : Type} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [Algebra (IsLocalRing.ResidueField A) (ZMod 7)]
    (T : FDRep (IsLocalRing.ResidueField A) G₇)
    {X : FDRep K G₇} (L : StableLattice A X.ρ)
    (hReduction : Nonempty (FDRep.of L.reductionRepresentation ≅ T))
    (hEquiv : Nonempty (Representation.Equiv
      (FDRep.scalarExtension T).ρ (nthSymmetricPower ρSL₇ 4))) :
    Module.finrank (IsLocalRing.ResidueField A) L.reduction = 5 := by
  letI : FiniteDimensional (ZMod 7) V := finiteDimensional_of_finrank_eq_two hV
  let e : V ≃ₗ[(ZMod 7)] (Fin 2 → ZMod 7) :=
    two_dimensional_linear_equiv_of_finrank_eq_two (V := V) hV
  let f := SymmetricPower.map 4 e.toLinearMap
  let g := SymmetricPower.map 4 e.symm.toLinearMap
  have hleft : g.comp f = LinearMap.id := by
    -- The symmetric-power functor carries inverse linear equivalences to inverse endomorphisms.
    calc
      g.comp f = SymmetricPower.map 4 (e.symm.toLinearMap.comp e.toLinearMap) := by
        rw [← SymmetricPower.map_comp 4 e.toLinearMap e.symm.toLinearMap]
      _ = SymmetricPower.map 4 LinearMap.id := by
            congr
            ext x
            simp
      _ = LinearMap.id := SymmetricPower.map_id 4
  letI : FiniteDimensional (ZMod 7) (Sym[ZMod 7]^4 V) :=
    FiniteDimensional.of_injective f <| by
      intro x y hxy
      calc
        x = g (f x) := by
              symm
              exact LinearMap.congr_fun hleft x
        _ = g (f y) := by rw [hxy]
        _ = y := LinearMap.congr_fun hleft y
  have hReductionDim :
      Module.finrank (IsLocalRing.ResidueField A) L.reduction =
        Module.finrank (IsLocalRing.ResidueField A) T := by
    -- Repackage the reduction comparison as equality of the underlying residue-field dimensions.
    rcases hReduction with ⟨e⟩
    simpa using reduction_finrank_eq_of_iso (T := T) e
  have hTdim :
      Module.finrank (IsLocalRing.ResidueField A) T =
        Module.finrank (ZMod 7) (Sym[ZMod 7]^4 V) := by
    -- The scalar-extended owner identifies `T` with the actual fourth symmetric power.
    rcases hEquiv with ⟨e⟩
    simpa using finrank_eq_of_scalarExtension_equiv (T := T) e
  -- Compare both sides to the explicit `Sym⁴(V)` degree computation.
  calc
    Module.finrank (IsLocalRing.ResidueField A) L.reduction =
        Module.finrank (IsLocalRing.ResidueField A) T :=
      hReductionDim
    _ = Module.finrank (ZMod 7) (Sym[ZMod 7]^4 V) := hTdim
    _ = 5 := sym4_degree_eq_five hV

/-- Helper for Exercise 16-16.3-9: unpacking an `(R')`-lift together with an equivariant
identification of its scalar extension with the fourth symmetric power already yields a stable
lattice reduction of degree `5`. -/
theorem hasRPrimeLift_reduction_degree_eq_five_of_sym4_equiv
    (hV : Module.finrank (ZMod 7) V = 2)
    {A : Type} [CommRing A] [IsLocalRing A]
    {K : Type} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [Algebra (IsLocalRing.ResidueField A) (ZMod 7)]
    {T : FDRep (IsLocalRing.ResidueField A) G₇}
    (hT : FDRep.HasRPrimeLift T K)
    (hEquiv : Nonempty (Representation.Equiv
      (FDRep.scalarExtension T).ρ (nthSymmetricPower ρSL₇ 4))) :
    ∃ X : FDRep K G₇, CategoryTheory.Simple X ∧
      ∃ L : StableLattice A X.ρ,
        Nonempty (FDRep.of L.reductionRepresentation ≅ T) ∧
          Module.finrank (IsLocalRing.ResidueField A) L.reduction = 5 := by
  rcases hT with ⟨X, hXsimple, L, hReduction⟩
  refine ⟨X, hXsimple, L, hReduction, ?_⟩
  -- Collapse the unpacked lift data to the already established reduction-degree computation.
  exact
    rPrimeLift_reduction_degree_eq_five_of_sym4_equiv
      (V := V) (hV := hV) (T := T) (L := L) hReduction hEquiv

/-- Helper for Exercise 16-16.3-9: over an algebraically closed characteristic-zero field, a
simple lift with the same generic and reduction degrees would already contradict Serre's degree
divisibility obstruction once the reduction degree is `5`. -/
theorem modSeven_lift_contradiction_of_generic_degree_eq_reduction
    {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra A K] [IsFractionRing A K]
    {X : FDRep K G₇} [CategoryTheory.Simple X]
    [FiniteDimensional (ZMod 7) V]
    (hV : Module.finrank (ZMod 7) V = 2)
    (L : StableLattice A X.ρ)
    (hDegree :
      Module.finrank K X = Module.finrank (IsLocalRing.ResidueField A) L.reduction)
    (hReductionDegree :
      Module.finrank (IsLocalRing.ResidueField A) L.reduction = 5) :
    False := by
  -- Rewrite the missing generic-degree comparison into the degree-`5` hypothesis required by
  -- the Chapter 6 divisibility obstruction.
  have hX : Module.finrank K X = 5 := by
    rw [hDegree, hReductionDegree]
  exact
    simple_fdRep_degree_five_absurd_of_finrank_eq_two
      (V := V) (X := X) hV hX

/-- Helper for Exercise 16-16.3-9: once a degree bridge between a simple characteristic-zero lift
and the reduction of its stable lattice is available, the mod-`7` fourth symmetric power cannot
admit an `(R')`-lift whose scalar extension is `Sym⁴(V)`. -/
theorem modSeven_not_rPrimeLiftable_of_generic_degree_bridge
    (hV : Module.finrank (ZMod 7) V = 2)
    {A : Type} [CommRing A] [IsLocalRing A]
    {K : Type} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] [IsAlgClosed K]
    [Algebra (IsLocalRing.ResidueField A) (ZMod 7)]
    (hBridge :
      ∀ {X : FDRep K G₇} [CategoryTheory.Simple X] (L : StableLattice A X.ρ),
        Module.finrank K X = Module.finrank (IsLocalRing.ResidueField A) L.reduction) :
    ¬ ∃ T : FDRep (IsLocalRing.ResidueField A) G₇,
        FDRep.HasRPrimeLift T K ∧
          Nonempty (Representation.Equiv
            (FDRep.scalarExtension T).ρ (nthSymmetricPower ρSL₇ 4)) := by
  intro hLift
  rcases hLift with ⟨T, hT, hEquiv⟩
  rcases hasRPrimeLift_reduction_degree_eq_five_of_sym4_equiv
      (V := V) (hV := hV) (T := T) hT hEquiv with
    ⟨X, hXsimple, L, hReduction, hReductionDegree⟩
  letI : CategoryTheory.Simple X := hXsimple
  letI : FiniteDimensional (ZMod 7) V := finiteDimensional_of_finrank_eq_two hV
  -- The lift data and the scalar-extension comparison already force reduction degree `5`, so the
  -- desired contradiction is exactly the Chapter `6` divisibility obstruction once the generic
  -- degree is identified with that same reduction degree.
  exact
    modSeven_lift_contradiction_of_generic_degree_eq_reduction
      (V := V) (K := K) (A := A) (X := X) hV L (hBridge L) hReductionDegree

end ModSevenExample

end SpecialLinear

end Representation
