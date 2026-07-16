import stacks_proof.stacks_project.Chap12.Definition_12_14_2
import stacks_proof.stacks_project.Chap12.Lemma_12_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomologicalComplex

universe v u

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
noncomputable section

variable (S : ShortComplex (ChainComplex 𝒜 ℤ)) (hS : S.ShortExact)

/- Domain-style sampling in the chain-complex long-exact-sequence API:
- core/canonical owner boundary: `ShortComplex.ShortExact.δ`
- core/canonical owner shifted homology map:
  `(homologyFunctor 𝒜 (ComplexShape.down ℤ) 0).shiftMap`
- source-facing bridge datum: `homOfDegreewiseSplit` from Lemma `12.14.4`

This item is a `bridge/view`: it compares the explicit chain-level connecting morphism from
Lemma `12.14.4` with the owner boundary map in the long exact homology sequence, using the owner
`Functor.ShiftSequence.shiftMap` interface on chain homology.
-/

variable (σ : ∀ n : ℤ, (ChainComplex.degreewiseShortComplex S n).Splitting)

attribute [local simp] XIsoOfEq_hom_naturality smul_smul

/-- Helper for Lemma 12.14.5: the chosen split lift in degree `i` of a cycle in `S.X₃`. -/
abbrev degreewiseSplitLift {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i) :
    A ⟶ S.X₂.X i :=
  z ≫ (σ i).s

/-- Helper for Lemma 12.14.5: the explicit boundary representative in degree `i - 1` obtained by
differentiating the split lift. -/
abbrev degreewiseSplitBoundary {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i) :
    A ⟶ S.X₁.X (i - 1) :=
  degreewiseSplitLift S σ i z ≫ S.X₂.d i (i - 1) ≫ (σ (i - 1)).r

/-- Helper for Lemma 12.14.5: in the chain shape, the successor of `i` is `i - 1`. -/
lemma degreewiseSplitLiftNext (i : ℤ) : (down ℤ).next i = i - 1 := by
  simp

/-- Helper for Lemma 12.14.5: the split lift and its boundary satisfy the relations used by the
short-exact-sequence boundary formula. -/
lemma degreewiseSplitBoundaryData {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i - 1) = 0) :
    degreewiseSplitLift S σ i z ≫ S.g.f i = z ∧
      degreewiseSplitBoundary S σ i z ≫ S.f.f (i - 1) =
        degreewiseSplitLift S σ i z ≫ S.X₂.d i (i - 1) := by
  have hs : (σ i).s ≫ S.g.f i = 𝟙 _ := by
    simpa using (σ i).s_g
  have hr :
      (σ (i - 1)).r ≫ S.f.f (i - 1) =
        𝟙 _ - S.g.f (i - 1) ≫ (σ (i - 1)).s := by
    simpa using (σ (i - 1)).r_f
  constructor
  · -- The chosen lift is a section of `S.g` in degree `i`.
    simpa [degreewiseSplitLift, Category.assoc] using congrArg (fun t ↦ z ≫ t) hs
  · -- Expand `r_f` and kill the correction term by the cocycle condition on `z`.
    have hcomm :
        S.X₂.d i (i - 1) ≫ S.g.f (i - 1) =
          S.g.f i ≫ S.X₃.d i (i - 1) := by
      simpa using S.g.comm i (i - 1)
    have hkill :
        z ≫ (σ i).s ≫ S.X₂.d i (i - 1) ≫ S.g.f (i - 1) ≫ (σ (i - 1)).s = 0 := by
      calc
        z ≫ (σ i).s ≫ S.X₂.d i (i - 1) ≫ S.g.f (i - 1) ≫ (σ (i - 1)).s =
            z ≫ (σ i).s ≫ (S.X₂.d i (i - 1) ≫ S.g.f (i - 1)) ≫ (σ (i - 1)).s := by
              simp [Category.assoc]
        _ =
            z ≫ (σ i).s ≫ (S.g.f i ≫ S.X₃.d i (i - 1)) ≫ (σ (i - 1)).s := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ z ≫ (σ i).s ≫ t ≫ (σ (i - 1)).s) hcomm
        _ = z ≫ ((σ i).s ≫ S.g.f i) ≫ S.X₃.d i (i - 1) ≫ (σ (i - 1)).s := by
              simp [Category.assoc]
        _ = z ≫ S.X₃.d i (i - 1) ≫ (σ (i - 1)).s := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ z ≫ t ≫ S.X₃.d i (i - 1) ≫ (σ (i - 1)).s) hs
        _ = 0 := by
              simpa [Category.assoc] using congrArg (fun t ↦ t ≫ (σ (i - 1)).s) hz
    have hsub :
        z ≫ (σ i).s ≫ S.X₂.d i (i - 1) ≫
            (𝟙 _ - S.g.f (i - 1) ≫ (σ (i - 1)).s) =
          z ≫ (σ i).s ≫ S.X₂.d i (i - 1) := by
      -- Expand the postcomposition across the subtraction and kill the correction term by `hkill`.
      simpa [sub_eq_add_neg, Category.assoc, hkill]
    calc
      degreewiseSplitBoundary S σ i z ≫ S.f.f (i - 1) =
          z ≫ (σ i).s ≫ S.X₂.d i (i - 1) ≫
            ((σ (i - 1)).r ≫ S.f.f (i - 1)) := by
              simp [degreewiseSplitBoundary, degreewiseSplitLift, Category.assoc]
      _ = z ≫ (σ i).s ≫ S.X₂.d i (i - 1) ≫
            (𝟙 _ - S.g.f (i - 1) ≫ (σ (i - 1)).s) := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ z ≫ (σ i).s ≫ S.X₂.d i (i - 1) ≫ t) hr
      _ = z ≫ (σ i).s ≫ S.X₂.d i (i - 1) := hsub
      _ = degreewiseSplitLift S σ i z ≫ S.X₂.d i (i - 1) := by
            simp [degreewiseSplitLift]

/-- Helper for Lemma 12.14.5: the explicit split boundary becomes the differential of the chosen
split lift after postcomposing with the monomorphism `f_{i-1}`. -/
lemma degreewiseSplitBoundary_comp_f {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i - 1) = 0) :
    degreewiseSplitBoundary S σ i z ≫ S.f.f (i - 1) =
      degreewiseSplitLift S σ i z ≫ S.X₂.d i (i - 1) := by
  -- This is exactly the second component of the boundary data package proved above.
  simpa using (degreewiseSplitBoundaryData S σ i z hz).2

/-- Helper for Lemma 12.14.5: in the chain shape, the successor of `i - 1` is `i - 2`. -/
lemma degreewiseSplitBoundaryNext (i : ℤ) : (down ℤ).next (i - 1) = i - 2 := by
  calc
    (down ℤ).next (i - 1) = i - 1 - 1 := degreewiseSplitLiftNext (i - 1)
    _ = i - 2 := by omega

/-- Helper for Lemma 12.14.5: the explicit boundary representative is a cycle in degree
`i - 1`. -/
lemma degreewiseSplitBoundaryCycle {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i - 1) = 0) :
    degreewiseSplitBoundary S σ i z ≫ S.X₁.d (i - 1) (i - 2) = 0 := by
  letI : Mono (S.f.f (i - 2)) := (σ (i - 2)).mono_f
  have hdata := degreewiseSplitBoundaryData S σ i z hz
  have hcomm :
      S.X₁.d (i - 1) (i - 2) ≫ S.f.f (i - 2) =
        S.f.f (i - 1) ≫ S.X₂.d (i - 1) (i - 2) := by
    simpa using S.f.comm (i - 1) (i - 2)
  -- Postcompose with the split monomorphism in degree `i - 2` and use `d ≫ d = 0`.
  apply (cancel_mono (S.f.f (i - 2))).1
  simpa using
    calc
      (degreewiseSplitBoundary S σ i z ≫ S.X₁.d (i - 1) (i - 2)) ≫ S.f.f (i - 2) =
          degreewiseSplitBoundary S σ i z ≫
            (S.f.f (i - 1) ≫ S.X₂.d (i - 1) (i - 2)) := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ degreewiseSplitBoundary S σ i z ≫ t) hcomm
      _ =
          degreewiseSplitLift S σ i z ≫ S.X₂.d i (i - 1) ≫ S.X₂.d (i - 1) (i - 2) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ t ≫ S.X₂.d (i - 1) (i - 2)) hdata.2
      _ = 0 := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ degreewiseSplitLift S σ i z ≫ t)
                (S.X₂.d_comp_d i (i - 1) (i - 2))

/-- Helper for Lemma 12.14.5: after identifying the shifted target degree with `X (i - 1)`, the
degree-`i` component of `homOfDegreewiseSplit` is the explicit split boundary representative. -/
lemma shiftedHomOfDegreewiseSplit_eq_degreewiseSplitBoundary {A : 𝒜} (i : ℤ)
    (z : A ⟶ S.X₃.X i) :
    (z ≫ (homOfDegreewiseSplit S σ).f i) ≫ (S.X₁.shiftMinusOneXIso i).hom =
      degreewiseSplitBoundary S σ i z := by
  -- Read off the shifted component from `homOfDegreewiseSplit_f` and expand the boundary notation.
  simpa [degreewiseSplitBoundary, degreewiseSplitLift, Category.assoc] using
    congrArg (fun t ↦ z ≫ t) (homOfDegreewiseSplit_f S σ i)

/-- Helper for Lemma 12.14.5: the shifted component of `homOfDegreewiseSplit` carries a cycle in
`S.X₃.X i` to a cycle in `S.X₁.X (i - 1)`. -/
lemma shiftedHomOfDegreewiseSplitCycle {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i - 1) = 0) :
    ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
        (S.X₁.shiftMinusOneXIso i).hom) ≫
      S.X₁.d (i - 1) (i - 2) = 0 := by
  -- First rewrite the shifted component to the explicit split boundary representative.
  calc
    ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
          (S.X₁.shiftMinusOneXIso i).hom) ≫
        S.X₁.d (i - 1) (i - 2) =
      degreewiseSplitBoundary S σ i z ≫ S.X₁.d (i - 1) (i - 2) := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ t ≫ S.X₁.d (i - 1) (i - 2))
            (shiftedHomOfDegreewiseSplit_eq_degreewiseSplitBoundary S σ i z)
    _ = 0 := by
          simpa using
            (degreewiseSplitBoundaryCycle S σ i z hz)

/-- Helper for Lemma 12.14.5: the canonical short-exact-sequence boundary sends a refined cycle
class to the explicit split boundary representative. -/
lemma shortExactBoundaryOnLiftCycles {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i - 1) = 0) :
    S.X₃.liftCycles z (i - 1) (degreewiseSplitLiftNext i) hz ≫ S.X₃.homologyπ i ≫
        hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) =
      S.X₁.liftCycles (degreewiseSplitBoundary S σ i z) (i - 2)
          (degreewiseSplitBoundaryNext i)
          (degreewiseSplitBoundaryCycle S σ i z hz) ≫
        S.X₁.homologyπ (i - 1) := by
  have hdata := degreewiseSplitBoundaryData S σ i z hz
  -- Apply the owner formula `δ_eq` to the explicit split lift and boundary representative.
  simpa [degreewiseSplitLift, degreewiseSplitBoundary] using
    hS.δ_eq i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) z hz
      (degreewiseSplitLift S σ i z) hdata.1
      (degreewiseSplitBoundary S σ i z) hdata.2
      (i - 2) (degreewiseSplitBoundaryNext i)

/-- Helper for Lemma 12.14.5: a cycle in `K⟦-1⟧` stays a cycle after transporting the degree-`i`
component to `K.X (i - 1)`. -/
lemma shiftMinusOneComponentCycle (K : ChainComplex 𝒜 ℤ) {A : 𝒜} {i : ℤ}
    (f : A ⟶ (K⟦(-1 : ℤ)⟧).X i)
    (hf : f ≫ (K⟦(-1 : ℤ)⟧).d i (i - 1) = 0) :
    f ≫ (K.shiftMinusOneXIso i).hom ≫ K.d (i - 1) (i - 1 - 1) = 0 := by
  have hd :
      (K.shiftMinusOneXIso i).inv ≫ (K⟦(-1 : ℤ)⟧).d i (i - 1) =
        (((-1 : ℤ).negOnePow) • K.d (i - 1) (i - 1 - 1)) ≫
          (K.shiftMinusOneXIso (i - 1)).inv := by
    -- Rewrite the shifted differential through the owner degree identifications for `K⟦-1⟧`.
    simpa [ChainComplex.shiftMinusOneXIso] using
      (ChainComplex.shiftFunctor_obj_d (C := 𝒜) (-1) K i (i - 1))
  have hzero :
      f ≫ (K.shiftMinusOneXIso i).hom ≫
          (((( -1 : ℤ).negOnePow) • K.d (i - 1) (i - 1 - 1)) ≫
            (K.shiftMinusOneXIso (i - 1)).inv) = 0 := by
    -- Transport the shifted differential equation along `(K.shiftMinusOneXIso i).hom`.
    calc
      f ≫ (K.shiftMinusOneXIso i).hom ≫
          (((( -1 : ℤ).negOnePow) • K.d (i - 1) (i - 1 - 1)) ≫
            (K.shiftMinusOneXIso (i - 1)).inv) =
        f ≫ (K.shiftMinusOneXIso i).hom ≫ (K.shiftMinusOneXIso i).inv ≫
          (K⟦(-1 : ℤ)⟧).d i (i - 1) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ f ≫ (K.shiftMinusOneXIso i).hom ≫ t) hd.symm
      _ = f ≫ (K⟦(-1 : ℤ)⟧).d i (i - 1) := by
            simp
      _ = 0 := hf
  have hscaled :
      f ≫ (K.shiftMinusOneXIso i).hom ≫
          (((-1 : ℤ).negOnePow) • K.d (i - 1) (i - 1 - 1)) = 0 := by
    -- Cancel the terminal isomorphism to recover the transported differential equation itself.
    apply (cancel_mono ((K.shiftMinusOneXIso (i - 1)).inv)).1
    simpa [Category.assoc] using hzero
  -- The `(-1)^(-1)` sign is harmless for a zero equation.
  simpa using hscaled

/-- Helper for Lemma 12.14.5: the predecessor index used after transporting a cycle from
`K⟦-1⟧` to `K`. -/
lemma shiftMinusOneTransportNext (i : ℤ) : (down ℤ).next (i - 1) = i - 1 - 1 := by
  simp

/-- Helper for Lemma 12.14.5: transporting a cycle representative from `K⟦-1⟧` to `K` preserves
the cycle condition in the target degree. -/
lemma shiftMinusOneTransportCycle (K : ChainComplex 𝒜 ℤ) {A : 𝒜} {i : ℤ}
    (f : A ⟶ (K⟦(-1 : ℤ)⟧).X i)
    (hf : f ≫ (K⟦(-1 : ℤ)⟧).d i (i - 1) = 0) :
    (f ≫ (K.shiftMinusOneXIso i).hom) ≫ K.d (i - 1) (i - 1 - 1) = 0 := by
  simpa [Category.assoc] using
    shiftMinusOneComponentCycle (K := K) (i := i) (f := f) hf

/-- Helper for Lemma 12.14.5: transporting a lifted cycle class in `K⟦-1⟧` across the chain
homology shift isomorphism gives the lifted cycle class of the transported representative. -/
lemma shiftMinusOneLiftCycles_homologyπ (K : ChainComplex 𝒜 ℤ) {A : 𝒜} {i : ℤ}
    (f : A ⟶ (K⟦(-1 : ℤ)⟧).X i)
    (hf : f ≫ (K⟦(-1 : ℤ)⟧).d i (i - 1) = 0) :
    (K⟦(-1 : ℤ)⟧).liftCycles f (i - 1) (degreewiseSplitLiftNext i) hf ≫
        (K⟦(-1 : ℤ)⟧).homologyπ i ≫
        ((homologyFunctor 𝒜 (down ℤ) 0).shiftIso (-1) i (i - 1) (by omega)).hom.app K =
      K.liftCycles (f ≫ (K.shiftMinusOneXIso i).hom) (i - 1 - 1)
          (shiftMinusOneTransportNext i)
          (shiftMinusOneTransportCycle (K := K) (i := i) (f := f) hf) ≫
        K.homologyπ (i - 1) := by
  have hfShiftedCochain :
      f ≫ ((shiftFunctor (CochainComplex 𝒜 ℤ) (1 : ℤ)).obj
          ((ChainComplex.cochainComplexEquivalence 𝒜).functor.obj K)).d (-i) (-i + 1) = 0 := by
    -- Normalize the shifted cochain differential to the transported chain differential once.
    change -f ≫ ((ChainComplex.cochainComplexEquivalence 𝒜).functor.obj K).d (-i + 1) (-i + 2) = 0
    simpa [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using hf
  -- Route correction: first test whether the chain-side shift transport is already definitionally
  -- the cochain owner theorem on `cochainComplexEquivalence.obj K`.
  simpa [Category.assoc, degreewiseSplitLiftNext, shiftMinusOneTransportNext,
    ChainComplex.shiftMinusOneXIso] using
    (CochainComplex.liftCycles_shift_homologyπ
      ((ChainComplex.cochainComplexEquivalence 𝒜).functor.obj K)
      (f := f) (n := (1 : ℤ)) (i := -i) (j := -i + 1)
      (hj := by simp)
      (hf := hfShiftedCochain)
      (i' := -i + 1) (hi' := by omega)
      (j' := -i + 2) (hj' := by
        change (-i + 1) + 1 = -i + 2
        omega))

/-- Helper for Lemma 12.14.5: specializing the shift transport to `homOfDegreewiseSplit`
identifies the transported lifted-cycle class with the explicit split boundary class. -/
lemma shiftedHomOfDegreewiseSplitLiftCycles {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i - 1) = 0)
    (hz' : (z ≫ (homOfDegreewiseSplit S σ).f i) ≫ (S.X₁⟦(-1 : ℤ)⟧).d i (i - 1) = 0) :
    (S.X₁⟦(-1 : ℤ)⟧).liftCycles (z ≫ (homOfDegreewiseSplit S σ).f i)
          (i - 1) (degreewiseSplitLiftNext i) hz' ≫
        (S.X₁⟦(-1 : ℤ)⟧).homologyπ i ≫
        ((homologyFunctor 𝒜 (down ℤ) 0).shiftIso (-1) i (i - 1) (by omega)).hom.app S.X₁ =
      S.X₁.liftCycles (degreewiseSplitBoundary S σ i z) (i - 2)
          (degreewiseSplitBoundaryNext i)
          (degreewiseSplitBoundaryCycle S σ i z hz) ≫
        S.X₁.homologyπ (i - 1) := by
  have hi2 : i - 1 - 1 = i - 2 := by
    omega
  have hcomponentCyclePred :
      ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
          (S.X₁.shiftMinusOneXIso i).hom) ≫
        S.X₁.d (i - 1) (i - 1 - 1) = 0 := by
    -- Transport the shifted cocycle condition to the unshifted complex one step before rewriting.
    simpa [Category.assoc] using
      shiftMinusOneComponentCycle (K := S.X₁) (i := i)
        (f := z ≫ (homOfDegreewiseSplit S σ).f i) hz'
  have hcomponentCycle :
      ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
          (S.X₁.shiftMinusOneXIso i).hom) ≫
        S.X₁.d (i - 1) (i - 2) = 0 := by
    -- Rewrite the predecessor index once so later `liftCycles` comparisons use the textbook degree.
    rw [← hi2]
    exact hcomponentCyclePred
  have hcycle :
      ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
          (S.X₁.shiftMinusOneXIso i).hom) ≫
        S.X₁.d (i - 1) (i - 2) = 0 := by
    -- Rewrite the transported representative to the explicit split boundary cycle.
    simpa using shiftedHomOfDegreewiseSplitCycle S σ i z hz
  have liftCycles_eq_hcycle
      (hk' :
        ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom) ≫
          S.X₁.d (i - 1) (i - 2) = 0) :
      S.X₁.liftCycles
          ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom)
          (i - 2) (degreewiseSplitBoundaryNext i) hk' =
        S.X₁.liftCycles
          ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom)
          (i - 2) (degreewiseSplitBoundaryNext i) hcycle := by
    -- The lifted cycle class is independent of the chosen proof that the representative is a cycle.
    apply (cancel_mono (S.X₁.iCycles (i - 1))).1
    simp
  have liftCycles_reindex :
      S.X₁.liftCycles
          ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom)
          (i - 1 - 1)
          (by simpa using (HomologicalComplex.next ℤ (i - 1)))
          hcomponentCyclePred =
        S.X₁.liftCycles
          ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom)
          (i - 2) (degreewiseSplitBoundaryNext i) hcomponentCycle := by
    -- The two index choices encode the same boundary degree, so both lifts have the same image in
    -- the cycles object.
    apply (cancel_mono (S.X₁.iCycles (i - 1))).1
    simp
  have liftCycles_eq_boundary
      (hk' : degreewiseSplitBoundary S σ i z ≫ S.X₁.d (i - 1) (i - 2) = 0) :
      S.X₁.liftCycles
          ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom)
          (i - 2) (degreewiseSplitBoundaryNext i) hcycle =
        S.X₁.liftCycles
          (degreewiseSplitBoundary S σ i z)
          (i - 2) (degreewiseSplitBoundaryNext i) hk' := by
    -- Compare the two lifted cycle classes on the nose after postcomposing with `iCycles`.
    apply (cancel_mono (S.X₁.iCycles (i - 1))).1
    calc
      S.X₁.liftCycles
            ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
              (S.X₁.shiftMinusOneXIso i).hom)
            (i - 2) (degreewiseSplitBoundaryNext i) hcycle ≫
          S.X₁.iCycles (i - 1) =
        (z ≫ (homOfDegreewiseSplit S σ).f i) ≫
          (S.X₁.shiftMinusOneXIso i).hom := by
            simp
      _ = degreewiseSplitBoundary S σ i z := by
            simpa using shiftedHomOfDegreewiseSplit_eq_degreewiseSplitBoundary S σ i z
      _ =
        S.X₁.liftCycles (degreewiseSplitBoundary S σ i z)
          (i - 2) (degreewiseSplitBoundaryNext i) hk' ≫
            S.X₁.iCycles (i - 1) := by
              simp
  -- Route correction: first transport the shifted homology class, then rewrite its representative.
  calc
    (S.X₁⟦(-1 : ℤ)⟧).liftCycles (z ≫ (homOfDegreewiseSplit S σ).f i)
          (i - 1) (degreewiseSplitLiftNext i) hz' ≫
        (S.X₁⟦(-1 : ℤ)⟧).homologyπ i ≫
        ((homologyFunctor 𝒜 (down ℤ) 0).shiftIso (-1) i (i - 1) (by omega)).hom.app S.X₁ =
      S.X₁.liftCycles
          ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom)
          (i - 1 - 1)
          (by simpa using (HomologicalComplex.next ℤ (i - 1)))
          hcomponentCyclePred ≫
        S.X₁.homologyπ (i - 1) := by
          simpa [degreewiseSplitLiftNext i] using
            shiftMinusOneLiftCycles_homologyπ (K := S.X₁) (i := i)
              (f := z ≫ (homOfDegreewiseSplit S σ).f i) hz'
    _ =
      S.X₁.liftCycles
          ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom)
          (i - 2) (degreewiseSplitBoundaryNext i) hcomponentCycle ≫
        S.X₁.homologyπ (i - 1) := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ S.X₁.homologyπ (i - 1)) liftCycles_reindex
    _ =
      S.X₁.liftCycles
          ((z ≫ (homOfDegreewiseSplit S σ).f i) ≫
            (S.X₁.shiftMinusOneXIso i).hom)
          (i - 2) (degreewiseSplitBoundaryNext i) hcycle ≫
        S.X₁.homologyπ (i - 1) := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ S.X₁.homologyπ (i - 1))
              (liftCycles_eq_hcycle hcomponentCycle).symm
    _ =
      S.X₁.liftCycles (degreewiseSplitBoundary S σ i z) (i - 2)
          (degreewiseSplitBoundaryNext i)
          (degreewiseSplitBoundaryCycle S σ i z hz) ≫
        S.X₁.homologyπ (i - 1) := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ S.X₁.homologyπ (i - 1))
              (liftCycles_eq_boundary
                (degreewiseSplitBoundaryCycle S σ i z hz))

/-- Helper for Lemma 12.14.5: evaluating the chain-homology `shiftMap` of the explicit connecting
chain map on a refined cycle class yields the same explicit split boundary representative. -/
lemma shiftMapHomOfDegreewiseSplitOnLiftCycles {A : 𝒜} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i - 1) = 0) :
    S.X₃.liftCycles z (i - 1) (degreewiseSplitLiftNext i) hz ≫ S.X₃.homologyπ i ≫
        (homologyFunctor 𝒜 (down ℤ) 0).shiftMap (ChainComplex.homOfDegreewiseSplit S σ)
          i (i - 1) (by omega) =
        S.X₁.liftCycles (degreewiseSplitBoundary S σ i z) (i - 2)
          (degreewiseSplitBoundaryNext i)
          (degreewiseSplitBoundaryCycle S σ i z hz) ≫
        S.X₁.homologyπ (i - 1) := by
  -- Route correction: normalize `shiftMap` to a shifted representative-level equality first.
  dsimp [Functor.shiftMap]
  change S.X₃.liftCycles z (i - 1) (degreewiseSplitLiftNext i) hz ≫
      S.X₃.homologyπ i ≫ homologyMap (ChainComplex.homOfDegreewiseSplit S σ) i ≫
        ((homologyFunctor 𝒜 (down ℤ) 0).shiftIso (-1) i (i - 1) (by omega)).hom.app S.X₁ =
      S.X₁.liftCycles (degreewiseSplitBoundary S σ i z) (i - 2)
        (degreewiseSplitBoundaryNext i)
        (degreewiseSplitBoundaryCycle S σ i z hz) ≫
      S.X₁.homologyπ (i - 1)
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  -- The remaining comparison is exactly the transported lift-cycles statement specialized above.
  exact shiftedHomOfDegreewiseSplitLiftCycles S σ i z hz _

-- Proof sketch: compare the explicit chain map `homOfDegreewiseSplit S σ` from
-- Lemma `12.14.4` with the canonical boundary map in the snake-lemma construction of
-- the homology long exact sequence; the identification `H_i(A[-1]) ≅ H_{i-1}(A)` is the owner
-- shift-map construction `(homologyFunctor 𝒜 (ComplexShape.down ℤ) 0).shiftMap` specialized to
-- `k = -1`.
/-- Lemma 12.14.5: after identifying `H_i(A[-1]_•)` with `H_{i-1}(A_•)`, the homology map
induced by the explicit chain map `δ(σ) : C_• ⟶ A[-1]_•` of Lemma 12.14.4 is exactly the
connecting morphism occurring in the long exact homology sequence of the short exact sequence of
chain complexes. -/
@[stacks 011E]
theorem homologyMap_homOfDegreewiseSplit_eq_δ (i : ℤ) :
    (homologyFunctor 𝒜 (down ℤ) 0).shiftMap (ChainComplex.homOfDegreewiseSplit S σ)
      i (i - 1) (by omega) =
      hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) := by
  let deltaSigma :
      S.X₃.homology i ⟶ S.X₁.homology (i - 1) :=
    (homologyFunctor 𝒜 (down ℤ) 0).shiftMap (ChainComplex.homOfDegreewiseSplit S σ)
      i (i - 1) (by omega)
  let delta :
      S.X₃.homology i ⟶ S.X₁.homology (i - 1) :=
    hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1))
  -- Compare both morphisms on arbitrary refined cycle representatives of `H_i(S.X₃)`.
  apply yoneda.map_injective
  ext A x
  have hi_next : (down ℤ).next i = i - 1 := degreewiseSplitLiftNext i
  obtain ⟨A', π, _, z, hz, hx⟩ :=
    S.X₃.eq_liftCycles_homologyπ_up_to_refinements x (i - 1) hi_next
  -- Refinements are epimorphic, so it is enough to compare after precomposing by `π`.
  apply (cancel_epi π).1
  calc
    π ≫ x ≫ deltaSigma =
      (π ≫ x) ≫ deltaSigma := by
          simp
    _ =
      S.X₃.liftCycles z (i - 1) (degreewiseSplitLiftNext i) hz ≫
        S.X₃.homologyπ i ≫ deltaSigma := by
          simpa [deltaSigma] using congrArg (fun t ↦ t ≫ deltaSigma) hx
    _ = S.X₁.liftCycles (degreewiseSplitBoundary S σ i z) (i - 2)
          (degreewiseSplitBoundaryNext i)
          (degreewiseSplitBoundaryCycle S σ i z hz) ≫
        S.X₁.homologyπ (i - 1) := by
          simpa [deltaSigma] using
            (shiftMapHomOfDegreewiseSplitOnLiftCycles S σ i z hz)
    _ =
      S.X₃.liftCycles z (i - 1) (degreewiseSplitLiftNext i) hz ≫
        S.X₃.homologyπ i ≫ delta := by
          simpa [delta] using
            (shortExactBoundaryOnLiftCycles S hS σ i z hz).symm
    _ = (π ≫ x) ≫ delta := by
          simpa [delta] using (congrArg (fun t ↦ t ≫ delta) hx).symm
    _ = π ≫ x ≫ delta := by
          simp

end
end ChainComplex
