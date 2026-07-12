import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape HomologicalComplex

universe u v

noncomputable section

namespace CategoryTheory.ShortComplex

variable {V : Type u} [Category.{v} V] [Abelian V]
variable {S : ShortComplex (CochainComplex V ℤ)}
variable (hS : S.ShortExact)
variable (spl : ∀ n : ℤ, (S.map (HomologicalComplex.eval V (up ℤ) n)).Splitting)

/-
Domain-style sampling in the cohomology-boundary owner API:
- primitive split datum: `CochainComplex.homOfDegreewiseSplit`
- degreewise companion formula: `CochainComplex.homOfDegreewiseSplit_f`
- owner short-exact boundary: `ShortComplex.ShortExact.δ`
- owner triangle boundary: `CochainComplex.homologyδOfTriangle`

Lemma 12.14.11 is a `bridge/view`: it identifies the triangle-level boundary map attached to the
degreewise split triangle with the short-exact-sequence boundary map `hS.δ`.
-/

-- Proof sketch: use the owner triangle boundary
-- `CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl)` for the
-- cohomology map induced by `CochainComplex.homOfDegreewiseSplit S spl`, then compare it with the
-- snake-lemma boundary `hS.δ` using `CochainComplex.homOfDegreewiseSplit_f` and the description of
-- `ShortComplex.ShortExact.δ`.
/-- Helper for Lemma 12.14.11: the split lift in `B^i` of a cocycle in `C^i`. -/
abbrev degreewiseSplitLift {A : V} (i : ℤ) (z : A ⟶ S.X₃.X i) : A ⟶ S.X₂.X i :=
  z ≫ (spl i).s

/-- Helper for Lemma 12.14.11: the boundary representative in `A^(i + 1)` obtained by
differentiating the split lift. -/
abbrev degreewiseSplitBoundary {A : V} (i : ℤ) (z : A ⟶ S.X₃.X i) : A ⟶ S.X₁.X (i + 1) :=
  degreewiseSplitLift (S := S) spl i z ≫ S.X₂.d i (i + 1) ≫ (spl (i + 1)).r

/-- Helper for Lemma 12.14.11: in the cochain shape, the successor of `i` is `i + 1`. -/
lemma degreewise_split_lift_next (i : ℤ) : (up ℤ).next i = i + 1 := by
  simp

/-- Helper for Lemma 12.14.11: the split lift and its boundary satisfy the relations used by the
connecting morphism formula for a short exact sequence. -/
lemma degreewise_split_boundary_data {A : V} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i + 1) = 0) :
    degreewiseSplitLift (S := S) spl i z ≫ S.g.f i = z ∧
      degreewiseSplitBoundary (S := S) spl i z ≫ S.f.f (i + 1) =
        degreewiseSplitLift (S := S) spl i z ≫ S.X₂.d i (i + 1) := by
  have hs : (spl i).s ≫ S.g.f i = 𝟙 _ := by
    simpa using (spl i).s_g
  have hr : (spl (i + 1)).r ≫ S.f.f (i + 1) = 𝟙 _ - S.g.f (i + 1) ≫ (spl (i + 1)).s := by
    simpa using (spl (i + 1)).r_f
  constructor
  · -- The chosen lift is a section of `S.g` in degree `i`.
    simpa [degreewiseSplitLift, Category.assoc] using congrArg (fun t ↦ z ≫ t) hs
  · -- Expanding `r_f` leaves one correction term, which vanishes by the cocycle condition on `z`.
    have hcomm :
        S.X₂.d i (i + 1) ≫ S.g.f (i + 1) = S.g.f i ≫ S.X₃.d i (i + 1) := by
      simpa using S.g.comm i (i + 1)
    have hkill :
        z ≫ (spl i).s ≫ S.X₂.d i (i + 1) ≫ S.g.f (i + 1) ≫ (spl (i + 1)).s = 0 := by
      calc
        z ≫ (spl i).s ≫ S.X₂.d i (i + 1) ≫ S.g.f (i + 1) ≫ (spl (i + 1)).s =
            z ≫ (spl i).s ≫ (S.X₂.d i (i + 1) ≫ S.g.f (i + 1)) ≫ (spl (i + 1)).s := by
              simp [Category.assoc]
        _ =
            z ≫ (spl i).s ≫ (S.g.f i ≫ S.X₃.d i (i + 1)) ≫ (spl (i + 1)).s := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ z ≫ (spl i).s ≫ t ≫ (spl (i + 1)).s) hcomm
        _ = z ≫ ((spl i).s ≫ S.g.f i) ≫ S.X₃.d i (i + 1) ≫ (spl (i + 1)).s := by
              simp [Category.assoc]
        _ = z ≫ S.X₃.d i (i + 1) ≫ (spl (i + 1)).s := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ z ≫ t ≫ S.X₃.d i (i + 1) ≫ (spl (i + 1)).s) hs
        _ = 0 := by
              simpa [Category.assoc] using congrArg (fun t ↦ t ≫ (spl (i + 1)).s) hz
    have hsub :
        z ≫ (spl i).s ≫ S.X₂.d i (i + 1) ≫
            (𝟙 _ - S.g.f (i + 1) ≫ (spl (i + 1)).s) =
          z ≫ (spl i).s ≫ S.X₂.d i (i + 1) := by
      -- TODO: expand the postcomposition across the subtraction using the preadditive composition
      -- lemmas, then collapse the correction term with `hkill`.
      sorry
    calc
      degreewiseSplitBoundary (S := S) spl i z ≫ S.f.f (i + 1) =
          z ≫ (spl i).s ≫ S.X₂.d i (i + 1) ≫ ((spl (i + 1)).r ≫ S.f.f (i + 1)) := by
            simp [degreewiseSplitBoundary, degreewiseSplitLift, Category.assoc]
      _ = z ≫ (spl i).s ≫ S.X₂.d i (i + 1) ≫
            (𝟙 _ - S.g.f (i + 1) ≫ (spl (i + 1)).s) := by
              simpa [Category.assoc] using congrArg (fun t ↦ z ≫ (spl i).s ≫ S.X₂.d i (i + 1) ≫ t) hr
      _ = z ≫ (spl i).s ≫ S.X₂.d i (i + 1) := hsub
      _ = degreewiseSplitLift (S := S) spl i z ≫ S.X₂.d i (i + 1) := by
            simp [degreewiseSplitLift]

/-- Helper for Lemma 12.14.11: in the cochain shape, the successor of `i + 1` is `i + 2`. -/
lemma degreewise_split_boundary_next (i : ℤ) : (up ℤ).next (i + 1) = i + 2 := by
  simpa [add_assoc] using degreewise_split_lift_next (i + 1)

/-- Helper for Lemma 12.14.11: the boundary representative is a cocycle in degree `i + 1`. -/
lemma degreewise_split_boundary_cycle {A : V} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i + 1) = 0) :
    degreewiseSplitBoundary (S := S) spl i z ≫ S.X₁.d (i + 1) (i + 2) = 0 := by
  letI : Mono (S.f.f (i + 2)) := (spl (i + 2)).mono_f
  have hdata := degreewise_split_boundary_data (S := S) (spl := spl) i z hz
  have hcomm :
      S.X₁.d (i + 1) (i + 2) ≫ S.f.f (i + 2) =
        S.f.f (i + 1) ≫ S.X₂.d (i + 1) (i + 2) := by
    simpa using S.f.comm (i + 1) (i + 2)
  -- Postcompose with the split monomorphism in degree `i + 2` and rewrite through `S.f.comm`.
  apply (cancel_mono (S.f.f (i + 2))).1
  simpa using
    calc
      (degreewiseSplitBoundary (S := S) spl i z ≫ S.X₁.d (i + 1) (i + 2)) ≫ S.f.f (i + 2) =
          degreewiseSplitBoundary (S := S) spl i z ≫
            (S.f.f (i + 1) ≫ S.X₂.d (i + 1) (i + 2)) := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ degreewiseSplitBoundary (S := S) spl i z ≫ t) hcomm
      _ =
          degreewiseSplitLift (S := S) spl i z ≫ S.X₂.d i (i + 1) ≫ S.X₂.d (i + 1) (i + 2) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ t ≫ S.X₂.d (i + 1) (i + 2)) hdata.2
      _ = 0 := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ degreewiseSplitLift (S := S) spl i z ≫ t)
                (S.X₂.d_comp_d i (i + 1) (i + 2))

/-- Helper for Lemma 12.14.11: the triangle boundary map sends a refined cocycle class to the
explicit boundary representative coming from the degreewise splitting. -/
lemma homologyδ_of_degreewise_split_on_liftCycles {A : V} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i + 1) = 0) :
    S.X₃.liftCycles z (i + 1) (degreewise_split_lift_next i) hz ≫ S.X₃.homologyπ i ≫
        CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl)
          i (i + 1) rfl =
      S.X₁.liftCycles (degreewiseSplitBoundary (S := S) spl i z) (i + 2)
          (degreewise_split_boundary_next i)
          (degreewise_split_boundary_cycle (S := S) (spl := spl) i z hz) ≫
        S.X₁.homologyπ (i + 1) := by
  -- TODO: after `dsimp [CochainComplex.homologyδOfTriangle, Functor.shiftMap,
  -- CochainComplex.homologyFunctor_shift]`, rewrite by
  -- `HomologicalComplex.homologyπ_naturality_assoc` and
  -- `HomologicalComplex.liftCycles_comp_cyclesMap_assoc`, then identify the shifted cycle
  -- condition for `z ≫ (CochainComplex.homOfDegreewiseSplit S spl).f i` via the explicit sign in
  -- the shifted differential and finish with the non-`assoc` form of
  -- `CochainComplex.liftCycles_shift_homologyπ`.
  sorry

/-- Helper for Lemma 12.14.11: the short-exact-sequence connecting morphism sends the same
refined cocycle class to the same explicit boundary representative. -/
lemma short_exact_boundary_on_liftCycles {A : V} (i : ℤ) (z : A ⟶ S.X₃.X i)
    (hz : z ≫ S.X₃.d i (i + 1) = 0) :
    S.X₃.liftCycles z (i + 1) (degreewise_split_lift_next i) hz ≫ S.X₃.homologyπ i ≫
        hS.δ i (i + 1) rfl =
      S.X₁.liftCycles (degreewiseSplitBoundary (S := S) spl i z) (i + 2)
          (degreewise_split_boundary_next i)
          (degreewise_split_boundary_cycle (S := S) (spl := spl) i z hz) ≫
        S.X₁.homologyπ (i + 1) := by
  have hdata := degreewise_split_boundary_data (S := S) spl i z hz
  -- Apply the owner formula for the connecting morphism to the split lift and its boundary.
  simpa [degreewiseSplitLift, degreewiseSplitBoundary] using
    hS.δ_eq i (i + 1) rfl z hz
      (degreewiseSplitLift (S := S) spl i z) hdata.1
      (degreewiseSplitBoundary (S := S) spl i z) hdata.2
      (i + 2) (degreewise_split_boundary_next i)

/-- Lemma 12.14.11: for a degreewise splitting of a short exact sequence
`0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0`, the cohomology boundary map of the degreewise split triangle, i.e. of
the canonical connecting morphism `CochainComplex.homOfDegreewiseSplit S spl : C^• ⟶ A^•[1]`, is
the connecting morphism in the associated long exact cohomology sequence. -/
theorem homologyMap_homOfDegreewiseSplit_eq_δ (i : ℤ) :
    CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl) i (i + 1)
      rfl = hS.δ i (i + 1) rfl := by
  -- We compare both morphisms on arbitrary refined cocycle representatives of `H^i(C^•)`.
  apply yoneda.map_injective
  ext A x
  have hi_next : (up ℤ).next i = i + 1 := by simp
  obtain ⟨A', π, _, z, hz, hx⟩ :=
    S.X₃.eq_liftCycles_homologyπ_up_to_refinements x (i + 1) hi_next
  -- Refinements are epimorphic, so it suffices to compare both sides after precomposing by `π`.
  apply (cancel_epi π).1
  calc
    π ≫ x ≫ CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl)
        i (i + 1) rfl =
      (π ≫ x) ≫ CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl)
        i (i + 1) rfl := by simp
    _ =
      S.X₃.liftCycles z (i + 1) (degreewise_split_lift_next i) hz ≫ S.X₃.homologyπ i ≫
        CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl)
          i (i + 1) rfl := by
            simpa using congrArg
              (fun t ↦ t ≫
                CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl)
                  i (i + 1) rfl) hx
    _ = S.X₁.liftCycles (degreewiseSplitBoundary (S := S) spl i z) (i + 2)
          (degreewise_split_boundary_next i)
          (degreewise_split_boundary_cycle (S := S) (spl := spl) i z hz) ≫
        S.X₁.homologyπ (i + 1) := by
          rw [homologyδ_of_degreewise_split_on_liftCycles (S := S) (spl := spl) i z hz]
    _ =
      S.X₃.liftCycles z (i + 1) (degreewise_split_lift_next i) hz ≫ S.X₃.homologyπ i ≫
        hS.δ i (i + 1) rfl := by
          rw [short_exact_boundary_on_liftCycles (S := S) hS spl i z hz]
    _ = (π ≫ x) ≫ hS.δ i (i + 1) rfl := by
          simpa using (congrArg (fun t ↦ t ≫ hS.δ i (i + 1) rfl) hx).symm
    _ = π ≫ x ≫ hS.δ i (i + 1) rfl := by simp

end CategoryTheory.ShortComplex
