

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_4_4_3_1 (from Chap04) -/
open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule
noncomputable section

universe u v

namespace Representation

local notation "L²(" G ")" => G →₂[(Measure.haar : Measure G)] ℂ

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [Finite G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ W]

local instance : Fintype G := Fintype.ofFinite G

local instance : Invertible (Nat.card G : ℂ) := by
  refine invertibleOfNonzero ?_
  exact_mod_cast Nat.card_pos.ne'

/-- Helper for Remark 4-4.3-1: the source-faithful plain-function model of the regular
representation acts by left translation `(ρ_s f)(t) = f (s⁻¹ * t)`. -/
private def funLeftRegular : Representation ℂ G (G → ℂ) :=
  { toFun := fun s ↦
      { toFun := fun f t ↦ f (s⁻¹ * t)
        map_add' := by
          intro f g
          rfl
        map_smul' := by
          intro a f
          rfl }
    map_one' := by
      ext f t
      simp
    map_mul' := by
      intro s t
      ext f x
      simp [mul_assoc] }

/-- Helper for Remark 4-4.3-1: the canonical map from plain functions on a finite group into the
Haar `L²` space. -/
private def funLeftRegular_toL2 : (G → ℂ) →ₗ[ℂ] L²(G) :=
  { toFun := fun f =>
      (MeasureTheory.MemLp.of_discrete (μ := (Measure.haar : Measure G))
        (f := f) (p := (2 : ℝ≥0∞))).toLp f
    map_add' := by
      intro f g
      simpa using MeasureTheory.MemLp.toLp_add
        (MeasureTheory.MemLp.of_discrete (μ := (Measure.haar : Measure G))
          (f := f) (p := (2 : ℝ≥0∞)))
        (MeasureTheory.MemLp.of_discrete (μ := (Measure.haar : Measure G))
          (f := g) (p := (2 : ℝ≥0∞)))
    map_smul' := by
      intro a f
      simpa using MeasureTheory.MemLp.toLp_const_smul
        (p := (2 : ℝ≥0∞)) a
        (MeasureTheory.MemLp.of_discrete (μ := (Measure.haar : Measure G))
          (f := f) (p := (2 : ℝ≥0∞))) }

/-- Helper for Remark 4-4.3-1: singleton sets have positive Haar measure in the finite discrete
compact-group setting, so almost-everywhere equal functions are pointwise equal. -/
private theorem haar_singleton_pos (g : G) : 0 < (Measure.haar : Measure G) {g} := by
  -- Finite Hausdorff groups are discrete, so a singleton is a nonempty open set.
  simpa using (isOpen_discrete {g}).measure_pos (μ := (Measure.haar : Measure G))
    (Set.singleton_nonempty g)

/-- Helper for Remark 4-4.3-1: the source function-space regular model is equivariantly
equivalent to the Haar `L²` regular representation. -/
private def funLeftRegular_equiv_l2Regular : funLeftRegular (G := G).Equiv (l2Regular G) := by
  refine Equiv.mk (LinearEquiv.ofBijective (funLeftRegular_toL2 (G := G)) ?_) ?_
  · constructor
    · intro f g hfg
      let hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (Measure.haar : Measure G) :=
        MeasureTheory.MemLp.of_discrete (μ := (Measure.haar : Measure G))
          (f := f) (p := (2 : ℝ≥0∞))
      let hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (Measure.haar : Measure G) :=
        MeasureTheory.MemLp.of_discrete (μ := (Measure.haar : Measure G))
          (f := g) (p := (2 : ℝ≥0∞))
      -- Equality in `L²` gives almost-everywhere equality of representatives.
      have hae : f =ᵐ[(Measure.haar : Measure G)] g := by
        exact (show hf.toLp f = hg.toLp g ↔ f =ᵐ[(Measure.haar : Measure G)] g by
          simp [MeasureTheory.MemLp.toLp]).mp hfg
      -- Positivity of singleton Haar measure upgrades a.e. equality to pointwise equality.
      ext x
      exact (MeasureTheory.ae_iff_of_countable.mp hae) x (ne_of_gt (haar_singleton_pos (G := G) x))
    · intro F
      -- Every `L²` class on a finite group is represented by its underlying function.
      refine ⟨F, ?_⟩
      simp [funLeftRegular_toL2, MeasureTheory.MemLp.toLp]
  · intro g
    ext f
    let hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (Measure.haar : Measure G) :=
      MeasureTheory.MemLp.of_discrete (μ := (Measure.haar : Measure G))
        (f := f) (p := (2 : ℝ≥0∞))
    -- Both actions are left translation by `g⁻¹`; `toLp_compMeasurePreserving` records this.
    have hEq :
        (l2Regular G) g (funLeftRegular_toL2 (G := G) f) =
          funLeftRegular_toL2 (G := G) (funLeftRegular (G := G) g f) := by
      rw [l2Regular_apply]
      symm
      simpa [funLeftRegular, funLeftRegular_toL2] using
        (MeasureTheory.Lp.toLp_compMeasurePreserving
          (μ := (Measure.haar : Measure G)) (μb := (Measure.haar : Measure G))
          (f := fun t : G ↦ g⁻¹ * t) hf
          (measurePreserving_mul_left (Measure.haar : Measure G) g⁻¹))
    exact Filter.EventuallyEq.of_eq <| by
      simpa [LinearMap.comp_apply] using
        congrArg (fun z : L²(G) => (z : G → ℂ)) hEq

/-- Helper for Remark 4-4.3-1: the usual finite left-regular representation is the same regular
model after identifying finitely supported functions with all functions on a finite group. -/
private def leftRegular_equiv_l2Regular : (leftRegular ℂ G).Equiv (l2Regular G) := by
  let eFinsuppFun : (leftRegular ℂ G).Equiv funLeftRegular (G := G) := by
    refine Equiv.mk (Finsupp.linearEquivFunOnFinite ℂ ℂ G) ?_
    intro g
    apply LinearMap.ext
    intro f
    ext x
    -- The finite-support owner and the plain-function owner have the same translation formula.
    change ((leftRegular ℂ G) g f) x = f (g⁻¹ * x)
    exact Representation.ofMulAction_apply (k := ℂ) (G := G) (H := G) g f x
  exact eFinsuppFun.trans (funLeftRegular_equiv_l2Regular (G := G))

/-- Helper for Remark 4-4.3-1: postcomposition with the regular-model equivalence identifies
intertwining maps into `leftRegular` and into `l2Regular`. -/
private def intertwiningMap_leftRegular_l2Regular_equiv (σ : Representation ℂ G W) :
    σ.IntertwiningMap (leftRegular ℂ G) ≃ₗ[ℂ] σ.IntertwiningMap (l2Regular G) :=
  { toFun := fun f ↦ (leftRegular_equiv_l2Regular (G := G)).toIntertwiningMap.comp f
    invFun := fun f ↦ (leftRegular_equiv_l2Regular (G := G)).symm.toIntertwiningMap.comp f
    left_inv := by
      intro f
      -- Compose with the equivalence and its inverse; the linear maps cancel pointwise.
      apply IntertwiningMap.ext
      ext x
      simp
    right_inv := by
      intro f
      -- The same cancellation works in the reverse direction.
      apply IntertwiningMap.ext
      ext x
      simp
    map_add' := by
      intro f g
      -- Postcomposition is linear on the target intertwining space.
      apply IntertwiningMap.ext
      ext x
      simp
    map_smul' := by
      intro a f
      -- Scalar multiplication commutes with postcomposition.
      apply IntertwiningMap.ext
      ext x
      simp }

end PeterWeyl

section FiniteRegularMultiplicity

variable {G : Type u} [Group G] [Finite G]
variable {W : Type v} [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ W]

local instance : Fintype G := Fintype.ofFinite G

local instance : Invertible (Nat.card G : ℂ) := by
  refine invertibleOfNonzero ?_
  exact_mod_cast Nat.card_pos.ne'

/-- Helper for Remark 4-4.3-1: in the finite case, the intertwining space into the ordinary
left-regular representation already has dimension `dim σ`. This is the finite-group
character-sum input transported later to `l2Regular`. -/
private theorem leftRegular_intertwining_finrank (σ : Representation ℂ G W) :
    Module.finrank ℂ (σ.IntertwiningMap (leftRegular ℂ G)) = Module.finrank ℂ W := by
  let ρ := leftRegular ℂ G
  have hsum :
      ∑ g : G, ρ.character g * σ.character g⁻¹ =
        (Nat.card G : ℂ) * Module.finrank ℂ W := by
    -- Only the identity contributes because the left-regular character vanishes off `1`.
    rw [Finset.sum_eq_single 1]
    · rw [leftRegular_character_one]
      simp [σ.char_one]
    · intro g _ hg
      rw [leftRegular_character_eq_zero_of_ne_one hg]
      simp
    · intro h
      exact False.elim (h (Finset.mem_univ 1))
  have hfinrank :
      (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) =
        Module.finrank ℂ W := by
    -- Apply the orthogonality formula and then collapse the sum with `hsum`.
    calc
      (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) =
          (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ := by
            symm
            simpa using (card_inv_mul_sum_char_mul_char_eq_finrank σ ρ)
      _ = Module.finrank ℂ W := by
        rw [hsum]
        field_simp
  exact_mod_cast hfinrank

end FiniteRegularMultiplicity

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [Finite G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ W]

local instance : Fintype G := Fintype.ofFinite G

/-- Remark 4-4.3-1 (2): source part (b). Each irreducible finite-dimensional complex
continuous representation of a compact group on a Hausdorff complex topological vector space
occurs in the `L²` regular representation with multiplicity equal to its degree. Using the
chapter's multiplicity owner, this is the statement that the intertwining space from `σ` into the
`L²` regular representation has complex dimension `dim σ`. -/
theorem finrank_intertwiningMap_l2Regular
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] :
    Module.finrank ℂ (σ.IntertwiningMap (l2Regular G)) =
      Module.finrank ℂ W := by
  let _ := hσ
  -- Route correction: transport the established finite left-regular multiplicity formula across
  -- the source-faithful equivalence `leftRegular ≃ l2Regular`.
  calc
    Module.finrank ℂ (σ.IntertwiningMap (l2Regular G)) =
        Module.finrank ℂ (σ.IntertwiningMap (leftRegular ℂ G)) := by
          symm
          exact (intertwiningMap_leftRegular_l2Regular_equiv (G := G) (W := W) σ).finrank_eq
    _ = Module.finrank ℂ W := by
          simpa using leftRegular_intertwining_finrank (G := G) (W := W) σ
end PeterWeyl

end Representation
