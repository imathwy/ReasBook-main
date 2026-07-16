import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.InducedLattice

/-!
# The reduction-of-induced isomorphism (part 2 of `hind`) — construction in progress

This file builds the `G`-equivariant isomorphism `reduction (Ind L) ≅ Ind (reduction L)` (the second,
deeper half of the bridge hypothesis `hind` for step (D) of Theorem 17-17.2-1), where
`Ind L = inducedStableLattice V L`.

The strategy is to build the inverse direction `Ψ : Ind (reduction L) → reduction (Ind L)`,
`IndV.mk g [l] ↦ [indMk V g ↑l]`, via `Coinvariants.lift`, then conclude it is an isomorphism by a
surjection + dimension count.

So far this file provides the foundational *reduced generator maps*:

* `redMkA V L g : reduction L →ₗ[A] reduction (Ind L)`  (the `A`-linear `[l] ↦ [indMk V g ↑l]`),
* `redMk  V L g : reduction L →ₗ[k̄] reduction (Ind L)` (its `k̄`-linear upgrade),

together with the helper `reductionUpgrade` (turn an `A`-linear map between lattice reductions into a
`k̄`-linear one — the `A`- and `k̄`-actions agree by `residue_smul_reduction`).
-/

noncomputable section

universe u

open CategoryTheory Finsupp TensorProduct
open scoped Representation

namespace Representation

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k̄" => IsLocalRing.ResidueField A

/-- On a lattice reduction, the residue-field scalar `mk a` and the underlying ring scalar `a` act
the same way (the `k̄`-action is the `A`-action through `A ↠ k̄`). -/
theorem residue_smul_reduction {E : Type u} [AddCommGroup E] [Module K E] [Module A E]
    [IsScalarTower A K E] (ρ : Representation K G E) (L : StableLattice A ρ) (a : A)
    (x : L.reduction) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) • x = a • x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [StableLattice.reduction_smul_mk]; rfl

/-- Upgrade an `A`-linear map between lattice reductions to a `k̄`-linear map; the `A`- and
`k̄`-actions agree by `residue_smul_reduction`. -/
def reductionUpgrade {E F : Type u} [AddCommGroup E] [Module K E] [Module A E] [IsScalarTower A K E]
    [AddCommGroup F] [Module K F] [Module A F] [IsScalarTower A K F]
    {ρ : Representation K G E} {σ : Representation K G F}
    (L : StableLattice A ρ) (M : StableLattice A σ) (f : L.reduction →ₗ[A] M.reduction) :
    L.reduction →ₗ[IsLocalRing.ResidueField A] M.reduction where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    show f ((Ideal.Quotient.mk _ a : IsLocalRing.ResidueField A) • x)
      = (Ideal.Quotient.mk _ a : IsLocalRing.ResidueField A) • f x
    rw [residue_smul_reduction, map_smul, residue_smul_reduction]

/-- The `A`-linear reduced generator map `[l] ↦ [indMk V g ↑l]` from `reduction L` to
`reduction (Ind L)`. -/
def redMkA {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) (g : G) :
    L.reduction →ₗ[A] (inducedStableLattice V L).reduction :=
  Submodule.liftQ L.maximalIdealSubmodule
    ((Submodule.mkQ _).comp
      (((indMk V g).restrictScalars A ∘ₗ L.toSubmodule.subtype).codRestrict
        (inducedStableLattice V L).toSubmodule
        (fun l => Submodule.subset_span ⟨(g, l), rfl⟩)))
    (by
      intro w hw
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      refine Submodule.smul_induction_on hw ?_ ?_
      · intro a ha t _; rw [map_smul]; exact Submodule.smul_mem_smul ha Submodule.mem_top
      · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy)

@[simp] theorem redMkA_mk {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) (g : G)
    (l : L.toSubmodule) :
    redMkA V L g (Submodule.Quotient.mk l)
      = Submodule.Quotient.mk
          (⟨indMk V g (l : V.V), Submodule.subset_span ⟨(g, l), rfl⟩⟩ :
            (inducedStableLattice V L).toSubmodule) := by
  rw [redMkA, Submodule.liftQ_apply]; rfl

/-- The `k̄`-linear reduced generator map `[l] ↦ [indMk V g ↑l]`. -/
def redMk {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) (g : G) :
    L.reduction →ₗ[IsLocalRing.ResidueField A] (inducedStableLattice V L).reduction where
  toFun := redMkA V L g
  map_add' := (redMkA V L g).map_add
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    show redMkA V L g ((Ideal.Quotient.mk _ a : IsLocalRing.ResidueField A) • x)
      = (Ideal.Quotient.mk _ a : IsLocalRing.ResidueField A) • redMkA V L g x
    rw [residue_smul_reduction, map_smul, residue_smul_reduction]

@[simp] theorem redMk_mk {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) (g : G)
    (l : L.toSubmodule) :
    redMk V L g (Submodule.Quotient.mk l)
      = Submodule.Quotient.mk
          (⟨indMk V g (l : V.V), Submodule.subset_span ⟨(g, l), rfl⟩⟩ :
            (inducedStableLattice V L).toSubmodule) :=
  redMkA_mk V L g l

/-- The induced generators satisfy the `H`-coinvariance relation already in `Ind L` (before
reduction): `indMk V (↑h·g) (V.ρ h x) = indMk V g x`.  This is the coinvariants relation of the
`K`-induction `IndV H.subtype V.ρ`. -/
theorem indMk_act_eq {H : Subgroup G} (V : FDRep K H) (g : G) (h : H) (x : V.V) :
    indMk V (↑h * g) (V.ρ h x) = indMk V g x := by
  show Representation.Coinvariants.mk _ (single (↑h * g) (1:K) ⊗ₜ[K] V.ρ h x)
    = Representation.Coinvariants.mk _ (single g (1:K) ⊗ₜ[K] x)
  rw [show (single (↑h * g) (1:K) ⊗ₜ[K] V.ρ h x)
      = (Representation.tprod ((Representation.leftRegular K G).comp H.subtype) V.ρ) h
          (single g (1:K) ⊗ₜ[K] x) by
    rw [Representation.tprod_apply, TensorProduct.map_tmul]
    congr 1
    simp [Representation.leftRegular, Representation.ofMulAction_single]]
  exact Representation.Coinvariants.mk_self_apply _ h _

/-- Compatibility of the reduced generators with the `H`-action:
`redMk (↑h·g) ∘ redRep h = redMk g`. -/
theorem redMk_act_eq {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) (g : G) (h : H)
    (y : L.reduction) :
    redMk V L (↑h * g) (L.reductionRepresentation h y) = redMk V L g y := by
  obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [StableLattice.reductionRepresentation_apply_mk, redMk_mk, redMk_mk]
  congr 1
  apply Subtype.ext
  show indMk V (↑h * g) ((L.toRepresentation h l : L.toSubmodule) : V.V) = indMk V g (l : V.V)
  rw [StableLattice.toRepresentation_apply_coe]
  exact indMk_act_eq V g h (l : V.V)

/-- The `k̄`-linear tensor map `(G →₀ k̄) ⊗ reduction L → reduction (Ind L)`,
`single g r ⊗ y ↦ r • redMk g y`. -/
def psiTensor {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) :
    TensorProduct k̄ (G →₀ k̄) L.reduction →ₗ[k̄] (inducedStableLattice V L).reduction :=
  TensorProduct.lift (Finsupp.linearCombination k̄ (fun g => redMk V L g))

theorem psiTensor_single_tmul {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ)
    (g : G) (r : k̄) (y : L.reduction) :
    psiTensor V L (single g r ⊗ₜ[k̄] y) = r • redMk V L g y := by
  rw [psiTensor, TensorProduct.lift.tmul, Finsupp.linearCombination_single]; rfl

/-- `psiTensor` is invariant under the induced `H`-coinvariance action, so it descends to the induced
coinvariants. -/
theorem psiInvariance {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) (h : H) :
    (psiTensor V L) ∘ₗ
        (Representation.tprod ((Representation.leftRegular k̄ G).comp H.subtype)
          L.reductionRepresentation) h
      = psiTensor V L := by
  apply TensorProduct.ext'
  intro a y
  rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul]
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, TensorProduct.add_tmul, map_add, hp, hq,
      TensorProduct.add_tmul, map_add]
  | single g r =>
      rw [show ((Representation.leftRegular k̄ G).comp H.subtype) h (single g r)
          = single (↑h * g) r by
            simp [Representation.leftRegular, Representation.ofMulAction_single],
        psiTensor_single_tmul, psiTensor_single_tmul, redMk_act_eq]

/-- **The inverse map `Ψ` of the reduction-of-induced isomorphism:**
`Ψ : Ind (reduction L) → reduction (Ind L)`, `IndV.mk g [l] ↦ [indMk V g ↑l]`, obtained by
descending `psiTensor` through the induced coinvariants.  (Its type is, definitionally,
`Ind (reduction L) →ₗ[k̄] reduction (Ind L)`.) -/
def psi {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) :=
  Representation.Coinvariants.lift
    (Representation.tprod ((Representation.leftRegular k̄ G).comp H.subtype)
      L.reductionRepresentation)
    (psiTensor V L) (psiInvariance V L)

@[simp] theorem psi_mk {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) (g : G)
    (l : L.toSubmodule) :
    psi V L (Representation.IndV.mk H.subtype L.reductionRepresentation g
        (Submodule.Quotient.mk l))
      = Submodule.Quotient.mk
          (⟨indMk V g (l : V.V), Submodule.subset_span ⟨(g, l), rfl⟩⟩ :
            (inducedStableLattice V L).toSubmodule) := by
  show psi V L (Representation.Coinvariants.mk _
      (single g (1:k̄) ⊗ₜ[k̄] Submodule.Quotient.mk l)) = _
  simp only [psi, Representation.Coinvariants.lift_mk]
  rw [psiTensor_single_tmul, one_smul, redMk_mk]

/-- `Ψ` is surjective: its image contains every reduced generator `[indMk V g ↑l]`, and these span
`reduction (Ind L)`. -/
theorem psi_surjective {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) :
    Function.Surjective (psi V L) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro x -
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨g, l⟩, rfl⟩ := hy
      exact ⟨Representation.IndV.mk H.subtype L.reductionRepresentation g (Submodule.Quotient.mk l),
        psi_mk V L g l⟩
  | zero =>
      rw [show (Submodule.Quotient.mk (⟨0, Submodule.zero_mem _⟩ :
          (inducedStableLattice V L).toSubmodule) : (inducedStableLattice V L).reduction)
          = 0 from rfl]
      exact Submodule.zero_mem _
  | add a b ha hb iha ihb =>
      rw [show (Submodule.Quotient.mk (⟨a + b, Submodule.add_mem _ ha hb⟩ :
            (inducedStableLattice V L).toSubmodule))
          = Submodule.Quotient.mk (⟨a, ha⟩ : (inducedStableLattice V L).toSubmodule)
            + Submodule.Quotient.mk ⟨b, hb⟩ from rfl]
      exact Submodule.add_mem _ iha ihb
  | smul c a ha iha =>
      rw [show (Submodule.Quotient.mk (⟨c • a, Submodule.smul_mem _ c ha⟩ :
            (inducedStableLattice V L).toSubmodule))
          = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c)
              • Submodule.Quotient.mk (⟨a, ha⟩ : (inducedStableLattice V L).toSubmodule) by
        rw [residue_smul_reduction]; rfl]
      exact Submodule.smul_mem (LinearMap.range (psi V L))
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c) iha

/-- `Ψ` is `G`-equivariant: it intertwines the induced action on `Ind (reduction L)` with the
reduced action on `reduction (Ind L)`.  (Together with `psi_surjective` and a dimension count, this
makes `Ψ` an isomorphism of `k̄[G]`-representations.) -/
theorem psi_equivariant {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) (g' : G) :
    (psi V L) ∘ₗ (Representation.ind H.subtype L.reductionRepresentation g')
      = ((inducedStableLattice V L).reductionRepresentation g') ∘ₗ (psi V L) := by
  apply Representation.IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro y
  obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change psi V L ((Representation.ind H.subtype L.reductionRepresentation g')
      (Representation.IndV.mk H.subtype L.reductionRepresentation g (Submodule.Quotient.mk l)))
    = (inducedStableLattice V L).reductionRepresentation g'
        (psi V L (Representation.IndV.mk H.subtype L.reductionRepresentation g
          (Submodule.Quotient.mk l)))
  rw [Representation.ind_mk, psi_mk, psi_mk,
    StableLattice.reductionRepresentation_apply_mk]
  congr 1
  apply Subtype.ext
  show indMk V (g * g'⁻¹) (l : V.V)
    = ((inducedStableLattice V L).toRepresentation g' ⟨indMk V g (l : V.V), _⟩ :
        (inducedStableLattice V L).toSubmodule)
  rw [StableLattice.toRepresentation_apply_coe, indOwnerK_rho_indMk]

end Representation
