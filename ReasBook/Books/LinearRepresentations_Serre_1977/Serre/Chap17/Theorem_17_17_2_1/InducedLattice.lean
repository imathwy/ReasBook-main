import Mathlib
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.DecompositionInductionBridge

/-!
# The induced stable lattice (part 1 of the induced-lattice/reduction bridge `hind`)

For `V : FDRep K H` and a stable `A`-lattice `L` of `V.ρ`, this file constructs the stable
`A`-lattice `inducedStableLattice V L` of the induced representation `(indOwnerK V).ρ`, namely the
`A`-span of the induced generators `indMk V g ↑l` (`g : G`, `l ∈ L`).

This is the first half of the hypothesis `hind` of
`decompositionHom_subgroupInduction_of_bridge` (step (D) of Theorem 17-17.2-1): the second half is
the reduction isomorphism `reduction (Ind L) ≅ Ind (reduction L)`.

## Key design points

* `indMk V g : V.V →ₗ[K] (indOwnerK V).V` is `Representation.IndV.mk` viewed as a `K`-linear map
  into the **opaque** induced carrier `(indOwnerK V).V`.  Because the codomain is the opaque alias
  `indOwnerK V`, the instances `Module A`/`IsScalarTower A K` on it resolve canonically (no
  abbreviation-unfolding diamond), while `indMk V g` remains a genuine `LinearMap`, so `map_sum`,
  `map_smul`, `map_smul_of_tower` all apply.
* `indOwnerK_rho_indMk` is a storm-free `rfl`-backed characterization of the induced action on the
  generators, used to avoid the `whnf` blow-up that a direct `(indOwnerK V).ρ`-defeq would trigger
  (`(indOwnerK V).ρ` is, by `rfl`, `Representation.ind H.subtype V.ρ`, but exposing that through a
  bare `show` storms; routing through this lemma keeps everything within the default heartbeat
  budget).
-/

noncomputable section

universe u

open CategoryTheory Finsupp TensorProduct
open scoped Representation

namespace Representation

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

/-- `Representation.IndV.mk` viewed as a `K`-linear map into the opaque induced carrier
`(indOwnerK V).V`.  Keeping the codomain opaque lets `Module A`/`IsScalarTower A K` resolve on it
while preserving the `LinearMap` structure. -/
def indMk {H : Subgroup G} (V : FDRep K H) (g : G) : V.V →ₗ[K] (indOwnerK V).V :=
  Representation.IndV.mk H.subtype V.ρ g

/-- Storm-free characterization of the induced action on the generators `indMk V g₂ x`.  By `rfl`,
`(indOwnerK V).ρ = Representation.ind H.subtype V.ρ`, but routing through this lemma (rather than a
bare defeq `show`) keeps the `whnf` cost bounded. -/
theorem indOwnerK_rho_indMk {H : Subgroup G} (V : FDRep K H) (g g₂ : G) (x : V.V) :
    (indOwnerK V).ρ g (indMk V g₂ x) = indMk V (g₂ * g⁻¹) x := by
  have h : (indOwnerK V).ρ g (indMk V g₂ x)
      = Representation.ind H.subtype V.ρ g (Representation.IndV.mk H.subtype V.ρ g₂ x) := rfl
  rw [h, Representation.ind_mk]; rfl

/-- The generators `indMk V g v` (`g : G`, `v : V.V`) `K`-span the whole induced carrier. -/
private theorem span_indMk_eq_top {H : Subgroup G} (V : FDRep K H) :
    Submodule.span K (Set.range (fun gv : G × V.V => indMk V gv.1 gv.2))
      = (⊤ : Submodule K (indOwnerK V).V) := by
  show Submodule.span K (Set.range (fun gv : G × V.V =>
      Representation.IndV.mk H.subtype V.ρ gv.1 gv.2))
    = (⊤ : Submodule K (Representation.IndV H.subtype V.ρ))
  have h1 : (Set.range (fun gv : G × V.V => Representation.IndV.mk H.subtype V.ρ gv.1 gv.2))
      = (Representation.Coinvariants.mk _) ''
          (Set.range (fun gv : G × V.V => single gv.1 (1:K) ⊗ₜ[K] gv.2)) := by
    rw [← Set.range_comp]; rfl
  rw [h1, Submodule.span_image]
  have htop : Submodule.span K (Set.range (fun gv : G × V.V => single gv.1 (1:K) ⊗ₜ[K] gv.2))
      = (⊤ : Submodule K (TensorProduct K (G →₀ K) V.V)) := by
    rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨m, n, rfl⟩
    rw [← m.sum_single, Finsupp.sum, TensorProduct.sum_tmul]
    refine Submodule.sum_mem _ (fun g _ => ?_)
    have hsm : (single g (m g) : G →₀ K) ⊗ₜ[K] n = (m g) • (single g (1:K) ⊗ₜ[K] n) := by
      rw [smul_tmul']; congr 1; rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsm]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(g, n), rfl⟩)
  rw [htop, Submodule.map_top, LinearMap.range_eq_top]
  exact Representation.Coinvariants.mk_surjective _

/-- **Part 1 of `hind`.**  The stable `A`-lattice of the induced representation `(indOwnerK V).ρ`
spanned by the induced generators `indMk V g ↑l` (`g : G`, `l ∈ L`).  Its underlying `A`-submodule
is `A`-finitely-generated (it is spanned by `G × (basis of L)`, both finite) and `K`-spans the whole
induced space (since `L` `K`-spans `V` and the `indMk V g` are `K`-linear). -/
def inducedStableLattice {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) :
    StableLattice A (indOwnerK V).ρ where
  toSubmodule := Submodule.span A (Set.range (fun gl : G × ↥L.toSubmodule =>
    indMk V gl.1 (gl.2 : V.V)))
  apply_mem_toSubmodule g := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨⟨g₂, l⟩, rfl⟩ := hy
        rw [Representation.restrictScalars_apply, indOwnerK_rho_indMk]
        exact Submodule.subset_span ⟨(g₂ * g⁻¹, l), rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  isLattice := by
    classical
    haveI : Submodule.IsLattice K L.toSubmodule := L.isLattice
    haveI : Fintype (Module.Free.ChooseBasisIndex A L.toSubmodule) :=
      Module.Free.ChooseBasisIndex.fintype A L.toSubmodule
    let b := Module.Free.chooseBasis A L.toSubmodule
    refine { fg := ?_, span_eq_top := ?_ }
    · -- Finite generation: replace the `G × L` generating set by the finite `G × (basis of L)`.
      have heq : Submodule.span A (Set.range (fun gl : G × ↥L.toSubmodule =>
          indMk V gl.1 (gl.2 : V.V)))
          = Submodule.span A (Set.range (fun p : G × Module.Free.ChooseBasisIndex A L.toSubmodule =>
              indMk V p.1 (b p.2 : V.V))) := by
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨⟨g, l⟩, rfl⟩
          show indMk V g (l : V.V) ∈ _
          have hl : (l : V.V) = ∑ i, b.repr l i • (b i : V.V) := by
            conv_lhs => rw [show (l : V.V) = L.toSubmodule.subtype l from rfl, ← b.sum_repr l]
            rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [map_smul]; rfl)
          rw [hl, map_sum]
          refine Submodule.sum_mem _ (fun i _ => ?_)
          rw [LinearMap.map_smul_of_tower]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(g, i), rfl⟩)
        · rw [Submodule.span_le]
          rintro _ ⟨⟨g, i⟩, rfl⟩
          exact Submodule.subset_span ⟨(g, ⟨b i, (b i).2⟩), rfl⟩
      rw [heq]; exact Submodule.fg_span (Set.finite_range _)
    · -- `K`-span is everything: the generators `K`-span (`span_indMk_eq_top`), and each generator
      -- `indMk V g v` lies in the `K`-span of `toSubmodule` since `v ∈ span K L`.
      rw [eq_top_iff, ← span_indMk_eq_top V, Submodule.span_le]
      rintro _ ⟨⟨g, v⟩, rfl⟩
      show indMk V g v ∈ _
      have hv : v ∈ Submodule.span K (↑L.toSubmodule : Set V.V) := by
        rw [Submodule.IsLattice.span_eq_top (A := K) (M := L.toSubmodule)]; trivial
      induction hv using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (Submodule.subset_span ⟨(g, ⟨y, hy⟩), rfl⟩)
      | zero => simp
      | add a c _ _ ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
      | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

@[simp] theorem inducedStableLattice_toSubmodule {H : Subgroup G} (V : FDRep K H)
    (L : StableLattice A V.ρ) :
    (inducedStableLattice V L).toSubmodule
      = Submodule.span A (Set.range (fun gl : G × ↥L.toSubmodule => indMk V gl.1 (gl.2 : V.V))) :=
  rfl

/-- **Part 1 of `hind` reduces the bridge hypothesis to the reduction isomorphism for the explicit
induced lattice.**  Given, for every `V` and every stable lattice `L`, a `G`-equivariant isomorphism
`reduction (Ind L) ≅ Ind (reduction L)` (the second, deeper half of `hind`), one obtains the full
hypothesis `hind` of `decompositionHom_subgroupInduction_of_bridge` by choosing
`Lind := inducedStableLattice V L`.  This isolates the sole remaining obligation for step (D) of
Theorem 17-17.2-1: the reduction-commutes-with-induction isomorphism for `inducedStableLattice`. -/
theorem hind_of_inducedStableLattice_reductionIso (H : Subgroup G)
    (hiso : ∀ V : FDRep K H, ∀ L : StableLattice A V.ρ,
      Nonempty (FDRep.of (inducedStableLattice V L).reductionRepresentation ≅
        FDRep.subgroupInduction (k := IsLocalRing.ResidueField A) (G := G)
          (FDRep.of L.reductionRepresentation))) :
    ∀ V : FDRep K H, ∀ L : StableLattice A V.ρ,
      ∃ Lind : StableLattice A (indOwnerK V).ρ,
        Nonempty (FDRep.of Lind.reductionRepresentation ≅
          FDRep.subgroupInduction (k := IsLocalRing.ResidueField A) (G := G)
            (FDRep.of L.reductionRepresentation)) :=
  fun V L => ⟨inducedStableLattice V L, hiso V L⟩

end Representation
