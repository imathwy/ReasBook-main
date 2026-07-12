import Mathlib.Algebra.DirectSum.Module
import LinearRepresentations_Serre_1977.Chap04.Proposition_4_37

noncomputable section

open scoped MonoidAlgebra Representation

-- Semantic recall: `lean_leansearch` surfaced `DirectSum.Decomposition.isInternal` and
-- `Representation.directSum`; local Chapter 4 precedent packages decomposition statements by
-- `DirectSum.IsInternal`, so this item records the basis-indexed decomposition of the `π`
-- isotypic component using the generated subrepresentations `W(x₁)`.

universe u v w y z

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]
variable {Hπ : Type w} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ]
  [FiniteDimensional ℂ Hπ]
variable {ι : Type y} [Fintype ι] [One ι]
variable {κ : Type z}
local instance instDecidableEqProposition_4_38Index : DecidableEq κ := Classical.decEq κ

/-- Companion bridge: for `x₁ ∈ V_{i,1}`, the generated subrepresentation `W(x₁)` lies in the
canonical `π`-isotypic subrepresentation of `ρ`. -/
theorem matrixCoefficientProjectionGeneratedSubrepresentation_le_piIsotypicSubrepresentation
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (x₁ : V[ρ, π, b; (1 : ι)]) :
    matrixCoefficientProjectionGeneratedSubrepresentation
        ρ π b (1 : ι) x₁.1 x₁.2 ≤
      ρ.isotypicSubrepresentation π := by
  intro v hv
  have hv' : v ∈ matrixCoefficientProjectionGeneratedSubspace ρ π b (1 : ι) x₁.1 := by
    change v ∈
      (matrixCoefficientProjectionGeneratedSubrepresentation
        ρ π b (1 : ι) x₁.1 x₁.2).toSubmodule at hv
    simpa [matrixCoefficientProjectionGeneratedSubrepresentation_toSubmodule_eq
      ρ π b (1 : ι) x₁.1 x₁.2] using hv
  change v ∈ ρ.moduleIsotypicComponent π
  exact
    matrixCoefficientProjectionGeneratedSubspace_le_piIsotypicComponent
      ρ π b x₁.1 x₁.2 hv'

/-- The basis-indexed family `k ↦ W(x₁^(k))` attached to a basis of `V_{i,1}`. -/
def matrixCoefficientProjectionGeneratedSubrepresentationFamily
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (c : Module.Basis κ ℂ V[ρ, π, b; (1 : ι)]) :
    κ → Subrepresentation ρ :=
  fun k ↦
    matrixCoefficientProjectionGeneratedSubrepresentation
      ρ π b (1 : ι) (c k).1 (c k).2

/-- The family `k ↦ W(x₁^(k))` viewed inside the canonical `π`-isotypic subrepresentation
`V_i`. -/
def matrixCoefficientProjectionGeneratedSubrepresentationFamilyInPiIsotypicComponent
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (c : Module.Basis κ ℂ V[ρ, π, b; (1 : ι)]) :
    κ → Subrepresentation (ρ.isotypicSubrepresentation π).toRepresentation :=
  fun k ↦
    { toSubmodule :=
        (matrixCoefficientProjectionGeneratedSubrepresentationFamily ρ π b c k).toSubmodule.comap
          (ρ.isotypicSubrepresentation π).toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro g v hv
        change ρ g v.1 ∈
          (matrixCoefficientProjectionGeneratedSubrepresentationFamily ρ π b c k).toSubmodule
        exact
          Subrepresentation.apply_mem_toSubmodule
            (matrixCoefficientProjectionGeneratedSubrepresentationFamily ρ π b c k) g hv }

/-- Each basis-generated subrepresentation `W(x₁^(k))` lies in the canonical `π`-isotypic
subrepresentation. -/
theorem matrixCoefficientProjectionGeneratedSubrepresentationFamily_le_piIsotypicSubrepresentation
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (c : Module.Basis κ ℂ V[ρ, π, b; (1 : ι)])
    (k : κ) :
    matrixCoefficientProjectionGeneratedSubrepresentationFamily ρ π b c k ≤
      ρ.isotypicSubrepresentation π :=
  matrixCoefficientProjectionGeneratedSubrepresentation_le_piIsotypicSubrepresentation
    ρ π b (c k)

/-- Helper for Proposition 4-38: the `k`-th coordinate image under the direct-sum equivalence
from Proposition 4-34 is exactly the basis-generated subrepresentation `W(c k)` inside the
canonical `π`-isotypic component. -/
private theorem coordinateRangeInPiIsotypic_eq_generatedFamily
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (c : Module.Basis κ ℂ V[ρ, π, b; (1 : ι)])
    (e : DirectSum κ (fun _ : κ ↦ Hπ) ≃ₗ[ℂ] ↥(ρ.isotypicSubrepresentation π).toSubmodule)
    (he : ∀ k : κ, ∀ v : Hπ,
      (ρ.isotypicSubrepresentation π).toSubmodule.subtype
        (e (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) =
          ∑ α, (b.repr v α) • p[ρ, π, b; α, (1 : ι)] (c k))
    (k : κ) :
    LinearMap.range (e.toLinearMap.comp (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k)) =
      (matrixCoefficientProjectionGeneratedSubrepresentationFamilyInPiIsotypicComponent
        ρ π b c k).toSubmodule := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    -- Rewrite the comap membership as ambient membership in `W(c k)`.
    change (ρ.isotypicSubrepresentation π).toSubmodule.subtype
        (e (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) ∈
      (matrixCoefficientProjectionGeneratedSubrepresentationFamily ρ π b c k).toSubmodule
    rw [he k v]
    -- The explicit generator formula is the value of the canonical intertwiner, hence it lies in
    -- the range that defines `W(c k)`.
    change matrixCoefficientProjectionIntertwiningMap
        ρ π b (1 : ι) (c k) (c k).property v ∈
      (matrixCoefficientProjectionGeneratedSubrepresentationFamily ρ π b c k).toSubmodule
    rw [matrixCoefficientProjectionGeneratedSubrepresentationFamily,
      matrixCoefficientProjectionGeneratedSubrepresentation]
    exact LinearMap.mem_range_self
      (matrixCoefficientProjectionIntertwiningMap ρ π b (1 : ι) (c k) (c k).property).toLinearMap v
  · intro hy
    -- Move the subtype-comap membership back to the ambient generated subrepresentation.
    change y.1 ∈
      (matrixCoefficientProjectionGeneratedSubrepresentationFamily ρ π b c k).toSubmodule at hy
    rcases (show y.1 ∈
        LinearMap.range
          (matrixCoefficientProjectionIntertwiningMap
            ρ π b (1 : ι) (c k) (c k).property).toLinearMap from by
          simpa [matrixCoefficientProjectionGeneratedSubrepresentationFamily,
            matrixCoefficientProjectionGeneratedSubrepresentation] using hy) with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    apply Subtype.ext
    -- Compare both underlying vectors through the common explicit intertwiner formula.
    calc
      (ρ.isotypicSubrepresentation π).toSubmodule.subtype
          (e (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v))
        = ∑ α, (b.repr v α) • p[ρ, π, b; α, (1 : ι)] (c k) := he k v
      _ = matrixCoefficientProjectionIntertwiningMap
            ρ π b (1 : ι) (c k) (c k).property v := by
            rw [matrixCoefficientProjectionIntertwiningMap_apply]
      _ = y.1 := hv

omit [FiniteDimensional ℂ Hπ] in
/-- Helper for Proposition 4-38: a linear equivalence from a direct sum transports the standard
coordinate summands to an internal family of coordinate ranges. -/
private theorem coordinateRangeIsInternalOfLinearEquiv
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (e : DirectSum κ (fun _ : κ ↦ Hπ) ≃ₗ[ℂ] M) :
    DirectSum.IsInternal
      (fun k : κ ↦
        LinearMap.range
          (e.toLinearMap.comp (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k))) := by
  let source : κ → Submodule ℂ (DirectSum κ (fun _ : κ ↦ Hπ)) :=
    fun k ↦ LinearMap.range (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k)
  have hSourceIndep : iSupIndep source := by
    -- Isolate a chosen coordinate by applying the corresponding projection map.
    rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
    intro s v hv hsum i hi
    rcases hv i hi with ⟨x, hx⟩
    have hcomponent :
        DirectSum.component ℂ κ (fun _ : κ ↦ Hπ) i (∑ j ∈ s, v j) = 0 := by
      simpa using congrArg (DirectSum.component ℂ κ (fun _ : κ ↦ Hπ) i) hsum
    have hx_zero : x = 0 := by
      calc
        x = DirectSum.component ℂ κ (fun _ : κ ↦ Hπ) i (v i) := by
              simpa [hx] using
                (DirectSum.component.lof_self (R := ℂ) (ι := κ) (M := fun _ : κ ↦ Hπ) i x).symm
        _ = ∑ j ∈ s, DirectSum.component ℂ κ (fun _ : κ ↦ Hπ) i (v j) := by
              symm
              rw [Finset.sum_eq_single_of_mem i hi]
              · intro j hj hji
                rcases hv j hj with ⟨xj, hxj⟩
                calc
                  DirectSum.component ℂ κ (fun _ : κ ↦ Hπ) i (v j)
                    = DirectSum.component ℂ κ (fun _ : κ ↦ Hπ) i
                        (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) j xj) := by
                          rw [← hxj]
                  _ = 0 := by
                        simp [DirectSum.component.of, hji]
        _ = DirectSum.component ℂ κ (fun _ : κ ↦ Hπ) i (∑ j ∈ s, v j) := by
              symm
              simp [map_sum]
        _ = 0 := hcomponent
    -- Once the chosen coordinate vanishes, the entire supported vector vanishes.
    simpa [hx_zero] using hx.symm
  have hSourceTop : iSup source = ⊤ := by
    -- The direct sum is generated by its standard coordinate inclusions.
    simpa [source, DirectSum.lof] using
      (DFinsupp.iSup_range_lsingle (R := ℂ) (M := fun _ : κ ↦ Hπ))
  have hIndep :
      iSupIndep
        (fun k : κ ↦
          LinearMap.range
            (e.toLinearMap.comp (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k))) := by
    -- Injective linear maps preserve independence of the source coordinate family.
    simpa [source, LinearMap.range_comp] using
      (LinearMap.iSupIndep_map e.toLinearMap e.injective hSourceIndep)
  have hTop :
      iSup (fun k : κ ↦ LinearMap.range
        (e.toLinearMap.comp (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k))) = ⊤ := by
    -- Surjectivity of `e` transports the spanning property of the source direct sum.
    calc
      iSup (fun k : κ ↦ LinearMap.range
          (e.toLinearMap.comp (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k)))
          = iSup (fun k : κ ↦ (source k).map e.toLinearMap) := by
              congr with k
              rw [LinearMap.range_comp]
      _ = (iSup source).map e.toLinearMap := by
            rw [Submodule.map_iSup]
      _ = ⊤ := by
            rw [hSourceTop, Submodule.map_top]
            exact LinearMap.range_eq_top.2 e.surjective
  -- Package the transported independence and spanning statements as internality.
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndep hTop

/-- Proposition 4-38 (1): if `x₁^(k)` is a basis of `V_{i,1}`, then the `π`-isotypic component
`V_i` is the internal direct sum of the generated subrepresentations `W(x₁^(k))`, viewed inside
the canonical owner `σ` of `V_i`. -/
theorem isInternal_piIsotypicComponent_of_matrixCoefficientProjectionSubspace_basis
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (c : Module.Basis κ ℂ V[ρ, π, b; (1 : ι)]) :
    DirectSum.IsInternal
      (fun k ↦
        (matrixCoefficientProjectionGeneratedSubrepresentationFamilyInPiIsotypicComponent
          ρ π b c k).toSubmodule) := by
  classical
  rcases exists_piIsotypicComponent_equiv_directSum_of_matrixCoefficientBasis
      ρ π b (1 : ι) c with ⟨e, he⟩
  let eLin : DirectSum κ (fun _ : κ ↦ Hπ) ≃ₗ[ℂ] ↥(ρ.isotypicSubrepresentation π).toSubmodule := e
  have heLin : ∀ k : κ, ∀ v : Hπ,
      (ρ.isotypicSubrepresentation π).toSubmodule.subtype
        (eLin (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) =
          ∑ α, (b.repr v α) • p[ρ, π, b; α, (1 : ι)] (c k) := by
    intro k v
    simpa [eLin] using he k v
  have hfamily :
      (fun k : κ ↦ LinearMap.range
          (eLin.toLinearMap.comp (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k))) =
        (fun k ↦
          (matrixCoefficientProjectionGeneratedSubrepresentationFamilyInPiIsotypicComponent
            ρ π b c k).toSubmodule) := by
    -- Proposition 4-34 identifies each coordinate image with the corresponding `W(c k)`.
    funext k
    exact coordinateRangeInPiIsotypic_eq_generatedFamily ρ π b c eLin heLin k
  -- Transport the standard coordinate decomposition across the direct-sum equivalence.
  rw [← hfamily]
  exact coordinateRangeIsInternalOfLinearEquiv eLin

/-- Proposition 4-38 (2): for each basis vector `x₁^(k) ∈ V_{i,1}`, the generated
subrepresentation `W(x₁^(k))` is isomorphic to `π`. -/
theorem matrixCoefficientProjectionGeneratedSubrepresentation_nonempty_equiv_of_basis
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (c : Module.Basis κ ℂ V[ρ, π, b; (1 : ι)])
    (k : κ) :
    Nonempty
      (π.Equiv
        (matrixCoefficientProjectionGeneratedSubrepresentationFamily ρ π b c k).toRepresentation) :=
    by
  have hk_ne : ((c k : V[ρ, π, b; (1 : ι)]) : V) ≠ 0 := by
    intro hk
    apply Module.Basis.ne_zero c k
    ext
    exact hk
  simpa [matrixCoefficientProjectionGeneratedSubrepresentationFamily] using
    matrixCoefficientProjectionGeneratedSubrepresentation_nonempty_equiv
      ρ π b ((c k : V[ρ, π, b; (1 : ι)]) : V) (c k).2 hk_ne

end

end Representation
