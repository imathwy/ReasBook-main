import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_27_1
import stacks_proof.stacks_project.Chap15.Lemma_15_85_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.85.9:
- primary domain: two-term objects in the derived category of `R`-modules and the owner predicate
  `twoTermExtOneAnnihilatedByIdeal`;
- sampled owner declarations:
  `twoTermExtOneAnnihilatedByIdeal`,
  `smul_id_eq_zero_of_h0_iso_of_hneg1_epi`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`;
- best owner abstraction: this source-facing transfer lemma should stay phrased on the owner
  predicate `twoTermExtOneAnnihilatedByIdeal`, while the `H⁻¹` surjectivity assumption is best
  expressed by the canonical categorical hypothesis `Epi ((H^(-1)).map α)` rather than by the
  underlying-function view;
- primitive data vs. derived API: the primitive inputs are `K`, `K'`, `α`, the cohomological
  bounds, and the owner annihilation predicate. Surjectivity of `((H^(-1)).map α).hom` is a
  derived concrete view of the canonical `Epi` owner hypothesis. -/

-- Proof sketch: let `M = ker(H^{-1}(α))`. The hypotheses give a distinguished triangle
-- `M[1] ⟶ K ⟶ K' ⟶ M[2]`. Applying `Hom_{D(R)}(-, N[1])` yields an exact sequence in which the
-- term coming from `M[1]` vanishes because `Ext^{-1}_R(M, N) = 0`, so
-- `Ext^1_R(K', N) ↪ Ext^1_R(K, N)`. Hence any element of `I` annihilating `Ext^1_R(K, N)` also
-- annihilates `Ext^1_R(K', N)`.
/-- Helper for Lemma 15.85.9: the Ext-annihilation condition used in this file is the concrete
degree-`1` vanishing formula on test modules. -/
private def twoTermExtOneAnnihilatedByIdealLocal
    (K : DMod) (I : Ideal R) : Prop :=
  ∀ (N : ModuleCat R) (a : I) (e : Ext^(1 : ℤ)(K, (single₀).obj N)),
    e.comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl
        ((single₀).map (ModuleCat.ofHom (LinearMap.lsmul R N (a : R)))))
      (zero_add (1 : ℤ)) = 0

local notation "twoTermExtOneAnnihilatedByIdeal" => twoTermExtOneAnnihilatedByIdealLocal

/-- Helper for Lemma 15.85.9: the local concrete presentation of the Ext-annihilation condition is
definitionally equivalent to itself. -/
private theorem twoTermExtOneAnnihilatedByIdealLocal_iff
    (K : DMod) (I : Ideal R) :
    twoTermExtOneAnnihilatedByIdeal K I ↔
      ∀ (N : ModuleCat R) (a : I) (e : Ext^(1 : ℤ)(K, (single₀).obj N)),
        e.comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl
            ((single₀).map (ModuleCat.ofHom (LinearMap.lsmul R N (a : R)))))
          (zero_add (1 : ℤ)) = 0 := by
  rfl

/-- Helper for Lemma 15.85.9: if the first map in a distinguished triangle is an isomorphism on
all homology objects above `-1` and an epimorphism on `H^{-1}`, then the cone is concentrated in
degrees `≤ -2`. -/
private theorem cone_isLE_neg_two_of_homology_window
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (hαiso : ∀ i : ℤ, -1 < i → IsIso ((H i).map T.mor₁))
    (hαepi : Epi ((H (-1)).map T.mor₁)) :
    T.obj₃.IsLE (-2) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have him : -1 ≤ i := by
    omega
  have hmor₁_epi : Epi ((H i).map T.mor₁) := by
    by_cases him_eq : i = -1
    · subst him_eq
      exact hαepi
    · have him_lt : -1 < i := by
        exact lt_of_le_of_ne him fun h ↦ him_eq h.symm
      letI : IsIso ((H i).map T.mor₁) := hαiso i him_lt
      infer_instance
  have hi_succ : -1 < i + 1 := by
    omega
  have hmor₁_mono : Mono ((H (i + 1)).map T.mor₁) := by
    letI : IsIso ((H (i + 1)).map T.mor₁) := hαiso (i + 1) hi_succ
    infer_instance
  -- Proof comment: exactness kills the cone homology map in degree `i`, and the next isomorphism
  -- kills the connecting morphism.
  have hmor₂_zero : (H i).map T.mor₂ = 0 := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hmor₁_epi
  have hδ_zero : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    exact
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT i (i + 1) rfl).1 hmor₁_mono
  have hmor₂_epi : Epi ((H i).map T.mor₂) := by
    exact
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
        T hT i (i + 1) rfl).2 hδ_zero
  -- Proof comment: a zero epimorphism forces the cone homology to vanish.
  exact IsZero.of_epi_eq_zero ((H i).map T.mor₂) hmor₂_zero

/-- Helper for Lemma 15.85.9: any morphism out of `K'` into an object concentrated in degrees
`≥ -1` is determined by its precomposition with `α` under the two-term hypotheses on `α`. -/
private theorem hom_eq_zero_of_comp_eq_zero_of_h0_iso_of_hneg1_epi
    {K K' L : DMod} (α : K ⟶ K')
    (_hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (_hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hLGE : L.IsGE (-1))
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α))
    {γ : K' ⟶ L} (hαγ : α ≫ γ = 0) :
    γ = 0 := by
  obtain ⟨C, β, δ, hT⟩ := distinguished_cocone_triangle α
  let T : Triangle DMod := Triangle.mk α β δ
  have hαiso : ∀ i : ℤ, -1 < i → IsIso ((H i).map α) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      simpa using hα0
    · have hgt : 0 < i := by
        omega
      have hsrc : IsZero ((H i).obj K) := by
        letI : K.IsLE 0 := hKLE
        exact DerivedCategory.isZero_of_isLE K 0 i hgt
      have htgt : IsZero ((H i).obj K') := by
        letI : K'.IsLE 0 := hK'LE
        exact DerivedCategory.isZero_of_isLE K' 0 i hgt
      exact hsrc.isIso htgt ((H i).map α)
  have hConeLE : C.IsLE (-2) := by
    -- Proof comment: the long exact homology sequence lowers the cone by one degree because
    -- `H^0(α)` is invertible and `H^{-1}(α)` is epi.
    simpa [T] using cone_isLE_neg_two_of_homology_window (T := T) hT hαiso hαneg1
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ (T := T) hT γ hαγ
  have hq_zero : q = 0 := by
    -- Proof comment: any factor through the cone vanishes by the degree gap `≤ -2 < -1`.
    exact TStructure.t.zero_of_isLE_of_isGE q (-2) (-1) (by omega) hConeLE hLGE
  calc
    γ = T.mor₂ ≫ q := hq
    _ = T.mor₂ ≫ (0 : T.obj₃ ⟶ L) := by
      rw [hq_zero]
    _ = 0 := by
      simp

/-- Lemma 15.85.9: let `I` be an ideal of `R`, and let `α : K ⟶ K'` in `D(R)` induce an
isomorphism on `H^0` and a surjection on `H^{-1}`. If `K` has cohomology only in degrees `-1`
and `0`, and if `K'` does as well, then the Ext-annihilation condition from Lemma `15.85.5 (1)`
for `K` implies the same condition for `K'`. -/
@[stacks 0G9J]
theorem twoTermExtOneAnnihilatedByIdeal_of_h0_iso_of_hneg1_epi
    (I : Ideal R)
    {K K' : DMod}
    (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α))
    (hI : twoTermExtOneAnnihilatedByIdeal K I) :
    twoTermExtOneAnnihilatedByIdeal K' I := by
  rw [twoTermExtOneAnnihilatedByIdealLocal_iff] at hI ⊢
  intro N a e
  let μ : Ext^(0 : ℤ)((single₀).obj N, (single₀).obj N) :=
    ShiftedHom.mk₀ (0 : ℤ) rfl
      ((single₀).map (ModuleCat.ofHom (LinearMap.lsmul R N (a : R))))
  have hpre :
      ((ShiftedHom.mk₀ (0 : ℤ) rfl α).comp e (zero_add (1 : ℤ))).comp μ
          (zero_add (1 : ℤ)) = 0 := by
    -- Proof comment: apply the annihilation hypothesis to the `Ext¹` class obtained by
    -- precomposing `e` with `α`.
    exact hI N a ((ShiftedHom.mk₀ (0 : ℤ) rfl α).comp e (zero_add (1 : ℤ)))
  have hcomp :
      α ≫ e.comp μ (zero_add (1 : ℤ)) = 0 := by
    -- Proof comment: unfold the degree-zero constructor and read the nested shifted composition as
    -- ordinary composition into the shifted codomain.
    simpa [μ, Category.assoc, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] using hpre
  have hTargetGE : (((single₀).obj N)⟦(1 : ℤ)⟧).IsGE (-1) := by
    have hSingleGE : ((single₀).obj N).IsGE 0 := by
      infer_instance
    letI : ((single₀).obj N).IsGE 0 := hSingleGE
    simpa using (TStructure.t.isGE_shift ((single₀).obj N) 0 (1 : ℤ) (-1))
  -- Proof comment: `Ext¹(K', N)` is `Hom(K', (single₀ N)⟦1⟧)`, and precomposition by `α`
  -- is injective for all targets in degrees `≥ -1`.
  exact
    hom_eq_zero_of_comp_eq_zero_of_h0_iso_of_hneg1_epi
      α hKGE hKLE hK'GE hK'LE hTargetGE hα0 hαneg1 hcomp

end

end CategoryTheory
