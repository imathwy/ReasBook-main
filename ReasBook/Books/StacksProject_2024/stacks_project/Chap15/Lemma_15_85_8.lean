import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_7
import StacksProject_2024.stacks_project.Chap13.Lemma_13_27_3
import StacksProject_2024.stacks_project.Chap13.Remark_13_4_4

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

open DerivedCategory.TStructure
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

section

variable {𝒜 : Type u} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

/-
Domain-style sampling for Lemma 15.85.8:
- primary domain: the canonical `t`-structure on derived categories of abelian categories, and
  its specialization to scalar endomorphisms of two-term derived `R`-modules;
- sampled owner declarations in this domain:
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.Epi`;
- best owner abstraction: the cohomological amplitude hypotheses belong to the canonical
  `t`-structure owners `K.IsGE (-1)`, `K.IsLE 0`, `K'.IsGE (-1)`, and `K'.IsLE 0`, while the map
  hypotheses are the canonical categorical conditions `IsIso ((H^0).map α)` and
  `Epi ((H^(-1)).map α)`, whose intrinsic categorical conclusion is `Epi α`;
- primitive data vs. derived API: for the owner theorem below, the primitive inputs are `K`, `K'`,
  `α`, and the cohomological hypotheses. In the module specialization, the canonical bridge is the
  purely categorical `cancel_epi` argument after obtaining `Epi α`; the hypotheses on `H^0(α)`
  and `H^{-1}(α)` are source-facing bridge data used only to supply `Epi α`. The proof-route data
  involving a kernel object `M`, a distinguished triangle, and the vanishing
  `Hom(M⟦2⟧, K') = 0` are internal bridge data and should not become public wrapper data.

Source/core/bridge triage:
- `source-facing`: the scalar-annihilation transfer theorem in `D(R)` below;
- `core/canonical`: the owner predicates `IsGE` / `IsLE`, the homology-map hypotheses on `α`,
  and the resulting categorical conclusion `Epi α` in `D(𝒜)`;
- `bridge/view`: the distinguished-triangle argument and the Chapter 13 vanishing/factorization
  lemmas used in the proof sketch.
-/

-- Proof sketch: let `M` be the kernel of `H⁻¹(α)`. The hypotheses on the two-term cohomology of
-- `K` and `K'`, together with `H⁰(α)` being an isomorphism and `H⁻¹(α)` being surjective, place
-- `α` in a distinguished triangle `M⟦1⟧ ⟶ K ⟶ K' ⟶ M⟦2⟧`. If `f • 𝟙 K = 0`, then
-- `α ≫ (f • 𝟙 K') = 0`, so `f • 𝟙 K'` factors through a morphism `M⟦2⟧ ⟶ K'`. Lemma `13.27.3`
-- gives `Hom(M⟦2⟧, K') = 0` because `M⟦2⟧` is concentrated in degree `-2` and `K'` has
-- cohomology only in degrees `-1` and `0`.
/-- Helper for Lemma 15.85.8: above degree `-1`, the homology map of a two-term morphism is
automatically an isomorphism once the degree-`0` homology map is an isomorphism. -/
private theorem homology_map_isIso_above_neg_one_of_two_term
    {K K' : D(𝒜)} (α : K ⟶ K')
    (hKLE : K.IsLE 0) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H 0).map α)) :
    ∀ i : ℤ, -1 < i → IsIso ((H i).map α) := by
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
    -- Proof comment: in positive degrees both homology objects vanish, so the induced map is the
    -- unique morphism between zero objects and hence an isomorphism.
    exact hsrc.isIso htgt ((H i).map α)

/-- Helper for Lemma 15.85.8: if the first map in a distinguished triangle is an isomorphism on
all homology objects above `-1` and an epimorphism on `H^{-1}`, then the cone is concentrated in
degrees `≤ -2`. -/
private theorem cone_isLE_neg_two_of_homology_window
    (T : Triangle D(𝒜)) (hT : T ∈ distTriang D(𝒜))
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
  -- Proof comment: exactness first kills the cone homology map in degree `i`, and then the next
  -- isomorphism kills the connecting morphism.
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
  -- Proof comment: a zero epimorphism has zero codomain, so the cone homology vanishes in
  -- degree `i`.
  exact IsZero.of_epi_eq_zero ((H i).map T.mor₂) hmor₂_zero

/-- Helper for Lemma 15.85.8: maps from an object concentrated in degrees `≤ -2` to one
concentrated in degrees `≥ -1` form a subsingleton. -/
private theorem subsingleton_hom_of_isLE_neg_two_of_isGE_neg_one
    {C K' : D(𝒜)}
    (hC : C.IsLE (-2)) (hK'GE : K'.IsGE (-1)) :
    Subsingleton (C ⟶ K') := by
  have hn : (0 : ℤ) < (-1 : ℤ) - (-2 : ℤ) := by
    omega
  let e0 : K'⟦(0 : ℤ)⟧ ≅ K' := (shiftFunctorZero (D(𝒜)) ℤ).app K'
  have hsub_shift : Subsingleton (C ⟶ K'⟦(0 : ℤ)⟧) := by
    exact shiftedHom_subsingleton_of_lt_sub C K' (-2) (-1) 0 hC hK'GE hn
  -- Proof comment: this is the Chapter 13 orthogonality statement in degree `0`.
  refine ⟨fun f g ↦ ?_⟩
  have hfg_shift : f ≫ e0.inv = g ≫ e0.inv := by
    exact Subsingleton.elim _ _
  exact (cancel_mono e0.inv).1 hfg_shift

/-- Helper for Lemma 15.85.8: any endomorphism of `K'` that vanishes after precomposition with
`α` is zero. -/
theorem endomorphism_zero_of_comp_eq_zero_of_h0_iso_of_hneg1_epi
    {K K' : D(𝒜)} (α : K ⟶ K')
    (_hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α))
    {γ : K' ⟶ K'} (hαγ : α ≫ γ = 0) :
    γ = 0 := by
  obtain ⟨C, β, δ, hT⟩ := distinguished_cocone_triangle α
  let T : Triangle D(𝒜) := Triangle.mk α β δ
  have hαiso : ∀ i : ℤ, -1 < i → IsIso ((H i).map α) := by
    -- Proof comment: outside degree `-1`, the two-term hypothesis forces all positive homology
    -- maps to be isomorphisms once degree `0` is.
    exact homology_map_isIso_above_neg_one_of_two_term α hKLE hK'LE hα0
  have hConeLE : C.IsLE (-2) := by
    -- Proof comment: the long exact homology sequence lowers the cone by one degree because
    -- `H^0(α)` is invertible and `H^{-1}(α)` is epi.
    simpa [T] using cone_isLE_neg_two_of_homology_window (T := T) hT hαiso hαneg1
  have hsub : Subsingleton (C ⟶ K') := by
    -- Proof comment: the cone sits in degrees `≤ -2`, so maps from it to the two-term object
    -- `K'` vanish by Chapter 13 orthogonality.
    exact subsingleton_hom_of_isLE_neg_two_of_isGE_neg_one hConeLE hK'GE
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ (T := T) hT γ hαγ
  have hsubT : Subsingleton (T.obj₃ ⟶ K') := by
    simpa [T] using hsub
  have hq_zero : q = 0 := by
    letI : Subsingleton (T.obj₃ ⟶ K') := hsubT
    exact Subsingleton.elim _ _
  calc
    γ = T.mor₂ ≫ q := hq
    _ = T.mor₂ ≫ (0 : T.obj₃ ⟶ K') := by
      rw [hq_zero]
    _ = 0 := by
      simp

end

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "DModR" => DerivedCategory ModR

/-- Lemma 15.85.8: let `α : K ⟶ K'` be a morphism in `D(R)` between objects with cohomology only
in degrees `-1` and `0`. If `H⁰(α)` is an isomorphism and `H⁻¹(α)` is an epimorphism, then any
scalar `f : R` acting by zero on `K` also acts by zero on `K'`. -/
theorem smul_id_eq_zero_of_h0_iso_of_hneg1_epi
    {K K' : DModR} (α : K ⟶ K') (f : R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α))
    (hf : f • 𝟙 K = 0) :
    f • 𝟙 K' = 0 := by
  have hcomp_zero : α ≫ (f • 𝟙 K') = 0 := by
    -- Proof comment: scalar multiplication commutes with composition, and the source action
    -- already vanishes by hypothesis.
    calc
      α ≫ (f • 𝟙 K') = f • α := by simp
      _ = (f • 𝟙 K) ≫ α := by simp
      _ = 0 := by simpa [hf]
  exact
    endomorphism_zero_of_comp_eq_zero_of_h0_iso_of_hneg1_epi
      α hKGE hKLE hK'GE hK'LE hα0 hαneg1 hcomp_zero

end

end CategoryTheory
