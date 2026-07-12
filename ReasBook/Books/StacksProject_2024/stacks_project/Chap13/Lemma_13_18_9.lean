import Mathlib
import StacksProject_2024.Chap13.Definition_13_18_1
import StacksProject_2024.Chap13.Lemma_13_18_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling:
- primary domain: short exact sequences of bounded-below cochain complexes and compatible
  bounded-below injective resolutions;
- sampled owner declarations:
  `CategoryTheory.ShortComplex.Hom`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CochainComplex.PlusWithTermsIn.ι`,
  `CochainComplex.plus`,
  `CochainComplex.InjectivePlus`,
  `CochainComplex.InjectiveResolution`;
- best owner abstraction: the resolving row should be owned by
  `ShortComplex (InjectivePlus 𝒜)`, its comparison with the given short exact sequence by a
  single `ShortComplex.Hom`, and short exactness by `ShortComplex.ShortExact`;
- primitive data here: the short exact resolving row in `InjectivePlus 𝒜`, the morphism from `S`
  to its underlying short complex, and the quasi-isomorphism witnesses on the three vertical
  components;
- derived API here: the source-facing existence theorems below, with any columnwise
  `InjectiveResolution` view recovered directly from the canonical row and comparison morphism.

Source/core/bridge triage:
- `source-facing`: the injective-resolution diagram data above a bounded-below short exact
  sequence, together with its existence theorems;
- `core/canonical`: `ShortComplex (InjectivePlus 𝒜)`, `ShortComplex.Hom`,
  `ShortComplex.ShortExact`, `CochainComplex.InjectiveResolution`, and the generic
  extension-closure interface `ObjectProperty.prop_X₂_of_shortExact`;
- `bridge/view`: the `strictlyGE_zero` existence specializations below.
-/

local notation "injPlusι" => PlusWithTermsIn.ι (isInjective 𝒜)

section

variable [EnoughInjectives 𝒜]

/-- Helper for Lemma 13.18.9: the comparison map of an injective resolution is a quasi-isomorphism
by definition. -/
private theorem injectiveResolution_map_quasiIso {K : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) : QuasiIso I.ι := by
  -- This is exactly the bundled quasi-isomorphism field of `InjectiveResolution`.
  infer_instance

/-- Helper for Lemma 13.18.9: in a morphism between short exact rows of cochain complexes,
quasi-isomorphisms on the outer vertical maps force a quasi-isomorphism on the middle map. -/
theorem quasiIso_tau₂_of_shortExact
    {S T : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (hτ₁ : QuasiIso φ.τ₁) (hτ₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  -- Route correction: compare the derived triangles of the two short exact rows and apply the
  -- triangulated two-out-of-three lemma to the first and third components.
  let φQ := triangleOfSES.map hS hT φ
  have hSQ : triangleOfSES hS ∈ distTriang (DerivedCategory 𝒜) := by
    simpa using triangleOfSES_distinguished hS
  have hTQ : triangleOfSES hT ∈ distTriang (DerivedCategory 𝒜) := by
    simpa using triangleOfSES_distinguished hT
  have hQ₁ : IsIso φQ.hom₁ := by
    simpa [φQ] using ((isIso_Q_map_iff_quasiIso 𝒜 φ.τ₁).2 hτ₁)
  have hQ₃ : IsIso φQ.hom₃ := by
    simpa [φQ] using ((isIso_Q_map_iff_quasiIso 𝒜 φ.τ₃).2 hτ₃)
  have hQ₂ : IsIso φQ.hom₂ := by
    simpa [φQ] using (isIso₂_of_isIso₁₃ φQ hSQ hTQ hQ₁ hQ₃ : IsIso φQ.hom₂)
  exact (isIso_Q_map_iff_quasiIso 𝒜 φ.τ₂).1 (by simpa [φQ] using hQ₂)

/-- Helper for Lemma 13.18.9: bounded-below cochain complexes are closed under short exact
extensions. -/
private theorem plus_of_shortExact
    {S : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃) :
    CochainComplex.plus 𝒜 S.X₂ := by
  obtain ⟨a, hA'⟩ := (CochainComplex.plus_iff 𝒜 S.X₁).1 hA
  obtain ⟨c, hC'⟩ := (CochainComplex.plus_iff 𝒜 S.X₃).1 hC
  refine (CochainComplex.plus_iff 𝒜 S.X₂).2 ⟨min a c, ?_⟩
  -- Below the common lower bound, both outer terms vanish degreewise.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  let Si : ShortComplex 𝒜 := S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
  let hSi : Si.ShortExact := by
    simpa using hS.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
  have h₁ : CategoryTheory.Limits.IsZero (S.X₁.X i) := by
    let _ : S.X₁.IsStrictlyGE a := hA'
    exact S.X₁.isZero_of_isStrictlyGE a i (lt_of_lt_of_le hi (min_le_left _ _))
  have h₃ : CategoryTheory.Limits.IsZero (S.X₃.X i) := by
    let _ : S.X₃.IsStrictlyGE c := hC'
    exact S.X₃.isZero_of_isStrictlyGE c i (lt_of_lt_of_le hi (min_le_right _ _))
  -- Exactness with zero left term makes the right map monic, and a monomorphism into a zero
  -- object forces the middle term itself to be zero.
  have hmono : Mono Si.g := by
    exact (Si.exact_iff_mono (h₁.eq_of_src _ _)).1 hSi.exact
  letI : Mono Si.g := hmono
  simpa [Si] using CategoryTheory.Limits.IsZero.of_mono Si.g h₃

/-- Helper for Lemma 13.18.9: a short exact row of cochain complexes splits degreewise once its
left term is injective in every degree. -/
private theorem degreewise_splitting_of_shortExact_left_injective
    {T : ShortComplex (CochainComplex 𝒜 ℤ)} (hT : T.ShortExact)
    (hInj : ∀ n : ℤ, Injective (T.X₁.X n)) :
    ∀ n : ℤ, (T.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting := by
  -- Evaluate the short exact row in one degree and invoke the injective splitting criterion there.
  intro n
  let hTn : (T.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).ShortExact := by
    simpa using hT.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
  let _ : Injective ((T.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).X₁) := by
    simpa using hInj n
  exact hTn.splittingOfInjective

/-- Helper for Lemma 13.18.9: if the left term of a short exact row is a chosen injective
resolution complex, then every degree of the row is split exact. -/
private theorem degreewise_splitting_of_shortExact_left_resolution
    {T : ShortComplex (CochainComplex 𝒜 ℤ)} (hT : T.ShortExact)
    (I : InjectiveResolution T.X₁) :
    ∀ n : ℤ, (T.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting := by
  -- The previous degreewise criterion applies because the resolution complex is injective termwise.
  exact degreewise_splitting_of_shortExact_left_injective hT (fun n ↦ by simpa using I.injective n)

/-- Helper for Lemma 13.18.9: pushing out the row along a prescribed left injective resolution
reduces the horseshoe proof to the degreewise split case while preserving the middle
quasi-isomorphism. -/
private theorem pushout_row_shortExact_degreewiseSplit
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) :
    ∃ (T : ShortComplex (CochainComplex 𝒜 ℤ)) (ψ : S ⟶ T)
      (σ : ∀ n : ℤ, (T.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting),
        ψ.τ₁ = I.ι ∧ ψ.τ₃ = 𝟙 S.X₃ ∧ T.ShortExact ∧ QuasiIso ψ.τ₂ := by
  -- TODO: build the pushout row along `I.ι`, identify its right term with `S.X₃`, and split each
  -- evaluated short exact row using injectivity of the degreewise terms of `I`.
  sorry

-- Proof sketch: run the construction of `exists_injectiveResolutionDiagram_of_shortExact` starting
-- from the prescribed injective resolution of the left complex, then perform the pushout
-- reduction and the lifted-connecting-morphism construction relative to that fixed choice.
/-- Given a chosen injective resolution of the left complex, the diagram can be built with that
resolution as its left column, provided the outer terms of the short exact row are bounded below.
The middle term is then bounded below by short exactness. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃)
    (I : InjectiveResolution S.X₁) :
    ∃ (J K : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧ QuasiIso φ.τ₃ := by
  -- The source proof first records that the middle complex is bounded below as well.
  have hB : CochainComplex.plus 𝒜 S.X₂ :=
    plus_of_shortExact (𝒜 := 𝒜) hS hA hC
  -- The source-faithful route starts with the pushout reduction to a degreewise split row whose
  -- left column is already the prescribed injective resolution.
  obtain ⟨T, ψ, σ, hψ₁, hψ₃, hT, hψ₂⟩ :=
    pushout_row_shortExact_degreewiseSplit (𝒜 := 𝒜) S hS I
  -- TODO: choose a termwise-monomorphic injective resolution of `T.X₃`, lift the connecting
  -- morphism from the split row via Lemma `13.18.6`, and build the upper-triangular middle
  -- injective complex so that `quasiIso_tau₂_of_shortExact` closes the final middle comparison.
  clear hB T ψ σ hψ₁ hψ₃ hT hψ₂
  sorry

-- Proof sketch: choose a bounded-below injective resolution of the left complex using
-- Lemma 13.18.3, then apply the prescribed-left-resolution theorem just proved above.
/-- Lemma 13.18.9: if `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` is a short exact sequence of cochain complexes
whose outer terms are bounded below, then it extends to a commutative diagram whose vertical maps
are injective resolutions and whose lower row is again a short exact sequence of complexes. The
middle term is bounded below because bounded-below cochain complexes are closed under extensions.
-/
theorem exists_injectiveResolutionDiagram_of_shortExact
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃) :
    ∃ row : ShortComplex (InjectivePlus 𝒜), ∃ hom : S ⟶ row.map injPlusι,
      (row.map injPlusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧ QuasiIso hom.τ₂ ∧ QuasiIso hom.τ₃ := by
  -- Route correction: the source proof first fixes the left resolution and proves the stronger
  -- theorem; the present statement is only the wrapper that chooses such a resolution.
  obtain ⟨a, hA'⟩ := (CochainComplex.plus_iff 𝒜 S.X₁).1 hA
  obtain ⟨I, -, -⟩ :=
    exists_injectiveResolution_strictlyGE_with_termwise_mono
      (𝒜 := 𝒜) (K := S.X₁) a hA'
  -- Apply the prescribed-left-resolution theorem and then package its lower row.
  obtain ⟨J, K, f, g, hfg, φ, hφ₁, hrow, hφ₂, hφ₃⟩ :=
    exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution
      (S := S) hS hA hC I
  refine ⟨ShortComplex.mk f g hfg, φ, hrow, ?_, hφ₂, hφ₃⟩
  -- The left vertical map is the chosen injective-resolution map, hence a quasi-isomorphism.
  simpa [hφ₁] using injectiveResolution_map_quasiIso I

-- Proof sketch: choose the left and right injective resolutions using Lemma 13.18.3 with lower
-- bound `0`, so their targets are zero in negative degrees, and then carry out the same
-- upper-triangular construction of the middle resolution; the direct-sum model is also zero in
-- negative degrees.
-- Proof sketch: combine the prescribed-left-resolution construction with the bounded-below choice
-- from the previous theorem, using the given lower bound on the chosen left resolution to keep
-- the whole lower row zero in negative degrees.
/-- If the outer terms of the original sequence are zero in negative degrees and the chosen left
injective resolution is also zero in negative degrees, then the middle term is automatically zero
in negative degrees, and the diagram can be built with that prescribed left comparison map and
with the remaining resolving complexes zero in negative degrees. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution_strictlyGE_zero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (hI : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE 0)
    (hA : S.X₁.IsStrictlyGE 0) (hC : S.X₃.IsStrictlyGE 0) :
    ∃ (J K : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧
          QuasiIso φ.τ₃ ∧
          (J : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
          (K : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 := by
  -- This is the same horseshoe construction as above, but with the right resolution chosen
  -- strictly in degrees `≥ 0` and with the explicit middle model checked degreewise.
  --
  -- TODO: after the prescribed-left-resolution horseshoe is implemented, specialize the right
  -- injective resolution to the `0`-bounded one from Lemma `13.18.3` and prove the resulting
  -- shifted mapping-cone/direct-sum complex is also strictly concentrated in nonnegative degrees.
  sorry

-- Proof sketch: choose the left injective resolution strictly in degrees `≥ 0` using
-- Lemma 13.18.3, then invoke the prescribed-left-resolution strictlyGE-zero theorem.
/-- If the outer terms of the original short exact sequence are zero in negative degrees, then the
middle term is also zero in negative degrees, and the injective-resolution diagram can be chosen
so that all three lower resolving complexes are zero in negative degrees as well. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_strictlyGE_zero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : S.X₁.IsStrictlyGE 0) (hC : S.X₃.IsStrictlyGE 0) :
    ∃ row : ShortComplex (InjectivePlus 𝒜), ∃ hom : S ⟶ row.map injPlusι,
      (row.map injPlusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧
        QuasiIso hom.τ₂ ∧
        QuasiIso hom.τ₃ ∧
        (row.X₁ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
        (row.X₂ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
        (row.X₃ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 := by
  -- Route correction: as in the source proof, first choose the left resolution in degrees `≥ 0`
  -- and only then appeal to the prescribed-left-resolution construction.
  obtain ⟨I, hI, -⟩ :=
    exists_injectiveResolution_strictlyGE_with_termwise_mono
      (𝒜 := 𝒜) (K := S.X₁) 0 hA
  -- Apply the prescribed strictly-nonnegative theorem and repackage its lower row.
  obtain ⟨J, K, f, g, hfg, φ, hφ₁, hrow, hφ₂, hφ₃, hJ, hK⟩ :=
    exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution_strictlyGE_zero
      (S := S) hS I hI hA hC
  refine ⟨ShortComplex.mk f g hfg, φ, hrow, ?_, hφ₂, hφ₃, ?_, hJ, hK⟩
  · -- The left column is the chosen injective resolution, so its comparison map is a quasi-isomorphism.
    simpa [hφ₁] using injectiveResolution_map_quasiIso I
  · -- The chosen left injective resolution was constructed to vanish in all negative degrees.
    simpa using hI

end

end CochainComplex
