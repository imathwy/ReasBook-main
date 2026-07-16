import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_11
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_10
import StacksProject_2024.stacks_project.Chap15.Definition_15_69_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling:
- primary domain: vanishing of morphisms in derived categories and splitting distinguished
  triangles via the canonical binary-biproduct structure;
- sampled owner declarations:
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CochainComplex.derivedCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`,
  `CategoryTheory.isSplitEpi_mor₂_of_distinguished_mor₃_eq_zero`;
- best owner abstractions: `HasProjectiveAmplitudeIn` is the chapter-level source-facing amplitude
  predicate, `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang` is the canonical
  split-triangle owner, so the source-facing compatibility data should remain the owner theorem's
  native pair of equations rather than a parallel local wrapper;
- primitive data: the amplitude witness on `L`, the homology-vanishing hypothesis on `K`, the
  distinguished-triangle maps, and the chosen isomorphism to a biproduct;
- derived API: vanishing of `Hom(L, K)`, existence of a compatible biproduct isomorphism, and the
  corresponding uniqueness statement.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `15.77.1`;
- `core/canonical`: `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- `bridge/view`: the conjunction
  `f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g`, which exposes the source-facing
  compatibility equations without creating a second owner for split triangles.
-/

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Helper for Lemma 15.77.1: a projective-amplitude witness can be repackaged as a
`ProjectiveMinus` representative with the same lower support bound. -/
private theorem exists_projectiveMinus_iso_of_hasProjectiveAmplitudeIn
    {L : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b) :
    ∃ P : CochainComplex.ProjectiveMinus (ModuleCat R),
      Nonempty (L ≅ DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ)) ∧
        (P : CochainComplex (ModuleCat R) ℤ).IsStrictlyGE a := by
  rcases hL with ⟨P, e, hPge, hPle, hPproj⟩
  let Pminus : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨P, (CochainComplex.minus_iff (ModuleCat R) P).2 ⟨b, hPle⟩⟩, hPproj⟩
  -- The only change is the packaging of the bounded-above/projective data into the owner
  -- `ProjectiveMinus`; the represented derived object and lower cutoff stay unchanged.
  refine ⟨Pminus, ?_, ?_⟩
  · exact ⟨by simpa [Pminus] using e⟩
  · simpa [Pminus] using hPge

-- Proof sketch: choose a projective representative of `L` concentrated in degrees `[a, b]` from
-- `HasProjectiveAmplitudeIn`, replace `K` by a representative with zero terms in degrees `≥ a`
-- using the cohomology-vanishing hypothesis, and then apply Lemma `13.19.10` to conclude that
-- every map `L ⟶ K` in `D(R)` is zero.
/-- Lemma 15.77.1 (1): if `L` has projective-amplitude in `[a, b]` and the cohomology of `K`
vanishes in all degrees `i ≥ a`, then every morphism `L ⟶ K` in `D(R)` is zero. In particular,
this applies when `L` is perfect of tor-amplitude in `[a, b]`. -/
theorem hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge
    {K L : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj K))
    (f : L ⟶ K) :
    f = 0 := by
  obtain ⟨P, ⟨eL⟩, hPge⟩ := exists_projectiveMinus_iso_of_hasProjectiveAmplitudeIn hL
  let K' : CochainComplex (ModuleCat R) ℤ := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj K' ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hK' : ∀ i : ℤ, a ≤ i → IsZero (K'.homology i) := by
    intro i hi
    have hQi : IsZero ((H i).obj K) := hK i hi
    have hQpreimage : IsZero ((H i).obj (DerivedCategory.Q.obj K')) := by
      -- Move the cohomology-vanishing hypothesis onto the chosen represented target.
      exact ((H i).mapIso eK).isZero_iff.2 hQi
    -- The canonical comparison identifies derived homology of `Q.obj K'` with `K'.homology i`.
    exact (((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K').isZero_iff).1
      hQpreimage
  have hf' : eL.inv ≫ f ≫ eK.inv = 0 := by
    -- After transporting both source and target to complexes, the owner vanishing theorem applies.
    exact
      CochainComplex.derivedCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
        a hPge hK' (eL.inv ≫ f ≫ eK.inv)
  -- Transport the vanishing statement back across the chosen source and target isomorphisms.
  calc
    f = eL.hom ≫ (eL.inv ≫ f ≫ eK.inv) ≫ eK.hom := by simp [Category.assoc]
    _ = 0 := by simp [hf']

/-- Helper for Lemma 15.77.1: compatible biproduct splittings are unique once every morphism
`L ⟶ K` vanishes. -/
private theorem compatible_biprod_iso_unique_of_hom_eq_zero
    {K L M : DMod}
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod)
    (hLK : ∀ u : L ⟶ K, u = 0)
    {e₁ e₂ : M ≅ K ⊞ L}
    (he₁₁ : f ≫ e₁.hom = biprod.inl)
    (he₁₂ : e₁.hom ≫ biprod.snd = g)
    (he₂₁ : f ≫ e₂.hom = biprod.inl)
    (he₂₂ : e₂.hom ≫ biprod.snd = g) :
    e₁ = e₂ := by
  let s₁ : L ⟶ M := biprod.inr ≫ e₁.inv
  let s₂ : L ⟶ M := biprod.inr ≫ e₂.inv
  have hs₁g : s₁ ≫ g = 𝟙 L := by
    -- Each compatible splitting gives a section of `g`.
    calc
      s₁ ≫ g = biprod.inr ≫ e₁.inv ≫ (e₁.hom ≫ biprod.snd) := by
        simp [s₁, he₁₂, Category.assoc]
      _ = 𝟙 L := by simp
  have hs₂g : s₂ ≫ g = 𝟙 L := by
    -- The same computation applies to the second splitting.
    calc
      s₂ ≫ g = biprod.inr ≫ e₂.inv ≫ (e₂.hom ≫ biprod.snd) := by
        simp [s₂, he₂₂, Category.assoc]
      _ = 𝟙 L := by simp
  have hinv₁ : biprod.inl ≫ e₁.inv = f := by
    -- Compatibility with the first map determines the `K`-component of the inverse.
    calc
      biprod.inl ≫ e₁.inv = (f ≫ e₁.hom) ≫ e₁.inv := by rw [he₁₁]
      _ = f := by simp [Category.assoc]
  have hinv₂ : biprod.inl ≫ e₂.inv = f := by
    -- The same identification holds for the second inverse.
    calc
      biprod.inl ≫ e₂.inv = (f ≫ e₂.hom) ≫ e₂.inv := by rw [he₂₁]
      _ = f := by simp [Category.assoc]
  have hzero : (s₁ - s₂) ≫ g = 0 := by
    -- Subtracting the two sections annihilates under `g`.
    rw [Preadditive.sub_comp, hs₁g, hs₂g, sub_self]
  obtain ⟨u, hu⟩ :=
    Triangle.coyoneda_exact₂ (T := Triangle.mk f g δ) hT (s₁ - s₂) hzero
  have hu_zero : u = 0 := hLK u
  have hs_eq : s₁ = s₂ := by
    -- Exactness factors the section difference through `f`, and `Hom(L, K)` vanishing kills it.
    have hu' : u ≫ (Triangle.mk f g δ).mor₁ = 0 := by
      rw [hu_zero]
      exact zero_comp
    have hsub : s₁ - s₂ = 0 := by
      calc
        s₁ - s₂ = u ≫ (Triangle.mk f g δ).mor₁ := hu
        _ = 0 := hu'
    exact sub_eq_zero.mp hsub
  have heinv₁ : e₁.inv = biprod.desc f s₁ := by
    -- An inverse to a compatible splitting is determined by its two biproduct components.
    apply biprod.hom_ext'
    · simpa [s₁] using hinv₁
    · simp [s₁]
  have heinv₂ : e₂.inv = biprod.desc f s₂ := by
    -- The second inverse has the same normal form.
    apply biprod.hom_ext'
    · simpa [s₂] using hinv₂
    · simp [s₂]
  have h_inv : e₁.inv = e₂.inv := by
    -- Once the sections agree, the two inverses coincide.
    calc
      e₁.inv = biprod.desc f s₁ := heinv₁
      _ = biprod.desc f s₂ := by simpa [hs_eq]
      _ = e₂.inv := heinv₂.symm
  have h_hom : e₁.hom = e₂.hom := by
    -- Equality of inverses forces equality of the forward isomorphisms.
    apply (cancel_mono e₁.inv).1
    calc
      e₁.hom ≫ e₁.inv = 𝟙 M := by simp
      _ = e₂.hom ≫ e₂.inv := by simp
      _ = e₂.hom ≫ e₁.inv := by rw [h_inv]
  apply Iso.ext
  exact h_hom

-- Proof sketch: apply part `(1)` to the shifted target `K⟦(1 : ℤ)⟧` to deduce that the
-- connecting morphism `L ⟶ K⟦1⟧` of the distinguished triangle is zero. Lemma `13.4.11`
-- then gives a right inverse to `M ⟶ L`, and hence an isomorphism `M ≅ K ⊞ L` compatible with
-- the first and second maps of the triangle.
/-- Lemma 15.77.1 (2): if `L` has projective-amplitude in `[a, b]`, if the cohomology of `K`
vanishes in all degrees `i ≥ a + 1`, and if `K ⟶ M ⟶ L ⟶ K⟦1⟧` is a distinguished triangle in
`D(R)`, then there is an isomorphism `M ≅ K ⊞ L` compatible with the maps `K ⟶ M` and
`M ⟶ L`. -/
theorem exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ
    {K L M : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a + 1 ≤ i → IsZero ((H i).obj K))
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod) :
    ∃ e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g := by
  have hKshift : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj (K⟦(1 : ℤ)⟧)) := by
    intro i hi
    have hKi : IsZero ((H (i + 1)).obj K) := hK (i + 1) (by omega)
    -- Rewrite the shifted homology group back to the unshifted one in degree `i + 1`.
    exact
      (((H 0).shiftIso (1 : ℤ) i (i + 1) (add_comm 1 i)).app K).isZero_iff.2 hKi
  have hδ_zero : δ = 0 := by
    -- Part `(1)` applied to the shifted target kills the connecting morphism.
    exact
      hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge
        hL hKshift δ
  -- Once the connecting morphism vanishes, the distinguished triangle splits canonically.
  obtain ⟨e, he₁, he₂⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk f g δ) hT hδ_zero
  exact ⟨e, he₁, he₂.symm⟩

-- Proof sketch: part `(2)` gives existence once the stronger cohomology-vanishing hypothesis
-- forces the connecting morphism to vanish. For uniqueness, compare two compatible splittings by
-- a morphism of distinguished triangles and use part `(1)` to show the relevant cross-Hom group
-- `Hom_{D(R)}(L, K)` vanishes, so the comparison morphism is unique.
/-- Lemma 15.77.1 (3): if `L` has projective-amplitude in `[a, b]`, if the cohomology of `K`
vanishes in all degrees `i ≥ a`, and if `K ⟶ M ⟶ L ⟶ K⟦1⟧` is a distinguished triangle in
`D(R)`, then there exists a unique isomorphism `M ≅ K ⊞ L` compatible with the maps
`K ⟶ M` and `M ⟶ L`. -/
theorem existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge
    {K L M : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj K))
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod) :
    ∃! e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g := by
  have hKsucc : ∀ i : ℤ, a + 1 ≤ i → IsZero ((H i).obj K) := by
    intro i hi
    exact hK i (by omega)
  obtain ⟨e, he₁, he₂⟩ :=
    exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ
      hL hKsucc hT
  refine ⟨e, ⟨he₁, he₂⟩, ?_⟩
  intro e' he'
  -- Existence comes from part `(2)`, while uniqueness is reduced to the vanishing of `Hom(L, K)`.
  exact compatible_biprod_iso_unique_of_hom_eq_zero (e₁ := e') (e₂ := e) hT
    (fun u ↦ hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge hL hK u)
    he'.1 he'.2 he₁ he₂

end

end CategoryTheory
