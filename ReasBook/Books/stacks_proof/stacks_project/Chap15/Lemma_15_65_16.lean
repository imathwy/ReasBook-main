import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_11_5
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap15.Definition_15_59_13
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_2
import stacks_proof.stacks_project.Chap15.Lemma_15_65_6
import stacks_proof.stacks_project.Chap15.Lemma_15_65_16.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Ho" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q
private abbrev HoQ : Cpx ⥤ Ho :=
  HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/- Domain-style sampling for Lemma 15.65.16:
- primary domain: pseudo-coherence in `D(R)` and its behavior under the Chapter 15 derived tensor
  product owner;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: this file is `source-facing`, but its statements should stay directly on
  the canonical owners `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, the tensor notation
  `K ⊗[R]^L L`, and the homology functor owner `H`;
- primitive vs. derived:
  primitive data are the objects `K`, `L`, the bounds `n m a b`, and the homology-vanishing
  assumptions;
  derived API is the preservation of `m`-pseudo-coherence and pseudo-coherence under the canonical
  tensor owner.
-/

-- Proof sketch: choose bounded-above finite-projective models for `K` and `L` with the stated
-- cohomological control, compute the derived tensor product by the total tensor complex of these
-- models, and use the Tor spectral sequence to obtain isomorphisms above
-- `max (m + a) (n + b)` together with surjectivity in that degree.
/-- Helper for Lemma 15.65.16: pseudo-coherence is invariant under isomorphism in `D(R)`. -/
private theorem isPseudoCoherent_of_iso {K L : DMod} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Proof comment: keep the same bounded-above finite-free model and compose its comparison map
  -- with the target isomorphism.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.65.16: a pseudo-coherent derived complex is bounded above in the standard
`t`-structure. -/
private lemma pseudoCoherent_mem_t_minus
    (K : DMod) (hK : K.IsPseudoCoherent) :
    (t.minus : ObjectProperty DMod) K := by
  rcases hK with ⟨E, ⟨b, hE⟩, -, α, hα⟩
  let e : DerivedCategory.Q.obj E ≅ K := asIso α
  have hQ : (t.minus : ObjectProperty DMod) (DerivedCategory.Q.obj E) := by
    -- The chosen finite-free model is strictly zero above `b`, so its image in `D(R)` is
    -- bounded above at the same cutoff.
    refine ⟨b, ?_⟩
    change (DerivedCategory.Q.obj E).IsLE b
    exact (DerivedCategory.isLE_Q_obj_iff E b).2 inferInstance
  exact (t.minus : ObjectProperty DMod).prop_of_iso e hQ

/-- Helper for Lemma 15.65.16: a pseudo-coherent derived complex has vanishing cohomology in all
sufficiently large degrees. -/
private lemma eventually_isZero_homology_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((H i).obj K) := by
  -- Convert bounded-above membership into the usual eventual homology-vanishing formulation.
  exact
    (derivedCategory_t_minus_iff (K := K)).1
      (pseudoCoherent_mem_t_minus K hK)

/-- Helper for Lemma 15.65.16: conjugating a homotopy-category morphism along
`DerivedCategory.quotientCompQhIso` recovers the corresponding `DerivedCategory.Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {E K : Cpx} (f : E ⟶ K) :
    (Iso.homCongr
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K))
      (DerivedCategory.Qh.map (HoQ.map f)) =
        DerivedCategory.Q.map f := by
  -- Proof comment: this is the naturality square for `quotient ⋙ Qh ≅ Q`, rewritten as a
  -- conjugation identity on a literal cochain map.
  change
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        DerivedCategory.Qh.map (HoQ.map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map (HoQ.map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
        (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app E ≫
          DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f
  calc
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        DerivedCategory.Qh.map (HoQ.map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app E ≫
          DerivedCategory.Q.map f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫ k)
                hnat
    _ = DerivedCategory.Q.map f := by
          simpa using
            (Iso.inv_hom_id_assoc
              ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
              (DerivedCategory.Q.map f))

/-- Helper for Lemma 15.65.16: a derived composite out of a bounded-above projective source can
be represented by a literal cochain map. -/
private theorem exists_projective_minus_representative_of_composite
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {K L : Cpx} (ξ : (P : Cpx) ⟶ K)
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ β : (P : Cpx) ⟶ L, DerivedCategory.Q.map β = DerivedCategory.Q.map ξ ≫ α := by
  let eP := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P : Cpx)
  let eL := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app L
  let δ : DerivedCategory.Qh.obj (HoQ.obj P) ⟶ DerivedCategory.Qh.obj (HoQ.obj L) :=
    eP.hom ≫ DerivedCategory.Q.map ξ ≫ α ≫ eL.inv
  -- Proof comment: bounded-above projective sources see all derived morphisms already in the
  -- homotopy category, so we first lift the composite there.
  obtain ⟨βh, hβh⟩ :=
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L).surjective
      δ
  obtain ⟨β, hβ⟩ := HoQ.map_surjective βh
  refine ⟨β, ?_⟩
  have hQh : DerivedCategory.Qh.map (HoQ.map β) = δ := by
    simpa [hβ] using hβh
  -- Proof comment: conjugating the lifted `Qh`-identity back along `quotientCompQhIso` recovers
  -- the desired equality in `D(R)`.
  calc
    DerivedCategory.Q.map β =
      (Iso.homCongr eP eL) (DerivedCategory.Qh.map (HoQ.map β)) := by
        simpa using (quotientCompQhIso_homCongr_map (R := R) β).symm
    _ = (Iso.homCongr eP eL) δ := by simpa [hQh]
    _ = DerivedCategory.Q.map ξ ≫ α := by
      change eP.inv ≫ (eP.hom ≫ DerivedCategory.Q.map ξ ≫ α ≫ eL.inv) ≫ eL.hom =
        DerivedCategory.Q.map ξ ≫ α
      simp [Category.assoc]

/-- Helper for Lemma 15.65.16: an `IsLE a` bound on a derived object can be represented by an
actual cochain complex concentrated in degrees `≤ a`. -/
private theorem exists_strictlyLE_target_model_of_isLE
    (K : DMod) (a : ℤ) (hK : K.IsLE a) :
    ∃ Ka : Cpx, Ka.IsStrictlyLE a ∧ ∃ e : DerivedCategory.Q.obj Ka ≅ K, True := by
  let K0 : Cpx := DerivedCategory.Q.objPreimage K
  have hK0vanish : ∀ i : ℤ, a < i → IsZero (K0.homology i) := by
    intro i hi
    have hQi : IsZero ((H i).obj K) :=
      DerivedCategory.isZero_of_isLE K a i hi
    have hQpreimage :
        IsZero ((H i).obj (DerivedCategory.Q.obj K0)) := by
      let e :
          (H i).obj (DerivedCategory.Q.obj K0) ≅ (H i).obj K :=
        (H i).mapIso (DerivedCategory.Q.objObjPreimageIso K)
      exact (e.isZero_iff).2 hQi
    exact (((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K0).isZero_iff).1
      hQpreimage
  -- Proof comment: the source route truncates a chosen representative at the actual vanishing
  -- cutoff, so we package exactly that upper truncation as the bounded-above target model.
  have hK0le : K0.IsLE a := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hK0vanish i hi
  letI : K0.IsLE a := hK0le
  refine ⟨K0.truncLE a, inferInstance, ?_⟩
  refine ⟨asIso (DerivedCategory.Q.map (K0.ιTruncLE a)) ≪≫ DerivedCategory.Q.objObjPreimageIso K,
    trivial⟩

/-- Helper for Lemma 15.65.16: a bounded finite-free approximation map into `K` strictifies to an
actual chain map into any bounded-above target model of `K`. -/
private theorem lift_bounded_finite_free_approximation_to_truncated_target
    {E Ka : Cpx} {K : DMod}
    (hEbounded : ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b)
    (hEfree : E.IsTermwiseFiniteFree)
    (α : DerivedCategory.Q.obj E ⟶ K)
    (eKa : DerivedCategory.Q.obj Ka ≅ K) :
    ∃ α0 : E ⟶ Ka, DerivedCategory.Q.map α0 = α ≫ eKa.inv := by
  let P : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 <| by
        rcases hEbounded with ⟨_, b, _, hEb⟩
        exact ⟨b, hEb⟩⟩, fun i ↦ by
      let _ : E.IsTermwiseFiniteFree := hEfree
      change Projective (E.X i)
      infer_instance⟩
  obtain ⟨α0, hα0⟩ :=
    exists_projective_minus_representative_of_composite (R := R) P (𝟙 E) (α ≫ eKa.inv)
  refine ⟨α0, ?_⟩
  calc
    DerivedCategory.Q.map α0 = DerivedCategory.Q.map (𝟙 E) ≫ α ≫ eKa.inv := hα0
    _ = α ≫ eKa.inv := by simp

/-- Helper for Lemma 15.65.16: if the cone term of a distinguished triangle is concentrated in
degrees `< m`, then the first morphism induces cohomology isomorphisms above `m` and an
epimorphism in degree `m`. -/
private theorem homology_window_of_distinguishedTriangle_of_obj₃_isLE_pred
    (T : Triangle DMod) (hT : T ∈ distTriang DMod) (m : ℤ)
    (h₃ : T.obj₃.IsLE (m - 1)) :
    (∀ i : ℤ, m < i → IsIso ((H i).map T.mor₁)) ∧ Epi ((H m).map T.mor₁) := by
  constructor
  · intro i hi
    have hmor₂_zero : (H i).map T.mor₂ = 0 := by
      -- Proof comment: the cone term already has zero cohomology in degree `i`, so the map
      -- into that degree vanishes.
      exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) i (by omega)).eq_of_tgt _ _
    have hδ_zero : DerivedCategory.HomologySequence.δ T (i - 1) i (by omega) = 0 := by
      -- Proof comment: the same vanishing one degree lower kills the connecting morphism.
      exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) (i - 1) (by omega)).eq_of_src _ _
    letI : Epi ((H i).map T.mor₁) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 hmor₂_zero
    letI : Mono ((H i).map T.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT (i - 1) i (by omega)).2 hδ_zero
    -- Proof comment: once exactness makes the cohomology map both mono and epi, it is an
    -- isomorphism.
    simpa using isIso_of_mono_of_epi ((H i).map T.mor₁)
  · have hmor₂_zero : (H m).map T.mor₂ = 0 := by
      -- Proof comment: vanishing of the cone cohomology in degree `m` already gives the
      -- boundary epimorphism statement needed at the cutoff.
      exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) m (by omega)).eq_of_tgt _ _
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT m).2 hmor₂_zero

/-- Helper for Lemma 15.65.16: the theorem-local normalization API transports a fixed-`q`
page-one comparison to the corresponding `E₂` term. -/
private theorem associated_pageTwo_iso_of_pageOne_complex_iso_local
    (E : CohomologicalSpectralSequence (ModuleCat R) 0) (p q : ℤ)
    (C : Cpx)
    (e : CategoryTheory.Lemma_15_65_16.associatedPageOneComplex E q ≅ C) :
    Nonempty ((E.page 2).X (p, q) ≅ C.homology p) := by
  -- Proof comment: delegate the generic page-one/page-two transport to the theorem-local helper
  -- file so the remaining tensor comparison can stay focused on the source spectral-sequence map.
  simpa using
    (CategoryTheory.Lemma_15_65_16.associated_pageTwo_iso_of_pageOne_complex_iso_local
      (E := E) (p := p) (q := q) (C := C) e)

/-- Helper for Lemma 15.65.16: if an approximation morphism is an isomorphism on cohomology above
`m` and an epimorphism in degree `m`, then its mapping cone has no cohomology in degrees
`≥ m`. -/
private theorem approximation_cone_isLE_pred
    (T : Triangle DMod) (hT : T ∈ distTriang DMod) (m : ℤ)
    (hαiso : ∀ i : ℤ, m < i → IsIso ((H i).map T.mor₁))
    (hαepi : Epi ((H m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have him : m ≤ i := by
    omega
  have hmor₁_epi : Epi ((H i).map T.mor₁) := by
    by_cases him_eq : i = m
    · subst him_eq
      exact hαepi
    · have him_lt : m < i := lt_of_le_of_ne him fun h ↦ him_eq h.symm
      letI : IsIso ((H i).map T.mor₁) := hαiso i him_lt
      infer_instance
  have hmor₁_mono : Mono ((H (i + 1)).map T.mor₁) := by
    letI : IsIso ((H (i + 1)).map T.mor₁) := hαiso (i + 1) (by omega)
    infer_instance
  -- Proof comment: exactness first kills the map into the cone cohomology and then kills the
  -- connecting morphism one degree higher.
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
  -- Proof comment: a zero epimorphism has zero codomain, so the cone cohomology vanishes in
  -- degree `i`.
  exact IsZero.of_epi_eq_zero ((H i).map T.mor₂) hmor₂_zero

/-- Helper for Lemma 15.65.16: strictifying an approximation map to a bounded-above target model
preserves the original cohomology window, so its mapping cone is still concentrated in degrees
`< m`. -/
private theorem strictified_approximation_cone_isLE_pred
    {E Ka : Cpx} {K : DMod} (m : ℤ)
    (α : DerivedCategory.Q.obj E ⟶ K)
    (hαiso : ∀ i : ℤ, m < i → IsIso ((H i).map α))
    (hαepi : Epi ((H m).map α))
    (α0 : E ⟶ Ka)
    (eKa : DerivedCategory.Q.obj Ka ≅ K)
    (hα0 : DerivedCategory.Q.map α0 = α ≫ eKa.inv) :
    (DerivedCategory.Q.obj (CochainComplex.mappingCone α0)).IsLE (m - 1) := by
  have hα0iso : ∀ i : ℤ, m < i → IsIso ((H i).map (DerivedCategory.Q.map α0)) := by
    intro i hi
    -- Proof comment: the strictified map differs from the original approximation only by the
    -- chosen target isomorphism `eKa`.
    have hcomp : IsIso ((H i).map α ≫ (H i).map eKa.inv) := by
      letI : IsIso ((H i).map α) := hαiso i hi
      infer_instance
    simpa [hα0, Functor.map_comp] using hcomp
  have hα0epi : Epi ((H m).map (DerivedCategory.Q.map α0)) := by
    -- Proof comment: epimorphy at the cutoff is likewise preserved by postcomposing with the
    -- cohomology isomorphism induced by `eKa.inv`.
    have hcomp : Epi ((H m).map α ≫ (H m).map eKa.inv) := by
      letI : Epi ((H m).map α) := hαepi
      infer_instance
    simpa [hα0, Functor.map_comp] using hcomp
  have hT :
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α0) ∈
        distTriang DMod := by
    -- Proof comment: the standard mapping-cone triangle in the derived category is
    -- distinguished.
    simpa using
      DerivedCategory.mappingCone_triangle_distinguished α0
  -- Proof comment: now apply the earlier cone-vanishing criterion directly to the strictified
  -- approximation triangle.
  simpa using
    approximation_cone_isLE_pred
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α0))
      hT
      m
      hα0iso
      hα0epi

/-- Helper for Lemma 15.65.16: `m`-pseudo-coherence weakens monotonically in the cutoff index. -/
private theorem isMPseudoCoherent_mono_local
    {K : DMod} {m n : ℤ} (hmn : m ≤ n)
    (hK : K.IsMPseudoCoherent m) :
    K.IsMPseudoCoherent n := by
  rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
  -- Proof comment: keep the same bounded finite-free witness and only weaken the degree window.
  refine ⟨E, hbounds, hfree, α, ?_, ?_⟩
  · intro i hi
    exact hαgt i (lt_of_le_of_lt hmn hi)
  · by_cases hnm : n = m
    · subst hnm
      simpa using hαm
    · have hmn' : m < n := by
        omega
      letI : IsIso ((H n).map α) := hαgt n hmn'
      infer_instance

/-- Helper for Lemma 15.65.16: if a `t`-pseudo-coherent source maps to a target by a morphism
that is a cohomology isomorphism above `t` and an epimorphism in degree `t`, then the target is
also `t`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_homology_window
    {X Y : DMod} (t : ℤ) (f : X ⟶ Y)
    (hX : X.IsMPseudoCoherent t)
    (hfiso : ∀ i : ℤ, t < i → IsIso ((H i).map f))
    (hfepi : Epi ((H t).map f)) :
    Y.IsMPseudoCoherent t := by
  rcases hX with ⟨E, hbounds, hfree, α, hαiso, hαepi⟩
  -- Proof comment: compose the chosen approximation map for `X` with the windowed map `f`.
  refine ⟨E, hbounds, hfree, α ≫ f, ?_, ?_⟩
  · intro i hi
    have hcomp : IsIso ((H i).map α ≫ (H i).map f) := by
      letI : IsIso ((H i).map α) := hαiso i hi
      letI : IsIso ((H i).map f) := hfiso i hi
      infer_instance
    simpa [Functor.map_comp] using hcomp
  · have hcomp : Epi ((H t).map α ≫ (H t).map f) := by
      letI : Epi ((H t).map α) := hαepi
      letI : Epi ((H t).map f) := hfepi
      infer_instance
    simpa [Functor.map_comp] using hcomp

/-- Helper for Lemma 15.65.16: the tensor of two strictly bounded-above cochain complexes is
strictly bounded above by the sum of the two cutoffs. -/
private theorem tensorObj_isStrictlyLE_of_isStrictlyLE
    {E F : Cpx} {a b : ℤ}
    (hE : E.IsStrictlyLE a) (hF : F.IsStrictlyLE b) :
    CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj E F) (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  change 𝟙 ((CategoryTheory.GradedObject.Monoidal.tensorObj E.X F.X) n) = 0
  -- Proof comment: above `a + b`, every `(p,q)` summand has either `p > a` or `q > b`, so the
  -- corresponding tensor summand already vanishes.
  apply CategoryTheory.GradedObject.Monoidal.tensorObj_ext
  intro p q h
  have hpq : a < p ∨ b < q := by
    omega
  cases hpq with
  | inl hp =>
      let T : ModuleCat R ⥤ ModuleCat R :=
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).flip.obj (F.X q)
      have hzero : IsZero (E.X p) := E.isZero_of_isStrictlyLE a p hp
      have hsrc : IsZero (T.obj (E.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0
  | inr hq =>
      let T : ModuleCat R ⥤ ModuleCat R :=
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).obj (E.X p)
      have hzero : IsZero (F.X q) := F.isZero_of_isStrictlyLE b q hq
      have hsrc : IsZero (T.obj (F.X q)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0

/-- Helper for Lemma 15.65.16: the tensor of two strictly bounded-below cochain complexes is
strictly bounded below by the sum of the two lower cutoffs. -/
private theorem tensorObj_isStrictlyGE_of_isStrictlyGE
    {E F : Cpx} {a b : ℤ}
    (hE : E.IsStrictlyGE a) (hF : F.IsStrictlyGE b) :
    CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj E F) (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  change 𝟙 ((CategoryTheory.GradedObject.Monoidal.tensorObj E.X F.X) n) = 0
  -- Proof comment: below `a + b`, every `(p,q)` summand has either `p < a` or `q < b`, so the
  -- corresponding tensor summand already vanishes.
  apply CategoryTheory.GradedObject.Monoidal.tensorObj_ext
  intro p q h
  have hpq : p < a ∨ q < b := by
    omega
  cases hpq with
  | inl hp =>
      let T : ModuleCat R ⥤ ModuleCat R :=
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).flip.obj (F.X q)
      have hzero : IsZero (E.X p) := E.isZero_of_isStrictlyGE a p hp
      have hsrc : IsZero (T.obj (E.X p)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0
  | inr hq =>
      let T : ModuleCat R ⥤ ModuleCat R :=
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).obj (E.X p)
      have hzero : IsZero (F.X q) := F.isZero_of_isStrictlyGE b q hq
      have hsrc : IsZero (T.obj (F.X q)) := CategoryTheory.Functor.map_isZero T hzero
      simpa [T, Category.assoc] using
        hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0

/-- Helper for Lemma 15.65.16: each degree of the tensor total complex is finite free once both
inputs are bounded and termwise finite free. -/
private theorem tensor_degree_finite_free_of_bounded_bounds
    {E F : Cpx} (n aE bE aF bF : ℤ)
    (hEge : E.IsStrictlyGE aE) (hEle : E.IsStrictlyLE bE)
    (hFge : F.IsStrictlyGE aF) (hFle : F.IsStrictlyLE bF)
    (hEfree : E.IsTermwiseFiniteFree) (hFfree : F.IsTermwiseFiniteFree) :
    Module.Free R ((HomologicalComplex.tensorObj E F).X n) ∧
      Module.Finite R ((HomologicalComplex.tensorObj E F).X n) := by
  -- TODO: identify degree `n` with the finite direct sum of the surviving `(p,q)`-summands with
  -- `p + q = n`, then transport finite freeness across that finite decomposition.
  sorry

/-- Helper for Lemma 15.65.16: the tensor of two bounded finite-free complexes is itself a
bounded finite-free witness, so its image in `D(R)` is `t`-pseudo-coherent for every cutoff
`t`. -/
private theorem tensorObj_isMPseudoCoherent_of_bounded_termwiseFiniteFree
    (E F : Cpx) (t : ℤ)
    (hEbounded : ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b)
    (hFbounded : ∃ a b : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE b)
    (hEfree : E.IsTermwiseFiniteFree)
    (hFfree : F.IsTermwiseFiniteFree) :
    (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F)).IsMPseudoCoherent t := by
  rcases hEbounded with ⟨aE, bE, hEge, hEle⟩
  rcases hFbounded with ⟨aF, bF, hFge, hFle⟩
  have hTensorGE :
      CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj E F) (aE + aF) :=
    tensorObj_isStrictlyGE_of_isStrictlyGE (R := R) hEge hFge
  have hTensorLE :
      CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj E F) (bE + bF) :=
    tensorObj_isStrictlyLE_of_isStrictlyLE (R := R) hEle hFle
  have hTensorFree : CochainComplex.IsTermwiseFiniteFree (HomologicalComplex.tensorObj E F) := by
    refine ⟨fun n ↦ ?_⟩
    exact
      tensor_degree_finite_free_of_bounded_bounds
        (R := R) n aE bE aF bF hEge hEle hFge hFle hEfree hFfree
  -- Proof comment: use the total tensor complex itself as the bounded finite-free witness and
  -- take the identity comparison map in `D(R)`.
  refine
    ⟨HomologicalComplex.tensorObj E F, ⟨aE + aF, bE + bF, hTensorGE, hTensorLE⟩,
      hTensorFree, 𝟙 _, ?_, ?_⟩
  · intro i hi
    letI : IsIso ((H i).map (𝟙 (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F)))) :=
      Functor.map_isIso (H i) (𝟙 (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F)))
    infer_instance
  · letI : IsIso ((H t).map (𝟙 (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F)))) :=
      Functor.map_isIso (H t) (𝟙 (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F)))
    infer_instance

/-- Helper for Lemma 15.65.16: the strictified tensor comparison already has the source-faithful
homology window before transporting along the final tensor/derived-tensor identification. -/
private theorem tensor_strictified_comparison_homology_window
    {E F Ka Lb : Cpx}
    (n m a b : ℤ)
    (hKa : Ka.IsStrictlyLE a)
    (hLb : Lb.IsStrictlyLE b)
    (α0 : E ⟶ Ka)
    (β0 : F ⟶ Lb)
    (hConeα :
      (DerivedCategory.Q.obj (CochainComplex.mappingCone α0)).IsLE (n - 1))
    (hConeβ :
      (DerivedCategory.Q.obj (CochainComplex.mappingCone β0)).IsLE (m - 1)) :
    let τ := DerivedCategory.Q.map (HomologicalComplex.tensorHom α0 β0)
    (∀ i : ℤ, max (m + a) (n + b) < i → IsIso ((H i).map τ)) ∧
      Epi ((H (max (m + a) (n + b))).map τ) := by
  -- TODO: package the two source-faithful spectral-sequence windows for `τ`: the first
  -- filtration gives the `n + b` bound from `hConeα` and `hLb`, and the second filtration gives
  -- the `m + a` bound from `hConeβ` and `hKa`; then combine them at the maximum cutoff.
  sorry

/-- Helper for Lemma 15.65.16: after strictifying both approximation maps to bounded-above target
models, the induced map from the tensor of the finite-free witnesses to the derived tensor product
has the source-faithful homology window `> max (m + a, n + b)` and is epimorphic at the cutoff. -/
private theorem exists_tensor_strictified_comparison
    {E F Ka Lb : Cpx} {K L : DMod}
    (n m a b : ℤ)
    (hKa : Ka.IsStrictlyLE a)
    (hLb : Lb.IsStrictlyLE b)
    (eKa : DerivedCategory.Q.obj Ka ≅ K)
    (eLb : DerivedCategory.Q.obj Lb ≅ L)
    (α0 : E ⟶ Ka)
    (β0 : F ⟶ Lb)
    (hConeα :
      (DerivedCategory.Q.obj (CochainComplex.mappingCone α0)).IsLE (n - 1))
    (hConeβ :
      (DerivedCategory.Q.obj (CochainComplex.mappingCone β0)).IsLE (m - 1)) :
    ∃ γ : DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F) ⟶ K ⊗[R]^L L,
      (∀ i : ℤ, max (m + a) (n + b) < i → IsIso ((H i).map γ)) ∧
        Epi ((H (max (m + a) (n + b))).map γ) := by
  -- TODO: first prove `tensor_strictified_comparison_homology_window` for
  -- `Q.map (tensorHom α₀ β₀)`, then transport that window through the canonical comparison
  -- `Q.obj (tensorObj Ka Lb) ≅ K ⊗[R]^L L`.
  sorry

/-- Lemma 15.65.16 (1): if `K` is `n`-pseudo-coherent with vanishing cohomology in degrees
strictly above `a`, and `L` is `m`-pseudo-coherent with vanishing cohomology in degrees strictly
above `b`, then `K ⊗[R]^L L` is `max (m + a) (n + b)`-pseudo-coherent. -/
@[stacks 0DJE]
theorem derivedTensorProduct_isMPseudoCoherent_of_isMPseudoCoherent_of_vanishingAbove
    (K L : DMod) (n m a b : ℤ)
    (hK : K.IsMPseudoCoherent n)
    (hKvanish : ∀ i : ℤ, a < i → IsZero ((H i).obj K))
    (hL : L.IsMPseudoCoherent m)
    (hLvanish : ∀ j : ℤ, b < j → IsZero ((H j).obj L)) :
    (K ⊗[R]^L L).IsMPseudoCoherent (max (m + a) (n + b)) := by
  -- Route correction: the cone-to-homology-window direction is now isolated in
  -- `homology_window_of_distinguishedTriangle_of_obj₃_isLE_pred`. This pass reaches the
  -- source-faithful chain-level setup: keep the original bounded finite-free witnesses `E`, `F`,
  -- replace only the targets by strict `≤ a` and `≤ b` models, and strictify the two derived
  -- approximation maps to honest cochain maps `α₀`, `β₀`.
  have hKle : K.IsLE a := by
    -- Proof comment: the given cohomology-vanishing hypothesis is exactly the `IsLE a` owner.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hKvanish i hi
  have hLle : L.IsLE b := by
    -- Proof comment: similarly, the target-side vanishing for `L` determines the cutoff `b`.
    rw [DerivedCategory.isLE_iff]
    intro j hj
    exact hLvanish j hj
  rcases hK with ⟨E, hEbounded, hEfree, α, hαiso, hαepi⟩
  rcases hL with ⟨F, hFbounded, hFfree, β, hβiso, hβepi⟩
  obtain ⟨Ka, hKa, eKa, -⟩ :=
    exists_strictlyLE_target_model_of_isLE (R := R) K a hKle
  obtain ⟨Lb, hLb, eLb, -⟩ :=
    exists_strictlyLE_target_model_of_isLE (R := R) L b hLle
  obtain ⟨α0, hα0⟩ :=
    lift_bounded_finite_free_approximation_to_truncated_target
      (R := R) hEbounded hEfree α eKa
  obtain ⟨β0, hβ0⟩ :=
    lift_bounded_finite_free_approximation_to_truncated_target
      (R := R) hFbounded hFfree β eLb
  have hConeα :
      (DerivedCategory.Q.obj (CochainComplex.mappingCone α0)).IsLE (n - 1) := by
    -- Proof comment: the strictified approximation `α₀ : E ⟶ Ka` still has the original
    -- `n`-approximation window, so its cone stays concentrated in degrees `< n`.
    exact
      strictified_approximation_cone_isLE_pred
        (R := R)
        n
        α
        hαiso
        hαepi
        α0
        eKa
        hα0
  have hConeβ :
      (DerivedCategory.Q.obj (CochainComplex.mappingCone β0)).IsLE (m - 1) := by
    -- Proof comment: the same cone bound holds for the strictified approximation to `L`.
    exact
      strictified_approximation_cone_isLE_pred
        (R := R)
        m
        β
        hβiso
        hβepi
        β0
        eLb
        hβ0
  let t : ℤ := max (m + a) (n + b)
  have hSourceRaw :
      (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E F)).IsMPseudoCoherent t :=
    tensorObj_isMPseudoCoherent_of_bounded_termwiseFiniteFree
      (R := R) E F t hEbounded hFbounded hEfree hFfree
  obtain ⟨γ, hγiso, hγepi⟩ :=
    exists_tensor_strictified_comparison
      (R := R) n m a b hKa hLb eKa eLb α0 β0 hConeα hConeβ
  -- Proof comment: once the tensor of the two finite-free witnesses is available as the bounded
  -- source model, the whole theorem reduces to transporting that witness across the strictified
  -- comparison map `γ`.
  exact
    isMPseudoCoherent_of_homology_window
      (R := R) t γ hSourceRaw hγiso hγepi

-- Proof sketch: by Lemma `15.65.5`, pseudo-coherent objects admit bounded-above termwise finite
-- projective models, so they satisfy the hypotheses of part `(1)` for suitable cohomological
-- bounds; applying part `(1)` then yields pseudo-coherence of the derived tensor product.
/-- Lemma 15.65.16 (2): if `K` and `L` are pseudo-coherent, then
`K ⊗[R]^L L` is pseudo-coherent. -/
@[stacks 0DJE]
theorem derivedTensorProduct_isPseudoCoherent_of_isPseudoCoherent
    (K L : DMod)
    (hK : K.IsPseudoCoherent)
    (hL : L.IsPseudoCoherent) :
    (K ⊗[R]^L L).IsPseudoCoherent := by
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent]
  intro t
  obtain ⟨a, hKa⟩ :=
    eventually_isZero_homology_of_isPseudoCoherent (R := R) K hK
  obtain ⟨b, hLb⟩ :=
    eventually_isZero_homology_of_isPseudoCoherent (R := R) L hL
  have hKt : K.IsMPseudoCoherent (t - b) := by
    -- Proof comment: convert pseudo-coherence of `K` into the specific cutoff needed so that
    -- `(t - b) + b = t`.
    exact
      (isPseudoCoherent_iff_forall_isMPseudoCoherent (R := R) K).1 hK (t - b)
  have hLt : L.IsMPseudoCoherent (t - a) := by
    -- Proof comment: choose the matching cutoff for `L` so that `(t - a) + a = t`.
    exact
      (isPseudoCoherent_iff_forall_isMPseudoCoherent (R := R) L).1 hL (t - a)
  have hTensor :
      (K ⊗[R]^L L).IsMPseudoCoherent
        (max ((t - a) + a) ((t - b) + b)) := by
    -- Proof comment: part `(1)` applies once both pseudo-coherent inputs are specialized to these
    -- tailored cutoffs and the eventual homology-vanishing bounds are supplied.
    exact
      derivedTensorProduct_isMPseudoCoherent_of_isMPseudoCoherent_of_vanishingAbove
        (R := R)
        K
        L
        (t - b)
        (t - a)
        a
        b
        hKt
        hKa
        hLt
        hLb
  simpa using hTensor

end

end CategoryTheory
