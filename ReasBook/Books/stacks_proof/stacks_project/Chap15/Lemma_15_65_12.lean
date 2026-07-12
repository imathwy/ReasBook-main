import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Basis
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_65_6
import StacksProject_2024.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape
open scoped DerivedTensorWithAlgebra
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "HB" => DerivedCategory.homologyFunctor (ModuleCat B)
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "KModA" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "QisA" => HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)
local notation "QhA" => (DerivedCategory.Qh : KModA ⥤ DModA)

/-- Helper for Lemma 15.65.12: the additive functor on homotopy categories induced by a functor
to the derived category. -/
private abbrev mapHomotopyCategoryToDerived
    {C : Type u} {E : Type u} [Category C] [Category E] [Preadditive C] [Abelian E]
    [HasDerivedCategory E] (F : C ⥤ E) [F.Additive] :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory E :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/- Domain-style sampling for Lemma 15.65.12:
- primary domain: derived scalar extension on module derived categories and preservation of
  pseudo-coherence;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`;
- best owner abstraction: the core/canonical owner is the derived scalar-extension functor
  `derivedTensorWithAlgebra (algebraMap A B) : D(A) ⥤ D(B)`, with pseudo-coherence carried by the existing
  `DerivedCategory` predicates rather than any local wrapper;
- primitive vs. derived:
  primitive data are the ring map `A → B` and the pseudo-coherence witness on `K`;
  the preservation statements below are derived API over that owner;
- source/core/bridge triage:
  `source-facing`: scalar extension preserves `m`-pseudo-coherence and pseudo-coherence;
  `core/canonical`: `derivedTensorWithAlgebra` and the `DerivedCategory` pseudo-coherence owners;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to an object.
- layer: this file is source-facing over canonical owners, so the theorem surface should use the
  existing owner notation instead of repeating raw functor application terms. -/

/-- Helper for Lemma 15.65.12: pseudo-coherence is invariant under isomorphism in the derived
category. -/
private theorem isPseudoCoherent_of_iso {K L : DModA} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Proof comment: keep the same bounded-above finite-free model and compose its comparison map
  -- with the given derived isomorphism.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.65.12: a derived complex is pseudo-coherent exactly when it is
`m`-pseudo-coherent for every integer `m`. This local bridge reuses the earlier canonical
derived-category iff without changing the target statement. -/
private theorem pseudoCoherent_iff_forall_mPseudoCoherent (K : DModA) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  -- Proof comment: this is exactly the earlier Chapter 15 owner theorem, specialized to the
  -- present coefficient ring `A`.
  simpa using isPseudoCoherent_iff_forall_isMPseudoCoherent (R := A) K

/-- Helper for Lemma 15.65.12: the scalar-extended cochain complex obtained by applying ordinary
extension of scalars termwise to a cochain complex of `A`-modules. -/
private abbrev scalarExtendedComplex (E : CpxA) :
    CochainComplex (ModuleCat B) ℤ :=
  (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj E)

/-- Helper for Lemma 15.65.12: identify the restricted `B`-module `B` with itself so that the
termwise scalar-extension object can be rewritten as the standard tensor product `B ⊗[A] M`. -/
private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.65.12: the restricted `B`-module underlying `B` forms the expected scalar
tower over `A`, so the tensor-product comparison may be written over `B`. -/
private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/-- Helper for Lemma 15.65.12: each term of the ordinary scalar-extended complex is canonically
the tensor product `B ⊗[A] E^i`. -/
private noncomputable def extendScalarsTermLinearEquiv (E : CpxA) (i : ℤ) :
    ((scalarExtendedComplex (A := A) (B := B) E).X i : ModuleCat B) ≃ₗ[B] (B ⊗[A] (E.X i)) := by
  -- Proof comment: unfold `ModuleCat.extendScalars` once and rewrite the chosen scalar-extended
  -- term into the canonical algebra-tensor-module model.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv (A := A) (B := B))
      (LinearEquiv.refl A (E.X i)))

/-- Helper for Lemma 15.65.12: scalar extension sends a finite free term of `E` to a free
`B`-module. -/
private noncomputable instance extendScalars_mapHomologicalComplex_term_moduleFree
    (E : CpxA) (i : ℤ) [Module.Free A (E.X i)] :
    Module.Free B
      ((scalarExtendedComplex (A := A) (B := B) E).X i : ModuleCat B) := by
  -- Proof comment: choose a basis of `E.X i`, base-change that basis to `B`, and transport it
  -- across the canonical tensor-product identification of the scalar-extended term.
  let b := (Module.Free.chooseBasis A (E.X i)).baseChange B
  exact Module.Free.of_basis (b.map (extendScalarsTermLinearEquiv (A := A) (B := B) E i).symm)

/-- Helper for Lemma 15.65.12: scalar extension sends a finite free term of `E` to a finite
`B`-module. -/
private noncomputable instance extendScalars_mapHomologicalComplex_term_moduleFinite
    (E : CpxA) (i : ℤ) [Module.Free A (E.X i)] [Module.Finite A (E.X i)] :
    Module.Finite B
      ((scalarExtendedComplex (A := A) (B := B) E).X i : ModuleCat B) := by
  -- Proof comment: the same base-changed basis is finite, so it witnesses finite generation of
  -- the scalar-extended term over `B`.
  let b := (Module.Free.chooseBasis A (E.X i)).baseChange B
  exact Module.Finite.of_basis
    (b.map (extendScalarsTermLinearEquiv (A := A) (B := B) E i).symm)

/-- Helper for Lemma 15.65.12: termwise finite freeness is preserved by ordinary scalar extension
of cochain complexes. -/
private theorem extendScalars_mapHomologicalComplex_isTermwiseFiniteFree
    (E : CpxA) (hE : E.IsTermwiseFiniteFree) :
    (scalarExtendedComplex (A := A) (B := B) E).IsTermwiseFiniteFree := by
  letI : E.IsTermwiseFiniteFree := hE
  -- Proof comment: each scalar-extended term inherits the free and finite instances proved just
  -- above, so the whole cochain complex is termwise finite free.
  refine ⟨fun i ↦ ?_⟩
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 15.65.12: ordinary scalar extension preserves a lower support bound on a
cochain complex. -/
private theorem scalarExtendedComplex_isStrictlyGE
    (E : CpxA) {a : ℤ} (hE : E.IsStrictlyGE a) :
    (scalarExtendedComplex (A := A) (B := B) E).IsStrictlyGE a := by
  letI : E.IsStrictlyGE a := hE
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  -- Proof comment: in degrees below the lower cutoff, the source term is already zero, and exact
  -- scalar extension preserves zero objects.
  exact (ModuleCat.extendScalars (algebraMap A B)).map_isZero (E.isZero_of_isStrictlyGE a i hi)

/-- Helper for Lemma 15.65.12: ordinary scalar extension preserves an upper support bound on a
cochain complex. -/
private theorem scalarExtendedComplex_isStrictlyLE
    (E : CpxA) {b : ℤ} (hE : E.IsStrictlyLE b) :
    (scalarExtendedComplex (A := A) (B := B) E).IsStrictlyLE b := by
  letI : E.IsStrictlyLE b := hE
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  -- Proof comment: in degrees above the upper cutoff, the source term is zero, so its
  -- scalar-extended term is zero as well.
  exact (ModuleCat.extendScalars (algebraMap A B)).map_isZero (E.isZero_of_isStrictlyLE b i hi)

/-- Helper for Lemma 15.65.12: this is the explicit total-left-derived counit comparison from the
derived tensor of a strict cochain model to its ordinary scalar extension. -/
private noncomputable def derivedTensorWithAlgebra_complexComparison
    (E : CpxA) :
    ((derivedTensorWithAlgebra (algebraMap A B)).obj (DerivedCategory.Q.obj E)) ⟶
      DerivedCategory.Q.obj (scalarExtendedComplex (A := A) (B := B) E) :=
  let F₀ : ModuleCat A ⥤ ModuleCat B := ModuleCat.extendScalars (algebraMap A B)
  letI : F₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).left_adjoint_additive
  let F : KModA ⥤ DModB := mapHomotopyCategoryToDerived F₀
  letI : F.HasLeftDerivedFunctor QisA := by
    change
      (mapHomotopyCategoryToDerived
        (ModuleCat.extendScalars (algebraMap A B))).HasLeftDerivedFunctor QisA
    simpa [mapHomotopyCategoryToDerived] using
      extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap A B)
  -- Proof comment: conjugate the total-left-derived counit by `quotientCompQhIso` on the source
  -- and target so that the right-hand side is written as the strict scalar-extended complex.
  (derivedTensorWithAlgebra (algebraMap A B)).map
      ((DerivedCategory.quotientCompQhIso (ModuleCat A)).app E).inv ≫
    (F.totalLeftDerivedCounit QhA QisA).app
      ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj E) ≫
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat B) (up ℤ) ⥤ DModB).map
      ((Functor.mapHomotopyCategoryFactors
        (ModuleCat.extendScalars (algebraMap A B)) (up ℤ)).inv.app E) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat B)).app
      (scalarExtendedComplex (A := A) (B := B) E)).hom

/-- Helper for Lemma 15.65.12: bounded-above finite-free complexes compute derived tensor by
ordinary scalar extension. -/
private theorem derivedTensorWithAlgebra_complexComparison_isIso_of_termwiseFiniteFree
    (E : CpxA) (hE : E.IsTermwiseFiniteFree)
    {b : ℤ} (hEb : E.IsStrictlyLE b) :
    IsIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E) := by
  -- Route correction: the proof now has the correct explicit counit morphism; the remaining work
  -- is to show that a bounded-above finite-free complex computes the left derived functor of
  -- extension of scalars, so this counit component is invertible.
  -- TODO: show each finite free term is left acyclic for `ModuleCat.extendScalars (algebraMap A B)`,
  -- apply `computes_unbounded_leftDerived_of_termwise_higherLeftDerivedVanishes` to the homotopy
  -- quotient of `E`, and then rewrite `Functor.computesLeftDerivedAt_iff` along the displayed
  -- comparison morphism.
  let _ := hE
  let _ := hEb
  sorry

/-- Helper for Lemma 15.65.12: derived tensor preserves upper cohomological bounds. -/
private theorem derivedTensorWithAlgebra_preserves_isLE
    (C : DModA) (n : ℤ) (hC : C.IsLE n) :
    ((derivedTensorWithAlgebra (algebraMap A B)).obj C).IsLE n := by
  -- TODO: use the truncation triangle `τ≤n C ⟶ C ⟶ τ≥(n + 1) C ⟶` and the left-derived
  -- truncation-comparison theorem to show that `LF(C)` has the same homology as `LF(τ≥(n + 1) C)`
  -- in degrees `> n`; since `τ≥(n + 1) C` is zero under `hC`, those homology objects vanish.
  let _ := hC
  sorry

/-- Helper for Lemma 15.65.12: if the approximation morphism is an isomorphism on cohomology
above `m` and an epimorphism in degree `m`, then its cone has no cohomology in degrees `≥ m`. -/
private theorem approximation_cone_isLE_pred
    (T : Triangle DModA) (hT : T ∈ distTriang DModA) (m : ℤ)
    (hαiso : ∀ i : ℤ, m < i → IsIso ((HA i).map T.mor₁))
    (hαepi : Epi ((HA m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have him : m ≤ i := by omega
  have hmor₁_epi : Epi ((HA i).map T.mor₁) := by
    by_cases him_eq : i = m
    · subst him_eq
      exact hαepi
    · have him_lt : m < i := lt_of_le_of_ne him fun h ↦ him_eq h.symm
      letI : IsIso ((HA i).map T.mor₁) := hαiso i him_lt
      infer_instance
  have hmor₁_mono : Mono ((HA (i + 1)).map T.mor₁) := by
    letI : IsIso ((HA (i + 1)).map T.mor₁) := hαiso (i + 1) (by omega)
    infer_instance
  -- Proof comment: exactness of the long exact sequence first kills the map into the cone
  -- cohomology and then kills the connecting morphism one degree higher.
  have hmor₂_zero : (HA i).map T.mor₂ = 0 := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hmor₁_epi
  have hδ_zero : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    exact
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT i (i + 1) rfl).1 hmor₁_mono
  have hmor₂_epi : Epi ((HA i).map T.mor₂) := by
    exact
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
        T hT i (i + 1) rfl).2 hδ_zero
  -- Proof comment: a zero epimorphism has zero codomain, so the cone cohomology vanishes in
  -- degree `i`.
  exact CategoryTheory.Limits.IsZero.of_epi_eq_zero ((HA i).map T.mor₂) hmor₂_zero

/-- Helper for Lemma 15.65.12: if the third vertex of a distinguished triangle has no cohomology
in degrees `≥ m`, then the first morphism is an isomorphism on cohomology above `m` and an
epimorphism in degree `m`. -/
private theorem homology_window_of_distinguishedTriangle_of_obj₃_isLE_pred
    (T : Triangle DModB) (hT : T ∈ distTriang DModB) (m : ℤ)
    (h₃ : T.obj₃.IsLE (m - 1)) :
    (∀ i : ℤ, m < i → IsIso ((HB i).map T.mor₁)) ∧ Epi ((HB m).map T.mor₁) := by
  constructor
  · intro i hi
    have hmor₂_zero : (HB i).map T.mor₂ = 0 := by
      exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) i (by omega)).eq_of_tgt _ _
    have hδ_zero : DerivedCategory.HomologySequence.δ T (i - 1) i (by omega) = 0 := by
      exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) (i - 1) (by omega)).eq_of_src _ _
    letI : Epi ((HB i).map T.mor₁) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 hmor₂_zero
    letI : Mono ((HB i).map T.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT (i - 1) i (by omega)).2 hδ_zero
    -- Proof comment: once both mono and epi come from the vanishing cone cohomology window, the
    -- cohomology map is an isomorphism.
    simpa using isIso_of_mono_of_epi ((HB i).map T.mor₁)
  · have hmor₂_zero : (HB m).map T.mor₂ = 0 := by
      exact (DerivedCategory.isZero_of_isLE T.obj₃ (m - 1) m (by omega)).eq_of_tgt _ _
    -- Proof comment: exactness at degree `m` gives the required epimorphism on the first
    -- cohomology map once the cone cohomology already vanishes there.
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT m).2 hmor₂_zero

-- Proof sketch: choose a bounded finite-free approximation of `K` as in the definition of
-- `m`-pseudo-coherence, apply derived scalar extension to the comparison map, and use that
-- tensoring a finite free complex with `B` stays finite free over `B`, while the cone stays
-- acyclic in degrees `≥ m`.
/-- Lemma 15.65.12: derived extension of scalars along `A → B` preserves `m`-pseudo-coherent
objects of `D(A)`. -/
@[stacks 0650]
theorem derivedTensorWithAlgebra_isMPseudoCoherent
    (K : DModA) (m : ℤ) (hK : K.IsMPseudoCoherent m) :
    (K ⊗[A]^L[B]).IsMPseudoCoherent m := by
  rcases hK with ⟨E, ⟨a, b, hEge, hEle⟩, hEfree, α, hαiso, hαepi⟩
  obtain ⟨C, β, δ, hTα⟩ := distinguished_cocone_triangle α
  let E' := scalarExtendedComplex (A := A) (B := B) E
  have hE'free : E'.IsTermwiseFiniteFree := by
    -- Proof comment: the finite-free source approximation stays finite free after ordinary
    -- scalar extension, so the only remaining work is to compare it with derived tensor.
    exact extendScalars_mapHomologicalComplex_isTermwiseFiniteFree (A := A) (B := B) E hEfree
  have hCone : C.IsLE (m - 1) := by
    -- Proof comment: the source approximation has the required homology window, so its cone is
    -- concentrated in degrees `< m`.
    simpa using
      approximation_cone_isLE_pred (A := A)
        (Triangle.mk α β δ)
        hTα
        m hαiso hαepi
  letI : E'.IsTermwiseFiniteFree := hE'free
  have hE'ge : E'.IsStrictlyGE a := by
    -- Proof comment: ordinary scalar extension is termwise and does not change the support
    -- bounds of the chosen approximation complex.
    exact scalarExtendedComplex_isStrictlyGE (A := A) (B := B) E hEge
  have hE'le : E'.IsStrictlyLE b := by
    -- Proof comment: the same support-preservation applies on the bounded-above side.
    exact scalarExtendedComplex_isStrictlyLE (A := A) (B := B) E hEle
  let T :=
    (derivedTensorWithAlgebra (algebraMap A B)).mapTriangle.obj
      (Triangle.mk α β δ)
  have hT : T ∈ distTriang DModB := by
    -- Proof comment: derived tensor is exact, so it sends the approximation triangle to another
    -- distinguished triangle.
    simpa [T] using
      (derivedTensorWithAlgebra_isTriangulated (R := A) (A := B) (algebraMap A B)).map_distinguished
        (Triangle.mk α β δ)
        hTα
  have hTensorCone : T.obj₃.IsLE (m - 1) := by
    -- Proof comment: the cone bound survives derived tensor by the new truncation-comparison
    -- helper.
    simpa [T] using
      derivedTensorWithAlgebra_preserves_isLE (A := A) (B := B) C (m - 1) hCone
  have hComparisonIso :
      IsIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E) := by
    -- Proof comment: this is the one remaining source-faithful bridge: bounded-above finite-free
    -- complexes compute derived tensor by ordinary tensor.
    exact
      derivedTensorWithAlgebra_complexComparison_isIso_of_termwiseFiniteFree
        (A := A) (B := B) E hEfree hEle
  let comparison :
      (DerivedCategory.Q.obj E ⊗[A]^L[B]) ≅
        DerivedCategory.Q.obj E' :=
    asIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E)
  let α' : DerivedCategory.Q.obj E' ⟶ (K ⊗[A]^L[B]) :=
    comparison.inv ≫ (derivedTensorWithAlgebra (algebraMap A B)).map α
  obtain ⟨hα'iso_raw, hα'epi_raw⟩ :=
    homology_window_of_distinguishedTriangle_of_obj₃_isLE_pred
      T hT m hTensorCone
  refine ⟨E', ⟨a, b, hE'ge, hE'le⟩, hE'free, α', ?_, ?_⟩
  · intro i hi
    have hLeft :
        IsIso ((HB i).map comparison.inv) := by
      infer_instance
    have hRight :
        IsIso ((HB i).map ((derivedTensorWithAlgebra (algebraMap A B)).map α)) :=
      hα'iso_raw i hi
    -- Proof comment: transport the homology-window isomorphism across the comparison
    -- isomorphism on the left vertex.
    simpa [α', Functor.map_comp] using
      (show IsIso
        (((HB i).map comparison.inv) ≫
          ((HB i).map ((derivedTensorWithAlgebra (algebraMap A B)).map α))) by
            infer_instance)
  · have hLeft :
        IsIso ((HB m).map comparison.inv) := by
      infer_instance
    have hRight :
        Epi ((HB m).map ((derivedTensorWithAlgebra (algebraMap A B)).map α)) :=
      hα'epi_raw
    -- Proof comment: the same left-vertex comparison turns the epimorphism at degree `m` into
    -- the required epimorphism for the witness map from `Q.obj E'`.
    simpa [α', Functor.map_comp] using
      (show Epi
        (((HB m).map comparison.inv) ≫
          ((HB m).map ((derivedTensorWithAlgebra (algebraMap A B)).map α))) by
            infer_instance)

-- Proof sketch: rewrite pseudo-coherence as `m`-pseudo-coherence for all `m` using the canonical
-- owner theorem `isPseudoCoherent_iff_forall_isMPseudoCoherent`, then apply part `(1)` degreewise.
/-- Derived extension of scalars along `A → B` preserves pseudo-coherent objects of `D(A)`. -/
theorem derivedTensorWithAlgebra_isPseudoCoherent
    (K : DModA) (hK : K.IsPseudoCoherent) :
    (K ⊗[A]^L[B]).IsPseudoCoherent := by
  rw [pseudoCoherent_iff_forall_mPseudoCoherent] at hK ⊢
  intro m
  simpa using derivedTensorWithAlgebra_isMPseudoCoherent K m (hK m)

end

end CategoryTheory
