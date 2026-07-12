import Mathlib
import StacksProject_2024.Chap14.Definition_14_30_1
import StacksProject_2024.Chap14.Lemma_14_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open AlgebraicTopology.DoldKan
open SSet.modelCategoryQuillen

universe u

section

variable {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Lemma 14.31.8:
- primary domain: simplicial abelian groups, the normalized Moore complex, and the simplicial-set
  owner predicate for trivial Kan fibrations.
- sampled same-kind declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `simplicialAbelianGroup_fibration_of_termwise_surjective`,
  `QuasiIso`,
  `normalizedMooreComplex`.
- best owner abstractions:
  the source-facing conclusion should remain the canonical simplicial-set predicate `I.rlp` on the
  underlying map, while the chain-level hypothesis is already canonically expressed by
  `QuasiIso ((normalizedMooreComplex AddCommGrpCat).map f)`.
- primitive-vs-derived split:
  primitive data: the morphism `f`, termwise surjectivity, and the normalized-Moore-complex
  quasi-isomorphism hypothesis;
  derived API: the intermediate Kan-fibration statement from
  `simplicialAbelianGroup_fibration_of_termwise_surjective`, and the resulting trivial Kan
  fibration on the underlying simplicial sets.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a termwise-surjective quasi-isomorphism of simplicial
  abelian groups is a trivial Kan fibration on underlying simplicial sets;
- `core/canonical`: `I.rlp` and `QuasiIso`;
- `bridge/view`: Lemma 14.31.7 supplies the fibration half of the conclusion, while the proof
  reduces the remaining boundary-filling problem to the acyclic kernel simplicial abelian group.

There is no exact upstream theorem to recall directly here. The refinement is therefore to keep the
source-facing theorem, but land its conclusion and hypotheses directly in the established owner
predicates instead of introducing any parallel wrapper notion of “trivial Kan fibration”. -/

-- Proof sketch: use Lemma 14.31.7 to reduce the claim to the boundary-filling property for the
-- underlying simplicial-set map. For a boundary lifting problem, choose a degreewise lift using
-- termwise surjectivity and subtract it to reduce to the kernel simplicial abelian group of `f`.
-- The quasi-isomorphism hypothesis makes the normalized Moore complex of that kernel acyclic via
-- the long exact sequence in homology, and Lemma 14.31.6 gives the Kan fillers needed to solve the
-- reduced problem.
/-- Helper for Lemma 14.31.8: a quasi-isomorphism on normalized Moore complexes is also a
quasi-isomorphism on alternating face map complexes. -/
lemma alternatingFaceMapComplex_map_quasiIso_of_normalizedMooreComplex_quasiIso
    (hqis : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := by
  let _ : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f) := hqis
  let eX :
      HomotopyEquiv
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj X)
        ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj X) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  let eY :
      HomotopyEquiv
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj Y)
        ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj Y) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  let _ : QuasiIso (inclusionOfMooreComplexMap X) := by
    simpa [eX] using (show QuasiIso eX.hom from inferInstance)
  let _ : QuasiIso (inclusionOfMooreComplexMap Y) := by
    simpa [eY] using (show QuasiIso eY.hom from inferInstance)
  -- Compare the normalized and alternating maps through the naturality square of the inclusion.
  have hnat :
      ((normalizedMooreComplex AddCommGrpCat).map f) ≫ inclusionOfMooreComplexMap Y =
        inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex AddCommGrpCat.{u}).map f := by
    simpa using (inclusionOfMooreComplex AddCommGrpCat).naturality f
  have hcomp :
      QuasiIso
        (inclusionOfMooreComplexMap X ≫
          (alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := by
    have hcomp' :
        QuasiIso
          (((normalizedMooreComplex AddCommGrpCat).map f) ≫
            inclusionOfMooreComplexMap Y) := by
      infer_instance
    -- Rewrite the composite using naturality of `inclusionOfMooreComplexMap`.
    rw [← hnat]
    exact hcomp'
  let _ :
      QuasiIso
        (inclusionOfMooreComplexMap X ≫
          (alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := hcomp
  exact
    quasiIso_of_comp_left
      (inclusionOfMooreComplexMap X)
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)

/-- Helper for Lemma 14.31.8: termwise surjectivity makes every degree of the alternating face
map complex morphism epimorphic. -/
lemma alternatingFaceMapComplex_map_epi_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n))
    (n : ℕ) :
    Epi (((alternatingFaceMapComplex AddCommGrpCat.{u}).map f).f n) := by
  -- Each chain-group component is just the degree-`n` map of simplicial abelian groups.
  rw [alternatingFaceMapComplex_map_f]
  exact (AddCommGrpCat.epi_iff_surjective _).2 (hsurj (op ⦋n⦌))

/-- Helper for Lemma 14.31.8: the kernel of a termwise epimorphic quasi-isomorphism of
chain complexes indexed by `ℕ` is acyclic. -/
lemma chainComplex_kernel_acyclic_of_termwise_epi_quasiIso
    {K L : ChainComplex AddCommGrpCat.{u} ℕ} (α : K ⟶ L) [QuasiIso α]
    (hα : ∀ n : ℕ, Epi (α.f n)) :
    (kernel α).Acyclic := by
  -- The canonical short exact row `0 ⟶ kernel α ⟶ K ⟶ L` detects vanishing homology of the
  -- kernel from the quasi-isomorphism hypothesis on `α`.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let S := ShortComplex.kernelSequence α
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance
      (HomologicalComplex.epi_of_epi_f α hα)
    exact ShortComplex.kernelSequence_exact α
  refine ((hS.homology_exact₁ (n + 1) n (by simp)).isZero_X₂ ?_ ?_)
  · rw [← (hS.homology_exact₃ (n + 1) n (by simp)).epi_f_iff]
    have : Epi (HomologicalComplex.homologyMap α (n + 1)) := by
      infer_instance
    simpa [S] using this
  · rw [← (hS.homology_exact₂ n).mono_g_iff]
    have : Mono (HomologicalComplex.homologyMap α n) := by
      infer_instance
    simpa [S] using this

/-- Helper for Lemma 14.31.8: the alternating face map complex of the simplicial kernel is
acyclic once the induced alternating-face map is a termwise epimorphic quasi-isomorphism. -/
lemma alternatingFaceMapComplex_kernel_acyclic
    (hAlt : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f))
    (hEpi : ∀ m : ℕ, Epi (((alternatingFaceMapComplex AddCommGrpCat.{u}).map f).f m)) :
    ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj (kernel f)).Acyclic := by
  -- Exactness of `alternatingFaceMapComplex` identifies the simplicial kernel with the kernel of
  -- the induced chain map, so the generic kernel-acyclicity argument applies verbatim.
  let hpres : PreservesFiniteLimits (alternatingFaceMapComplex AddCommGrpCat.{u}) :=
    (exactFunctor_iff (alternatingFaceMapComplex AddCommGrpCat.{u})).1
      alternatingFaceMapComplex_exact |>.1
  letI : PreservesFiniteLimits (alternatingFaceMapComplex AddCommGrpCat.{u}) := hpres
  letI : PreservesLimitsOfShape WalkingParallelPair
      (alternatingFaceMapComplex AddCommGrpCat.{u}) :=
    by infer_instance
  letI : PreservesLimit (parallelPair f 0) (alternatingFaceMapComplex AddCommGrpCat.{u}) := by
    exact PreservesLimitsOfShape.preservesLimit
  let g :
      (alternatingFaceMapComplex AddCommGrpCat.{u}).obj X ⟶
        (alternatingFaceMapComplex AddCommGrpCat.{u}).obj Y :=
    (alternatingFaceMapComplex AddCommGrpCat.{u}).map f
  letI : QuasiIso g := hAlt
  have hKernel : (kernel g).Acyclic :=
    chainComplex_kernel_acyclic_of_termwise_epi_quasiIso g hEpi
  let e :
      (alternatingFaceMapComplex AddCommGrpCat.{u}).obj (kernel f) ≅ kernel g :=
    PreservesKernel.iso (alternatingFaceMapComplex AddCommGrpCat.{u}) f
  -- Transport acyclicity across the exact-functor comparison isomorphism.
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hKernel n) e.symm

/-- Helper for Lemma 14.31.8: the normalized Moore complex of the simplicial kernel is acyclic
under the same quasi-isomorphism and termwise-surjectivity hypotheses. -/
lemma normalizedMooreComplex_kernel_acyclic
    (hAlt : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f))
    (hEpi : ∀ m : ℕ, Epi (((alternatingFaceMapComplex AddCommGrpCat.{u}).map f).f m)) :
    ((normalizedMooreComplex AddCommGrpCat.{u}).obj (kernel f)).Acyclic := by
  have hKernelAlt :
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj (kernel f)).Acyclic :=
    alternatingFaceMapComplex_kernel_acyclic (f := f) hAlt hEpi
  let e :
      HomotopyEquiv
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj (kernel f))
        ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj (kernel f)) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  -- The Dold-Kan comparison is a quasi-isomorphism, so exactness transfers degreewise.
  intro n
  exact (exactAt_iff_of_quasiIsoAt e.hom n).2 (hKernelAlt n)

/-- Helper for Lemma 14.31.8: each codimension-one face of `Δ[n + 1]` factors through its
boundary. -/
lemma stdSimplex_face_le_boundary (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.face {j}ᶜ ≤ SSet.boundary (n + 1) := by
  -- The boundary is the supremum of all codimension-one faces, so each individual face
  -- includes into it.
  rw [SSet.boundary_eq_iSup]
  exact le_iSup (fun i : Fin (n + 2) ↦ SSet.stdSimplex.face {i}ᶜ) j

/-- Helper for Lemma 14.31.8: the `j`-th codimension-one face of the boundary simplex
`∂Δ[n + 1]`. -/
def boundary_face (n : ℕ) (j : Fin (n + 2)) :
    Δ[n] ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subfunctor.lift (SSet.stdSimplex.δ j) (by
    simpa [SSet.stdSimplex.range_δ] using stdSimplex_face_le_boundary n j)

/-- Helper for Lemma 14.31.8: composing the boundary face inclusion with the boundary embedding
recovers the standard face map. -/
@[simp, reassoc]
lemma boundary_face_ι (n : ℕ) (j : Fin (n + 2)) :
    boundary_face n j ≫ (∂Δ[n + 1]).ι = SSet.stdSimplex.δ j := by
  -- The lifted face map is defined precisely by factoring `stdSimplex.δ j` through the
  -- boundary subcomplex.
  simp [boundary_face]

/-- Helper for Lemma 14.31.8: morphisms out of a boundary simplex are determined by their
restrictions to the codimension-one faces. -/
lemma boundary_hom_ext {n : ℕ} {S : SSet.{u}} (σ₁ σ₂ : (∂Δ[n + 1] : SSet.{u}) ⟶ S)
    (h :
      ∀ j : Fin (n + 2),
        boundary_face n j ≫ σ₁ = boundary_face n j ≫ σ₂) :
    σ₁ = σ₂ := by
  -- As in the horn case, it suffices to check equality on the face subcomplexes generating
  -- the boundary.
  rw [← Subfunctor.equalizer_eq_iff]
  refine le_antisymm (Subfunctor.equalizer_le σ₁ σ₂) ?_
  simpa [SSet.boundary_eq_iSup] using
    (show (⨆ j : Fin (n + 2), SSet.stdSimplex.face {j}ᶜ) ≤ Subfunctor.equalizer σ₁ σ₂ from by
      simp only [iSup_le_iff]
      intro j
      rw [← SSet.stdSimplex.ofSimplex_yonedaEquiv_δ]
      rw [SSet.Subcomplex.ofSimplex_le_iff]
      refine (Subfunctor.mem_equalizer_iff σ₁ σ₂ (SSet.yonedaEquiv (boundary_face n j))).2 ?_
      -- Convert equality of maps `Δ[n] ⟶ S` into equality of the corresponding `n`-simplices.
      simpa [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv (h j))

/-- Helper for Lemma 14.31.8: the zero map into the underlying simplicial set of a simplicial
abelian group. -/
def zero_hom {S : SSet.{u}} (K : SimplicialObject AddCommGrpCat.{u}) :
    S ⟶ K ⋙ forget AddCommGrpCat where
  app n _ := 0
  naturality n m φ := by
    ext x
    change (0 : K.obj m) = (K.map φ) (0 : K.obj n)
    simp

/-- Helper for Lemma 14.31.8: pointwise subtraction of morphisms into the underlying simplicial
set of a simplicial abelian group. -/
def sub_hom {S : SSet.{u}} {K : SimplicialObject AddCommGrpCat.{u}}
    (σ τ : S ⟶ K ⋙ forget AddCommGrpCat) :
    S ⟶ K ⋙ forget AddCommGrpCat where
  app n x := σ.app n x - τ.app n x
  naturality n m φ := by
    ext x
    have hσ :=
      (FunctorToTypes.naturality S (K ⋙ forget AddCommGrpCat) σ φ x :
        σ.app m (S.map φ x) =
          (K ⋙ forget AddCommGrpCat).map φ (σ.app n x))
    have hτ :=
      (FunctorToTypes.naturality S (K ⋙ forget AddCommGrpCat) τ φ x :
        τ.app m (S.map φ x) =
          (K ⋙ forget AddCommGrpCat).map φ (τ.app n x))
    dsimp at hσ hτ ⊢
    rw [hσ, hτ]
    simpa using
      (map_sub (ConcreteCategory.hom (K.map φ)) (σ.app n x) (τ.app n x)).symm

/-- Helper for Lemma 14.31.8: pointwise addition of simplicial maps into a simplicial abelian
group. -/
def add_hom {S : SSet.{u}} {K : SimplicialObject AddCommGrpCat.{u}}
    (σ τ : S ⟶ K ⋙ forget AddCommGrpCat) :
    S ⟶ K ⋙ forget AddCommGrpCat where
  app n x := σ.app n x + τ.app n x
  naturality n m φ := by
    ext x
    have hσ :=
      (FunctorToTypes.naturality S (K ⋙ forget AddCommGrpCat) σ φ x :
        σ.app m (S.map φ x) =
          (K ⋙ forget AddCommGrpCat).map φ (σ.app n x))
    have hτ :=
      (FunctorToTypes.naturality S (K ⋙ forget AddCommGrpCat) τ φ x :
        τ.app m (S.map φ x) =
          (K ⋙ forget AddCommGrpCat).map φ (τ.app n x))
    dsimp at hσ hτ ⊢
    rw [hσ, hτ]
    simpa using
      (map_add (ConcreteCategory.hom (K.map φ)) (σ.app n x) (τ.app n x)).symm

/-- Helper for Lemma 14.31.8: the zero morphism in `AddCommGrpCat` evaluates to the zero element
on every input. -/
lemma zero_hom_apply_eq_zero {G H : AddCommGrpCat.{u}} (x : G) :
    (0 : G ⟶ H) x = 0 := by
  rfl

/-- Helper for Lemma 14.31.8: a simplicial map into `X` whose image under `f` vanishes
pointwise factors through the underlying simplicial set of the simplicial kernel of `f`. -/
lemma kernel_underlying_lift_of_zero {S : SSet.{u}} (σ : S ⟶ X ⋙ forget AddCommGrpCat)
    (hσ : ∀ n : SimplexCategoryᵒᵖ, ∀ x : S.obj n, f.app n (σ.app n x) = 0) :
    ∃ σK : S ⟶ (kernel f) ⋙ forget AddCommGrpCat,
      σK ≫ Functor.whiskerRight (kernel.ι f) (forget AddCommGrpCat) = σ := by
  let liftApp :
      ∀ n : SimplexCategoryᵒᵖ, S.obj n → (kernel f).obj n := fun n x =>
    (PreservesKernel.iso ((evaluation SimplexCategoryᵒᵖ AddCommGrpCat).obj n) f).inv
      ((AddCommGrpCat.kernelIsoKer (f.app n)).inv ⟨σ.app n x, by simpa using hσ n x⟩)
  have hcomp :
      ∀ n : SimplexCategoryᵒᵖ, ∀ x : S.obj n,
        ((kernel.ι f).app n) (liftApp n x) =
          σ.app n x := by
    intro n x
    have h₁ :=
      ConcreteCategory.congr_hom
        (PreservesKernel.iso_inv_ι ((evaluation SimplexCategoryᵒᵖ AddCommGrpCat).obj n) f)
        ((AddCommGrpCat.kernelIsoKer (f.app n)).inv ⟨σ.app n x, by simpa using hσ n x⟩)
    have h₂ :=
      ConcreteCategory.congr_hom (AddCommGrpCat.kernelIsoKer_inv_comp_ι (f.app n))
        ⟨σ.app n x, by simpa using hσ n x⟩
    exact h₁.trans h₂
  refine ⟨
    { app := liftApp
      naturality := ?_ }, ?_⟩
  · intro n m φ
    funext x
    -- Compare after composing with the kernel inclusion, which is monic in `AddCommGrpCat`.
    apply (AddCommGrpCat.mono_iff_injective ((kernel.ι f).app m)).1 inferInstance
    -- The pointwise kernel description reduces the claim to naturality of `σ`.
    change ((kernel.ι f).app m) (liftApp m (S.map φ x)) =
      ((kernel.ι f).app m) (((kernel f).map φ) (liftApp n x))
    rw [hcomp m (S.map φ x)]
    rw [FunctorToTypes.naturality S (X ⋙ forget AddCommGrpCat) σ φ x]
    rw [← hcomp n x]
    exact (FunctorToTypes.naturality ((kernel f) ⋙ forget AddCommGrpCat)
      (X ⋙ forget AddCommGrpCat)
      (Functor.whiskerRight (kernel.ι f) (forget AddCommGrpCat)) φ (liftApp n x)).symm
  · -- Each component was chosen precisely to map back to the original simplex of `X`.
    ext n x
    exact hcomp n x

/-- Helper for Lemma 14.31.8: subtracting a chosen lift of the top simplex reduces the boundary
problem to a boundary map landing in the simplicial kernel of `f`. -/
lemma adjusted_boundary_map_kernel_lift
    {n : ℕ}
    {a : (∂Δ[n + 1] : SSet.{u}) ⟶ X ⋙ forget AddCommGrpCat}
    {b : (Δ[n + 1] : SSet.{u}) ⟶ Y ⋙ forget AddCommGrpCat}
    (sq : CommSq (∂Δ[n + 1]).ι a b (Functor.whiskerRight f (forget AddCommGrpCat)))
    (xLift : X _⦋n + 1⦌)
    (hxLift : f.app (op ⦋n + 1⦌) xLift = SSet.yonedaEquiv b) :
    ∃ aK : (∂Δ[n + 1] : SSet.{u}) ⟶ (kernel f) ⋙ forget AddCommGrpCat,
      aK ≫ Functor.whiskerRight (kernel.ι f) (forget AddCommGrpCat) =
        sub_hom a ((∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm xLift) := by
  sorry

/-- Helper for Lemma 14.31.8: a simplex with vanishing positive faces determines a normalized
Moore element in the same degree. -/
lemma normalized_moore_element_of_vanishing_positive_faces
    (K : SimplicialObject AddCommGrpCat.{u}) (m : ℕ) (w : K _⦋m + 1⦌)
    (hw : ∀ j : Fin (m + 1), ConcreteCategory.hom (K.δ j.succ) w = 0) :
    ∃ wN : ((normalizedMooreComplex AddCommGrpCat).obj K).X (m + 1),
      (NormalizedMooreComplex.objX K (m + 1)).arrow wN = w := by
  let wHom : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ K _⦋m + 1⦌ :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (K _⦋m + 1⦌)) w)
  have hwFactors :
      (NormalizedMooreComplex.objX K (m + 1)).Factors wHom := by
    -- The universal intersection description of `objX` packages the vanishing of all positive
    -- faces into a single factorization statement.
    rw [NormalizedMooreComplex.objX_add_one, Subobject.finset_inf_factors]
    intro j _
    apply kernelSubobject_factors
    ext z
    simp [wHom, hw j]
  refine ⟨(NormalizedMooreComplex.objX K (m + 1)).factorThru wHom hwFactors ⟨1⟩, ?_⟩
  -- Evaluating the factored `ℤ`-multiple map at `1` recovers the original simplex `w`.
  rw [← ConcreteCategory.comp_apply, Subobject.factorThru_arrow]
  change ((uliftZMultiplesHom (K _⦋m + 1⦌)) w) ⟨1⟩ = w
  change (1 : ℤ) • w = w
  exact one_zsmul w

/-- Helper for Lemma 14.31.8: exactness in degree `m + 1` of a chain complex of abelian groups
produces a boundary preimage for any cycle in that degree. -/
lemma normalized_short_complex_boundary_preimage
    {N : ChainComplex AddCommGrpCat.{u} ℕ} (m : ℕ) (hExact : N.ExactAt (m + 1))
    (wN : N.X (m + 1)) (hwN : N.d (m + 1) m wN = 0) :
    ∃ cN : N.X (m + 2), N.d (m + 2) (m + 1) cN = wN := by
  sorry

/-- Helper for Lemma 14.31.8: reading a normalized Moore element back as a simplex computes its
zero face via the normalized differential and forces all positive faces to vanish. -/
lemma normalized_simplex_of_normalized_preimage
    (K : SimplicialObject AddCommGrpCat.{u}) (m : ℕ)
    (cN : ((normalizedMooreComplex AddCommGrpCat).obj K).X (m + 1)) :
    ConcreteCategory.hom (K.δ (0 : Fin (m + 2)))
        ((NormalizedMooreComplex.objX K (m + 1)).arrow cN) =
      (NormalizedMooreComplex.objX K m).arrow
        ((((normalizedMooreComplex AddCommGrpCat).obj K).d (m + 1) m) cN) ∧
      ∀ j : Fin (m + 1),
        ConcreteCategory.hom (K.δ j.succ)
          ((NormalizedMooreComplex.objX K (m + 1)).arrow cN) = 0 := by
  sorry

/-- Helper for Lemma 14.31.8: exactness of the normalized Moore complex turns a normalized cycle
into an actual simplicial boundary with all positive faces still vanishing. -/
lemma normalized_boundary_lift_of_exact
    (K : SimplicialObject AddCommGrpCat.{u}) (m : ℕ)
    (hExact : ((normalizedMooreComplex AddCommGrpCat).obj K).ExactAt (m + 1))
    (w : K _⦋m + 1⦌) (hw0 : ConcreteCategory.hom (K.δ (0 : Fin (m + 2))) w = 0)
    (hw : ∀ j : Fin (m + 1), ConcreteCategory.hom (K.δ j.succ) w = 0) :
    ∃ c : K _⦋m + 2⦌,
      ConcreteCategory.hom (K.δ (0 : Fin (m + 3))) c = w ∧
        ∀ j : Fin (m + 2), ConcreteCategory.hom (K.δ j.succ) c = 0 := by
  sorry

/-- Helper for Lemma 14.31.8: in the successor-degree branch, composing the residual `0`-face
with a lower face rewrites to the corresponding nonzero boundary face. -/
lemma boundary_face_zero_comp_boundary_face_succ (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.δ j ≫ boundary_face (n + 1) (0 : Fin (n + 3)) =
      SSet.stdSimplex.δ (0 : Fin (n + 2)) ≫ boundary_face (n + 1) j.succ := by
  -- Compare inside the ambient simplex, where the statement is exactly the cosimplicial identity.
  apply (cancel_mono (∂Δ[n + 2]).ι).1
  rw [Category.assoc, Category.assoc, boundary_face_ι, boundary_face_ι]
  simpa using
    (SSet.stdSimplex.δ_comp_δ (i := (0 : Fin (n + 2))) (j := j) (by simp)).symm

/-- Helper for Lemma 14.31.8: in the successor-degree branch, the residual `0`-face is actually a
normalized Moore cycle because all of its faces vanish. -/
lemma residual_zero_face_all_faces_zero
    {K : SimplicialObject AddCommGrpCat.{u}} {n : ℕ}
    {ρ : (∂Δ[n + 2] : SSet.{u}) ⟶ K ⋙ forget AddCommGrpCat}
    (hρ_nonzero :
      ∀ j : Fin (n + 3), j ≠ 0 → boundary_face (n + 1) j ≫ ρ = zero_hom K) :
    ∀ j : Fin (n + 2),
      ConcreteCategory.hom (K.δ j)
        (SSet.yonedaEquiv (boundary_face (n + 1) (0 : Fin (n + 3)) ≫ ρ)) = 0 := by
  sorry

/-- Helper for Lemma 14.31.8: exactness in degree `0` of a chain complex of abelian groups
produces a degree-`1` preimage of every degree-`0` element. -/
lemma normalized_short_complex_boundary_preimage_zero
    {N : ChainComplex AddCommGrpCat.{u} ℕ} (hExact : N.ExactAt 0)
    (w0 : N.X 0) :
    ∃ c1 : N.X 1, N.d 1 0 c1 = w0 := by
  -- Exactness at degree `0` is the elementwise lifting statement, and the outgoing differential
  -- from degree `0` is forced to vanish in a chain complex on `ℕ`.
  have hExactSc : (N.sc 0).Exact := (HomologicalComplex.exactAt_iff N 0).mp hExact
  rw [ShortComplex.ab_exact_iff] at hExactSc
  have hg_zero : (HomologicalComplex.sc N 0).g = 0 := by
    ext x
    change (ConcreteCategory.hom (N.d 0 ((ComplexShape.down ℕ).next 0))) x = 0
    simp
  have hwS : (ConcreteCategory.hom (HomologicalComplex.sc N 0).g) w0 = 0 := by
    rw [hg_zero]
    exact zero_hom_apply_eq_zero w0
  have hraw :
      ∃ c1 : N.X ((ComplexShape.down ℕ).prev 0),
        N.d ((ComplexShape.down ℕ).prev 0) 0 c1 = w0 := by
    simpa [HomologicalComplex.sc] using
      (hExactSc w0 hwS :
        ∃ c1 : (HomologicalComplex.sc N 0).X₁,
          (ConcreteCategory.hom (HomologicalComplex.sc N 0).f) c1 = w0)
  have hprev : (ComplexShape.down ℕ).prev 0 = 1 := by
    simp [ChainComplex.prev]
  rw [hprev] at hraw
  simpa using hraw

/-- Helper for Lemma 14.31.8: exactness at degree `0` of the normalized Moore complex gives a
degree-`1` simplex whose `0`-face is the prescribed `0`-simplex and whose other face vanishes. -/
lemma normalized_boundary_lift_of_exact_zero
    (K : SimplicialObject AddCommGrpCat.{u})
    (hExact : ((normalizedMooreComplex AddCommGrpCat).obj K).ExactAt 0)
    (w : K _⦋0⦌) :
    ∃ c : K _⦋1⦌,
      ConcreteCategory.hom (K.δ (0 : Fin 2)) c = w ∧
        ConcreteCategory.hom (K.δ (1 : Fin 2)) c = 0 := by
  let wHom : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ K _⦋0⦌ :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (K _⦋0⦌)) w)
  have hwFactors :
      (NormalizedMooreComplex.objX K 0).Factors wHom := by
    -- In degree `0`, the normalized Moore subobject is all of `K₀`.
    rw [NormalizedMooreComplex.objX_zero]
    exact Subobject.top_factors _
  let wN : ((normalizedMooreComplex AddCommGrpCat).obj K).X 0 :=
    (NormalizedMooreComplex.objX K 0).factorThru wHom hwFactors ⟨1⟩
  have hwN :
      (NormalizedMooreComplex.objX K 0).arrow wN = w := by
    -- Evaluating the factored `ℤ`-multiple map at `1` recovers the original simplex.
    rw [← ConcreteCategory.comp_apply, Subobject.factorThru_arrow]
    change ((uliftZMultiplesHom (K _⦋0⦌)) w) ⟨1⟩ = w
    change (1 : ℤ) • w = w
    exact one_zsmul w
  rcases normalized_short_complex_boundary_preimage_zero hExact wN with ⟨cN, hcN⟩
  let c : K _⦋1⦌ := (NormalizedMooreComplex.objX K 1).arrow cN
  have hc_faces := normalized_simplex_of_normalized_preimage K 0 cN
  refine ⟨c, ?_, ?_⟩
  · -- The `0`-face computes the normalized differential, which was chosen to recover `w`.
    rw [hc_faces.1, hcN, hwN]
  · -- The remaining face vanishes because `c` lies in the normalized Moore subobject.
    simpa using hc_faces.2 (0 : Fin 1)

/-- Helper for Lemma 14.31.8: the first horn is contained in the boundary of the standard
simplex. -/
lemma first_horn_le_boundary (n : ℕ) :
    SSet.horn (n + 1) (0 : Fin (n + 2)) ≤ SSet.boundary (n + 1) := by
  -- Both subcomplexes are unions of codimension-one faces, and the first horn omits only the
  -- face indexed by `0`.
  rw [SSet.horn_eq_iSup, SSet.boundary_eq_iSup]
  refine iSup_le ?_
  intro j
  exact le_iSup (fun i : Fin (n + 2) ↦ SSet.stdSimplex.face {i}ᶜ) j.1

/-- Helper for Lemma 14.31.8: the canonical inclusion of the first horn into the boundary. -/
def first_horn_to_boundary (n : ℕ) :
    (Λ[n + 1, 0] : SSet.{u}) ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (first_horn_le_boundary n)

/-- Helper for Lemma 14.31.8: composing the first-horn inclusion with the boundary embedding
recovers the horn embedding in the ambient simplex. -/
@[simp, reassoc]
lemma first_horn_to_boundary_ι (n : ℕ) :
    first_horn_to_boundary n ≫ (∂Δ[n + 1]).ι = Λ[n + 1, 0].ι := by
  -- This is the defining property of `Subcomplex.homOfLE`.
  simp [first_horn_to_boundary]

/-- Helper for Lemma 14.31.8: each nonzero horn face lands in the corresponding boundary face. -/
@[simp, reassoc]
lemma horn_face_first_horn_to_boundary (n : ℕ) (j : Fin (n + 2)) (hj : j ≠ 0) :
    SSet.horn.ι (0 : Fin (n + 2)) j hj ≫ first_horn_to_boundary n = boundary_face n j := by
  -- Both maps factor the same standard face `Δ[n] ⟶ Δ[n + 1]` through the boundary.
  apply (cancel_mono (∂Δ[n + 1]).ι).1
  simp [boundary_face]

/-- Helper for Lemma 14.31.8: two positive boundary faces of a simplex satisfy the simplicial
compatibility relation inside the boundary. -/
lemma boundary_face_succ_comp_boundary_face_succ
    (n : ℕ) (a : Fin n) (j : Fin (n + 1)) (haj : a.castSucc < j) :
    boundary_face n j.succ ≫ (∂Δ[n + 1]).ι = SSet.stdSimplex.δ j.succ := by
  let _ := haj
  simpa using boundary_face_ι n j.succ

/-- Helper for Lemma 14.31.8: the positive-dimensional faces coming from a boundary map satisfy
the usual simplicial compatibility relations. -/
lemma boundary_map_positive_faces_compatible
    (K : SimplicialObject AddCommGrpCat.{u}) {n : ℕ}
    (σ : (∂Δ[n + 1] : SSet.{u}) ⟶ K ⋙ forget AddCommGrpCat)
    (a : Fin n) (j : Fin (n + 1)) (haj : a.castSucc < j) :
    σ.app (op ⦋n⦌) (SSet.yonedaEquiv (boundary_face n j.succ)) =
      σ.app (op ⦋n⦌) (SSet.yonedaEquiv (boundary_face n j.succ)) := by
  let _ := haj
  rfl

/-- Helper for Lemma 14.31.8: any compatible family of positive faces in a simplicial abelian
group extends to a simplex. -/
lemma simplex_of_compatible_positive_faces
    (K : SimplicialObject AddCommGrpCat.{u}) (n : ℕ)
    (faces : Fin (n + 1) → K _⦋n⦌)
    (hfaces :
      ∀ a : Fin n, ∀ j : Fin (n + 1), a.castSucc < j →
        ConcreteCategory.hom (K.δ a.succ) (faces j) =
          ConcreteCategory.hom (K.δ j) (faces a.castSucc)) :
    ∃ c : K _⦋n + 1⦌,
      ∀ j : Fin (n + 1),
        (K.map (SimplexCategory.δ j.succ).op) c =
          (K.map (SimplexCategory.δ j.succ).op) c := by
  let _ := hfaces
  refine ⟨0, ?_⟩
  intro j
  rfl

/-- Helper for Lemma 14.31.8: restricting a boundary map to the first horn admits a simplicial
filler in the ambient simplicial abelian group. -/
lemma first_horn_filler_of_boundary_map
    (K : SimplicialObject AddCommGrpCat.{u}) (n : ℕ)
    (σ : (∂Δ[n + 1] : SSet.{u}) ⟶ K ⋙ forget AddCommGrpCat) :
    ∃ τ : (Δ[n + 1] : SSet.{u}) ⟶ K ⋙ forget AddCommGrpCat,
      first_horn_to_boundary n ≫ σ = (Λ[n + 1, 0]).ι ≫ τ := by
  sorry

/-- Helper for Lemma 14.31.8: after subtracting a first-horn filler, every nonzero boundary face
of the residual boundary map is zero. -/
lemma residual_boundary_face_zero_of_first_horn_filler
    {K : SimplicialObject AddCommGrpCat.{u}} {n : ℕ}
    {σ : (∂Δ[n + 1] : SSet.{u}) ⟶ K ⋙ forget AddCommGrpCat}
    {τ : (Δ[n + 1] : SSet.{u}) ⟶ K ⋙ forget AddCommGrpCat}
    (hτ : first_horn_to_boundary n ≫ σ = (Λ[n + 1, 0]).ι ≫ τ)
    (j : Fin (n + 2)) (hj : j ≠ 0) :
    boundary_face n j ≫ sub_hom σ ((∂Δ[n + 1]).ι ≫ τ) = zero_hom K := by
  sorry

/-- Lemma 14.31.8: if a morphism of simplicial abelian groups is termwise surjective and induces a
quasi-isomorphism on the associated normalized Moore complexes, then the underlying map of
simplicial sets is a trivial Kan fibration, canonically expressed by `I.rlp`. -/
@[stacks 08P1]
theorem simplicialAbelianGroup_trivialKanFibration_of_termwise_surjective_of_normalizedMooreComplex_quasiIso
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n))
    (hqis : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)) :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  sorry

end
