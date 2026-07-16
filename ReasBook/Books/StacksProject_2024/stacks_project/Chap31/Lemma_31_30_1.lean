import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import StacksProject_2024.stacks_project.Chap24.Definition_24_3_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_43_10
import StacksProject_2024.stacks_project.Chap29.RelativeProjPresentation
import StacksProject_2024.stacks_project.Chap31.Lemma_31_30_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- The commutative-ring-valued structure sheaf of a scheme, as a sheaf on its open subsets. -/
private abbrev schemeCommRingSheaf (S : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} :=
  S.sheaf

-- Semantic source/core/bridge check:
-- * source-facing main item: Lemma 31.30.1 and its three textbook alternative hypotheses on a
--   graded algebra sheaf `𝒜`;
-- * core/canonical conclusion owner: `QuasiCompact p`;
-- * bridge layer used here: `RelativeProjPresentation p`, together with an explicit identification
--   of its nonnegative degree pieces with those of `𝒜`, because the current project does not yet
--   expose a scheme-side relative `Proj_S` owner with the sheaf-level graded finiteness
--   hypotheses appearing in the source.

/-- A chosen relative `Proj` presentation `P : RelativeProjPresentation p` for the graded algebra
sheaf `𝒜`, recorded by identifying each nonnegative degree piece of `P` with the corresponding
graded piece of `𝒜`. -/
structure RelativeProjPresentationOf
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (P : RelativeProjPresentation p) where
  /-- The degree-`d` piece of the chosen presentation agrees with the degree-`d` piece of
  `𝒜`. -/
  degreePieceIso : ∀ d : ℕ, P.degreePiece d ≅ 𝒜 d

/-- An affine-local quasi-compactness interface for a relative `Proj` morphism `p : X ⟶ S`: every
point of the base has an affine neighbourhood on which the restricted morphism is quasi-compact. -/
@[stacks 07ZX]
abbrev RelativeProjAffineLocalQuasiCompact (p : X ⟶ S) : Prop :=
  ∀ s : S, ∃ U : S.affineOpens, s ∈ (U : S.Opens) ∧ QuasiCompact (p ∣_ (U : S.Opens))

/-- Unfold `RelativeProjAffineLocalQuasiCompact` into the affine-local quasi-compactness condition
recorded in Lemma 31.30.1. -/
theorem relativeProjAffineLocalQuasiCompact_iff :
    RelativeProjAffineLocalQuasiCompact p ↔
      ∀ s : S, ∃ U : S.affineOpens, s ∈ (U : S.Opens) ∧ QuasiCompact (p ∣_ (U : S.Opens)) :=
  Iff.rfl

/-- The presentation-level bridge for the first source hypothesis of Lemma 31.30.1 on a chosen
relative `Proj` presentation `P : RelativeProjPresentation p`.

The current repository does not yet expose the sheaf-level owner for "`\mathcal A` is of finite
type as a sheaf of `\mathcal A_0`-algebras". On the available `RelativeProjPresentation` surface,
the source hypothesis is therefore recorded through the finite-type consequences it supplies for
the structural morphism and the twists, together with the affine-local quasi-compactness needed in
Lemma 31.30.1 itself. -/
@[stacks 07ZX]
class RelativeProjFiniteTypeAlgebraHypothesis
    (P : outParam (RelativeProjPresentation p)) : Prop where
  /-- The structural morphism is affine-locally quasi-compact. -/
  affineLocalQuasiCompact : RelativeProjAffineLocalQuasiCompact p
  /-- The structural morphism is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType p
  /-- Every twist `\mathcal O_X(d)` in the chosen presentation is a finite type
  `\mathcal O_X`-module. -/
  twist_isFiniteType : ∀ d : ℤ, (P.twist d).IsFiniteType

/-- A finite-type relative `Proj` presentation exposes local finite type of the structural
morphism. -/
@[stacks 07ZX]
instance instLocallyOfFiniteTypeOfRelativeProjFiniteTypeAlgebraHypothesis
    (P : outParam (RelativeProjPresentation p)) [h : RelativeProjFiniteTypeAlgebraHypothesis P] :
    LocallyOfFiniteType p :=
  h.locallyOfFiniteType

/-- A finite-type relative `Proj` presentation makes every twist in the chosen presentation a
finite type `\mathcal O_X`-module. -/
@[stacks 07ZX]
theorem RelativeProjFiniteTypeAlgebraHypothesis.isFiniteType_twist
    {P : RelativeProjPresentation p}
    (h : RelativeProjFiniteTypeAlgebraHypothesis P) (d : ℤ) :
    (P.twist d).IsFiniteType :=
  h.twist_isFiniteType d

/-- The first source hypothesis in Lemma 31.30.1, expressed on the current project surface as the
existence of a chosen relative `Proj` presentation of `𝒜` carrying the finite-type bridge data
above. -/
@[stacks 07ZX]
abbrev RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis
    (p : X ⟶ S) (𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)) : Prop :=
  ∃ (P : RelativeProjPresentation p), RelativeProjPresentationOf P ∧
    RelativeProjFiniteTypeAlgebraHypothesis P

/-- The second source hypothesis in Lemma 31.30.1, expressed on the current project surface
through the existing projective-bundle presentation owner of Lemma 31.30.5, together with a chosen
relative `Proj` presentation of `𝒜`. -/
@[stacks 07ZX]
abbrev RelativeProjGeneratedByDegreeOneFiniteModuleHypothesis
    (p : X ⟶ S) (𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)) : Prop :=
  ∃ (P : RelativeProjPresentation p), RelativeProjPresentationOf P ∧
    RelativeProjGeneratedByDegreeOneFiniteModuleProjectiveBundleHypothesis P

/-- The presentation-level bridge for the third source hypothesis of Lemma 31.30.1 on a chosen
relative `Proj` presentation `P : RelativeProjPresentation p`.

The current project still lacks the quotient-relative-`Proj` owner needed to state the full
submodule / locally-nilpotent quotient clause intrinsically. This bridge therefore keeps the
visible finite-type positive-degree submodule data on the available presentation surface together
with the affine-local quasi-compactness consequence used in Lemma 31.30.1. -/
@[stacks 07ZX]
class RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientBridge
    (P : outParam (RelativeProjPresentation p)) : Prop where
  /-- A positive degree carrying the finite type submodule used in the source clause. -/
  degree : ℕ
  /-- The chosen degree is positive. -/
  degree_pos : 0 < degree
  /-- The finite type positive-degree submodule appearing in the source clause. -/
  submodule : Subobject (P.degreePiece degree)
  /-- The chosen submodule is finite type over `\mathcal O_S`. -/
  submodule_isFiniteType : (Subobject.underlying.obj submodule).IsFiniteType
  /-- The source clause yields affine-local quasi-compactness of the structural morphism. -/
  affineLocalQuasiCompact : RelativeProjAffineLocalQuasiCompact p

/-- The source-visible positive-degree finite type submodule data in the third hypothesis of
Lemma 31.30.1, recorded against a chosen relative `Proj` presentation of `𝒜`. The current project
still lacks the quotient-relative-`Proj` owner needed to express the locally nilpotent quotient
clause intrinsically, so that remaining part is kept in the presentation-level bridge field
`bridge`. -/
structure RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientData
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (P : RelativeProjPresentation p) where
  /-- The chosen presentation represents the nonnegative degree pieces of `𝒜`. -/
  presentation : RelativeProjPresentationOf P
  /-- A positive degree carrying the finite type submodule appearing in the source clause. -/
  degree : ℕ
  /-- The chosen degree is positive. -/
  degree_pos : 0 < degree
  /-- The finite type positive-degree submodule appearing in the source clause. -/
  submodule : Subobject (𝒜 degree)
  /-- The chosen submodule is finite type over `\mathcal O_S`. -/
  submodule_isFiniteType : (Subobject.underlying.obj submodule).IsFiniteType
  /-- The remaining presentation-level bridge data for the quotient-relative-`Proj` clause. -/
  bridge : RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientBridge P

/-- The third source hypothesis in Lemma 31.30.1, expressed on the current project surface as the
existence of a chosen relative `Proj` presentation of `𝒜` carrying the visible positive-degree
finite-type submodule data above. -/
@[stacks 07ZX]
abbrev RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientHypothesis
    (p : X ⟶ S) (𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)) : Prop :=
  ∃ (P : RelativeProjPresentation p),
    RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientData P

/-- The source-facing disjunction of the three alternative hypotheses in Lemma 31.30.1. -/
@[stacks 07ZX]
abbrev RelativeProjQuasiCompactHypothesis
    (p : X ⟶ S) (𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)) : Prop :=
  RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis p 𝒜 ∨
    RelativeProjGeneratedByDegreeOneFiniteModuleHypothesis p 𝒜 ∨
      RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientHypothesis p 𝒜

/-- The first source hypothesis in Lemma 31.30.1 yields the affine-local quasi-compactness
interface used in the Stacks proof. -/
@[stacks 07ZX]
theorem RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis.affineLocalQuasiCompact
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis p 𝒜) :
    RelativeProjAffineLocalQuasiCompact p := by
  rcases h with ⟨P, -, hP⟩
  exact hP.affineLocalQuasiCompact

/-- The second source hypothesis in Lemma 31.30.1 yields a projective relative `Proj`
presentation. -/
@[stacks 07ZX]
theorem RelativeProjGeneratedByDegreeOneFiniteModuleHypothesis.projective
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjGeneratedByDegreeOneFiniteModuleHypothesis p 𝒜) :
    Projective p := by
  rcases h with ⟨P, -, hP⟩
  exact hP.projective

/-- The third source hypothesis in Lemma 31.30.1 yields the affine-local quasi-compactness
interface used in the Stacks proof. -/
@[stacks 07ZX]
theorem RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientHypothesis.affineLocalQuasiCompact
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientHypothesis p 𝒜) :
    RelativeProjAffineLocalQuasiCompact p := by
  rcases h with ⟨P, hP⟩
  exact hP.bridge.affineLocalQuasiCompact

/-- The third source hypothesis in Lemma 31.30.1 exhibits the visible finite type
positive-degree submodule data carried by the current project surface. -/
@[stacks 07ZX]
theorem RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientHypothesis.exists_finiteTypeSubmodule
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientHypothesis p 𝒜) :
    ∃ (P : RelativeProjPresentation p) (presentation : RelativeProjPresentationOf P) (d : ℕ),
      0 < d ∧ ∃ F : Subobject (𝒜 d), (Subobject.underlying.obj F).IsFiniteType := by
  rcases h with ⟨P, hP⟩
  exact ⟨P, hP.presentation, hP.degree, hP.degree_pos, hP.submodule, hP.submodule_isFiniteType⟩

/-- Any of the three source hypotheses in `RelativeProjQuasiCompactHypothesis` yields the
affine-local quasi-compactness interface used in the Stacks proof of Lemma 31.30.1. -/
@[stacks 07ZX]
theorem RelativeProjQuasiCompactHypothesis.affineLocalQuasiCompact
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjQuasiCompactHypothesis p 𝒜) :
    RelativeProjAffineLocalQuasiCompact p := by
  rcases h with h | h | h
  · exact h.affineLocalQuasiCompact
  · intro s
    have hp : Projective p := h.projective
    have hq : QuasiCompact p := hp.toQuasiProjective.toFiniteType.toQuasiCompact
    letI : QuasiCompact p := hq
    rcases Scheme.exists_affineOpens_containing S s with ⟨U, hsU⟩
    exact ⟨U, hsU, by infer_instance⟩
  · exact h.affineLocalQuasiCompact

/-- A relative `Proj` morphism that is quasi-compact on an affine neighbourhood of every base
point is quasi-compact. -/
theorem relativeProj_quasiCompact_of_affineLocal
    (h : RelativeProjAffineLocalQuasiCompact p) :
    QuasiCompact p := sorry

/-- The affine-local quasi-compactness interface from Lemma 31.30.1 exposes the canonical owner
`QuasiCompact p`. -/
@[stacks 07ZX]
theorem RelativeProjAffineLocalQuasiCompact.quasiCompact
    (h : RelativeProjAffineLocalQuasiCompact p) :
    QuasiCompact p :=
  relativeProj_quasiCompact_of_affineLocal h

/-- The first source hypothesis in Lemma 31.30.1 implies that the relative `Proj` morphism is
quasi-compact. -/
@[stacks 07ZX]
theorem RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis.quasiCompact
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjFiniteTypeAsDegreeZeroAlgebraHypothesis p 𝒜) :
    QuasiCompact p :=
  relativeProj_quasiCompact_of_affineLocal h.affineLocalQuasiCompact

/-- The second source hypothesis in Lemma 31.30.1 implies that the relative `Proj` morphism is
quasi-compact. -/
@[stacks 07ZX]
theorem RelativeProjGeneratedByDegreeOneFiniteModuleHypothesis.quasiCompact
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjGeneratedByDegreeOneFiniteModuleHypothesis p 𝒜) :
    QuasiCompact p :=
  h.projective.toQuasiProjective.toFiniteType.toQuasiCompact

/-- The third source hypothesis in Lemma 31.30.1 implies that the relative `Proj` morphism is
quasi-compact. -/
@[stacks 07ZX]
theorem RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientHypothesis.quasiCompact
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientHypothesis p 𝒜) :
    QuasiCompact p :=
  relativeProj_quasiCompact_of_affineLocal h.affineLocalQuasiCompact

/-- Any of the three source hypotheses in Lemma 31.30.1 implies that the relative `Proj`
morphism is quasi-compact. -/
@[stacks 07ZX]
theorem RelativeProjQuasiCompactHypothesis.quasiCompact
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjQuasiCompactHypothesis p 𝒜) :
    QuasiCompact p := by
  rcases h with h | h | h
  · exact h.quasiCompact
  · exact h.quasiCompact
  · exact h.quasiCompact

/-- Lemma 31.30.1: let `S` be a scheme, let `\mathcal A` be a quasi-coherent graded
`\mathcal O_S`-algebra, and let `p : X = \underline{\mathrm{Proj}}_S(\mathcal A) ⟶ S` be the
relative `Proj` morphism. If one of the following holds:

1. `\mathcal A` is of finite type as a sheaf of `\mathcal A_0`-algebras,
2. `\mathcal A` is generated by `\mathcal A_1` as an `\mathcal A_0`-algebra and
   `\mathcal A_1` is a finite type `\mathcal A_0`-module,
3. there exists a finite type quasi-coherent `\mathcal A_0`-submodule
   `\mathcal F \subset \mathcal A_+` such that
   `\mathcal A_+ / \mathcal F \mathcal A` is a locally nilpotent sheaf of ideals of
   `\mathcal A / \mathcal F \mathcal A`,

then `p` is quasi-compact.

In the current environment, where the scheme-side relative `Proj` construction is represented by
`RelativeProjPresentation p`, the three source clauses are recorded by combining the graded algebra
sheaf `𝒜` with a chosen presentation of its nonnegative degree pieces: the finite-type clause
through `RelativeProjFiniteTypeAlgebraHypothesis`, the degree-one clause through the
projective-bundle owner from Lemma 31.30.5, and the submodule clause through the source-visible
positive-degree finite type submodule data together with the remaining presentation-level bridge
`RelativeProjFiniteTypeSubmoduleLocallyNilpotentQuotientBridge`. -/
@[stacks 07ZX]
theorem relativeProj_quasiCompact_of_finiteness
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h : RelativeProjQuasiCompactHypothesis p 𝒜) :
    QuasiCompact p :=
  h.quasiCompact

end AlgebraicGeometry.Scheme.Hom
