import Mathlib
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_9_1 (from Chap20) -/
open CategoryTheory TopologicalSpace TopCat

noncomputable section

universe u uι

section

variable {X : TopCat.{u}} {ι : Type uι}
variable (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u uι}) (i : ℕ)

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for Definition 20.9.1:
- primary domain: Čech complexes and Čech cohomology of abelian presheaves on indexed families of
  opens of a topological space;
- sampled owner API:
  `FormalCoproduct.cochainComplexFunctor`,
  `AlgebraicTopology.alternatingCofaceMapComplex`,
  `cechComplexFunctor`,
  `HomologicalComplex.homologyFunctor`,
  `indexedOpenCoverCechCohomology`;
- `source-facing`: the Čech complex and its degree-`i` cohomology for a family `U : ι → Opens X`;
- `core/canonical`: `cechComplexFunctor U`;
- `bridge/view`: the opens-specific finite-product witness `opensHasFiniteProducts X`, factored out
  to the local Chapter 20 Čech prelude instead of being redefined here.

Primitive data are only the family `U` and the additive presheaf `F`. The finite intersections,
restriction maps, differential, and resulting cochain complex are derived by the owner
`cechComplexFunctor U`, and degree-`i` Čech cohomology is then derived by
`HomologicalComplex.homologyFunctor`. This file should therefore recall the canonical owner
directly, rather than reintroducing a parallel tuplewise/intersectionwise implementation.
-/

/- Core/canonical owner: the Čech complex attached to a family in a category with finite products
is `cechComplexFunctor`. -/
recall cechComplexFunctor

/- Definition 20.9.1: for an abelian presheaf `F` on a topological space `X` and an indexed
family of opens `U`, the Čech complex is the specialization `((cechComplexFunctor U).obj F :
CochainComplex AddCommGrpCat ℕ)`. -/
#check ((cechComplexFunctor U).obj F : CochainComplex AddCommGrpCat ℕ)

/- Companion check: the degree-`i` Čech cohomology group is the degree-`i` homology object of the
canonical Čech complex above. -/
#check ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
  ((cechComplexFunctor U).obj F) : AddCommGrpCat)

end

/-! ### Lemma_20_9_2 (from Chap20) -/
open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u v

variable {X : TopCat.{u}} (ℱ : X.Presheaf AddCommGrpCat.{max u v})

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for degree-zero Čech comparison on abelian presheaves:
- primary domain: degree-zero Čech cohomology and the unique-gluing formulation of the sheaf
  condition for `TopCat.Presheaf`;
- sampled owner declarations:
  `opensHasFiniteProducts`,
  `CategoryTheory.cechComplexFunctor`,
  `HomologicalComplex.homologyFunctor`,
  `CochainComplex.isoHomologyπ₀`,
  `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`;
- best owner abstraction: the canonical degree-zero Čech cohomology object
  `((cechComplexFunctor U).obj ℱ).homology 0`;
- primitive data: the family `U` of opens and the additive presheaf `ℱ`;
- derived API: the Čech augmentation into degree `0`, its induced map to `H^0`, and the
  unique-gluing bridge expressed through `TopCat.Presheaf.IsCompatible` and
  `TopCat.Presheaf.IsGluing`.

Source/core/bridge triage:
- source-facing: the degree-zero Čech comparison map and the textbook bijectivity criterion in
  Lemma 20.9.2;
- core/canonical: the owner `((cechComplexFunctor U).obj ℱ).homology 0`;
- bridge/view: the restriction map into compatible families and its comparison with the canonical
  degree-zero Čech cohomology object.
-/

-- Proof sketch: both composites from `iSup U` to `U i ⊓ U j` factor through the same restriction
-- map, so the restricted family coming from a global section is compatible.
/-- Global sections restrict to a compatible family on any open covering. -/
theorem abelianPresheaf_restriction_isCompatible {ι : Type v} (U : ι → Opens X)
    (s : ℱ.obj (op (iSup U))) :
    IsCompatible ℱ U (fun i ↦ ℱ.map (Opens.leSupr U i).op s) := sorry

/-- The canonical map from sections on `iSup U` to degree-zero Čech cohomology of the covering
`U`, viewed as the degree-`0` homology of the canonical Čech complex. -/
abbrev abelianPresheafToCechH0 {ι : Type v} (U : ι → Opens X) :
    ℱ.obj (op (iSup U)) ⟶ ((cechComplexFunctor U).obj ℱ).homology 0 :=
  let K := (cechComplexFunctor U).obj ℱ
  K.liftCycles' (cechAugmentationMap (iSup U) U ℱ rfl) 1 (by simp)
      (cechAugmentationMap_comp_d_zero_one (iSup U) U ℱ rfl) ≫
    K.homologyπ 0

-- Proof sketch: degree-zero Čech cocycles are exactly compatible local families, while
-- `CochainComplex.isoHomologyπ₀` identifies degree-zero cycles with degree-zero homology.
/-- The canonical map to degree-zero Čech cohomology is bijective exactly when compatible local
families on `U` admit unique gluings on `iSup U`. -/
theorem abelianPresheafToCechH0_bijective_iff_existsUnique_gluing {ι : Type v}
    (U : ι → Opens X) :
    Function.Bijective (abelianPresheafToCechH0 ℱ U) ↔
      ∀ sf : ∀ i : ι, ℱ.obj (op (U i)),
        IsCompatible ℱ U sf → ∃! s : ℱ.obj (op (iSup U)), IsGluing ℱ U sf s := sorry

-- Proof sketch: rewrite the sheaf condition using the owner theorem
-- `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`. The bridge theorem above identifies the
-- source unique-gluing condition for one cover with the canonical degree-zero Čech comparison.
/-- Lemma 20.9.2: an abelian presheaf on `X` is a sheaf if and only if for every open covering,
the natural map from sections on the union to the degree-zero Čech cohomology of the covering is
bijective. -/
theorem abelianPresheaf_isSheaf_iff_bijective_toCechH0 :
    ℱ.IsSheaf ↔
      ∀ ⦃ι : Type v⦄ (U : ι → Opens X),
        Function.Bijective (abelianPresheafToCechH0 ℱ U) := sorry

/-! ### Lemma_20_9_3 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open scoped BigOperators ZeroObject

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for Lemma 20.9.3:
- primary domain: Čech complexes and their degree-zero augmentations for abelian presheaves on an
  indexed family of opens;
- sampled owner API:
  `CategoryTheory.cechComplexFunctor`,
  `AlgebraicTopology.alternatingCofaceMapComplex`,
  `CochainComplex.fromSingle₀AsComplex`,
  `CochainComplex.fromSingle₀Equiv`;
- `source-facing`: the tuplewise Čech terms, restriction maps, augmentation, and the contractible
  extended Čech complex when one cover member is `U`;
- `core/canonical`: `CategoryTheory.cechComplexFunctor 𝒰`;
- `bridge/view`: the explicit tuplewise `cechTerm` / `cechDifferential` formulas and the
  degree-zero augmentation map written in those coordinates, with the degree objects of
  `cechComplexFunctor 𝒰` used directly by definitional equality.

Primitive data is only the indexed family `𝒰`, the presheaf `F`, and the open `U` together with
the cover equality `U = iSup 𝒰`. The ordinary Čech complex itself is not primitive public data
here: it is the canonical owner `cechComplexFunctor`, while the tuplewise coordinates remain only
as the bridge API used by the later ordered/alternating comparison files.
-/

/-- The intersection of the members of an indexed tuple in an open family `𝒰`. -/
abbrev cechIntersection (𝒰 : ι → Opens X) {n : ℕ} (σ : Fin n → ι) : Opens X :=
  ⨅ a, 𝒰 (σ a)

-- Proof sketch: the intersection over all entries of `σ` is contained in the intersection obtained
-- after omitting one entry, because the latter imposes fewer membership conditions.
/-- Omitting one index enlarges the corresponding intersection of cover members. -/
theorem cechIntersection_le_succAbove (𝒰 : ι → Opens X) {n : ℕ}
    (σ : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    cechIntersection 𝒰 σ ≤
      cechIntersection 𝒰 (σ ∘ j.succAboveEmb) := sorry

/-- The degree `p` term of the Čech complex of a presheaf `F` with respect to a family `𝒰`. -/
abbrev cechTerm (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of
    (∀ σ : Fin (p + 1) → ι, F.obj (op (cechIntersection 𝒰 σ)))

@[simp] theorem cechComplexFunctor_obj_X (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    ((cechComplexFunctor 𝒰).obj F).X p = cechTerm 𝒰 F p :=
  rfl

/-- The restriction map associated to omitting one index from a Čech multi-index. -/
abbrev cechRestriction (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) {n : ℕ}
    (σ : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    F.obj (op (cechIntersection 𝒰 (σ ∘ j.succAboveEmb))) ⟶
      F.obj (op (cechIntersection 𝒰 σ)) :=
  F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op

/-- The underlying function of the degree-`p` Čech differential. -/
def cechDifferentialToFun (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    cechTerm 𝒰 F p → cechTerm 𝒰 F (p + 1) :=
  fun s σ ↦
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • cechRestriction 𝒰 F σ j (s (σ ∘ j.succAboveEmb))

-- Proof sketch: each restriction map is additive, finite sums preserve addition, and the scalar
-- coefficients `(-1)^j` distribute over addition in every section group.
/-- The Čech differential is additive on cochains. -/
theorem cechDifferentialToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : cechTerm 𝒰 F p) :
    cechDifferentialToFun 𝒰 F p (s + t) =
      cechDifferentialToFun 𝒰 F p s + cechDifferentialToFun 𝒰 F p t := sorry

/-- The degree-`p` differential in the Čech complex of `F` for the family `𝒰`. -/
abbrev cechDifferential (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    cechTerm 𝒰 F p ⟶ cechTerm 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (cechDifferentialToFun 𝒰 F p)
      (cechDifferentialToFun_map_add 𝒰 F p))

-- Proof sketch: every member `𝒰 i` of the family lies below `iSup 𝒰`; rewriting with
-- `hcover : U = iSup 𝒰` gives the desired inclusion `𝒰 i ≤ U`.
/-- Any member of an open cover of `U` is contained in `U`. -/
theorem openFamily_le_of_iSup_eq (U : Opens X) (𝒰 : ι → Opens X) (hcover : U = iSup 𝒰)
    (i : ι) :
    𝒰 i ≤ U := sorry

-- Proof sketch: each intersection term is contained in each participating cover member, and hence
-- in `U` once `U = iSup 𝒰` is used.
/-- Every nonempty Čech intersection of a cover of `U` is itself contained in `U`. -/
theorem cechIntersection_le_of_iSup_eq (U : Opens X) (𝒰 : ι → Opens X) (hcover : U = iSup 𝒰)
    {n : ℕ} (σ : Fin (n + 1) → ι) :
    cechIntersection 𝒰 σ ≤ U := sorry

/-- The underlying function of the canonical augmentation from `F(U)` to degree `0` Čech cochains. -/
def cechAugmentationToFun (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    F.obj (op U) → cechTerm 𝒰 F 0 :=
  fun s σ ↦ F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover σ)).op s

-- Proof sketch: each component of the augmentation is a restriction morphism of abelian groups,
-- hence additive; the whole map is additive because it is defined componentwise.
/-- The canonical degree-zero Čech augmentation is additive. -/
theorem cechAugmentationToFun_map_add (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰)
    (s t : F.obj (op U)) :
    cechAugmentationToFun U 𝒰 F hcover (s + t) =
      cechAugmentationToFun U 𝒰 F hcover s + cechAugmentationToFun U 𝒰 F hcover t := sorry

/-- The canonical map from `F(U)` to degree `0` of the Čech complex of the covering `𝒰`. -/
abbrev cechAugmentationMap (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    F.obj (op U) ⟶ ((cechComplexFunctor 𝒰).obj F).X 0 :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (cechAugmentationToFun U 𝒰 F hcover)
      (cechAugmentationToFun_map_add U 𝒰 F hcover))

-- Proof sketch: expanding the degree-zero differential shows that each component is the
-- alternating sum of two identical restrictions from `F(U)` to a double intersection, so the two
-- terms cancel.
/-- The canonical augmentation is a cocycle in degree `0` of the Čech complex. -/
theorem cechAugmentationMap_comp_d_zero_one (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    cechAugmentationMap U 𝒰 F hcover ≫ ((cechComplexFunctor 𝒰).obj F).d 0 1 = 0 := sorry

/-- The augmentation from `F(U)` to the Čech complex viewed as a morphism from a single-term
complex in degree `0`. -/
abbrev extendedCechComplexAugmentation (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj (F.obj (op U)) ⟶
      (cechComplexFunctor 𝒰).obj F :=
  (CochainComplex.fromSingle₀Equiv ((cechComplexFunctor 𝒰).obj F) (F.obj (op U))).symm
    ⟨cechAugmentationMap U 𝒰 F hcover, cechAugmentationMap_comp_d_zero_one U 𝒰 F hcover⟩

/-- The extended Čech complex of `F` for a cover `U = ⋃ᵢ Uᵢ`, obtained by placing `F(U)` in
degree `-1`. -/
def extendedCechComplex (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.fromSingle₀AsComplex ((cechComplexFunctor 𝒰).obj F) (F.obj (op U))
    (extendedCechComplexAugmentation U 𝒰 F hcover)

-- Proof sketch: choose the index `i` with `𝒰 i = U`, define the contracting homotopy by inserting
-- `i` at the front of every multi-index, and check componentwise that `dh + hd = 𝟙`.
/-- If one member of the covering family equals `U`, the extended Čech complex is contractible. -/
theorem extendedCechComplex_homotopyEquivalent_zero_of_eq_at (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) (i : ι) (hi : 𝒰 i = U) :
    Nonempty (HomotopyEquiv (extendedCechComplex U 𝒰 F hcover) 0) := sorry

-- Proof sketch: choose an index `i` with `𝒰 i = U` and apply the explicit contracting-homotopy
-- construction from the indexed version of the lemma.
/-- Lemma 20.9.3: if an open cover of `U` contains `U` itself as one of its members, then the
extended Čech complex of an abelian presheaf `F` on `X`, obtained by placing `F(U)` in degree `-1`,
is homotopy equivalent to the zero complex. -/
theorem extendedCechComplex_homotopyEquivalent_zero_of_exists_eq
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (htrivial : ∃ i : ι, 𝒰 i = U) :
    Nonempty (HomotopyEquiv (extendedCechComplex U 𝒰 F hcover) 0) := sorry
