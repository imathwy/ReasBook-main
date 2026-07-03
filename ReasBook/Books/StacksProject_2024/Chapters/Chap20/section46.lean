import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_46_1 (from Chap20) -/
noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Definition 20.46.1:
- primary domain: strictly perfect cochain complexes of module sheaves over a sheaf of rings, with
  the present item the ringed-space specialization;
- sampled owner declarations:
  `CochainComplex.IsStrictlyPerfect`,
  `cochainComplex_isStrictlyPerfect_iff`;
- best owner abstraction: the chapter-local owner `CochainComplex.IsStrictlyPerfect`, already
  defined generically for cochain complexes of module sheaves over a sheaf of rings;
- primitive data: strict lower and upper bounds together with the degreewise retract-of-finite-free
  presentation built into that owner;
- derived API: the source-facing bridge theorem `cochainComplex_isStrictlyPerfect_iff`.

Source/core/bridge triage:
- `source-facing`: Definition 20.46.1 itself, recalled here for complexes of `\mathcal O_X`-modules;
- `core/canonical`: `CochainComplex.IsStrictlyPerfect` from Lemma `20.47.9`;
- `bridge/view`: `cochainComplex_isStrictlyPerfect_iff`, which recovers the textbook boundedness
  plus explicit retract presentation.

The definition should therefore be a direct recall of the existing owner, not a second ringed-space
wrapper and not a parallel local predicate.
-/

/- Definition 20.46.1: the notion of a strictly perfect complex of `\mathcal O_X`-modules is the
existing owner `CochainComplex.IsStrictlyPerfect`. -/
recall CochainComplex.IsStrictlyPerfect

/- The source wording is recovered by the canonical bridge theorem, specialized to complexes of
`\mathcal O_X`-modules. -/
recall cochainComplex_isStrictlyPerfect_iff

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_2 (from Chap20) -/
noncomputable section

open CategoryTheory
open CochainComplex

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable {K L : CochainComplex (RingedSpace.Modules X) ℤ}

-- Proof sketch: unpack `IsStrictlyPerfect`. Boundedness of the mapping cone follows
-- from boundedness of `K` and `L`, and each term of `mappingCone f` is a binary
-- biproduct of a term of `L` with a shifted term of `K`, so the termwise retract presentations by
-- finite free modules combine to give one for the cone term.
/-- Lemma 20.46.2: the cone of a morphism between strictly perfect complexes of
`\mathcal O_X`-modules is strictly perfect. -/
theorem mappingCone_isStrictlyPerfect (f : K ⟶ L)
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (mappingCone f) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_3 (from Chap20) -/
open CategoryTheory MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace CochainComplex

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
variable {K L : CochainComplex (SheafOfModules R) ℤ}

-- Proof sketch: boundedness of the total tensor complex follows from boundedness of the two
-- strictly perfect inputs. In each degree, the total tensor term is a finite direct sum of tensor
-- products of retracts of finite free module sheaves, hence again a retract of a finite free
-- module sheaf.
/-- The tensor product of two strictly perfect complexes of modules over a sheaf of rings is
strictly perfect. In Lean, this totalized tensor product is the monoidal tensor on
`CochainComplex (SheafOfModules R) ℤ`. -/
theorem isStrictlyPerfect_tensor
    [MonoidalCategory (CochainComplex (SheafOfModules R) ℤ)]
    (hK : IsStrictlyPerfect K)
    (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (K ⊗ L) := sorry

end CochainComplex

variable {X : RingedSpace.{u}}
variable {K L : CochainComplex (RingedSpace.Modules X) ℤ}

variable [MonoidalCategory (CochainComplex (RingedSpace.Modules X) ℤ)]

/-- Lemma 20.46.3: the totalized tensor product of two strictly perfect complexes of
`\mathcal O_X`-modules on a ringed space is strictly perfect. In Lean, this totalized tensor
product is the monoidal tensor on `CochainComplex (RingedSpace.Modules X) ℤ`. -/
theorem tensor_isStrictlyPerfect_of_isStrictlyPerfect
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (K ⊗ L) :=
  CochainComplex.isStrictlyPerfect_tensor hK hL

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_4 (from Chap20) -/
open scoped AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

-- Proof sketch: the pullback functor on module sheaves induces a termwise pullback functor on
-- cochain complexes. Strict boundedness is preserved under this induced functor, and in each
-- degree a retract of a finite free module sheaf pulls back to a retract of a finite free module
-- sheaf.
/-- Lemma 20.46.4: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `\mathcal F^\bullet` is a strictly perfect complex of `\mathcal O_Y`-modules, then
the pulled-back complex `f^*\mathcal F^\bullet` is a strictly perfect complex of
`\mathcal O_X`-modules. -/
theorem cochainComplex_isStrictlyPerfect_pullback
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (E : CochainComplex (RingedSpace.Modules Y) ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    CochainComplex.IsStrictlyPerfect (((f^*).mapHomologicalComplex (up ℤ)).obj E) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_5 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ℰ ℱ 𝒢 : (RingedSpace.Modules X)}

/- Domain-style sampling for Lemma 20.46.5:
- primary domain: sheaves of `\mathcal O_X`-modules on a ringed space, with local lifting against
  epimorphisms from a source sheaf that is a direct summand of a finite free module sheaf;
- sampled owner declarations:
  `(RingedSpace.Modules X)`,
  `CategoryTheory.finiteFreeRetractModuleProperty`,
  `SheafOfModules.RingedSite.exists_cover_lift_of_epi_of_retract_finiteFree`,
  `moduleSheafRestrictionToOpen`;
- best owner abstraction: the generic ringed-site owner
  `CategoryTheory.finiteFreeRetractModuleProperty`, specialized here to the underlying sheaf of
  rings `X.ringCatSheaf`;
- primitive data: the morphisms `f : ℰ ⟶ ℱ` and `p : 𝒢 ⟶ ℱ`, the epimorphism structure on `p`,
  and the finite-free-retract owner hypothesis on `ℰ`;
- derived API: the local lift on restrictions to an open neighborhood of each point.

Source/core/bridge triage:
- `source-facing`: this local lifting theorem;
- `core/canonical`: `(RingedSpace.Modules X)`,
  `CategoryTheory.finiteFreeRetractModuleProperty`, and `moduleSheafRestrictionToOpen`;
- `bridge/view`: the ringed-site covering-lift theorem
  `SheafOfModules.RingedSite.exists_cover_lift_of_epi_of_retract_finiteFree`, whose specialization
  at the top open yields this pointwise neighborhood statement.

This file should therefore keep the source-facing lemma and reuse the project owner directly,
rather than keeping a second local predicate for the same finite-free-retract condition. -/

-- Proof sketch: choose a finite free sheaf `\mathcal O_X^{\oplus I}` of which `ℰ` is a retract.
-- Since `p` is surjective, the images in `ℱ` of the finitely many basis sections admit local lifts
-- to `𝒢` near any chosen point. These local lifts assemble to a lift from the finite free sheaf,
-- and composing with the retraction data yields a local lift from `ℰ`.
/-- Lemma 20.46.5: if `\mathcal E` is a direct summand of a finite free `\mathcal O_X`-module and
`p : \mathcal G \to \mathcal F` is surjective, then every morphism `\mathcal E \to \mathcal F`
locally lifts through `p`. -/
theorem exists_open_neighborhood_lift_of_epi_of_retract_finiteFree
    (f : ℰ ⟶ ℱ) (p : 𝒢 ⟶ ℱ) [Epi p]
    (hℰ : finiteFreeRetractModuleProperty X.ringCatSheaf ℰ)
    (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U)
      (l : (moduleSheafRestrictionToOpen U).obj ℰ ⟶ (moduleSheafRestrictionToOpen U).obj 𝒢),
      l ≫ (moduleSheafRestrictionToOpen U).map p = (moduleSheafRestrictionToOpen U).map f := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_6 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

-- Proof sketch: for each point `x`, restrict to a sufficiently small open neighborhood `U`
-- where the finite free summands appearing in the strictly perfect complex split termwise. On
-- `U`, boundedness plus the acyclicity of the target implies the restricted source complex is
-- K-projective, so the restricted morphism is homotopic to zero.
/-- Lemma 20.46.6 (1): if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` is a morphism of
complexes of `\mathcal O_X`-modules with `\mathcal E^\bullet` strictly perfect and
`\mathcal F^\bullet` acyclic, then `\alpha` is locally on `X` homotopic to zero. -/
theorem exists_open_neighborhood_homotopy_zero_of_isStrictlyPerfect_of_acyclic
    (E F : CochainComplex (RingedSpace.Modules X) ℤ) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E) (hF : F.Acyclic) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      Nonempty
        (Homotopy
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)
          0) := sorry

-- Proof sketch: work by induction on the length of the strictly perfect complex `E`. For the
-- top nonzero degree, `H^i(F^\bullet)=0` for `i ≥ a` makes the cocycle sheaf a local quotient of
-- the previous term, so Lemma `20.46.5` gives a local null-homotopy on the top summand. Removing
-- that degree yields a shorter strictly perfect complex, and the induction closes.
/-- Lemma 20.46.6 (2): if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` is a morphism of
complexes of `\mathcal O_X`-modules with `\mathcal E^\bullet` strictly perfect,
`\mathcal E^i = 0` for `i < a`, and `H^i(\mathcal F^\bullet) = 0` for `i \ge a`, then
`\alpha` is locally on `X` homotopic to zero. -/
theorem exists_open_neighborhood_homotopy_zero_of_isStrictlyPerfect_of_isStrictlyGE_of_homology_isZero
    [CategoryWithHomology (RingedSpace.Modules X)]
    (E F : CochainComplex (RingedSpace.Modules X) ℤ) (α : E ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      Nonempty
        (Homotopy
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)
          0) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_7 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

-- Proof sketch: pass from `f` to its mapping cone. The hypotheses on the homology maps imply that
-- `C(f)` has zero homology in degrees `≥ a`, so the composite `E ⟶ F ⟶ C(f)` is locally
-- homotopic to zero by Lemma `20.46.6`. Over such an open neighborhood, the distinguished
-- triangle `G ⟶ F ⟶ C(f) ⟶ G⟦1⟧` yields a lift of the restricted map `α` to `G` up to homotopy.
/-- Lemma 20.46.7: if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` and
`f : \mathcal G^\bullet \to \mathcal F^\bullet` are morphisms of complexes of
`\mathcal O_X`-modules, `\mathcal E^\bullet` is strictly perfect, `\mathcal E^j = 0` for
`j < a`, and `H^j(f)` is an isomorphism for `j > a` and surjective for `j = a`, then locally on
`X` the map `\alpha` lifts through `f` up to homotopy. -/
theorem exists_open_neighborhood_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi
    [CategoryWithHomology (RingedSpace.Modules X)]
    (E F G : CochainComplex (RingedSpace.Modules X) ℤ) (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      ∃ β : (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E) ⟶
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G),
        Nonempty
          (Homotopy
            (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map α)
            (β ≫
              (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f))) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_8 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u}}

/-- Restriction of `\mathcal O_X`-modules to an open subset is additive. -/
local instance moduleSheafRestrictionToOpen_additive (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).Additive := sorry

-- Proof sketch: represent the derived morphism by a roof `E → G ← F`, use Lemma `20.46.7`
-- locally to lift the map from the strictly perfect source through a quasi-isomorphism to an
-- actual morphism of restricted complexes, and then rewrite the resulting equality in the
-- restricted derived category via `mapDerivedCategoryFactors`.
/-- Lemma 20.46.8 (1): if `\mathcal E^\bullet` is strictly perfect, then every morphism
`\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` in `D(\mathcal O_X)` is locally represented
by a morphism of complexes after restricting to a suitable open neighborhood. -/
theorem exists_open_neighborhood_restriction_eq_Q_map_of_isStrictlyPerfect
    (E F : CochainComplex (RingedSpace.Modules X) ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      ∃ αU :
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E) ⟶
            (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F),
        ((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategory).map α =
          ((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategoryFactors.hom.app E) ≫
            DerivedCategory.Q.map αU ≫
            ((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapDerivedCategoryFactors.inv.app F) :=
  sorry

-- Proof sketch: the vanishing of `DerivedCategory.Q.map α` means the morphism of complexes
-- becomes zero in the derived category. Apply part `(1)` to the zero morphism and use the local
-- null-homotopy criterion from the strictly perfect case to conclude that the restricted map is
-- homotopic to zero on a neighborhood of each point.
/-- Lemma 20.46.8 (2): if `\mathcal E^\bullet` is strictly perfect and a morphism of complexes
`\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` becomes zero in `D(\mathcal O_X)`, then
after restricting to a suitable open neighborhood it is homotopic to zero. -/
theorem exists_open_neighborhood_homotopy_zero_of_Q_map_eq_zero_of_isStrictlyPerfect
    (E F : CochainComplex (RingedSpace.Modules X) ℤ) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hα : DerivedCategory.Q.map α = 0) :
    ∀ x : X, ∃ (U : Opens X.carrier) (_ : x ∈ U),
      Nonempty
        (Homotopy
          (((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)
          0) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_9 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [Abelian (Modules X)]
variable [CategoryWithHomology (Modules X)]
variable [HasProducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [SymmetricCategory (Modules X)]
variable [MonoidalClosed (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (K L : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules X))]
variable [MonoidalClosed (DerivedCategory (Modules X))]

/-- Use the preadditive structure induced by the ambient abelian category so the standard
cochain-complex and derived-category APIs use the same instance. -/
local instance : Preadditive (Modules X) :=
  Abelian.toPreadditive

local notation "ModX" => Modules X
local notation "CpxX" => CochainComplex ModX ℤ
local notation "DModX" => DerivedCategory ModX

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O_X`-modules on a ringed space. -/
noncomputable def moduleComplexInternalHomDegree
    (K L : CpxX) (n : ℤ) : ModX :=
  Limits.piObj (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p)))

-- Proof sketch: if `j` is the successor of `i` in the cochain-complex shape, then `j = i + 1`,
-- and both sides reduce to the same degree after reassociating addition on `ℤ`.
/-- Reindexing the target degree in the differential of the internal-Hom complex on a ringed
space. -/
theorem moduleComplexInternalHom_succIndexEq
    {i j p : ℤ} (hij : (up ℤ).Rel i j) :
    i + (p + 1) = j + p := sorry

/-- The postcomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPostcompose
    (K L : CpxX) (i j p : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPrecompose
    (K L : CpxX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (moduleComplexInternalHom_succIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential on a ringed space. -/
noncomputable def moduleComplexInternalHomDComponent
    (K L : CpxX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  if Even i then
    moduleComplexInternalHomPostcompose K L i j p -
      moduleComplexInternalHomPrecompose K L i j p hij
  else
    moduleComplexInternalHomPostcompose K L i j p +
      moduleComplexInternalHomPrecompose K L i j p hij

/-- The differential on the internal-Hom complex of two cochain complexes of `\mathcal O_X`-
modules on a ringed space. -/
noncomputable def moduleComplexInternalHomD
    (K L : CpxX) (i j : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      moduleComplexInternalHomDegree K L j :=
  if hij : (up ℤ).Rel i j then
    Pi.lift (fun p : ℤ ↦ moduleComplexInternalHomDComponent K L i j p hij)
  else
    0

-- Proof sketch: by definition, the internal-Hom differential is zero unless `j = i + 1`.
/-- The internal-Hom differential on a ringed space vanishes away from adjacent cohomological
degrees. -/
theorem moduleComplexInternalHom_shape
    (K L : CpxX) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    moduleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand the two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- source and target complexes, and cancel the mixed terms with the standard cochain sign
-- convention.
/-- Two consecutive differentials in the internal-Hom complex on a ringed space compose to zero. -/
theorem moduleComplexInternalHom_dCompD
    (K L : CpxX) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    moduleComplexInternalHomD K L i j ≫ moduleComplexInternalHomD K L j k = 0 := sorry

/-- The internal-Hom complex of two cochain complexes of `\mathcal O_X`-modules on a ringed
space. -/
noncomputable def moduleComplexInternalHom
    (K L : CpxX) : CpxX where
  X := moduleComplexInternalHomDegree K L
  d := moduleComplexInternalHomD K L
  shape := fun i j hij ↦ moduleComplexInternalHom_shape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦ moduleComplexInternalHom_dCompD K L i j k hij hjk

-- Proof sketch: choose a K-injective resolution `F ⟶ I`. The complex
-- `moduleComplexInternalHom E I` computes `R\mathcal H\!\mathit{om}(E, F)`. Because `E` is
-- strictly perfect, it is bounded with termwise finite free retracts, so the local lifting and
-- homotopy-vanishing statements of Lemma `20.46.8` show that
-- `moduleComplexInternalHom E F ⟶ moduleComplexInternalHom E I` is a quasi-isomorphism. Hence
-- the underived internal-Hom complex already represents the derived internal Hom, and its degree
-- terms identify with the finite direct sums from Section `20.41`.
/-- Lemma 20.46.9: if `\mathcal E^\bullet` is a strictly perfect complex of
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, then the derived internal Hom
`R\mathcal H\!\mathit{om}(\mathcal E^\bullet, \mathcal F^\bullet)` is represented by the
canonical internal-Hom complex `moduleComplexInternalHom E F`. For a strictly perfect source,
its degree-`n` term is the finite direct sum
`\bigoplus_{n = p + q}\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal E^{-q}, \mathcal F^p)`
with the differential of Section `20.41`. -/
theorem derivedInternalHom_iso_moduleComplexInternalHom_of_isStrictlyPerfect
    (E F : CpxX)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    IsIsomorphic ((DerivedCategory.Q.obj (moduleComplexInternalHom E F)) : DModX)
      ((ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_10 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [Abelian (Modules X)]
variable [HasProducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [SymmetricCategory (Modules X)]
variable [MonoidalClosed (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (K L : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (Modules X))]
variable [MonoidalPreadditive (Modules X)]

local notation "ModX" => Modules X
local notation "CpxX" => CochainComplex ModX ℤ

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O_X`-modules on a ringed space. -/
noncomputable def moduleComplexInternalHomDegree
    (K L : CpxX) (n : ℤ) : ModX :=
  Limits.piObj (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p)))

-- Proof sketch: if `j` is the successor of `i` in the cochain-complex shape, then `j = i + 1`,
-- and both sides reduce to the same degree after reassociating addition on `ℤ`.
/-- Reindexing the target degree in the differential of the internal-Hom complex on a ringed
space. -/
theorem moduleComplexInternalHom_succIndexEq
    {i j p : ℤ} (hij : (up ℤ).Rel i j) :
    i + (p + 1) = j + p := sorry

/-- The postcomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPostcompose
    (K L : CpxX) (i j p : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPrecompose
    (K L : CpxX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (moduleComplexInternalHom_succIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential on a ringed space. -/
noncomputable def moduleComplexInternalHomDComponent
    (K L : CpxX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  if Even i then
    moduleComplexInternalHomPostcompose K L i j p -
      moduleComplexInternalHomPrecompose K L i j p hij
  else
    moduleComplexInternalHomPostcompose K L i j p +
      moduleComplexInternalHomPrecompose K L i j p hij

/-- The differential on the internal-Hom complex of two cochain complexes of `\mathcal O_X`-
modules on a ringed space. -/
noncomputable def moduleComplexInternalHomD
    (K L : CpxX) (i j : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      moduleComplexInternalHomDegree K L j :=
  if hij : (up ℤ).Rel i j then
    Pi.lift (fun p : ℤ ↦ moduleComplexInternalHomDComponent K L i j p hij)
  else
    0

-- Proof sketch: by definition, the internal-Hom differential is zero unless `j = i + 1`.
/-- The internal-Hom differential on a ringed space vanishes away from adjacent cohomological
degrees. -/
theorem moduleComplexInternalHom_shape
    (K L : CpxX) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    moduleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand the two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- source and target complexes, and cancel the mixed terms with the standard cochain sign
-- convention.
/-- Two consecutive differentials in the internal-Hom complex on a ringed space compose to zero. -/
theorem moduleComplexInternalHom_dCompD
    (K L : CpxX) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    moduleComplexInternalHomD K L i j ≫ moduleComplexInternalHomD K L j k = 0 := sorry

/-- The internal-Hom complex of two cochain complexes of `\mathcal O_X`-modules on a ringed
space. -/
noncomputable def moduleComplexInternalHom
    (K L : CpxX) : CpxX where
  X := moduleComplexInternalHomDegree K L
  d := moduleComplexInternalHomD K L
  shape := fun i j hij ↦ moduleComplexInternalHom_shape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦ moduleComplexInternalHom_dCompD K L i j k hij hjk

-- Proof sketch: this is exactly Lemma `20.46.9` specialized to the explicit internal-Hom complex
-- defined above. For every acyclic `K^\bullet`, compare
-- `Tot(K^\bullet \otimes \mathcal H^\bullet)` with
-- `\mathcal H\!\mathit{om}^\bullet(E^\bullet, Tot(K^\bullet \otimes F^\bullet))` via the
-- tensor-Hom comparison map; K-flatness of `F^\bullet` makes the target acyclic, and the local
-- acyclicity criterion for strictly perfect sources then gives the source acyclic.
/-- Lemma 20.46.10: in the situation of Lemma `20.46.9`, if `\mathcal F^\bullet` is K-flat, then
the internal-Hom complex
`\mathcal H^\bullet = \mathcal H\!\mathit{om}^\bullet(\mathcal E^\bullet, \mathcal F^\bullet)`
with `\mathcal E^\bullet` strictly perfect is K-flat. -/
theorem moduleComplexInternalHom_isKFlat_of_isStrictlyPerfect
    (E F : CpxX)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hF : CochainComplex.IsKFlat F) :
    CochainComplex.IsKFlat (moduleComplexInternalHom E F) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_46_11 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

set_option checkBinderAnnotations false
set_option maxHeartbeats 1000000

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Abelian.toPreadditive

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.46.11:
- primary domain: derived internal Hom for complexes of `\mathcal O_X`-modules on a ringed space,
  computed by the canonical internal-Hom complex under boundedness and finite-free-retract
  hypotheses;
- sampled owner declarations:
  `(RingedSpace.Modules X)`,
  `moduleComplexInternalHom`,
  `moduleComplexInternalHom_isKInjective_of_isKFlat`,
  `finiteFreeRetractModuleProperty`;
- best owner abstraction: the Chapter 20 owner
  `AlgebraicGeometry.RingedSpace.moduleComplexInternalHom`, already introduced for the ringed-space
  internal-Hom complex in Lemma 20.41.8, together with the generic finite-free-retract owner
  `finiteFreeRetractModuleProperty X.sheaf` for the repeated source hypothesis on the terms of
  `E`;
- primitive data: the ringed space `X`, the complexes `E` and `F`, the bounded-below hypothesis on
  `F`, the bounded-above hypothesis on `E`, and the degreewise direct-summand-of-finite-free
  condition on the terms of `E`;
- derived API: the derived-category object represented by `moduleComplexInternalHom E F`.

Source/core/bridge triage:
- `source-facing`: Lemma 20.46.11 itself, whose extra boundedness hypotheses are genuine source
  content and are not already packaged by the strict-perfect owner;
- `core/canonical`: `(RingedSpace.Modules X)`, `moduleComplexInternalHom`, and
  `finiteFreeRetractModuleProperty`;
- `bridge/view`: the pointwise specialization of `finiteFreeRetractModuleProperty X.sheaf` to the
  terms `E.X n`, recovering the explicit retract-of-finite-free formulation from the owner
  property.

This file should therefore keep only the source-facing hypothesis layer and directly reuse the
existing internal-Hom owner, rather than redeclare the internal-Hom complex and its componentwise
machinery a second time. -/

section

variable {X : RingedSpace.{u}}
variable [Abelian (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasProducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ K L : CochainComplex (RingedSpace.Modules X) ℤ,
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "ModX" => (RingedSpace.Modules X)
local notation "CpxX" => CochainComplex ModX ℤ
local notation "DModX" => DerivedCategory ModX

-- Proof sketch: choose a bounded-below K-injective replacement `F ⟶ I`. Because `E` is bounded
-- above and each `E^n` is a retract of a finite free module sheaf, only finitely many terms
-- contribute in each total degree, so the canonical internal-Hom complex from Lemma `20.41.8`
-- reduces to the finite direct-sum formula from the text. The same strict-perfect argument used
-- degreewise then shows that `moduleComplexInternalHom E F ⟶ moduleComplexInternalHom E I` is a
-- quasi-isomorphism, hence this canonical internal-Hom complex already represents the derived
-- internal Hom.
/-- Lemma 20.46.11: if `\mathcal F^\bullet` is bounded below, `\mathcal E^\bullet` is bounded
above, and each term `\mathcal E^n` is a retract of a finite free `\mathcal O_X`-module, then the
derived internal Hom `R\mathcal H\!\mathit{om}(\mathcal E^\bullet, \mathcal F^\bullet)` is
represented by the canonical internal-Hom complex `moduleComplexInternalHom E F`. Under these
hypotheses, its degree-`n` term is the finite direct sum
`\bigoplus_{n = p + q}\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal E^{-q}, \mathcal F^p)`
described in Section 20.42. -/
theorem derivedInternalHom_iso_moduleComplexInternalHom_of_boundedBelow_of_boundedAbove_termwise_finiteFreeRetract
    (E F : CpxX)
    (hF_boundedBelow : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE_boundedAbove : ∃ b : ℤ, E.IsStrictlyLE b)
    (hE_termwise_finiteFreeRetract :
      ∀ n : ℤ, ∃ I : Type u, Finite I ∧
        Nonempty (Retract (E.X n) (SheafOfModules.free I : ModX))) :
    IsIsomorphic
      ((((DerivedCategory.Q : CpxX ⥤ DModX)).obj
        ((moduleComplexInternalHom : CpxX → CpxX → CpxX) E F)) : DModX)
      ((ihom (((DerivedCategory.Q : CpxX ⥤ DModX)).obj E)).obj
        (((DerivedCategory.Q : CpxX ⥤ DModX)).obj F)) := sorry

end

end AlgebraicGeometry.RingedSpace
