import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_20_1 (from Chap20) -/
open CategoryTheory TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X Z : TopCat.{u}}

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]

-- Proof sketch: by Modules, Lemma `17.6.1`, pushforward along a closed immersion is exact, so its
-- higher right derived functors vanish. Apply Lemma `20.13.6` to the morphism `i`.
/-- Lemma 20.20.1: if `i : Z ⟶ X` is a closed immersion of topological spaces and `F` is an
abelian sheaf on `Z`, then the global degree-`p` cohomology of `F` on `Z` is canonically
isomorphic to the global degree-`p` cohomology of `i_* F` on `X`. -/
theorem global_cohomology_iso_pushforward_of_isClosedEmbedding
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i) (F : Z.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIsomorphic (F.H' p (⊤ : Opens Z))
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F).H' p (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory

/-! ### Lemma_20_20_2 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}}

variable [IrreducibleSpace X]

/-- On an irreducible topological space, the constant abelian sheaf is flasque. -/
-- Proof sketch: by Definition `6.7.4`, sections of the constant sheaf over an open `U` are the
-- locally constant maps `U → A`. Every nonempty open subset of an irreducible space is again
-- irreducible, hence connected, so such a section is determined by any one of its values and is
-- therefore constant. Restriction maps are then surjective, which is exactly flasqueness.
theorem constantAbelianSheaf_isFlasque_of_irreducible
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) := sorry

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

-- Proof sketch: the previous theorem makes the constant abelian sheaf `\underline A` flasque on
-- an irreducible space. Flasque sheaves are acyclic for global sections by Lemma `20.12.3`, so
-- the positive-degree global cohomology objects `H^p(X, \underline A)` vanish.
/-- Lemma 20.20.2: if `X` is irreducible, then the higher cohomology of the constant abelian
sheaf `\underline A` vanishes in every positive degree. -/
theorem isZero_higherCohomology_constantAbelianSheaf_of_irreducible
    (A : AddCommGrpCat.{u}) {p : ℕ} (hp : 0 < p) :
    IsZero (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).H' p
      (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory

/-! ### Lemma_20_20_3 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-
Domain-style sampling for Lemma 20.20.3:
- primary domain: abelian sheaves on a topological space, their generation by finite sums of
  extension-by-zero constant sheaves, and finite filtrations by subobjects with controlled
  subquotients;
- sampled owner declarations:
  `constantSheaf`,
  `openSubsetSheafExtensionByInitialObject`,
  `CategoryTheory.subobjectSubquotient`,
  `ShortComplex.ShortExact`;
- best owner abstractions:
  `constantSheaf` and `openSubsetSheafExtensionByInitialObject` for the sheaves `j_!
  \underline{\mathbf Z}_U`,
  `ShortComplex.ShortExact` for the exact-sequence condition on a quotient,
  `subobjectSubquotient` for successive quotients of the filtration;
- source/core/bridge triage:
  `source-facing`: finite generation by finitely many quasi-compact local generators and the
  existence of a finite filtration with successive quotients of the specified form;
  `core/canonical`: the sheaf owners `constantSheaf`, `openSubsetSheafExtensionByInitialObject`,
  the exactness owner `ShortComplex.ShortExact`, and the abelian subquotient owner
  `subobjectSubquotient`;
  `bridge/view`: the chapter-local abbreviation `extensionByZeroConstantIntegerSheaf` identifying
  the source-text sheaf `j_! \underline{\mathbf Z}_U` with the canonical Chapter 6 owner.
- primitive data versus derived API: the opens `U`, `V`, the comparison maps, and the filtration
  stages are genuine source-level data here; the ambient coproduct object for finitely many
  generators is derived canonical data and should therefore use the finite coproduct owner
  directly rather than an arbitrary cofan witness. -/

/-- The constant abelian sheaf `\underline{\mathbf Z}` on `X`. The coefficient group is modeled by
`ULift ℤ` to match the ambient universe. -/
abbrev constantIntegerSheaf (X : TopCat.{u}) : X.Sheaf AddCommGrpCat.{u} :=
  ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)) : X.Sheaf AddCommGrpCat.{u})

/-- The lower-shriek image `j_{U!}\underline{\mathbf Z}` of the constant integer sheaf on the open
subspace `U`. -/
abbrev extensionByZeroConstantIntegerSheaf (U : Opens X) : X.Sheaf AddCommGrpCat.{u} :=
  ((j! U).obj
    (constantIntegerSheaf (extensionByZeroOpenSubsetSpace U)) :
    X.Sheaf AddCommGrpCat.{u})

/-- A sheaf is generated by finitely many sections over quasi-compact opens when it is an
epimorphic image of the canonical finite coproduct of sheaves `j_{U_i!}\underline{\mathbf Z}`
with each `U_i` quasi-compact. -/
def IsGeneratedByFinitelyManyQuasiCompactSections
    (F : Subobject (constantIntegerSheaf X)) : Prop :=
  ∃ (n : ℕ) (U : Fin n → Opens X),
    (∀ i, IsCompact (U i : Set X)) ∧
      ∃ π : (∐ fun i : Fin n ↦ extensionByZeroConstantIntegerSheaf (U i)) ⟶
          (F : X.Sheaf AddCommGrpCat.{u}),
        Epi π

/-- An abelian sheaf admits a short exact presentation by two extension-by-zero constant integer
sheaves on quasi-compact opens. -/
def HasExtensionByZeroIntegerShortExactPresentation
    (A : X.Sheaf AddCommGrpCat.{u}) : Prop :=
  ∃ (U V : Opens X),
    IsCompact (U : Set X) ∧
      IsCompact (V : Set X) ∧
        ∃ (f : extensionByZeroConstantIntegerSheaf V ⟶ extensionByZeroConstantIntegerSheaf U)
          (g : extensionByZeroConstantIntegerSheaf U ⟶ A) (zero : f ≫ g = 0),
          (ShortComplex.mk f g zero).ShortExact

/-- A finite increasing filtration of an abelian sheaf whose successive quotients admit short exact
presentations by extension-by-zero constant integer sheaves on quasi-compact opens. -/
structure FiniteExtensionByZeroIntegerFiltration (A : X.Sheaf AddCommGrpCat.{u}) where
  /-- The length of the finite filtration. -/
  length : ℕ
  /-- The filtration stages `0 = F₀ ⊆ \cdots ⊆ F_n = A`. -/
  stage : Fin (length + 1) → Subobject A
  /-- The filtration starts at the zero subsheaf. -/
  zero_eq : stage 0 = ⊥
  /-- The filtration ends at the whole sheaf. -/
  top_eq : stage (Fin.last length) = ⊤
  /-- Consecutive stages are nested. -/
  step_le : ∀ i : Fin length, stage i.castSucc ≤ stage i.succ
  /-- Each successive quotient admits the required short exact presentation. -/
  quotient_hasPresentation :
    ∀ i : Fin length,
      HasExtensionByZeroIntegerShortExactPresentation (subobjectSubquotient (step_le i))

-- Proof sketch: rewrite finite generation of the subsheaf as an epimorphism from a finite
-- coproduct of sheaves `j_{U_i!}\underline{\mathbf Z}` with quasi-compact `U_i`, refine the
-- generators by finite intersections so the local integer sections satisfy the gcd condition from
-- the Stacks Project proof, and then filter by the allowed integer values. Each successive quotient
-- is generated by one integer over a quasi-compact union, and its kernel is generated by the same
-- integer over a quasi-compact open, yielding the displayed short exact sequence.
/-- Lemma 20.20.3: if intersections of quasi-compact opens in `X` are quasi-compact and
`ℱ ⊆ \underline{\mathbf Z}` is generated by finitely many sections over quasi-compact opens, then
`ℱ` admits a finite filtration by abelian subsheaves whose successive quotients fit into short
exact sequences `0 ⟶ j'_! \underline{\mathbf Z}_V ⟶ j_! \underline{\mathbf Z}_U ⟶
\mathcal{F}_i / \mathcal{F}_{i-1} ⟶ 0` with `U` and `V` quasi-compact opens. -/
theorem exists_finite_extensionByZeroIntegerFiltration_of_finitely_generated_subsheaf
    (hqc_inter :
      ∀ U V : Opens X,
        IsCompact (U : Set X) →
          IsCompact (V : Set X) →
            IsCompact (U ⊓ V : Set X))
    (F : Subobject (constantIntegerSheaf X))
    (hF : IsGeneratedByFinitelyManyQuasiCompactSections F) :
    Nonempty (FiniteExtensionByZeroIntegerFiltration (F : X.Sheaf AddCommGrpCat.{u})) := sorry

end

/-! ### Lemma_20_20_4 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}}
variable [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

-- Proof sketch: write any abelian sheaf `F` as the filtered colimit of its subsheaves generated by
-- finitely many local sections over compact opens and use Lemma `20.19.1` to pass cohomology
-- through that filtered colimit. Then induct on the number of generators, reducing to quotients of
-- sheaves `j_! \underline{\mathbf Z}_U`. For the kernel of such a quotient, use the finite
-- filtration supplied by Lemma `20.20.3`; the long exact cohomology sequence and induction on the
-- filtration length propagate the assumed vanishing from the extension-by-zero constant integer
-- sheaves to every abelian sheaf.
/-- Lemma 20.20.4: if `X` is quasi-compact, its quasi-compact opens form a basis, and
quasi-compact opens are stable under binary intersection, then vanishing of `H^p(X, j_!
\underline{\mathbf Z}_U)` for every compact open `U` and every `p > d` implies vanishing of
`H^p(X, \mathcal F)` for every abelian sheaf `\mathcal F` and every `p > d`.

The textbook topological hypotheses are expressed canonically by
`[CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]`. -/
theorem isZero_higherCohomology_of_acyclic_extensionByZeroConstantIntegerSheaf
    (d : ℕ)
    (hacyclic :
      ∀ (U : Opens X), IsCompact (U : Set X) →
        ∀ ⦃p : ℕ⦄, d < p →
          IsZero ((extensionByZeroConstantIntegerSheaf U).H' p (⊤ : Opens X)))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) {p : ℕ} (hp : d < p) :
    IsZero (F.H' p (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory

/-! ### Example_20_20_5 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

/-- The points of the countable topological space from Example 20.20.5, modeled by positive
integers. -/
structure CountableInitialSegmentPoint where
  /-- The positive integer indexing the point. -/
  index : ℕ+
deriving DecidableEq

/-- The basic open subset `U_n = { i | i ≤ n }` in the countable initial-segment topology. -/
@[reducible] def countableInitialSegmentBasicOpen (n : ℕ+) :
    Set CountableInitialSegmentPoint :=
  { i | i.index ≤ n }

/-- The topology on the positive integers whose opens are generated by the finite initial segments
`U_n = { i | i ≤ n }`. -/
@[reducible] def countableInitialSegmentTopology :
    TopologicalSpace CountableInitialSegmentPoint :=
  TopologicalSpace.generateFrom (Set.range countableInitialSegmentBasicOpen)

/-- The canonical topological-space structure for the space of Example 20.20.5. -/
instance countableInitialSegmentPoint_instTopologicalSpace :
    TopologicalSpace CountableInitialSegmentPoint :=
  countableInitialSegmentTopology

/-- The topological space from Example 20.20.5. -/
@[reducible] def countableInitialSegmentSpace : TopCat :=
  TopCat.of CountableInitialSegmentPoint

/-- The lattice of opens of the countable initial-segment space has the whole space as a top
element. -/
instance countableInitialSegmentOpens_instOrderTop :
    OrderTop (Opens countableInitialSegmentSpace) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

-- Proof sketch: each `U_n` is one of the generating opens in the `generateFrom` presentation of
-- `countableInitialSegmentTopology`.
/-- Each finite initial segment `U_n` is open in the topology of Example 20.20.5. -/
theorem countableInitialSegmentBasicOpen_isOpen (n : ℕ+) :
    IsOpen (countableInitialSegmentBasicOpen n) := sorry

/-- The basic open `U_n` as an object of `Opens X` for the space of Example 20.20.5. -/
@[reducible] def countableInitialSegmentOpen (n : ℕ+) :
    Opens countableInitialSegmentSpace :=
  ⟨countableInitialSegmentBasicOpen n, countableInitialSegmentBasicOpen_isOpen n⟩

-- Proof sketch: if `m ≤ n`, then every point with index at most `m` also has index at most `n`,
-- so `U_m ⊆ U_n`.
/-- The basic opens are nested in the same order as their indices. -/
theorem countableInitialSegmentOpen_mono {m n : ℕ+} (h : m ≤ n) :
    countableInitialSegmentOpen m ≤ countableInitialSegmentOpen n := sorry

/-- Abelian sheaves on the countable initial-segment space. -/
abbrev CountableInitialSegmentAbelianSheaf :=
  countableInitialSegmentSpace.Sheaf AddCommGrpCat

/-- Inverse systems of abelian groups indexed by the positive integers. -/
abbrev PositiveAbelianGroupInverseSystem :=
  (ℕ+)ᵒᵖ ⥤ AddCommGrpCat

/-- The sections of a sheaf on the basic open `U_n`. -/
abbrev countableInitialSegmentStageSections
    (F : CountableInitialSegmentAbelianSheaf) (n : ℕ+) :=
  F.presheaf.obj (op (countableInitialSegmentOpen n))

/-- The global sections of a sheaf on the space of Example 20.20.5. -/
abbrev countableInitialSegmentGlobalSections
    (F : CountableInitialSegmentAbelianSheaf) :=
  F.presheaf.obj (op (⊤ : Opens countableInitialSegmentSpace))

/-- The restriction morphism `F(U_m) ⟶ F(U_n)` for `U_n ⊆ U_m`. -/
abbrev countableInitialSegmentSectionsTransition
    (F : CountableInitialSegmentAbelianSheaf) {m n : ℕ+} (h : n ≤ m) :
    countableInitialSegmentStageSections F m ⟶ countableInitialSegmentStageSections F n :=
  F.presheaf.map (homOfLE (countableInitialSegmentOpen_mono h)).op

-- Proof sketch: for the identity inequality `n ≤ n`, the inclusion `U_n ⊆ U_n` is the identity,
-- so the associated restriction morphism is the identity section map.
/-- Restriction to the same basic open is the identity map. -/
theorem countableInitialSegmentSectionsTransition_id
    (F : CountableInitialSegmentAbelianSheaf) (n : ℕ+) :
    countableInitialSegmentSectionsTransition F (show n ≤ n from le_rfl) =
      𝟙 (countableInitialSegmentStageSections F n) := sorry

-- Proof sketch: the inclusion `U_n ⊆ U_ℓ` factors through `U_m` whenever `n ≤ m ≤ ℓ`, and the
-- presheaf restriction maps compose functorially along inclusions of opens.
/-- The restriction maps along the chain of basic opens compose as expected. -/
theorem countableInitialSegmentSectionsTransition_comp
    (F : CountableInitialSegmentAbelianSheaf)
    {ℓ m n : ℕ+} (hnm : n ≤ m) (hmℓ : m ≤ ℓ) :
    countableInitialSegmentSectionsTransition F (show n ≤ ℓ from Nat.le_trans hnm hmℓ) =
      countableInitialSegmentSectionsTransition F hmℓ ≫
        countableInitialSegmentSectionsTransition F hnm := sorry

/-- The inverse system `n ↦ F(U_n)` attached to an abelian sheaf on the countable
initial-segment space. -/
def countableInitialSegmentSectionsInverseSystem
    (F : CountableInitialSegmentAbelianSheaf) :
    PositiveAbelianGroupInverseSystem where
  obj n := countableInitialSegmentStageSections F n.unop
  map f := countableInitialSegmentSectionsTransition F (leOfHom f.unop)
  map_id n := countableInitialSegmentSectionsTransition_id F n.unop
  map_comp f g :=
    countableInitialSegmentSectionsTransition_comp F (leOfHom g.unop) (leOfHom f.unop)

/-- The restriction map from global sections to the basic open `U_n`. -/
abbrev countableInitialSegmentGlobalSectionsRestriction
    (F : CountableInitialSegmentAbelianSheaf) (n : ℕ+) :
    countableInitialSegmentGlobalSections F ⟶ countableInitialSegmentStageSections F n :=
  F.presheaf.map
    (homOfLE (show countableInitialSegmentOpen n ≤ (⊤ : Opens countableInitialSegmentSpace)
      from le_top)).op

-- Proof sketch: both sides are the restriction from `X` to `U_n`, with the left side factoring
-- through the intermediate restriction from `X` to `U_m`; presheaf functoriality identifies these
-- composites.
/-- The global restriction maps are compatible with the transition morphisms of the inverse system
`n ↦ F(U_n)`. -/
theorem countableInitialSegmentGlobalSectionsRestriction_natural
    (F : CountableInitialSegmentAbelianSheaf) {m n : (ℕ+)ᵒᵖ} (f : m ⟶ n) :
    countableInitialSegmentGlobalSectionsRestriction F n.unop =
      countableInitialSegmentGlobalSectionsRestriction F m.unop ≫
        (countableInitialSegmentSectionsInverseSystem F).map f := sorry

-- Proof sketch: rewrite the left side as composition with the identity map from the constant cone
-- point and then apply the previous compatibility statement.
/-- The global-sections cone satisfies the naturality identity required of a cone. -/
theorem countableInitialSegmentGlobalSectionsCone_naturality
    (F : CountableInitialSegmentAbelianSheaf) {m n : (ℕ+)ᵒᵖ} (f : m ⟶ n) :
    ((Functor.const ((ℕ+)ᵒᵖ)).obj (countableInitialSegmentGlobalSections F)).map f ≫
      countableInitialSegmentGlobalSectionsRestriction F n.unop =
    countableInitialSegmentGlobalSectionsRestriction F m.unop ≫
      (countableInitialSegmentSectionsInverseSystem F).map f := sorry

/-- The canonical cone from global sections `Γ(X, F)` to the inverse system `n ↦ F(U_n)`. -/
def countableInitialSegmentGlobalSectionsCone
    (F : CountableInitialSegmentAbelianSheaf) :
    Cone (countableInitialSegmentSectionsInverseSystem F) where
  pt := countableInitialSegmentGlobalSections F
  π :=
    { app := fun n ↦ countableInitialSegmentGlobalSectionsRestriction F n.unop
      naturality := fun _ _ f ↦
        countableInitialSegmentGlobalSectionsCone_naturality F f }

section Cohomology

variable [HasWeakSheafify
  (Opens.grothendieckTopology countableInitialSegmentSpace) AddCommGrpCat]
variable [HasSheafify
  (Opens.grothendieckTopology countableInitialSegmentSpace) AddCommGrpCat]
variable [HasExt
  (Sheaf (Opens.grothendieckTopology countableInitialSegmentSpace) AddCommGrpCat)]

/-- The lower-shriek image `j_! \underline{\mathbf Z}_{U_n}` of the constant integer sheaf on the
basic open `U_n`. -/
abbrev countableInitialSegmentExtensionByZeroConstantIntegerSheaf
    (n : ℕ+) : CountableInitialSegmentAbelianSheaf :=
  ((openSubsetSheafExtensionByInitialObject (countableInitialSegmentOpen n)).obj
    ((constantSheaf
      (Opens.grothendieckTopology
        (extensionByZeroOpenSubsetSpace (countableInitialSegmentOpen n)))
      AddCommGrpCat).obj (AddCommGrpCat.of ℤ) :
      (extensionByZeroOpenSubsetSpace (countableInitialSegmentOpen n)).Sheaf AddCommGrpCat) :
    CountableInitialSegmentAbelianSheaf)

-- Proof sketch: classify the opens of the topology as `∅`, `X`, and the basic finite initial
-- segments `U_n`; arbitrary unions of basic opens are again either a basic open or all of `X`,
-- so no additional opens occur.
/-- Example 20.20.5 (1): the opens of `X` are exactly `∅`, `X`, and the basic initial segments
`U_n = { i | i ≤ n }`. -/
theorem countableInitialSegmentTopology_isOpen_iff
    {s : Set CountableInitialSegmentPoint} :
    IsOpen s ↔
      s = ∅ ∨ s = Set.univ ∨ ∃ n : ℕ+, s = countableInitialSegmentBasicOpen n := sorry

-- Proof sketch: evaluate a sheaf `F` on the chain of basic opens `U_1 ⊆ U_2 ⊆ ⋯`; the sheaf
-- condition on this topology identifies a global section with a compatible family of local
-- sections on the `U_n`, which is exactly the universal property of the inverse limit.
/-- Example 20.20.5 (2): for an abelian sheaf `\mathcal F` on `X`, the global sections
`Γ(X, \mathcal F)` form the limit of the inverse system `n ↦ \mathcal F(U_n)`. -/
theorem countableInitialSegmentGlobalSectionsCone_isLimit
    (F : CountableInitialSegmentAbelianSheaf) :
    Nonempty (IsLimit (countableInitialSegmentGlobalSectionsCone F)) := sorry

-- Proof sketch: translate abelian sheaves on this topology into inverse systems of abelian
-- groups using the previous limit description, then choose a short exact sequence of inverse
-- systems whose inverse limit is not exact; the corresponding long exact cohomology sequence
-- produces a sheaf with nonzero `H^1`.
/-- Example 20.20.5 (3): there exists an abelian sheaf on `X` whose first cohomology group is
nonzero. -/
theorem exists_countableInitialSegmentAbelianSheaf_with_nontrivial_firstCohomology :
    ∃ F : CountableInitialSegmentAbelianSheaf,
      ¬ IsZero (F.H' 1 (⊤ : Opens countableInitialSegmentSpace)) := sorry

-- Proof sketch: for a basic open `U_n`, the extension-by-zero sheaf `j_! \underline{\mathbf Z}`
-- is supported on a compact open chain segment; restriction to smaller basic opens stays in the
-- same class, so the higher global cohomology vanishes by the explicit calculation on this
-- one-dimensional inverse-system model.
/-- Example 20.20.5 (4): for the inclusion of a basic open `U_n ⊆ X`, the lower-shriek sheaf
`j_! \underline{\mathbf Z}_{U_n}` has vanishing higher cohomology in every positive degree. -/
theorem countableInitialSegment_extensionByZeroConstantIntegerSheaf_higherCohomology_isZero
    (n : ℕ+) {p : ℕ} (hp : 0 < p) :
    IsZero
      ((countableInitialSegmentExtensionByZeroConstantIntegerSheaf n).H' p
        (⊤ : Opens countableInitialSegmentSpace)) := sorry

end Cohomology

-- Proof sketch: every open cover of `X` contains a maximal basic open, and the whole space is an
-- open set, so any open cover admits a finite subcover.
/-- Example 20.20.5 (5): the space `X` is quasi-compact, expressed canonically as
`CompactSpace X`. -/
theorem countableInitialSegmentSpace_compact :
    CompactSpace CountableInitialSegmentPoint := sorry

-- Proof sketch: the topology has a basis of quasi-compact opens closed under finite intersection,
-- namely the finite initial segments `U_n`, so `X` is spectral in the canonical mathlib sense.
/-- Example 20.20.5 (6): the space `X` is spectral apart from the quasi-separatedness clause,
expressed canonically as `PrespectralSpace X`. -/
theorem countableInitialSegmentSpace_prespectral :
    PrespectralSpace CountableInitialSegmentPoint := sorry

-- Proof sketch: intersections of basic quasi-compact opens are again basic quasi-compact opens,
-- so quasi-compact opens are stable under binary intersection.
/-- Example 20.20.5 (7): quasi-compact opens of `X` are stable under binary intersection,
expressed canonically as `QuasiSeparatedSpace X`. -/
theorem countableInitialSegmentSpace_quasiSeparated :
    QuasiSeparatedSpace CountableInitialSegmentPoint := sorry

/-! ### Lemma_20_20_6 (from Chap20) -/
open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

/-- The constant abelian sheaf on `X` with value `ℤ`. -/
abbrev constantIntegerAbelianSheaf (X : TopCat) : X.Sheaf AddCommGrpCat :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The constant abelian sheaf on the open subspace `U` with value `dℤ`. -/
abbrev integerMultiplesAbelianSheaf {X : TopCat} (U : Opens X) (d : ℤ) :
    ((Opens.toTopCat X).obj U).Sheaf AddCommGrpCat :=
  (constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat).obj
    (AddCommGrpCat.of ↑(AddSubgroup.zmultiples d))

-- Proof sketch: on an irreducible space, every nonempty open subset has only constant sections in
-- the ambient constant sheaf `\underline{\mathbf Z}`. The subgroup cut out by `ℋ` on a nonempty
-- open is therefore some `n\mathbf Z`, and if this subgroup is not yet locally constant one can
-- shrink to a smaller nonempty open with strictly smaller positive generator; well-foundedness of
-- the positive integers forces this process to stop.
/-- Lemma 20.20.6: for a subobject `ℋ` of the constant abelian sheaf
`\underline{\mathbf Z}` on an irreducible space, there is a nonempty open subset on which `ℋ`
is isomorphic to the constant abelian sheaf with value `d\mathbf Z` for some integer `d`. -/
theorem exists_nonempty_open_restrictIso_integerMultiplesAbelianSheaf
    {X : TopCat} [IrreducibleSpace X]
    (ℋ : Subobject (constantIntegerAbelianSheaf X)) :
    ∃ (U : Opens X) (_ : (U : Set X).Nonempty) (d : ℤ),
      Nonempty (((TopCat.Sheaf.pullback AddCommGrpCat (Opens.inclusion' U)).obj
          (((ℋ : Subobject (constantIntegerAbelianSheaf X)) : X.Sheaf AddCommGrpCat))) ≅
        integerMultiplesAbelianSheaf U d) := sorry

/-! ### Proposition_20_20_7_Grothendieck (from Chap20) -/
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CategoryTheory
namespace Sheaf

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

-- Proof sketch: argue by induction on `d`. First use the finite decomposition of a Noetherian
-- space into irreducible components to reduce, via the short exact sequence for an open subset and
-- its closed complement together with Lemma `20.20.1`, to the case that `X` is irreducible. For
-- irreducible `X`, the case `d = 0` follows from Lemma `20.20.2`, and the case `d > 0` reduces by
-- Lemma `20.20.4` to extension-by-zero constant sheaves on opens, where the standard short exact
-- sequence with the constant sheaf on `X` and the induction hypothesis on the closed complement
-- gives the vanishing in degrees `p > d`.
/-- Proposition 20.20.7 (Grothendieck): if `X` is a Noetherian topological space of Krull
dimension at most `d`, then every abelian sheaf on `X` has vanishing global cohomology in degrees
strictly larger than `d`. -/
theorem isZero_higherCohomology_of_noetherianSpace_of_topologicalKrullDim_le
    (d : ℕ) (hXdim : topologicalKrullDim X ≤ d)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) {p : ℕ} (hp : d < p) :
    IsZero (F.H' p (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory
