import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.SheafOfFunctions

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_7_1 (from Chap06) -/
universe u v

open CategoryTheory TopCat

namespace TopCat

scoped notation "Sh(" X ")" => TopCat.Sheaf (Type _) X

end TopCat

open scoped TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.7.1:
- primary domain: sheaves of sets on a topological space and their morphisms as a full
  subcategory of presheaves;
- sampled owner declarations:
  `TopCat.Sheaf`,
  `TopCat.Presheaf.IsSheaf`,
  `TopCat.Sheaf.forget`,
  `CategoryTheory.Sheaf.homEquiv`;
- best owner abstraction: the canonical sheaf owner `X.Sheaf (Type v)`, with source-facing
  Stacks notation `Sh(X)`;
- primitive data: none beyond the canonical owner `X.Sheaf (Type v)` and the sheaf predicate on a
  `Type`-valued presheaf;
- derived API: the underlying presheaf, the forgetful functor to presheaves, and the equivalence
  between morphisms of sheaves and morphisms of the underlying presheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks notation `Sh(X)` together with the description of its morphisms;
- `core/canonical`: `TopCat.Sheaf` and `TopCat.Presheaf.IsSheaf`;
- `bridge/view`: `TopCat.Sheaf.forget` and `Sheaf.homEquiv`, which expose the underlying
  presheaf-level view without introducing a parallel local owner.

Since Definition 6.7.1 only recalls the canonical category of sheaves of sets and its morphisms,
this file should stay in direct recall/check form rather than define any wrapper around the sheaf
owner or around sheaf morphisms. -/

/- Definition 6.7.1 (1) and (3): the category of sheaves of sets on a topological space `X`,
denoted `Sh(X)` in the Stacks Project, is the canonical project-facing owner `Sh(X)`
of set-valued presheaves satisfying the sheaf condition. -/
recall TopCat.Sheaf
#check (Sh(X))

/- The sheaf condition on a set-valued presheaf on `X` is the canonical predicate
`TopCat.Presheaf.IsSheaf`, expressing existence and uniqueness of gluing for compatible local
sections over open covers. -/
#check (Presheaf.IsSheaf : X.Presheaf (Type v) → Prop)

section

variable {X}
variable (ℱ 𝒢 : Sh(X))

/- Definition 6.7.1 (2): morphisms in `Sh(X)` are exactly morphisms of the underlying presheaves,
via the canonical fully faithful inclusion of sheaves into presheaves. -/
#check (Sheaf.homEquiv : (ℱ ⟶ 𝒢) ≃ (ℱ.presheaf ⟶ 𝒢.presheaf))

/- The same identification is implemented by the canonical forgetful functor from sheaves to
presheaves. -/
#check (Sheaf.forget (Type v) X : Sh(X) ⥤ X.Presheaf (Type v))

end

/-! ### Remark_6_7_2 (from Chap06) -/
open CategoryTheory.Limits Opposite TopCat

universe u v

/- Domain-style sampling for Remark 6.7.2:
- primary domain: sheaves on a topological space, evaluated on the empty open and on disjoint
  unions of opens;
- sampled owner API:
  `TopCat.Sheaf.isTerminalOfEmpty`,
  `TopCat.Sheaf.isProductOfDisjoint`,
  `Types.isTerminalEquivUnique`,
  `IsTerminal`;
- owner abstraction: the core/canonical owner for the empty-open clause is the terminal-object
  statement `TopCat.Sheaf.isTerminalOfEmpty`;
- primitive data: only the sheaf `F`;
- derived API: the `Type`-valued singleton-section reformulation, obtained from
  `Types.isTerminalEquivUnique`.

Source/core/bridge triage:
- `source-facing`: the remark that a sheaf has a final object of sections over the empty open, and
  that disjoint unions of opens give binary products of sections;
- `core/canonical`: `TopCat.Sheaf.isTerminalOfEmpty` and `TopCat.Sheaf.isProductOfDisjoint`;
- `bridge/view`: the `Unique` instance below, which is the `Type`-specialization of terminality.

The file already uses the canonical sheaf owners directly, so the only local declaration kept here
is the derived singleton-section instance rather than a parallel wrapper theorem. -/

/- Remark 6.7.2: for any sheaf on a topological space, the sections over the empty open are a
final object in the target category. -/
recall TopCat.Sheaf.isTerminalOfEmpty

/- In particular, for a sheaf of types or sets, the sections over the empty open form a singleton
type. -/
noncomputable instance {X : TopCat.{u}} (F : X.Sheaf (Type v)) :
    Unique (F.obj.obj (op ⊥)) :=
  Types.isTerminalEquivUnique _ F.isTerminalOfEmpty

/- Companion recall: if `U` and `V` are disjoint opens, then the sheaf condition identifies the
sections on `U ⊔ V` as the binary product of the sections on `U` and on `V`. -/
recall TopCat.Sheaf.isProductOfDisjoint

/-! ### Example_6_7_3 (from Chap06) -/
open TopCat

universe u

section

variable (X Y : TopCat.{u})

/- Domain-style sampling for Example 6.7.3:
- primary domain: set-valued sheaves on a topological space, specifically the sheaf of continuous
  maps into a fixed target space;
- sampled owner declarations:
  `presheafToTop`,
  `presheafToTop_obj`,
  `sheafToTop`,
  `TopCat.Presheaf.IsSheaf`;
- best owner abstraction: the bundled sheaf owner `sheafToTop Y`, whose underlying presheaf is the
  canonical `presheafToTop X Y`;
- primitive data: only the target space `Y` together with the canonical presheaf of continuous
  maps, already supplied upstream by `presheafToTop`;
- derived API: the sheaf condition on that presheaf, carried by `(sheafToTop Y).property`.

Source/core/bridge triage:
- `source-facing`: the presheaf on `X` sending `U` to the continuous maps `U ⟶ Y`;
- `core/canonical`: the bundled owner `sheafToTop Y`;
- `bridge/view`: the unbundled predicate `(presheafToTop X Y).IsSheaf`.

Since this example only recalls that the canonical presheaf of continuous maps is a sheaf, the file
should stay in direct recall/check form rather than introduce any local wrapper around either
`presheafToTop` or `sheafToTop`.
-/

/- Canonical recall: the sheaf of continuous maps from opens of `X` into `Y` is
`sheafToTop Y`. -/
recall sheafToTop

/- Companion recall: the underlying rule `U ↦ {f : U → Y | Continuous f}` with restriction by
precomposition is the canonical presheaf `presheafToTop X Y`. -/
recall presheafToTop

/- Example 6.7.3: for topological spaces `X` and `Y`, the presheaf sending an open set `U ⊆ X`
to the set of continuous maps `U → Y`, with the obvious restriction maps, satisfies the sheaf
condition. This is the `.property` field of the canonical owner `sheafToTop Y`. -/
#check (show (presheafToTop X Y).IsSheaf from (sheafToTop Y).property)

end

/-! ### Definition_6_7_4 (from Chap06) -/
open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens Topology
open scoped TopCat AlgebraicGeometry

universe u v

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.7.4:
- primary domain: set-valued sheaves on a topological space, comparing the source-facing locally
  constant model with the canonical constant sheaf;
- sampled owner abstractions:
  `CategoryTheory.constantSheaf`,
  `A ₚ X`,
  `TopCat.LocalPredicate`,
  `TopCat.subpresheafToTypes`,
  `TopCat.subsheafToTypes`;
- source/core/bridge triage:
  `source-facing`: `locallyConstantPresheaf`, `locallyConstantSheaf`;
  `core/canonical`: `TopCat.subsheafToTypes` for the sheaf of locally constant functions, and
    `CategoryTheory.constantSheaf` for the constant-object comparison;
  `bridge/view`: `constantSheafToLocallyConstantSheaf` and the theorem-level `IsIso` results for
  it and its section maps;
- primitive data: the only genuine data are the local predicate `IsLocallyConstant` on ordinary
  `A`-valued sections, together with the chapter-owner constant presheaf `A ₚ X`;
- derived API: both the presheaf and the sheaf come from the local-predicate owner, while the
  comparison with `constantSheaf` is the bridge built by sheafification and proved invertible
  afterward.
-/

private def locallyConstantPredicate (A : Type (max u v)) : LocalPredicate fun _ : X ↦ A where
  pred {U} f := IsLocallyConstant f
  res {_ _} i f hf := hf.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality {U} f hf := (IsLocallyConstant.iff_exists_open f).2 fun x ↦ by
    rcases hf x with ⟨V, hxV, i, hi⟩
    rcases hi.exists_open ⟨x.1, hxV⟩ with ⟨W, hW_open, hxW, hW⟩
    refine ⟨i '' W, (Opens.isOpenEmbedding_of_le i.le).isOpenMap _ hW_open, ?_, ?_⟩
    · exact ⟨⟨x.1, hxV⟩, hxW, by ext; rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      simpa using hW z hz

/-- Definition 6.7.4 source-facing presheaf: over an open `U ⊆ X`, the sections are the locally
constant maps `U → A`, viewed canonically as the subpresheaf of all `A`-valued functions cut out by
the local predicate `IsLocallyConstant`. -/
abbrev locallyConstantPresheaf (A : Type (max u v)) : X.Presheaf (Type (max u v)) :=
  subpresheafToTypes (locallyConstantPredicate X A).toPrelocalPredicate

/-- The source-facing locally constant presheaf is a sheaf. -/
theorem locallyConstantPresheaf_isSheaf (A : Type (max u v)) :
    (locallyConstantPresheaf X A).IsSheaf :=
  subpresheafToTypes.isSheaf (locallyConstantPredicate X A)

/-- Definition 6.7.4 source-facing sheaf: the sheaf of locally constant `A`-valued functions. -/
abbrev locallyConstantSheaf (A : Type (max u v)) : TopCat.Sheaf (Type (max u v)) X :=
  subsheafToTypes (locallyConstantPredicate X A)

section

variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/- Definition 6.7.4: the constant sheaf on `X` with value `A` is the canonical sheafification
of the constant presheaf, namely `CategoryTheory.constantSheaf`. -/
recall CategoryTheory.constantSheaf

private def constantToLocallyConstantPresheaf (A : Type u) :
    (A ₚ X) ⟶ locallyConstantPresheaf X A where
  app U a := ⟨fun _ ↦ a, IsLocallyConstant.const a⟩
  naturality {_ _} i := by
    rfl

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- Helper for Definition 6.7.4: the constant-to-locally-constant presheaf map is locally
surjective because every locally constant section is constant on a neighborhood of each point. -/
private theorem constantToLocallyConstantPresheaf_isLocallySurjective (A : Type u) :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (constantToLocallyConstantPresheaf X A) := by
  constructor
  intro U s x hx
  -- Use local constancy to choose a neighborhood where the section is literally constant.
  rcases s.2.exists_open ⟨x, hx⟩ with ⟨V, hV_open, hxV, hV⟩
  let W : Opens X := ⟨Subtype.val '' V, U.2.isOpenMap_subtype_val _ hV_open⟩
  have hW_le : W ≤ U := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact z.2
  refine ⟨W, homOfLE hW_le, ?_, ?_⟩
  · -- The chosen neighborhood is hit by the constant section with value `s x`.
    refine ⟨s.1 ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    funext y
    rcases y.2 with ⟨z, hz, hyz⟩
    have hz_eq : z = ⟨y, hW_le y.2⟩ := by
      apply Subtype.ext
      simpa using hyz
    simpa [hz_eq] using (hV z hz).symm
  · exact ⟨⟨x, hx⟩, hxV, rfl⟩

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- Helper for Definition 6.7.4: equality of two constant sections holds locally because, at each
point, evaluating the equality shows the two constants agree on the whole ambient open. -/
private theorem constantToLocallyConstantPresheaf_isLocallyInjective (A : Type u) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (constantToLocallyConstantPresheaf X A) := by
  constructor
  intro U a b h x hx
  -- Evaluate the equality of constant functions at the chosen point to identify the constants.
  have hab : a = b := by
    exact congrFun (congrArg Subtype.val h) ⟨x, hx⟩
  refine ⟨U.unop, 𝟙 _, ?_, hx⟩
  simp [CategoryTheory.Presheaf.equalizerSieve, hab]

/-- Definition 6.7.4 bridge: the canonical comparison from the constant sheaf with value `A` to
the source-facing sheaf of locally constant `A`-valued functions. -/
noncomputable def constantSheafToLocallyConstantSheaf (A : Type u) :
    (constantSheaf (Opens.grothendieckTopology X) (Type u)).obj A ⟶
      locallyConstantSheaf X A :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (constantToLocallyConstantPresheaf X A)
      (locallyConstantPresheaf_isSheaf X A)⟩

/-- Helper for Definition 6.7.4: the concrete bridge to locally constant functions factors through
the generic sheafification map and the inverse of the sheafification isomorphism on the target
sheaf. -/
private theorem constantSheafToLocallyConstantSheaf_hom_factorization
    (A : Type u) :
    (constantSheafToLocallyConstantSheaf X A).hom =
      ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map
          (constantToLocallyConstantPresheaf X A)).hom ≫
        (sheafificationIso (locallyConstantSheaf X A)).inv.hom := by
  let J := Opens.grothendieckTopology X
  let η : (A ₚ X) ⟶ locallyConstantPresheaf X A := constantToLocallyConstantPresheaf X A
  -- Compare the concrete bridge with the universal sheafification map followed by the inverse
  -- of the target sheafification isomorphism.
  simpa [J, η, constantSheafToLocallyConstantSheaf, CategoryTheory.sheafificationIso,
    CategoryTheory.isoSheafify_inv] using
    (CategoryTheory.sheafifyMap_sheafifyLift
      (J := J) η (𝟙 (locallyConstantPresheaf X A))
      (locallyConstantPresheaf_isSheaf X A))

/-- Definition 6.7.4 companion: the canonical comparison from the constant sheaf to the sheaf of
locally constant functions is an isomorphism. -/
theorem constantSheafToLocallyConstantSheaf_isIso (A : Type u) :
    IsIso (constantSheafToLocallyConstantSheaf X A) := by
  let J := Opens.grothendieckTopology X
  let f :
      (constantSheaf J (Type u)).obj A ⟶
        (presheafToSheaf J (Type u)).obj (locallyConstantPresheaf X A) :=
    (presheafToSheaf J (Type u)).map (constantToLocallyConstantPresheaf X A)
  let g :
      (presheafToSheaf J (Type u)).obj (locallyConstantPresheaf X A) ⟶
        locallyConstantSheaf X A :=
    (sheafificationIso (locallyConstantSheaf X A)).inv
  -- Route correction: use the library equivalence between local bijectivity of a presheaf map
  -- and of its sheafification map, then factor the concrete comparison through that map.
  have hf_inj : CategoryTheory.Sheaf.IsLocallyInjective (J := J) f := by
    -- Unfold `f` and transfer local injectivity directly across `presheafToSheaf.map`.
    change CategoryTheory.Sheaf.IsLocallyInjective
      ((presheafToSheaf J (Type u)).map (constantToLocallyConstantPresheaf X A))
    exact
      (Presheaf.isLocallyInjective_presheafToSheaf_map_iff
        (J := J) (A := Type u) (φ := constantToLocallyConstantPresheaf X A)).2
        (constantToLocallyConstantPresheaf_isLocallyInjective (X := X) A)
  have hf_surj : CategoryTheory.Sheaf.IsLocallySurjective (J := J) f := by
    -- Unfold `f` and transfer local surjectivity by the analogous equivalence.
    change CategoryTheory.Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type u)).map (constantToLocallyConstantPresheaf X A))
    exact
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
        (J := J) (A := Type u) (φ := constantToLocallyConstantPresheaf X A)).2
        (constantToLocallyConstantPresheaf_isLocallySurjective (X := X) A)
  have hf_iso : IsIso f := by
    -- A locally bijective morphism of sheaves of types is an isomorphism.
    exact
      (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso
        (J := J) (A := Type u) (f := f)).1 ⟨hf_inj, hf_surj⟩
  have hg_iso : IsIso g := by
    infer_instance
  have hfactor : constantSheafToLocallyConstantSheaf X A = f ≫ g := by
    -- Identify the concrete bridge with the sheafified map followed by the target inverse.
    apply CategoryTheory.Sheaf.hom_ext
    exact constantSheafToLocallyConstantSheaf_hom_factorization (X := X) (A := A)
  letI : IsIso f := hf_iso
  letI : IsIso g := hg_iso
  rw [hfactor]
  infer_instance

/-- Definition 6.7.4 companion: for every open `U ⊆ X`, the induced map on sections of the
canonical comparison from the constant sheaf with value `A` to the sheaf of locally constant
`A`-valued functions is an isomorphism. -/
theorem constantSheafToLocallyConstantSheaf_app_isIso
    (A : Type u) (U : Opens X) :
    IsIso ((constantSheafToLocallyConstantSheaf X A).hom.app (op U)) := by
  letI := constantSheafToLocallyConstantSheaf_isIso X A
  letI :
      IsIso
        ((sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).map
          (constantSheafToLocallyConstantSheaf X A)) :=
    Functor.map_isIso _ (constantSheafToLocallyConstantSheaf X A)
  simpa using
    (show IsIso
      ((((sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).map
          (constantSheafToLocallyConstantSheaf X A)).app (op U))) by
      infer_instance)

end

end

/-! ### Example_6_7_5 (from Chap06) -/
/- Domain-style sampling for Example 6.7.5:
- primary domain: dependent-function presheaves and their canonical sheaf packaging on a
  topological space;
- sampled owner API:
  `TopCat.presheafToTypes`,
  `TopCat.Presheaf.toTypes_isSheaf`,
  `TopCat.sheafToTypes`,
  `TopCat.presheafToTypes_obj`,
  `TopCat.presheafToTypes_map`;
- source/core/bridge triage:
  `source-facing`: the presheaf `U ↦ ∀ x : U, A x.1` with restriction by precomposition;
  `core/canonical`: the mathlib owner `TopCat.presheafToTypes`;
  `bridge/view`: the sheaf proof `TopCat.Presheaf.toTypes_isSheaf`, the packaged sheaf
    `TopCat.sheafToTypes`, and the companion object/map computation lemmas.

Primitive data are only the dependent-function presheaf itself. The sheaf proof, sheaf packaging,
and object/map formulas are derived API on that owner, so this file should stay as direct recall of
the canonical mathlib declarations rather than introducing any local wrapper or renamed copy.
-/

/- Example 6.7.5: for a family of sets `A : X → Type v` on a topological space `X`, the
presheaf `U ↦ ∀ x : U, A x.1` with restriction by precomposition along inclusions of opens is the
canonical presheaf `TopCat.presheafToTypes`. -/
recall TopCat.presheafToTypes

/- The same presheaf satisfies the sheaf condition. In mathlib this is the canonical theorem
`TopCat.Presheaf.toTypes_isSheaf`. -/
recall TopCat.Presheaf.toTypes_isSheaf

/- Companion recall: packaging the same presheaf together with its sheaf proof gives the mathlib
sheaf `TopCat.sheafToTypes`. -/
recall TopCat.sheafToTypes

/- Companion recall: the value of the underlying presheaf on an open `U` is the product of the
fibers over points of `U`, formalized as dependent functions on `U`. -/
recall TopCat.presheafToTypes_obj

/- Companion recall: the restriction maps are given by restricting a dependent function along the
inclusion of opens. -/
recall TopCat.presheafToTypes_map

/-! ### Example_6_7_6 (from Chap06) -/
open CategoryTheory TopologicalSpace TopCat
open TopCat.Presheaf

universe u v

noncomputable section

variable {X : TopCat.{u}}

/- Domain-style sampling for Example 6.7.6:
- primary domain: sheaf conditions for presheaves of sections on a topological space;
- sampled owner API:
  `TopCat.PrelocalPredicate`,
  `TopCat.LocalPredicate`,
  `TopCat.subpresheafToTypes`,
  `TopCat.subpresheafToTypes.isSheaf`;
- source/core/bridge triage:
  `source-facing`: the direct-sum presheaf `U ↦ Π₀ x : U, M x.1`;
  `core/canonical`: the subsheaf-of-functions owner supplied by `subpresheafToTypes`;
  `bridge/view`: the comparison isomorphism identifying a `DFinsupp` section with an ordinary
    dependent function whose nonzero locus is finite.

Primitive data for the source-facing object are just ordinary dependent functions together with the
finite-support condition. The `DFinsupp` presentation from `Example_6_4_5` is therefore a concrete
model, while the owner abstraction for the sheaf argument is the canonical subpresheaf of
`TopCat.presheafToTypes` cut out by the finite-support predicate.
-/

section

variable (M : X → Type v) [∀ x, AddCommGroup (M x)]

/-- Ordinary dependent sections on an open set whose nonzero locus is finite. -/
private def pointwiseFiniteSupport {U : Opens X} (s : ∀ x : U, M x.1) : Prop :=
  Set.Finite {x : U | s x ≠ 0}

/-- The finite-support condition is stable under restriction, so it defines a prelocal predicate on
the sheaf of all dependent functions. -/
private def pointwiseFiniteSupportPrelocalPredicate : TopCat.PrelocalPredicate M where
  pred := pointwiseFiniteSupport M
  res := by
    intro U V i s hs
    classical
    simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using
      Set.Finite.preimage_embedding
        ⟨Set.inclusion i.le, fun a b h ↦ by simpa [Set.inclusion] using h⟩ hs

/-- If every open subset of `X` is compact, finite support is a local predicate. -/
private def pointwiseFiniteSupportLocalPredicate
    (hqc : ∀ U : Opens X, IsCompact (U : Set X)) : TopCat.LocalPredicate M where
  toPrelocalPredicate := pointwiseFiniteSupportPrelocalPredicate M
  locality := by
    intro U s hs
    classical
    choose V hxV i hi using hs
    have hi' (x : U) : Set.Finite { y : V x | s (i x y) ≠ 0 } := by
      simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using hi x
    obtain ⟨t, ht⟩ :=
      (hqc U).elim_finite_subcover (fun x : U ↦ (V x : Set X)) (fun x ↦ (V x).isOpen)
        (by
          intro x hx
          exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simpa using hxV ⟨x, hx⟩⟩)
    refine Set.Finite.subset
      (t.finite_toSet.biUnion fun x hx ↦ (hi' x).image (i x)) fun y hy ↦ ?_
    rcases Set.mem_iUnion₂.1 (ht y.2) with ⟨x, hx, hyV⟩
    refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
    refine ⟨⟨y.1, hyV⟩, ?_, ?_⟩
    · simpa using hy
    · ext
      rfl

/-- A `DFinsupp` section is canonically the same thing as an ordinary dependent section with finite
support. -/
private noncomputable def pointwiseDirectSumSectionEquiv (U : Opens X) :
    (Π₀ x : U, M x.1) ≃ { s : ∀ x : U, M x.1 // pointwiseFiniteSupport M s } where
  toFun f := ⟨f, by simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using f.finite_support⟩
  invFun s := by
    classical
    exact DFinsupp.mk s.2.toFinset fun x ↦ s.1 x
  left_inv := by
    classical
    intro f
    let g : ∀ y : ((f.finite_support.toFinset : Finset U) : Set U), M y.1 := fun y ↦ f y.1
    ext x
    change (DFinsupp.mk f.finite_support.toFinset g : Π₀ y : U, M y.1) x = f x
    by_cases hx : f x = 0
    · have hx' : x ∉ f.finite_support.toFinset := by
        rw [Set.Finite.mem_toFinset]
        simp [Set.mem_setOf_eq, hx]
      simp [g, DFinsupp.mk_apply, hx', hx]
    · have hx' : x ∈ f.finite_support.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact hx
      simp [g, DFinsupp.mk_apply, hx']
  right_inv := by
    classical
    intro s
    let g : ∀ y : ((s.2.toFinset : Finset U) : Set U), M y.1 := fun y ↦ s.1 y.1
    apply Subtype.ext
    funext x
    change (DFinsupp.mk s.2.toFinset g : Π₀ y : U, M y.1) x = s.1 x
    by_cases hx : s.1 x = 0
    · have hx' : x ∉ s.2.toFinset := by
        rw [Set.Finite.mem_toFinset]
        simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using hx
      simp [g, DFinsupp.mk_apply, hx', hx]
    · have hx' : x ∈ s.2.toFinset := by
        rw [Set.Finite.mem_toFinset]
        simpa [pointwiseFiniteSupport, Set.mem_setOf_eq] using hx
      simp [g, DFinsupp.mk_apply, hx']

/-- The underlying set-valued presheaf of `pointwiseDirectSumPresheaf` is canonically the
subpresheaf of all dependent functions cut out by the finite-support predicate. -/
private noncomputable def pointwiseDirectSumUnderlyingIsoSubpresheaf :
    pointwiseDirectSumPresheaf M ⋙ forget AddCommGrpCat.{max u v} ≅
      subpresheafToTypes (pointwiseFiniteSupportPrelocalPredicate M) :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso (pointwiseDirectSumSectionEquiv M U.unop))
    (by
      intro U V i
      ext f
      rfl)

/-- Under the compact-open hypothesis, the underlying set-valued presheaf of
`pointwiseDirectSumPresheaf` is a sheaf because it is the canonical subsheaf of all dependent
functions satisfying the local finite-support predicate. -/
private theorem pointwiseDirectSumPresheaf_underlying_isSheaf_of_compact_opens
    (hqc : ∀ U : Opens X, IsCompact (U : Set X)) :
    TopCat.Presheaf.IsSheaf (pointwiseDirectSumPresheaf M ⋙ forget AddCommGrpCat.{max u v}) := by
  exact
    (isSheaf_iso_iff (pointwiseDirectSumUnderlyingIsoSubpresheaf M)).2 <|
      subpresheafToTypes.isSheaf (pointwiseFiniteSupportLocalPredicate M hqc)

/-- Example 6.7.6: if every open subset of `X` is quasi-compact, then the pointwise direct-sum
presheaf from Example 6.4.5 satisfies the sheaf condition. -/
theorem pointwiseDirectSumPresheaf_isSheaf_of_compact_opens
    (hqc : ∀ U : Opens X, IsCompact (U : Set X)) :
    (pointwiseDirectSumPresheaf M).IsSheaf := by
  exact
    (isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat.{max u v}) (pointwiseDirectSumPresheaf M)).2 <|
      pointwiseDirectSumPresheaf_underlying_isSheaf_of_compact_opens M hqc

-- Proof sketch: on an infinite discrete space, the singleton open cover identifies the sheaf
-- condition with an infinite product, while `pointwiseDirectSumPresheaf` uses the direct sum.
/-- Helper for Example 6.7.6: a direct-sum section on `⊤` that is equal to `1` at every point has
infinite support, so it cannot come from `DFinsupp`. -/
private lemma global_support_infinite_of_all_ones [Infinite X] (t : Π₀ _ : (⊤ : Opens X), ℤ)
    (ht : ∀ x : X, t ⟨x, by trivial⟩ = 1) :
    ¬ Set.Finite {y : (⊤ : Opens X) | t y ≠ 0} := by
  intro hsupport
  let e : X ↪ {y : (⊤ : Opens X) | t y ≠ 0} :=
    ⟨fun x ↦ ⟨⟨x, by trivial⟩, by simp [ht x]⟩, fun x y hxy ↦ by
      simpa using congrArg (fun z : {y : (⊤ : Opens X) | t y ≠ 0} => z.1.1) hxy⟩
  have : Finite {y : (⊤ : Opens X) | t y ≠ 0} := hsupport.to_subtype
  have : Finite X := Finite.of_injective e e.injective
  exact not_finite X

/-- Companion to Example 6.7.6: on an infinite discrete space, the pointwise direct-sum presheaf
with constant fiber `ℤ` does not satisfy the sheaf condition. -/
theorem pointwiseDirectSumPresheaf_not_isSheaf_of_infinite_discrete
    [DiscreteTopology X] [Infinite X] :
    ¬ (pointwiseDirectSumPresheaf (fun _ : X ↦ ℤ)).IsSheaf := by
  classical
  intro hsheaf
  let F := pointwiseDirectSumPresheaf (fun _ : X ↦ ℤ)
  let U : X → Opens X := fun x ↦ ⟨{x}, isOpen_discrete _⟩
  let sf : ∀ x : X, F.obj (Opposite.op (U x)) := fun x ↦
    DFinsupp.single ⟨x, by
      change x ∈ ({x} : Set X)
      simp⟩ (1 : ℤ)
  let Fsh : X.Sheaf AddCommGrpCat := ⟨F, hsheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F U sf := by
    intro x y
    ext z
    -- On a point of `U x ⊓ U y`, both singleton sections evaluate at the unique common point.
    have hz_x : z.1 = x := by
      simpa [U] using z.2.1
    have hz_y : z.1 = y := by
      simpa [U] using z.2.2
    have hleft :
        ((F.map (Opens.infLELeft (U x) (U y)).op) (sf x)) z = 1 := by
      rw [pointwiseDirectSumPresheaf_map_apply]
      have hindex :
          (⟨z, (Opens.infLELeft (U x) (U y)).le z.2⟩ : U x) =
            ⟨x, by
              change x ∈ ({x} : Set X)
              simp⟩ := by
        ext
        exact hz_x
      rw [hindex]
      simp [sf]
    have hright :
        ((F.map (Opens.infLERight (U x) (U y)).op) (sf y)) z = 1 := by
      rw [pointwiseDirectSumPresheaf_map_apply]
      have hindex :
          (⟨z, (Opens.infLERight (U x) (U y)).le z.2⟩ : U y) =
            ⟨y, by
              change y ∈ ({y} : Set X)
              simp⟩ := by
        ext
        exact hz_y
      rw [hindex]
      simp [sf]
    exact hleft.trans hright.symm
  have hcover : (⊤ : Opens X) ≤ iSup U := by
    -- Every point belongs to its own singleton open, so the singleton opens cover `⊤`.
    intro x hx
    simp [U]
  obtain ⟨t, ht, -⟩ := Fsh.existsUnique_gluing' (U := U) (V := (⊤ : Opens X))
    (iUV := fun x ↦ homOfLE (by
      intro y hy
      trivial)) hcover sf hcompat
  have ht_one : ∀ x : X, t ⟨x, by trivial⟩ = 1 := by
    intro x
    -- Evaluating the gluing on the singleton cover recovers the prescribed local section.
    have hx := congrArg (fun g => g ⟨x, by simp [U]⟩) (ht x)
    simpa [Fsh, F, sf, U] using hx
  -- The glued section is everywhere `1`, hence has infinite support, contradicting `DFinsupp`.
  exact global_support_infinite_of_all_ones t ht_one t.finite_support

end
