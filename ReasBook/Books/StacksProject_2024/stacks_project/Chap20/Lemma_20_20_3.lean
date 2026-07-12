import StacksProject_2024.Chap06.Lemma_6_31_7
import StacksProject_2024.Chap06.Definition_6_7_4
import StacksProject_2024.Chap20.ExtensionByZeroConstantIntegerSheaf

-- Declarations for this item will be appended below by the statement pipeline.

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
  `CompactOpens`,
  `QuasiSeparatedSpace`,
  `j!ℤ[U]`,
  `RelSeries`,
  `Subobject.ofLE`,
  `cokernel`,
  `ShortComplex.ShortExact`;
- best owner abstractions:
  `CompactOpens X` for quasi-compact opens and `QuasiSeparatedSpace X` for their stability under
  binary intersections, together with the direct compact-open specialization
  `j!ℤ[U.toOpens]` of the lower-shriek constant integer sheaf notation `j!ℤ[U]`,
  `RelSeries` for finite filtrations of subobjects,
  `ShortComplex.ShortExact` for the exact-sequence condition on a quotient,
  the direct quotient `cokernel (Subobject.ofLE F₁ F₂ h)` for successive quotients of the
  filtration;
- source/core/bridge triage:
  `source-facing`: finite generation by finitely many quasi-compact local generators and the
  existence of a finite filtration with successive quotients of the specified form;
  `core/canonical`: the lower-shriek constant integer sheaf written as `j!ℤ[U]`,
  `ShortComplex.ShortExact`, and the direct cokernel quotient
  `cokernel (Subobject.ofLE F₁ F₂ h)`;
  `bridge/view`: the compact-open specialization `j!ℤ[U.toOpens]`.
- primitive data versus derived API: the opens `U`, `V`, the comparison maps, and the filtration
  step predicate on successive subquotients are genuine source-level data here; the finite chain
  itself should therefore use the canonical owner `RelSeries`, while the ambient coproduct object
  for finitely many generators is derived canonical data and should therefore use the finite
  coproduct owner directly rather than an arbitrary cofan witness. -/

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Helper for Lemma 20.20.3: once the threshold stages and their adjacent witnesses are known,
they package directly into a finite relation series. This is the assembly step needed after the
source-proof normalization of the generator family. -/
private theorem relSeries_of_chain
    {α : Type u} {r : SetRel α α} {n : ℕ}
    (c : Fin (n + 1) → α)
    (hstep : ∀ i : Fin n, (c i.castSucc, c i.succ) ∈ r) :
    ∃ s : RelSeries r, s.head = c 0 ∧ s.last = c (Fin.last n) := by
  -- The data already match the `RelSeries` structure, so only the endpoint identifications remain.
  refine ⟨RelSeries.mk n c hstep, ?_⟩
  constructor <;> rfl

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Helper for Lemma 20.20.3: on a subsingleton type, any two chosen endpoints are connected by
the singleton `RelSeries`. This handles the degenerate zero-object branch of the filtration. -/
private theorem relSeries_of_subsingleton
    {α : Type u} {r : SetRel α α} [Subsingleton α] (a b : α) :
    ∃ s : RelSeries r, s.head = a ∧ s.last = b := by
  -- The unique available point gives a one-term relation series, and both endpoints coincide.
  refine ⟨RelSeries.singleton r a, ?_⟩
  constructor
  · simp
  · simpa using (show a = b from Subsingleton.elim _ _)

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Helper for Lemma 20.20.3: a single relation step already gives a two-term `RelSeries`. This
is the minimal packaging used once one threshold quotient has been identified. -/
private theorem relSeries_of_step
    {α : Type u} {r : SetRel α α} {a b : α} (hab : (a, b) ∈ r) :
    ∃ s : RelSeries r, s.head = a ∧ s.last = b := by
  -- Start with the singleton series at `a` and append the given relation step to `b`.
  refine ⟨(RelSeries.singleton r a).snoc b (by simpa using hab), ?_⟩
  constructor <;> simp

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Helper for Lemma 20.20.3: after a verified prefix filtration ending at `b`, one more relation
step appends a new last stage `c`. This is the final assembly move for any threshold-by-threshold
construction. -/
private theorem relSeries_snoc_exists
    {α : Type u} {r : SetRel α α} {a b c : α}
    (s : RelSeries r) (hhead : s.head = a) (hlast : s.last = b) (hbc : (b, c) ∈ r) :
    ∃ t : RelSeries r, t.head = a ∧ t.last = c := by
  -- Append the last relation step to the existing chain and read off the endpoints by simp.
  refine ⟨s.snoc c (by simpa [hlast] using hbc), ?_⟩
  constructor
  · simpa [hhead]
  · simp

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Helper for Lemma 20.20.3: an epimorphism out of the empty compact-open coproduct forces the
target sheaf to be zero. This is the base case for induction on the number of generators. -/
private theorem isZero_of_emptyGeneratorPresentation
    (Y : X.Sheaf AddCommGrpCat.{u}) (U : Fin 0 → CompactOpens X)
    (π : (∐ fun i : Fin 0 ↦ j!ℤ[(U i).toOpens]) ⟶ Y) [Epi π] :
    Limits.IsZero Y := by
  -- The empty finite coproduct is the zero sheaf, so an epi from it has zero target.
  have hSource :
      Limits.IsZero ((∐ fun i : Fin 0 ↦ j!ℤ[(U i).toOpens]) : X.Sheaf AddCommGrpCat.{u}) := by
    simpa using (Limits.isZero_zero (X.Sheaf AddCommGrpCat.{u}))
  exact Limits.IsZero.of_epi π hSource

/-- Helper for Lemma 20.20.3: a top section of a sheaf over `Y` determines the unique morphism
from `constantIntegerSheaf Y` classified by that section. This packages the constant-generator
interface used later when the source proof has reduced to constant sections on compact opens. -/
private noncomputable def constantIntegerHomOfTopSection
    (Y : TopCat.{u}) [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    (G : Y.Sheaf AddCommGrpCat.{u})
    (s : G.1.obj (Opposite.op (⊤ : Opens Y))) :
    constantIntegerSheaf Y ⟶ G :=
  (constantIntegerSheaf_hom_equiv_top_section Y G).symm s

/-- Helper for Lemma 20.20.3: `constantIntegerHomOfTopSection` is inverse to the top-section
classification equivalence. This is the rewrite used when a constant-piece refinement is converted
back into a generator morphism. -/
private theorem constantIntegerHomOfTopSection_spec
    (Y : TopCat.{u}) [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    (G : Y.Sheaf AddCommGrpCat.{u})
    (s : G.1.obj (Opposite.op (⊤ : Opens Y))) :
    constantIntegerSheaf_hom_equiv_top_section Y G
        (constantIntegerHomOfTopSection (Y := Y) G s) = s := by
  -- Unfold the chosen inverse and cancel the top-section classification equivalence.
  simp [constantIntegerHomOfTopSection]

/-- Helper for Lemma 20.20.3: a generator morphism `j!ℤ[U.toOpens] ⟶ F` corresponds, via the
open-subset extension-by-zero adjunction, to a top section of the restricted subsheaf on `U`. -/
private noncomputable def generatorMapToRestrictedSection
    (F : Subobject (constantIntegerSheaf X)) (U : CompactOpens X)
    (ψ : j!ℤ[U.toOpens] ⟶ F) :
    (Subobject.underlying.obj (Subobject.restrict F U.toOpens)).1.obj
      (Opposite.op (⊤ : Opens (extensionByZeroOpenSubsetSpace U.toOpens))) := by
  let ψrestricted :
      constantIntegerSheaf (extensionByZeroOpenSubsetSpace U.toOpens) ⟶
        (TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (extensionByZeroOpenSubsetInclusion U.toOpens)).obj F :=
    (OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction
      (C := AddCommGrpCat.{u}) U.toOpens).homEquiv _ _ ψ
  let ψintoRestrict :
      constantIntegerSheaf (extensionByZeroOpenSubsetSpace U.toOpens) ⟶
        Subobject.underlying.obj (Subobject.restrict F U.toOpens) :=
    ψrestricted ≫
      (Subobject.underlyingIso
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (extensionByZeroOpenSubsetInclusion U.toOpens)).map F.arrow)).inv
  -- First move the generator along the adjunction, then rewrite the pulled-back arrow through the
  -- canonical underlying object of the restricted subobject.
  exact
    constantIntegerSheaf_hom_equiv_top_section
      (extensionByZeroOpenSubsetSpace U.toOpens)
      (Subobject.underlying.obj (Subobject.restrict F U.toOpens))
      ψintoRestrict

/-- Helper for Lemma 20.20.3: a locally constant integer-valued function on a compact space takes
only finitely many values. This is the finite-range input for the fiber-by-fiber refinement route
in the source proof. -/
private theorem locallyConstantIntegerRangeFinite
    {Y : TopCat.{u}} [CompactSpace Y] (ℓ : LocallyConstant Y (ULift ℤ)) :
    Set.Finite (Set.range ℓ) := by
  -- The compact-domain hypothesis is exactly the standard finiteness input for locally constant
  -- functions.
  simpa using ℓ.range_finite

/-- Helper for Lemma 20.20.3: the subtype of a compact open inherits the canonical compact-space
instance. This is the local compactness input used when a generator is normalized over its support.
-/
private theorem compactSpaceOfCompactOpen (U : CompactOpens X) :
    CompactSpace ↥(U.toOpens) := by
  -- Reinterpret the compactness of `U` as a `CompactSpace` structure on its subtype.
  exact isCompact_iff_compactSpace.mp U.isCompact

/-- Helper for Lemma 20.20.3: a value fiber of a locally constant integer-valued function on a
compact open support is again a compact open of the ambient space lying under that support. -/
private theorem fiberCompactOpenUnderLocallyConstantValue
    (U : CompactOpens X) (ℓ : LocallyConstant U.toOpens (ULift ℤ)) (z : ULift ℤ) :
    ∃ W : CompactOpens X, W ≤ U ∧ ∀ x : U.toOpens, x.1 ∈ (W : Set X) ↔ ℓ x = z := by
  -- First package the fiber as a compact open inside the open subspace `U`.
  letI : CompactSpace ↥(U.toOpens) := compactSpaceOfCompactOpen (X := X) U
  let hFiber : IsClopen {x : U.toOpens | ℓ x = z} :=
    ℓ.isLocallyConstant.isClopen_fiber z
  let Wsub : CompactOpens U.toOpens :=
    ⟨⟨{x : U.toOpens | ℓ x = z}, hFiber.1.isCompact⟩, hFiber.2⟩
  let W : CompactOpens X :=
    Wsub.map (extensionByZeroOpenSubsetInclusion U.toOpens) continuous_subtype_val
      U.toOpens.isOpenEmbedding.isOpenMap
  -- Then map that compact open along the open embedding into `X` and read off the fiber equation.
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    rw [CompactOpens.coe_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  · intro x
    constructor
    · intro hx
      rw [CompactOpens.coe_map] at hx
      rcases hx with ⟨y, hy, hyx⟩
      have hxy : y = x := Subtype.ext hyx
      have hyFiber : ℓ y = z := by
        simpa [Wsub] using hy
      simpa [hxy] using hyFiber
    · intro hx
      rw [CompactOpens.coe_map]
      refine ⟨x, ?_, rfl⟩
      simpa [Wsub] using hx

-- Proof sketch: rewrite finite generation of the subsheaf as an epimorphism from a finite
-- coproduct of sheaves `j!ℤ[(U i).toOpens]` with quasi-compact `U i`, refine the
-- generators by finite intersections so the local integer sections satisfy the gcd condition from
-- the Stacks Project proof, and then filter by the allowed integer values. Each successive quotient
-- is generated by one integer over a quasi-compact union, and its kernel is generated by the same
-- integer over a quasi-compact open, yielding the displayed short exact sequence for the direct
-- quotient `cokernel (Subobject.ofLE Fᵢ Fᵢ₊₁ h)`.

section

variable (F : Subobject (constantIntegerSheaf X))

local notation "UnderlyingSubsheaf" =>
  Subobject (Subobject.underlying.obj F)

/-- Lemma 20.20.3: if intersections of quasi-compact opens in `X` are quasi-compact and
`ℱ ⊆ constantIntegerSheaf X` is generated by finitely many sections over quasi-compact opens, then
`ℱ` admits a finite filtration by abelian subsheaves whose successive quotients fit into short
exact sequences
`0 ⟶ j!ℤ[V.toOpens] ⟶ j!ℤ[U.toOpens] ⟶
cokernel (Subobject.ofLE ℱᵢ₋₁ ℱᵢ h) ⟶ 0`
with `U` and `V` quasi-compact opens. The binary intersection hypothesis is carried canonically by
`[QuasiSeparatedSpace X]`, and the successive-quotient condition is exposed by the companion
theorem `extensionByZeroConstantIntegerFiltrationStep_iff`. -/
@[stacks 0A38]
theorem exists_finite_extensionByZeroIntegerFiltration_of_finitely_generated_subsheaf
    [QuasiSeparatedSpace X]
    (hF :
      ∃ (n : ℕ) (U : Fin n → CompactOpens X),
        ∃ π :
          (∐ fun i : Fin n ↦ j!ℤ[(U i).toOpens]) ⟶ F,
          Epi π) :
    let r : SetRel UnderlyingSubsheaf UnderlyingSubsheaf :=
      fun p ↦
        ∃ h₁₂ : p.1 ≤ p.2,
          ∃ U V : CompactOpens X,
            ∃ (ι : j!ℤ[V.toOpens] ⟶ j!ℤ[U.toOpens])
              (π : j!ℤ[U.toOpens] ⟶ cokernel (Subobject.ofLE p.1 p.2 h₁₂))
              (hιπ : ι ≫ π = 0),
              (ShortComplex.mk ι π hιπ).ShortExact
    ∃ s : RelSeries r,
      s.head = ⊥ ∧ s.last = ⊤ := by
  let r : SetRel UnderlyingSubsheaf UnderlyingSubsheaf :=
    fun p ↦
      ∃ h₁₂ : p.1 ≤ p.2,
        ∃ U V : CompactOpens X,
          ∃ (ι : j!ℤ[V.toOpens] ⟶ j!ℤ[U.toOpens])
            (π : j!ℤ[U.toOpens] ⟶ cokernel (Subobject.ofLE p.1 p.2 h₁₂))
            (hιπ : ι ≫ π = 0),
            (ShortComplex.mk ι π hιπ).ShortExact
  change ∃ s : RelSeries r, s.head = ⊥ ∧ s.last = ⊤
  rcases hF with ⟨n, U, π, hπ⟩
  letI : Epi π := hπ
  cases n with
  | zero =>
      -- Proof comment: if there are no generators, the presentation map comes from the empty
      -- coproduct, hence the target subsheaf object is zero and its subobject lattice collapses.
      have hZero : Limits.IsZero (Subobject.underlying.obj F) :=
        isZero_of_emptyGeneratorPresentation (X := X) (Y := F) U π
      have hSub : Subsingleton UnderlyingSubsheaf :=
        Subobject.subsingleton_of_isZero hZero
      letI : Subsingleton UnderlyingSubsheaf := hSub
      exact relSeries_of_subsingleton (r := r) (a := (⊥ : UnderlyingSubsheaf))
        (b := (⊤ : UnderlyingSubsheaf))
  | succ n =>
      -- Route correction: the previous last-generator induction normalized the problem to an
      -- arbitrary kernel statement for maps `j!ℤ[U.toOpens] ⟶ Q`, but such kernels can be
      -- multiplicity subsheaves and need not be of the form `j!ℤ[V.toOpens]`. The source-faithful
      -- route is instead to refine the presentation to positive constant generators with the
      -- pointwise gcd-attainment property and then filter by threshold values.
      -- The constant-piece endpoint of the source normalization is now exposed by
      -- `constantIntegerHomOfTopSection`: once a generator is rewritten as a constant section on a
      -- compact open, it can be converted back to a generator morphism without any further
      -- low-level sheaf bookkeeping.
      -- The first bridge in that normalization is now available as
      -- `generatorMapToRestrictedSection`, which rewrites each generator as a top section on the
      -- restricted subsheaf over its supporting compact open.
      -- The finite-range side of the source proof is also now isolated theorem-locally:
      -- `compactSpaceOfCompactOpen` supplies the compactness instance on the support, and
      -- `fiberCompactOpenUnderLocallyConstantValue` packages each attained value fiber as a new
      -- compact open beneath that support.
      -- TODO: the only remaining structural blocker is the section-level bridge
      -- `restrictedGeneratorLocallyConstant`. It should compose
      -- `generatorMapToRestrictedSection` with the restricted-subobject inclusion into the
      -- pulled-back ambient constant sheaf, compare that top section with a section of
      -- `constantIntegerSheaf X` over `U.toOpens`, forget to `Type`, and transport through
      -- `constantSheafToLocallyConstantSheaf_app_isIso`. After that bridge is proved, the finite
      -- range and compact-open fiber decomposition are already in place to resume the
      -- threshold-by-threshold exact-sequence construction.
      sorry

/-- The step relation in Lemma 20.20.3 is exactly the existence of the displayed compact-open
short exact sequence for the successive quotient. -/
theorem extensionByZeroConstantIntegerFiltrationStep_iff
    (F₁ F₂ : UnderlyingSubsheaf) :
    let r : SetRel UnderlyingSubsheaf UnderlyingSubsheaf :=
      fun p ↦
        ∃ h₁₂ : p.1 ≤ p.2,
          ∃ U V : CompactOpens X,
            ∃ (ι : j!ℤ[V.toOpens] ⟶ j!ℤ[U.toOpens])
              (π : j!ℤ[U.toOpens] ⟶ cokernel (Subobject.ofLE p.1 p.2 h₁₂))
              (hιπ : ι ≫ π = 0),
              (ShortComplex.mk ι π hιπ).ShortExact
    ((F₁, F₂) ∈ r) ↔
      ∃ h₁₂ : F₁ ≤ F₂,
        ∃ U V : CompactOpens X,
          ∃ (ι : j!ℤ[V.toOpens] ⟶ j!ℤ[U.toOpens])
            (π : j!ℤ[U.toOpens] ⟶ cokernel (Subobject.ofLE F₁ F₂ h₁₂))
            (hιπ : ι ≫ π = 0),
            (ShortComplex.mk ι π hιπ).ShortExact := by
  rfl

end

end
