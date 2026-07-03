import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_11_1 (from Chap06) -/
open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace

universe u

section

variable {X : TopCat} (ℱ : TopCat.Sheaf (Type u) X) (U : Opens X)

/- Domain-style sampling for Lemma 6.11.1:
- primary domain: sheaf sections and the sheafification-unit comparison with stalk families on a
  topological space;
- sampled owner declarations:
  `TopCat.Presheaf.section_ext`,
  `TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- best owner abstraction: the canonical sheaf extensionality theorem `section_ext`; the other
  sampled declarations are adjacent owner API for deriving sectionwise injectivity from stalk maps,
  but the present source-facing statement is directly about equality of stalk germs;
- primitive data: the sheaf `ℱ` and the open subset `U`;
- derived API: the map `ℱ.presheaf.toSheafify.app (op U)` and its underlying stalk-family
  function.

Source/core/bridge triage:
- `source-facing`: injectivity of the canonical map from sections on `U` to the family of stalks
  over points of `U`;
- `core/canonical`: `TopCat.Presheaf.section_ext`;
- `bridge/view`: `ℱ.presheaf.toSheafify.app (op U)`. -/
/-- Lemma 6.11.1: for every open subset `U` of `X`, the canonical map from sections of `ℱ` on
`U` to the family of stalks `(ℱ_x)_{x ∈ U}` is injective. -/
theorem sectionToStalkFamily_injective :
    Function.Injective (fun s ↦ (ℱ.presheaf.toSheafify.app (op U) s).1) := by
  intro s t hst
  exact section_ext ℱ U s t fun x hx ↦ congrFun hst ⟨x, hx⟩

end

/-! ### Definition_6_11_2 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Definition 6.11.2:
- primary domain: separated set-valued presheaves and sheafification on a topological space;
- sampled owner API:
  `Presieve.IsSeparated`,
  `Presheaf.IsLocallyInjective`,
  `TopCat.Presheaf.IsSheaf.section_ext`,
  `CategoryTheory.toSheafify`;
- best owner abstraction: the canonical site-theoretic predicate
  `Presieve.IsSeparated (Opens.grothendieckTopology X) ℱ`;
- primitive data: the presheaf `ℱ`;
- derived API: injectivity of the canonical map on sections into the sheafification and the
  specialization to sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks Project criterion via injectivity of the canonical map to the family
  of stalk germs;
- `core/canonical`: `Presieve.IsSeparated (Opens.grothendieckTopology X) ℱ`;
- `bridge/view`: the objectwise injectivity of `ℱ.toSheafify`. -/

/- Definition 6.11.2: the canonical owner notion for a separated set-valued presheaf on `X` is
`Presieve.IsSeparated (Opens.grothendieckTopology X)`. -/
recall Presieve.IsSeparated

/-- Definition 6.11.2: a set-valued presheaf on `X` is separated, in the canonical site-theoretic
sense for `Opens.grothendieckTopology X`, if and only if for every open subset `U` the canonical
map from sections on `U` to the family of germs in the stalks over points of `U`, namely the
underlying function of `(ℱ.toSheafify.app (op U))`, is injective. -/
theorem isSeparated_iff_injective_toStalkFamily (ℱ : X.Presheaf (Type u)) :
    Presieve.IsSeparated J ℱ ↔
      ∀ U : Opens X, Function.Injective (fun s ↦ (ℱ.toSheafify.app (op U) s).1) := by
  constructor
  · intro hℱ U s t hst
    -- Equality of the stalk-family images gives, at each point of `U`, a neighborhood on which the
    -- two sections agree.
    choose V hxV i₁ i₂ hV using fun x : U ↦
      ℱ.germ_eq x.1 x.2 x.2 s t (congrFun hst x)
    -- The pointwise neighborhoods form a covering presieve, so separatedness on the Grothendieck
    -- topology upgrades the local equalities to equality of the original sections.
    have hsep : Presieve.IsSeparatedFor ℱ (.ofArrows V i₁) := by
      rw [Presieve.isSeparatedFor_iff_generate]
      exact hℱ _ (by
        intro x hx
        exact ⟨V ⟨x, hx⟩, i₁ ⟨x, hx⟩, Sieve.ofArrows_mk _ _ _, hxV ⟨x, hx⟩⟩)
    exact hsep.ext fun _ _ hf ↦ by
      rcases hf with ⟨x⟩
      simpa [Subsingleton.elim (i₂ x) (i₁ x)] using hV x
  · intro hℱ U S hS x t₁ t₂ ht₁ ht₂
    -- Sheafification is a sheaf, hence separated on every covering sieve.
    have hsep : Presieve.IsSeparatedFor ℱ.sheafify.presheaf S.arrows :=
      ((isSheaf_iff_isSheaf_of_type J ℱ.sheafify.presheaf).1 ℱ.sheafify.2).isSeparated S hS
    -- Local equality along `S` therefore forces equality after applying the unit to sheafification,
    -- and the assumed injectivity on `U` pulls the conclusion back to `ℱ`.
    have hEq :
        ℱ.toSheafify.app (op U) t₁ = ℱ.toSheafify.app (op U) t₂ :=
      hsep (x.map ℱ.toSheafify) _ _ (ht₁.map ℱ.toSheafify) (ht₂.map ℱ.toSheafify)
    exact hℱ U (congrArg Subtype.val hEq)

end TopCat.Presheaf

/-! ### Example_6_11_3 (from Chap06) -/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open TopCat.Presheaf
open scoped TopCat

universe u

noncomputable section

/- Domain-style sampling for Example 6.11.3:
- primary domain: constant set-valued presheaves and sheaves on a topological space, together with
  their stalks;
- sampled owner API:
  `Functor.const`,
  `TopCat.Presheaf.Γgerm`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`,
  `CategoryTheory.constantSheaf`;
- best owner abstraction: the canonical stalk comparison
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, specialized to the constant presheaf;
- primitive data: the space `X`, the value type `A`, and the point `x : X`;
- derived API: the identification `A ≅ (A_p)_x` via `Γgerm` for the constant presheaf, and the
  composite map `A ⟶ \underline{A}_x`.

Source/core/bridge triage:
- `source-facing`: the map `(A_p)_x ⟶ \underline{A}_x` induced by sheafification, and the
  companion composite `A ⟶ \underline{A}_x`;
- `core/canonical`: `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- `bridge/view`: `TopCat.Presheaf.Γgerm` for the constant presheaf.
-/

section

variable (X : TopCat.{u}) (A : Type u)

/-- Helper for Example 6.11.3: the canonical stalk map of the constant presheaf is an isomorphism. -/
theorem constantPresheafΓgerm_isIso (x : X) :
    IsIso (Γgerm (A ₚ X) x) := by
  -- Collapse the stalk colimit along the top neighborhood of `x`.
  let F : (OpenNhds x)ᵒᵖ ⥤ Type u := (OpenNhds.inclusion x).op ⋙ (A ₚ X)
  let j : (OpenNhds x)ᵒᵖ := op (⊤ : OpenNhds x)
  have hj : IsInitial j := by
    refine IsInitial.ofUniqueHom (fun Y ↦ ?_) (fun Y m ↦ ?_)
    · exact (homOfLE le_top).op
    · exact Subsingleton.elim _ _
  -- Once the stalk is identified with this colimit, the initial object computes it.
  change IsIso (colimit.ι F j)
  letI : ∀ (i j : (OpenNhds x)ᵒᵖ) (f : i ⟶ j), IsIso (F.map f) := by
    intro i j f
    dsimp [F]
    infer_instance
  letI : HasColimit F := hasColimit_of_domain_hasInitial
  exact isIso_ι_of_isInitial hj F

/-- Helper for Example 6.11.3: the global germ map of the constant presheaf is bijective on every stalk. -/
theorem constantPresheafΓgerm_bijective (x : X) :
    Function.Bijective (Γgerm (A ₚ X) x) := by
  -- Extract the underlying equivalence from the stalk isomorphism.
  haveI := constantPresheafΓgerm_isIso X A x
  exact (asIso (Γgerm (A ₚ X) x)).toEquiv.bijective

end

section

variable (X : TopCat.{u})
variable (A : Type u)

local notation "J" => Opens.grothendieckTopology X
local notation "hTop" =>
  IsTerminal.ofUniqueHom (fun U : Opens X ↦ Opens.leTop U) (fun U m ↦ Subsingleton.elim _ _)

/- Example 6.11.3: the canonical map `(A_p)_x ⟶ \underline{A}_x` is the specialization of the
owner theorem `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` to the constant presheaf.
-/
recall TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso

/- Source-facing specialization of the owner theorem to the constant presheaf `A_p`. -/
#check
  fun x : X ↦ stalkFunctor_map_unit_toSheafify_isIso x (Type u) (A ₚ X)

/-- Helper for Example 6.11.3: rewrite the canonical map to the constant-sheaf stalk through the stalk map of sheafification. -/
private theorem constantSheafΓgerm_eq (x : X) :
    (constantSheafAdj J (Type u) hTop).unit.app A ≫
        Γgerm ((constantSheaf J (Type u)).obj A).obj x =
      Γgerm (A ₚ X) x ≫
        (stalkFunctor (Type u) x).map (toSheafify J (A ₚ X)) := by
  -- The bridge is `stalkFunctor_map_germ` evaluated on the top open set.
  simpa using
    (stalkFunctor_map_germ (⊤ : Opens X) x True.intro
      (toSheafify J (A ₚ X))).symm

/-- Helper for Example 6.11.3: the composite `A = (A_p)_x ⟶ \underline{A}_x` is an isomorphism. -/
theorem constantSheafΓgerm_isIso (x : X) :
    IsIso
      ((constantSheafAdj J (Type u) hTop).unit.app A ≫
        Γgerm ((constantSheaf J (Type u)).obj A).obj x) := by
  -- Rewrite the target map as the constant-presheaf germ map followed by sheafification on stalks.
  rw [constantSheafΓgerm_eq X A x]
  -- Both factors are canonical isomorphisms, so their composite is as well.
  exact IsIso.comp_isIso' (constantPresheafΓgerm_isIso X A x)
    (stalkFunctor_map_unit_toSheafify_isIso x (Type u) (A ₚ X))

/-- Example 6.11.3: the composite map `A ⟶ \underline{A}_x` is bijective. -/
theorem constantSheafΓgerm_bijective (x : X) :
    Function.Bijective
      ((constantSheafAdj J (Type u) hTop).unit.app A ≫
        Γgerm ((constantSheaf J (Type u)).obj A).obj x) := by
  -- Convert the composite isomorphism into an equivalence of underlying functions.
  haveI := constantSheafΓgerm_isIso X A x
  let e := asIso
    ((constantSheafAdj J (Type u) hTop).unit.app A ≫
      Γgerm ((constantSheaf J (Type u)).obj A).obj x)
  exact e.toEquiv.bijective

end

/-! ### Example_6_11_4 (from Chap06) -/
open Opposite
open TopologicalSpace
open scoped ContDiff

noncomputable section

section

open Manifold

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "𝒪∞" => smoothSheaf (𝓘(ℝ, E)) 𝓘(ℝ) E ℝ

/- Domain-style sampling for Example 6.11.4:
- primary domain: stalks of concrete presheaves on topological spaces, specialized here to the
  smooth real-valued sheaf on `ℝ^n`;
- sampled owner API:
  `TopCat.Presheaf.germ_exist`,
  `TopCat.Presheaf.germ_eq`,
  `TopCat.Presheaf.germ_ext`,
  `smoothSheaf.eval_germ`;
- best owner abstraction: the stalk API on `TopCat.Presheaf`, with `germ_eq` and `germ_ext`
  controlling equality of germs and `germ_exist` providing representatives;
- primitive data: opens `U, V : Opens E`, a point `x : E` with `x ∈ U` and `x ∈ V`, and sections
  `f` and `g` of the smooth sheaf on `U` and `V`;
- derived API: no new public wrapper is needed; Example 6.11.4 is a direct specialization of the
  owner theorems above.

Source/core/bridge triage:
- `source-facing`: two smooth functions defined near `x` determine the same stalk element exactly
  when they agree after restriction to some smaller neighbourhood of `x`;
- `core/canonical`: `TopCat.Presheaf.germ_eq` and `TopCat.Presheaf.germ_ext`;
- `bridge/view`: the specialization from an arbitrary concrete presheaf to the smooth-function
  sheaf on `ℝ^n`. -/

/-
Every element of the stalk of the smooth real-valued sheaf on `ℝ^n` is represented by a smooth
function defined on some open neighbourhood of the point. This is the specialization of the
canonical stalk-representative theorem `TopCat.Presheaf.germ_exist`.
-/
recall TopCat.Presheaf.germ_exist

/- Companion recall: equality of germs in any concrete presheaf is detected after restricting to a
smaller neighbourhood. -/
recall TopCat.Presheaf.germ_eq

/- Companion recall: agreement of restrictions on a smaller neighbourhood gives equality of germs.
-/
recall TopCat.Presheaf.germ_ext

/-- Example 6.11.4: two smooth functions defined near `x` determine the same stalk element if and
only if they agree after restriction to some smaller neighbourhood of `x`. This is the direct
smooth-sheaf specialization of `TopCat.Presheaf.germ_eq` and `TopCat.Presheaf.germ_ext`. -/
theorem smoothSheaf_germ_eq_iff
    {U V : Opens E} (x : E) (hxU : x ∈ U) (hxV : x ∈ V)
    (f : 𝒪∞.presheaf.obj (op U)) (g : 𝒪∞.presheaf.obj (op V)) :
    𝒪∞.presheaf.germ U x hxU f = 𝒪∞.presheaf.germ V x hxV g ↔
      ∃ (W : Opens E) (_ : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V),
        𝒪∞.presheaf.map iU.op f = 𝒪∞.presheaf.map iV.op g := by
  constructor
  · intro h
    exact 𝒪∞.presheaf.germ_eq x hxU hxV f g h
  · rintro ⟨W, hxW, iU, iV, h⟩
    exact 𝒪∞.presheaf.germ_ext W hxW iU iV h

end

/-! ### Example_6_11_5 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace Filter TopCat
open CategoryTheory.Limits
open scoped Topology

universe u

noncomputable section

/-
Domain-style sampling for Example 6.11.5:
- primary domain: sheaves of set-valued functions on a topological space, their stalks, and stalk
  evaluation maps;
- sampled owner API:
  `TopCat.presheafToTypes`,
  `TopCat.sheafToTypes`,
  `TopCat.presheafToType`,
  `TopCat.stalkToFiber`;
- owner abstraction:
  the core/canonical owners are the sheaves of all functions `TopCat.sheafToTypes` /
  `TopCat.sheafToType`, with `TopCat.stalkToFiber` giving the canonical evaluation pattern for
  local-predicate subsheaves;
- primitive-vs-derived split:
  primitive data are the family `A : X → Type u`, the point `x : X`, and later the sequence
  `sequence : ℕ → X`;
  the source-facing evaluation map on stalks is defined directly on the owner
  `TopCat.sheafToTypes`, following the same colimit-level evaluation pattern as
  `TopCat.stalkToFiber`, while the binary-tail map is derived from a cocone into
  `Filter.Germ atTop Bool`;
- source/core/bridge triage:
  `source-facing`: `dependentFunctionStalkToFiber` and `stalkToBinaryTail`;
  `core/canonical`: `TopCat.sheafToTypes`, `TopCat.sheafToType`, `TopCat.stalkToFiber`,
    `TopCat.stalkToFiber_germ`;
  `bridge/view`: the neighborhood cocone encoding eventual tails.
-/

section

variable {X : TopCat.{u}} (A : X → Type u) (x : X)

/-- Example 6.11.5 (1): for the sheaf `U ↦ ∏_{y ∈ U} A_y` on a topological space `X`, there is a
canonical evaluation map from the stalk at `x` to the fiber `A_x`. This is the direct
all-functions analogue of mathlib's canonical `TopCat.stalkToFiber`. -/
noncomputable def dependentFunctionStalkToFiber :
    (X.sheafToTypes A).presheaf.stalk x ⟶ A x :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf)
    { pt := A x
      ι :=
        { app := fun U f ↦ f ⟨x, (unop U).2⟩
          naturality := by
            intro U V i
            funext f
            rfl } }

-- Proof sketch: this is the defining evaluation formula for the colimit cocone used in
-- `dependentFunctionStalkToFiber`.
/-- The canonical map from the stalk to the fiber sends a germ to the value of the section at `x`.
-/
theorem dependentFunctionStalkToFiber_germ (U : Opens X) (hx : x ∈ U)
    (f : (X.sheafToTypes A).presheaf.obj (op U)) :
    dependentFunctionStalkToFiber A x ((X.sheafToTypes A).presheaf.germ U x hx f) = f ⟨x, hx⟩ := by
  simp [Presheaf.germ, dependentFunctionStalkToFiber]

-- Proof sketch: if a stalk element were represented by a germ over some neighborhood `U`, then the
-- assumed point `y ∈ U` with empty fiber would force that section set to be empty, so no germ can
-- exist and the colimit defining the stalk is empty.
/-- If every neighborhood of `x` contains a point with empty fiber, then the stalk at `x` is empty.
-/
theorem isEmpty_stalk_of_exists_empty_fiber_in_every_openNhds
    (h : ∀ U : OpenNhds x, ∃ y : U.1, IsEmpty (A y)) :
    IsEmpty ((X.sheafToTypes A).presheaf.stalk x) := by
  refine ⟨fun t ↦ ?_⟩
  obtain ⟨U, hxU, f, rfl⟩ := (X.sheafToTypes A).presheaf.germ_exist x t
  obtain ⟨y, hy⟩ := h ⟨U, hxU⟩
  exact hy.false (f y)

end

namespace Example_6_11_5

open Filter.Germ

section

variable {X : TopCat.{u}} {x : X} {sequence : ℕ → X}

private abbrev binaryNeighborhoodPresheaf (x : X) :=
  (OpenNhds.inclusion x).op ⋙ (X.sheafToType (ULift.{u} Bool)).presheaf

private theorem eventually_mem (sequence : ℕ → X)
    (hsequence : Tendsto sequence atTop (nhds x)) (U : OpenNhds x) :
    ∀ᶠ n : ℕ in atTop, sequence n ∈ U.1 := by
  exact hsequence (U.1.2.mem_nhds U.2)

/-- The leg of the cocone sending a neighborhood section around `x` to its eventual binary tail
along a sequence converging to `x`. -/
private def stalkToBinaryTailLeg (x : X) (sequence : ℕ → X) (U : (OpenNhds x)ᵒᵖ) :
    (binaryNeighborhoodPresheaf x).obj U ⟶
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool) := by
  classical
  intro f
  exact
    ((fun n : ℕ ↦
        if h : sequence n ∈ (unop U).1 then
          f ⟨sequence n, h⟩
        else
          ULift.up false) :
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool))

private theorem restrict_apply (x : X) (sequence : ℕ → X) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V)
    (f : (binaryNeighborhoodPresheaf x).obj U)
    (n : ℕ) (hn : sequence n ∈ (unop V).1) :
    ((binaryNeighborhoodPresheaf x).map i f) ⟨sequence n, hn⟩ =
      f ⟨sequence n, i.unop.le hn⟩ := rfl

private theorem stalkToBinaryTailLeg_naturality (x : X) (sequence : ℕ → X)
    (hsequence : Tendsto sequence atTop (nhds x))
    {U V : (OpenNhds x)ᵒᵖ}
    (i : U ⟶ V) :
    ((binaryNeighborhoodPresheaf x).map i) ≫ stalkToBinaryTailLeg x sequence V =
      stalkToBinaryTailLeg x sequence U := by
  classical
  funext f
  change
    ((fun n : ℕ ↦
        if h : sequence n ∈ (unop V).1 then
          ((binaryNeighborhoodPresheaf x).map i f) ⟨sequence n, h⟩
        else
          ULift.up false) :
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) =
      ((fun n : ℕ ↦
          if h : sequence n ∈ (unop U).1 then
            f ⟨sequence n, h⟩
          else
            ULift.up false) :
        Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool))
  apply coe_eq.2
  filter_upwards [eventually_mem sequence hsequence (unop V)] with n hn
  have hU : sequence n ∈ (unop U).1 := i.unop.le hn
  simp only [hn, hU]
  exact restrict_apply x sequence i f n hn

/-- The cocone realizing the map from the stalk at `x` to tails of binary sequences along
`sequence`. -/
private def stalkToBinaryTailCocone (x : X) (sequence : ℕ → X)
    (hsequence : Tendsto sequence atTop (nhds x)) :
    Cocone (binaryNeighborhoodPresheaf x) where
  pt := Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)
  ι :=
    { app := fun U ↦ stalkToBinaryTailLeg x sequence U
      naturality := fun _ _ i ↦
        stalkToBinaryTailLeg_naturality x sequence hsequence i }

-- Proof sketch: a section on a neighborhood of `∞` determines a binary sequence on all large
-- integers, hence a germ at `atTop`; the cocone above packages this eventual-equality class.
/-- A convergent sequence `sequence n → x` induces a canonical map from the stalk at `x` of the
sheaf of `{0,1}`-valued functions to the set of tails of binary sequences, encoded as germs in
`Filter.Germ atTop (ULift Bool)`. -/
noncomputable def stalkToBinaryTail (sequence : ℕ → X)
    (hsequence : Tendsto sequence atTop (nhds x)) :
    (X.sheafToType (ULift.{u} Bool)).presheaf.stalk x ⟶
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool) :=
  colimit.desc _ (stalkToBinaryTailCocone x sequence hsequence)

private def binarySectionOfSequence (sequence : ℕ → X) (b : ℕ → ULift.{u} Bool) :
    (X.sheafToType (ULift.{u} Bool)).presheaf.obj (op (⊤ : Opens X)) := by
  classical
  intro y
  exact
    if hy : y.1 ∈ Set.range sequence then
      b (Function.invFun sequence y.1)
    else
      ULift.up false

private theorem binarySectionOfSequence_apply (sequence : ℕ → X)
    (hsequence_injective : Function.Injective sequence)
    (b : ℕ → ULift.{u} Bool) (n : ℕ) :
    binarySectionOfSequence sequence b ⟨sequence n, by trivial⟩ = b n := by
  classical
  rw [binarySectionOfSequence]
  have hleft := Function.leftInverse_invFun hsequence_injective n
  simp [hleft]

/-- The stalk element determined by the global section attached to a binary sequence, with value
`false` away from the range of `sequence`. -/
private def stalkOfBinarySequence (x : X) (sequence : ℕ → X) (b : ℕ → ULift.{u} Bool) :
    (X.sheafToType (ULift.{u} Bool)).presheaf.stalk x :=
  (X.sheafToType (ULift.{u} Bool)).presheaf.germ (⊤ : Opens X) x (by trivial)
    (binarySectionOfSequence sequence b)

private theorem stalkToBinaryTailLeg_top (hsequence_injective : Function.Injective sequence)
    (b : ℕ → ULift.{u} Bool) :
    stalkToBinaryTailLeg x sequence (op ⟨(⊤ : Opens X), by trivial⟩)
        (binarySectionOfSequence sequence b) =
      (b : Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) := by
  classical
  apply coe_eq.2
  exact Filter.Eventually.of_forall fun n ↦ by
    have htop : sequence n ∈ (⊤ : Opens X) := by trivial
    simp [htop, binarySectionOfSequence_apply sequence hsequence_injective b n]

-- Proof sketch: for the global section attached to a binary sequence `b`, the induced tail germ is
-- exactly `b` itself, because the top open contains every term of the sequence.
/-- The stalk-to-tail map sends the germ of the global section attached to a binary sequence `b`
to the tail class of `b`. -/
private theorem stalkToBinaryTail_stalkOfBinarySequence
    (hsequence : Tendsto sequence atTop (nhds x))
    (hsequence_injective : Function.Injective sequence) (b : ℕ → ULift.{u} Bool) :
    stalkToBinaryTail sequence hsequence (stalkOfBinarySequence x sequence b) =
      (b : Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) := by
  classical
  rw [stalkOfBinarySequence, TopCat.Presheaf.germ, stalkToBinaryTail]
  simpa only [Types.Colimit.ι_desc_apply, stalkToBinaryTailCocone] using
    stalkToBinaryTailLeg_top hsequence_injective b

-- Proof sketch: every germ of a binary sequence is represented by an actual sequence `b : ℕ →
-- Bool`, and injectivity of `sequence` lets us realize it by a global `{0,1}`-valued function on
-- `X` whose restriction to the sequence is exactly `b`.
/-- Example 6.11.5 (2): if `sequence n → x` and the points `sequence n` are pairwise distinct, then
the stalk of the `{0,1}`-valued function sheaf at `x` surjects onto the set of tails of binary
sequences. -/
theorem stalkToBinaryTail_surjective (hsequence : Tendsto sequence atTop (nhds x))
    (hsequence_injective : Function.Injective sequence) :
    Function.Surjective (stalkToBinaryTail sequence hsequence) := by
  intro g
  refine inductionOn g ?_
  intro b
  exact ⟨stalkOfBinarySequence x sequence b,
    stalkToBinaryTail_stalkOfBinarySequence hsequence hsequence_injective b⟩

private theorem constFalseTail_ne_modifiedAlternatingTail (n₀ : ℕ) :
    ((fun _ : ℕ ↦ ULift.up false) :
      Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) ≠
      ((fun n : ℕ ↦ if n = n₀ then ULift.up false else ULift.up (decide (n % 2 = 0))) :
        Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) := by
  intro h
  have h' := coe_eq.mp h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h'
  let m := 2 * max N (n₀ + 1)
  have hmN : N ≤ m := by
    dsimp [m]
    omega
  have hmn₀ : m ≠ n₀ := by
    dsimp [m]
    omega
  have hmEven : m % 2 = 0 := by
    dsimp [m]
    omega
  have hm := hN m hmN
  simp [m, hmn₀, hmEven] at hm

private theorem stalkToFiber_stalkOfBinarySequence_of_mem
    (b : ℕ → ULift.{u} Bool) (hx : x ∈ Set.range sequence) :
    dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x
        (stalkOfBinarySequence x sequence b) =
      b (Function.invFun sequence x) := by
  classical
  simpa [stalkOfBinarySequence, binarySectionOfSequence, hx] using
    dependentFunctionStalkToFiber_germ (fun _ : X ↦ ULift.{u} Bool) x (⊤ : Opens X) (by trivial)
      (binarySectionOfSequence sequence b)

private theorem stalkToFiber_stalkOfBinarySequence_of_not_mem
    (b : ℕ → ULift.{u} Bool) (hx : x ∉ Set.range sequence) :
    dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x
        (stalkOfBinarySequence x sequence b) =
      ULift.up false := by
  classical
  simpa [stalkOfBinarySequence, binarySectionOfSequence, hx] using
    dependentFunctionStalkToFiber_germ (fun _ : X ↦ ULift.{u} Bool) x (⊤ : Opens X) (by trivial)
      (binarySectionOfSequence sequence b)

-- Proof sketch: the constant-zero sequence and the parity sequence define two distinct stalk
-- elements because their tails are not eventually equal, but both evaluate to `false` at `∞`.
/-- Example 6.11.5 (3): if `sequence n → x` and the points `sequence n` are pairwise distinct, then
the canonical map from the stalk at `x` of the sheaf of `{0,1}`-valued functions to the fiber
`{0,1}` is not injective. -/
theorem binaryStalkToFiber_not_injective (hsequence : Tendsto sequence atTop (nhds x))
    (hsequence_injective : Function.Injective sequence) :
    ¬ Function.Injective (dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x) := by
  classical
  intro hInj
  let n₀ := Function.invFun sequence x
  let b₁ : ℕ → ULift.{u} Bool := fun n ↦
    if n = n₀ then ULift.up false else ULift.up (decide (n % 2 = 0))
  have hFiber :
      dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x
          (stalkOfBinarySequence x sequence (fun _ : ℕ ↦ ULift.up false)) =
        dependentFunctionStalkToFiber (fun _ : X ↦ ULift.{u} Bool) x
          (stalkOfBinarySequence x sequence b₁) := by
    by_cases hx : x ∈ Set.range sequence
    · rw [stalkToFiber_stalkOfBinarySequence_of_mem _ hx,
        stalkToFiber_stalkOfBinarySequence_of_mem _ hx]
      simp [b₁, n₀]
    · rw [stalkToFiber_stalkOfBinarySequence_of_not_mem _ hx,
        stalkToFiber_stalkOfBinarySequence_of_not_mem _ hx]
  have hStalk :
      stalkOfBinarySequence x sequence (fun _ : ℕ ↦ ULift.up false) =
        stalkOfBinarySequence x sequence b₁ := by
    exact hInj hFiber
  have hTail :
      ((fun _ : ℕ ↦ ULift.up false) :
        Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) =
        (b₁ : Filter.Germ (Filter.atTop : Filter ℕ) (ULift.{u} Bool)) := by
    have hTailMap := congrArg (stalkToBinaryTail sequence hsequence) hStalk
    exact
      (stalkToBinaryTail_stalkOfBinarySequence hsequence
          hsequence_injective (fun _ : ℕ ↦ ULift.up false)).symm.trans <|
        hTailMap.trans <|
          stalkToBinaryTail_stalkOfBinarySequence hsequence hsequence_injective b₁
  exact constFalseTail_ne_modifiedAlternatingTail n₀ hTail

end

end Example_6_11_5
