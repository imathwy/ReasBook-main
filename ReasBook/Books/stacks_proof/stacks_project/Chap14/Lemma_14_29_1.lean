import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Limits
open HomologicalComplex

universe v u

prefix:max "◇" => HomologicalComplex.cylinder

noncomputable section

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

open HomologicalComplex.cylinder

private abbrev downRel : ∀ j : ℕ, ∃ i, (ComplexShape.down ℕ).Rel i j :=
  fun j ↦ ⟨j + 1, rfl⟩

/-
Domain-style sampling:
- primary domain: chain-complex cylinders and the homotopy-cofiber universal property;
- sampled owner declarations: `HomologicalComplex.cylinder`,
  `HomologicalComplex.cylinder.desc`, `HomologicalComplex.cylinder.ι₀_desc`,
  `HomologicalComplex.cylinder.ι₁_desc`,
  `Functor.CorepresentableBy`, and `Functor.CorepresentableBy.homEquiv_symm_comp`;
- best owner abstraction: the source-facing Stacks cylinder `◇A`, written directly with the
  canonical mathlib owner `HomologicalComplex.cylinder`, with its universal property expressed by
  the canonical cylinder owner `cylinder.desc` and packaged by `Functor.CorepresentableBy`;
  mathlib does not provide a separate cylinder endofunctor owner here, so the public functoriality
  statement remains source-facing and should be derived from that owner data rather than replaced
  by a parallel local wrapper API;
- owner assumption layer: these owners live at the preadditive plus binary-biproduct level, so
  `[Abelian C]` would be redundant here.

Primitive-vs-derived split:
- primitive data: two chain maps `a, b : A ⟶ B` and a homotopy `Homotopy a b`;
- derived API: the resulting corepresentability witness and the induced cylinder map attached to a
  morphism `f : A ⟶ B`.

Source/core/bridge triage:
- `source-facing`: the homotopy functor represented by maps out of `◇A` and the functoriality of
  the Stacks cylinder construction `A ↦ ◇A`;
- `core/canonical`: `HomologicalComplex.cylinder`, `HomologicalComplex.cylinder.desc`,
  and `Functor.CorepresentableBy`;
- `bridge/view`: the corepresentability witness and the private map extracted from it.
-/

/-- Helper for Lemma 14.29.1: a pair of endpoint maps `A ⟶ B` together with a homotopy
between them. -/
@[ext]
private structure HomotopyTriple (A B : ChainComplex C ℕ) where
  left : A ⟶ B
  right : A ⟶ B
  homotopy : Homotopy left right

/-- Helper for Lemma 14.29.1: once the endpoints are fixed, equality of the degreewise homotopy
components identifies the corresponding homotopy triples. -/
private theorem homotopyTriple_ext_of_hom
    {A B : ChainComplex C ℕ}
    {a₁ a₂ b₁ b₂ : A ⟶ B}
    {h₁ : Homotopy a₁ a₂} {h₂ : Homotopy b₁ b₂}
    (hleft : a₁ = b₁) (hright : a₂ = b₂) (hhom : h₁.hom = h₂.hom) :
    (HomotopyTriple.mk a₁ a₂ h₁ : HomotopyTriple A B) =
      HomotopyTriple.mk b₁ b₂ h₂ := by
  -- After rewriting the endpoints, `Homotopy.ext` reduces the comparison to the `hom` field.
  cases hleft
  cases hright
  have hEq : h₁ = h₂ := Homotopy.ext hhom
  cases hEq
  rfl

/-- Helper for Lemma 14.29.1: the identity map acts trivially on homotopy triples. -/
private theorem homotopyFunctor_map_id_aux
    (A B : ChainComplex C ℕ) (x : HomotopyTriple A B) :
    { left := x.left ≫ 𝟙 B, right := x.right ≫ 𝟙 B, homotopy := x.homotopy.compRight (𝟙 B) } = x :=
  by
    cases x with
    | mk left right homotopy =>
        -- Route correction: simplify the endpoint identities first, then compare the homotopy
        -- field through its degreewise components.
        refine homotopyTriple_ext_of_hom (by simp) (by simp) ?_
        ext i j
        simp [Homotopy.compRight_hom]

/-- Helper for Lemma 14.29.1: postcomposition on homotopy triples is compatible with
composition of chain maps. -/
private theorem homotopyFunctor_map_comp_aux
    (A : ChainComplex C ℕ) {B₁ B₂ B₃ : ChainComplex C ℕ}
    (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₃) (x : HomotopyTriple A B₁) :
    (show HomotopyTriple A B₃ from
      { left := x.left ≫ (f ≫ g), right := x.right ≫ (f ≫ g),
        homotopy := x.homotopy.compRight (f ≫ g) }) =
      (show HomotopyTriple A B₃ from
        { left := (x.left ≫ f) ≫ g, right := (x.right ≫ f) ≫ g,
          homotopy := (x.homotopy.compRight f).compRight g }) :=
  by
    cases x with
    | mk left right homotopy =>
        -- Reassociate both endpoint maps and the whiskered homotopy in parallel.
        refine homotopyTriple_ext_of_hom (by simp [Category.assoc]) (by simp [Category.assoc]) ?_
        ext i j
        simp [Homotopy.compRight_hom, Category.assoc]

/-- The covariant functor sending `B` to triples `(a, b, h)` of maps `a, b : A ⟶ B` equipped
with a homotopy `h : Homotopy a b`. -/
noncomputable def homotopyFunctor
    (A : ChainComplex C ℕ) :
    ChainComplex C ℕ ⥤ Type v where
  obj B := HomotopyTriple A B
  map {_ B₂} f x := { left := x.left ≫ f, right := x.right ≫ f, homotopy := x.homotopy.compRight f }
  map_id B := funext (homotopyFunctor_map_id_aux A B)
  map_comp f g := funext (homotopyFunctor_map_comp_aux A f g)

/-- Helper for Lemma 14.29.1: restricting a map out of `A ⊞ A` along `(𝟙, -𝟙)` computes the
difference of its two endpoint maps. -/
private theorem biprod_lift_comp_eq_sub
    {A B : ChainComplex C ℕ} (α : A ⊞ A ⟶ B) :
    biprod.lift (𝟙 A) (-𝟙 A) ≫ α = biprod.inl ≫ α - biprod.inr ≫ α := by
  have hα : α = biprod.desc (biprod.inl ≫ α) (biprod.inr ≫ α) := by
    ext <;> simp
  -- Rewrite through the biproduct coordinates to expose the `(𝟙, -𝟙)` combination.
  rw [hα]
  simp [sub_eq_add_neg]

/-- Helper for Lemma 14.29.1: the map `biprod.desc a b` restricts along `(𝟙, -𝟙)` to `a - b`. -/
private theorem biprod_lift_desc_eq_sub
    {A B : ChainComplex C ℕ} (a b : A ⟶ B) :
    biprod.lift (𝟙 A) (-𝟙 A) ≫ biprod.desc a b = a - b := by
  -- This is the previous restriction formula specialized to a biproduct descendent.
  simpa using (biprod_lift_comp_eq_sub (A := A) (B := B) (biprod.desc a b))

/-- Helper for Lemma 14.29.1: a morphism out of `A ⊞ A` is determined by its two endpoint
components. -/
private theorem biprod_desc_inl_inr
    {A B : ChainComplex C ℕ} (α : A ⊞ A ⟶ B) :
    biprod.desc (biprod.inl ≫ α) (biprod.inr ≫ α) = α := by
  -- The two endpoint composites recover the original morphism by biproduct extensionality.
  ext <;> simp

/-- Helper for Lemma 14.29.1: a homotopy `a ∼ b` gives the null-homotopy needed for the
homotopy-cofiber universal property of the cylinder. -/
private noncomputable def homotopyToDescData
    {A B : ChainComplex C ℕ} {a b : A ⟶ B} (h : Homotopy a b) :
    Homotopy (biprod.lift (𝟙 A) (-𝟙 A) ≫ biprod.desc a b) 0 :=
  (Homotopy.ofEq (biprod_lift_desc_eq_sub a b)).trans (Homotopy.equivSubZero h)

/-- Helper for Lemma 14.29.1: a null-homotopy after restriction along `(𝟙, -𝟙)` recovers a
homotopy between the two endpoint maps. -/
private noncomputable def descDataToHomotopy
    {A B : ChainComplex C ℕ} {α : A ⊞ A ⟶ B}
    (hα : Homotopy (biprod.lift (𝟙 A) (-𝟙 A) ≫ α) 0) :
    Homotopy (biprod.inl ≫ α) (biprod.inr ≫ α) :=
  Homotopy.equivSubZero.symm ((Homotopy.ofEq (biprod_lift_comp_eq_sub α)).symm.trans hα)

/-- Helper for Lemma 14.29.1: the owner sigma type of cylinder descent data. -/
private abbrev CylinderDescData (A B : ChainComplex C ℕ) :=
  Σ (α : A ⊞ A ⟶ B), Homotopy (biprod.lift (𝟙 A) (-𝟙 A) ≫ α) 0

/-- Helper for Lemma 14.29.1: postcomposing cylinder descent data produces descent data for
the postcomposed map. -/
private noncomputable def descDataCompRight
    {A B D : ChainComplex C ℕ} {α : A ⊞ A ⟶ B}
    (hα : Homotopy (biprod.lift (𝟙 A) (-𝟙 A) ≫ α) 0) (g : B ⟶ D) :
    Homotopy (biprod.lift (𝟙 A) (-𝟙 A) ≫ (α ≫ g)) 0 :=
  ((Homotopy.ofEq (by simp [Category.assoc])).symm.trans (hα.compRight g)).trans
    (Homotopy.ofEq (by simp))

/-- Helper for Lemma 14.29.1: passing from a homotopy to descent data and back recovers the
original homotopy. -/
private theorem descDataToHomotopy_homotopyToDescData_hom
    {A B : ChainComplex C ℕ} {a b : A ⟶ B} (h : Homotopy a b) :
    (descDataToHomotopy (homotopyToDescData h)).hom = h.hom := by
  -- Unfold the two bridge constructions only to the degreewise `hom` field; all transport terms
  -- coming from `ofEq` contribute `0`, so the remaining component is exactly `h.hom`.
  funext i j
  simp [descDataToHomotopy, homotopyToDescData, Homotopy.equivSubZero]

/-- Helper for Lemma 14.29.1: converting owner descent data to a homotopy triple commutes with
postcomposition in the target. -/
private theorem descDataToHomotopy_compRight_hom
    {A B D : ChainComplex C ℕ} {α : A ⊞ A ⟶ B}
    (hα : Homotopy (biprod.lift (𝟙 A) (-𝟙 A) ≫ α) 0) (g : B ⟶ D) :
    (descDataToHomotopy (descDataCompRight hα g)).hom = ((descDataToHomotopy hα).compRight g).hom := by
  -- The postcomposition descent datum only inserts endpoint equalities; after taking `.hom`,
  -- both sides reduce to whiskering the original `hα.hom` by `g`.
  funext i j
  simp [descDataToHomotopy, descDataCompRight, Homotopy.equivSubZero]

/-- Helper for Lemma 14.29.1: the owner sigma descent data is recovered from its induced
homotopy triple. -/
private theorem descData_roundtrip
    {A B : ChainComplex C ℕ} (x : CylinderDescData A B) :
    ⟨biprod.desc (biprod.inl ≫ x.1) (biprod.inr ≫ x.1), homotopyToDescData (descDataToHomotopy x.2)⟩ = x := by
  obtain ⟨α, hα⟩ := x
  -- Reduce the sigma-data equality to its map component and the relevant homotopy components.
  rw [HomologicalComplex.homotopyCofiber.descSigma_ext_iff]
  constructor
  · exact biprod_desc_inl_inr α
  · intro i j hij
    simp [homotopyToDescData, descDataToHomotopy]

/-- Helper for Lemma 14.29.1: the owner sigma descent data and endpoint homotopy triples are
equivalent presentations of the same information. -/
private theorem descDataEquivHomotopyTriple_left_inv
    {A B : ChainComplex C ℕ} (x : CylinderDescData A B) :
    ⟨biprod.desc (biprod.inl ≫ x.1) (biprod.inr ≫ x.1), homotopyToDescData (descDataToHomotopy x.2)⟩ = x :=
  descData_roundtrip x

/-- Helper for Lemma 14.29.1: converting a homotopy triple to owner descent data and back is
the identity. -/
private theorem descDataEquivHomotopyTriple_right_inv
    {A B : ChainComplex C ℕ} (x : HomotopyTriple A B) :
    { left := biprod.inl ≫ biprod.desc x.left x.right
    , right := biprod.inr ≫ biprod.desc x.left x.right
    , homotopy := descDataToHomotopy (homotopyToDescData x.homotopy) } = x := by
  cases x with
  | mk left right homotopy =>
      -- Simplify the endpoint maps through the biproduct descendent, then identify the homotopy
      -- field using the roundtrip computation on `.hom`.
      refine homotopyTriple_ext_of_hom (by simp) (by simp) ?_
      simpa using
        (descDataToHomotopy_homotopyToDescData_hom
          (A := A) (B := B) (a := left) (b := right) homotopy)

/-- Helper for Lemma 14.29.1: the owner cylinder descent data and homotopy triples are
equivalent. -/
private noncomputable def descDataEquivHomotopyTriple
    (A B : ChainComplex C ℕ) :
    CylinderDescData A B ≃ HomotopyTriple A B where
  toFun := fun x ↦
    { left := biprod.inl ≫ x.1, right := biprod.inr ≫ x.1, homotopy := descDataToHomotopy x.2 }
  invFun := fun x ↦ ⟨biprod.desc x.left x.right, homotopyToDescData x.homotopy⟩
  left_inv := descDataEquivHomotopyTriple_left_inv
  right_inv := descDataEquivHomotopyTriple_right_inv

/-- Helper for Lemma 14.29.1: postcomposition of owner descent data matches postcomposition of
the corresponding homotopy triple. -/
private theorem descDataEquivHomotopyTriple_map
    {A B D : ChainComplex C ℕ} (g : B ⟶ D) (x : CylinderDescData A B) :
    descDataEquivHomotopyTriple A D ⟨x.1 ≫ g, descDataCompRight x.2 g⟩ =
      (homotopyFunctor A).map g (descDataEquivHomotopyTriple A B x) := by
  obtain ⟨α, hα⟩ := x
  -- Both routes give the same endpoint maps after reassociation; the homotopy components match
  -- by the explicit postcomposition formula for `descDataToHomotopy`.
  refine homotopyTriple_ext_of_hom
    (by simp [descDataEquivHomotopyTriple, Category.assoc])
    (by simp [descDataEquivHomotopyTriple, Category.assoc]) ?_
  simpa using
    (descDataToHomotopy_compRight_hom (A := A) (B := B) (D := D) (α := α) hα g)

/-- Helper for Lemma 14.29.1: the owner inverse of `descEquiv` sends postcomposition of a map
out of the cylinder to postcomposition of the corresponding descent data. -/
private theorem descEquiv_symm_comp
    (A : ChainComplex C ℕ) {B D : ChainComplex C ℕ} (g : B ⟶ D) (f : ◇A ⟶ B) :
    ((HomologicalComplex.homotopyCofiber.descEquiv
      (φ := biprod.lift (𝟙 A) (-𝟙 A)) D downRel).symm (f ≫ g)) =
      ⟨(((HomologicalComplex.homotopyCofiber.descEquiv
          (φ := biprod.lift (𝟙 A) (-𝟙 A)) B downRel).symm f).1 ≫ g),
        descDataCompRight
          (((HomologicalComplex.homotopyCofiber.descEquiv
              (φ := biprod.lift (𝟙 A) (-𝟙 A)) B downRel).symm f).2) g⟩ := by
  -- Unfold the owner inverse once and compare the resulting sigma data componentwise.
  rw [HomologicalComplex.homotopyCofiber.descSigma_ext_iff]
  constructor
  · change HomologicalComplex.homotopyCofiber.inr (biprod.lift (𝟙 A) (-𝟙 A)) ≫ (f ≫ g) =
      (HomologicalComplex.homotopyCofiber.inr (biprod.lift (𝟙 A) (-𝟙 A)) ≫ f) ≫ g
    simp [Category.assoc]
  · intro i j hij
    -- On the homotopy field, the inserted `ofEq` witnesses are zero, so both sides have the same
    -- degreewise postcomposition formula.
    simp [HomologicalComplex.homotopyCofiber.descEquiv, descDataCompRight, Category.assoc]

/-- Helper for Lemma 14.29.1: morphisms out of the cylinder are equivalent to endpoint triples
with a homotopy between them. -/
private noncomputable def diamondHomEquiv
    (A B : ChainComplex C ℕ) :
    (◇A ⟶ B) ≃ HomotopyTriple A B :=
  -- Route correction: we still use the owner descent-data API, but we bridge directly from
  -- the owner sigma data to `HomotopyTriple`, avoiding the previous proof-carrying structure
  -- transport layer.
  ((HomologicalComplex.homotopyCofiber.descEquiv
      (φ := biprod.lift (𝟙 A) (-𝟙 A)) B downRel).symm).trans
    (descDataEquivHomotopyTriple A B)

/-- Helper for Lemma 14.29.1: the representing equivalence respects postcomposition in the
target chain complex. -/
private theorem diamondCorepresentableByHomotopyFunctor_homEquiv_comp
    (A : ChainComplex C ℕ) {B D : ChainComplex C ℕ} (g : B ⟶ D) (f : ◇A ⟶ B) :
    diamondHomEquiv A D (f ≫ g) = (homotopyFunctor A).map g (diamondHomEquiv A B f) := by
  let x :
      CylinderDescData A B :=
    ((HomologicalComplex.homotopyCofiber.descEquiv
      (φ := biprod.lift (𝟙 A) (-𝟙 A)) B downRel).symm f)
  -- Unfold the owner inverse data for maps out of the cylinder and simplify the explicit
  -- postcomposition on the associated sigma descent data.
  change descDataEquivHomotopyTriple A D
      (((HomologicalComplex.homotopyCofiber.descEquiv
        (φ := biprod.lift (𝟙 A) (-𝟙 A)) D downRel).symm (f ≫ g))) =
    (homotopyFunctor A).map g
      (descDataEquivHomotopyTriple A B
        (((HomologicalComplex.homotopyCofiber.descEquiv
          (φ := biprod.lift (𝟙 A) (-𝟙 A)) B downRel).symm f)))
  rw [descEquiv_symm_comp A g f]
  simpa [x] using (descDataEquivHomotopyTriple_map (A := A) (B := B) (D := D) g x)

/-- Lemma 14.29.1 (1): the Stacks cylinder `◇A` corepresents the functor sending a chain complex
`B` to triples `(a, b, h)` consisting of two maps `a, b : A ⟶ B` and a homotopy
`h : Homotopy a b`. -/
@[stacks 01A2]
noncomputable def diamondCorepresentableByHomotopyFunctor
    (A : ChainComplex C ℕ) :
    (homotopyFunctor A).CorepresentableBy ◇A :=
  { homEquiv := fun {Y} ↦ diamondHomEquiv A Y
    homEquiv_comp := diamondCorepresentableByHomotopyFunctor_homEquiv_comp A }

/-- Helper for Lemma 14.29.1: source-precomposition acts on homotopy triples by composing the
two endpoint maps and their homotopy on the left. -/
private noncomputable def homotopyFunctorPrecomp
    {A B D : ChainComplex C ℕ} (f : A ⟶ B) :
    HomotopyTriple B D → HomotopyTriple A D
  | ⟨a, b, h⟩ => { left := f ≫ a, right := f ≫ b, homotopy := h.compLeft f }

/-- Helper for Lemma 14.29.1: precomposition by the identity leaves homotopy triples unchanged. -/
private theorem homotopyFunctorPrecomp_id
    {A D : ChainComplex C ℕ} (x : HomotopyTriple A D) :
    homotopyFunctorPrecomp (𝟙 A) x = x :=
  by
    cases x with
    | mk left right homotopy =>
        -- Identity precomposition only changes the homotopy field by `compLeft (𝟙 A)`.
        refine homotopyTriple_ext_of_hom (by simp) (by simp) ?_
        ext i j
        simp [Homotopy.compLeft_hom]

/-- Helper for Lemma 14.29.1: source-precomposition commutes with postcomposition in the target. -/
private theorem homotopyFunctorPrecomp_map
    {A B D E : ChainComplex C ℕ} (f : A ⟶ B) (g : D ⟶ E)
    (x : HomotopyTriple B D) :
    (homotopyFunctor A).map g (homotopyFunctorPrecomp f x) =
      homotopyFunctorPrecomp f ((homotopyFunctor B).map g x) :=
  by
    cases x with
    | mk left right homotopy =>
        -- Both routes produce the same endpoint maps `A ⟶ E`; the homotopy components agree by
        -- the explicit `compLeft` and `compRight` formulas.
        refine homotopyTriple_ext_of_hom (by simp [homotopyFunctorPrecomp, Category.assoc])
          (by simp [homotopyFunctorPrecomp, Category.assoc]) ?_
        ext i j
        simp [homotopyFunctorPrecomp, Homotopy.compLeft_hom, Homotopy.compRight_hom,
          Category.assoc]

/-- Helper for Lemma 14.29.1: successive source-precompositions compose as expected. -/
private theorem homotopyFunctorPrecomp_comp
    {A B D E : ChainComplex C ℕ} (f : A ⟶ B) (g : B ⟶ D)
    (x : HomotopyTriple D E) :
    homotopyFunctorPrecomp (f ≫ g) x =
      homotopyFunctorPrecomp f (homotopyFunctorPrecomp g x) :=
  by
    cases x with
    | mk left right homotopy =>
        -- Successive source whiskerings reassociate on endpoints and on the homotopy field.
        refine homotopyTriple_ext_of_hom (by simp [Category.assoc]) (by simp [Category.assoc]) ?_
        ext i j
        simp [Homotopy.compLeft_hom, Category.assoc]

/-- Helper for Lemma 14.29.1: the universal triple corresponding to the identity map of the
cylinder. -/
private noncomputable def canonicalTriple
    (A : ChainComplex C ℕ) :
    HomotopyTriple A (◇A) :=
  (diamondCorepresentableByHomotopyFunctor A).homEquiv (𝟙 (◇A))

private noncomputable abbrev diamondMap {A B : ChainComplex C ℕ} (f : A ⟶ B) : ◇A ⟶ ◇B :=
  (diamondCorepresentableByHomotopyFunctor A).homEquiv.symm
    (homotopyFunctorPrecomp f (canonicalTriple B))

/-- Helper for Lemma 14.29.1: applying the representing equivalence to `diamondMap f` recovers
the triple obtained by precomposing the universal triple of `◇B` with `f`. -/
private theorem diamondMap_homEquiv
    {A B : ChainComplex C ℕ} (f : A ⟶ B) :
    (diamondCorepresentableByHomotopyFunctor A).homEquiv (diamondMap f) =
      homotopyFunctorPrecomp f (canonicalTriple B) := by
  -- `diamondMap` is defined by transporting the precomposed canonical triple back along
  -- the representing equivalence.
  simpa [diamondMap] using
    (Equiv.apply_symm_apply (diamondCorepresentableByHomotopyFunctor A).homEquiv
      (homotopyFunctorPrecomp f (canonicalTriple B)))

-- Proof sketch: apply the injectivity of the owner equivalence
-- `diamondCorepresentableByHomotopyFunctor A`. Under `homEquiv`, both
-- `diamondMap (𝟙 A)` and `𝟙 (◇A)` correspond to the canonical triple
-- `(ι₀ A, ι₁ A, homotopy₀₁ A downRel)`.
/-- The cylinder construction sends identity maps to identity maps. -/
private theorem diamondFunctor_map_id
    (A : ChainComplex C ℕ) :
    diamondMap (𝟙 A) = 𝟙 (◇A) := by
  -- Compare both maps under the representing equivalence, where they both correspond
  -- to the canonical triple of `◇A`.
  apply (diamondCorepresentableByHomotopyFunctor A).homEquiv.injective
  rw [diamondMap_homEquiv]
  simpa [canonicalTriple] using homotopyFunctorPrecomp_id (canonicalTriple A)

-- Proof sketch: again use the injectivity of
-- `diamondCorepresentableByHomotopyFunctor A`. The two maps have the same `homEquiv` image,
-- namely the transported triple
-- `(f ≫ g ≫ ι₀ D, f ≫ g ≫ ι₁ D, ((homotopy₀₁ D downRel).compLeft g).compLeft f)`.
/-- The cylinder construction sends compositions to compositions. -/
private theorem diamondFunctor_map_comp
    {A B D : ChainComplex C ℕ} (f : A ⟶ B) (g : B ⟶ D) :
    diamondMap (f ≫ g) = diamondMap f ≫ diamondMap g := by
  -- Compare both maps under the representing equivalence from `◇A`; after rewriting naturality
  -- and the canonical triple, the goal becomes the associativity of source precomposition.
  apply (diamondCorepresentableByHomotopyFunctor A).homEquiv.injective
  rw [diamondMap_homEquiv]
  change homotopyFunctorPrecomp (f ≫ g) (canonicalTriple D) =
    diamondHomEquiv A (◇D) (diamondMap f ≫ diamondMap g)
  rw [diamondCorepresentableByHomotopyFunctor_homEquiv_comp A (g := diamondMap g)
    (f := diamondMap f)]
  change homotopyFunctorPrecomp (f ≫ g) (canonicalTriple D) =
    (homotopyFunctor A).map (diamondMap g)
      ((diamondCorepresentableByHomotopyFunctor A).homEquiv (diamondMap f))
  rw [diamondMap_homEquiv]
  rw [homotopyFunctorPrecomp_map]
  have hcanonical :
      (homotopyFunctor B).map (diamondMap g) (canonicalTriple B) =
        homotopyFunctorPrecomp g (canonicalTriple D) := by
    -- The canonical triple is the `homEquiv` image of the identity on `◇B`, so naturality
    -- identifies its image under `diamondMap g` with the `homEquiv` image of `diamondMap g`.
    calc
      (homotopyFunctor B).map (diamondMap g) (canonicalTriple B) =
          diamondHomEquiv B (◇D) (diamondMap g) := by
            simpa [canonicalTriple, Category.comp_id] using
              (diamondCorepresentableByHomotopyFunctor_homEquiv_comp
                (A := B) (B := ◇B) (D := ◇D) (g := diamondMap g) (f := 𝟙 (◇B))).symm
      _ = homotopyFunctorPrecomp g (canonicalTriple D) := diamondMap_homEquiv g
  rw [hcanonical]
  exact homotopyFunctorPrecomp_comp f g (canonicalTriple D)

/-- Lemma 14.29.1 (2): the Stacks cylinder construction `A ↦ ◇A` is functorial on `ℕ`-indexed
chain complexes in a preadditive category with binary biproducts. -/
@[stacks 01A2]
noncomputable def diamondFunctor : ChainComplex C ℕ ⥤ ChainComplex C ℕ where
  obj A := ◇A
  map {_ _} f := diamondMap f
  map_id A := diamondFunctor_map_id A
  map_comp f g := diamondFunctor_map_comp f g

end ChainComplex
