import StacksProject_2024.Chap20.Definition_20_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open Set.powersetCard
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Remark 20.23.5:
- primary domain: explicit-order ordered Čech complexes and their invariance under changing the
  total order on the index set.
- sampled owner declarations:
  `OrderedCechIndex`,
  `orderedCechIndexOrderEmbedding`,
  `orderedCechTermOfOrder`,
  `orderedCechComplexOfOrder`.
- best owner abstraction: the explicit-order owner `orderedCechComplexOfOrder o 𝒰 F` from
  `Definition_20_23_2`; this file should stay at the bridge/view layer and construct the canonical
  change-of-order isomorphism between two such owners.

Source/core/bridge triage:
- `source-facing`: Remark 20.23.5, asserting canonical independence of the chosen total ordering.
- `core/canonical`: `orderedCechComplexOfOrder o 𝒰 F` and its explicit-order term/index API from
  `Definition_20_23_2`.
- `bridge/view`: the reindexing permutation, signed component isomorphisms, and the induced complex
  isomorphism between two order choices.

Primitive data versus derived API:
- primitive data: two linear orders `o₁`, `o₂`, the cover `𝒰`, and the presheaf `F`.
- derived API: the underlying finite subset of an ordered index, the reindexing permutation, the
  degreewise signed reindexing isomorphisms, and the resulting complex isomorphism. -/

/-- The finite subset of indices underlying an ordered Čech multi-index. -/
noncomputable def orderedCechIndexSubset (o : LinearOrder ι) {p : ℕ}
    (σ : OrderedCechIndex o p) : Set.powersetCard ι (p + 1) :=
  letI := o
  ofFinEmbEquiv (orderedCechIndexOrderEmbedding o σ)

/-- The enumeration of a finite index set by `Fin` with respect to an explicit linear order. -/
noncomputable def orderedCechIndexEnumeration (o : LinearOrder ι) {p : ℕ}
    (s : Set.powersetCard ι (p + 1)) : Fin (p + 1) ≃ s.val :=
  letI := o
  (orderIsoOfFin s).toEquiv

/-- Reordering the same finite Čech index set by a second total ordering. -/
noncomputable def orderedCechIndexReindex (o₁ o₂ : LinearOrder ι) {p : ℕ}
    (σ : OrderedCechIndex o₂ p) : OrderedCechIndex o₁ p :=
  let s := orderedCechIndexSubset o₂ σ
  letI := o₁
  let e := ofFinEmbEquiv.symm s
  ⟨e, e.strictMono⟩

/-- The permutation sending the `o₁`-ordering of a finite index set to its `o₂`-ordering. -/
noncomputable def orderedCechIndexPermutation (o₁ o₂ : LinearOrder ι) {p : ℕ}
    (σ : OrderedCechIndex o₂ p) : Equiv.Perm (Fin (p + 1)) :=
  let s := orderedCechIndexSubset o₂ σ
  let e₁ := orderedCechIndexEnumeration o₁ s
  let e₂ := orderedCechIndexEnumeration o₂ s
  e₂.trans e₁.symm

-- Proof sketch: both ordered embeddings enumerate the same finite subset of `ι`; `cechIntersection`
-- is the infimum of the corresponding family of opens, so it depends only on that subset and not
-- on which total ordering is used to list its elements.
/-- Reordering a finite Čech index set by a different total order does not change the underlying
intersection of covering opens. -/
theorem cechIntersection_orderedCechIndexReindex (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) {p : ℕ} (σ : OrderedCechIndex o₂ p) :
    cechIntersection 𝒰 (orderedCechIndexReindex o₁ o₂ σ) = cechIntersection 𝒰 σ := sorry

-- Proof sketch: apply `F.obj` to the equality of intersections from
-- `cechIntersection_orderedCechIndexReindex`; the two section groups are the same object after this
-- rewrite.
/-- Reordering an ordered Čech multi-index identifies the two corresponding section groups. -/
theorem orderedCechComponent_eq (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ} (σ : OrderedCechIndex o₂ p) :
    F.obj (op (cechIntersection 𝒰 (orderedCechIndexReindex o₁ o₂ σ))) =
      F.obj (op (cechIntersection 𝒰 σ)) := sorry

/-- The canonical identification of section groups obtained by reordering the same finite index
set. -/
noncomputable def orderedCechComponentIso (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ} (σ : OrderedCechIndex o₂ p) :
    F.obj (op (cechIntersection 𝒰 (orderedCechIndexReindex o₁ o₂ σ))) ≅
      F.obj (op (cechIntersection 𝒰 σ)) :=
  eqToIso (orderedCechComponent_eq o₁ o₂ 𝒰 F σ)

/-- The coordinatewise signed reindexing map from the ordered Čech term for `o₁` to the ordered
Čech term for `o₂`. -/
noncomputable def orderedCechTermChangeOrderToFun (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o₁ 𝒰 F p → orderedCechTermOfOrder o₂ 𝒰 F p :=
  fun s σ ↦
    (↑(Equiv.Perm.sign (orderedCechIndexPermutation o₁ o₂ σ)) : ℤ) •
      (orderedCechComponentIso o₁ o₂ 𝒰 F σ).hom (s (orderedCechIndexReindex o₁ o₂ σ))

/-- The inverse coordinatewise signed reindexing map from the ordered Čech term for `o₂` to the
ordered Čech term for `o₁`. -/
noncomputable def orderedCechTermChangeOrderInvFun (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o₂ 𝒰 F p → orderedCechTermOfOrder o₁ 𝒰 F p :=
  fun s σ ↦
    (↑(Equiv.Perm.sign (orderedCechIndexPermutation o₂ o₁ σ)) : ℤ) •
      (orderedCechComponentIso o₂ o₁ 𝒰 F σ).hom (s (orderedCechIndexReindex o₂ o₁ σ))

-- Proof sketch: evaluation at any ordered multi-index is additive, the identification morphism of
-- section groups is additive, and multiplication by the sign of a permutation is additive.
/-- The signed reindexing map between ordered Čech terms is additive. -/
theorem orderedCechTermChangeOrderToFun_map_add (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : orderedCechTermOfOrder o₁ 𝒰 F p) :
    orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p (s + t) =
      orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p s +
        orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p t := sorry

-- Proof sketch: apply the forward map and then the reverse map at a fixed ordered multi-index.
-- The two reindexings return to the original finite subset, the two identification isomorphisms
-- compose to the identity, and the two permutation signs multiply to `1`.
/-- Changing from `o₁` to `o₂` and back recovers the original ordered Čech term. -/
theorem orderedCechTermChangeOrder_left_inv (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTermOfOrder o₁ 𝒰 F p) :
    orderedCechTermChangeOrderInvFun o₁ o₂ 𝒰 F p
        (orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p s) = s := sorry

-- Proof sketch: the same argument as in `orderedCechTermChangeOrder_left_inv`, with the two orders
-- interchanged, shows that the reverse map is also a left inverse of the forward map.
/-- Changing from `o₂` to `o₁` and back recovers the original ordered Čech term. -/
theorem orderedCechTermChangeOrder_right_inv (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTermOfOrder o₂ 𝒰 F p) :
    orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p
        (orderedCechTermChangeOrderInvFun o₁ o₂ 𝒰 F p s) = s := sorry

/-- The signed reindexing equivalence between ordered Čech terms for two total orders. -/
noncomputable def orderedCechTermChangeOrderEquiv (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o₁ 𝒰 F p ≃+ orderedCechTermOfOrder o₂ 𝒰 F p where
  toFun := orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p
  invFun := orderedCechTermChangeOrderInvFun o₁ o₂ 𝒰 F p
  map_add' := orderedCechTermChangeOrderToFun_map_add o₁ o₂ 𝒰 F p
  left_inv := orderedCechTermChangeOrder_left_inv o₁ o₂ 𝒰 F p
  right_inv := orderedCechTermChangeOrder_right_inv o₁ o₂ 𝒰 F p

/-- The degreewise signed reindexing isomorphism between ordered Čech terms for two total orders. -/
noncomputable def orderedCechTermChangeOrderIso (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o₁ 𝒰 F p ≅ orderedCechTermOfOrder o₂ 𝒰 F p :=
  (orderedCechTermChangeOrderEquiv o₁ o₂ 𝒰 F p).toAddCommGrpIso

-- Proof sketch: compare the two ordered Čech differentials componentwise. After reindexing a
-- fixed finite subset, omitting the `j`th entry before or after changing orders differs exactly by
-- the sign of the permutation that records how the two total orderings enumerate the same subset,
-- so the signed reindexing intertwines the alternating sums.
/-- The degreewise signed reindexing is compatible with the ordered Čech differentials. -/
theorem orderedCechTermChangeOrder_comm (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    ∀ i j, (ComplexShape.up ℕ).Rel i j →
      (orderedCechTermChangeOrderIso o₁ o₂ 𝒰 F i).hom ≫
          (orderedCechComplexOfOrder o₂ 𝒰 F).d i j =
        (orderedCechComplexOfOrder o₁ 𝒰 F).d i j ≫
          (orderedCechTermChangeOrderIso o₁ o₂ 𝒰 F j).hom := sorry

/-- Remark 20.23.5: two total orderings on the index set define canonically isomorphic ordered
Čech complexes, so the ordered Čech complex is independent of the chosen total ordering up to a
canonical isomorphism of complexes. -/
noncomputable def orderedCechComplexChangeOrderIso (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComplexOfOrder o₁ 𝒰 F ≅ orderedCechComplexOfOrder o₂ 𝒰 F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ orderedCechTermChangeOrderIso o₁ o₂ 𝒰 F p)
    (orderedCechTermChangeOrder_comm o₁ o₂ 𝒰 F)

-- Proof sketch: by construction `orderedCechComplexChangeOrderIso` is obtained from the
-- degreewise signed reindexing equivalences, so its degree-`p` component is exactly the map
-- described by the explicit permutation formula in the textbook.
/-- The degree-`p` component of the order-change isomorphism is the signed reindexing map given by
the permutation that compares the two orderings on the same finite subset of indices. -/
theorem orderedCechComplexChangeOrderIso_hom_apply (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTermOfOrder o₁ 𝒰 F p) (σ : OrderedCechIndex o₂ p) :
    ((orderedCechComplexChangeOrderIso o₁ o₂ 𝒰 F).hom.f p s) σ =
      (↑(Equiv.Perm.sign (orderedCechIndexPermutation o₁ o₂ σ)) : ℤ) •
        (orderedCechComponentIso o₁ o₂ 𝒰 F σ).hom
          (s (orderedCechIndexReindex o₁ o₂ σ)) := sorry
