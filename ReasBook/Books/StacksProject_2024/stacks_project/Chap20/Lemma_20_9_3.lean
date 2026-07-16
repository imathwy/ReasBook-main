import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksProject_2024.stacks_project.Chap20.Definition_20_9_1
import StacksProject_2024.stacks_project.Chap20.OpensInstances
import StacksProject_2024.stacks_project.Chap20.«20_9_0_1»

open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace HomologicalComplex
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open scoped BigOperators ZeroObject

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Lemma 20.9.3:
- primary domain: Čech complexes and their degree-zero augmentations for abelian presheaves on an
  indexed family of opens;
- sampled owner API:
  `CategoryTheory.cechComplexFunctor`,
  `TopCat.Presheaf.cechComplex`,
  `AlgebraicTopology.alternatingCofaceMapComplex`,
  `CochainComplex.fromSingle₀AsComplex`,
  `CochainComplex.fromSingle₀Equiv`;
- `source-facing`: the tuplewise Čech terms, restriction maps, augmentation, and the contractible
  extended Čech complex when one cover member is `U`;
- `core/canonical`: `CategoryTheory.cechComplexFunctor 𝒰`;
- `bridge/view`: the explicit tuplewise `cechTerm` / `cechDifferential` formulas and the
  degree-zero augmentation map written in those coordinates, with the source-facing owner
  `cechComplex 𝒰 F` reusing the canonical `cechComplexFunctor 𝒰`.

Primitive data is only the indexed family `𝒰`, the presheaf `F`, and the open `U` together with a
cover equality identifying `U` and `iSup 𝒰`. The ordinary Čech complex itself is not primitive
public data here: it is the canonical owner `cechComplexFunctor`, while the tuplewise coordinates
remain only as the bridge API used by the later ordered/alternating comparison files.
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
      cechIntersection 𝒰 (σ ∘ j.succAboveEmb) := by
  refine le_iInf fun i ↦ ?_
  simpa [cechIntersection] using
    (iInf_le (fun a : Fin (n + 1) ↦ 𝒰 (σ a)) (j.succAboveEmb i))

/-- The degree `p` term of the Čech complex of a presheaf `F` with respect to a family `𝒰`. -/
abbrev cechTerm (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of
    (∀ σ : Fin (p + 1) → ι, F.obj (op (cechIntersection 𝒰 σ)))

/-- The finite product in `Opens X` indexed by a Čech tuple is the corresponding intersection. -/
private theorem cechTupleProduct_eq_intersection (𝒰 : ι → Opens X) {n : ℕ}
    (σ : Fin n → ι) :
    ∏ᶜ (fun a : Fin n ↦ 𝒰 (σ a)) = cechIntersection 𝒰 σ := by
  let K : Discrete (Fin n) ⥤ Opens X := Discrete.functor (fun a : Fin n ↦ 𝒰 (σ a))
  change limit K = cechIntersection 𝒰 σ
  calc
      limit K =
        ⨅ a : Discrete (Fin n), 𝒰 (σ a.as) := by
          simpa [K] using limit_eq_iInf K
    _ = ⨅ a : Fin n, 𝒰 (σ a) := by
          refine le_antisymm ?_ ?_
          · refine le_iInf fun a ↦ ?_
            exact iInf_le (fun b : Discrete (Fin n) ↦ 𝒰 (σ b.as)) ⟨a⟩
          · refine le_iInf fun a ↦ ?_
            exact iInf_le (fun b : Fin n ↦ 𝒰 (σ b)) a.as
    _ = cechIntersection 𝒰 σ := rfl

/-- The degree-`p` term of `cechComplex 𝒰 F`, rewritten as the product over the tuplewise Čech
intersections. -/
private theorem cechComplex_obj_X_eq_product (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (cechComplex 𝒰 F).X p =
      ∏ᶜ fun σ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 σ)) := by
  change ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).obj
      (SimplexCategory.mk p) = _
  simp only [FormalCoproduct.cosimplicialObjectFunctor_obj_obj, FormalCoproduct.cech_obj,
    FormalCoproduct.power_I, FormalCoproduct.power_obj]
  congr
  ext σ
  exact congrArg (fun U : Opens X ↦ F.obj (op U)) (cechTupleProduct_eq_intersection 𝒰 σ)

/-- The evaluation morphism from the tuplewise Čech term to one chosen Čech intersection factor. -/
noncomputable def cechTermEval (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (σ : Fin (p + 1) → ι) :
    cechTerm 𝒰 F p ⟶ F.obj (op (cechIntersection 𝒰 σ)) :=
  AddCommGrpCat.ofHom
    { toFun := fun s ↦ s σ
      map_zero' := rfl
      map_add' := by
        intro x y
        rfl }

@[simp] theorem cechTermEval_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (σ : Fin (p + 1) → ι)
    (s : cechTerm 𝒰 F p) :
    cechTermEval 𝒰 F p σ s = s σ :=
  rfl

/-- The canonical product comparison between the owner degree of the Čech complex and the
tuplewise function model used for explicit Čech cochains. -/
private noncomputable def cechTermProductIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (∏ᶜ fun σ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 σ))) ≅ cechTerm 𝒰 F p where
  hom :=
    AddCommGrpCat.ofHom
      { toFun := fun x σ ↦
          (Pi.π (fun τ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 τ))) σ) x
        map_zero' := by
          funext σ
          change (Pi.π (fun τ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 τ))) σ) 0 = 0
          exact map_zero _
        map_add' := by
          intro x y
          funext σ
          change (Pi.π (fun τ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 τ))) σ) (x + y) =
            (Pi.π (fun τ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 τ))) σ) x +
              (Pi.π (fun τ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 τ))) σ) y
          exact map_add _ _ _ }
  inv :=
    Pi.lift (fun σ : Fin (p + 1) → ι ↦ cechTermEval 𝒰 F p σ)
  hom_inv_id := by
    apply Pi.hom_ext
    intro σ
    rw [Category.assoc, Pi.lift_π]
    ext x
    rfl
  inv_hom_id := by
    ext x σ
    change ((Pi.lift (fun τ : Fin (p + 1) → ι ↦ cechTermEval 𝒰 F p τ) ≫
        Pi.π (fun τ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 τ))) σ) x) = x σ
    rw [Pi.lift_π]
    rfl

/-- The canonical bridge between the owner degree of the Čech complex and the tuplewise function
model used in the explicit coordinate formulas. -/
noncomputable abbrev cechTermIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (cechComplex 𝒰 F).X p ≅ cechTerm 𝒰 F p :=
  eqToIso (cechComplex_obj_X_eq_product 𝒰 F p) ≪≫ cechTermProductIso 𝒰 F p

/-- The restriction map associated to omitting one index from a Čech multi-index. -/
abbrev cechRestriction (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) {n : ℕ}
    (σ : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    F.obj (op (cechIntersection 𝒰 (σ ∘ j.succAboveEmb))) ⟶
      F.obj (op (cechIntersection 𝒰 σ)) :=
  F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op

/-- The underlying function of the degree-`p` Čech differential. -/
def cechDifferentialToFun (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    cechTerm 𝒰 F p → cechTerm 𝒰 F (p + 1) :=
  fun s ↦
    fun σ : Fin (p + 2) → ι ↦
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        cechRestriction 𝒰 F σ j (s (σ ∘ j.succAboveEmb))

-- Proof sketch: each restriction map is additive, finite sums preserve addition, and the scalar
-- coefficients `(-1)^j` distribute over addition in every section group.
/-- The Čech differential is additive on cochains. -/
theorem cechDifferentialToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : cechTerm 𝒰 F p) :
    cechDifferentialToFun 𝒰 F p (s + t) =
      cechDifferentialToFun 𝒰 F p s + cechDifferentialToFun 𝒰 F p t := by
  funext σ
  let A : Fin (p + 2) → F.obj (op (cechIntersection 𝒰 σ)) :=
    fun j ↦
      (-1 : ℤ) ^ (j : ℕ) • cechRestriction 𝒰 F σ j (s (σ ∘ j.succAboveEmb))
  let B : Fin (p + 2) → F.obj (op (cechIntersection 𝒰 σ)) :=
    fun j ↦
      (-1 : ℤ) ^ (j : ℕ) • cechRestriction 𝒰 F σ j (t (σ ∘ j.succAboveEmb))
  let C : Fin (p + 2) → F.obj (op (cechIntersection 𝒰 σ)) :=
    fun j ↦ A j + B j
  let D : Fin (p + 2) → F.obj (op (cechIntersection 𝒰 σ)) :=
    fun j ↦
      (-1 : ℤ) ^ (j : ℕ) •
        cechRestriction 𝒰 F σ j ((s + t) (σ ∘ j.succAboveEmb))
  change
    ∑ j : Fin (p + 2), D j =
      (∑ j : Fin (p + 2), A j) + (∑ j : Fin (p + 2), B j)
  calc
    ∑ j : Fin (p + 2), D j = ∑ j : Fin (p + 2), C j := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simp [D, C, A, B, Pi.add_apply, map_add, smul_add]
    _ = (∑ j : Fin (p + 2), A j) + (∑ j : Fin (p + 2), B j) := by
        change ∑ j : Fin (p + 2), (A j + B j) =
          (∑ j : Fin (p + 2), A j) + ∑ j : Fin (p + 2), B j
        exact Finset.sum_add_distrib

/-- The degree-`p` differential in the Čech complex of `F` for the family `𝒰`. -/
abbrev cechDifferential (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    cechTerm 𝒰 F p ⟶ cechTerm 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (cechDifferentialToFun 𝒰 F p)
      (cechDifferentialToFun_map_add 𝒰 F p))

@[simp] theorem cechDifferential_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (s : cechTerm 𝒰 F p) :
    cechDifferential 𝒰 F p s = cechDifferentialToFun 𝒰 F p s :=
  rfl

/-- Helper for Lemma 20.9.3: applying `eqToHom` in `AddCommGrpCat` is ordinary casting on the
underlying section type. -/
private theorem addCommGrpCat_eqToHom_apply {A B : AddCommGrpCat} (h : A = B) (x : A) :
    (AddCommGrpCat.Hom.hom (eqToHom h)) x =
      cast (congrArg (fun Z : AddCommGrpCat ↦ ↥Z) h) x := by
  cases h
  rfl

/-- Helper for Lemma 20.9.3: transporting a Čech cochain component along an equality of tuples
simply rewrites the tuple index. -/
private theorem cast_cechSection_eq (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (f : (σ : Fin (p + 1) → ι) → F.obj (op (cechIntersection 𝒰 σ)))
    {σ τ : Fin (p + 1) → ι} (h : σ = τ) :
    cast
        (congrArg
          (fun Z : AddCommGrpCat.{max u v} ↦ ↥Z)
          (congrArg (fun ν ↦ F.obj (op (cechIntersection 𝒰 ν))) h))
        (f σ) =
      f τ := by
  cases h
  rfl

/-- Helper for Lemma 20.9.3: evaluating the tuplewise comparison isomorphism is just the
corresponding product projection after transporting to the product presentation. -/
@[reassoc]
private theorem cechTermIso_hom_comp_cechTermEval (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (σ : Fin (p + 1) → ι) :
    (cechTermIso 𝒰 F p).hom ≫ cechTermEval 𝒰 F p σ =
      eqToHom (cechComplex_obj_X_eq_product 𝒰 F p) ≫
        Pi.π (fun τ : Fin (p + 1) → ι ↦ F.obj (op (cechIntersection 𝒰 τ))) σ := by
  -- Proof comment: after replacing the owner degree with its product model, the remaining map is
  -- exactly evaluation at the `σ`-component.
  ext s
  rfl

/-- Helper for Lemma 20.9.3: the deleted-tuple projection on tuplewise product opens agrees with
the canonical inclusion of the corresponding Čech intersections. -/
private theorem cechTupleProductRestrictionTransport (𝒰 : ι → Opens X) {p : ℕ}
    (σ : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    eqToHom (cechTupleProduct_eq_intersection 𝒰 σ).symm ≫
        Pi.lift
          (fun a : Fin (p + 1) ↦
            Pi.π (fun b : Fin (p + 2) ↦ 𝒰 (σ b)) (j.succAbove a)) =
      homOfLE (cechIntersection_le_succAbove 𝒰 σ j) ≫
        eqToHom (cechTupleProduct_eq_intersection 𝒰 (σ ∘ j.succAboveEmb)).symm := by
  -- Proof comment: `Opens X` is a thin category, so both composites are the unique morphism
  -- from the full tuple intersection to the deleted tuple intersection.
  exact Subsingleton.elim _ _

/-- Helper for Lemma 20.9.3: after applying the presheaf to the deleted-tuple projection square,
the two resulting composites on sections agree. -/
private theorem cechTupleProductRestrictionTransport_map (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    F.map
        (Pi.lift
          (fun a : Fin (p + 1) ↦
            Pi.π (fun b : Fin (p + 2) ↦ 𝒰 (σ b)) (j.succAbove a))).op ≫
      F.map (eqToHom (cechTupleProduct_eq_intersection 𝒰 σ).symm).op =
        F.map (eqToHom (cechTupleProduct_eq_intersection 𝒰 (σ ∘ j.succAboveEmb)).symm).op ≫
          F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op := by
  -- Proof comment: `F.map` turns the thin-category transport square on opens into the matching
  -- equality of section restriction composites.
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map <|
    congrArg Quiver.Hom.op (cechTupleProductRestrictionTransport 𝒰 σ j)

/-- Helper for Lemma 20.9.3: after projecting to the deleted tuple component, the transport square
on tuple products becomes the corresponding equality on sections. -/
private theorem cechTupleProductRestrictionTransport_map_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : Fin (p + 2) → ι) (j : Fin (p + 2))
    (t : ↑(∏ᶜ fun τ : Fin (p + 1) → ι ↦ F.obj (op (∏ᶜ fun a : Fin (p + 1) ↦ 𝒰 (τ a))))) :
    F.map (eqToHom (cechTupleProduct_eq_intersection 𝒰 σ).symm).op
        (F.map
          (Pi.lift
            (fun a : Fin (p + 1) ↦
              Pi.π (fun b : Fin (p + 2) ↦ 𝒰 (σ b)) (j.succAbove a))).op
          ((Pi.π
                (fun τ : Fin (p + 1) → ι ↦
                  F.obj (op (∏ᶜ fun a : Fin (p + 1) ↦ 𝒰 (τ a))))
                (σ ∘ j.succAbove)) t)) =
      F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op
        (F.map (eqToHom (cechTupleProduct_eq_intersection 𝒰 (σ ∘ j.succAbove)).symm).op
          ((Pi.π
                (fun τ : Fin (p + 1) → ι ↦
                  F.obj (op (∏ᶜ fun a : Fin (p + 1) ↦ 𝒰 (τ a))))
                (σ ∘ j.succAbove)) t)) := by
  -- Proof comment: precompose the morphism-level transport square with the deleted-tuple
  -- projection and then evaluate it on the chosen section `t`.
  simpa using
    congrArg
      (fun f ↦
        ((Pi.π
              (fun τ : Fin (p + 1) → ι ↦
                F.obj (op (∏ᶜ fun a : Fin (p + 1) ↦ 𝒰 (τ a))))
              (σ ∘ j.succAbove) ≫
            f) t))
      (cechTupleProductRestrictionTransport_map 𝒰 F σ j)

/-- Helper for Lemma 20.9.3: the formal-coproduct coface component at a tuple `σ` is the usual
restriction from the deleted tuple `(σ ∘ j.succAboveEmb)` to `σ`. -/
private theorem formalCechCofaceComponent_eq_cechRestriction (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ} (s : (cechComplex 𝒰 F).X p)
    (σ : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    (cechTermIso 𝒰 F (p + 1)).hom
        (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ j
          s) σ =
      cechRestriction 𝒰 F σ j ((cechTermIso 𝒰 F p).hom s (σ ∘ j.succAboveEmb)) := by
  -- Route correction: the owner/product transport is already built into `cechTermIso`, so it is
  -- cheaper and more stable to unfold that bridge once and let `simp` expose the deleted-tuple
  -- restriction map directly.
  simp [cechTermIso, cechTermProductIso, cechTermEval, cechRestriction, Function.comp_def]

/-- Helper for Lemma 20.9.3: evaluating the owner Čech differential in tuplewise coordinates gives
the explicit alternating-sum formula. -/
private theorem cechTermIso_hom_d_apply_aux (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (s : (cechComplex 𝒰 F).X p)
    (σ : Fin (p + 2) → ι) :
    (cechTermIso 𝒰 F (p + 1)).hom ((cechComplex 𝒰 F).d p (p + 1) s) σ =
      cechDifferentialToFun 𝒰 F p ((cechTermIso 𝒰 F p).hom s) σ := by
  let postcompose :
      ((cechComplex 𝒰 F).X p ⟶ (cechComplex 𝒰 F).X (p + 1)) →+
        (((cechComplex 𝒰 F).X p) →+ F.obj (op (cechIntersection 𝒰 σ))) :=
    { toFun := fun f ↦
        AddCommGrpCat.Hom.hom
          (f ≫ (cechTermIso 𝒰 F (p + 1)).hom ≫ cechTermEval 𝒰 F (p + 1) σ)
      map_zero' := by
        ext x
        simp
      map_add' := by
        intro f g
        ext x
        simp [Category.assoc] }
  -- Proof comment: rewrite the owner differential as the alternating coface sum and then push
  -- the whole computation through the additive postcomposition map at the fixed component `σ`.
  change postcompose ((cechComplex 𝒰 F).d p (p + 1)) s = _
  rw [cechComplexFunctor_d_eq_objD]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  simp only [cechDifferentialToFun]
  change
      postcompose
        (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ j)
        s =
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      cechRestriction 𝒰 F σ j ((cechTermIso 𝒰 F p).hom s (σ ∘ j.succAboveEmb))
  have hsum :
      postcompose
          (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ j) =
        ∑ j : Fin (p + 2),
          postcompose
            ((-1 : ℤ) ^ (j : ℕ) •
              ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ j) := by
    simpa using map_sum postcompose
      (fun j : Fin (p + 2) ↦ (-1 : ℤ) ^ (j : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ j)
      Finset.univ
  rw [hsum]
  have hsum_apply :
      (∑ j : Fin (p + 2),
          postcompose
            ((-1 : ℤ) ^ (j : ℕ) •
              ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ
                j))
        s =
        ∑ j : Fin (p + 2),
          (postcompose
            ((-1 : ℤ) ^ (j : ℕ) •
              ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ
                j))
            s := by
    simpa using
      (Finset.sum_apply s Finset.univ
        (fun j : Fin (p + 2) ↦
          postcompose
            ((-1 : ℤ) ^ (j : ℕ) •
              ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ
                j)))
  rw [hsum_apply]
  refine Finset.sum_congr rfl ?_
  intro j hj
  -- Proof comment: each summand is exactly the coface component computation from the previous
  -- bridge lemma, with the alternating sign carried through by additivity.
  have hz :
      postcompose
          ((-1 : ℤ) ^ (j : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ j) =
        (-1 : ℤ) ^ (j : ℕ) •
          postcompose
            (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ j) := by
    simpa using map_zsmul postcompose ((-1 : ℤ) ^ (j : ℕ))
      (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj F).δ j)
  rw [hz]
  simp only [postcompose]
  exact congrArg (fun z ↦ (-1 : ℤ) ^ (j : ℕ) • z)
    (formalCechCofaceComponent_eq_cechRestriction 𝒰 F s σ j)

/-- The canonical bridge `cechTermIso` identifies the owner Čech differential with the explicit
tuplewise alternating-sum differential. -/
theorem cechTermIso_comm_d (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (cechComplex 𝒰 F).d p (p + 1) ≫ (cechTermIso 𝒰 F (p + 1)).hom =
      (cechTermIso 𝒰 F p).hom ≫ cechDifferential 𝒰 F p := by
  -- Proof comment: the evaluated bridge theorem already computes both sides in the same tuplewise
  -- coordinates.
  ext s σ
  simpa [cechDifferential] using cechTermIso_hom_d_apply_aux 𝒰 F p s σ

/-- Evaluating `cechTermIso_comm_d` on a cochain and a tuple recovers the explicit alternating-sum
formula for the owner Čech differential. -/
@[simp] theorem cechTermIso_hom_d_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (s : (cechComplex 𝒰 F).X p)
    (σ : Fin (p + 2) → ι) :
    (cechTermIso 𝒰 F (p + 1)).hom ((cechComplex 𝒰 F).d p (p + 1) s) σ =
      cechDifferentialToFun 𝒰 F p ((cechTermIso 𝒰 F p).hom s) σ := by
  -- Proof comment: reuse the direct tuplewise computation to keep the public simp theorem flat.
  simpa using cechTermIso_hom_d_apply_aux 𝒰 F p s σ

/-- Transporting the owner square-zero relation through `cechTermIso` shows that the explicit
tuplewise Čech differential also squares to zero. -/
theorem cechDifferential_comp_cechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    cechDifferential 𝒰 F p ≫ cechDifferential 𝒰 F (p + 1) = 0 := by
  -- Proof comment: transport the owner relation `d ≫ d = 0` across the degreewise
  -- identifications supplied by `cechTermIso`.
  ext s σ
  let t : (cechComplex 𝒰 F).X p := (cechTermIso 𝒰 F p).inv s
  have ht : (cechTermIso 𝒰 F p).hom t = s := by
    simpa [t] using (Iso.inv_hom_id_apply (cechTermIso 𝒰 F p) s)
  have hzero :=
    congrArg
      (fun k ↦ ((k ≫ (cechTermIso 𝒰 F (p + 2)).hom) t) σ)
      ((cechComplex 𝒰 F).d_comp_d p (p + 1) (p + 2))
  -- Route correction: first evaluate the owner square-zero relation on the owner cochain `t`,
  -- and only then rewrite each owner differential into the explicit tuplewise formula.
  have hzero' :
      (cechTermIso 𝒰 F (p + 2)).hom
          ((cechComplex 𝒰 F).d (p + 1) (p + 2) ((cechComplex 𝒰 F).d p (p + 1) t)) σ =
        0 := by
    simpa [Category.assoc, t] using hzero
  rw [cechTermIso_hom_d_apply] at hzero'
  have hfirst :
      (cechTermIso 𝒰 F (p + 1)).hom ((cechComplex 𝒰 F).d p (p + 1) t) =
        cechDifferentialToFun 𝒰 F p ((cechTermIso 𝒰 F p).hom t) := by
    ext τ
    simpa using cechTermIso_hom_d_apply 𝒰 F p t τ
  rw [hfirst, ht] at hzero'
  simpa [cechDifferential] using hzero'

-- Proof sketch: every member `𝒰 i` of the family lies below `iSup 𝒰`; rewriting along the cover
-- equality gives the desired inclusion `𝒰 i ≤ U`.
/-- Any member of a cover `U = iSup 𝒰` is contained in `U`. -/
theorem openFamily_le_of_iSup_eq (U : Opens X) (𝒰 : ι → Opens X) (hcover : U = iSup 𝒰)
    (i : ι) :
    𝒰 i ≤ U := by
  simpa [hcover] using (le_iSup 𝒰 i)

-- Proof sketch: each intersection term is contained in each participating cover member, and hence
-- in `U` after rewriting along the cover equality.
/-- Every nonempty Čech intersection of a cover `U = iSup 𝒰` is itself contained in `U`. -/
theorem cechIntersection_le_of_iSup_eq (U : Opens X) (𝒰 : ι → Opens X) (hcover : U = iSup 𝒰)
    {n : ℕ} (σ : Fin (n + 1) → ι) :
    cechIntersection 𝒰 σ ≤ U := by
  calc
    cechIntersection 𝒰 σ ≤ 𝒰 (σ 0) := by
      simpa [cechIntersection] using
        (iInf_le (fun a : Fin (n + 1) ↦ 𝒰 (σ a)) 0)
    _ ≤ U := openFamily_le_of_iSup_eq U 𝒰 hcover (σ 0)

/-- Helper for Lemma 20.9.3: inserting a cover member equal to `U` at the front of a Čech tuple
does not change the corresponding intersection. -/
theorem cechIntersection_cons_eq_of_eq_at (U : Opens X) (𝒰 : ι → Opens X)
    (hcover : U = iSup 𝒰) (i : ι) (hi : 𝒰 i = U) {p : ℕ} (σ : Fin (p + 1) → ι) :
    cechIntersection 𝒰 (Fin.cons i σ) = cechIntersection 𝒰 σ := by
  refine le_antisymm ?_ ?_
  · -- Forgetting the front entry is exactly the successor-embedding monotonicity of intersections.
    simpa using cechIntersection_le_succAbove 𝒰 (Fin.cons i σ) 0
  · -- The tail intersection already lies in `U`, so it satisfies the extra front constraint too.
    refine le_iInf fun a ↦ ?_
    refine Fin.cases ?_ ?_ a
    · simpa [hi] using cechIntersection_le_of_iSup_eq U 𝒰 hcover σ
    · intro b
      simpa [cechIntersection] using (iInf_le (fun c : Fin (p + 1) ↦ 𝒰 (σ c)) b)

/-- The underlying function of the canonical augmentation from `F(U)` to degree `0` Čech cochains. -/
def cechAugmentationToFun (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    F.obj (op U) → cechTerm 𝒰 F 0 :=
  fun s ↦
    fun σ : Fin 1 → ι ↦
      F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover σ)).op s

@[simp] theorem cechAugmentationToFun_apply (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰)
    (s : F.obj (op U)) (σ : Fin 1 → ι) :
    cechAugmentationToFun U 𝒰 F hcover s σ =
      F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover σ)).op s :=
  rfl

-- Proof sketch: each component of the augmentation is a restriction morphism of abelian groups,
-- hence additive; the whole map is additive because it is defined componentwise.
/-- The canonical degree-zero Čech augmentation is additive. -/
theorem cechAugmentationToFun_map_add (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰)
    (s t : F.obj (op U)) :
    cechAugmentationToFun U 𝒰 F hcover (s + t) =
      cechAugmentationToFun U 𝒰 F hcover s + cechAugmentationToFun U 𝒰 F hcover t := by
  funext σ
  simp [cechAugmentationToFun, map_add]

/-- The canonical map from `F(U)` to degree `0` of the Čech complex of the covering `𝒰`. -/
abbrev cechAugmentationMap (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    F.obj (op U) ⟶ (cechComplex 𝒰 F).X 0 :=
  AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (cechAugmentationToFun U 𝒰 F hcover)
        (cechAugmentationToFun_map_add U 𝒰 F hcover)) ≫
    (cechTermIso 𝒰 F 0).inv

@[simp] theorem cechTermIso_hom_cechAugmentationMap_apply (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰)
    (s : F.obj (op U)) (σ : Fin 1 → ι) :
    (cechTermIso 𝒰 F 0).hom (cechAugmentationMap U 𝒰 F hcover s) σ =
      F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover σ)).op s := by
  change ((cechAugmentationMap U 𝒰 F hcover ≫ (cechTermIso 𝒰 F 0).hom) s) σ =
    F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover σ)).op s
  simp [cechAugmentationMap, cechAugmentationToFun]

/-- Helper for Lemma 20.9.3: the one-term Čech intersection at a chosen cover member `i` with
`𝒰 i = U` is exactly `U`. -/
private theorem cechIntersection_single_eq_of_eq_at (U : Opens X) (𝒰 : ι → Opens X)
    (i : ι) (hi : 𝒰 i = U) :
    cechIntersection 𝒰 (fun _ : Fin 1 ↦ i) = U := by
  -- Proof comment: a singleton infimum in `Opens X` is just the chosen open itself.
  simpa [cechIntersection, hi]

/-- Helper for Lemma 20.9.3: evaluating the degree-zero Čech augmentation at the chosen cover
member `i` and transporting back along `𝒰 i = U` recovers the original section of `F(U)`. -/
private theorem cechAugmentationAtChosenIndex_apply (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) (i : ι) (hi : 𝒰 i = U)
    (s : F.obj (op U)) :
    F.map
        (eqToHom (cechIntersection_single_eq_of_eq_at U 𝒰 i hi).symm).op
        ((cechTermIso 𝒰 F 0).hom (cechAugmentationMap U 𝒰 F hcover s) (fun _ ↦ i)) =
      s := by
  let hσ : cechIntersection 𝒰 (fun _ : Fin 1 ↦ i) = U :=
    cechIntersection_single_eq_of_eq_at U 𝒰 i hi
  let α : cechIntersection 𝒰 (fun _ : Fin 1 ↦ i) ⟶ U :=
    homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover (fun _ ↦ i))
  have hα : α = eqToHom hσ := by
    -- Proof comment: `Opens X` is thin, so the cover inclusion is the equality transport.
    apply Subsingleton.elim
  have hop : α.op ≫ (eqToHom hσ.symm).op = 𝟙 (op U) := by
    simpa [hα] using congrArg Quiver.Hom.op (eqToHom_trans hσ hσ.symm)
  -- Proof comment: after rewriting the augmentation component with the chosen tuple, the
  -- restriction and the transport are inverse equalities.
  rw [cechTermIso_hom_cechAugmentationMap_apply]
  have hcomp :
      (ConcreteCategory.hom (F.map (α.op ≫ (eqToHom hσ.symm).op))) s =
        (ConcreteCategory.hom (F.map (eqToHom hσ.symm).op))
          ((ConcreteCategory.hom (F.map α.op)) s) := by
    simpa using
      congrArg (fun f ↦ (ConcreteCategory.hom f) s) (F.map_comp α.op (eqToHom hσ.symm).op)
  rw [← hcomp, hop]
  simp

-- Proof sketch: expanding the degree-zero differential shows that each component is the
-- alternating sum of two identical restrictions from `F(U)` to a double intersection, so the two
-- terms cancel.
/-- The canonical augmentation is a cocycle in degree `0` of the Čech complex. -/
theorem cechAugmentationMap_comp_d_zero_one (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    cechAugmentationMap U 𝒰 F hcover ≫ (cechComplex 𝒰 F).d 0 1 = 0 := by
  -- Proof comment: pass to tuplewise coordinates in degree `1`; each component is the difference
  -- of the two identical restriction maps from `F(U)` to the same double intersection.
  let ε : F.obj (op U) ⟶ cechTerm 𝒰 F 0 :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (cechAugmentationToFun U 𝒰 F hcover)
        (cechAugmentationToFun_map_add U 𝒰 F hcover))
  have hε : cechAugmentationMap U 𝒰 F hcover ≫ (cechTermIso 𝒰 F 0).hom = ε := by
    simp [cechAugmentationMap, ε]
  apply (cancel_mono (cechTermIso 𝒰 F 1).hom).1
  rw [Category.assoc, cechTermIso_comm_d, ← Category.assoc, hε, zero_comp]
  ext s σ
  -- Route correction: evaluate after the degree-`1` tuplewise comparison, so the two coface
  -- summands cancel directly in the explicit alternating-sum formula.
  simp [ε, cechDifferential, cechDifferentialToFun, Fin.sum_univ_two]
  let α : cechIntersection 𝒰 σ ⟶ U := homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover σ)
  have h0 :
      homOfLE (cechIntersection_le_succAbove 𝒰 σ 0) ≫
        homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover (σ ∘ Fin.succ)) =
      α := by
    apply Subsingleton.elim
  have h1 :
      homOfLE (cechIntersection_le_succAbove 𝒰 σ 1) ≫
        homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover (σ ∘ Fin.succAbove 1)) =
      α := by
    apply Subsingleton.elim
  have hs0 :
      cechRestriction 𝒰 F σ 0
          ((F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover (σ ∘ Fin.succ))).op) s) =
        F.map α.op s := by
    change
      ((F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover (σ ∘ Fin.succ))).op ≫
          F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ 0)).op) s) =
        _
    rw [← F.map_comp]
    rw [show
        (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover (σ ∘ Fin.succ))).op ≫
            (homOfLE (cechIntersection_le_succAbove 𝒰 σ 0)).op =
          α.op by
        simpa using congrArg Quiver.Hom.op h0]
  have hs1 :
      cechRestriction 𝒰 F σ 1
          ((F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover
              (σ ∘ Fin.succAbove 1))).op) s) =
        F.map α.op s := by
    change
      ((F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover
            (σ ∘ Fin.succAbove 1))).op ≫
          F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ 1)).op) s) =
        _
    rw [← F.map_comp]
    rw [show
        (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover (σ ∘ Fin.succAbove 1))).op ≫
            (homOfLE (cechIntersection_le_succAbove 𝒰 σ 1)).op =
          α.op by
        simpa using congrArg Quiver.Hom.op h1]
  calc
    cechRestriction 𝒰 F σ 0
          ((F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover (σ ∘ Fin.succ))).op) s) +
        -cechRestriction 𝒰 F σ 1
          ((F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover
              (σ ∘ Fin.succAbove 1))).op) s) =
      F.map α.op s + -F.map α.op s := by
        rw [hs0, hs1]
    _ = 0 := by
      abel

/-- Specialized source-facing form of `cechAugmentationMap_comp_d_zero_one` for the cover
`iSup 𝒰`. -/
theorem cechAugmentationMap_comp_d_zero_one_of_iSup
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    cechAugmentationMap (iSup 𝒰) 𝒰 F rfl ≫ (cechComplex 𝒰 F).d 0 1 = 0 := by
  simpa using cechAugmentationMap_comp_d_zero_one (iSup 𝒰) 𝒰 F rfl

/-- The ordinary Čech augmentation, viewed as a morphism from `F(U)[0]` to the Čech complex. -/
def extendedCechComplexAugmentation (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj (F.obj (op U)) ⟶ cechComplex 𝒰 F :=
  (CochainComplex.fromSingle₀Equiv (cechComplex 𝒰 F) (F.obj (op U))).symm
    ⟨cechAugmentationMap U 𝒰 F hcover, cechAugmentationMap_comp_d_zero_one U 𝒰 F hcover⟩

/-- The extended ordinary Čech complex obtained by adjoining `F(U)` in degree `-1`. -/
def extendedCechComplex (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.fromSingle₀AsComplex (cechComplex 𝒰 F) (F.obj (op U))
    (extendedCechComplexAugmentation U 𝒰 F hcover)

/-- Helper for Lemma 20.9.3: `extendedCechComplex U 𝒰 F hcover` viewed with its explicit
`CochainComplex AddCommGrpCat.{max u v} ℕ` target universe. -/
private abbrev extendedCechComplexTyped (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  extendedCechComplex U 𝒰 F hcover

/-- Helper for Lemma 20.9.3: a contracting homotopy of the identity packages directly into a
homotopy equivalence with the zero complex. -/
private theorem homotopyEquivalences_zero_of_contractingHomotopy
    {C : CochainComplex AddCommGrpCat.{max u v} ℕ}
    (h : Homotopy (𝟙 C) 0) :
    homotopyEquivalences AddCommGrpCat.{max u v} (ComplexShape.up ℕ) (0 : C ⟶ 0) := by
  -- The zero maps give both directions, and the contracting homotopy supplies the nontrivial
  -- identity-side witness.
  exact ⟨{
    hom := 0
    inv := 0
    homotopyHomInvId := h.symm
    homotopyInvHomId := Homotopy.ofEq (by simp)
  }, rfl⟩

-- Proof sketch: choose the index `i` with `𝒰 i = U`, define the contracting homotopy by inserting
-- `i` at the front of every multi-index, and check componentwise that `dh + hd = 𝟙`.
/-- If one member of the covering family equals `U`, the extended Čech complex is homotopy
equivalent to the zero complex. -/
theorem extendedCechComplex_homotopyEquivalent_zero_of_eq_at (U : Opens X)
    (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) (i : ι) (hi : 𝒰 i = U) :
    homotopyEquivalences AddCommGrpCat.{max u v} (ComplexShape.up ℕ)
      (0 : extendedCechComplex U 𝒰 F hcover ⟶ 0) := by
  -- TODO: use `cechAugmentationAtChosenIndex_apply` for the degree-zero left inverse, define the
  -- positive-degree front-insertion maps through `cechTermIso` and
  -- `cechIntersection_cons_eq_of_eq_at`, prove the owner-side identity `dh + hd = 𝟙` via
  -- `cechTermIso_hom_d_apply`, and then package the contracting homotopy with
  -- `homotopyEquivalences_zero_of_contractingHomotopy`.
  sorry

/-- Companion bridge: the homotopy-equivalence witness of
`extendedCechComplex_homotopyEquivalent_zero_of_eq_at` packages into an actual
`HomotopyEquiv`. -/
theorem extendedCechComplex_nonempty_homotopyEquiv_zero_of_eq_at (U : Opens X)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰)
    (i : ι) (hi : 𝒰 i = U) :
    Nonempty (HomotopyEquiv (extendedCechComplex U 𝒰 F hcover) 0) := by
  rcases extendedCechComplex_homotopyEquivalent_zero_of_eq_at U 𝒰 F hcover i hi with ⟨e, -⟩
  exact ⟨e⟩

-- Proof sketch: choose an index `i` with `𝒰 i = U` and apply the explicit contracting-homotopy
-- construction from the indexed version of the lemma.
/-- Lemma 20.9.3: if an open cover of `U` contains `U` itself as one of its members, then the
extended Čech complex of an abelian presheaf `F` on `X`, obtained by placing `F(U)` in degree `-1`,
is homotopy equivalent to the zero complex. -/
@[stacks 0G6S]
theorem extendedCechComplex_homotopyEquivalent_zero_of_exists_eq
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (htrivial : ∃ i : ι, 𝒰 i = U) :
    homotopyEquivalences AddCommGrpCat.{max u v} (ComplexShape.up ℕ)
      (0 : extendedCechComplex U 𝒰 F hcover ⟶ 0) := by
  rcases htrivial with ⟨i, hi⟩
  simpa using extendedCechComplex_homotopyEquivalent_zero_of_eq_at U 𝒰 F hcover i hi

/-- Companion bridge: Lemma `20.9.3` yields an actual `HomotopyEquiv` from the extended Čech
complex to `0`. -/
theorem extendedCechComplex_nonempty_homotopyEquiv_zero_of_exists_eq
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (htrivial : ∃ i : ι, 𝒰 i = U) :
    Nonempty (HomotopyEquiv (extendedCechComplex U 𝒰 F hcover) 0) := by
  rcases extendedCechComplex_homotopyEquivalent_zero_of_exists_eq U 𝒰 F hcover htrivial with
    ⟨e, -⟩
  exact ⟨e⟩
